"""Explicit code/nonce observations for deployment validation.

This instrument does not implement CREATE2 or supply a Denote deployment oracle.
Creator bytecode differs by construction between source and compiled routes;
compare its nonce and balance, and compare complete code for created accounts.
Every route must provide every explicitly planned account, including nonexistent
accounts and deployments rolled back by the parent. Missing data is an error.
"""
from .engine import HarnessError
from .stateful import ROUTES, _bytes, compare_sequences


def _word(value):
    if type(value) is not int or not 0 <= value < 2**256:
        raise HarnessError('account quantity must be an unsigned 256-bit integer')
    return value


def validate_accounts(row):
    if not isinstance(row, dict) or set(row) != {'creator', 'accounts'}:
        raise HarnessError('complete deployment observations required')
    creator = row['creator']
    if not isinstance(creator, dict) or set(creator) != {'address', 'nonce', 'balance'}:
        raise HarnessError('complete creator observation required')
    _bytes(creator['address'], 20)
    _word(creator['nonce'])
    _word(creator['balance'])
    if not isinstance(row['accounts'], list):
        raise HarnessError('account observation array required')
    accounts = {}
    for account in row['accounts']:
        if not isinstance(account, dict) or set(account) != {'address', 'code', 'nonce', 'balance'}:
            raise HarnessError('complete created-account observation required')
        address = _bytes(account['address'], 20)
        if address == creator['address'] or address in accounts:
            raise HarnessError('duplicate or creator deployment account')
        accounts[address] = (_bytes(account['code']), _word(account['nonce']), _word(account['balance']))
    return creator, accounts


def observe_accounts(node, record, creator, addresses):
    """Sample exact post-state at the transaction's mined block, never latest."""
    addresses = list(addresses)
    if len(set(addresses)) != len(addresses):
        raise HarnessError('duplicate deployment observation address')
    block = record['receipt']['blockNumber']
    def quantities(address):
        return {'address': address,
                'nonce': int(node.rpc('eth_getTransactionCount', address, block), 16),
                'balance': int(node.rpc('eth_getBalance', address, block), 16)}
    result = {'creator': quantities(creator),
              'accounts': [{**quantities(address), 'code': node.rpc('eth_getCode', address, block)}
                           for address in sorted(addresses)]}
    validate_accounts(result)
    return result


def compare_deployment_sequences(ids, traces, account_plan):
    """Compare base observations plus code/nonces/balances on an explicit plan.

    A discovery adapter must build the cumulative cross-route account union;
    supplying only each route's locally created accounts is not sufficient.
    This API requires that plan instead of inferring empty account state.
    """
    if len(account_plan) != len(ids):
        raise HarnessError('deployment plan does not cover all transactions')
    if not isinstance(traces, dict) or set(traces) != set(ROUTES):
        raise HarnessError('all three deployment routes required')
    if any(not isinstance(traces[r], list) or len(traces[r]) != len(ids) for r in ROUTES):
        raise HarnessError('incomplete deployment sequence')
    base = {route: [] for route in ROUTES}
    parsed = {route: [] for route in ROUTES}
    cumulative = set()
    for index, plan in enumerate(account_plan):
        if not isinstance(plan, list) or len(set(plan)) != len(plan):
            raise HarnessError('unique deployment address plan required')
        expected = {_bytes(address, 20) for address in plan}
        if not cumulative <= expected:
            raise HarnessError('deployment plan dropped a previously observed account')
        cumulative = expected
        for route in ROUTES:
            row = traces[route][index]
            if not isinstance(row, dict) or 'deployment' not in row:
                raise HarnessError('missing deployment state; base-only observations are insufficient')
            creator, accounts = validate_accounts(row['deployment'])
            if set(accounts) != expected:
                raise HarnessError('deployment account observation differs from explicit plan')
            parsed[route].append((creator, accounts))
            base[route].append({key: value for key, value in row.items() if key != 'deployment'})
    divergences = compare_sequences(ids, base)
    for index, ident in enumerate(ids):
        rows = [parsed[route][index] for route in ROUTES]
        if len({row[0]['address'] for row in rows}) != 1:
            raise HarnessError('creator identity differs across routes')
        values = {
            'creatorNonce': [row[0]['nonce'] for row in rows],
            'creatorBalance': [row[0]['balance'] for row in rows],
            'code': [tuple(row[1][a][0] for a in sorted(row[1])) for row in rows],
            'accountNonce': [tuple(row[1][a][1] for a in sorted(row[1])) for row in rows],
            'accountBalance': [tuple(row[1][a][2] for a in sorted(row[1])) for row in rows],
        }
        signature = tuple((key, v[0] == v[1], v[1] == v[2], v[0] == v[2])
                          for key, v in values.items() if not v[0] == v[1] == v[2])
        if signature:
            divergences.append({'id': ident, 'index': index, 'signature': signature,
                                'accounts': sorted(rows[0][1])})
    return sorted(divergences, key=lambda row: row['index'])
