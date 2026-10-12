"""Execute account-world instrumentation mutations against preserved actual A/C traces.

Every mutant must build and produce complete observations. Resource, parser,
coverage and other tooling failures do not count as detection. First-call
witnesses execute the same initial world and actual transaction as the source
receipt, and an empty-sequence execution checks the one-call deletion control.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import HarnessError, command, write_json
from .denote import SequenceAdapter
from .stateful import compare_sequences

MUTANTS = {
    'world-initial-nonce': ('nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat balance, code',
                            'nonce := 0, balance := Uint256.ofNat balance, code'),
    'world-initial-balance': ('nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat balance, code',
                              'nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat (balance + 1), code'),
    'world-initial-code': ('nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat balance, code',
                           'nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat balance, code := []'),
    'world-initial-storage': ('current.writeStorage slot.1 (Uint256.ofNat slot.2)',
                              'current.writeStorage slot.1 (Uint256.ofNat (slot.2 + 1))'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-campaign', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo = Path.cwd()
    if command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('account-world mutations require clean exact source')
    head = command(['git', 'rev-parse', 'HEAD']).strip()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    saved = args.source_campaign.resolve() if args.source_campaign else out / 'source'
    if args.source_campaign is None:
        command([sys.executable, '-m', 'solidity_differential.check_stateful', '--external-accounts',
            '--transactions', '32', '--senders', '3', '--model-driver',
            'Contracts/SolidityImportSmoke/StorageSequenceModel.lean', '--source-fixture',
            'Contracts/SolidityImportSmoke/StorageSequence.sol', '--output', saved], log=out / 'source.log')
    campaign = json.loads((saved / 'campaign.json').read_text())
    if campaign['divergences'] or not campaign['transactions']:
        raise HarnessError('source account-world baseline is not complete and agreeing')
    if json.loads((saved / 'source.input.json').read_text())['sources']['Sequence.sol']['content'] != (repo / 'Contracts/SolidityImportSmoke/StorageSequence.sol').read_text():
        raise HarnessError('saved source differs from the current imported fixture')
    initial = json.loads((saved / 'initial-accounts.json').read_text())
    if not initial or not json.loads((saved / 'provenance.json').read_text())['externalAccounts']:
        raise HarnessError('saved campaign did not execute account-world observations')
    storage = json.loads((saved / 'initial-storage.json').read_text())
    source_files = [saved / name for name in ['campaign.json', 'source.input.json', 'source.output.json',
        'compiled.input.json', 'compiled.output.json', 'initial-accounts.json', 'initial-storage.json', 'implementation.json', 'provenance.json']]
    source_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}
    write_json(out / 'source-provenance.json', {'sha256': source_hashes})
    transactions, plans = campaign['transactions'], campaign['slots']
    ids = [tx['id'] for tx in transactions]
    work = out / 'work'
    # A transported shallow snapshot avoids growing transferred alternate-store chains.
    command(['git', 'clone', '--no-local', '--depth', '1', '--no-checkout', repo, work])
    command(['git', '-C', work, 'checkout', '--detach', head])
    (work / '.lake').mkdir()
    command(['cp', '-a', '--reflink=auto', repo / '.lake/build', work / '.lake/build'])
    (work / '.lake/packages').symlink_to((repo / '.lake/packages').resolve(), target_is_directory=True)
    command(['cp', '-a', repo / '.lake/solidity-import', work / '.lake/solidity-import'])
    source = work / 'Compiler/SolidityImport/SequenceRunner.lean'
    original = source.read_text()
    account = transactions[0]['target']

    def execute(directory, calls, slots):
        directory.mkdir(parents=True, exist_ok=False)
        with (directory / 'build.log').open('x') as log:
            result = subprocess.run(['lake', 'build', 'Compiler.SolidityImport.SequenceRunner'],
                cwd=work, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        if result.returncode:
            raise HarnessError('account-world mutated implementation failed to compile; not detection')
        previous = Path.cwd()
        try:
            os.chdir(work)
            adapter = SequenceAdapter(directory / 'B', work / 'Contracts/SolidityImportSmoke/StorageSequenceModel.lean',
                account, initial_storage=storage, initial_accounts=initial,
                observe_accounts=[row['address'] for row in initial])
            rows = adapter(calls, slots)
            manifest = adapter.identity.manifest
        finally:
            os.chdir(previous)
        sha = hashlib.sha256(source.read_bytes()).hexdigest()
        if manifest['revision'] != head or manifest['files'][str(source)] != sha:
            raise HarnessError('executed account-world mutation provenance differs')
        write_json(directory / 'implementation.json', manifest)
        write_json(directory / 'observations.json', rows)
        return rows

    def compare(rows, count):
        return compare_sequences(ids[:count], {'source': campaign['observations']['source'][:count],
            'compiled': campaign['observations']['compiled'][:count], 'model': rows})

    if compare(execute(out / 'baseline', transactions, plans), len(transactions)):
        raise HarnessError('model baseline differs from preserved actual A/C')
    results = []
    try:
        for name, (before, after) in MUTANTS.items():
            if original.count(before) != 1:
                raise HarnessError('nonunique account-world mutation anchor: ' + name)
            mutated = original.replace(before, after)
            source.write_text(mutated)
            full = compare(execute(out / name / 'full', transactions, plans), len(transactions))
            if not full or full[0]['id'] != ids[0]:
                raise HarnessError('account-world mutant lacks the expected first-call witness')
            witness = compare(execute(out / name / 'witness', transactions[:1], plans[:1]), 1)
            if not witness or witness[0]['signature'] != full[0]['signature']:
                raise HarnessError('account-world minimal replay changed its mismatch category')
            if execute(out / name / 'delete-0', [], []) != []:
                raise HarnessError('account-world empty deletion control failed')
            sha = hashlib.sha256(mutated.encode()).hexdigest()
            for phase in ['full', 'witness', 'delete-0']:
                manifest = json.loads((out / name / phase / 'implementation.json').read_text())
                if manifest['files'][str(source)] != sha:
                    raise HarnessError('account-world executed mutation does not match intended source')
            results.append({'mutant': name, 'detected': True, 'baselinePassed': True,
                'signature': witness[0]['signature'], 'witnessCaseIds': [ids[0]], 'deletion_minimal': True,
                'sourceSha256': sha, 'scope': 'actual Denote versus preserved actual EVM A/C'})
            write_json(out / 'mutation-results.json', results)
            source.write_text(original)
    finally:
        source.write_text(original)
    if source_hashes != {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}:
        raise HarnessError('preserved actual A/C source evidence changed')
    if command(['git', 'rev-parse', 'HEAD']).strip() != head or command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('source checkout changed during account-world mutations')
    write_json(out / 'complete.json', {'head': head, 'exit': 0, 'mutants': len(results), 'newEVMSequenceTransactions': 0 if args.source_campaign else 4 * len(transactions)})
    print(f'Detected {len(results)} executed account-world mutations with one-call witnesses')


if __name__ == '__main__':
    main()
