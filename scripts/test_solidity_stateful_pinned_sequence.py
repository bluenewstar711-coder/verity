"""Reject source drift and check complete pinned-sequence inputs before execution."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from solidity_differential import pinned_sequence as instrument
from solidity_differential.check_pinned_sequence_fixture import FIXTURE, materialize
from solidity_differential.engine import HarnessError


class PinnedSequenceInputs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.output = Path(self.temp.name)
        self.config_path = materialize(self.output)
        self.config = instrument.load_config(self.config_path)
        self.root = self.config['project']

    def sources(self):
        return instrument.pinned_sources(self.root, self.config['revision'], self.config['entry'])

    def test_exact_source_and_tracked_edit(self):
        sources, _ = self.sources()
        fixture = (FIXTURE / 'src/RoleRegistry.sol').read_text()
        self.assertEqual(sources['src/RoleRegistry.sol']['content'], fixture)
        (self.root / 'src/RoleRegistry.sol').write_text('contract Changed {}\n')
        with self.assertRaisesRegex(HarnessError, 'dirty'):
            self.sources()

    def test_untracked_production_input_is_rejected(self):
        (self.root / 'src/Injected.sol').write_text('contract Injected {}\n')
        with self.assertRaisesRegex(HarnessError, 'dirty'):
            self.sources()

    def test_wrong_revision_is_rejected(self):
        with self.assertRaisesRegex(HarnessError, 'revision'):
            instrument.pinned_sources(self.root, '0' * 40, self.config['entry'])

    def test_fixture_revision_is_reproducible(self):
        again = Path(self.temp.name) / 'again'
        again.mkdir()
        other = json.loads(materialize(again).read_text())
        self.assertEqual(other['revision'], self.config['revision'])
        head = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True)
        self.assertEqual(head.strip(), self.config['revision'])

    def test_transactions_reproduce_and_retain_complete_payload(self):
        target = '0x' + '12' * 20
        rows = instrument.transaction_sequence(self.config, 64, 7, target)
        self.assertEqual(rows, instrument.transaction_sequence(self.config, 64, 7, target))
        self.assertNotEqual(rows, instrument.transaction_sequence(self.config, 64, 8, target))
        self.assertEqual(len({row['id'] for row in rows}), 64)
        self.assertEqual({row['function'] for row in rows},
                         {s.split('(')[0] for s in self.config['signatures']})
        for row in rows:
            data = bytes.fromhex(row['data'][2:])
            self.assertEqual([int.from_bytes(data[i:i + 32], 'big')
                              for i in range(4, len(data), 32)], row['args'])
            self.assertEqual(row['target'], target)
        # A reduced sequence preserves the original environment and calldata.
        self.assertEqual(rows[12]['blockNumber'], 14)
        self.assertEqual(rows[12]['sender'], instrument.SENDERS[1])
        self.assertEqual(rows[0]['args'], [int(instrument.SENDERS[1], 16)])

    def test_deterministic_prefix_cannot_be_truncated(self):
        count = len(self.config['prefix'])
        with self.assertRaisesRegex(HarnessError, f'at least {count}'):
            instrument.transaction_sequence(self.config, count - 1, 7, '0x' + '12' * 20)

    def test_every_signature_requires_argument_pools(self):
        del self.config['arguments']['setAdmin(address)']
        with self.assertRaisesRegex(HarnessError, 'argument pools'):
            instrument.transaction_sequence(self.config, 64, 7, '0x' + '12' * 20)

    def test_dynamic_arguments_are_rejected(self):
        with self.assertRaisesRegex(HarnessError, 'unsupported'):
            instrument.argument_types('f(bytes,uint256)')

    def test_driver_imports_every_root_and_mutant_only_alters_model(self):
        base = instrument.driver_source(self.root, self.config)
        mutant = instrument.driver_source(self.root, self.config, 'drop-events')
        for signature in self.config['signatures']:
            self.assertIn('  function ' + signature + '\n', base)
        self.assertIn('optimizerRuns := some 466', base)
        self.assertIn('def model : CompilationModel := tested.model\n', base)
        self.assertIn('| .emit _ _ => false', mutant)
        self.assertEqual(base.split('def model')[0], mutant.split('def model')[0])
        with self.assertRaisesRegex(HarnessError, 'unknown'):
            instrument.driver_source(self.root, self.config, 'other')

    def test_nonce_zero_deployment_address(self):
        self.assertEqual(instrument.create_address(instrument.SENDERS[0]),
                         '0x5fbdb2315678afecb367f032d93f642f64180aa3')


if __name__ == '__main__':
    unittest.main()
