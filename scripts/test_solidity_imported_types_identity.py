"""Prevent source/manifest substitution in the multi-file imported-type campaigns."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from solidity_differential.imported_types import DIRECTORY, validate_imported_types


class ImportedTypesIdentityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.fixture = Path(self.temp.name)
        source = Path(__file__).resolve().parents[1] / 'Contracts/SolidityImportSmoke' / DIRECTORY
        shutil.copytree(source, self.fixture / DIRECTORY)
        self.root = self.fixture / DIRECTORY

    def test_exact_pin(self):
        validate_imported_types(self.fixture)

    def test_source_tampering(self):
        path = self.root / 'libraries/RecordHashLib.sol'
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            validate_imported_types(self.fixture)

    def test_manifest_hash_cannot_authorize_tampering(self):
        path = self.root / 'libraries/RecordHashLib.sol'
        path.write_bytes(path.read_bytes() + b'\n')
        manifest = self.root / 'manifest.json'
        record = json.loads(manifest.read_text())
        record['files']['libraries/RecordHashLib.sol']['sha256'] = \
            hashlib.sha256(path.read_bytes()).hexdigest()
        manifest.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            validate_imported_types(self.fixture)

    def test_fixture_substitution(self):
        manifest = self.root / 'manifest.json'
        record = json.loads(manifest.read_text())
        record['fixture'] = 'other-fixture'
        manifest.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'identity differs'):
            validate_imported_types(self.fixture)

    def test_additional_source_is_rejected(self):
        (self.root / 'interfaces/Injected.sol').write_text('pragma solidity >=0.5.0;\n')
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            validate_imported_types(self.fixture)


if __name__ == '__main__':
    unittest.main()
