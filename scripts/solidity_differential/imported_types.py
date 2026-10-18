"""Integrity pin for the multi-file imported-type fixtures.

The nested dynamic struct ABI and ABI hashing campaigns import declarations
from `Contracts/SolidityImportSmoke/imported-types/`. Every file's exact bytes
are pinned both here and in that directory's manifest, so editing the manifest
alone cannot authorize changed or additional fixture sources.
"""
import hashlib
import json
from pathlib import Path

DIRECTORY = 'imported-types'
FIXTURE_ID = 'nested-dynamic-struct-imported-types'
PINNED_FILES = {
    'interfaces/INestedRecord.sol': 'e4cc3e6b8d8077e92baf499a79e86cc20c6a046ef954279ed49a787e5f879630',
    'libraries/RecordHashLib.sol': '6f929816145e918bc0fc83d49394c4aafb959f7292eb9efb36e81b9a8b234789',
}


def imported_type_paths(fixture_dir):
    """Absolute paths of the pinned sources and their manifest."""
    root = Path(fixture_dir) / DIRECTORY
    return [root / name for name in PINNED_FILES] + [root / 'manifest.json']


def validate_imported_types(fixture_dir):
    """Reject substituted, edited or additional imported-type sources."""
    root = Path(fixture_dir) / DIRECTORY
    manifest = json.loads((root / 'manifest.json').read_text())
    if manifest.get('fixture') != FIXTURE_ID:
        raise ValueError('imported-type fixture identity differs')
    sources = {p.relative_to(root).as_posix() for p in root.rglob('*.sol')}
    if set(manifest['files']) != set(PINNED_FILES) or sources != set(PINNED_FILES):
        raise ValueError('imported-type inventory differs')
    for name, expected in PINNED_FILES.items():
        if manifest['files'][name] != {'sha256': expected}:
            raise ValueError('imported-type manifest differs')
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError('imported-type bytes differ: ' + name)
    return manifest
