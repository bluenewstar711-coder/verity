"""Compare generated nested dynamic struct ABI variants using public Denote and real EVMs."""
import argparse
import json
import shutil
from pathlib import Path
import sys
from .engine import command, write_json, HarnessError
from .programs import nested_dynamic_struct_abi_source
from .check_storage import canonical_observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path('Contracts/SolidityImportSmoke/NestedDynamicStructAbi.sol').read_text()
    template = Path('Contracts/SolidityImportSmoke/NestedDynamicStructAbiModel.lean').read_text()
    anchor = 'from "Contracts/SolidityImportSmoke" entry "NestedDynamicStructAbi.sol"'
    if template.count(anchor) != 1:
        raise HarnessError('nonunique ABI source anchor')
    baseline = None
    for variant in ('baseline', 'condition', 'bindings', 'collision'):
        directory = output / variant
        directory.mkdir()
        shutil.copytree(Path('Contracts/SolidityImportSmoke/imported-types'), directory / 'imported-types')
        fixture = directory / 'NestedDynamicStructAbi.sol'
        fixture.write_text(nested_dynamic_struct_abi_source(source, variant))
        if variant == 'collision' and fixture.read_text().count('_verity_slice_tmp_0_memory = flag') != 12:
            raise HarnessError('collision variant must use the actual first decoder name')
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "NestedDynamicStructAbi.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_nested_dynamic_struct_abi',
            '--source-fixture', fixture, '--model-driver', driver,
            '--output', directory / 'campaign'], timeout=1800, log=directory / 'check.log')
        if variant == 'collision':
            yul = (directory / 'campaign/model.yul').read_text()
            if yul.count('let _verity_slice_tmp_1_memory := mload(64)') != 6:
                raise HarnessError('all six memory decoders must avoid the colliding source name')
        report = json.loads((directory / 'campaign/campaign.json').read_text())
        if len(report['transactions']) != 408:
            raise HarnessError('incomplete ABI variant control matrix')
        observable = {'transactions': report['transactions'],
            'observations': canonical_observations(report['observations'])}
        if baseline is None:
            baseline = observable
        elif baseline != observable:
            write_json(output / 'metamorphic-divergence.json',
                {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise HarnessError('ABI variant changed observable behavior')
    write_json(output / 'complete.json', {'exit': 0, 'variants': 4, 'cases': 1632})
    print(f'All nested dynamic struct ABI variants agree: {output}')


if __name__ == '__main__':
    main()
