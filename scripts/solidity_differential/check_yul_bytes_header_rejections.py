"""Located near misses for immutable bytes-header Yul observations."""
import argparse
import json
from pathlib import Path
import subprocess
from .engine import HarnessError, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    out = parser.parse_args().output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cases = [
        ('header', 'mload(buffer)', None),
        ('free-pointer', 'mload(0x40)', 'Yul mload currently requires an immutable bytes object'),
        ('scalar-address', 'mload(input)', 'Yul mload currently requires an immutable bytes object'),
        ('payload-address', 'mload(add(buffer, 32))', 'Yul mload currently requires an immutable bytes object'),
        ('header-arithmetic', 'mload(add(buffer, 0))', 'Yul mload currently requires an immutable bytes object'),
        ('nested-load', 'mload(mload(buffer))', 'Yul mload currently requires an immutable bytes object'),
        ('object-pointer', 'buffer', 'unbound Yul identifier buffer'),
    ]
    results = []
    for name, expression, diagnostic in cases:
        project = out / name
        project.mkdir()
        source = ('pragma solidity 0.8.34;\ncontract C {\n'
          'function h(uint256 input) internal pure returns (uint256 result) {\n'
          'bytes memory buffer = abi.encode(input);\n'
          'assembly { result := ' + expression + ' }\n}\n'
          'function f(uint256 input) external pure returns (uint256) { return h(input); }\n}\n')
        (project / 'Case.sol').write_text(source)
        driver = project / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\nopen Compiler.CompilationModel\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
            ' using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            ' contract C\n function f(uint256)\n')
        result = subprocess.run(['lake', 'env', 'lean', str(driver)], capture_output=True,
                                text=True, timeout=180)
        log = result.stdout + result.stderr
        (project / 'import.log').write_text(log)
        if diagnostic is None:
            if result.returncode:
                raise HarnessError('header positive control failed: ' + log)
        else:
            offset = source.index('assembly { result := ') + len('assembly { result := ')
            if expression.startswith('mload('):
                offset += 6
            line = source.count('\n', 0, offset) + 1
            column = offset - source.rfind('\n', 0, offset)
            location = f'Case.sol:{line}:{column}:'
            if result.returncode == 0 or diagnostic not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {diagnostic}: {log}')
        results.append({'case': name, 'exit': result.returncode, 'diagnostic': diagnostic})
        write_json(out / 'results.json', results)
    write_json(out / 'complete.json', {'exit': 0, 'cases': len(cases)})
    print(f'{len(cases)} bytes-header acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
