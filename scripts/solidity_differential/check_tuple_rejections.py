"""Located acceptance and rejection controls for tuple-local/helper lowering."""
import argparse
import json
from pathlib import Path
import subprocess
from solidity_differential.engine import HarnessError, write_json

# Each negative control is valid Solidity; `at` identifies its exact first
# unsupported AST node, including unsupported syntax in an unselected branch.
CASES = [
 ('literal', '', '(uint256 a, uint256 b) = (x, x + 1); return a + b;', None, None),
 ('skipped', '', '(uint256 a, , uint256 b) = (x, 100 / (x + 1), x + 1); return a + b;', None, None),
 ('mutable', '', '(uint256 a, uint256 b) = (x, x + 1); a = b; b = 7; return a + b;', None, None),
 ('conditional', '', '(uint256 a, uint256 b) = x == 0 ? (uint256(1), uint256(2)) : (100 / x, x); return a + b;', None, None),
 ('helper', 'function h(uint256 y) internal pure returns (uint256, uint256) { if(y == 0) return (1, 2); return (y, y + 1); }', '(uint256 a, uint256 b) = h(x); return a + b;', None, None),
 ('helper-effect', 'uint256 stored; function h(uint256 y) internal returns (uint256, uint256) { stored = y; return (stored, stored + 1); }', '(uint256 a, uint256 b) = h(x); return a + b;', None, None),
 ('direct-public', 'function h(uint256 y) public pure returns (uint256, uint256) { return (y, y + 1); }', '(uint256 a, uint256 b) = h(x); return a + b;', None, None),
 ('external-public', 'function h(uint256 y) public pure returns (uint256, uint256) { return (y, y); }', '(uint256 a, uint256 b) = this.h(x); return a + b;', 'multi-value calls require an internal helper or direct public call', 'this.h(x)'),
 ('library-public', 'library L { function h(uint256 y) public pure returns (uint256, uint256) { return (y, y); } }', '(uint256 a, uint256 b) = L.h(x); return a + b;', 'multi-value calls require an internal helper or direct public call', 'L.h(x)'),
 ('named', 'function h(uint256 y) internal pure returns (uint256 named, uint256 second) { return (y, y); }', '(uint256 a, uint256 b) = h(x); return a + b;', 'named multi-value helper results are unsupported', 'uint256 named'),
 ('reference-local', '', '(bytes memory a, uint256 b) = (abi.encode(x), x); return b;', 'tuple component of type bytes is outside this slice', 'bytes memory a'),
 ('signed-local', '', '(int256 a, uint256 b) = (int256(x), x); return b;', 'tuple component of type int256 is outside this slice', 'int256 a'),
 ('inline-array', '', '(uint256[2] memory a, uint256 b) = ([x, x], x); return b;', 'tuple component of type uint256[2] is outside this slice', 'uint256[2] memory a'),
 ('component-effect', 'uint256 stored; function bump(uint256 y) internal returns (uint256) { stored = y; return y; }', '(uint256 a, uint256 b) = (bump(x), x); return a + b;', 'stateful tuple components require explicit evaluation-order support', 'bump(x)'),
 ('skipped-effect', 'uint256 stored; function bump(uint256 y) internal returns (uint256) { stored = y; return y; }', '(uint256 a, , uint256 b) = (x, bump(x), x); return a + b;', 'stateful tuple components require explicit evaluation-order support', 'bump(x)'),
 ('argument-effect', 'uint256 stored; function bump(uint256 y) internal returns (uint256) { stored = y; return y; } function h(uint256 y) internal pure returns (uint256, uint256) { return (y, y); }', '(uint256 a, uint256 b) = h(bump(x)); return a + b;', 'stateful helper call arguments require explicit evaluation-order support', 'bump(x)'),
 ('dead-effect', 'uint256 stored; function bump(uint256 y) internal returns (uint256) { stored = y; return y; }', '(uint256 a, uint256 b) = true ? (x, x) : (bump(x), x); return a + b;', 'stateful tuple components require explicit evaluation-order support', 'bump(x)'),
 ('missing-path', 'function h(uint256 y) internal pure returns (uint256, uint256) { if(y > 0) return (y, y); }', '(uint256 a, uint256 b) = h(x); return a + b;', 'inlined tuple helper does not return on every path', 'if(y > 0)'),
 ('assembly', 'function h(uint256 y) internal pure returns (uint256, uint256) { assembly { let z := y } return (y, y); }', '(uint256 a, uint256 b) = h(x); return a + b;', 'assembly results of multi-value helpers are unsupported', 'assembly {'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    out = parser.parse_args().output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    for name, declarations, body, diagnostic, at in CASES:
        directory = out / name
        directory.mkdir()
        prefix = declarations if declarations.startswith('library ') else ''
        inside = '' if prefix else declarations
        source = 'pragma solidity 0.8.34;\n' + prefix + '\ncontract C {\n' + inside + '\nfunction f(uint256 x) external returns (uint256) {\n' + body + '\n}\n}\n'
        (directory / 'Case.sol').write_text(source)
        driver = directory / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\nopen Compiler.CompilationModel\n'
          f'solidity_import tested from {json.dumps(str(directory))} entry "Case.sol"\n'
          ' using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
          ' contract C\n function f(uint256)\n')
        result = subprocess.run(['lake', 'env', 'lean', str(driver)], text=True,
          capture_output=True, timeout=180)
        log = result.stdout + result.stderr
        (directory / 'import.log').write_text(log)
        location = None
        if diagnostic is None:
            if result.returncode:
                raise HarnessError(f'{name}: positive control failed: {log}')
        else:
            assert source.count(at) == 1, (name, at)
            offset = source.index(at)
            line = source.count('\n', 0, offset) + 1
            column = offset - source.rfind('\n', 0, offset)
            location = f'Case.sol:{line}:{column}:'
            if result.returncode == 0 or diagnostic not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {diagnostic}: {log}')
        results.append(dict(case=name, exit=result.returncode, diagnostic=diagnostic, location=location))
        write_json(out / 'results.json', results)
    write_json(out / 'complete.json', dict(exit=0, cases=len(CASES)))
    print(f'{len(CASES)} tuple acceptance/rejection controls pass')

if __name__ == '__main__':
    main()
