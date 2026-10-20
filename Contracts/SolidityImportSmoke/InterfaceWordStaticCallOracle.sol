// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). Constructor-only
// configuration; every runtime call enters the fallback. The response word is
// `value ^ (fold & mask)`, where `fold` mixes the calldata size, the selector and
// every 32-byte calldata word in order, so selector, argument values, argument
// order and calldata length are all observable through a nonzero mask.
contract WordStaticOracle {
    uint256 private value;
    bool private failed;
    uint256 private length;
    uint256 private mask;

    constructor(uint256 v, bool f, uint256 n, uint256 m) {
        value = v;
        failed = f;
        length = n;
        mask = m;
    }

    fallback() external {
        uint256 v = value;
        bool f = failed;
        uint256 n = length;
        uint256 m = mask;
        assembly ("memory-safe") {
            let size := calldatasize()
            let acc := add(mul(size, 31), shr(224, calldataload(0)))
            for { let offset := 4 } lt(offset, size) { offset := add(offset, 32) } {
                acc := add(mul(acc, 31), calldataload(offset))
            }
            mstore(0, xor(v, and(acc, m)))
            if f { revert(0, n) }
            return(0, n)
        }
    }
}
