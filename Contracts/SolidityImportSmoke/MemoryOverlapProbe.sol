// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// A manually modeled engine probe. Raw overlapping pointers are not admitted
// by solidity_import; this must not be described as an imported fixture.
contract MemoryOverlapProbe {
    function read() external pure returns (uint256 result) {
        assembly {
            mstore(0, not(0))
            mstore(1, 0)
            result := mload(0)
        }
    }
}
