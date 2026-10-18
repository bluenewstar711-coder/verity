// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {NestedRecord} from "../interfaces/INestedRecord.sol";

/// Hashes a complete dynamic struct behind a fixed creation-code prefix, the
/// CREATE2-style key derivation pattern: an 85-byte outer packed preimage over
/// a nested packed buffer containing `abi.encode` of the whole root.
library RecordHashLib {
    error CodeDeploymentFailed();

    /// @dev Creation-code prefix that returns the appended data as runtime code.
    /// hex       opcode          stack              comments
    /// ------------------------------------------------------------------------------
    /// 60 0b     PUSH1 0x0b      [11]               11 = length(prefix)
    /// 38        CODESIZE        [codesize, 11]
    /// 03        SUB             [len]              with len = codesize - 11
    /// 80        DUP1            [len, len]
    /// 60 0b     PUSH1 0x0b      [11, len, len]     code offset = 11
    /// 5f        PUSH0           [0, 11, len, len]  mem offset = 0
    /// 39        CODECOPY        [len]              mem[0:len] <- code[11:11+len]
    /// 5f        PUSH0           [0, len]           return offset = 0
    /// f3        RETURN          []                 mem[0:len] is returned
    bytes constant CODE_PREFIX = hex"600b380380600b5f395ff3";

    function toKey(NestedRecord memory record) internal pure returns (bytes32) {
        // The fixed-size prefix makes the packed encoding unambiguous.
        return keccak256(
            abi.encodePacked(
                uint8(0xff),
                record.origin,
                uint256(0),
                keccak256(abi.encodePacked(CODE_PREFIX, abi.encode(record)))
            )
        );
    }

    /// @dev Deploys the record as code at the address given by its key's last 20 bytes.
    function deployAsCode(NestedRecord memory record) internal returns (address deployed) {
        bytes memory creationCode = abi.encodePacked(CODE_PREFIX, abi.encode(record));
        assembly ("memory-safe") {
            deployed := create2(0, add(creationCode, 0x20), mload(creationCode), 0)
        }
        require(deployed != address(0), CodeDeploymentFailed());
    }
}
