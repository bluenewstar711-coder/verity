pragma solidity 0.8.34;
import {NestedRecord} from "imported-types/interfaces/INestedRecord.sol";

contract NestedDynamicStructAbi {
    function memoryUnused(NestedRecord memory record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function memoryDeadline(NestedRecord memory record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return record.deadline;
    }
    function memoryTokenLate(NestedRecord memory record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.items[0].token;
    }
    function memoryTokenSecond(NestedRecord memory record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.items[1].token;
    }
    function calldataUnused(NestedRecord calldata record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function calldataDeadline(NestedRecord calldata record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return record.deadline;
    }
    function calldataTokenLate(NestedRecord calldata record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.items[0].token;
    }
    function calldataTokenSecond(NestedRecord calldata record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.items[1].token;
    }
    function memoryOrigin(NestedRecord memory record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.origin;
    }
    function calldataOrigin(NestedRecord calldata record, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return record.origin;
    }
    function memoryLength(NestedRecord memory record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return record.items.length;
    }
    function calldataLength(NestedRecord calldata record, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return record.items.length;
    }
}
