// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 indexed digest);
    function digest(uint256 input) internal pure returns (uint256 result) {
        bytes memory buffer = abi.encode(input);
        bytes memory aliasBuffer = buffer;
        if (input % 2 == 0) {
            bytes memory buffer = abi.encodePacked(hex"010203", aliasBuffer);
            assembly { result := add(mload(buffer), input) }
        } else {
            bytes memory buffer = abi.encodePacked(hex"ff", aliasBuffer, aliasBuffer);
            assembly { result := add(input, mload(buffer)) }
        }
        bytes memory emptyBuffer = abi.encodePacked(hex"");
        assembly { result := add(result, add(mload(aliasBuffer), mload(emptyBuffer))) }
        assembly { result := add(result, mload(buffer)) }
    }
    function change(uint256 input) external returns (uint256) {
        uint256 result = digest(input);
        value = result;
        emit Changed(result);
        require(input != 20, "header rollback");
        return result;
    }
    function fail() external {
        value = digest(1);
        emit Changed(value);
        require(false, "header fail");
    }
    function read() external view returns (uint256) { return value; }
}
