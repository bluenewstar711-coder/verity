// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant MAX_HEIGHT = 3;

struct RecordItem {
    address token;
    uint256 weight;
    uint256 cursor;
    address source;
}

struct NestedRecord {
    uint256 head;
    address origin;
    address token;
    RecordItem[] items;
    uint256 deadline;
    uint256 threshold;
    address firstGate;
    address secondGate;
}

struct Envelope {
    NestedRecord record;
    bool flag;
    address sender;
    uint256 start;
    uint256 expiry;
    uint256 step;
    bytes32 group;
    address hook;
    bytes payload;
    address receiver;
    address validator;
    bool limited;
    uint128 maxUnits;
    uint128 maxAmount;
    uint256 rateCap;
}

struct VerifierConfig {
    uint256 minRate;
    address allowedCaller;
    bool active;
    bytes4 tag;
}

library VerifierHashLib {
    error TreeTooHigh();

    function hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32) {
        return keccak256(abi.encode(left, right));
    }

    function computeRoot(bytes32 leafHash, uint256 leafIndex, bytes32[] memory proof) internal pure returns (bytes32) {
        if (proof.length > MAX_HEIGHT) return bytes32(0);
        bytes32 hash = leafHash;
        for (uint256 i = 0; i < proof.length; ++i) {
            bool isRight = (leafIndex >> i) & 1 == 1;
            hash = isRight ? hashNode(proof[i], hash) : hashNode(hash, proof[i]);
        }
        return hash;
    }

    function isLeaf(bytes32 root, bytes32 leafHash, uint256 leafIndex, bytes32[] memory proof) internal pure returns (bool) {
        if (proof.length > MAX_HEIGHT) return false;
        if (leafIndex >= (1 << proof.length)) return false;

        bytes32 hash = leafHash;
        for (uint256 i = 0; i < proof.length; ++i) {
            bool isRight = (leafIndex >> i) & 1 == 1;
            hash = isRight ? hashNode(proof[i], hash) : hashNode(hash, proof[i]);
        }

        return hash == root;
    }
}

contract SequenceFixture {
    error NotTheSender();
    error ExpiredTree();
    error InvalidLeaf();
    error RateTooLow();

    mapping(address => mapping(bytes32 => uint256)) public maxBlockNumber;
    mapping(bytes32 => uint256) private verifiedCounts;
    bytes private storedPayload;
    bytes32 private lastVerifiedRoot;
    uint256 private lastDecodedRate;

    function _decodeStoredHeader() internal view returns (VerifierConfig memory) {
        return abi.decode(storedPayload, (VerifierConfig));
    }

    function _decodeUintArray(bytes memory raw) internal pure returns (uint256[] memory) {
        return abi.decode(raw, (uint256[]));
    }

    function _firstOrZero(uint256[] memory xs) internal pure returns (uint256) {
        return xs.length == 0 ? 0 : xs[0];
    }

    function change(uint256 input) external returns (uint256, uint256) {
        uint256 minRate = 1000 + (input % 500);
        address allowedCaller = address(uint160(0x3000 + (input % 11)));
        bool active = (input & 1) == 0;
        bytes4 tag = bytes4(keccak256(abi.encode(input)));

        bytes memory encodedConfig = abi.encode(minRate, allowedCaller, active, tag);
        storedPayload = encodedConfig;

        VerifierConfig memory cfg = _decodeStoredHeader();
        uint256 directMinRate = abi.decode(encodedConfig, (VerifierConfig)).minRate;

        (uint256 tupRate, , bool tupActive, bytes4 tupTag) =
            abi.decode(storedPayload, (uint256, address, bool, bytes4));

        uint256 shiftedInput = (input % 1000) + 77;
        bytes memory singleBuf = abi.encode(shiftedInput);
        uint256 singleDecoded = abi.decode(singleBuf, (uint256));
        bytes memory arrBuf = abi.encode(uint256(0x20), uint256(1), shiftedInput);
        uint256[] memory arrDecoded = _decodeUintArray(arrBuf);
        uint256 inlineElem = _firstOrZero(abi.decode(arrBuf, (uint256[])));
        uint256 extraWord = singleDecoded + arrDecoded[0] + inlineElem;
        bytes32 root = keccak256(
            abi.encode(cfg.minRate, cfg.allowedCaller, tupActive, tupTag, extraWord)
        );

        maxBlockNumber[msg.sender][root] = block.number + (input % 17);
        verifiedCounts[root] += 1;
        lastVerifiedRoot = root;
        lastDecodedRate = cfg.minRate + directMinRate + tupRate;

        require(input != 20, "validator change rollback");
        return (
            lastDecodedRate + verifiedCounts[root],
            (uint256(root) & 0xFFFFFFFFFFFFFFFF) + maxBlockNumber[msg.sender][root]
        );
    }

    function decodeMixedPayload(bytes calldata raw, uint256 rateFloor) external returns (uint256, uint256) {
        (VerifierConfig memory cfg, uint256[] memory weights, bytes memory extraBytes, string memory label) =
            abi.decode(raw, (VerifierConfig, uint256[], bytes, string));

        if (cfg.minRate < rateFloor) revert RateTooLow();

        uint256 weightSum = weights.length;
        for (uint256 i = 0; i < weights.length; ++i) {
            weightSum += weights[i];
        }

        bytes32 extraHash = keccak256(bytes.concat(extraBytes, bytes(label)));
        uint256 bonus = extraBytes.length + bytes(label).length + (cfg.active ? 11 : 22);

        storedPayload = extraBytes;
        verifiedCounts[extraHash] += 1;
        lastVerifiedRoot = extraHash;
        lastDecodedRate = cfg.minRate + weightSum;

        return (
            lastDecodedRate + bonus + verifiedCounts[extraHash],
            (uint256(extraHash) & 0xFFFFFFFFFFFFFFFF) + (uint256(uint32(cfg.tag)))
        );
    }

    function verifyEnvelopeCd(Envelope calldata envelope, bytes32 root, uint256 actualRate) external returns (uint256, uint256) {
        (uint256 minRate, address allowedCaller, uint256 leafIndex, bytes32[] memory proof) =
            abi.decode(envelope.payload, (uint256, address, uint256, bytes32[]));

        if (allowedCaller != address(0) && allowedCaller != msg.sender) {
            revert NotTheSender();
        }
        if (actualRate < minRate) {
            revert RateTooLow();
        }

        bytes32 leafHash = keccak256(abi.encode(envelope.sender, envelope.step, minRate, allowedCaller));
        bytes32 targetRoot = root == bytes32(0)
            ? VerifierHashLib.computeRoot(leafHash, leafIndex % 8, proof)
            : root;
        if (!VerifierHashLib.isLeaf(targetRoot, leafHash, leafIndex % 8, proof)) {
            revert InvalidLeaf();
        }

        verifiedCounts[targetRoot] += 1;
        lastVerifiedRoot = targetRoot;
        lastDecodedRate = actualRate - minRate + proof.length;

        return (
            lastDecodedRate + verifiedCounts[targetRoot],
            (uint256(leafHash) & 0xFFFFFFFFFFFFFFFF) + envelope.record.items.length
        );
    }

    function fail() external {
        lastDecodedRate = 9999;
        bytes memory badBool = abi.encode(uint256(2));
        bool flag = abi.decode(badBool, (bool));
        if (flag) {
            lastDecodedRate = 1;
        }
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        return (
            uint256(lastVerifiedRoot) & 0xFFFFFFFFFFFFFFFF,
            lastDecodedRate,
            storedPayload.length,
            maxBlockNumber[msg.sender][lastVerifiedRoot]
        );
    }
}
