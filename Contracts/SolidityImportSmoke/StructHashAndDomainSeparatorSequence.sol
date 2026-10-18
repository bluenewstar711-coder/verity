// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant MAX_HEIGHT = 3;

bytes32 constant RECORD_ITEM_TYPEHASH =
    keccak256("RecordItem(address token,uint256 weight,uint256 cursor,address source)");

bytes32 constant RECORD_TYPEHASH = keccak256(
    "NestedRecord(uint256 head,address origin,address token,RecordItem[] items,uint256 deadline,uint256 threshold,address firstGate,address secondGate)RecordItem(address token,uint256 weight,uint256 cursor,address source)"
);

bytes32 constant ENVELOPE_TYPEHASH = keccak256(
    "Envelope(NestedRecord record,bool flag,address sender,uint256 start,uint256 expiry,uint256 step,bytes32 group,address hook,bytes payload,address receiver,address validator,bool limited,uint128 maxUnits,uint128 maxAmount,uint256 rateCap)RecordItem(address token,uint256 weight,uint256 cursor,address source)NestedRecord(uint256 head,address origin,address token,RecordItem[] items,uint256 deadline,uint256 threshold,address firstGate,address secondGate)"
);

bytes32 constant PRICE_VERIFIER_ENVELOPE_TYPEHASH = keccak256(
    "PriceVerifierEnvelope(Envelope envelope,address allowedCaller)RecordItem(address token,uint256 weight,uint256 cursor,address source)NestedRecord(uint256 head,address origin,address token,RecordItem[] items,uint256 deadline,uint256 threshold,address firstGate,address secondGate)Envelope(NestedRecord record,bool flag,address sender,uint256 start,uint256 expiry,uint256 step,bytes32 group,address hook,bytes payload,address receiver,address validator,bool limited,uint128 maxUnits,uint128 maxAmount,uint256 rateCap)"
);

bytes32 constant RATE_VERIFIER_ENVELOPE_TYPEHASH = keccak256(
    "RateVerifierEnvelope(Envelope envelope,uint256 rate,address allowedCaller)RecordItem(address token,uint256 weight,uint256 cursor,address source)NestedRecord(uint256 head,address origin,address token,RecordItem[] items,uint256 deadline,uint256 threshold,address firstGate,address secondGate)Envelope(NestedRecord record,bool flag,address sender,uint256 start,uint256 expiry,uint256 step,bytes32 group,address hook,bytes payload,address receiver,address validator,bool limited,uint128 maxUnits,uint128 maxAmount,uint256 rateCap)"
);

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

library HashLib {
    error TreeTooHigh();

    function envelopeTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("EnvelopeTree(Envelope root,uint256 nonce)");
        if (height == 1) return keccak256("EnvelopeTree(Envelope[2] root,uint256 nonce)");
        if (height == 2) return keccak256("EnvelopeTree(Envelope[2][2] root,uint256 nonce)");
        if (height == 3) return keccak256("EnvelopeTree(Envelope[2][2][2] root,uint256 nonce)");
        revert TreeTooHigh();
    }

    function priceVerifierEnvelopeTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("PriceVerifierEnvelopeTree(PriceVerifierEnvelope root,uint256 maxBlockNumber)");
        if (height == 1) return keccak256("PriceVerifierEnvelopeTree(PriceVerifierEnvelope[2] root,uint256 maxBlockNumber)");
        if (height == 2) return keccak256("PriceVerifierEnvelopeTree(PriceVerifierEnvelope[2][2] root,uint256 maxBlockNumber)");
        if (height == 3) return keccak256("PriceVerifierEnvelopeTree(PriceVerifierEnvelope[2][2][2] root,uint256 maxBlockNumber)");
        revert TreeTooHigh();
    }

    function rateVerifierEnvelopeTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("RateVerifierEnvelopeTree(RateVerifierEnvelope root,uint256 maxBlockNumber)");
        if (height == 1) return keccak256("RateVerifierEnvelopeTree(RateVerifierEnvelope[2] root,uint256 maxBlockNumber)");
        if (height == 2) return keccak256("RateVerifierEnvelopeTree(RateVerifierEnvelope[2][2] root,uint256 maxBlockNumber)");
        if (height == 3) return keccak256("RateVerifierEnvelopeTree(RateVerifierEnvelope[2][2][2] root,uint256 maxBlockNumber)");
        revert TreeTooHigh();
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

    function hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32) {
        return keccak256(abi.encode(left, right));
    }

    function hashRecordItem(RecordItem memory items) internal pure returns (bytes32) {
        return keccak256(
            abi.encode(
                RECORD_ITEM_TYPEHASH,
                items.token,
                items.weight,
                items.cursor,
                items.source
            )
        );
    }

    function hashRecord(NestedRecord memory record) internal pure returns (bytes32) {
        bytes memory encodedItems;
        for (uint256 i = 0; i < record.items.length; i++) {
            encodedItems = bytes.concat(
                encodedItems,
                hashRecordItem(record.items[i])
            );
        }

        return keccak256(
            abi.encode(
                RECORD_TYPEHASH,
                record.head,
                record.origin,
                record.token,
                keccak256(encodedItems),
                record.deadline,
                record.threshold,
                record.firstGate,
                record.secondGate
            )
        );
    }

    function hashEnvelope(Envelope memory envelope) internal pure returns (bytes32) {
        return keccak256(
            abi.encode(
                ENVELOPE_TYPEHASH,
                hashRecord(envelope.record),
                envelope.flag,
                envelope.sender,
                envelope.start,
                envelope.expiry,
                envelope.step,
                envelope.group,
                envelope.hook,
                keccak256(envelope.payload),
                envelope.receiver,
                envelope.validator,
                envelope.limited,
                envelope.maxUnits,
                envelope.maxAmount,
                envelope.rateCap
            )
        );
    }

    function hashPriceVerifierEnvelope(Envelope memory envelope, address allowedCaller) internal pure returns (bytes32) {
        return keccak256(abi.encode(PRICE_VERIFIER_ENVELOPE_TYPEHASH, hashEnvelope(envelope), allowedCaller));
    }

    function hashRateVerifierEnvelope(Envelope memory envelope, uint256 rate, address allowedCaller) internal pure returns (bytes32) {
        return keccak256(abi.encode(RATE_VERIFIER_ENVELOPE_TYPEHASH, hashEnvelope(envelope), rate, allowedCaller));
    }
}

contract SequenceFixture {
    bytes32 internal constant EIP712_DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(uint256 head,address verifyingContract)");
    bytes32 internal constant ENTER_TYPEHASH =
        keccak256("Enter(bytes32 recordId,address sender,address receiver,uint256 maxExpiry,uint256 nonce)");

    mapping(bytes32 => uint256) private envelopeCounts;
    mapping(address => uint256) private nonces;
    bytes32 private lastEnvelopeDigest;
    bytes32 private lastRecordHash;
    uint256 private lastPayloadLen;

    function DOMAIN_SEPARATOR() public view returns (bytes32) {
        return keccak256(abi.encode(EIP712_DOMAIN_TYPEHASH, block.chainid, address(this)));
    }

    function change(uint256 input) external returns (uint256, uint256) {
        if (input == 19) {
            return (uint256(HashLib.envelopeTreeTypeHash(MAX_HEIGHT + 1)), 0);
        }
        if (input == 21) {
            return (0, uint256(HashLib.priceVerifierEnvelopeTreeTypeHash(MAX_HEIGHT + 1)));
        }
        if (input == 23) {
            return (uint256(HashLib.rateVerifierEnvelopeTreeTypeHash(MAX_HEIGHT + 1)), 0);
        }

        uint256 height = input % (MAX_HEIGHT + 1);
        bytes32 treeHash = HashLib.envelopeTreeTypeHash(height);
        bytes32 priceTreeHash = HashLib.priceVerifierEnvelopeTreeTypeHash(height);
        bytes32 rateTreeHash = HashLib.rateVerifierEnvelopeTreeTypeHash(height);
        bytes32 combinedTree = HashLib.hashNode(treeHash, HashLib.hashNode(priceTreeHash, rateTreeHash));

        RecordItem memory item = RecordItem({
            token: address(uint160(0x1000 + (input % 7))),
            weight: 8000 + (input % 500),
            cursor: 2000 + (input % 300),
            source: address(uint160(0x2000 + (input % 5)))
        });
        bytes32 itemHash = HashLib.hashRecordItem(item);

        uint256 nonce = nonces[msg.sender]++;
        uint256 maxExpiry = block.timestamp + height;
        bytes32 enterStructHash = keccak256(
            abi.encode(ENTER_TYPEHASH, combinedTree, msg.sender, item.token, maxExpiry, nonce)
        );
        bytes32 enterDigest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), enterStructHash));

        envelopeCounts[combinedTree] += 1;
        lastEnvelopeDigest = enterDigest;
        lastRecordHash = itemHash;
        lastPayloadLen = height;

        require(input != 20, "envelope hash rollback");
        return (
            (uint256(enterDigest) & 0xFFFFFFFFFFFFFFFF) + envelopeCounts[combinedTree] + nonce,
            (uint256(itemHash) & 0xFFFFFFFFFFFFFFFF) + height
        );
    }

    function fail() external {
        nonces[msg.sender] = 999;
        lastEnvelopeDigest = bytes32(uint256(888));
        lastRecordHash = HashLib.envelopeTreeTypeHash(MAX_HEIGHT + 2);
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        bytes32 dom = DOMAIN_SEPARATOR();
        return (
            uint256(lastEnvelopeDigest) & 0xFFFFFFFFFFFFFFFF,
            uint256(lastRecordHash) & 0xFFFFFFFFFFFFFFFF,
            nonces[msg.sender] + lastPayloadLen * 100,
            uint256(dom) & 0xFFFFFFFFFFFFFFFF
        );
    }

    function inspectEnvelopeMem(Envelope memory envelope, uint256 rate) external returns (uint256, uint256) {
        bytes32 rHash = HashLib.hashRateVerifierEnvelope(envelope, rate, envelope.validator);
        bytes32 digest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), rHash));

        uint256 itemBonus = envelope.record.items.length;
        if (itemBonus > 0) {
            RecordItem memory firstItem = envelope.record.items[0];
            itemBonus += firstItem.weight + (uint256(HashLib.hashRecordItem(firstItem)) & 0xFFFF);
        }

        uint256 payloadBonus = envelope.payload.length + (uint256(keccak256(envelope.payload)) & 0xFFFF);
        uint256 flagBonus = (envelope.flag ? 10 : 20) + (envelope.limited ? 100 : 200)
            + uint256(envelope.maxUnits) + uint256(envelope.maxAmount) + envelope.record.head;

        envelopeCounts[rHash] += 1;
        lastEnvelopeDigest = digest;
        lastRecordHash = rHash;
        lastPayloadLen = envelope.payload.length;

        return (
            (uint256(digest) & 0xFFFFFFFFFFFFFFFF)
                + itemBonus
                + envelopeCounts[rHash],
            (uint256(rHash) & 0xFFFFFFFFFFFFFFFF)
                + payloadBonus
                + flagBonus
        );
    }

    function inspectEnvelopeCd(Envelope calldata envelope, uint256 rate, address allowedCaller) external returns (uint256, uint256) {
        bytes32 mHash = HashLib.hashRecord(envelope.record);
        bytes32 pHash = HashLib.hashPriceVerifierEnvelope(envelope, allowedCaller);
        bytes32 digest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), pHash));

        uint256 itemBonus = envelope.record.items.length;
        if (itemBonus > 0) {
            RecordItem memory firstItem = envelope.record.items[0];
            itemBonus += firstItem.cursor + (uint256(HashLib.hashRecordItem(firstItem)) & 0xFFFF);
        }

        uint256 payloadBonus = envelope.payload.length + (uint256(keccak256(envelope.payload)) & 0xFFFF) + rate;
        uint256 flagBonus = (envelope.flag ? 1 : 2) + (envelope.limited ? 3 : 4)
            + uint256(envelope.maxUnits) + uint256(envelope.maxAmount) + envelope.record.deadline;

        envelopeCounts[pHash] += 1;
        lastEnvelopeDigest = digest;
        lastRecordHash = mHash;
        lastPayloadLen = envelope.payload.length;

        return (
            (uint256(digest) & 0xFFFFFFFFFFFFFFFF)
                + itemBonus
                + envelopeCounts[pHash],
            (uint256(mHash) & 0xFFFFFFFFFFFFFFFF)
                + payloadBonus
                + flagBonus
        );
    }
}
