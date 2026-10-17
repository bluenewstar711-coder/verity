// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant UNIT = 1e18;
uint256 constant RATE_SCALE = 1e12;

library MulDivLib {
    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }
}

library MinCastLib {
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := xor(x, mul(xor(x, y), lt(y, x)))
        }
    }

    function toUint128(uint256 x) internal pure returns (uint128) {
        require(x <= type(uint128).max, "max uint128 exceeded");
        return uint128(x);
    }
}

contract SequenceFixture {
    using MulDivLib for uint256;
    using MulDivLib for uint128;
    using MinCastLib for uint128;

    error ConfigUninitialized();
    error StepBlocked(bytes32 id, address user, uint128 balance);

    event EntryUpdated(
        bytes32 indexed id,
        address indexed user,
        uint256 balanceDelta,
        uint256 reserveDelta,
        uint256 accrued
    );

    struct Entry {
        uint128 balance;
        uint128 reserve;
        uint128 lastUpdate;
        uint128[2] slots;
    }

    struct RateConfig {
        uint128 decay;
        uint16 rate0;
        uint16 rate1;
        uint16 rate2;
        uint8 spacing;
    }

    struct SummaryCard {
        uint128 totalAdded;
        uint64 activeCount;
        uint16[2] bandCounts;
    }

    struct BucketView {
        uint128 shareTotal;
        uint64 tag;
        uint32[2] tiers;
    }

    address private recipient;
    bytes32 private activeKey;
    SummaryCard public summaryCard;
    mapping(bytes32 => BucketView) public bucketView;
    mapping(bytes32 id => RateConfig) private rateConfig;
    mapping(bytes32 id => mapping(address user => Entry)) public entries;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function slotOf(bytes32 id, address user, uint256 index) external view returns (uint128) {
        return entries[id][user].slots[index];
    }

    function interpolatedRate(bytes32 id, uint256 remaining) public view returns (uint256) {
        RateConfig storage _config = rateConfig[id];
        require(_config.spacing > 0, ConfigUninitialized());

        if (remaining >= 30 days) return _config.rate2 * RATE_SCALE;

        (uint256 start, uint256 end, uint256 rateLower, uint256 rateUpper) =
            remaining < 1 days ? (0 days,  1 days, _config.rate0 * RATE_SCALE, _config.rate1 * RATE_SCALE) :
                                      (1 days, 30 days, _config.rate1 * RATE_SCALE, _config.rate2 * RATE_SCALE);

        return (rateLower * (end - remaining) + rateUpper * (remaining - start)) / (end - start);
    }

    function previewEntry(bytes32 id, address user, uint256 horizon)
        public
        view
        returns (uint128, uint128, uint128)
    {
        Entry storage _entry = entries[id][user];
        uint128 _balance = _entry.balance;
        uint256 decayedBalance = uint256(_balance).mulDivDown(
            type(uint128).max - rateConfig[id].decay,
            type(uint128).max
        );
        uint128 _reserve = _entry.reserve;
        uint256 decayedReserve =
            _balance > 0 ? _reserve - uint256(_reserve).mulDivUp(_balance - decayedBalance, _balance) : 0;
        uint256 accrualEnd = MinCastLib.min(block.timestamp, horizon);
        uint128 _lastUpdate = _entry.lastUpdate;
        uint128 charge = (_lastUpdate < horizon && accrualEnd >= _lastUpdate)
            ? uint128(decayedReserve.mulDivDown(accrualEnd - _lastUpdate, horizon - _lastUpdate))
            : 0;
        return (uint128(decayedBalance) - charge, uint128(decayedReserve) - charge, charge);
    }

    function change(uint256 input) external returns (uint256) {
        bytes32 id = bytes32((input + 1) & 1);
        address user = msg.sender;
        address recip = address(0x6000);
        recipient = recip;
        activeKey = id;

        RateConfig storage cfg = rateConfig[id];
        if (cfg.spacing == 0) {
            cfg.spacing = 10;
            cfg.decay = uint128((input & 0xf) * 1_000);
            cfg.rate0 = 10;
            cfg.rate1 = 25;
            cfg.rate2 = 60;
        } else {
            cfg.decay += uint128((input & 0x7) * 100);
        }

        Entry storage entry = entries[id][user];
        uint128 addedBalance = uint128(((input & 0x3f) + 10) * 1_000);
        uint128 addedReserve = uint128(((input & 0xf) + 2) * 100);
        uint256 slotIdx = input & 1;
        entry.slots[slotIdx] = uint128(((input & 0x1f) + 1) * 200);
        uint256 weightSum = uint256(entry.slots[slotIdx]) * (slotIdx + 1);

        uint256 horizon = block.timestamp + ((input % 5) + 1) * 10 days;
        (uint128 viewBalance, uint128 viewReserve, uint128 accrued) = previewEntry(id, user, horizon);
        uint128 newBalance = viewBalance + addedBalance;
        uint128 newReserve = viewReserve + addedReserve;

        entry.balance = newBalance;
        entry.reserve = newReserve;
        entry.lastUpdate = uint128(block.timestamp.zeroFloorSub(10));

        if (input == 21) {
            revert StepBlocked(id, user, newBalance);
        }

        emit EntryUpdated(id, user, addedBalance, addedReserve, accrued);

        // Storage-variable key preludes in 2-key and 1-key struct member writes (=, delete, op=, ++):
        entries[id][recipient].balance = 100;
        entries[id][recipient].balance += accrued + 1;
        delete entries[id][recipient].reserve;

        bucketView[activeKey].tag = 10;
        uint64 prevTag = bucketView[activeKey].tag++;
        uint128 nextShareTotal = ++bucketView[activeKey].shareTotal;
        bucketView[activeKey].tiers[input & 1] = uint32(newBalance & 0xffff);

        summaryCard.totalAdded += newBalance;
        summaryCard.activeCount += 1;
        summaryCard.bandCounts[input & 1] = uint16((accrued & 0xff) + 1);

        uint256 remainingTime = ((input % 3) * 15 days) + 12 hours;
        uint256 rateValue = interpolatedRate(id, remainingTime);

        uint256 summary;
        unchecked {
            summary =
                uint256(newBalance) +
                uint256(newReserve) +
                uint256(accrued) +
                uint256(entries[id][recipient].balance) +
                uint256(prevTag) +
                uint256(nextShareTotal) +
                rateValue +
                weightSum;
        }

        bytes32 digest = bytes32(
            uint256(id) ^
            (summary << 12) ^
            (rateValue << 4) ^
            weightSum
        );
        uint256 metric = (uint256(digest) & 0xffffffff) + (summary & 0xffffffff);
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, "PSM: rollback");
        return totalScore;
    }

    function fail() external {
        recipient = address(0xBEEF);
        totalScore += 777;
        revert("PSM: fail");
    }

    function read() external view returns (uint256, bytes32, bytes32, address) {
        return (totalScore, lastDigest, activeKey, recipient);
    }
}
