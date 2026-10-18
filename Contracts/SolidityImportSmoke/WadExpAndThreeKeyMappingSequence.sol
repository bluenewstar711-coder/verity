// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

int256 constant LN_LEVEL_BASE = 0.004987541511039073e18; // floor(ln(1.005) * 1e18)
uint256 constant MAX_LEVEL = 6744;
uint256 constant RATIO_ROUNDING_STEP = 1e11;

library WadExpLib {
    using WadExpLib for uint256;

    error RatioAboveOne();
    error LevelOutOfRange();

    function divHalfDownUnchecked(uint256 x, uint256 d) internal pure returns (uint256) {
        unchecked {
            return (x + (d - 1) / 2) / d;
        }
    }

    function wadExp(int256 x) internal pure returns (uint256) {
        unchecked {
            if (x < 0) {
                return 1e36 / wadExp(-x);
            } else {
                int256 ln2 = 0.693147180559945309e18; // floor(ln(2) * 1e18)
                int256 offset = 0.32261121498945987e18;
                int256 q = (x + offset) / ln2;
                int256 r = x - q * ln2;
                int256 secondTerm = r * r / (2 * 1e18);
                int256 thirdTerm = secondTerm * r / (3 * 1e18);
                int256 expR = 1e18 + r + secondTerm + thirdTerm;
                return uint256(expR) << uint256(q);
            }
        }
    }

    function levelToRatio(uint256 level) internal pure returns (uint256) {
        require(level <= MAX_LEVEL, LevelOutOfRange());
        unchecked {
            return uint256(1e36)
                    .divHalfDownUnchecked(1e18 + wadExp(LN_LEVEL_BASE * (int256(MAX_LEVEL / 2) - int256(level))))
                    .divHalfDownUnchecked(RATIO_ROUNDING_STEP) * RATIO_ROUNDING_STEP;
        }
    }

    function ratioToLevel(uint256 ratio, uint256 spacing) internal pure returns (uint256) {
        require(ratio <= 1e18, RatioAboveOne());
        uint256 low = 0;
        uint256 high = MAX_LEVEL;
        while (low != high) {
            unchecked {
                uint256 mid = (low + high) / 2;
                if (levelToRatio(mid) < ratio) low = mid + 1;
                else high = mid;
            }
        }
        return (low + spacing - 1) / spacing * spacing;
    }
}

contract SequenceFixture {
    enum Party {
        First,
        Second
    }

    struct Quota {
        uint128 limit;
        uint64 used;
        bool active;
    }

    uint16[4] private feeTiers;
    uint256[3] private epochCaps;
    mapping(Party => mapping(address => mapping(address => uint256))) private nonces;
    mapping(bytes32 => mapping(address => mapping(uint256 => bool))) private approvals;
    mapping(bytes32 => mapping(address => mapping(uint256 => Quota))) private quotas;
    uint256 private lastRatio;
    uint256 private lastLevel;

    function change(uint256 input) external returns (uint256, uint256) {
        if (input == 19) {
            return (WadExpLib.levelToRatio(MAX_LEVEL + 1), 0);
        }
        if (input == 21) {
            return (0, WadExpLib.ratioToLevel(1e18 + 1, 8));
        }

        uint256 rawLevel = (input * 337) % (MAX_LEVEL + 1);
        uint256 spacing = (input % 2 == 0) ? 8 : 24;
        uint256 alignedLevel = (rawLevel / spacing) * spacing;
        uint256 ratio = WadExpLib.levelToRatio(alignedLevel);
        uint256 recoveredLevel = WadExpLib.ratioToLevel(ratio, spacing);
        lastRatio += ratio;
        lastLevel += recoveredLevel;

        uint256 idx4 = input % feeTiers.length;
        uint256 idx3 = input % epochCaps.length;
        feeTiers[0] = uint16(100 + (input % 50));
        feeTiers[1] = uint16(200 + (input % 50));
        feeTiers[2] = uint16(300 + (input % 50));
        feeTiers[3] = uint16(400 + (input % 50));
        delete feeTiers[1];
        feeTiers[idx4] = feeTiers[idx4] + uint16(recoveredLevel % 100);
        uint16[4] memory snapFees = feeTiers;
        feeTiers[0] = uint16(snapFees[0] + uint16(snapFees.length));

        epochCaps[0] = 10 + (input % 7);
        epochCaps[1] = 20 + (input % 7);
        epochCaps[2] = 30 + (input % 7);
        if (input % 5 == 4) {
            delete epochCaps;
        }
        epochCaps[idx3] = epochCaps[idx3] + (ratio / 1e11 + epochCaps.length);
        uint256[3] memory snapCaps = epochCaps;

        address delegate = address(uint160(0xBEEF + (input % 3)));
        Party side = (input % 2 == 0) ? Party.First : Party.Second;
        nonces[side][msg.sender][delegate] += 1;
        uint256 nAfterInc = ++nonces[side][msg.sender][delegate];
        if (input % 7 == 6) {
            delete nonces[Party.Second][msg.sender][delegate];
        }

        bytes32 groupId = bytes32(uint256(0xA11CE + (input % 2)));
        uint256 bucket = input % 3;
        approvals[groupId][msg.sender][bucket] = (input % 3 != 0);
        if (input % 4 == 3) {
            delete approvals[groupId][msg.sender][(bucket + 1) % 3];
        }

        quotas[groupId][msg.sender][bucket] = Quota({
            limit: uint128(1000 + ratio / 1e12),
            used: uint64(recoveredLevel + nAfterInc),
            active: true
        });
        Quota storage q = quotas[groupId][msg.sender][bucket];
        q.used += uint64(snapFees[idx4]);
        Quota memory qSnap = quotas[groupId][msg.sender][bucket];
        if (input % 6 == 5) {
            delete quotas[groupId][msg.sender][(bucket + 2) % 3];
        }

        require(input != 20, "wad exp 3key rollback");
        return (
            ratio + snapCaps[0] + snapCaps[1] + snapCaps[2] + uint256(qSnap.limit),
            recoveredLevel + uint256(qSnap.used) + nonces[side][msg.sender][delegate]
        );
    }

    function fail() external {
        bytes32 groupId = bytes32(uint256(0xA11CE));
        feeTiers[0] = 999;
        epochCaps[0] = 888;
        nonces[Party.First][msg.sender][msg.sender] = 777;
        quotas[groupId][msg.sender][0].limit = 666;
        lastRatio = WadExpLib.levelToRatio(MAX_LEVEL + 5);
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        bytes32 groupId = bytes32(uint256(0xA11CE));
        address d0 = address(uint160(0xBEEF));
        address d1 = address(uint160(0xBEEF + 1));
        uint256 feeSummary =
            uint256(feeTiers[0]) +
            (uint256(feeTiers[1]) << 16) +
            (uint256(feeTiers[2]) << 32) +
            (uint256(feeTiers[3]) << 48);
        uint256 capSummary = epochCaps[0] + epochCaps[1] * 10 + epochCaps[2] * 100;
        uint256 nonceSummary =
            nonces[Party.First][msg.sender][d0] +
            nonces[Party.Second][msg.sender][d1] * 100 +
            (approvals[groupId][msg.sender][0] ? 10000 : 0) +
            (approvals[groupId][msg.sender][1] ? 20000 : 0);
        Quota storage q0 = quotas[groupId][msg.sender][0];
        uint256 quotaSummary =
            lastRatio + lastLevel + uint256(q0.limit) + uint256(q0.used) + (q0.active ? 1 : 0);
        return (feeSummary, capSummary, nonceSummary, quotaSummary);
    }

    function quoteLevelRoundtrip(uint256 level, uint256 spacing) external pure returns (uint256, uint256) {
        uint256 boundedSpacing = spacing == 0 ? 8 : spacing;
        uint256 ratio = WadExpLib.levelToRatio(level);
        uint256 recovered = WadExpLib.ratioToLevel(ratio, boundedSpacing);
        return (ratio, recovered);
    }
}
