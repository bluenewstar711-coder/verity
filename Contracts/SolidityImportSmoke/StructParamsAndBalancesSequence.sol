// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type Id is bytes32;

struct AssetParams {
    address baseToken;
    address quoteToken;
    address oracle;
    address rateModel;
    uint256 maxRatio;
}

struct Holding {
    uint256 supplyShares;
    uint128 borrowShares;
    uint128 collateral;
}

struct Reserve {
    uint128 totalSupplyAssets;
    uint128 totalSupplyShares;
    uint128 totalBorrowAssets;
    uint128 totalBorrowShares;
    uint128 lastUpdate;
    uint128 fee;
}

uint256 constant WAD = 1e18;

library AssetParamsLib {
    uint256 internal constant ASSET_PARAMS_BYTES_LENGTH = 5 * 32;

    function id(AssetParams memory params) internal pure returns (Id paramsId) {
        assembly ("memory-safe") {
            paramsId := keccak256(params, ASSET_PARAMS_BYTES_LENGTH)
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

    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }
}

library WadMathLib {
    function wMulDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD);
    }

    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function wTaylorCompounded(uint256 x, uint256 n) internal pure returns (uint256) {
        uint256 firstTerm = x * n;
        uint256 secondTerm = mulDivDown(firstTerm, firstTerm, 2 * WAD);
        uint256 thirdTerm = mulDivDown(secondTerm, firstTerm, 3 * WAD);
        return firstTerm + secondTerm + thirdTerm;
    }
}

library ShareConversionLib {
    using WadMathLib for uint256;

    uint256 internal constant VIRTUAL_SHARES = 1e6;
    uint256 internal constant VIRTUAL_ASSETS = 1;

    function toSharesDown(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivDown(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    function toAssetsDown(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivDown(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }

    function toSharesUp(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivUp(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    function toAssetsUp(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivUp(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }
}

contract SequenceFixture {
    using AssetParamsLib for AssetParams;
    using WadMathLib for uint256;
    using ShareConversionLib for uint256;
    using MinCastLib for uint256;

    error ReserveStepBlocked(Id reserveId, uint256 totalSupplyAssets, uint256 totalBorrowAssets);

    event InterestAccrued(Id indexed id, uint256 prevBorrowRate, uint256 interest, uint256 feeShares);

    address public feeRecipient;
    Id public lastReserveId;
    mapping(Id => Reserve) public reserves;
    mapping(Id => mapping(address => Holding)) public holdings;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function _simulatedReserve(Id id, address rateModel, uint256 ratePerSecond) internal view returns (Reserve memory m) {
        m = reserves[id];
        uint256 elapsed = block.timestamp.zeroFloorSub(m.lastUpdate);
        if (elapsed != 0 && m.totalBorrowAssets != 0 && rateModel != address(0)) {
            uint256 interest = uint256(m.totalBorrowAssets).wMulDown(ratePerSecond.wTaylorCompounded(elapsed));
            m.totalBorrowAssets += interest.toUint128();
            m.totalSupplyAssets += interest.toUint128();
            if (m.fee != 0) {
                uint256 feeAmount = interest.wMulDown(m.fee);
                uint256 feeShares =
                    feeAmount.toSharesDown(uint256(m.totalSupplyAssets).zeroFloorSub(feeAmount), m.totalSupplyShares);
                m.totalSupplyShares += feeShares.toUint128();
            }
        }
        ++m.lastUpdate;
    }

    function computeId(AssetParams memory params) external pure returns (Id) {
        return params.id();
    }

    function expectedReserveBalances(AssetParams memory params, uint256 ratePerSecond)
        public
        view
        returns (uint256, uint256, uint256, uint256)
    {
        Id id = params.id();
        Reserve memory m = _simulatedReserve(id, params.rateModel, ratePerSecond);
        return (m.totalSupplyAssets, m.totalSupplyShares, m.totalBorrowAssets, m.totalBorrowShares);
    }

    function expectedTotalSupplyAssets(AssetParams memory params, uint256 ratePerSecond)
        external
        view
        returns (uint256 totalSupplyAssets)
    {
        (totalSupplyAssets,,,) = expectedReserveBalances(params, ratePerSecond);
    }

    function expectedSupplyAssets(AssetParams memory params, address user, uint256 ratePerSecond)
        external
        view
        returns (uint256)
    {
        Id id = params.id();
        uint256 supplyShares = holdings[id][user].supplyShares;
        (uint256 totalSupplyAssets, uint256 totalSupplyShares,,) = expectedReserveBalances(params, ratePerSecond);
        return supplyShares.toAssetsDown(totalSupplyAssets, totalSupplyShares);
    }

    function expectedBorrowAssets(AssetParams memory params, address user, uint256 ratePerSecond)
        external
        view
        returns (uint256)
    {
        Id id = params.id();
        uint256 borrowShares = holdings[id][user].borrowShares;
        (,, uint256 totalBorrowAssets, uint256 totalBorrowShares) = expectedReserveBalances(params, ratePerSecond);
        return borrowShares.toAssetsUp(totalBorrowAssets, totalBorrowShares);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 bucket = input & 0x3;
        address user = address(uint160(0x3000 | bucket));
        address feeRecip = address(uint160(0x6000 | ((input >> 2) & 0x3)));
        feeRecipient = feeRecip;

        uint256 supplyDelta = ((input & 0x3f) + 1) * 1000;
        uint256 borrowDelta = supplyDelta / 2;
        uint256 ratePerSecond = ((input & 0xf) + 1) * 1e8;

        AssetParams memory mp = AssetParams({
            baseToken: address(uint160(0x1000 | bucket)),
            quoteToken: address(uint160(0x2000 | bucket)),
            oracle: address(uint160(0x4000 | bucket)),
            rateModel: (input & 8) != 0 ? address(0) : address(uint160(0x5000 | bucket)),
            maxRatio: 800000000000000000 + bucket * 10000000000000000
        });
        Id id = mp.id();
        Reserve memory m = _simulatedReserve(id, mp.rateModel, ratePerSecond);

        uint256 mintedSupplyShares = supplyDelta.toSharesDown(m.totalSupplyAssets, m.totalSupplyShares);
        m.totalSupplyAssets += supplyDelta.toUint128();
        m.totalSupplyShares += mintedSupplyShares.toUint128();

        uint256 mintedBorrowShares = borrowDelta.toSharesUp(m.totalBorrowAssets, m.totalBorrowShares);
        m.totalBorrowAssets += borrowDelta.toUint128();
        m.totalBorrowShares += mintedBorrowShares.toUint128();

        m.fee = uint128(((input & 0x7) + 1) * 1e16);
        m.lastUpdate = uint128(block.timestamp.zeroFloorSub(5));
        uint128 stepTag = m.lastUpdate++;
        reserves[id] = m;

        Holding memory pos = holdings[id][user];
        pos.supplyShares += mintedSupplyShares;
        pos.borrowShares += mintedBorrowShares.toUint128();
        pos.collateral += uint128(supplyDelta * 2);
        holdings[id][user] = pos;
        lastReserveId = id;

        if (input == 21) {
            revert ReserveStepBlocked(id, m.totalSupplyAssets, m.totalBorrowAssets);
        }

        emit InterestAccrued(id, ratePerSecond, m.totalSupplyAssets, m.totalSupplyShares);

        uint256 summary;
        unchecked {
            summary =
                uint256(Id.unwrap(id)) +
                uint256(uint160(feeRecipient)) +
                uint256(m.totalSupplyAssets) +
                uint256(m.totalSupplyShares) +
                uint256(m.totalBorrowAssets) +
                uint256(m.totalBorrowShares) +
                pos.supplyShares +
                uint256(pos.borrowShares) +
                uint256(pos.collateral) +
                uint256(stepTag) +
                uint256(m.lastUpdate);
        }

        bytes32 digest = bytes32(
            uint256(Id.unwrap(id)) ^
            (summary << 16) ^
            (uint256(m.lastUpdate) << 8) ^
            uint256(stepTag)
        );
        uint256 metric = (uint256(digest) & 0xffffffff) + (summary & 0xffffffff);
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, "SP: rollback");
        return totalScore;
    }

    function fail() external {
        feeRecipient = address(0xBEEF);
        totalScore += 999;
        revert("SP: fail");
    }

    function read() external view returns (uint256, bytes32, Id, address) {
        return (totalScore, lastDigest, lastReserveId, feeRecipient);
    }
}
