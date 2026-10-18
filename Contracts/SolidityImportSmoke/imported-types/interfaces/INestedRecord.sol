// SPDX-License-Identifier: MIT
pragma solidity >=0.5.0;

// Construct-generic imported type declarations. Only `NestedRecord` (a dynamic
// struct whose fourth member is an array of flat static structs) is used by
// the importing fixtures; every other declaration exercises how the importer
// ignores unrelated structs, errors and interface members in imported files.

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

struct RecordItem {
    address token;
    uint256 weight;
    uint256 cursor;
    address source;
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
    uint128 maxAmount; // second cap, interpreted by `flag`
    uint256 rateCap;
}

/// @dev Packed narrow members share storage words when used as storage.
struct PackedCounters {
    uint128 total;
    uint128 factor;
    uint128 available;
    uint128 credit;
    uint16 rate0;
    uint16 rate1;
    uint16 rate2;
    uint16 rate3;
    uint16 rate4;
    uint16 rate5;
    uint16 rate6;
    uint32 rate;
    uint8 spacing;
}

struct WideSlots {
    uint128 first;
    uint128 second;
    uint128 third;
    uint128 fourth;
    uint128 fifth;
    uint128 bitmap;
    uint128[128] slots;
}

interface INestedRecord {
    /// ERRORS ///
    error AlreadyUsed();
    error ArrayNotSorted();
    error CapExceeded();
    error InconsistentInput();
    error InvalidHead();
    error InvalidIndex();
    error InvalidOrigin();
    error InvalidSpacing();
    error NotInitialized();
    error Unauthorized();

    // forgefmt: disable-start
    /// STORAGE GETTERS ///
    function slotsOf(bytes32 key, address account) external view returns (uint128 first, uint128 second, uint128 third, uint128 fourth, uint128 fifth, uint128 bitmap);
    function countersOf(bytes32 key) external view returns (uint128 total, uint128 factor, uint128 available, uint128 credit, uint16 rate0, uint16 rate1, uint16 rate2, uint16 rate3, uint16 rate4, uint16 rate5, uint16 rate6, uint32 rate, uint8 spacing);
    function used(address account, bytes32 group) external view returns (uint128);
    function isAllowed(address owner, address delegate) external view returns (bool);
    function admin() external view returns (address);

    /// BATCHING ///
    function batch(bytes[] memory calls) external;

    /// UPDATES ///
    function setAdmin(address newAdmin) external;
    function setRate(bytes32 key, uint256 index, uint256 newRate) external;
    function submit(Envelope memory envelope, bytes memory proof, uint256 units, address beneficiary) external returns (uint256 firstAmount, uint256 secondAmount);
    function settle(NestedRecord memory record, uint256 itemIndex, uint256 amount, address onBehalf, bool flag, address hook, bytes memory data) external returns (uint256 settledFirst, uint256 settledSecond);
    function flash(address[] memory tokens, uint256[] memory amounts, address hook, bytes memory data) external;
    function touch(NestedRecord memory record) external returns (bytes32);

    /// VIEWS ///
    function preview(NestedRecord memory record, bytes32 key, address account) external view returns (uint128 nextFirst, uint128 nextSecond, uint128 accrued);
    function toRecord(bytes32 key) external view returns (NestedRecord memory);
    function rates(bytes32 key) external view returns (uint16[7] memory);
    function slotAt(bytes32 key, address account, uint256 index) external view returns (uint128);
    function isHealthy(NestedRecord memory record, bytes32 key, address account) external view returns (bool);
    // forgefmt: disable-end
}
