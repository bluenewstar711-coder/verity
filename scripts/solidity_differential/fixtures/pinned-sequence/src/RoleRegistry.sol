// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Multi-entry-point role/authorization registry: role handover, guarded
/// configuration with custom errors, delegation/revocation and monotonic
/// per-owner counters, each change logged by an event.
contract RoleRegistry {
    error Unauthorized();
    error AlreadySet();
    error AboveLimit();
    error NotIncreasing();

    event SetAdmin(address indexed newAdmin);
    event SetOperator(address indexed newOperator);
    event SetAuditor(address indexed newAuditor);
    event EnableLevel(uint256 indexed level);
    event SetLimit(address indexed token, uint256 indexed index, uint256 newLimit);
    event SetUsed(address indexed caller, address indexed owner, bytes32 indexed group, uint128 amount);
    event SetDelegate(address indexed caller, address indexed owner, address indexed delegate, bool allowed);

    uint256 constant MAX_LEVEL = 1e18;
    uint256 constant LIMIT_UNIT = 1e12;

    address public admin;
    address public operator;
    address public auditor;
    mapping(uint256 => bool) public isLevelEnabled;
    mapping(address => mapping(uint256 => uint16)) public limitOf;
    mapping(address => mapping(bytes32 => uint128)) public used;
    mapping(address => mapping(address => bool)) public isDelegate;

    function setAdmin(address newAdmin) external {
        require(msg.sender == admin, Unauthorized());
        require(newAdmin != admin, AlreadySet());
        admin = newAdmin;
        emit SetAdmin(newAdmin);
    }

    function setOperator(address newOperator) external {
        require(msg.sender == admin, Unauthorized());
        require(newOperator != operator, AlreadySet());
        operator = newOperator;
        emit SetOperator(newOperator);
    }

    function setAuditor(address newAuditor) external {
        require(msg.sender == admin, Unauthorized());
        require(newAuditor != auditor, AlreadySet());
        auditor = newAuditor;
        emit SetAuditor(newAuditor);
    }

    function enableLevel(uint256 level) external {
        require(msg.sender == admin, Unauthorized());
        require(level <= MAX_LEVEL, AboveLimit());
        require(!isLevelEnabled[level], AlreadySet());
        isLevelEnabled[level] = true;
        emit EnableLevel(level);
    }

    function setLimit(address token, uint256 index, uint256 newLimit) external {
        require(msg.sender == operator, Unauthorized());
        require(index < 4, AboveLimit());
        require(newLimit / LIMIT_UNIT <= type(uint16).max, AboveLimit());
        limitOf[token][index] = uint16(newLimit / LIMIT_UNIT);
        emit SetLimit(token, index, newLimit);
    }

    function setUsed(bytes32 group, uint128 amount, address onBehalf) external {
        require(msg.sender == onBehalf || isDelegate[onBehalf][msg.sender], Unauthorized());
        require(amount > used[onBehalf][group], NotIncreasing());
        used[onBehalf][group] = amount;
        emit SetUsed(msg.sender, onBehalf, group, amount);
    }

    function setDelegate(address delegate, bool allowed, address onBehalf) external {
        require(msg.sender == onBehalf || isDelegate[onBehalf][msg.sender], Unauthorized());
        isDelegate[onBehalf][delegate] = allowed;
        emit SetDelegate(msg.sender, onBehalf, delegate, allowed);
    }
}
