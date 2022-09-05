////////////////////////////////////////////////////////////////////////////
//                       Imports and multi-contracts                      //
////////////////////////////////////////////////////////////////////////////
import "erc20.spec"

// Declaring aliases for contracts according to the format:
// using Target_Contract as Alias_Name
/************************
 *     L1 contracts     *
 ************************/
    using DummyERC20UnderlyingA_L1 as UNDERLYING_ASSET_A 
    using DummyERC20UnderlyingB_L1 as UNDERLYING_ASSET_B
    using ATokenWithPoolA_L1 as ATOKEN_A
    using ATokenWithPoolB_L1 as ATOKEN_B
    using DummyERC20RewardToken as REWARD_TOKEN
    using SymbolicLendingPoolL1 as LENDINGPOOL_L1
    using IncentivesControllerMock_L1 as incentivesController

/************************
 *     L2 contracts     *
 ************************/
    using BridgeL2Harness as BRIDGE_L2
    using StaticATokenA_L2 as STATIC_ATOKEN_A
    using StaticATokenB_L2 as STATIC_ATOKEN_B

// For referencing structs
    using BridgeHarness as Bridge

////////////////////////////////////////////////////////////////////////////
//                       Methods                                          //
////////////////////////////////////////////////////////////////////////////
// Declaring contracts' methods and summarizing them as needed
methods {
/**********************
 *     Bridge.sol     *
 **********************/
 // Note that some functions should only be called via BridgeHarness
 // e.g. withdraw(), invoked by the initiateWithdraw on L2.
    initialize(uint256, address, address, address[], uint256[])
    initializing() returns (bool) envfree
    deposit(address, uint256, uint256, uint16, bool) returns (uint256) 
    withdraw(address, uint256, address, uint256, uint256, bool)
    updateL2State(address)
    receiveRewards(uint256, address, uint256)
    listEqualLength(address[], uint256[]) returns (bool) envfree
    approvedL1TokensLength() returns(uint256) envfree
    
/*************************
 *     BridgeHarness     *
 *************************/
    // Note that these methods take as args OR return the contract types that are written in comment to their right.
    // In CVL we contracts are addresses an therefore we demand return of an address
    getATokenOfUnderlyingAsset(address, address) returns (address) envfree
    getLendingPoolOfAToken(address) returns (address) envfree //(ILendingPool)
    _staticToDynamicAmount_Wrapper(uint256, address, address) envfree //(ILendingPool)
    _dynamicToStaticAmount_Wrapper(uint256, address, address) envfree //(ILendingPool)
    _computeRewardsDiff_Wrapper(uint256, uint256, uint256) envfree
    _getCurrentRewardsIndex_Wrapper(address) returns (uint256) 
    initiateWithdraw_L2(address, uint256, address, bool)
    bridgeRewards_L2(address, uint256)
    getUnderlyingAssetOfAToken(address) returns (address) envfree
    underlyingtoAToken(address) returns (address) => DISPATCHER(true)
    Cairo_isValidL2Address(uint256) returns (bool) envfree

/******************************
 *     IStarknetMessaging     *
 ******************************/
    // The methods of Bridge.sol that call this contract are being overridden to bypass the messaging communication.
    // Instead, we modeled the L2 side in solidity and made direct calls between the sides.

/************************
 *     ILendingPool     *
 ************************/
    // The lending pool used in the contract is encapsulated within a struct in IBridge.sol.
    // We point to direct calls to these methods using dispatchers. 
    deposit(address, uint256, address, uint16) => DISPATCHER(true)
    withdraw(address, uint256, address) returns (uint256) => DISPATCHER(true)
    getReserveNormalizedIncome(address) returns (uint256) => DISPATCHER(true)
    LENDINGPOOL_L1.liquidityIndexByAsset(address) returns (uint256) envfree


/*************************************************
 *     IATokenWithPool     *
 *************************************************/
    mint(address, uint256, uint256) returns (bool) => DISPATCHER(true)
    mint(address, uint256) returns (bool) => DISPATCHER(true)
    burn(address, address, uint256, uint256) => DISPATCHER(true)
    burn(address, uint256) returns (bool) => DISPATCHER(true)
    POOL() returns (address) => DISPATCHER(true)
    scaledTotalSupply() returns (uint256) => DISPATCHER(true)
    getIncentivesController() => DISPATCHER(true)
    ATOKEN_A.balanceOf_super(address) returns (uint256) envfree
/************************************
 *     IncentivesControllerMock     *
 ************************************/
    _rewardToken() returns (address) envfree => DISPATCHER(true)
    DISTRIBUTION_END() returns (uint256) => CONSTANT
    getRewardsVault() returns (address) => DISPATCHER(true)
    getAssetData(address) returns (uint256, uint256, uint256) => DISPATCHER(true)
    // Note that the sender of the funds here is RewardsVault which is arbitrary by default.
    // If any rule that count on the reward token balance, calls this method a `require RewardsVault != to` make sense to add
    claimRewards(address[], uint256, address) returns (uint256) => DISPATCHER(true)
    
/***************************
 *     BridgeL2Harness     *
 ***************************/
    BRIDGE_L2.l2RewardsIndexSetter(uint256)
    BRIDGE_L2.deposit(address, uint256, address) 
    BRIDGE_L2.initiateWithdraw(address, uint256, address, address, bool)
    BRIDGE_L2.bridgeRewards(address, address, uint256)
    BRIDGE_L2.claimRewards(address, address)
    BRIDGE_L2.l2RewardsIndex() returns (uint256) envfree
    BRIDGE_L2.getStaticATokenAddress(address) returns (address) envfree
    BRIDGE_L2.address2uint256(address) returns (uint256) envfree

/******************
 *     Tokens     *
 ******************/
    UNDERLYING_ASSET_ADDRESS() returns (address) => DISPATCHER(true)
    ATOKEN_A.UNDERLYING_ASSET_ADDRESS() returns (address) envfree
    ATOKEN_B.UNDERLYING_ASSET_ADDRESS() returns (address) envfree  
    claimRewards(address) returns (uint256) => DISPATCHER(true)
    getRewTokenAddress() returns (address) => rewardToken()

/******************
 *     Ray Math   *
 ******************/
 // See also notes at bottom of file (under "Summarizations")
 // Comment out the next two lines to remove the simplification,
 // and let the prover use the original library functions.
    rayMul(uint256 a, uint256 b) returns (uint256) => rayMulConst(a, b)
    rayDiv(uint256 a, uint256 b) returns (uint256) => rayDivConst(a, b)
}

////////////////////////////////////////////////////////////////////////////
//                       Definitions                                      //
////////////////////////////////////////////////////////////////////////////

// Definition of RAY unit
definition RAY() returns uint256 = 10^27;

// Used for the Ray math summarization.
// Effectively sets the liquidity index in L1 to be a constant, given
// by the following value.
// Note: if the summarization is not used, i.e. they are commented out,
// this value has no use.
definition myConstRayValue() returns uint256 = RAY()*4;

// The following definition shall be used later in some invariants,
// by filtering out the 'initialize' function.
definition excludeInitialize(method f) returns bool =
    f.selector != 
    initialize(uint256, address, address, address[], uint256[]).selector; 

// A filter for parametric rules.
// The functions receiveRewards and withdraw should not be called by an external user
// Unless a message was already sent, which we mock through the additional functions that
// call the L2 interface.
// Using this filter via:
// filtered{f -> messageSentFilter(f)} will reduce running time, by skipping the analysis
// of these functions.
definition messageSentFilter(method f) returns bool = 
    f.selector != receiveRewards(uint256, address, uint256).selector
    &&
    f.selector != withdraw(address, uint256, address, uint256, uint256, bool).selector;

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

/*
    @Rule - a template for rule description:

    @Description: Significance of rule, property
        

    @Formula:
        {
            require something (pre-condition)
        }
            < call any function or specific function >
        {
            assert post-condition
        }

    @Note:
        Some notes about requirements or special consideration of the rule.
    @Link:
        Link to last verification report run of the rule.
*/

// Checks basic properties of withdrawal.
rule integrityOfWithdraw(address recipient){
    bool toUnderlyingAsset;
    uint256 staticAmount; 
    env e; calldataarg args;
    address underlying;
    address static;
    address aToken;
    uint256 l2RewardsIndex = BRIDGE_L2.l2RewardsIndex();
    
    setupTokens(underlying, aToken, static);
    setupUser(e.msg.sender);
    require recipient != aToken;
    require recipient != currentContract;

    uint256 underlyingBalanceBefore = tokenBalanceOf(e, underlying, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    initiateWithdraw_L2(e, aToken, staticAmount, recipient, toUnderlyingAsset);

    uint256 underlyingBalanceAfter = tokenBalanceOf(e, underlying, recipient);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    if (toUnderlyingAsset){
        assert 
        (underlyingBalanceAfter >= underlyingBalanceBefore) &&
        (aTokenBalanceAfter == aTokenBalanceBefore);
    }
    else {
        assert 
        (aTokenBalanceAfter >= aTokenBalanceBefore) &&
        (underlyingBalanceAfter == underlyingBalanceBefore);

    }
    assert rewardTokenBalanceAfter >= rewardTokenBalanceBefore;
}

// If a balance of tokens changed, then deposit or withdrawal must have been called.
rule balanceOfUnderlyingAssetChanged(method f, uint256 amount)
filtered{f -> messageSentFilter(f)} {
    env e;    
    address asset;
    address AToken;
    address static;
    address recipient;
    bool fromToUA;
    
    setupTokens(asset, AToken, static);
    setupUser(e.msg.sender);

    // Underlying asset balances of sender and recipient before call.
    uint256 recipientBalanceA1 = tokenBalanceOf(e, AToken, recipient);
    uint256 recipientBalanceU1 = tokenBalanceOf(e, asset, recipient);

    // Call any interface function 
    callFunctionSetParams(f, e, recipient, AToken, asset, amount, fromToUA);

    // Underlying asset balances of sender and recipient after call.
    uint256 recipientBalanceA2 = tokenBalanceOf(e, AToken, recipient);
    uint256 recipientBalanceU2 = tokenBalanceOf(e, asset, recipient);

    bool balancesChanged = !(
        recipientBalanceA1 == recipientBalanceA2 && 
        recipientBalanceU1 == recipientBalanceU2);

    assert balancesChanged =>
            (f.selector == deposit(address, uint256, uint256, uint16, bool).selector 
            ||
            f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector)
            , "balanceOf changed";
}

// added 1
rule noImpactOnOther(method f, uint256 amount)
{
    env e;    
    address asset;
    address AToken;
    address static;
    address recipient;
    address other;
    bool fromToUA;
    
    setupTokens(asset, AToken, static);
    setupUser(e.msg.sender);
    setupUser(recipient);
    setupUser(other);

    require other!=recipient && other != e.msg.sender;

    uint256 _balanceU = tokenBalanceOf(e, asset, other);
    uint256 _balanceA = tokenBalanceOf(e, AToken, other);
    uint256 _balanceS = tokenBalanceOf(e, static, other);
    uint256 _balanceR = tokenBalanceOf(e, rewardToken(), other);
    
    // Call any interface function 
    callFunctionSetParams(f, e, recipient, AToken, asset, amount, fromToUA);

    uint256 balanceU_ = tokenBalanceOf(e, asset, other);
    uint256 balanceA_ = tokenBalanceOf(e, AToken, other);
    uint256 balanceS_ = tokenBalanceOf(e, static, other);
    uint256 balanceR_ = tokenBalanceOf(e, rewardToken(), other);

    assert _balanceU == balanceU_;
    assert _balanceA == balanceA_;
    assert _balanceS == balanceS_;
    assert _balanceR == balanceR_;
}

// A call to deposit and a subsequent call to withdraw with the same amount of 
// staticATokens received, should yield the same original balance for the user.
// For underlying tokens, the condition is modified by a bound, since staticToDynamic is not inversible with dyanmicToStatic.
rule depositWithdrawReversed(uint256 amount)
{
    env eB; env eF;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2Recipient = BRIDGE_L2.address2uint256(eB.msg.sender);
    uint16 referralCode;
    bool fromUA; // (deposit) from underlying asset
    bool toUA; // (withdraw) to underlying asset

    setupTokens(asset, Atoken, static);
    setupUser(eF.msg.sender);
    requireRayIndex(asset);
    require eF.msg.sender == eB.msg.sender;
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);

    uint256 balanceU1 = tokenBalanceOf(eB, asset, eB.msg.sender);
    uint256 balanceA1 = tokenBalanceOf(eB, Atoken, eB.msg.sender);
    uint256 balanceS1 = tokenBalanceOf(eB, static, eB.msg.sender);
        uint256 staticAmount = deposit(eB, Atoken, l2Recipient, amount, referralCode, fromUA);
    /////////////////////////
    /*
    One can use these values (post-deposit pre-withdrawal) for debugging.
    uint256 balanceU2 = tokenBalanceOf(eB, asset, eB.msg.sender);
    uint256 balanceA2 = tokenBalanceOf(eB, Atoken, eB.msg.sender);
    uint256 balanceS2 = tokenBalanceOf(eB, static, eB.msg.sender);
    */
    /////////////////////////
        initiateWithdraw_L2(eF, Atoken, staticAmount, eF.msg.sender, toUA);
    uint256 balanceU3 = tokenBalanceOf(eF, asset, eF.msg.sender);
    uint256 balanceA3 = tokenBalanceOf(eF, Atoken, eF.msg.sender);
    uint256 balanceS3 = tokenBalanceOf(eF, static, eF.msg.sender);
    
    assert balanceS1 == balanceS3;
    assert fromUA == toUA => balanceU3 - balanceU1 <= (indexL1/RAY()+1)/2;
    assert fromUA == toUA => balanceA3 == balanceA1;
}

// added 2
rule depositAdditive(uint256 amount1, uint256 amount2) {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUA; // (deposit) from underlying asset
    bool toUA; // (withdraw) to underlying asset
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);
    // require l2Recipient != e.msg.sender;

    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);

	storage initialStorage = lastStorage;

    uint256 staticAmount1 = deposit(e, Atoken, l2Recipient, amount1, referralCode, fromUA);
    uint256 staticAmount2 = deposit(e, Atoken, l2Recipient, amount2, referralCode, fromUA);
    uint256 balanceU_12 = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_12 = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_12 = tokenBalanceOf(e, static, e.msg.sender);

	uint256 staticAmount = deposit(e, Atoken, l2Recipient, amount1 + amount2, referralCode, fromUA) at initialStorage;
    uint256 balanceU_all = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_all = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_all = tokenBalanceOf(e, static, e.msg.sender);

    assert staticAmount1 + staticAmount2 - 1 <= staticAmount 
            && staticAmount1 + staticAmount2 + 1 >= staticAmount;
    assert balanceU_12 == balanceU_all;
    assert balanceA_12-balanceA_all<=rayMulConst(1, b) && balanceA_all-balanceA_12<=rayMulConst(1, b);
    assert balanceS_12 - balanceS_all <= 1 
        && balanceS_all - balanceS_12 <= 1;
}

// added 3
rule depositAtokenVsUA(uint256 amount) {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUA; // (deposit) from underlying asset
    bool toUA; // (withdraw) to underlying asset
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);

	storage initialStorage = lastStorage;

    uint256 balanceU = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS = tokenBalanceOf(e, static, e.msg.sender);

    uint256 staticAmount1 = deposit(e, Atoken, l2Recipient, amount, referralCode, true);
    uint256 balanceU_fromUA = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_fromUA = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_fromUA = tokenBalanceOf(e, static, e.msg.sender);

    uint256 staticAmount2 = deposit(e, Atoken, l2Recipient, amount, referralCode, false) at initialStorage;
    uint256 balanceU_fromAT = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_fromAT = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_fromAT = tokenBalanceOf(e, static, e.msg.sender);

    assert staticAmount1 == staticAmount2;
    assert balanceU == balanceU_fromUA + amount && balanceU == balanceU_fromAT;
    assert balanceA == balanceA_fromUA && balanceA == balanceA_fromAT + rayMulConst(rayDivConst(amount, b), b);
    assert balanceS == balanceS_fromUA - staticAmount1 && balanceS == balanceS_fromAT - staticAmount2;
}

// added 4
rule withdrawAdditive() {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2sender;
    address recipient;
    uint256 staticAmount1;
    uint256 staticAmount2;
    uint256 l2RewardsIndex;
    bool toUnderlyingAsset;
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);

	storage initialStorage = lastStorage;

    initiateWithdraw_L2(e, Atoken, staticAmount1, recipient, toUnderlyingAsset);
    initiateWithdraw_L2(e, Atoken, staticAmount2, recipient, toUnderlyingAsset);

    uint256 balanceU_12 = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_12 = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_12 = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR_12 = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    initiateWithdraw_L2(e, Atoken, staticAmount1 + staticAmount2, recipient, toUnderlyingAsset) at initialStorage;
    uint256 balanceU_all = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_all = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_all = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR_all = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    assert balanceU_12 == balanceU_all;
    assert balanceA_12 == balanceA_all;
    assert balanceS_12 == balanceS_all;
    assert balanceR_12 <= balanceR_all; // the seperate withdraw allows more time for reward accumulation
}

// added 5
rule withdrawAtokenVsUA(uint256 amount) {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2sender;
    address recipient;
    uint256 staticAmount;
    uint256 l2RewardsIndex;
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    setupUser(recipient);
    requireRayIndex(asset);
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);

	storage initialStorage = lastStorage;

    // require recipient != currentContract
    uint256 balanceU = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    uint256 balanceUr = tokenBalanceOf(e, asset, recipient);
    uint256 balanceAr = tokenBalanceOf(e, Atoken, recipient);
    uint256 balanceSr = tokenBalanceOf(e, static, recipient);
    uint256 balanceRr = tokenBalanceOf(e, rewardToken(), recipient);

    initiateWithdraw_L2(e, Atoken, staticAmount, recipient, true);
    uint256 balanceU_toUA = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_toUA = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_toUA = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR_toUA = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    uint256 balanceUr_toUA = tokenBalanceOf(e, asset, recipient);
    uint256 balanceAr_toUA = tokenBalanceOf(e, Atoken, recipient);
    uint256 balanceSr_toUA = tokenBalanceOf(e, static, recipient);
    uint256 balanceRr_toUA = tokenBalanceOf(e, rewardToken(), recipient);

    initiateWithdraw_L2(e, Atoken, staticAmount, recipient, false) at initialStorage;
    uint256 balanceU_toAT = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_toAT = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_toAT = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR_toAT = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    uint256 balanceUr_toAT = tokenBalanceOf(e, asset, recipient);
    uint256 balanceAr_toAT = tokenBalanceOf(e, Atoken, recipient);
    uint256 balanceSr_toAT = tokenBalanceOf(e, static, recipient);
    uint256 balanceRr_toAT = tokenBalanceOf(e, rewardToken(), recipient);

    assert balanceS == balanceS_toUA + staticAmount 
        &&  balanceS == balanceS_toAT + staticAmount;
    assert balanceUr == balanceUr_toUA - rayMulConst(staticAmount, b) 
        && balanceAr == balanceAr_toAT - rayMulConst(staticAmount, b);
    assert balanceUr == balanceUr_toAT
        && balanceAr == balanceAr_toUA;
    assert balanceRr <= balanceRr_toUA 
        && balanceRr <= balanceRr_toAT; 
}


rule zeroStaticATokensCannotWithdraw(uint256 amount, method f) filtered {
    f-> f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector 
} {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2sender;
    address l2Recipient;
    uint256 staticAmount;
    uint256 l2RewardsIndex;
    bool fromToUA;
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);
    require tokenBalanceOf(e, static, e.msg.sender) == 0;

    uint256 _balanceU = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 _balanceA = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 _balanceS = tokenBalanceOf(e, static, e.msg.sender);
    uint256 _balanceR = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    uint256 _balanceUr = tokenBalanceOf(e, asset, l2Recipient);
    uint256 _balanceAr = tokenBalanceOf(e, Atoken, l2Recipient);
    uint256 _balanceSr = tokenBalanceOf(e, static, l2Recipient);
    uint256 _balanceRr = tokenBalanceOf(e, rewardToken(), l2Recipient);

    initiateWithdraw_L2(e, Atoken, amount, l2Recipient, fromToUA);

    uint256 balanceU_ = tokenBalanceOf(e, asset, e.msg.sender);
    uint256 balanceA_ = tokenBalanceOf(e, Atoken, e.msg.sender);
    uint256 balanceS_ = tokenBalanceOf(e, static, e.msg.sender);
    uint256 balanceR_ = tokenBalanceOf(e, rewardToken(), e.msg.sender);

    uint256 balanceUr_ = tokenBalanceOf(e, asset, l2Recipient);
    uint256 balanceAr_ = tokenBalanceOf(e, Atoken, l2Recipient);
    uint256 balanceSr_ = tokenBalanceOf(e, static, l2Recipient);
    uint256 balanceRr_ = tokenBalanceOf(e, rewardToken(), l2Recipient);

    assert _balanceU == balanceU_;
    assert _balanceA == balanceA_;
    assert _balanceS == balanceS_;
    assert _balanceR == balanceR_;
    assert _balanceUr == balanceUr_;
    assert _balanceAr == balanceAr_;
    assert _balanceSr == balanceSr_;
    assert _balanceRr == balanceRr_;
}

// added 6
rule zeroWithdrawRevert(uint256 amount, method f) {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2sender;
    address l2Recipient;
    uint256 staticAmount;
    uint256 l2RewardsIndex;
    bool fromToUA;
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);

    initiateWithdraw_L2@withrevert(e, Atoken, 0, l2Recipient, fromToUA);
    assert(lastReverted);
}

// added 7
rule cannontWithdrawMoreThanOwned(uint256 amount) {
    env e;
    address Atoken; // AAVE Token
    address asset;  // underlying asset
    address static; // staticAToken
    uint256 l2sender;
    address l2Recipient;
    uint256 staticAmount;
    uint256 l2RewardsIndex;
    bool fromToUA;
    uint256 b;

    setupTokens(asset, Atoken, static);
    setupUser(e.msg.sender);
    requireRayIndex(asset);
    require amount > tokenBalanceOf(e, static, e.msg.sender);

    initiateWithdraw_L2@withrevert(e, Atoken, amount, l2Recipient, fromToUA);
    assert(lastReverted);
}

// Checks that the transitions between static to dynamic are inverses.
// Verified
rule dynamicToStaticInversible1(uint256 amount)
{
    // We assume both indexes (L1,L2) are represented in Ray (1e27).
    address asset;
    requireRayIndex(asset);
    uint256 dynm = _staticToDynamicAmount_Wrapper(amount, asset, LENDINGPOOL_L1);
    uint256 stat = _dynamicToStaticAmount_Wrapper(dynm, asset, LENDINGPOOL_L1);
    assert amount == stat;
}

// Checks that it isn't possible to gain from transforming dynamic to static
// and back.
// This is violated because the mul and div are not inverses of each other,
// therefore can lead to mul(div(a,b),b) > a (depends on remainder value).
rule dynamicToStaticInversible2(uint256 amount)
{
    // We assume both indexes (L1,L2) are represented in Ray (1e27).
    address asset;
    requireRayIndex(asset);
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(asset);
    uint256 stat = _dynamicToStaticAmount_Wrapper(amount, asset, LENDINGPOOL_L1);
    uint256 dynm = _staticToDynamicAmount_Wrapper(stat, asset, LENDINGPOOL_L1);
    // assert dynm <= amount;  // Violated
    assert dynm - amount <= (indexL1/RAY() + 1)/2; // Pass
}

// We make sure that the message sent booleans are always false,
// meaning that, according to our implementation, no external call can
// invoke receiveRewards and withdraw in Bridge.sol, but only through the 
// designated functions in the harnessed Bridge contract.
invariant alwaysUnSent(env e)
   !withdrawMessageStatus(e) && !bridgeRewardsMessageStatus(e)
    filtered{f -> messageSentFilter(f)}


// Check consistency of 'asset' being registered as the underlying
// token of 'AToken', both in the AToken contract, and also in the 
// mapping _aTokenData.
// We exclude the 'initialize' function since it is called only once
// in the code. 
invariant underlying2ATokenConsistency(address AToken, address asset)
     (asset !=0 <=> AToken !=0) 
     =>
     (getUnderlyingAssetHelper(AToken) == asset 
     <=>
     getUnderlyingAssetOfAToken(AToken) == asset)
     filtered{f-> excludeInitialize(f) && messageSentFilter(f)}

// Check consistency of 'asset' being registered as the underlying
// token of 'AToken', and 'AToken' connected to 'asset' in the lending pool.
// We exclude the 'initialize' function since it is called only once
// in the code. 
invariant ATokenAssetPair(address asset, address AToken)
    (asset !=0 <=> AToken !=0) 
    =>
    (getUnderlyingAssetHelper(AToken) == asset 
    <=>
    getATokenOfUnderlyingAsset(LENDINGPOOL_L1, asset) == AToken)
    filtered{f -> excludeInitialize(f)  && messageSentFilter(f)}

// The aToken-asset pair should be correctly registered after calling
// initialize, right after the constructor.
// This is complementary to the two invariants above.
rule initializeIntegrity(address AToken, address asset)
{
    env e;
    calldataarg args;

    // Post-constructor conditions
    require getUnderlyingAssetHelper(AToken) == 0;
    require getATokenOfUnderlyingAsset(LENDINGPOOL_L1, asset) == 0;
    
    initialize(e, args);

    assert (asset !=0 && AToken !=0) => (
        getUnderlyingAssetHelper(AToken) == asset 
        <=>
        getATokenOfUnderlyingAsset(LENDINGPOOL_L1, asset) == AToken);
}


// added 8
rule initializeConditions(address AToken, address asset, uint256 l2Bridge, address messagingContract, address incentivesControllerVar, address[] l1Tokens, uint256[] l2Tokens)
{
    env e;

    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerVar, l1Tokens, l2Tokens);
    bool succeeded = !lastReverted;

    assert !Cairo_isValidL2Address(l2Bridge) => !succeeded;
    assert incentivesControllerVar == 0 => !succeeded;
    assert !listEqualLength(l1Tokens, l2Tokens) => !succeeded;  // why does l1Tokens.length == l2Tokens.length not work?
    // assert l1Tokens.length == 0 => !succeeded; // should fail
    // assert messagingContract ==0 => !succeeded; // should fail
}

// added 9
rule cannotInitializeTwice(address AToken, address asset)
{
    env e1;
    calldataarg args1;
    env e2;
    calldataarg args2;

    // Post-constructor conditions
    require getUnderlyingAssetHelper(AToken) == 0;
    require getATokenOfUnderlyingAsset(LENDINGPOOL_L1, asset) == 0;

    require initializing() == false;

    initialize@withrevert(e1, args1);
    bool firstSucceeded = !lastReverted;

    initialize@withrevert(e2, args2);
    bool secondSucceeded = !lastReverted;

    assert  firstSucceeded => !secondSucceeded, "second initialize call should fail";
}

// added 10
rule onlyInitializeCanChangeApprovedL1TokensList(method f) {
    env e;
    calldataarg args;
    //length of the approved tokens array before
    uint256 _length = approvedL1TokensLength();
    f(e, args);
    //length of the approved tokens array after
    uint256 length_ = approvedL1TokensLength();
    //if theres a change the function called can only be initialize
    assert _length != length_ => f.selector == initialize(uint256, address, address, address[], uint256[]).selector;

}

// added 11
rule cannotBeCalledExternally(method f) filtered{f -> !messageSentFilter(f)}
{
    env e; 
    calldataarg args;
    require withdrawMessageStatus(e)==false && bridgeRewardsMessageStatus(e)==false;
    f(e, args);

    assert false; // unreachable
}

// added 12
rule rewardsIndexIncreasingOverTime() {
    env e1; 
    env e2;
    address aToken;
    require e1.block.timestamp < e2.block.timestamp;
    
    uint256 _l2RewardsIndex = BRIDGE_L2.l2RewardsIndex();
    
    assert _getCurrentRewardsIndex_Wrapper(e1, aToken) <= _getCurrentRewardsIndex_Wrapper(e2, aToken);
    assert _l2RewardsIndex <= BRIDGE_L2.l2RewardsIndex();
}

// added 13
rule L2RewardsIndexLtL1() {
    method f;
    env e;
    address receiver;
    address aToken;
    address asset;
    address static;
    uint256 amount; 
    bool fromToUA;

    require getUnderlyingAssetHelper(aToken) == 0;
    require getATokenOfUnderlyingAsset(LENDINGPOOL_L1, asset) == 0;

    require BRIDGE_L2.l2RewardsIndex() <= _getCurrentRewardsIndex_Wrapper(e, aToken);
    callFunctionSetParams(f, e, receiver, aToken, asset, amount, fromToUA);
    assert BRIDGE_L2.l2RewardsIndex() <= _getCurrentRewardsIndex_Wrapper(e, aToken);
}

// added 14
rule bridgeRewardsIntegrity() {
    env e;
    address recipient;
    uint256 amount;
    setupUser(e.msg.sender);
    setupUser(recipient);
    require e.msg.sender!=recipient;

    uint256 _balanceRs = tokenBalanceOf(e, rewardToken(), e.msg.sender);
    uint256 _balanceRr = tokenBalanceOf(e, rewardToken(), recipient);
    uint256 _balanceRb = tokenBalanceOf(e, rewardToken(), currentContract);
    bridgeRewards_L2@withrevert(e, recipient, amount);
    bool succeeded = !lastReverted;
    uint256 balanceRs_ = tokenBalanceOf(e, rewardToken(), e.msg.sender);
    uint256 balanceRr_ = tokenBalanceOf(e, rewardToken(), recipient);
    uint256 balanceRb_ = tokenBalanceOf(e, rewardToken(), currentContract);

    if (amount> 0 && succeeded) {
        assert balanceRs_ < _balanceRs;
        assert balanceRr_ > _balanceRr;
        assert balanceRb_ == _balanceRb;
    }
    assert amount > _balanceRs => !succeeded;
}

// added 15
rule bridgeRewardsAdditive() {
    env e;
    address recipient;
    uint256 amount1;
    uint256 amount2;

    uint256 balanceRs = tokenBalanceOf(e, rewardToken(), e.msg.sender);
    require amount1+amount2 < balanceRs;

    storage initialStorage = lastStorage;
    bridgeRewards_L2(e, recipient, amount1);
    bridgeRewards_L2(e, recipient, amount2);

    uint256 _balanceRs = tokenBalanceOf(e, rewardToken(), e.msg.sender);
    uint256 _balanceRr = tokenBalanceOf(e, rewardToken(), recipient);
    
    bridgeRewards_L2(e, recipient, amount1+amount2) at initialStorage;
    uint256 balanceRs_ = tokenBalanceOf(e, rewardToken(), e.msg.sender);
    uint256 balanceRr_ = tokenBalanceOf(e, rewardToken(), recipient);
    
    assert balanceRs_ == _balanceRs;
    assert balanceRr_ == _balanceRr;
}

// Sanity(f) - there exists a non-reverting path for a the contract method f.
// If the rule is verified (green V), no such path exists.
rule sanity(method f) {
    env e;
    address receiver;
    address aToken;
    address asset;
    address static;
    uint256 amount; 
    bool fromToUnderlyingAsset;
    setupTokens(asset, aToken, static);
    setupUser(e.msg.sender);
    callFunctionSetParams(f, e, receiver, aToken, asset, amount, fromToUnderlyingAsset);
    assert false;
}

////////////////////////////////////////////////////////////////////////////
//                       Functions                                        //
////////////////////////////////////////////////////////////////////////////

// A general requirement set for the token trio:
// asset - underlying asset
// AToken - correpsonding AToken in the lending pool.
// static - staticAToken to be minted on L2.
function setupTokens(
    address asset, 
    address AToken, 
    address static){
    // Selects a dummy contract implementation for the tokens trio.
    // Note that if it used twice, for two different trios, it is possible
    // they will share the same addresses.
    tokenSelector(asset, AToken, static);
    // Links tokens to each other throught the bridges and pool stored data.
    setLinkage(asset, AToken, static);
    // Links asset and AToken. (Might be redundant after calling 'setLinkage').
    requireInvariant ATokenAssetPair(asset, AToken);
}

// A general requirement set for an extenral user using the bridge.
// User should usually be the msg.sender, but not necessarily the recipient!
function setupUser(address user){
    // Exclude contracts addresses from possible values of [user].
    requireValidUser(user);
}

// Selects specific instances for underlying asset, AToken and static tokens.
function tokenSelector(
    address asset, 
    address AToken, 
    address static){
    require asset == UNDERLYING_ASSET_A || asset == UNDERLYING_ASSET_B;
    require AToken == ATOKEN_A || AToken == ATOKEN_B;
    require static == STATIC_ATOKEN_A || static == STATIC_ATOKEN_B;
}

// By definition, the liquidity indexes are expressed in RAY units.
// Therefore they must be at least as large as RAY (assuming liquidity index > 1).
function requireRayIndex(address asset) {
    require LENDINGPOOL_L1.liquidityIndexByAsset(asset) >= RAY();
    require BRIDGE_L2.l2RewardsIndex() >= RAY();
}

// Require a constant value for the L1 index.
// Supposed to (hopefully) make runs faster, note that is reduces coverage!
function constantL1Index(address asset, uint256 value_in_Ray){
   require LENDINGPOOL_L1.liquidityIndexByAsset(asset) == value_in_Ray*RAY();
}

// Linking the instances of ERC20s and LendingPool 
// within the ATokenData struct to the corresponding symbolic contracts.
function setLinkage(
    address asset, 
    address AToken, 
    address static){
    // Setting the underlying token of the given AToken as either UNDERLYING_ASSET_A or UNDERLYING_ASSET_B
    require getUnderlyingAssetOfAToken(AToken) == asset;
    require getLendingPoolOfAToken(AToken) == LENDINGPOOL_L1;
    require BRIDGE_L2.getStaticATokenAddress(AToken) == static;
    setUnderlyingAToken(AToken, asset);
}

function setUnderlyingAToken(address AToken, address asset) {
    // Note that if AToken is neither ATOKEN_A nor ATOKEN_B,
    // this function will force asset == 0.
    require getUnderlyingAssetHelper(AToken) == asset;
}

function getUnderlyingAssetHelper(address AToken) returns address {
    if (AToken == ATOKEN_A) {
        return ATOKEN_A.UNDERLYING_ASSET_ADDRESS();
    }
    else if (AToken == ATOKEN_B) {
        return ATOKEN_B.UNDERLYING_ASSET_ADDRESS();
    }
    // Warning: default value is 0!
    return 0;
}

// Require the token trio (asset, Atoken, StaticAToken) to have
// distinct addresses.
function requireValidTokens(
    address asset, 
    address AToken, 
    address static){
        require asset != AToken &&
                AToken != static &&
                static != asset;
}

// Requirements for a "valid" user - exclude contracts addresses.
function requireValidUser(address user){
    require 
        user != Bridge &&
        user != BRIDGE_L2 &&
        user != UNDERLYING_ASSET_A &&
        user != UNDERLYING_ASSET_B &&
        user != ATOKEN_A &&
        user != ATOKEN_B &&
        user != STATIC_ATOKEN_A &&
        user != STATIC_ATOKEN_B &&
        user != REWARD_TOKEN &&
        user != LENDINGPOOL_L1 &&
        user != incentivesController;
}

// Returns the address of the reward token contract (used for summarization)
function rewardToken() returns address {
    return REWARD_TOKEN;
}

// A function selector helper, to specify the receiver.
function callFunctionSetParams(
    method f, env e, address receiver,
    address aToken, address asset,
    uint256 amount, bool fromToUnderlyingAsset) returns uint256 {
    // Inhibits the user from calling the functions withdraw and receiveRewards.
    // Expect unreachability for these functions (intended). 
    requireInvariant alwaysUnSent(e);
    if (f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector){
        require receiver != currentContract;
        return initiateWithdraw_L2(e, aToken, amount, receiver, fromToUnderlyingAsset); 
    }   
    else if (f.selector == deposit(address, uint256, uint256, uint16, bool).selector){
        uint256 l2Recipient = BRIDGE_L2.address2uint256(receiver);
        uint16 referralCode;
        require receiver != currentContract;
        return deposit(e, aToken, l2Recipient, amount, referralCode, fromToUnderlyingAsset);
    }
    else if (f.selector == bridgeRewards_L2(address, uint256).selector) {
        bridgeRewards_L2(e, receiver, amount);
        return 0;
    }
        else if (f.selector == updateL2State(address).selector) {
        updateL2State(e, aToken);
        return 0;
    }
    else if (f.selector == withdraw(address,uint256,address,uint256,uint256,bool).selector) {
        withdraw(e, aToken, e.msg.sender, receiver, amount, BRIDGE_L2.l2RewardsIndex(),fromToUnderlyingAsset);
        return 0;
    }
    else {
        calldataarg args;
        f(e, args);
        return 0;
    }     
}

////////////////////////////////////////////////////////////////////////////
//                       Summarizations                                   //
////////////////////////////////////////////////////////////////////////////
/*
The following functions are used as summarization (under-approximation)
for the real functions in the code rayMul and rayDiv.
While the real functions assume any value for b,
here it is fixed by value to myConstRayValue() (a is not limited).
This dratically reduces coverage, but can still catch bugs related
to non-conservation of tokens.
The main benefit is the reduced runtime of rules.

To switch on/off the summarization, simply comment the lines
in the methods block of declaring these functions (127-128)
*/

function rayMulConst(uint256 a, uint256 b) returns uint256
{
    uint256 myValue = myConstRayValue();
    uint256 val_Ray = myConstRayValue()/RAY();
    require b == myValue;
    require a <= (max_uint - RAY()/2)/ myValue;
    return to_uint256(val_Ray*a);
}

function rayDivConst(uint256 a, uint256 b) returns uint256 
{
    uint256 myValue = myConstRayValue();
    uint256 val_Ray = myConstRayValue()/RAY();
    require b == myValue;
    require a <= (max_uint - myValue/2) / RAY();
    return to_uint256((2*a + val_Ray) / (2*val_Ray));
}
