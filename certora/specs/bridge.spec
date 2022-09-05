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
    deposit(address, uint256, uint256, uint16, bool) returns (uint256) 
    withdraw(address, uint256, address, uint256, uint256, bool)
    updateL2State(address)
    receiveRewards(uint256, address, uint256)
    
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
    _approveBridgeTokens_Wrapper(address[],uint256[]) envfree
    _getCurrentRewardsIndex_Wrapper(address) returns (uint256) 
    initiateWithdraw_L2(address, uint256, address, bool)
    bridgeRewards_L2(address, uint256)
    getUnderlyingAssetOfAToken(address) returns (address) envfree
    underlyingtoAToken(address) returns (address) => DISPATCHER(true)
    claimRewardsStatic_L2(address)
    getL2AddressOfAToken(address) returns (uint256) envfree
    getApprovedL1TokensLength() returns (uint256) envfree
    getL2Bridge() returns (uint256) envfree
    getIncentivesController() returns (address) envfree
    getRewardToken() returns (address) envfree

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
    LENDINGPOOL_L1.getReserveNormalizedIncome(address)


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
    ATOKEN_A.scaledTotalSupply()
    ATOKEN_B.scaledTotalSupply()
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
    getL1Bridge() returns (address) => DISPATCHER(true)
    REWARD_TOKEN() returns (address) => DISPATCHER(true)
    incentivesController.claimRewards(address[], uint256, address)
    incentivesController.getL1Bridge()
    incentivesController.REWARD_TOKEN()
    
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
    BRIDGE_L2.REW_AAVE() envfree

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

/***************************
 *     Underlying Asset    *
 ***************************/
    UNDERLYING_ASSET_A.totalSupply() returns (uint256) envfree
    UNDERLYING_ASSET_B.totalSupply() returns (uint256) envfree

/***************************
 *     Static A Token      *
 ***************************/
    STATIC_ATOKEN_A.totalSupply() returns (uint256) envfree
    STATIC_ATOKEN_B.totalSupply() returns (uint256) envfree
    STATIC_ATOKEN_A.mint(address, uint256)
    STATIC_ATOKEN_A.burn(address, uint256)
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

definition excludeApproveTokens(method f) returns bool = 
    f.selector != 
    _approveBridgeTokens_Wrapper(address[],uint256[]).selector;

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
//                       New Rules                                        //
////////////////////////////////////////////////////////////////////////////

// @note I received a timeout error when I tried to run the entire spec, so I had to run rules one-by-one
// and therefore turned all invariants into rules

/*
    @Rule 1

    @Description:
        Depositing to nobody should revert and should not change any of the balances
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/77635ad1faf7875f7bec?anonymousKey=a78a890a0850434430c648a68a227707c867b9a6
*/
rule depositToNobody()
{
    env e; 
    uint256 amount;
    address aToken; 
    address underlyingAsset;  
    address staticAToken; 
    uint16 referralCode;
    bool fromUnderlyingAsset;
    uint256 l2Recipient = 0; // deposit to nobody

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);
    
    deposit@withrevert(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);

    bool depositReverted = lastReverted;

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);
    
    assert depositReverted &&
           underlyingAssetBalanceBefore == underlyingAssetBalanceAfter && 
           aTokenBalanceBefore == aTokenBalanceAfter && 
           staticATokenBalanceBefore == staticATokenBalanceAfter &&
           rewardTokenBalanceBefore == rewardTokenBalanceAfter,
           "depositing to nobody should revert and should not change balances";
}

/*
    @Rule 2

    @Description:
        If depositing from underlying asset, then:
        (1) underlying asset balance should decrease by amount deposited
        (2) aToken balance should remain the same
        (3) staticAToken balance should increase by (static) amount deposited 

        If depositing from aToken, then:
        (1) Underlying asset should remain the same
        (2) aToken balance should decrease by amount deposited (according to bound)
        (3) staticAToken balance should increased by (static) amount deposited
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/f851ebaedd0d9c5dd6b8/?anonymousKey=4aa5c410a0fc0e50bb4ef67923c424822a5f8f2a
*/
rule integrityOfDeposit(){
    env e; 
    uint256 amount;
    address aToken;
    address underlyingAsset; 
    address staticAToken;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUnderlyingAsset; 
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    uint256 staticAmount = deposit(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);

    if (fromUnderlyingAsset){
        assert 
        (underlyingAssetBalanceAfter == underlyingAssetBalanceBefore - amount) &&
        (aTokenBalanceAfter == aTokenBalanceBefore) &&
        (staticATokenBalanceAfter == staticATokenBalanceBefore + staticAmount);
    }
    else {
        assert 
        (underlyingAssetBalanceAfter == underlyingAssetBalanceBefore) &&
        (aTokenBalanceAfter - aTokenBalanceBefore + amount <= (indexL1/RAY() + 1)/2) &&
        (staticATokenBalanceAfter == staticATokenBalanceBefore + staticAmount);
    }
}

/*
    @Rule 3

    @Description:
        If balance of staticAToken has changed, it must have come from the deposit or withdraw method
    @Methods:
        All methods (except filtered)
    @Note:
        Expands on Rule "balanceOfUnderlyingAssetChanged" to also include staticAToken balance
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/a3a716b89481649a19ba/?anonymousKey=e3da7b0928f8598aaf0bd2d30c78ddb5a100aee5
*/
rule balancesChanged(method f)
    filtered{f -> messageSentFilter(f)} {
    env e;  
    uint256 amount;  
    address underlyingAsset;
    address aToken;
    address staticAToken;
    address recipient;
    bool fromUnderlyingAsset;
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfter= tokenBalanceOf(e, staticAToken, recipient);

    bool balancesChanged = 
        aTokenBalanceBefore != aTokenBalanceAfter ||
        underlyingAssetBalanceBefore != underlyingAssetBalanceAfter ||
        staticATokenBalanceBefore != staticATokenBalanceAfter;

    assert balancesChanged =>
            (f.selector == deposit(address, uint256, uint256, uint16, bool).selector 
            ||
            f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector)
            , "A balance change must not occur if deposit or withdraw was not called";
}

/*
    @Rule 4

    @Description:
        Deposit increases the L1 bridge's aToken balance by amount (according to bound)
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/f5a8796d3d3f1c5c58bc/?anonymousKey=0134170d92a51b39021d3914f9cbe04eb68896c4
*/
rule depositUpdatesL1Bridge(){
    env e; 
    uint256 amount;
    address aToken; 
    address underlyingAsset; 
    address staticAToken; 
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUnderlyingAsset; 
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 L1BridgeATokenBalanceBefore = tokenBalanceOf(e, aToken, Bridge);
    deposit(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);
    uint256 L1BridgeATokenBalanceAfter = tokenBalanceOf(e, aToken, Bridge);

    assert L1BridgeATokenBalanceAfter - L1BridgeATokenBalanceBefore - amount <= (indexL1/RAY() + 1)/2;
}

/*
    @Rule 5

    @Description:
        Withdrawing to nobody should revert and not change any of the balances
    @Methods:
        withdraw
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/ad26d6b2723e08b177f4/?anonymousKey=a0b8b40137bb5e97e6141a826b75d23e52c61399
*/
rule withdrawToNobody()
{
    env e;
    uint256 amount;
    address aToken;
    address underlyingAsset; 
    address staticAToken; 
    bool toUnderlyingAsset;
    address recipient;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require recipient == 0; // withdraw to nobody

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);
    
    initiateWithdraw_L2@withrevert(e, aToken, amount, recipient, toUnderlyingAsset);

    bool initiateWithdrawReverted = lastReverted;

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);
    
    assert initiateWithdrawReverted &&
           underlyingAssetBalanceBefore == underlyingAssetBalanceAfter && 
           aTokenBalanceBefore == aTokenBalanceAfter && 
           staticATokenBalanceBefore == staticATokenBalanceAfter &&
           rewardTokenBalanceAfter == rewardTokenBalanceBefore, 
           "withdrawing to nobody must revert and balances must not change";
}

/*
    @Rule 6

    @Description:
        Deposit updates the underlying asset, aToken, and staticAToken by the correct amount
    @Methods:
        withdraw
    @Note:
        Expands on Rule "integrityOfWithdraw" to also include:
        (1) The amounts by which balances should change
        (2) The staticAToken balance
        (3) The balances of the sender and recipient
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/140e7d1a7e1cf7a9ff4c/?anonymousKey=1dbe60af3c0121a126341bbc7d66233ad899e80d
*/
rule integrityOfWithdrawExpanded(){
    env e;
    address recipient;
    bool toUnderlyingAsset;
    uint256 staticAmount; 
    address underlyingAsset;
    address staticAToken;
    address aToken;
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require recipient != aToken;
    require recipient != currentContract;

    uint256 dynamicAmount = _staticToDynamicAmount_Wrapper(staticAmount, underlyingAsset, LENDINGPOOL_L1);

    // Recipient balances before
    uint256 recipientUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 recipientStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    // Sender balances before
    uint256 senderUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 senderRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);   

    initiateWithdraw_L2(e, aToken, staticAmount, recipient, toUnderlyingAsset);

    // Recipient balances after
    uint256 recipientUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 recipientStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);
    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    // Sender balances after
    uint256 senderUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 senderStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 senderRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);   

    if (toUnderlyingAsset){
        assert 
        (recipientUnderlyingAssetBalanceAfter == recipientUnderlyingAssetBalanceBefore + dynamicAmount) &&
        (recipientATokenBalanceAfter == recipientATokenBalanceBefore);
    }
    else {
        assert 
        (recipientATokenBalanceAfter == recipientATokenBalanceBefore + dynamicAmount) &&
        (recipientUnderlyingAssetBalanceAfter == recipientUnderlyingAssetBalanceBefore);
    }

    assert
    (senderStaticATokenBalanceAfter == senderStaticATokenBalanceBefore - staticAmount) &&
    (recipientRewardTokenBalanceAfter >= recipientRewardTokenBalanceBefore);
    
    assert e.msg.sender != recipient =>
    ((senderUnderlyingAssetBalanceAfter == senderUnderlyingAssetBalanceBefore) &&
    (senderATokenBalanceAfter == senderATokenBalanceBefore) &&
    (recipientStaticATokenBalanceAfter == recipientStaticATokenBalanceBefore)) &&
    senderRewardTokenBalanceAfter == senderRewardTokenBalanceBefore;
}

/*
    @Rule 7

    @Description:
        Withdraw decreases the L1 bridge's aToken balance by amount (according to bound)
    @Methods:
        withdraw
    @Sanity:
        PASSES
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/c35d888efa4aac265b6a/?anonymousKey=7b0261a19d91c2a66f9149afba131a90be62bc96
*/
rule withdrawUpdatesL1Bridge(){
    env e; 
    uint256 staticAmount;
    address recipient;
    address aToken; 
    address underlyingAsset;  
    address staticAToken; 
    bool toUnderlyingAsset; 
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 dynamicAmount = _staticToDynamicAmount_Wrapper(staticAmount, underlyingAsset, LENDINGPOOL_L1);

    uint256 L1BridgeATokenBalanceBefore = tokenBalanceOf(e, aToken, Bridge);
    initiateWithdraw_L2(e, aToken, staticAmount, e.msg.sender, toUnderlyingAsset);
    uint256 L1BridgeATokenBalanceAfter = tokenBalanceOf(e, aToken, Bridge);

    assert L1BridgeATokenBalanceAfter == L1BridgeATokenBalanceBefore - dynamicAmount;
}

/*
    @Rule 8

    @Description:
        When staticAToken balance is zero, one can not claim:
        (1) Underlying asset
        (2) aTokens
        (3) rewardTokens
    @Methods:
        withdraw
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/2ca2c85be5226dcb3c72/?anonymousKey=fb0de38fbfdfff8182b5f6dd0a70c0f24aadef5e
*/
rule cannotClaimWhenZeroStaticATokens(){
    env e;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    address recipient;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipient);
    uint16 referralCode;
    bool toUnderlyingAsset;
    uint256 staticAmount;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    require senderStaticATokenBalanceBefore == 0; // zero staticATokens

    initiateWithdraw_L2@withrevert(e, aToken, staticAmount, recipient, toUnderlyingAsset);

    bool initiateWithdrawReverted = lastReverted;

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert initiateWithdrawReverted &&
           underlyingAssetBalanceBefore == underlyingAssetBalanceAfter && 
           aTokenBalanceBefore == aTokenBalanceAfter && 
           staticATokenBalanceAfter == staticATokenBalanceBefore &&
           rewardTokenBalanceAfter == rewardTokenBalanceBefore, 
           "balances must not change because sender's staticATokenBalance was zero";
}

/*
    @Rule 9

    @Description:
        If staticAToken balance is zero, then no method should change the balance of staticAToken balance, except deposit
    @Methods:
        All methods (except filtered)
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/f080e7cc743972d73c91/?anonymousKey=7bb2f405ea6b1b62f990d6079a9e31cd26103ae0
*/
rule onlyDepositChangesStaticATokenBalanceWhenZero(method f)
    filtered{f -> messageSentFilter(f)} {
    env e;  
    calldataarg args;
    uint256 amount;  
    address underlyingAsset;
    address aToken;
    address staticAToken;
    address recipient;
    bool fromToUnderlyingAsset;
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    require staticATokenBalanceBefore == 0;

    f@withrevert(e, args);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceAfter= tokenBalanceOf(e, staticAToken, e.msg.sender);

    assert staticATokenBalanceAfter !=  staticATokenBalanceBefore =>
            (f.selector == deposit(address, uint256, uint256, uint16, bool).selector), 
            "A balance change must not occur if deposit was not called as staticAToken balance was zero";
}

/*
    @Rule 10

    @Description:
        An individual's aToken balance is not greater than total supply
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/f21aa4a5760be9f1c207/?anonymousKey=2b4ec635c18424f7733bfdccaf22d479bd89d8bf
*/
rule individualATokenBalanceIsNotGreaterThanTotalSupply(method f) 
    filtered{f -> messageSentFilter(f) && f.selector != initiateWithdraw_L2(address, uint256, address, bool).selector
    && f.selector != deposit(address, uint256, uint256, uint16, bool).selector} {

    address recipient;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    bool fromToUnderlyingAsset;
    uint256 amount;
    env e;
    calldataarg args;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require aToken ==  ATOKEN_A;

    uint256 aTokenTotalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);
    uint256 aTokenAccountBalanceBefore = tokenBalanceOf(e, aToken, recipient);

    f(e, args);

    uint256 aTokenTotalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);
    uint256 aTokenAccountBalanceAfter = tokenBalanceOf(e, aToken, recipient);

    assert aTokenAccountBalanceBefore <= aTokenTotalSupplyBefore => aTokenAccountBalanceAfter <= aTokenTotalSupplyAfter, 
    "individual account aToken balance must not be greater than total supply";
}

/*
    @Rule 11

    @Description:
        An individual's staticAToken balance is not greater than the total supply
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/5aeea10436ddd10cbe4e/?anonymousKey=62cd96d6777bcf8a866a070c991a893078510953
*/
rule individualStaticATokenBalanceIsNotGreaterThanTotalSupply(method f)
    filtered{f -> messageSentFilter(f) && f.selector != initiateWithdraw_L2(address, uint256, address, bool).selector
    && f.selector != deposit(address, uint256, uint256, uint16, bool).selector} {

    address recipient;
    address staticAToken;
    uint256 amount;
    address underlyingAsset;
    address aToken;
    bool fromToUnderlyingAsset;
    env e;
    calldataarg args;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require staticAToken == STATIC_ATOKEN_A;

    uint256 staticATokenTotalSupplyBefore = STATIC_ATOKEN_A.totalSupply();
    uint256 staticATokenAccountBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);

    f(e, args);

    uint256 staticATokenTotalSupplyAfter = STATIC_ATOKEN_A.totalSupply();
    uint256 staticATokenAccountBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);

    assert staticATokenAccountBalanceBefore <= staticATokenTotalSupplyBefore => staticATokenAccountBalanceAfter <= staticATokenTotalSupplyAfter, 
    "individual account staticAToken balance must not be greater than total supply";
}

/*
    @Rule 12

    @Description:
        An individual's underlying asset balance is not greater than the total supply
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/940b07bee4730bfbcbe5/?anonymousKey=11b5d0128c0795d2d648444b90075d3a6d5bdcef
*/
rule individualUnderlyingAssetBalanceIsNotGreaterThanTotalSupply(method f)
    filtered{f -> messageSentFilter(f) && f.selector != initiateWithdraw_L2(address, uint256, address, bool).selector
    && f.selector != deposit(address, uint256, uint256, uint16, bool).selector} {
    address recipient;
    address staticAToken;
    uint256 amount;
    address underlyingAsset;
    address aToken;
    bool fromToUnderlyingAsset;
    env e;
    calldataarg args;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require underlyingAsset == UNDERLYING_ASSET_A;

    uint256 underlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_A.totalSupply();
    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);

    f(e, args);
    //callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 underlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_A.totalSupply();
    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);

    assert underlyingAssetBalanceBefore <= underlyingAssetTotalSupplyBefore => underlyingAssetBalanceAfter <= underlyingAssetTotalSupplyAfter, 
    "individual account staticAToken balance must not be greater than total supply";
}

/*
    @Rule 13

    @Description:
        Total supply of underlying asset should remain constant
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/1a7db5d4185770bc4c88/?anonymousKey=8c3d0716fbdf4decf09e34c4859bebc2dc554c05
*/
rule underlyingAssetTotalSupplyConstant() {
    calldataarg args;
    env e;
    method f;

    uint256 underlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_A.totalSupply();
    f(e, args);
    uint256 underlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_A.totalSupply();

    assert underlyingAssetTotalSupplyBefore == underlyingAssetTotalSupplyAfter, "Underlying Asset Total Supply must remain constant";
}

/*
    @Rule 14

    @Description:
        Total supply of aToken can only increase if the deposit method has been called AND fromUnderlyingAsset is true
        Total supply of aToken can only decrease if the withdraw method has been called AND toUnderlyingAsset is true
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/d94ee1bdb16311cc30f5/?anonymousKey=d9bc08b6bfa4f909f2f70340946c9c85083e29f1
*/
rule aTokenTotalSupplyChange(method f) 
    filtered{f -> messageSentFilter(f)} {
    env eDeposit;
    env eInitiateWithdraw;
    env e;
    calldataarg args;
    address account;
    address recipientDeposit;
    address recipientInitiateWithdraw;
    address aTokenDeposit;
    address aTokenInitiateWithdraw;
    address aToken;
    address underlyingAsset;
    uint256 amount;
    uint256 amountDeposit;
    uint256 amountInitiateWithdraw;
    uint16 referralCode;
    bool fromUnderlyingAsset;
    bool toUnderlyingAsset;
    bool fromToUnderlyingAsset;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipientDeposit);

    require aToken == ATOKEN_A;

    uint256 aTokenTotalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);

    if (f.selector == deposit(address, uint256, uint256, uint16, bool).selector) {
        deposit(eDeposit, aTokenDeposit, l2Recipient, amountDeposit, referralCode, fromUnderlyingAsset);
    } else if (f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector) {
        initiateWithdraw_L2(eInitiateWithdraw, aTokenInitiateWithdraw, amountInitiateWithdraw, recipientInitiateWithdraw, toUnderlyingAsset);
    } else {
        f(e, args);
    }

    uint256 aTokenTotalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);

    if (aTokenTotalSupplyAfter > aTokenTotalSupplyBefore) {
        assert f.selector == deposit(address, uint256, uint256, uint16, bool).selector && fromUnderlyingAsset == true;
    } else if (aTokenTotalSupplyAfter < aTokenTotalSupplyBefore) {
        assert f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector && toUnderlyingAsset == true;
    } else {
        assert aTokenTotalSupplyAfter == aTokenTotalSupplyBefore;
    }
}

/*
    @Rule 15

    @Description:
        Total supply of staticAToken can only increase if the deposit method has been called
        Total supply of staticAToken can only decrease if the withdraw method has been called
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0()) 
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/a30b3aa4839d15b0ad3d/?anonymousKey=5233a0783e218d8b42905e2f6a6d737610b551cd
*/
rule staticATokenTotalSupplyChange() {
    address account;
    address staticAToken;
    calldataarg args;
    method f;
    env e;

    require staticAToken == STATIC_ATOKEN_A;

    uint256 staticATokenTotalSupplyBefore = STATIC_ATOKEN_A.totalSupply();
    f(e, args);
    uint256 staticATokenTotalSupplyAfter = STATIC_ATOKEN_A.totalSupply();

    if (staticATokenTotalSupplyAfter > staticATokenTotalSupplyBefore) {
        assert f.selector == deposit(address, uint256, uint256, uint16, bool).selector;
    } else if (staticATokenTotalSupplyAfter < staticATokenTotalSupplyBefore) {
        assert f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector;
    } else {
        assert staticATokenTotalSupplyBefore == staticATokenTotalSupplyAfter;
    }
}

/*
    @Rule 16

    @Description:
        Can not withdraw amount greater than balance
    @Methods:
        withdraw
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/172035d0ea01c0f7fea4/?anonymousKey=c36cf20a2c4a9f48d52cb05d85b7d915b7418b6f
*/
rule cannotWithdrawAmountGreaterThanStaticATokenBalance(){
    env e;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    address recipient;
    bool toUnderlyingAsset;
    uint256 staticAmount;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    require staticAmount > senderStaticATokenBalanceBefore;

    initiateWithdraw_L2@withrevert(e, aToken, staticAmount, recipient, toUnderlyingAsset);

    bool initiateWithdrawReverted = lastReverted;

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert initiateWithdrawReverted &&
           underlyingAssetBalanceBefore == underlyingAssetBalanceAfter && 
           aTokenBalanceBefore == aTokenBalanceAfter && 
           staticATokenBalanceAfter == staticATokenBalanceBefore, 
           "balances must not change because withdrawal amount is greater than balance";
}

/*
    @Rule 17

    @Description:
        Can not deposit amount greater than balance
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/ccffb6c5e2438ddb5057/?anonymousKey=b795b4a4601d768a2735fc1b363f620dd8574035
*/
rule cannotDepositAmountGreaterThanBalance(){
    env e;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    address recipient;
    uint16 referralCode;
    bool fromUnderlyingAsset;
    uint256 amount;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipient);

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    uint256 senderUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);

    if (fromUnderlyingAsset) {
        require amount > senderUnderlyingAssetBalanceBefore;
    } else {
        require amount > senderATokenBalanceBefore;
    }

    deposit@withrevert(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);

    bool depositReverted = lastReverted;

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert  depositReverted &&
            underlyingAssetBalanceBefore == underlyingAssetBalanceAfter && 
            aTokenBalanceBefore == aTokenBalanceAfter && 
            staticATokenBalanceAfter == staticATokenBalanceBefore, 
            "balances must not change because withdrawal amount is greater than balance";
}

/*
    @Rule 18

    @Description:
        The aToken balance of L1 bridge is greater than or equal to the balance of staticAToken,
        so if everyone withdraws their staticAToken, there is enough aToken to provide to all users
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/8aa48dfa968c6c7d324f/?anonymousKey=e6ddb34f2134880a895f6f20caf79071b4b954bd
*/
rule L1BridgeATokenBalanceGreaterThanStaticATokenTotalSupply() {
    env e;
    method f;
    calldataarg args;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    address account;
    uint256 amount;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(account);
    requireRayIndex(underlyingAsset);

    require staticAToken == STATIC_ATOKEN_A;

    uint256 L1BridgeATokenBalanceBefore = tokenBalanceOf(e, aToken, Bridge);
    uint256 staticATokenTotalSupplyBefore = STATIC_ATOKEN_A.totalSupply();
    uint256 dynamicStaticATokenTotalSupplyBefore = _staticToDynamicAmount_Wrapper(staticATokenTotalSupplyBefore, staticAToken, LENDINGPOOL_L1);

    f(e, args);

    uint256 L1BridgeATokenBalanceAfter = tokenBalanceOf(e, aToken, Bridge);
    uint256 staticATokenTotalSupplyAfter = STATIC_ATOKEN_A.totalSupply();
    uint256 dynamicStaticATokenTotalSupplyAfter = _staticToDynamicAmount_Wrapper(staticATokenTotalSupplyAfter, staticAToken, LENDINGPOOL_L1);

    assert L1BridgeATokenBalanceBefore >= dynamicStaticATokenTotalSupplyBefore => L1BridgeATokenBalanceAfter >= dynamicStaticATokenTotalSupplyAfter,
    "L1 Bridge aToken balance must be greater than staticAToken balance";
}

/*
    @Rule 19

    @Description:
        An account's action does not decrease another account's balance
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/b45996d8fdaa5053eb3d/?anonymousKey=5e5af50032d634372e66fa237cb65ba19b88e32c
*/
rule senderCanNotDecreaseOtherBalance() {
    calldataarg args;
    env e;
    method f;
    address sender;
    address other;
    address aToken;
    address underlyingAsset;
    address staticAToken;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(other);
    requireRayIndex(underlyingAsset);

    require other != e.msg.sender; 
    
    uint256 otherATokenBalanceBefore = tokenBalanceOf(e, aToken, other); 
    uint256 otherUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, other);
    uint256 otherStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, other);
    uint256 otherRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, other);

    f(e, args);

    uint256 otherATokenBalanceAfter = tokenBalanceOf(e, aToken, other); 
    uint256 otherUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, other);
    uint256 otherStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, other);
    uint256 otherRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, other);

    assert otherATokenBalanceAfter >= otherATokenBalanceBefore &&
           otherUnderlyingAssetBalanceAfter >= otherUnderlyingAssetBalanceBefore &&
           otherStaticATokenBalanceAfter >= otherStaticATokenBalanceBefore &&
           otherRewardTokenBalanceAfter >= otherRewardTokenBalanceBefore, 
           "The balances must not decrease"; 
}

/*
    @Rule 20

    @Description:
        Methods for one aToken, underlyingAsset, staticAToken group do not affect another aToken, underlyingAsset, staticAToken group's balance.
        In other words, the correct tokens are minted/burned. No other tokens are minted/burned.
    @Methods:
        All
    @SANITY:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/40fe434226214f3e1006/?anonymousKey=62941220c78925bdc8d3dac4123ac99a6da9c760
*/
rule otherTokensBalanceDoesNotChange(method f) 
filtered{f -> messageSentFilter(f)}
{
    env e; 
    uint256 amount;
    address aToken; 
    address otherAToken;
    address underlyingAsset;  
    address otherUnderlyingAsset;
    address staticAToken; 
    address otherStaticAToken;
    address recipient;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipient);
    uint16 referralCode;
    bool fromToUnderlyingAsset; 
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupTokens(otherUnderlyingAsset, otherAToken, otherStaticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require otherStaticAToken != staticAToken;
    require otherUnderlyingAsset != underlyingAsset;
    require otherAToken != aToken;

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    uint256 otherUnderlyingAssetBalanceBefore = tokenBalanceOf(e, otherUnderlyingAsset, e.msg.sender);
    uint256 otherATokenBalanceBefore = tokenBalanceOf(e, otherAToken, e.msg.sender);   
    uint256 otherStaticATokenBalanceBefore = tokenBalanceOf(e, otherStaticAToken, e.msg.sender);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);

    uint256 otherUnderlyingAssetBalanceAfter = tokenBalanceOf(e, otherUnderlyingAsset, e.msg.sender);
    uint256 otherATokenBalanceAfter = tokenBalanceOf(e, otherAToken, e.msg.sender);   
    uint256 otherStaticATokenBalanceAfter = tokenBalanceOf(e, otherStaticAToken, e.msg.sender);

    assert otherStaticATokenBalanceAfter == otherStaticATokenBalanceBefore && 
           otherATokenBalanceAfter == otherATokenBalanceBefore &&
           otherUnderlyingAssetBalanceAfter == otherUnderlyingAssetBalanceBefore;
}

/*
    @Rule 21

    @Description:
        Methods for one aToken, underlyingAsset, staticAToken group do not affect another aToken, underlyingAsset, staticAToken group's supply.
        In other words, the correct tokens are minted/burned. No other tokens are minted/burned.
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/d848aa226153e9a366be/?anonymousKey=774d9d4eb10ae3cd307d61625366c6f88a2ac484
*/
rule otherTokensSupplyDoesNotChange(method f) 
    filtered{f -> messageSentFilter(f)} {
    env e; 
    uint256 amount;
    address aToken; 
    address otherAToken;
    address underlyingAsset;  
    address otherUnderlyingAsset;
    address staticAToken; 
    address otherStaticAToken;
    address recipient;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipient);
    uint16 referralCode;
    bool fromToUnderlyingAsset; 
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupTokens(otherUnderlyingAsset, otherAToken, otherStaticAToken);
    setupUser(e.msg.sender);
    setupUser(recipient);
    requireRayIndex(underlyingAsset);

    require otherStaticAToken != staticAToken;
    require otherUnderlyingAsset != underlyingAsset;
    require otherAToken != aToken;

    uint256 aTokenTotalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);
    uint256 underlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_A.totalSupply();

    uint256 otherATokenTotalSupplyBefore = ATOKEN_B.scaledTotalSupply(e);
    uint256 otherUnderlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_B.totalSupply();

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 aTokenTotalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);
    uint256 underlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_A.totalSupply();

    uint256 otherATokenTotalSupplyAfter = ATOKEN_B.scaledTotalSupply(e);
    uint256 otherUnderlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_B.totalSupply();

    assert otherATokenTotalSupplyAfter == otherATokenTotalSupplyBefore && 
           otherUnderlyingAssetTotalSupplyAfter == otherUnderlyingAssetTotalSupplyBefore;
}

/*
    @Rule 22

    @Description:
        The following relation between staticAToken, aToken and underlyingAsset must always hold:
        staticAToken <= aToken <= underlyingAsset
    @Note:
        Could be made stronger by removing filter
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/f3a44065dacd61b619e6/?anonymousKey=ace1d95fb71ee553d5b012399c12180de331bebd
*/
rule relationBetweenATokenAndUnderlyingAsset(method f) 
    filtered{f -> f.selector != deposit(address, uint256, uint256, uint16, bool).selector}{
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require staticAToken == STATIC_ATOKEN_A;
    require aToken == ATOKEN_A;
    require underlyingAsset == UNDERLYING_ASSET_A;

    uint256 aTokenTotalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);
    uint256 underlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_A.totalSupply();

    f(e, args);

    uint256 aTokenTotalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);
    uint256 underlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_A.totalSupply();

    assert (aTokenTotalSupplyBefore <= underlyingAssetTotalSupplyBefore) => (aTokenTotalSupplyAfter <= underlyingAssetTotalSupplyAfter);
}

/*
    @Rule 23

    @Description:
        Initialize reverts with messagingContract = 0
    @Methods:
        Initialize
    @Note:
        Expect that initialize reverts with a zero messaging contract, but this fails
    @Sanity:
        PASSES
    @Outcome:
         FAILS
    @Link:
        https://prover.certora.com/output/69969/b50001c2e3a367c74415/?anonymousKey=f685d22c97a60c6094d7a707d9963a231c2bdb4f
*/
rule initializeRevertsWithZeroMessagingContract() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;
    address[] l1Tokens;
    uint256[] l2Tokens;

    require messagingContract == 0;
    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);
    assert lastReverted;
}

/*
    @Rule 24

    @Description:
        Initialize reverts with L2 Bridge = 0
    @Methods:
        Initialize
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/75993add7a536f69e2be/?anonymousKey=f9155f450ecd1f6657d89cb23f26c8d3d3ff4978
*/
rule initializeRevertsWithZeroL2Bridge() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;
    address[] l1Tokens;
    uint256[] l2Tokens;

    require l2Bridge == 0;

    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);
    assert lastReverted;
}

/*
    @Rule 25

    @Description:
        Initialize reverts with incentives controller = 0
    @Methods:
        Initialize
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/8065b63e18f4be1d0883/?anonymousKey=9cb676c8322f97b16aaea9fb86ee4adbcd8863ba

*/
rule initializeRevertsWithZeroIncentivesController() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;
    address[] l1Tokens;
    uint256[] l2Tokens;

    require incentivesControllerAddress == 0;

    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);
    assert lastReverted;
}

/*
    @Rule 26

    @Description:
        Initialize reverts with empty L1 tokens and L2 tokens
    @Methods:
        Initialize
    @Note:
        Expect that initialize reverts when given empty tokens but fails
    @Sanity:
        PASSES
    @Outcome:
         FAILS
    @Link:
        https://prover.certora.com/output/69969/8d14252ebc42c54f2e2a/?anonymousKey=1a0a9603ecc92ad7d16cb0d3016d7825dcbc9fa6
*/
rule initializeRevertsWithEmptyTokens() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;
    address[] l1Tokens = [];
    uint256[] l2Tokens = [];

    // require l1Tokens.length == 0 && l2Tokens.length == 0;

    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);
    assert lastReverted;
}

/*
    @Rule 27

    @Description:
        Can not withdraw twice if the first withdraw was a full withdraw
    @Methods:
        withdraw
    @Note:
        Rule cannotWithdrawAmountGreaterThanStaticATokenBalance possibly covers this rule
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/99f868b82624fbf20917/?anonymousKey=bf05baa80e745be9615e2a3034343618ce435f8e
*/
rule noDoubleWithdrawIfFullyWithdrawnOnce(){
    address underlyingAsset;
    address staticAToken;
    address aToken;
    address recipient;
    bool toUnderlyingAsset;
    uint256 staticAmount; 
    uint256 staticAmount2;
    env e;
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    require recipient != aToken;
    require recipient != currentContract;

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    require staticAmount == senderStaticATokenBalanceBefore;
    require staticAmount2 > 0;

    initiateWithdraw_L2(e, aToken, staticAmount, recipient, toUnderlyingAsset);

    uint256 underlyingAssetBalanceAfterFirstWithdraw = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    initiateWithdraw_L2@withrevert(e, aToken, staticAmount2, recipient, toUnderlyingAsset);

    bool initiateWithdrawReverted = lastReverted;

    uint256 underlyingAssetBalanceAfterSecondWithdraw = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert initiateWithdrawReverted &&
           underlyingAssetBalanceAfterSecondWithdraw == underlyingAssetBalanceAfterFirstWithdraw && 
           aTokenBalanceAfterSecondWithdraw == aTokenBalanceAfterFirstWithdraw &&
           staticATokenBalanceAfterSecondWithdraw == staticATokenBalanceAfterFirstWithdraw &&
           rewardTokenBalanceAfterSecondWithdraw == rewardTokenBalanceAfterFirstWithdraw;
}

/*
    @Rule 28

    @Description:
        Only the owner of the tokens can change their balances
    @Methods:
        All 
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/9f61418b5167c81f0356/?anonymousKey=c92945abdf5927122138f42038fc111a28f8d84a
        
*/
rule onlyOwnerCanDecreaseBalances() {
	method f;
	env e;
	calldataarg args;
	address owner;
    address recipient;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    uint256 amount;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(owner);
	
    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, owner);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, owner);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, owner);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, owner);

    f(e, args);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, owner);
    uint256 aTokenBalanceAfter= tokenBalanceOf(e, aToken, owner);
    uint256 staticATokenBalanceAfter= tokenBalanceOf(e, staticAToken, owner);
    uint256 rewardTokenBalanceAfter= tokenBalanceOf(e, REWARD_TOKEN, owner);
    
    assert underlyingAssetBalanceAfter < underlyingAssetBalanceBefore => owner == e.msg.sender, 
           "If balances decreased, owner must have been the e.msg.sender of the function";
    assert aTokenBalanceAfter < aTokenBalanceBefore => owner == e.msg.sender, 
           "If balances decreased, owner must have been the e.msg.sender of the function"; 
    assert staticATokenBalanceAfter < staticATokenBalanceBefore => owner == e.msg.sender, 
           "If balances decreased, owner must have been the e.msg.sender of the function"; 
    assert rewardTokenBalanceAfter < rewardTokenBalanceBefore => owner == e.msg.sender, 
           "If balances decreased, owner must have been the e.msg.sender of the function"; 
}

/*
    @Rule 29

    @Description:
        Deposit with zero value should revert
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/37fb5df6cedd380e5988/?anonymousKey=41b16a6aadf09910c0d71103060b62374ac52da3
        
*/
rule depositWithZeroValue(){
    env e; 
    uint256 amount;
    address aToken; 
    address underlyingAsset; 
    address staticAToken; 
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUnderlyingAsset; 
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require amount == 0;

    deposit@withrevert(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);

    assert lastReverted;
}

/*
    @Rule 30

    @Description:
        Withdraw with zero value should revert
    @Methods:
        withdraw
    @Sanity:
        PASSES
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/f7a42ad2e18f77624c2f/?anonymousKey=3ed710c0acb04eefd538ff2b54b14a71c1e47b02
        
*/
rule withdrawWithZeroValue(){
    env e; 
    uint256 staticAmount;
    address aToken; 
    address underlyingAsset; 
    address staticAToken; 
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool toUnderlyingAsset; 
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require staticAmount == 0;

    initiateWithdraw_L2@withrevert(e, aToken, staticAmount, e.msg.sender, toUnderlyingAsset); 

    assert lastReverted;
}

/*
    @Rule 31 

    @Description:
        updateL2State should update the L2rewards index to the L1 current rewards index 
    @Methods:
        updateL2state
    @Sanity:
        PASSES
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/ea44a2dd43bad60803b3/?anonymousKey=910cc3dac3ff2edba91cca425f298c9460ff4e76
        
*/
rule integrityOfUpdateL2State(){
    address L1AToken;
    env e;

    updateL2State(e, L1AToken);

	assert BRIDGE_L2.l2RewardsIndex() == _getCurrentRewardsIndex_Wrapper(e, L1AToken);
}

/*
    @Rule 32 

    @Description:
        A user can only claim rewards once
    @Methods:
        claimRewards
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/84243c0726af0e16ac3d/?anonymousKey=cead2d3917b36267895dd3edfe076016394c51ce
        
*/
rule canOnlyClaimRewardsOnce(){
    address staticAToken;
    env e;

    claimRewardsStatic_L2@withrevert(e, staticAToken);
    bool firstRevert = lastReverted;

	claimRewardsStatic_L2@withrevert(e, staticAToken);
    bool secondRevert = lastReverted;

    assert !firstRevert => secondRevert, "claimRewards must only succeed once";
}

/*
    @Rule 33 

    @Description:
        Claiming rewards should increase the users rewAAVE token balance
        if the unclaimed rewards > 0
    @Methods:
        claimRewards
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/ad29332a3426708d3654/?anonymousKey=8560cd9f178b78d9b404081fdb6a606efddac4e9
        
*/
rule integrityOfClaimRewards(){
    env e;
    address staticAToken;
    setupUser(e.msg.sender);

    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);
    claimRewardsStatic_L2@withrevert(e, staticAToken);
    bool reverted = lastReverted;
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);

    // Claim rewards reverts if the amount to claim is zero (checked by rule: canOnlyClaimRewardsOnce)
    // so I check that the amount to claim is not zero (by checking that it did not revert) and
    // verify whether the reward token balance increased
    assert !reverted => rewardTokenBalanceAfter > rewardTokenBalanceBefore;

    // if the amount to claim is zero (and thus reverts), the reward token balance should remain the same
    assert reverted => rewardTokenBalanceAfter == rewardTokenBalanceBefore;
}

/*
    @Rule 34 

    @Description:
        Bridging rewards from L2 to L1:
        1. Burns the rewAAVE (i.e. decreases L2 sender user's balance of rewAAVE)
        2. L1 receives rewards and transfers to L1 recipient
    @Methods:
        bridgeRewards
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/adaae9a55d4faf2a06fe/?anonymousKey=a4d01fec00b9f808ae57c889af1153b53aad3cb4
        
*/
rule integrityOfBridgeRewards(){
    uint256 amount;
    address recipient;
    env e;

    setupUser(e.msg.sender);
    setupUser(recipient);

    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 senderRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);

    bridgeRewards_L2(e, recipient, amount);

    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 senderRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender);

    assert e.msg.sender != recipient => (recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore + amount) && 
                                        (senderRewardTokenBalanceAfter == senderRewardTokenBalanceBefore - amount);
    assert e.msg.sender == recipient => recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore;
}

/*
    @Rule 35 

    @Description:
        Claiming rewards does not affect others 
    @Methods:
        claimRewards
    @Note:
        Might be covered by other rule
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/6602b02325ee18495bb6/?anonymousKey=540561f2fcc311da736ce406e92daf414274cbca 
*/
rule claimRewardsDoesNotAffectOthers() {
    env e;
    address staticAToken;
    address aToken;
    address underlyingAsset;
    address other;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require e.msg.sender != other;

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, other);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, other);   
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, other);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, other);

    claimRewardsStatic_L2(e, staticAToken);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, other);
    uint256 aTokenBalanceAfter= tokenBalanceOf(e, aToken, other);   
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, other);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, other);

    assert rewardTokenBalanceAfter == rewardTokenBalanceBefore &&
           underlyingAssetBalanceAfter ==  underlyingAssetBalanceBefore &&
           staticATokenBalanceAfter == staticATokenBalanceBefore &&
           aTokenBalanceAfter == aTokenBalanceBefore;
}

/*
    @Rule 36 

    @Description:
        Bridging rewards does not affect others 
    @Methods:
        bridgeRewards
    @Note:
        Might be covered by other rule
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/42843a73c00eec51b9c1/?anonymousKey=ef9a6ae20dc75756432dcfca0ea0bb5db820771f
*/
rule bridgeRewardsDoesNotAffectOthers() {
    env e;
    address staticAToken;
    address aToken;
    address underlyingAsset;
    address other;
    address recipient;
    uint256 amount;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require recipient != other;
    require e.msg.sender != other;

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, other);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, other);   
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, other);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, other);

    bridgeRewards_L2(e, recipient, amount);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, other);
    uint256 aTokenBalanceAfter= tokenBalanceOf(e, aToken, other);   
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, other);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, other);

    assert rewardTokenBalanceAfter == rewardTokenBalanceBefore &&
           underlyingAssetBalanceAfter ==  underlyingAssetBalanceBefore &&
           staticATokenBalanceAfter == staticATokenBalanceBefore &&
           aTokenBalanceAfter == aTokenBalanceBefore;
}

/*
    @Rule 37 

    @Description:
        Claiming rewards does not affect token balances (except reward token)
    @Methods:
        claimRewards
    @Note
        This rule might already be covered by the balancesChanged rule
    @Sanity:
        PASSES
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/b031b237b3f62c46c665/?anonymousKey=892f1c49cc4acefa85ccf4c00c94e1f626dc0e69
*/
rule claimRewardsDoesNotAffectBalances(){
    env e;
    address staticAToken;
    address aToken;
    address underlyingAsset;
    address recipient;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);   
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    claimRewardsStatic_L2(e, staticAToken);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);   
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);

    assert  staticATokenBalanceAfter == staticATokenBalanceBefore &&
            aTokenBalanceAfter == aTokenBalanceBefore &&
            underlyingAssetBalanceAfter == underlyingAssetBalanceBefore;
}

/*
    @Rule 38 

    @Description:
        Bridging rewards does not affect token balances (except reward token)
    @Methods:
        bridgeRewards
    @Note: 
        This rule might already covered by the balancesChanged rule
    @Sanity:
        PASSES
    @Outcome:
         PASSES
    @Link:
        https://prover.certora.com/output/69969/4477823b16e73c0187e4/?anonymousKey=425b989ba1f14a0eebe226a800c97751435e1d96
*/
rule bridgeRewardsDoesNotAffectBalances(){
    env e;
    address underlyingAsset;
    address aToken;
    address staticAToken;
    address recipient;
    uint256 amount;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(recipient);

    requireRayIndex(underlyingAsset);

    uint256 senderUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);   
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);

    uint256 recipientUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);   
    uint256 recipientStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);

    bridgeRewards_L2(e, recipient, amount);

    uint256 senderUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceAfter= tokenBalanceOf(e, aToken, e.msg.sender);   
    uint256 senderStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);

    uint256 recipientUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);   
    uint256 recipientStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);

    assert  recipientStaticATokenBalanceAfter == recipientStaticATokenBalanceBefore &&
            recipientATokenBalanceAfter == recipientATokenBalanceBefore &&
            recipientUnderlyingAssetBalanceAfter == recipientUnderlyingAssetBalanceBefore &&
            senderStaticATokenBalanceAfter == senderStaticATokenBalanceBefore &&
            senderATokenBalanceAfter == senderATokenBalanceBefore &&
            senderUnderlyingAssetBalanceAfter == senderUnderlyingAssetBalanceBefore;
}

/*
    @Rule 39 

    @Description:
        Reward token balance should only increase if claimRewards, bridgeRewards, or withdraw has been called 
        from the appropiate sender and recipient and only decrease if bridgeRewards has been called from the appropiate sender
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/e427861f7ef4ade91d37/?anonymousKey=50ae687a8aa9f78f69fd478e4f108b5e52748df8
*/
rule rewardTokenBalanceChanged(method f)
    filtered{f -> messageSentFilter(f)} {
    env e; 
    address recipient; 
    address aToken;
    address staticAToken;
    address user;
    address underlyingAsset;
    bool fromUnderlyingAsset;
    uint256 amount;  

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(user);
    setupUser(recipient);

    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, user);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromUnderlyingAsset);

    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, user);

    bool rewardTokenBalanceIncrease = rewardTokenBalanceAfter > rewardTokenBalanceBefore;
    bool rewardTokenBalanceDecrease = rewardTokenBalanceAfter < rewardTokenBalanceBefore;

    assert rewardTokenBalanceIncrease =>
            (f.selector == claimRewardsStatic_L2(address).selector && user == e.msg.sender ||
            f.selector == bridgeRewards_L2(address, uint256).selector && user == recipient ||
            f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector && user == recipient)
            , "A reward token balance increase must not occur if claimRewards, bridgeRewards or withdraw was not called";

    assert rewardTokenBalanceDecrease =>
            (f.selector == bridgeRewards_L2(address, uint256).selector && user == e.msg.sender)
            , "A reward token balance decrease must not occur if claimRewards, bridgeRewards or withdraw was not called";
}

/*
    @Rule 40 

    @Description:
        Compute rewards diff should revert if the L1 rewards index is less than the L2 rewards index
    @Methods:
        computeRewardsDiff
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/6838cfe4dd856a616d87/?anonymousKey=a0e89f20aa5573c01a8931b12774ebc6f1a2ecf8
        
*/
rule computeRewardsDiffShouldRevertWithInvalidArguments(){
    uint256 amount;
    uint256 l2RewardsIndex;
    uint256 l1RewardsIndex;

    require l1RewardsIndex < l2RewardsIndex;

    _computeRewardsDiff_Wrapper@withrevert(amount,l2RewardsIndex,l1RewardsIndex);

    assert lastReverted;
}

/*
    @Rule 41 

    @Description:
        Only the bridge can mint staticATokens
    @Methods:
        mint
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/9dca2ae51aadcfb6b6e7/?anonymousKey=b5401a917168e0c6fc1adb3369c489ec23c18faa
*/
rule onlyBridgeCanMintStaticATokens(){
	env e;
    uint256 amount;
    address user;

    require STATIC_ATOKEN_A.owner(e) == BRIDGE_L2;

    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, STATIC_ATOKEN_A, user);
    
    STATIC_ATOKEN_A.mint@withrevert(e, user, amount);
    bool reverted = lastReverted;

    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, STATIC_ATOKEN_A, user);

    assert staticATokenBalanceBefore != staticATokenBalanceAfter => e.msg.sender == BRIDGE_L2, "The caller of 'mint' must be the L2 Bridge";
    // different way to check
    assert !reverted => e.msg.sender == BRIDGE_L2, "The caller of 'mint' must be the L2 Bridge";
}

/*
    @Rule 42 

    @Description:
        Only the bridge can burn staticATokens
    @Methods:
        burn
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/111e263a9a7d332b2b19/?anonymousKey=5186a1e57fff606fe11e6182dbf8bf5527e069b3
*/
rule onlyBridgeCanBurnStaticATokens(){
	env e;
    uint256 amount;
    address user;

    require STATIC_ATOKEN_A.owner(e) == BRIDGE_L2;

    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, STATIC_ATOKEN_A, user);
    STATIC_ATOKEN_A.burn@withrevert(e, user, amount);
    bool reverted = lastReverted;

    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, STATIC_ATOKEN_A, user);

    assert staticATokenBalanceBefore != staticATokenBalanceAfter => e.msg.sender == BRIDGE_L2, "The caller of 'burn' must be the L2 Bridge";
    // different way to check
    assert !reverted => e.msg.sender == BRIDGE_L2, "The caller of 'burn' must be the L2 Bridge";
}

/*
    @Rule 43 

    @Description:
        Approve Tokens should revert when the length of the l1Tokens array and l2Tokens array are different
    @Methods:
        _approveBridgeTokens
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/ccaaa575842a7dd70aa0/?anonymousKey=2e55411569cb769d84577649024e5a42d5fc5279
*/
rule approveTokensRevertsWithInvalidArguments() {
    env e;

    // require l1Tokens.length != l2Tokens.length;

    address[] l1Tokens = [ATOKEN_A, ATOKEN_B];
    uint256[] l2Tokens = [STATIC_ATOKEN_A];

    _approveBridgeTokens_Wrapper@withrevert(l1Tokens,l2Tokens);

    assert lastReverted;
}

/*
    @Rule 44 

    @Description:
        receiveRewards should increase recipient's rewards and keep callers rewards the same
    @Methods:
        receiveRewards
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/4555bbc65830aa6e6761/?anonymousKey=ac4bf89c607209512d4fcb964931e3f6ddc8134a
*/
rule integrityOfReceiveRewards() {
    uint256 l2sender;
    address recipient;
    uint256 amount;
    env e;

    setupUser(e.msg.sender);
    setupUser(recipient);

    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    receiveRewards(e,l2sender, recipient, amount);

    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore + amount;
}

/*
    @Rule 45 

    @Description:
        claimRewards should increase recipient's rewards by amount and 
        decrease incentives controllers rewards by amount
    @Methods:
        claimRewards
    @Sanity:
        PASSES 
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/ee0bb967f397883956b9/?anonymousKey=ee5763e4b478a91838485596f927d59c7823f815
*/
rule integrityOfIncentivesControllerClaimRewards() {
    address[] assets;
    uint256 amount;
    address recipient;
    env e;

    require recipient != incentivesController;

    uint256 incentivesControllerRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, incentivesController);
    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    incentivesController.claimRewards(e, assets, amount, recipient);

    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 incentivesControllerRewardTokenBalanceAfter= tokenBalanceOf(e, REWARD_TOKEN, incentivesController);

    assert (recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore + amount) &&
           (incentivesControllerRewardTokenBalanceAfter == incentivesControllerRewardTokenBalanceBefore - amount); 
}

/*
    @Rule 46 

    @Description:
        Zero address should not have its balance changed
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/a10861d6a4efc8bd25f4/?anonymousKey=1b2d8e08f767e913a3cd3ff50d94f5734257aa0e
*/
rule zeroAddressBalanceDoesNotChange() {
    method f;
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;
    uint256 amount;
    address user;
    address recipient;
    bool fromToUnderlyingAsset;

    require user == 0;
    require e.msg.sender != 0;

    setupTokens(underlyingAsset, aToken, staticAToken);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, user);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, user);   
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, user);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, user);

    f(e, args);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, user);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, user);   
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, user);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, user);

    assert underlyingAssetBalanceAfter == underlyingAssetBalanceBefore &&
           aTokenBalanceAfter == aTokenBalanceBefore &&
           staticATokenBalanceAfter == staticATokenBalanceBefore &&
           rewardTokenBalanceAfter == rewardTokenBalanceBefore;
}

/*
    @Rule 47

    @Description:
        If individual balance increases, total supply increases and vice versa
        If individual balance decreases, total supply decreases and vice versa
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        FAIL 
    @Link:
        https://prover.certora.com/output/69969/d522a066ce76aa2feab9/?anonymousKey=387c69bfbd4b3c0c475388a1ad0335b660c1b967
*/
rule monotonicityStaticATokenBalanceTotalSupply() {
    method f;
    env e;
    calldataarg args;
    address underlyingAsset;
    address staticAToken;
    address recipient;
    address aToken;
    address asset;
    uint256 amount;
    address user;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(user);
    setupUser(recipient);

    require staticAToken == STATIC_ATOKEN_A;

    uint256 balanceBefore = tokenBalanceOf(e, staticAToken, user);
    uint256 totalSupplyBefore = STATIC_ATOKEN_A.totalSupply();

    f(e, args);

    uint256 balanceAfter = tokenBalanceOf(e, staticAToken, user);
    uint256 totalSupplyAfter = STATIC_ATOKEN_A.totalSupply();

    assert balanceAfter > balanceBefore => totalSupplyAfter > totalSupplyBefore;
    assert balanceAfter < balanceBefore => totalSupplyAfter < totalSupplyBefore;
}

/*
    @Rule 48 

    @Description:
        If individual balance increases, total supply increases and vice versa
        If individual balance decreases, total supply decreases and vice versa
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/36e0f129bf1c67f07093/?anonymousKey=9bb4d7fc77ceb169318df6de40f76230b6f190b1
*/
rule monotonicityATokenBalanceTotalSupply() {
    method f;
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address recipient;
    address asset;
    address staticAToken;
    uint256 amount;
    address user;
    bool fromToUnderlyingAsset;

    require aToken == ATOKEN_A;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(user);
    setupUser(recipient);

    uint256 balanceBefore = tokenBalanceOf(e, aToken, user);
    uint256 totalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 balanceAfter = tokenBalanceOf(e, aToken, user);
    uint256 totalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);

    assert balanceAfter > balanceBefore => totalSupplyBefore == totalSupplyAfter;
    assert balanceAfter < balanceBefore => totalSupplyBefore == totalSupplyAfter;
    assert (fromToUnderlyingAsset && f.selector == deposit(address, uint256, uint256, uint16, bool).selector) => (balanceAfter == balanceBefore) => (totalSupplyAfter > totalSupplyBefore);
    assert (!fromToUnderlyingAsset && f.selector == deposit(address, uint256, uint256, uint16, bool).selector) => (balanceAfter == balanceBefore) => (totalSupplyAfter < totalSupplyBefore);
    assert (fromToUnderlyingAsset && f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector) => (balanceAfter == balanceBefore) => (totalSupplyAfter < totalSupplyBefore);
    assert (!fromToUnderlyingAsset && f.selector == initiateWithdraw_L2(address, uint256, address, bool).selector) => (balanceAfter == balanceBefore) => (totalSupplyAfter > totalSupplyBefore);
}

/*
    @Rule 49 

    @Description:
        aToken Data must only change through initialise and approveTokens
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/710247b9f6195674167c/?anonymousKey=c05650ea44e021ecb96db28f8d4af686e9526ae7
*/
rule aTokenDataChange() {
    method f;
    env e;
    calldataarg args;
    address aToken;

    uint256 l2AddressBefore = getL2AddressOfAToken(aToken);
    address underlyingAssetBefore = getUnderlyingAssetOfAToken(aToken);
    address lendingPoolBefore = getLendingPoolOfAToken(aToken);

    f(e,args);

    uint256 l2AddressAfter = getL2AddressOfAToken(aToken);
    address underlyingAssetAfter = getUnderlyingAssetOfAToken(aToken);
    address lendingPoolAfter = getLendingPoolOfAToken(aToken);

    bool aTokenDataChange = l2AddressAfter != l2AddressBefore || underlyingAssetAfter != underlyingAssetBefore || lendingPoolAfter != lendingPoolBefore;

    assert aTokenDataChange => f.selector == initialize(uint256, address, address, address[], uint256[]).selector ||
                               f.selector == _approveBridgeTokens_Wrapper(address[],uint256[]).selector;
}

/*
    @Rule 50

    @Description:
        Check consistency that 'l2Address' is being registered as the staticAToken token of 'AToken', 
        both in the BridgeL2 AtokenToStaticAToken_L2 mapping, and also in the mapping _aTokenData.
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/79701e80c7cdef85c747/?anonymousKey=e2431731832c121eaa6e70bce803b749ad4781ce
*/
rule staticATokenCorrespondsToAToken(method f)
    filtered{f-> excludeInitialize(f) && excludeApproveTokens(f)} {
    env e;
    calldataarg args;
    address aToken;

    uint256 l2TokenAddressBefore = getL2AddressOfAToken(aToken); // from ATokenData
    uint256 staticATokenBefore = BRIDGE_L2.address2uint256(BRIDGE_L2.getStaticATokenAddress(aToken)); // from mapping in BridgeL2Harness

    f(e, args);

    uint256 l2TokenAddressAfter = getL2AddressOfAToken(aToken); // from ATokenData
    uint256 staticATokenAfter =  BRIDGE_L2.address2uint256(BRIDGE_L2.getStaticATokenAddress(aToken)); // from mapping in BridgeL2Harness

    assert l2TokenAddressBefore == staticATokenBefore <=> l2TokenAddressAfter == staticATokenAfter; 
}

/*
    @Rule 51

    @Description:
        L1 Bridge should not have balances except aToken balance
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/23294f8739788de1de8c/?anonymousKey=ac14d99f781c57e3db9ce9fa67b3da263df30864
*/
rule L1BridgeBalancesZeroExceptAToken(method f)
    filtered{f -> messageSentFilter(f)} {
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;
    address recipient;
    uint256 amount;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(recipient);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, Bridge);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, Bridge);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, Bridge);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, Bridge);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, Bridge);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, Bridge);

    assert (underlyingAssetBalanceBefore == 0 &&
           staticATokenBalanceBefore == 0 &&
           rewardTokenBalanceBefore == 0) => 
           (underlyingAssetBalanceAfter == 0 &&
           staticATokenBalanceAfter == 0 &&
           rewardTokenBalanceAfter == 0);
}

/*
    @Rule 52

    @Description:
        L2 Bridge should not have balance
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/d63afdef6acf30763fb3/?anonymousKey=69b82f1f523aa0a60f604a427061f3a1b48fa5e3
*/
rule L2BridgeBalancesZero(method f)
    filtered{f -> messageSentFilter(f)} {
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;
    address recipient;
    uint256 amount;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(recipient);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, BRIDGE_L2);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, BRIDGE_L2);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, BRIDGE_L2);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, BRIDGE_L2);

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, BRIDGE_L2);
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, BRIDGE_L2);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, BRIDGE_L2);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, BRIDGE_L2);

    assert (underlyingAssetBalanceBefore == 0 &&
           staticATokenBalanceBefore == 0 &&
           rewardTokenBalanceBefore == 0 &&
           aTokenBalanceBefore == 0) => 
           (underlyingAssetBalanceAfter == 0 &&
           staticATokenBalanceAfter == 0 &&
           rewardTokenBalanceAfter == 0 &&
           aTokenBalanceAfter == 0);
}

/*
    @Rule 53

    @Description:
        Update L2 state should revert if L1 rewards index is less than L2 rewards index,
        _computeRewardsDiff_Wrapper reverts if L1 rewards index is less than L2 rewards index.
    @Methods:
        updateL2State
    @Note:
        Expected to revert, but does not
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/6e7b7e2a4b8a4e7e4444/?anonymousKey=2164a342fad5ee834bc861338225e31f27a43aff
*/
rule updateL2StateRevertsIfL2IndexGreaterThanL1(){
    env e;
    address L1AToken;
    uint256 L1RewardsIndex = _getCurrentRewardsIndex_Wrapper(e, L1AToken);
    uint256 L2RewardsIndex = BRIDGE_L2.l2RewardsIndex();

    require L1RewardsIndex < L2RewardsIndex;

    updateL2State@withrevert(e, L1AToken);

    assert lastReverted;
}

/*
    @Rule 54

    @Description:
        Approve Tokens reverts when the length of the arrays are empty
    @Methods:
        _approveBridgeTokens
    @Note:
        Expected to revert but does not
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/5fc2211fedb2817751b0/?anonymousKey=72ebaf6ec84f694a2829d0dc4b44fdcda85b1a14
*/
rule approveTokensRevertsWhenEmpty() {
    address[] l1Tokens = [];
    uint256[] l2Tokens = [];
    env e;

    // require l1Tokens.length == 0 && l2Tokens.length == 0;

    _approveBridgeTokens_Wrapper@withrevert(l1Tokens,l2Tokens);

    assert lastReverted;
}

/*
    @Rule 55

    @Description:
        Approve Tokens should increase approved L1 Tokens Array
    @Methods:
        _approveBridgeTokens
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/a6ea9fb94bcf342e56a4/?anonymousKey=64c054d1c0a800d103d59eb7a7fc836ba1ffe63f
*/
rule approveTokensIncreasesApprovedL1TokensArray() {
    address[] l1Tokens = [ATOKEN_A, ATOKEN_B];
    uint256[] l2Tokens = [STATIC_ATOKEN_A, STATIC_ATOKEN_B];
    env e;

    uint256 approvedL1TokensLengthBefore = getApprovedL1TokensLength();
    require approvedL1TokensLengthBefore == 0;

    _approveBridgeTokens_Wrapper(l1Tokens,l2Tokens);

    uint256 approvedL1TokensLengthAfter = getApprovedL1TokensLength();

    assert approvedL1TokensLengthAfter == 2;
}

/*
    @Rule 56

    @Description:
        Initialize should increase approved L1 Tokens Array
    @Methods:
        initialize
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/b1146d8e023a742b4d88/?anonymousKey=10d4650170d6f4f0056425458709858a03d13e84
*/
rule initializeIncreasesApprovedL1TokensArray() {
    address[] l1Tokens = [ATOKEN_A, ATOKEN_B];
    uint256[] l2Tokens = [STATIC_ATOKEN_A, STATIC_ATOKEN_B];
    env e;
    address l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;

    uint256 approvedL1TokensLengthBefore = getApprovedL1TokensLength();
    require approvedL1TokensLengthBefore == 0;

    initialize(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);

    uint256 approvedL1TokensLengthAfter = getApprovedL1TokensLength();

    assert approvedL1TokensLengthAfter == 2;
}

/*
    @Rule 57

    @Description:
        Initialize should revert when the length of the l1Tokens array and l2Tokens array are different
    @Methods:
        initialize
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/2ad1bb35dc741564f0b3/?anonymousKey=8cbed14a3c19e0ee076c91ded08cdd37dc1ed894
*/
rule initializeRevertsWithInvalidTokenArrays() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;
    address incentivesControllerAddress;
    address[] l1Tokens = [ATOKEN_A, ATOKEN_B];
    uint256[] l2Tokens = [STATIC_ATOKEN_A];

    // require l1Tokens.length != l2Tokens.length;

    initialize@withrevert(e, l2Bridge, messagingContract, incentivesControllerAddress, l1Tokens, l2Tokens);

    assert lastReverted;
}

/*
    @Rule 58

    @Description:
        Initialize should not revert when valid token arrays are provided.
        Ensures that initializeRevertsWithInvalidTokenArrays is reverting because of the length of the arrays and not 
        the tokens inside. 
    @Methods:
        initialize
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/fc72a19569a6ca2abe43/?anonymousKey=2cbc84518645f55a24b3031bb099144079a02666
*/
rule initializePassesWithValidTokenArrays() {
    env e;
    calldataarg args;
    uint256 l2Bridge;
    address messagingContract;

    address[] l1Tokens = [ATOKEN_A, ATOKEN_B];
    uint256[] l2Tokens = [STATIC_ATOKEN_A, STATIC_ATOKEN_B];

    // these could cause it to revert
    // require e.msg.value == 0;
    // require l2Bridge != 0;
    // require incentivesControllerAddress != 0;

    initialize(e, l2Bridge, messagingContract, incentivesController, l1Tokens, l2Tokens);

    assert getL2Bridge() == l2Bridge && getIncentivesController() == incentivesController && getRewardToken() == REWARD_TOKEN;
}

/*
    @Rule 59

    @Description:
        No change in balance if user has zero balance and is not the recipient
        I filter claimRewards because anyone can claim arbitrary rewards in this implementation, even with zero balance.
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/c118d859fe25b5c88f2d/?anonymousKey=aa773855c08232df5902d3df91e2acd2d32c8192
*/
rule noChangeInBalanceIfZeroAndNotRecipient(method f) 
    filtered{f -> messageSentFilter(f) && f.selector != claimRewardsStatic_L2(address).selector} {
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;
    uint256 amount;
    address user;
    address recipient;
    bool fromToUnderlyingAsset;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(user);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, user);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, user);   
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, user);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, user);

    require underlyingAssetBalanceBefore == 0 && aTokenBalanceBefore == 0 && staticATokenBalanceBefore == 0 && rewardTokenBalanceBefore == 0;
    require recipient != user;

    callFunctionSetParams(f, e, recipient, aToken, underlyingAsset, amount, fromToUnderlyingAsset);

    uint256 underlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, user);
    uint256 aTokenBalanceAfter = tokenBalanceOf(e, aToken, user);   
    uint256 staticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, user);
    uint256 rewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, user);

    assert underlyingAssetBalanceAfter == 0 &&
           aTokenBalanceAfter == 0 &&
           staticATokenBalanceAfter == 0 &&
           rewardTokenBalanceAfter == 0;
}

/*
    @Rule 60

    @Description:
        The l2Address <> staticAToken pair should be correctly registered after calling
        initialize, right after the constructor.
    @Methods:
        initialize
    @Note:
        Expected, but failed
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/94c40fd7c813abce45b4/?anonymousKey=359cfbcadea1c0e43c6e8860af3070c6cb16d09f
*/
rule initializeIntegrityForStaticAToken() {
    env e;
    calldataarg args;
    address aToken;

    uint256 l2AddressBefore = getL2AddressOfAToken(aToken);
    uint256 staticATokenBefore = BRIDGE_L2.address2uint256(BRIDGE_L2.getStaticATokenAddress(aToken));

    require l2AddressBefore == 0;
    require staticATokenBefore == 0;
    
    initialize(e, args);

    uint256 l2AddressAfter = getL2AddressOfAToken(aToken);
    uint256 staticATokenAfter = BRIDGE_L2.address2uint256(BRIDGE_L2.getStaticATokenAddress(aToken));

    assert staticATokenAfter == l2AddressAfter;
}

/*
    @Rule 61

    @Description:
        Only L1 bridge can call receive rewards
    @Methods:
        receiveRewards
    @Note:
        Expected that no one can call receive rewards, but fails
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/4acfad988a3176e3024a/?anonymousKey=f1e5f7a74858bb8a0396c832153bc1b74b694fbc
       
*/
rule onlyBridgeCanCallReceiveRewards() {
    env e;
    uint256 l2sender;
    address recipient;
    uint256 amount;

    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    receiveRewards(e,l2sender, recipient, amount);

    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    
    assert ((e.msg.sender != BRIDGE_L2) && (e.msg.sender != Bridge)) => recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore;
}

/*
    @Rule 62

    @Description:
        Can not deposit twice if the first deposit was a full deposit
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES
    @Link:
        https://prover.certora.com/output/69969/68f3cdb214372a29a99e/?anonymousKey=8e77a3e9387afa42e599100ff33cc7eace9d6b1c
*/
rule noDoubleDepositIfFullyDepositedOnce(){
    address underlyingAsset;
    address staticAToken;
    address aToken;
    address recipient;
    bool fromUnderlyingAsset;
    uint256 amount; 
    uint256 amount2;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(recipient);
    uint16 referralCode;
    env e;
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);

    uint256 underlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    uint256 senderUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);

    require amount == senderUnderlyingAssetBalanceBefore;
    require amount2 > 0;

    deposit(e, aToken, l2Recipient, amount, referralCode, true);

    uint256 underlyingAssetBalanceAfterFirstWithdraw = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfterFirstWithdraw = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    deposit@withrevert(e, aToken, l2Recipient, amount, referralCode, true);

    bool depositReverted = lastReverted;

    uint256 underlyingAssetBalanceAfterSecondWithdraw = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 aTokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, aToken, recipient);
    uint256 staticATokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, staticAToken, recipient);
    uint256 rewardTokenBalanceAfterSecondWithdraw = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    assert depositReverted &&
           underlyingAssetBalanceAfterSecondWithdraw == underlyingAssetBalanceAfterFirstWithdraw && 
           aTokenBalanceAfterSecondWithdraw == aTokenBalanceAfterFirstWithdraw &&
           staticATokenBalanceAfterSecondWithdraw == staticATokenBalanceAfterFirstWithdraw &&
           rewardTokenBalanceAfterSecondWithdraw == rewardTokenBalanceAfterFirstWithdraw;
}

/*
    @Rule 63

    @Description:
        Only L1 bridge can call incentive's controller claimrewards
    @Methods:
        claimRewards
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/7007f1f8725363842361/?anonymousKey=ee17696f84f47024b15e3a72dd916911de26fba8
       
*/
rule onlyL1BridgeCanCallIncentivesControllerClaimRewards() {
    address[] assets;
    uint256 amount;
    address recipient;
    env e;

    require recipient != incentivesController;
    require incentivesController.getL1Bridge(e) == Bridge;

    uint256 incentivesControllerRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, incentivesController);
    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    incentivesController.claimRewards@withrevert(e, assets, amount, recipient);

    bool claimRewardsReverted = lastReverted;

    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);
    uint256 incentivesControllerRewardTokenBalanceAfter= tokenBalanceOf(e, REWARD_TOKEN, incentivesController);

    assert e.msg.sender != Bridge => (claimRewardsReverted &&
           recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore &&
           incentivesControllerRewardTokenBalanceAfter == incentivesControllerRewardTokenBalanceBefore);
}

/*
    @Rule 64

    @Description:
        The following relation between staticAToken, aToken and underlyingAsset must always hold:
        staticAToken <= aToken <= underlyingAsset
    @Note:
        Could be made stronger by removing filter
    @Methods:
        All (except filtered)
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome: 
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/32980627bb158fc453fc/?anonymousKey=4e575844a09c7ffc0f80659d8c04d51c11091de5
*/
rule relationBetweenATokenAndStaticAToken(method f) 
    filtered{f -> messageSentFilter(f) && 
             f.selector != deposit(address, uint256, uint256, uint16, bool).selector &&
             f.selector != initiateWithdraw_L2(address, uint256, address, bool).selector} {
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require staticAToken == STATIC_ATOKEN_A;
    require aToken == ATOKEN_A;
    require underlyingAsset == UNDERLYING_ASSET_A;

    uint256 aTokenTotalSupplyBefore = ATOKEN_A.scaledTotalSupply(e);
    uint256 staticATokenTotalSupplyBefore = STATIC_ATOKEN_A.totalSupply();

    f(e, args);

    uint256 aTokenTotalSupplyAfter = ATOKEN_A.scaledTotalSupply(e);
    uint256 staticATokenTotalSupplyAfter = STATIC_ATOKEN_A.totalSupply();

    assert (aTokenTotalSupplyBefore >= staticATokenTotalSupplyBefore) => (aTokenTotalSupplyAfter >= staticATokenTotalSupplyAfter);
}

/*
    @Rule 65

    @Description:
        The following relation between staticAToken, aToken and underlyingAsset must always hold:
        staticAToken <= aToken <= underlyingAsset
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/7a00a361c363dde9a86a/?anonymousKey=0ae33f3458f21bf14fd7837f4e55bc0de9b802a8
*/
rule relationBetweenUnderlyingAssetAndStaticAToken(method f) 
    filtered{f -> f.selector != deposit(address, uint256, uint256, uint16, bool).selector}{
    env e;
    calldataarg args;
    address underlyingAsset;
    address aToken;
    address staticAToken;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require staticAToken == STATIC_ATOKEN_A;
    require aToken == ATOKEN_A;
    require underlyingAsset == UNDERLYING_ASSET_A;

    uint256 underlyingAssetTotalSupplyBefore = UNDERLYING_ASSET_A.totalSupply();
    uint256 staticATokenTotalSupplyBefore = STATIC_ATOKEN_A.totalSupply();

    f(e, args);

    uint256 underlyingAssetTotalSupplyAfter = UNDERLYING_ASSET_A.totalSupply();
    uint256 staticATokenTotalSupplyAfter = STATIC_ATOKEN_A.totalSupply();

    assert (staticATokenTotalSupplyBefore <= underlyingAssetTotalSupplyBefore) => (staticATokenTotalSupplyAfter <= underlyingAssetTotalSupplyAfter);
}

/*
    @Rule 66

    @Description:
        Deposit increases the AToken contract's underlying balance by the amount
    @Methods:
        deposit
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/a4418646af821aa5775b/?anonymousKey=7652258085e50acea210c891f73aa7e352648d63
        
*/
rule depositUpdatesATokenUnderlyingAssetBalance(){
    env e; 
    uint256 amount;
    address aToken; 
    address underlyingAsset; 
    address staticAToken; 
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUnderlyingAsset; 
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    uint256 aTokenUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, aToken);
    deposit(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);
    uint256 aTokenUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, aToken);

    assert fromUnderlyingAsset => aTokenUnderlyingAssetBalanceAfter == aTokenUnderlyingAssetBalanceBefore + amount;
    assert !fromUnderlyingAsset => aTokenUnderlyingAssetBalanceAfter == aTokenUnderlyingAssetBalanceBefore;
}

/*
    @Rule 67

    @Description:
        An individual account's REWARD_TOKEN balance is not greater than the incentives controller
        REWARD_TOKEN balance, so if an individual bridges rewards from L2 to L1, they can receive all of
        their rewards on L1.
    @Methods:
        All 
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/b9b913144f8a0b5abfe6/?anonymousKey=8c6ae45ef49d26a6e77cdc8d681f72a35dd06b0f
        
*/
rule individualRewardsIsNotGreaterThanIncentivesController(method f) { 
    address user;
    address aToken;
    address underlyingAsset;
    address staticAToken;
    bool fromToUnderlyingAsset;
    uint256 amount;
    env e;
    calldataarg args;

    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    requireRayIndex(underlyingAsset);

    require aToken ==  ATOKEN_A;

    uint256 incentivesControllerBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, incentivesController);
    uint256 userBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, user);

    f(e, args);

    uint256 incentivesControllerBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, incentivesController);
    uint256 userBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, user);

    assert incentivesControllerBalanceBefore >= userBalanceBefore => incentivesControllerBalanceAfter >= incentivesControllerBalanceAfter, 
    "individual account REWARDS TOKEN balance must not be greater than incentives Controller so a user can bridgeRewards from L2 to L1";
}

/*
    @Rule 68 

    @Description:
        L1 rewards index can not decrease
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        FAILS 
    @Link:
        https://prover.certora.com/output/69969/54e1bb006c4c2090a167/?anonymousKey=35347af834a0eb7133721bccb88e97f22382681d
        
*/
rule L1RewardsIndexCanNotDecrease(){
    address L1AToken;
    method f;
    env e;
    calldataarg args;

	uint256 L1RewardsIndexBefore = _getCurrentRewardsIndex_Wrapper(e, L1AToken);
    f(e, args);
    uint256 L1RewardsIndexAfter = _getCurrentRewardsIndex_Wrapper(e, L1AToken);
    assert L1RewardsIndexAfter >= L1RewardsIndexBefore;
}

/*
    @Rule 69

    @Description:
        L2 rewards index can not decrease
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/5e7b911982f4c548886a/?anonymousKey=71deeeddae59453bc84d59559eebe8631a57943b
        
*/
rule L2RewardsIndexCanNotDecrease(method f) 
    filtered{f -> messageSentFilter(f) && f.selector != updateL2State(address).selector}{
    env e;
    calldataarg args;

	uint256 L2RewardsIndexBefore = BRIDGE_L2.l2RewardsIndex();
    f(e, args);
    uint256 L2RewardsIndexAfter = BRIDGE_L2.l2RewardsIndex();
    assert L2RewardsIndexAfter >= L2RewardsIndexBefore;
}

/*
    @Rule 70

    @Description:
        Reward Token address is registerd correctly in the system
    @Methods:
        All
    @Sanity:
        PASSES
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/cb72b38bd503a9469f1d/?anonymousKey=bda9f41511a749b4d5d1808e7e059ea42a2c0c96
        
*/
rule rewardTokenAddressIsRegisteredAfterIntialize(){ 
    env e;
    calldataarg args;

    initialize(e, args);

    address ic = incentivesController.REWARD_TOKEN(e); // incentives Controller 
    address l1 = getRewardToken(); // L1 Bridge
    address l2 = BRIDGE_L2.getRewTokenAddress(e); // L2 Bridge

    assert ic == l1 && l1 == l2;
}

/*
    @Rule 71

    @Description:
        Reward Token address is consistent in the system
    @Methods:
        All
    @Sanity:
        PASSES (except certorafallback_0())
    @Outcome:
        PASSES 
    @Link:
        https://prover.certora.com/output/69969/7d4a5cda3c3594770ab7/?anonymousKey=1eb6bd28b38f299359c7cd501ddad491c69ffd07
        
*/
rule rewardTokenAddressIsConsistent(){ 
    env e;
    calldataarg args;
    method f;

    address ICRewardBefore = incentivesController.REWARD_TOKEN(e); // incentives Controller 
    address L1RewardBefore = getRewardToken(); // L1 Bridge
    address L2RewardBefore = BRIDGE_L2.getRewTokenAddress(e); // L2 Bridge

    f(e, args);

    address ICRewardAfter = incentivesController.REWARD_TOKEN(e); // incentives Controller 
    address L1RewardAfter = getRewardToken(); // L1 Bridge
    address L2RewardAfter = BRIDGE_L2.getRewTokenAddress(e); // L2 Bridge

    assert (ICRewardBefore == L1RewardBefore && L1RewardBefore == L2RewardBefore) => 
           (ICRewardAfter == L1RewardAfter && L1RewardAfter == L2RewardAfter);
}


/*
    @Rule 72

    @Description:
        Expands on integrityOfDeposit rule 

        If depositing from underlying asset, then:
        (1) Sender's underlying asset should decrease by amount deposited
        (2) Sender's aToken balance should remain the same
        (3) Recipient's staticAToken balance should increase by (static) amount deposited 

        If depositing from aToken, then:
        (1) Sender's underlying asset should remain the same
        (2) Sender's aToken balance should decrease by amount deposited (according to bound)
        (3) Recipient's staticAToken balance should increased by (static) amount deposited
    @Methods:
        deposit
    @Sanity:
        TBD
    @Outcome:
        TBD 
    @Link:
        TBD
*/
rule integrityOfDepositExpanded(){
    env e; 
    address recipient;
    uint256 amount;
    address aToken;
    address underlyingAsset; 
    address staticAToken;
    uint256 l2Recipient = BRIDGE_L2.address2uint256(e.msg.sender);
    uint16 referralCode;
    bool fromUnderlyingAsset; 
    uint256 indexL1 = LENDINGPOOL_L1.liquidityIndexByAsset(underlyingAsset);
    
    setupTokens(underlyingAsset, aToken, staticAToken);
    setupUser(e.msg.sender);
    setupUser(recipient);
    requireRayIndex(underlyingAsset);

    // Recipient balances before
    uint256 recipientUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceBefore = tokenBalanceOf(e, aToken, recipient);
    uint256 recipientStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, recipient);
    uint256 recipientRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    // Sender balances before
    uint256 senderUnderlyingAssetBalanceBefore = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceBefore = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 senderStaticATokenBalanceBefore = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 senderRewardTokenBalanceBefore = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender); 

    uint256 staticAmount = deposit(e, aToken, l2Recipient, amount, referralCode, fromUnderlyingAsset);

    // Recipient balances after
    uint256 recipientUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, recipient);
    uint256 recipientATokenBalanceAfter = tokenBalanceOf(e, aToken, recipient);
    uint256 recipientStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, recipient);
    uint256 recipientRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, recipient);

    // Sender balances after
    uint256 senderUnderlyingAssetBalanceAfter = tokenBalanceOf(e, underlyingAsset, e.msg.sender);
    uint256 senderATokenBalanceAfter = tokenBalanceOf(e, aToken, e.msg.sender);
    uint256 senderStaticATokenBalanceAfter = tokenBalanceOf(e, staticAToken, e.msg.sender);
    uint256 senderRewardTokenBalanceAfter = tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender); 
           
    if (fromUnderlyingAsset){
        assert 
        (senderUnderlyingAssetBalanceAfter == senderUnderlyingAssetBalanceBefore - amount) &&
        (senderATokenBalanceAfter == senderATokenBalanceBefore) &&
        (recipientStaticATokenBalanceAfter == recipientStaticATokenBalanceBefore + staticAmount);
    }
    else {
        assert 
        (senderUnderlyingAssetBalanceAfter == senderUnderlyingAssetBalanceBefore) &&
        (senderATokenBalanceAfter - senderATokenBalanceBefore + amount <= (indexL1/RAY() + 1)/2) &&
        (recipientStaticATokenBalanceAfter == recipientStaticATokenBalanceBefore + staticAmount);
    }

    if (e.msg.sender != recipient) {
        assert 
        (senderStaticATokenBalanceAfter == senderStaticATokenBalanceBefore) &&
        (recipientUnderlyingAssetBalanceAfter == recipientUnderlyingAssetBalanceBefore) &&
        (recipientATokenBalanceAfter == recipientATokenBalanceBefore);
    }

    assert senderRewardTokenBalanceAfter == senderRewardTokenBalanceBefore &&
           recipientRewardTokenBalanceAfter == recipientRewardTokenBalanceBefore;
}

////////////////////////////////////////////////////////////////////////////
//                       New Functions                                    //
////////////////////////////////////////////////////////////////////////////
// A general requirement set for the token trio:
// asset - underlying asset
// AToken - correpsonding AToken in the lending pool.
// static - staticAToken to be minted on L2.
function setupStrictTokens(
    address asset, 
    address AToken, 
    address static,
    bool A){
    // Selects a dummy contract implementation for the tokens trio.
    // Note that if it used twice, for two different trios, it is possible
    // they will share the same addresses.
    tokenSelector(asset, AToken, static);
    // Links tokens to each other throught the bridges and pool stored data.
    setLinkage(asset, AToken, static);
    // Links asset and AToken. (Might be redundant after calling 'setLinkage').
    requireInvariant ATokenAssetPair(asset, AToken);
}

// Selects specific instances for underlying asset, AToken and static tokens.
function tokenStrictSelector(
    address asset, 
    address AToken, 
    address static,
    bool A){
    if A {
        require asset == UNDERLYING_ASSET_A;
        require AToken == ATOKEN_A;
        require static == STATIC_ATOKEN_A;
    } else {
        require asset == UNDERLYING_ASSET_B;
        require AToken == ATOKEN_B;
        require static == STATIC_ATOKEN_B;        
    }

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
