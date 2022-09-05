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
    _getCurrentRewardsIndex_Wrapper(address) returns (uint256) 
    initiateWithdraw_L2(address, uint256, address, bool)
    bridgeRewards_L2(address, uint256)
    getUnderlyingAssetOfAToken(address) returns (address) envfree
    underlyingtoAToken(address) returns (address) => DISPATCHER(true)

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

/*
    @Link: https://prover.certora.com/output/93750/92fe288171e2f35af41a?anonymousKey=a069a02a29d863cf565d8cee7f8a5956e86a0c27
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

/////////////////////////
    // My rules
////////////////////////


// 1. // correctly update static balance
rule checkStaticATokenBalance(address recipient){
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

    uint256 _staticBalance= getStaticATokenBalance(e,aToken,e.msg.sender);
    uint256 _recepientAtokenBalance = tokenBalanceOf(e,aToken , recipient);
    uint256 _recepientAssetBalance = tokenBalanceOf(e,underlying , recipient);

    initiateWithdraw_L2(e, aToken, staticAmount, recipient, toUnderlyingAsset);
  
    uint256 staticBalance_= getStaticATokenBalance(e,aToken,e.msg.sender);
    uint256 recepientAtokenBalance_ = tokenBalanceOf(e,aToken , recipient);
    uint256 recepientAssetBalance_ = tokenBalanceOf(e,underlying , recipient);

    assert _staticBalance==staticBalance_+staticAmount;
    assert toUnderlyingAsset => (recepientAssetBalance_ == _recepientAssetBalance + _staticToDynamicAmount_Wrapper(staticAmount,aToken,LENDINGPOOL_L1));
    assert !toUnderlyingAsset => (recepientAtokenBalance_ == _recepientAtokenBalance + _staticToDynamicAmount_Wrapper(staticAmount,aToken,LENDINGPOOL_L1));
}


// 2. Cannot initialize agiain if already initialized
// NOTE :- Make initializing variable public to run this rule
rule cannotReInitialize{
    env e; calldataarg args;
    address underlying;
    address static;
    address aToken;
    uint256 l2RewardsIndex = BRIDGE_L2.l2RewardsIndex();
    
    setupTokens(underlying, aToken, static);
    setupUser(e.msg.sender);

    require(initializing(e)==false);

    initialize(e,args);

    initialize@withrevert(e,args);

    assert lastReverted==true,"initializing second time should revert";
}

// 3. Cannot change _messagingContract , _l2Bridge , _rewardToken , _incentivesController if set once
rule cannotChangeOnceSet(method f,env e,calldataarg args) filtered{f -> messageSentFilter(f) && excludeInitialize(f)}{

    address _messagingContract=_messagingContract(e);
    uint256 _l2Bridge=_l2Bridge(e);
    address _rewardToken=_rewardToken();
    address _incentivesController = _incentivesController(e);

    f(e,args);

    address messagingContract_=_messagingContract(e);
    uint256 l2Bridge_=_l2Bridge(e);
    address rewardToken_=_rewardToken();
    address incentivesController_ = _incentivesController(e);

    assert _messagingContract == messagingContract_;
    assert _l2Bridge==l2Bridge_;
    assert _rewardToken == rewardToken_;
    assert _incentivesController == incentivesController_;
}


// 4. Only owner can decrease his underlying , aToken , static balance
rule onlyUserCanDecreaseHisBalance(method f) filtered{f -> messageSentFilter(f)}{
    env e;calldataarg args;    
    address asset;
    address AToken;
    address static;
    address user;
    bool fromToUA;
    
    setupTokens(asset, AToken, static);
    setupUser(e.msg.sender);
    requireValidUser(user);

    uint256 _balanceU1=tokenBalanceOf(e, asset, user);
    uint256 _balanceA1=tokenBalanceOf(e,AToken,user);
    uint256 _balanceS1=tokenBalanceOf(e,static,user);

    f(e,args);

    uint256 balanceU1_=tokenBalanceOf(e, asset, user);
    uint256 balanceA1_=tokenBalanceOf(e,AToken,user);
    uint256 balanceS1_=tokenBalanceOf(e,static,user);

    bool balanceDecreased= (_balanceU1 > balanceU1_ || _balanceA1 > balanceA1_ || _balanceS1 > balanceS1_);
    // assert balanceU1_ < _balanceU1 => e.msg.sender==user;
    // assert balanceA1_ < _balanceA1 => e.msg.sender==user;
    // assert balanceS1_ < _balanceS1 => e.msg.sender==user;
    assert balanceDecreased==true => e.msg.sender==user;
}


ghost mathint totalApprovedTokens{
    init_state axiom totalApprovedTokens==0;
}

hook Sstore _aTokenData[KEY address user].l2TokenAddress uint256 newL2Address (uint256 oldL2Address) STORAGE{
    totalApprovedTokens=totalApprovedTokens+1;
}
// 5. check approvedTokenArray length
invariant correctnessOfApprovedL1TokensArray(env e)
    getApprovedTokensArrayLength(e)==totalApprovedTokens
     { preserved initialize(uint256 l2Bridge,address messagingContract,address _incentivesController,address[] l1Tokens,uint256[] l2Tokens) with (env e2){
        require(getApprovedTokensArrayLength(e) + l1Tokens.length <= max_uint);
        }
     }



function nonZeroL2Address(address a,address b) returns bool{
    env e;
    bool res= (getL2TokenAddress(e,a)!=0 && getL2TokenAddress(e,b)!=0 ) ? true:false;
    return res;
}

// 6. @Note: - this rule highlights a possibility/Bug of different l1Token having same corresponding l2Address.
// THIS RULE FAILS.
rule distinctL1TokenMustNotHaveSameL2Token{
    address L1TokenA;address L1TokenB;
    method f;env e;calldataarg args;
    require(L1TokenA!=0 && L1TokenB!=0 && L1TokenA!=L1TokenB);
    require(getL2TokenAddress(e,L1TokenA)==0 && getL2TokenAddress(e,L1TokenB)==0);

    initialize(e,args);

    assert nonZeroL2Address(L1TokenA,L1TokenB) == true => getL2TokenAddress(e,L1TokenA) != getL2TokenAddress(e,L1TokenB);
    
}

// 7. Reward balance can only change in initiateWithdraw_L2 , bridgeRewards_L2 and claimRewards_L2
rule rewardBalanceChangeRestriction(method f,env e,calldataarg args) filtered{f -> messageSentFilter(f)} {
    requireValidUser(e.msg.sender);
    address user;address asset;address Atoken;address static;address receiver;uint256 amount;bool fromUnderlyingAsset;
    setupTokens(asset, Atoken, static);
    uint256 _rewardBalance=getRewardBalance(e,user);
    callFunctionSetParams(f,e,receiver,Atoken,asset,amount,fromUnderlyingAsset);
    uint256 rewardBalance_=getRewardBalance(e,user);
    assert _rewardBalance!=rewardBalance_ => f.selector == initiateWithdraw_L2(address,uint256,address,bool).selector || f.selector == bridgeRewards_L2(address,uint256).selector || f.selector == claimRewardsStatic_L2(address).selector;
}

// 8. Reward balance of a user cannot decrease i.e its only increasing in nature.
rule rewardBalanceIsOnlyIncreasing(method f,env e,calldataarg args)filtered{f -> messageSentFilter(f) && f.selector != bridgeRewards_L2(address, uint256).selector}{
    address user;address asset;address Atoken;address static;address receiver;uint256 amount;bool fromUnderlyingAsset;
    setupTokens(asset, Atoken, static);
    requireValidUser(user);
    uint256 _rewardBalance = getRewardBalance(e,user);
    callFunctionSetParams(f,e,receiver,Atoken,asset,amount,fromUnderlyingAsset);
    uint256 rewardBalance_ = getRewardBalance(e,user);

    assert rewardBalance_ >= _rewardBalance,"rewardBalance cannot be decreased";
}

//9 - Cannot claim rewards again with claimRewards_l2 if already claimed
rule cannotClaimRewardsIfAlreadyClaimed(env e) {
    address Atoken; address asset;address static; 

    setupTokens(asset, Atoken, static);
    requireValidUser(e.msg.sender);

    claimRewardsStatic_L2(e, static);

    claimRewardsStatic_L2@withrevert(e, static); // this will revert coz in dummyStaticAToken implementation unclaimedRewards[recepient] becomes 0 after first call.

    assert lastReverted==true;
}

// 10. Zero address must have zero aToken balance.

invariant zeroAddressATokenCheck(env e)
    tokenBalanceOf(e,ATOKEN_A,0)==0

// 11. zero address must have zero static balance

invariant zeroAddressStaticBalanceCheck(env e)
    tokenBalanceOf(e,STATIC_ATOKEN_A,0)==0

//12 - Cannot withdraw in L2 if static balance is zero
rule zeroStaticBalanceCannotWithdraw(env e) {
    address recipient;address Atoken; address asset;  address static; uint256 amount; 
    bool fromtoUnderlyingAsset; 

    setupTokens(asset, Atoken, static);
    requireValidUser(e.msg.sender);
    require tokenBalanceOf(e, static, e.msg.sender) == 0;
    require (recipient != Atoken && recipient != currentContract);

    initiateWithdraw_L2@withrevert(e, Atoken, amount, recipient, fromtoUnderlyingAsset);

    assert lastReverted==true;
}

//13. If static balance of a user decreases then his aToken or underlying asset balance must increase and vice versa.
rule ifL1BalanceDecreaseL2BalanceIncreaseAndViceVersa(method f,env e,calldataarg args)filtered{f -> messageSentFilter(f) }{
    address asset;address Atoken;address static;address receiver;uint256 amount;bool fromToUnderlyingAsset;
    setupTokens(asset, Atoken, static);
    requireValidUser(e.msg.sender);
    require(receiver != ATOKEN_A && receiver != ATOKEN_B);  //receiver cannot be the pool itself

    uint256 _assetBalanceReceiver=tokenBalanceOf(e,asset,receiver);
    uint256 _ATokenBalanceReceiver=tokenBalanceOf(e,Atoken,receiver);
    uint256 _assetBalanceCaller=tokenBalanceOf(e,asset,e.msg.sender);
    uint256 _ATokenBalanceCaller=tokenBalanceOf(e,Atoken,e.msg.sender);
    uint256 _staticBalanceReceiver=tokenBalanceOf(e,static,receiver);
    uint256 _staticBalanceCaller=tokenBalanceOf(e,static,e.msg.sender);


    callFunctionSetParams(f,e,receiver,Atoken,asset,amount,fromToUnderlyingAsset);

    uint256 assetBalanceReceiver_=tokenBalanceOf(e,asset,receiver);
    uint256 ATokenBalanceReceiver_=tokenBalanceOf(e,Atoken,receiver);
    uint256 assetBalanceCaller_=tokenBalanceOf(e,asset,e.msg.sender);
    uint256 ATokenBalanceCaller_=tokenBalanceOf(e,Atoken,e.msg.sender);
    uint256 staticBalanceReceiver_=tokenBalanceOf(e,static,receiver);
    uint256 staticBalanceCaller_=tokenBalanceOf(e,static,e.msg.sender);

    assert (_assetBalanceCaller > assetBalanceCaller_ || _ATokenBalanceCaller >  ATokenBalanceCaller_) => _staticBalanceReceiver < staticBalanceReceiver_ ,"If balance of caller on L1 side decreases then balance of receiver on L2 side must increase";

    assert (_staticBalanceCaller > staticBalanceCaller_) => (_assetBalanceReceiver < assetBalanceReceiver_ || _ATokenBalanceReceiver <  ATokenBalanceReceiver_) ,"If balance of caller on L2 side decreases then balance of receiver on L1 side must increase";
}


// 14. A third use balance must not change if deposit is called by another different address with recepient != user.
rule checkEffectOnThirdParty_Deposit(method f,env e) filtered{f -> messageSentFilter(f) } {
    address asset;address Atoken;address static;address user;
    address receiver;uint256 amount;bool fromToUnderlyingAsset;uint16 referralCode;
    setupTokens(asset, Atoken, static);

    requireValidUser(receiver);
    requireValidUser(e.msg.sender);
    requireValidUser(user);
    require(user!=e.msg.sender && user!= receiver);

    uint256 _assetBalanceUser_original=tokenBalanceOf(e,asset,user);
    uint256 _ATokenBalanceUser_original=tokenBalanceOf(e,Atoken,user);
    uint256 _staticBalanceUser_original=tokenBalanceOf(e,static,user);
    uint256 _rewardTokenBalanceUser_original=getRewardBalance(e,user);

    uint256 receiver_uint=BRIDGE_L2.address2uint256(receiver);
    storage initialstate = lastStorage;

    deposit(e,Atoken,receiver_uint,amount,referralCode,fromToUnderlyingAsset);

    uint256 assetBalanceUser_Deposit=tokenBalanceOf(e,asset,user);
    uint256 ATokenBalanceUser_Deposit=tokenBalanceOf(e,Atoken,user);
    uint256 staticBalanceUser_Deposit=tokenBalanceOf(e,static,user);
    uint256 rewardTokenBalanceUser_Deposit=getRewardBalance(e,user);

    assert _assetBalanceUser_original == assetBalanceUser_Deposit;
    assert _ATokenBalanceUser_original == ATokenBalanceUser_Deposit;
    assert _staticBalanceUser_original == staticBalanceUser_Deposit;
    assert _rewardTokenBalanceUser_original == rewardTokenBalanceUser_Deposit;
}

// 15.A third use balance must not change if withdraw is called by another different address with recepient != user.
rule checkEffectOnThirdParty_Withdraw(method f,env e)filtered{f -> messageSentFilter(f) }{
    address asset;address Atoken;address static;address user;
    address receiver;uint256 amount;bool fromToUnderlyingAsset;uint16 referralCode;
    setupTokens(asset, Atoken, static);

    requireValidUser(e.msg.sender);
    requireValidUser(user);
    require(user!=e.msg.sender && user!= receiver);

    uint256 _assetBalanceUser_original=tokenBalanceOf(e,asset,user);
    uint256 _ATokenBalanceUser_original=tokenBalanceOf(e,Atoken,user);
    uint256 _staticBalanceUser_original=tokenBalanceOf(e,static,user);
    uint256 _rewardTokenBalanceUser_original=getRewardBalance(e,user);

    uint256 receiver_uint=BRIDGE_L2.address2uint256(receiver);

    initiateWithdraw_L2(e,Atoken,amount,receiver,fromToUnderlyingAsset);

    uint256 assetBalanceUser_Withdraw=tokenBalanceOf(e,asset,user);
    uint256 ATokenBalanceUser_Withdraw=tokenBalanceOf(e,Atoken,user);
    uint256 staticBalanceUser_Withdraw=tokenBalanceOf(e,static,user);
    uint256 rewardTokenBalanceUser_Withdraw=getRewardBalance(e,user);

    assert _assetBalanceUser_original == assetBalanceUser_Withdraw;
    assert _ATokenBalanceUser_original == ATokenBalanceUser_Withdraw;
    assert _staticBalanceUser_original == staticBalanceUser_Withdraw;
    assert _rewardTokenBalanceUser_original == rewardTokenBalanceUser_Withdraw;
}

// 16.A third use balance must not change if claimRewards is called by another different address.
rule checkEffectOnThirdParty_ClaimRewards(method f,env e)filtered{f -> messageSentFilter(f) }{
     address asset;address Atoken;address static;address user;
    address receiver;uint256 amount;bool fromToUnderlyingAsset;uint16 referralCode;
    setupTokens(asset, Atoken, static);

    // requireValidUser(receiver);
    requireValidUser(e.msg.sender);
    requireValidUser(user);
    require(user!=e.msg.sender && user!= receiver);
    uint256 receiver_uint=BRIDGE_L2.address2uint256(receiver);

    uint256 _assetBalanceUser_original=tokenBalanceOf(e,asset,user);
    uint256 _ATokenBalanceUser_original=tokenBalanceOf(e,Atoken,user);
    uint256 _staticBalanceUser_original=tokenBalanceOf(e,static,user);
    uint256 _rewardTokenBalanceUser_original=getRewardBalance(e,user);
    
    claimRewardsStatic_L2(e,static);

    uint256 assetBalanceUser_ClaimRewards=tokenBalanceOf(e,asset,user);
    uint256 ATokenBalanceUser_ClaimRewards=tokenBalanceOf(e,Atoken,user);
    uint256 staticBalanceUser_ClaimRewards=tokenBalanceOf(e,static,user);
    uint256 rewardTokenBalanceUser_ClaimRewards=getRewardBalance(e,user);

    assert _assetBalanceUser_original == assetBalanceUser_ClaimRewards;
    assert _ATokenBalanceUser_original == ATokenBalanceUser_ClaimRewards;
    assert _staticBalanceUser_original == staticBalanceUser_ClaimRewards;
    assert _rewardTokenBalanceUser_original == rewardTokenBalanceUser_ClaimRewards;

}
// 17. A third use balance must not change if bridgeRewards is called by another different address with recepient != user.
rule checkEffectOnThirdParty_BridgeRewards(method f,env e)filtered{f -> messageSentFilter(f) }{
     address asset;address Atoken;address static;address user;
    address receiver;uint256 amount;bool fromToUnderlyingAsset;uint16 referralCode;
    setupTokens(asset, Atoken, static);

    // requireValidUser(receiver);
    requireValidUser(e.msg.sender);
    requireValidUser(user);
    require(user!=e.msg.sender && user!= receiver);
    uint256 receiver_uint=BRIDGE_L2.address2uint256(receiver);

    uint256 _assetBalanceUser_original=tokenBalanceOf(e,asset,user);
    uint256 _ATokenBalanceUser_original=tokenBalanceOf(e,Atoken,user);
    uint256 _staticBalanceUser_original=tokenBalanceOf(e,static,user);
    uint256 _rewardTokenBalanceUser_original=getRewardBalance(e,user);

    bridgeRewards_L2(e,receiver,amount);

    uint256 assetBalanceUser_BridgeRewards=tokenBalanceOf(e,asset,user);
    uint256 ATokenBalanceUser_BridgeRewards=tokenBalanceOf(e,Atoken,user);
    uint256 staticBalanceUser_BridgeRewards=tokenBalanceOf(e,static,user);
    uint256 rewardTokenBalanceUser_BridgeRewards=getRewardBalance(e,user);

    assert _assetBalanceUser_original == assetBalanceUser_BridgeRewards;
    assert _ATokenBalanceUser_original == ATokenBalanceUser_BridgeRewards;
    assert _staticBalanceUser_original == staticBalanceUser_BridgeRewards;
    assert _rewardTokenBalanceUser_original == rewardTokenBalanceUser_BridgeRewards;
}


// 18. Sum of rewards balances of caller and reciver must not change before and after bridgeRewards.
rule bridgeRewardsDoesNotChangeRewardBalanceSum(method f,env e)filtered{f -> messageSentFilter(f) }{
          address asset;address Atoken;address static;
    address receiver;uint256 amount;bool fromToUnderlyingAsset;uint16 referralCode;
    setupTokens(asset, Atoken, static);

    requireValidUser(e.msg.sender);

    uint256 _callerRewardBalance = getRewardBalance(e,e.msg.sender);
    uint256 _receiverRewardBalance = getRewardBalance(e,receiver);

    bridgeRewards_L2(e,receiver,amount);

    uint256 callerRewardBalance_ = getRewardBalance(e,e.msg.sender);
    uint256 receiverRewardBalance_ = getRewardBalance(e,receiver);

    assert _callerRewardBalance + _receiverRewardBalance == callerRewardBalance_ + receiverRewardBalance_;
   
}

// 19. As more amount of static token withdraws , more the aToken balance or underlying balance of recepient becomes.
rule monotonicIncreaseInWithdraw{
    address asset;address Atoken;address static;
    address receiver;uint256 amount1;uint256 amount2;bool fromToUnderlyingAsset;uint16 referralCode;env e;
    setupTokens(asset, Atoken, static);

    requireValidUser(e.msg.sender);
    require(receiver != currentContract && receiver != Atoken);

    storage initialState = lastStorage;

    initiateWithdraw_L2(e,Atoken,amount1,receiver,fromToUnderlyingAsset);

    uint256 aTokenBalance1_=  tokenBalanceOf(e,Atoken,receiver);
    uint256 underlyingBalance1_=  tokenBalanceOf(e,asset,receiver);

    // uint256 changeInBalance1 = aTokenBalance1_- _aTokenBalance;

    initiateWithdraw_L2(e,Atoken,amount2,receiver,fromToUnderlyingAsset) at initialState;

    uint256 aTokenBalance2_=  tokenBalanceOf(e,Atoken,receiver);
    uint256 underlyingBalance2_=  tokenBalanceOf(e,asset,receiver);

    // uint256 changeInBalance2 = aTokenBalance2_- _aTokenBalance;

    assert amount2 > amount1 && !fromToUnderlyingAsset => aTokenBalance2_ > aTokenBalance1_;
    assert amount2 > amount1 && fromToUnderlyingAsset => underlyingBalance2_ > underlyingBalance1_;
}

//20 - user with zero reward balance cannot bridge rewards using bridgeRewards_L2
rule zeroRewardBalanceCannotBridgeToL1(env e) {
    address receiver;address Atoken; address asset;  address static;uint256 amount;bool toUnderlyingAsset; 

    setupTokens(asset, Atoken, static);
    requireValidUser(e.msg.sender);
    require tokenBalanceOf(e, REWARD_TOKEN, e.msg.sender) == 0;

    bridgeRewards_L2@withrevert(e, receiver, amount);

    assert lastReverted==true;
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
