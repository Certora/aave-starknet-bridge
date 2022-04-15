%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.uint256 import (
    Uint256, uint256_add, uint256_sub, uint256_mul, uint256_unsigned_div_rem)
from starkware.starknet.common.syscalls import get_caller_address
from starkware.cairo.common.math_cmp import is_le

from rewaave.math.wad_ray_math import ray_mul_no_rounding, ray_to_wad_no_rounding
from openzeppelin.token.erc20.library import ERC20_totalSupply, ERC20_balanceOf, ERC20_mint
from openzeppelin.access.ownable import Ownable_initializer, Ownable_only_owner, Ownable_get_owner

@storage_var
func acc_rewards_per_token() -> (res : Uint256):
end

# user => accRewardsPerToken at last interaction (in RAYs)
@storage_var
func user_snapshot_rewards_per_token(user : felt) -> (acc_rewards_per_token : Uint256):
end
# user => unclaimed_rewards (in RAYs)
@storage_var
func unclaimed_rewards(user : felt) -> (unclaimed : Uint256):
end

func update_user_snapshot_rewards_per_token{
        syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(user : felt):
    let (acc_rewards_per_token_) = acc_rewards_per_token.read()
    user_snapshot_rewards_per_token.write(user, acc_rewards_per_token_)
    return ()
end

func update_user{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(user : felt):
    alloc_locals
    let (balance) = ERC20_balanceOf(user)
    if balance.high + balance.low == 0:
        update_user_snapshot_rewards_per_token(user)
    else:
        let (pending) = get_pending_rewards(user)
        let (unclaimed) = unclaimed_rewards.read(user)
        let (unclaimed, overflow) = uint256_add(unclaimed, pending)
        assert overflow = 0
        unclaimed_rewards.write(user, unclaimed)
        update_user_snapshot_rewards_per_token(user)
    end
    return ()
end

func claimable_before_token_transfer{
        syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(from_ : felt, to : felt):
    alloc_locals
    if from_ == 0:
        # do nothing
        tempvar syscall_ptr = syscall_ptr
        tempvar pedersen_ptr = pedersen_ptr
        tempvar range_check_ptr = range_check_ptr
    else:
        update_user(from_)
        tempvar syscall_ptr = syscall_ptr
        tempvar pedersen_ptr = pedersen_ptr
        tempvar range_check_ptr = range_check_ptr
    end
    if to == 0:
        # do nothing
    else:
        update_user(to)
    end
    return ()
end

func get_pending_rewards{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(
        user : felt) -> (pending_rewards : Uint256):
    alloc_locals
    let (balance) = ERC20_balanceOf(user)
    let (supply) = ERC20_totalSupply()
    let (accRewardsPerToken_) = acc_rewards_per_token.read()
    let (user_snapshot_rewards_per_token_) = user_snapshot_rewards_per_token.read(user)
    let (accrued_since_last_interaction) = uint256_sub(
        accRewardsPerToken_, user_snapshot_rewards_per_token_)
    let (pending_rewards) = ray_mul_no_rounding(accrued_since_last_interaction, balance)
    return (pending_rewards)
end

func get_claimable_rewards{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(
        user : felt) -> (claimable_rewards : Uint256):
    alloc_locals
    let (unclaimed_rewards_) = unclaimed_rewards.read(user)
    let (pending) = get_pending_rewards(user)
    let (claimable_rewards, overflow) = uint256_add(unclaimed_rewards_, pending)
    assert overflow = 0
    let (claimable_rewards) = ray_to_wad_no_rounding(claimable_rewards)
    return (claimable_rewards)
end

func claimable_claim_rewards{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(
        user : felt, recipient : felt) -> (claimed : Uint256):
    let (claimed) = get_claimable_rewards(user)
    let (rewardsController_) = Ownable_get_owner()

    unclaimed_rewards.write(user, Uint256(0, 0))

    # TODO implement claiming

    if claimed.high + claimed.low == 0:
        return (Uint256(0, 0))
    else:
        update_user_snapshot_rewards_per_token(user)
        return (claimed)
    end
end

func claimable_push_acc_rewards_per_token{
        syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(
        acc_rewards_per_token_ : Uint256):
    alloc_locals
    acc_rewards_per_token.write(acc_rewards_per_token_)
    return ()
end

func claimable_get_acc_rewards_per_token{
        syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}() -> (res : Uint256):
    return acc_rewards_per_token.read()
end