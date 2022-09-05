certoraRun certora/harness/BridgeL2Harness.sol \
    --verify BridgeL2Harness:certora/specs/complexity.spec \
    --optimistic_loop \
    --send_only \
    --rule "sanity" \
    --msg "Bridge complexity check"
