certoraRun certora/harness/BridgeL2Harness.sol \
    --verify BridgeL2Harness:certora/specs/complexity.spec \
    --optimistic_loop \
    --send_only \
    --rule "sanity" \
    --cloud  \
    --msg "Bridge complexity check"
    # --solc solc8.10 \

