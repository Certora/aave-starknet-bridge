certoraRun certora/harness/BridgeL2Harness.sol \
    --verify BridgeL2Harness:certora/specs/complexity.spec \
    --solc solc8.10 \
    --optimistic_loop \
    --send_only \
    --rule "sanity" \
    --staging  \
    --msg "Bridge complexity check"
