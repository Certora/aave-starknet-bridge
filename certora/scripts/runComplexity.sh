certoraRun certora/harness/BridgeL2Harness.sol \
    --verify BridgeL2Harness:certora/specs/bridge.spec \
    --solc solc \
    --optimistic_loop \
    --send_only \
    --rule "sanity" \
    --cloud  \
    --msg "Bridge complexity check"
