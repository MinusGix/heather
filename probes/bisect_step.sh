LOG=${BISECT_LOG:?}
sha=$(git rev-parse --short HEAD)
if [ -n "${RAISE_DEPTH:-}" ]; then sed -i 's/^pub const NATIVE_DEPTH_LIMIT: u32 = 1024;/pub const NATIVE_DEPTH_LIMIT: u32 = 16384;/' crates/kernel/src/reduce.rs 2>/dev/null; fi
out=$(timeout 1700 furnace run -- bash probes/bisect_remote.sh 2>&1)
git checkout -- crates/kernel/src/reduce.rs 2>/dev/null
echo "$out" | grep -E "test result|rejected|remote (start|end)|NATIVE_DEPTH|^error" | sed "s/^/[$sha] /" >> "$LOG"
if echo "$out" | grep -q "test result: ok"; then echo "[$sha] VERDICT good" >> "$LOG"; exit 0
elif echo "$out" | grep -q "test result: FAILED"; then echo "[$sha] VERDICT bad" >> "$LOG"; exit 1
else echo "[$sha] VERDICT skip" >> "$LOG"; exit 125; fi
