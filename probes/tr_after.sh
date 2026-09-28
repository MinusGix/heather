set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^(error|warning: unused)" -A 8 | head -60
echo "=== BUILT ==="
bash probes/probe_run.sh probes/t_pc1.hthr probes/t_pc2.hthr probes/t_pc3.hthr probes/t_pcev3.hthr probes/t_pc4.hthr
echo "=== TR_AFTER DONE ==="
