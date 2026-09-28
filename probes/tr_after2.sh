set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^error' -A 12 | head -60
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_DECLINE=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -E '^#(projdecline|projenter)' | sort | uniq -c | sort -rn )
echo "=== LISTING DONE ==="
bash probes/probe_run.sh probes/t_pc1.hthr probes/t_pc2.hthr probes/t_pc3.hthr probes/t_pcev3.hthr probes/t_pc4.hthr
echo "=== TR_AFTER2 DONE ==="
