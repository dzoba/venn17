# Baseline result and first Lean19 attempt

The source-identical17 baseline passed all3,468 build jobs at03:33:42 UTC on September21,2026. Controller wall time was3,093.86s; OS command time3,087.36s. Sampled aggregate RSS peaked at4,240,850,944bytes (3.95GiB); OS maximum process RSS was3,439,067,136bytes. The controlled build used one Lean module worker. See `../logs/baseline17/baseline-summary.json` for measurement limits.

The topology assumption audit passed in7.22s and matched upstream output byte-for-byte. The final theorem depends on20 explicit native_decide axioms and3 standard logical axioms. This is the relative assumption set required for19; it is not a claim of kernel-reduced finite computations.

The baseline log reports2,348.5s summed compilation time for309 unchanged vendor modules and677.08s for147 diagram/core targets. Reusing hash-verified generic artifacts should save roughly39min of repeated compilation. The19 input has about4x the17 finite cells. Source inventory covers879 source lines in79 files, with27 native_decide proof invocations. Input19 SHA256 is ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d.

Working forecast for19 after generic reuse:30–90minutes and6–16GiB peak aggregate memory. These are estimates, not proven resource bounds. Nonlinear finite-check behavior or proof-port errors may invalidate them. The actual controller enforces32GiB aggregate RSS,10GiB owned output and8GiB filesystem reserve. The conservative whole-attempt deadline is14:42:08 UTC (12h after the17 baseline began). Stop and report resource failure instead of trying repeated variants.

This estimate was posted to Claude before any full19 build as board message1091. The prepared source and generated certificates are still awaiting Lean19 validation.
