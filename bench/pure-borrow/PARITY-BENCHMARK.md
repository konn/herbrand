# Final Pure Borrow paired benchmark

Status: complete exact-commit campaign against the current `main` content.
The raw outputs, provenance, and completed manifest are intentionally kept in
ignored `workspace/pure-borrow-benchmark`; their hashes below make the
measurement reproducible without committing temporary benchmark output.

## Identity and protocol

- Current-main baseline:
  commit `57e6917cf61f89a6e152aa3793cc749894ae9a4d`,
  tree `45615b9977e5e1ee4c51cee05590f93cf94da17f`.
- Candidate:
  commit `0a5efdd3311c19bf64666b44a47f7fbf6578ca5f`,
  tree `f9fee5f8463e5a4386ad73909c22d3bda20d0862`
  (`konn/pure-borrow`).
- Pure Borrow:
  `SoftwareFoundationGroupAtKyotoU/pure-borrow@79a0d1878ccbce8895039c253cc9e462a788d3f3`.
- Toolchain: GHC 9.12.4, Cabal 3.14.2.0, optimized `-O2` executables.
- Concurrency: single-threaded; neither executable uses `-threaded`, and no
  RTS `-N` option was used.
- Design: 21 alternating fresh-process pairs after warmup for seven SAT/UNSAT
  inputs under copying and nonmoving GC.
- Estimator: candidate/baseline paired elapsed ratio within each case/GC
  stratum; aggregate geometric mean with 100,000 deterministic stratified
  bootstrap resamples, seed `20260726`.
- Acceptance: per-case median/MAD gates plus aggregate 95% upper confidence
  bound at most `1.02`.

Executable SHA-256 fingerprints:

```text
efb69e34d170a5e94e873917efdbfcd63faa76775d70be57f7efe56f2138e34c  current-main
2e391bedfaabb4b20f8f88de14a5a965a197e1146399f6ba8fb3917e43fc4b57  pure-borrow
```

The runner generated the three synthetic inputs in ignored
`workspace/tuning-corpus`, rejected content drift, and recorded all fixture
hashes. Both source worktrees were clean. The production binaries were built
with explicit Cabal `--enable-optimization=2`; neither checkout's local Cabal
overlay participated.

Artifact SHA-256 fingerprints:

```text
2ce2957fe6ea3ed1401d0fcec0598719eebce819c64593c07d57e78d882e736a  run-paired.mjs
180e96a1f001f90d83fe1a5d64d995ca2edbb46d91af95ced2f331abc5b08ecf  analyze-paired.mjs
545fe8ac5504292d9e07ad6591fa470940298ad81a6fcb38412a758ae82b7743  provenance.json
35ee5d2bb82379e143b7f2c159fa4c9423a982e34942c69db0c4c5f8ca1936bc  manifest.json
0cb9f07ab54a3ef485cb2069c0414ac221f396456db1dce36921de03c9a6dbcd  baseline.csv
946b6800cfd8697f69ccf3f990361a1a4d919d2b65131f86610f695534aa82b9  candidate.csv
07d521ae46aff266df50d69055089ad1d91ae84e7fffc6f407a4c79d7241c9e9  report.json
ae0d112f967270c777ad5c331c25b56e3b204016fe69d8155cfe53e9a4a863bf  control-manifest.json
339b6c5fe9eef3b26759f88b2e9c34ed4117f3ccd669cb0af0b5a8093e684a45  control-baseline.csv
ab955bb49c8ce0aa9e4b1352030768885a3a2c62b29645908940242fa618977a  control-candidate.csv
5ef12aa4c78652cb0c2f82639f51aa63353f9bcd69022487d53e87f027b71826  control-report.json
c9303484e5ee952957941bb4655ac8d06e28e71fefa0abd51a200b1a85cc1dbb  all-binary-2-unsat.cnf
3b54f9f27d7139064a6b585ae40e1e650d634324f0ec3d476f0b268b527cb5f7  implication-chain-12-unsat.cnf
ea1c7697c4b2be671c51d340e207a71d6de0ccb7e2e5009c23bb8020d2075950  php-7-6-unsat.cnf
```

## Outcome

- Results matched: true
- Per-case elapsed gates: 10/14
- Aggregate UCB gates: 0/3

| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |
| --- | ---: | ---: | ---: | ---: | :---: |
| nonmoving | 147 | 1.1344 | 1.1670 | 1.0200 | no |
| copying | 147 | 1.1840 | 1.2157 | 1.0200 | no |
| all | 294 | 1.1589 | 1.1818 | 1.0200 | no |

| Case | GC | Allocation ratio | Elapsed ratio | Baseline median (s) | Candidate median (s) | Gate |
| --- | --- | ---: | ---: | ---: | ---: | :---: |
| data/satlib/uf20-91/uf20-01.cnf | nonmoving | 0.7793 | 0.9547 | 0.014 | 0.014 | yes |
| data/satlib/uf100-430/uf100-01.cnf | nonmoving | 0.2943 | 0.6823 | 0.027 | 0.015 | yes |
| data/satlib/flat200-479/flat200-1.cnf | nonmoving | 0.4361 | 1.2137 | 0.042 | 0.053 | no |
| data/satlib/Bejing/3blocks.cnf | nonmoving | 0.6099 | 6.8186 | 0.069 | 0.469 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | nonmoving | 0.9364 | 1.1401 | 0.014 | 0.015 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | nonmoving | 0.8789 | 0.9832 | 0.014 | 0.014 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | nonmoving | 0.1796 | 0.4000 | 0.067 | 0.026 | yes |
| data/satlib/uf20-91/uf20-01.cnf | copying | 0.7793 | 0.9389 | 0.014 | 0.014 | yes |
| data/satlib/uf100-430/uf100-01.cnf | copying | 0.2943 | 0.6070 | 0.027 | 0.015 | yes |
| data/satlib/flat200-479/flat200-1.cnf | copying | 0.4361 | 1.2781 | 0.040 | 0.053 | no |
| data/satlib/Bejing/3blocks.cnf | copying | 0.6099 | 8.9627 | 0.053 | 0.461 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | copying | 0.9364 | 1.0247 | 0.014 | 0.015 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | copying | 0.8789 | 1.0710 | 0.012 | 0.013 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | copying | 0.1796 | 0.4553 | 0.063 | 0.028 | yes |

UCB method: percentile bootstrap, resampling paired runs within each case/GC
stratum; seed `20260726`; 100,000 deterministic resamples.

The port is correct and substantially reduces allocation, but it remains
performance-regressive under the predeclared gate. The exact focused
production control reinforces the diagnosis: the 4,096-variable root
propagation chain is `12.4291x`, while PHP(7,6) conflict analysis and learned
insertion is `0.3308x`. Together with the lower allocation totals, this
localizes the dominant residual regression to the broader
propagation/enqueue/resume path. It does not establish intrinsic `BO`
overhead or assign the entire factor to one inner kernel.
