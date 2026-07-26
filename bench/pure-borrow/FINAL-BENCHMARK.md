# Pure Borrow paired benchmark

## Identity and protocol

- Baseline source commit:
  `05654118eb8cebc086684d9d73f9dfa6e2d7e531` (the exact current-branch
  content frozen before the port).
- Candidate branch: `konn/pure-borrow`; the exact benchmarked executable is
  identified by SHA-256 below.
- Pure Borrow:
  `SoftwareFoundationGroupAtKyotoU/pure-borrow@79a0d1878ccbce8895039c253cc9e462a788d3f3`.
- Toolchain: GHC 9.12.4, Cabal 3.14.2.0, optimized `-O2` executables.
- Concurrency: single-threaded; neither executable uses `-threaded`, and no
  RTS `-N` option was used.
- Design: 21 alternating, fresh-process baseline/candidate pairs after warmup,
  for seven SAT/UNSAT inputs under both copying and nonmoving GC.
- Estimator: candidate/baseline paired elapsed ratio within each case/GC
  stratum; aggregate geometric mean with 100,000 deterministic stratified
  bootstrap resamples.
- Acceptance limits: per-case median/MAD gates from the migration plan and an
  aggregate 95% upper-confidence bound no greater than 1.02.

Exact executable SHA-256 fingerprints:

```text
4a9a55564ff49767dd0eed93da6f013541b7b619d58c915922c35236b226461a  baseline
82214a166442650ceb23d84138092f0392e734418483a9dbb9bb4efbec5753ba  candidate
```

Artifact SHA-256 fingerprints:

```text
6286f83d45bede74691db7337d0a0245b6d94b11fb9f2f68e996f8f752d94a26  run-paired.mjs
a13e0f85b33f12f51c53cbe511172cd86bd787c03d1aa6b9fca0ce572adfb73b  final-baseline-raw.csv
a908c9452a5707d4b3b5c10df3696b9ca66ee39bcc1e7513259de018a9b97bd3  final-candidate-raw.csv
7bc7ceee7413315db52f88cd767be3651ddc8e38f107b4affc28d94261bf488f  final-report.json
```

## Outcome

- Results matched: true
- Per-case elapsed gates: 10/14
- Aggregate UCB gates: 0/3

| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |
| --- | ---: | ---: | ---: | ---: | :---: |
| nonmoving | 147 | 1.2705 | 1.3128 | 1.0200 | no |
| copying | 147 | 1.3357 | 1.3665 | 1.0200 | no |
| all | 294 | 1.3027 | 1.3290 | 1.0200 | no |

| Case | GC | Allocation ratio | Elapsed ratio | Baseline median (s) | Candidate median (s) | Gate |
| --- | --- | ---: | ---: | ---: | ---: | :---: |
| data/satlib/uf20-91/uf20-01.cnf | nonmoving | 0.7965 | 0.9967 | 0.012 | 0.012 | yes |
| data/satlib/uf100-430/uf100-01.cnf | nonmoving | 0.4028 | 0.9161 | 0.024 | 0.024 | yes |
| data/satlib/flat200-479/flat200-1.cnf | nonmoving | 0.5533 | 1.4663 | 0.046 | 0.060 | no |
| data/satlib/Bejing/3blocks.cnf | nonmoving | 0.6431 | 7.3231 | 0.072 | 0.512 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | nonmoving | 0.9333 | 1.0489 | 0.012 | 0.013 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | nonmoving | 0.8615 | 0.9671 | 0.013 | 0.012 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | nonmoving | 0.2969 | 0.5373 | 0.063 | 0.036 | yes |
| data/satlib/uf20-91/uf20-01.cnf | copying | 0.7965 | 1.0079 | 0.012 | 0.012 | yes |
| data/satlib/uf100-430/uf100-01.cnf | copying | 0.4028 | 0.9491 | 0.025 | 0.024 | yes |
| data/satlib/flat200-479/flat200-1.cnf | copying | 0.5533 | 1.3836 | 0.038 | 0.059 | no |
| data/satlib/Bejing/3blocks.cnf | copying | 0.6431 | 9.8971 | 0.049 | 0.455 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | copying | 0.9333 | 1.0091 | 0.013 | 0.013 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | copying | 0.8615 | 1.0370 | 0.013 | 0.013 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | copying | 0.2969 | 0.5534 | 0.060 | 0.036 | yes |

UCB method: percentile bootstrap, resampling paired runs within each case/GC stratum; 100000 deterministic resamples.

The port is correct but performance-regressive under the predeclared gate.
The aggregate regression is dominated by `3blocks`; candidate allocation is
lower on every case, so allocation reduction does not compensate for that
elapsed-time result.
