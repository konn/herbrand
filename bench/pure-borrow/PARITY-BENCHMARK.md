# Historical Pure Borrow paired benchmark

Status: historical `b7030c31268820c761feb17e38fd322e5ac6a61b`
measurement. The independent performance review rejected this campaign as
final evidence because its candidate tree identity, generated-fixture
provenance, analyzer seed, and post-run artifact manifest were incomplete.
The results below are retained for comparison, not presented as the final
exact-commit campaign. The corrected campaign is pending.

## Identity and protocol

- Polished primary baseline:
  `346cec06f4f19a6acd7e885496901281072696bf`
  (`perf: stabilize learned clause ordering`), which includes
  `9ec4edf3b76aa16b7594bf1d4c0a87d6ddbcb9a1`
  (`perf: replace set-based first-UIP analysis`).
- Candidate: `b7030c31268820c761feb17e38fd322e5ac6a61b`
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
  bootstrap resamples.

Executable SHA-256 fingerprints:

```text
e7f3ac41f736be983e71f3473af62eaf0d3b4d0533b77a8bdcf31e090eb8316e  polished-primary
5ab6a171483949e93864fbe282c7f510658a1b554cac5e1e4e4fc21a2d8fd1c9  pure-borrow
```

The raw CSVs and runner retain the `workspace/tuning-corpus/...` paths used
during this measurement. Those synthetic inputs remain intentionally
untracked; their hashes below identify the exact fixture contents without
adding them to the branch HEAD.

Artifact SHA-256 fingerprints:

```text
6286f83d45bede74691db7337d0a0245b6d94b11fb9f2f68e996f8f752d94a26  run-paired.mjs
b90960051c698dd18021523453a9ca4d15bd335ac587974483e9c8b300b35df0  analyze-paired.mjs
b37c465e194a7c995bec1d8da77aab33c63cdf6607b9d3a7992a3a3205d15f28  parity-main-raw.csv
12e9083d77c38323d1ab10d461adc21337b1cad4821a169d142046d84854f357  parity-pure-borrow-raw.csv
e4ffbd8f29a1c8ffeb4377a14b56f3d32422af5af2d553bf4aa55286bae296b3  parity-report.json
c9303484e5ee952957941bb4655ac8d06e28e71fefa0abd51a200b1a85cc1dbb  all-binary-2-unsat.cnf
3b54f9f27d7139064a6b585ae40e1e650d634324f0ec3d476f0b268b527cb5f7  implication-chain-12-unsat.cnf
ea1c7697c4b2be671c51d340e207a71d6de0ccb7e2e5009c23bb8020d2075950  php-7-6-unsat.cnf
```

## Outcome

- Results matched: true
- Per-case elapsed gates: 12/14
- Aggregate UCB gates: 0/3

| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |
| --- | ---: | ---: | ---: | ---: | :---: |
| nonmoving | 147 | 1.1214 | 1.1573 | 1.0200 | no |
| copying | 147 | 1.1507 | 1.2002 | 1.0200 | no |
| all | 294 | 1.1359 | 1.1663 | 1.0200 | no |

| Case | GC | Allocation ratio | Elapsed ratio | Baseline median (s) | Candidate median (s) | Gate |
| --- | --- | ---: | ---: | ---: | ---: | :---: |
| data/satlib/uf20-91/uf20-01.cnf | nonmoving | 0.7793 | 0.9914 | 0.012 | 0.011 | yes |
| data/satlib/uf100-430/uf100-01.cnf | nonmoving | 0.2943 | 0.6460 | 0.024 | 0.021 | yes |
| data/satlib/flat200-479/flat200-1.cnf | nonmoving | 0.4361 | 1.3859 | 0.043 | 0.057 | yes |
| data/satlib/Bejing/3blocks.cnf | nonmoving | 0.6099 | 6.8324 | 0.070 | 0.491 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | nonmoving | 0.9364 | 1.0449 | 0.012 | 0.012 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | nonmoving | 0.8789 | 0.9620 | 0.012 | 0.011 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | nonmoving | 0.1796 | 0.3657 | 0.062 | 0.024 | yes |
| data/satlib/uf20-91/uf20-01.cnf | copying | 0.7793 | 1.0216 | 0.012 | 0.012 | yes |
| data/satlib/uf100-430/uf100-01.cnf | copying | 0.2943 | 0.6325 | 0.035 | 0.024 | yes |
| data/satlib/flat200-479/flat200-1.cnf | copying | 0.4361 | 1.3061 | 0.047 | 0.062 | yes |
| data/satlib/Bejing/3blocks.cnf | copying | 0.6099 | 10.1118 | 0.049 | 0.525 | no |
| workspace/tuning-corpus/all-binary-2-unsat.cnf | copying | 0.9364 | 0.9727 | 0.012 | 0.012 | yes |
| workspace/tuning-corpus/implication-chain-12-unsat.cnf | copying | 0.8789 | 0.9008 | 0.013 | 0.012 | yes |
| workspace/tuning-corpus/php-7-6-unsat.cnf | copying | 0.1796 | 0.3572 | 0.071 | 0.025 | yes |

UCB method: percentile bootstrap, resampling paired runs within each case/GC stratum; 100000 deterministic resamples.
