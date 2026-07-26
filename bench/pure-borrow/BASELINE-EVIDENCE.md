# Pure Borrow migration baseline evidence

Captured on 2026-07-26 before Phase 1 of the migration.

## Identity and toolchain

- Baseline commit: `05654118eb8cebc086684d9d73f9dfa6e2d7e531`
- Baseline subject: `revert: restore complete benchmark baselines`
- Compiler selected by Cabal: GHC `9.12.4`
- Cabal: `3.14.2.0`
- Host: `Darwin 25.5.0 arm64`
- Optimization: `-O2`
- Benchmark concurrency: single-threaded; no `-threaded`, RTS `-N`, or
  parallel benchmark configuration
- `cabal.project` SHA-256:
  `3e37e9f332a52d0796552c37b2395330e07e6806334337e934df7574ced5ee1e`
- `cabal.project.freeze` SHA-256:
  `f200b383c38c95de888a15cac68ca86a683ef57a6a90631627afa09f82a8472e`
- Baseline `bench/sat.hs` SHA-256:
  `c463eed97d997975da739826b916b776cf086d7b4c62b834eee4b6057e65f9b9`

The actual builds used the user configuration copied to
`/tmp/herbrand-pure-borrow-cabal.config`, with build summaries redirected to
`/tmp` and remote build reporting disabled. All Cabal commands were run
offline.

## Observation overlay

The immutable baseline does not expose an ordered CDCL trajectory. The tracked
overlay is [`baseline-trace-overlay.patch`](baseline-trace-overlay.patch).
It adds only:

- a manual `cdcl-instrumented` Cabal flag;
- CPP-controlled trace storage and hooks;
- schema version 1 trace types;
- `cdcl-trace-snapshot`, a deterministic serializer with normalized models;
- exact transcripts for small witnesses and SHA-256/count pairs for large
  witnesses.

The trace records decisions, successful assignments and reasons, watch moves,
conflicts, learned clauses and watch indices, ordinary/restart backtracks,
restart classifications, and final SAT status.

- Overlay SHA-256:
  `880d21f56ea103619b9e265daaaf5a0701221edc6c97a62b35fc86f53f29b719`
- Patched Git tree:
  `76a7018cb96d6b40a2b19a1c1c897d32453b610e`
- Instrumented snapshot executable SHA-256:
  `15eaceb9523881d8a4d7e75fc8895eef82d6c272e984e828957ecea652e70b1f`
- Frozen output:
  [`baseline-trace-v1.expected`](baseline-trace-v1.expected)
- Frozen output SHA-256:
  `f8c6e4d340322c14e534656826c202c94d6c418224d1db3afe7124f70d3c7bde`

Replay was checked by cloning the repository, detaching at the baseline commit,
applying the tracked patch, staging its four paths, and running `git
write-tree`. The replay produced the patched tree above.

## Correctness and non-interference

Production:

```text
cabal --config-file=/tmp/herbrand-pure-borrow-cabal.config \
  test herbrand-test -f-cdcl-instrumented -O2 --offline \
  --test-show-details=direct
All 25214 tests passed
```

Instrumented:

```text
cabal --config-file=/tmp/herbrand-pure-borrow-cabal.config \
  test herbrand-test -fcdcl-instrumented -O2 --offline \
  --test-show-details=direct
All 25222 tests passed
```

The instrumented snapshot was also rebuilt with `recordTraceEvent` replaced by
an instrumented no-op. Hashing only `case=`, normalized `result=`, and all
pre-existing scalar `stats=` lines produced the same digest for the full-trace
and no-trace builds:

```text
1de53fe4a64f0dec3ed0c4e3ef142fc277482b77c36ccd6a0e948b72769dd805
```

This checks that trajectory collection preserves every frozen witness model
and scalar counter. The production suite additionally checks the original
non-instrumented behavior with all trace hooks compiled to no-ops.

## Frozen trajectory cases

Schema 1 covers:

- `root-units`: exact root propagation transcript;
- `mixed-polarity-watch`: 194 events, SHA-256
  `d913d586f8bc834b352086d8c4a7d26f9a7f970a535c51d6d06920a880fcc438`;
- `long-watch-chain`: 256 events including 126 watch moves, SHA-256
  `b957691f24620105090667360fdbf69fc05c5c67a1b392acc316390acfe519b0`;
- `watch-suffix-restore`: exact conflict, learned unit, cutoff, and replay;
- `restart-satisfiable`: exact open-clause restart classification;
- `restart-unsatisfiable`: exact unit-clause restart classification;
- `pure-literal-bypass`: exact early SAT finalization;
- `pure-literal-fallback`: exact contradictory-root UNSAT finalization.

The expected file is authoritative for normalized models, all scalar counters,
event counts, exact small transcripts, and large transcript digests.

## Benchmark corpus

The baseline benchmark reads every tracked file below:

| Group | Count |
|---|---:|
| `data/sat/huge/**` | 11 |
| `data/sudoku/**` | 4 |
| `data/satlib/**` | 1,021 |

The SHA-256 of the path-sorted per-file SHA-256 manifest for all 1,036 files is:

```text
739fc196a9785e261eae055cc72840c563ef53ef984aa570f30941466a28f1f5
```

The following representatives are frozen for smoke checks and later
single-threaded benchmark comparison. The exact baseline production executable
reported `Satisfiable` for each.

| Fixture | SHA-256 | Expected |
|---|---|---|
| `data/sat/huge/0.cnf` | `0e2cc8440b3561136d94ad5140be6e5f652d1644a3df0106f34d18203ece9bfd` | SAT |
| `data/sudoku/9x9/1.cnf` | `b4937a0dbcc92b104d04fd9c5e14d15dc6d10eef23a1b2283c844d2516a4d8c8` | SAT |
| `data/satlib/Bejing/2bitcomp_5.cnf` | `de54f317604f0d8417340897488986a4d55b26ceb54c46bc2af127f3f0cc0a77` | SAT |
| `data/satlib/flat200-479/flat200-1.cnf` | `f8516312492ea618618ffb65b0052dbfc8c3563c4ee5c341d24bf5b84e30f39f` | SAT |
| `data/satlib/uf100-430/uf100-01.cnf` | `56ac0fd4a0fd699c5192c8536ff1fc666d386913ed8086fc153b2e708e9f66aa` | SAT |
| `data/satlib/uf20-91-full/uf20-01.cnf` | `bbb43578ee4f0634de44a7632b6df4ee6b9204f1c82e77660616b0891b00eb24` | SAT |

The production `cdcl-dry` executable used for those checks has SHA-256
`4a9a55564ff49767dd0eed93da6f013541b7b619d58c915922c35236b226461a`.
