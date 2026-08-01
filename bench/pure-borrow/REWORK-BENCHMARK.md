# Pure Borrow rework benchmark

Status: complete. Supersedes `PARITY-BENCHMARK.md`, whose headline
`3blocks` regression is now explained (§5) rather than merely measured.

Raw outputs, provenance, completed manifests, oracle dumps and control CSVs are
kept in ignored `workspace/rework-evidence/`; their hashes below make the
measurement reproducible without committing benchmark output.

## 1. Identity and protocol

| side | commit | tree | Pure Borrow pin |
| --- | --- | --- | --- |
| **M** — `main` | `57e6917cf61f89a6e152aa3793cc749894ae9a4d` | `45615b9977e5e1ee4c51cee05590f93cf94da17f` | — |
| **P0** — port before this work | `d0ed109f60e17b59436b39eae4c0506487621742` | `6d43d1295c34107696981f84f7a725238ebc28a9` | `25485e5` |
| **P2** — reworked port | `e33149d` | — | `d58e0d1` |

`25485e5` sat on the unmerged `konn/perf` branch and is **not** an ancestor of
Pure Borrow `main`; that branch was re-landed as PRs #15–#34.

- Toolchain: GHC 9.12.4, Cabal 3.14.2.0, explicit `--enable-optimization=2`.
- Concurrency: single-threaded; no `-threaded`, no RTS `-N`.
- Design: 1 discarded warmup pair, then 32 retained alternating fresh-process
  pairs per case × collector, over the tracked seven-case corpus under both
  nonmoving and copying GC — **448 retained observations per side, 896 per
  campaign**.
- Estimator: paired log elapsed ratio per stratum; stratified percentile
  bootstrap, 100,000 deterministic resamples, seed `20260726`; 95th percentile
  as the one-sided upper bound.
- Runner and analyzer are the tracked scripts, used unmodified.

Note on comparability: `PARITY-BENCHMARK.md` and `FINAL-BENCHMARK.md` were
produced by a **21-pair** protocol with different script hashes. They are
protocol-incomparable with this campaign and are cited only as history.

## 2. Headline result — reworked port versus `main`

| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |
| --- | ---: | ---: | ---: | ---: | :---: |
| nonmoving | 224 | 0.7552 | 0.7659 | 1.0200 | yes |
| copying | 224 | 0.7433 | 0.7580 | 1.0200 | yes |
| **all** | **448** | **0.7493** | **0.7582** | 1.0200 | **yes** |

- Results matched: true. Per-case elapsed gates **14/14**. Aggregate UCB gates
  **3/3**. Memory gates **14/14**.
- The port is faster than `main` on aggregate and allocates less in **every**
  stratum.

| Case | GC | Alloc ratio | MUT ratio | Elapsed ratio | M median | P2 median |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `uf20-01` | nonmoving | 0.8163 | 1.0000 | 0.9791 | 0.013 | 0.013 |
| `uf100-01` | nonmoving | 0.3092 | 0.4706 | 0.5418 | 0.025 | 0.013 |
| `flat200-1` | nonmoving | 0.4535 | 0.6000 | 0.6431 | 0.037 | 0.025 |
| `3blocks` | nonmoving | 0.6594 | 0.7727 | 0.8685 | 0.068 | 0.060 |
| `all-binary-2` | nonmoving | 0.9522 | n/a | 1.0579 | 0.013 | 0.013 |
| `implication-chain-12` | nonmoving | 0.9146 | n/a | 1.0270 | 0.012 | 0.013 |
| `php-7-6` | nonmoving | 0.2006 | 0.3404 | 0.4354 | 0.058 | 0.024 |
| `uf20-01` | copying | 0.8163 | 0.0000 | 1.0055 | 0.013 | 0.013 |
| `uf100-01` | copying | 0.3092 | 0.4444 | 0.5373 | 0.025 | 0.013 |
| `flat200-1` | copying | 0.4535 | 0.6154 | 0.6882 | 0.036 | 0.025 |
| `3blocks` | copying | 0.6594 | 0.7727 | 0.7694 | 0.049 | 0.037 |
| `all-binary-2` | copying | 0.9522 | n/a | 0.9727 | 0.013 | 0.012 |
| `implication-chain-12` | copying | 0.9146 | n/a | 1.0128 | 0.013 | 0.013 |
| `php-7-6` | copying | 0.2006 | 0.3404 | 0.4449 | 0.057 | 0.025 |

The two cases above 1.0 are `all-binary-2` (4 clauses) and
`implication-chain-12` (13 clauses); both sit at the ~0.013 s process floor
where mutator time is below the RTS's printed resolution, and both pass their
per-case gate.

### Against the previous parity campaign

`PARITY-BENCHMARK.md` recorded `3blocks` at **6.8186×** (nonmoving) and
**8.9627×** (copying) versus `main`, with a combined geomean of 1.1589. The
same case is now **0.8685×** and **0.7694×**, and the combined geomean is
0.7493. The regression was never a Pure Borrow cost — see §5.

## 3. Reworked port versus the previous port

| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |
| --- | ---: | ---: | ---: | ---: | :---: |
| nonmoving | 224 | 0.6569 | 0.6670 | 1.0200 | yes |
| copying | 224 | 0.6348 | 0.6436 | 1.0200 | yes |
| **all** | **448** | **0.6458** | **0.6525** | 1.0200 | **yes** |

Per-case elapsed gates 14/14; aggregate UCB gates 3/3; memory gates 11/14.
`3blocks` elapsed ratio is 0.1221 (nonmoving) and 0.0880 (copying); mutator
time falls from 0.400 s to 0.016 s.

The three memory-strata failures are the cost of the fix and were predeclared:
`3blocks` allocated is 109,426,872 against a limit of 108,677,581 — a 2.7%
increase from the `Data.Set` the replacement fold builds — plus two copied-byte
strata within 0.4% of their limits. Against `main`, `3blocks` still allocates
0.6594×.

## 4. Supplementary corpus

Every non-corpus instance in `data/` with side-`M` or side-`P0` mutator time
≥ 0.005 s, pre-registered from a survey of all 81 candidates and deduplicated by
content hash, plus one constructed dedup-stress fixture. Single fresh-process
observations, mutator seconds:

| case | clauses | M | P0 | P2 | P2/P0 | P2/M | P2 alloc ÷ M |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `flat200-479/flat200-10` | 2,237 | 0.096 | 0.070 | 0.049 | 0.700 | 0.510 | 0.383 |
| `sudoku/9x9/1` | 3,286 | 0.012 | 0.057 | 0.009 | 0.158 | 0.750 | 0.644 |
| `sudoku/9x9/2` | 3,281 | 0.024 | 0.058 | 0.014 | 0.241 | 0.583 | 0.529 |
| `uf100-430/uf100-010` | 430 | 0.022 | 0.011 | 0.010 | 0.909 | 0.455 | 0.296 |
| `uf100-430/uf100-0250` | 430 | 0.009 | 0.005 | 0.005 | 1.000 | 0.556 | 0.351 |
| `uf100-430/uf100-01000` | 430 | 0.006 | 0.004 | 0.003 | 0.750 | 0.500 | 0.381 |
| `flat200-1-dup` (fixture) | 4,474 | 0.027 | 0.038 | 0.017 | 0.447 | 0.630 | 0.499 |

The reworked port is faster than **both** baselines on every instance and
allocates 30–64% of `main`. These are single observations and are reported as
indicative, not as gated acceptance evidence.

## 5. Why the previous regression was not Pure Borrow

The tracked focused production control, rebuilt unchanged against all three
source trees:

| workload | clauses | M | P0 | P0/M | P2 | **P2/M** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `production/propagation/root-chain-4096` | 4,097 | 5.94 ms | 74.52 ms | **12.55×** | 4.11 ms | **0.693×** |
| `production/analysis-and-insertion/php-7-6` | 133 | 51.03 ms | 15.87 ms | 0.311× | 16.46 ms | 0.323× |

The P0 column reproduces the 12.4291× / 0.3308× figures recorded in
`MAIN-OPTIMIZATION-PARITY.md`. That control runs 4,097 clauses through
`prepareCDCL` on every iteration, so its ratio tracked clause count squared, not
propagation: 4,097² vs 133² is a factor of ~950, which is what produced the
12.55× / 0.31× asymmetry. With the quadratic gone the "root propagation" control
is 0.693× — the port is faster than `main` — while the conflict-analysis control
is unchanged.

`MAIN-OPTIMIZATION-PARITY.md` localized the residual to "the broader
propagation path". That localization was wrong, and this supersedes it.

## 6. Correctness evidence

- Production suite **25,224** tests (25,214 previously, plus 10 new
  normalization tests); focused Pure Borrow suite **14**.
- **Full trajectory oracle** — all 39 integral `SolverStats` counters, all three
  list-valued fields including the complete ordered per-conflict learned-clause
  transcript, and the returned model — is **byte-identical between P0 and P2**
  on all seven acceptance cases, and identical to `M` except
  `duplicateEnqueueCount`, which equals `decisionCount` in every case and is a
  pre-existing accounting difference in the port's decision path.
- The dedup-stress fixture is the test the acceptance corpus cannot perform: the
  corpus contains **zero** duplicate clauses, repeated literals or tautologies,
  so normalization is the identity on all seven cases. The fixture is
  `flat200-1` with every clause duplicated as a second block and a repeated
  literal appended in every 7th clause — 4,474 clauses. At P2 its full oracle is
  **identical to `flat200-1`'s**, and identical to P0's output on the same
  input.
- `test/Logic/Propositional/Classical/SAT/CDCL/NormalizationSpec.hs` asserts
  **ordered** list equality against the previous implementation, kept verbatim
  as the reference, over interleaved duplicate clauses, repeated literals after
  a first occurrence, tautologies, permuted duplicates, clauses colliding only
  after inner nub, and the unit/empty boundaries.
- All 896 acceptance observations per campaign returned the expected SAT/UNSAT
  answer; no timeouts, no parse failures, no discarded samples.

## 7. Artifact hashes

Executables:

```text
e7f3ac41f736be983e71f3473af62eaf0d3b4d0533b77a8bdcf31e090eb8316e  M    cdcl-dry
cbdde63a7b471ae1775c9dce9905e9019b062b060f570d2e8b8d43140aea1ebe  P0   cdcl-dry
8c9e68caa1564e667e54eae2b433790669fd67727f97543c0c22c5c2284046cf  P2   cdcl-dry
```

Scripts, raw data and fixtures:

```text
49a40582089846bcb6973fcedba2818bb7fb58714d47873805bbe0d6adb8de10  run-paired.mjs
d04ca646c3290e239fa4d6cd0509d625dc564a5de1283910ec9f642a51736772  analyze-paired.mjs
92416262ddc9b306ecc938dc0fc00bf86b8641180443ad83012148a64ffcf946  p2-vs-p0 baseline.csv
abc8eb45ea1bb70d8d86d965c6466fc937fa7b37d66d736c079de50206699865  p2-vs-p0 candidate.csv
ae159391a102e0a251781169b5514cd6742ff939dee2b04f66684133fd7cb302  p2-vs-m  baseline.csv
276423f94ae03fed7b52fbb7bee506b6579f252201428a45b842b0ca36d0e9db  p2-vs-m  candidate.csv
ba71765e91a45c981e00e0e566a87ae67d2d87df11ae31c8a245e8f1c278f25d  flat200-1-dup.cnf
c9303484e5ee952957941bb4655ac8d06e28e71fefa0abd51a200b1a85cc1dbb  all-binary-2-unsat.cnf
3b54f9f27d7139064a6b585ae40e1e650d634324f0ec3d476f0b268b527cb5f7  implication-chain-12-unsat.cnf
ea1c7697c4b2be671c51d340e207a71d6de0ccb7e2e5009c23bb8020d2075950  php-7-6-unsat.cnf
```

## 8. Not done

Three planned slices were specified and adversarially reviewed but not
implemented, because the measured result made them non-load-bearing for any
claim above:

- **S3** — strict entry projection in the propagation transaction, per Pure
  Borrow's new `getContents` placement guidance. Targets Core size and
  growable-header read placement, not the measured regression.
- **S4** — instrumented per-solve transaction / borrow-boundary / `getContents`
  counters, which upstream asked for to close its allocation-attribution model.
- **S5** — restoring `main`'s `ContradictingAssertion`-with-negative-reason
  guard. That branch is believed unreachable but is unguarded, and would index
  the clause arena at −1 through unchecked primitives if ever reached.

None of these is required by the results reported here; S5 in particular remains
an open safety item.
