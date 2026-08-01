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
- **Allocated bytes** are lower than `main` in every one of the 14 strata
  (0.2006×–0.9522×). That is not the same as "lower memory everywhere":
  *copied* bytes are higher on two strata (`all-binary-2` nonmoving 1.0187,
  `implication-chain-12` nonmoving 1.0210) and *residency* is higher on two
  (`php-7-6` copying 1.0956, nonmoving 1.0029). All four pass because the gate
  carries an allowance; the ratios are stated here so the gate count is not read
  as a stronger claim than it is.
- Elapsed is above 1.0 on four strata, all at the process floor: `all-binary-2`
  nonmoving 1.0579, `implication-chain-12` nonmoving 1.0270 / copying 1.0128,
  `uf20-01` copying 1.0055.

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

Six of the fourteen strata — `uf20-01`, `all-binary-2` and
`implication-chain-12` under both collectors — sit at the ~0.013 s process floor
with mutator time at or below the RTS's 1 ms print resolution, so their ratios
are ~1.0 by construction. The analyzer weights all 448 pair log-ratios equally,
so those six **dilute** the aggregate rather than dominate it: restricted to the
eight strata with measurable mutator time the figure is **0.5995** against
`main` and **0.4655** against P0. The 0.7493 headline is therefore conservative,
but it is a spawn-floor-contaminated number rather than a solver-time one, and
the per-stratum rows above are the better evidence. `PURE-BORROW-REWORK-PLAN.md`
§6.5 demotes this aggregate to a regression screen for exactly this reason:
none of the three aggregate UCB booleans is a binding criterion.

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

This comparison bundles **S0 + S1 + S2** — the accessor, the pin bump and the
normalization fix — not S2 alone.

### Attribution: S2 alone

| Aggregate | Pairs | Geomean ratio | 95% UCB |
| --- | ---: | ---: | ---: |
| nonmoving | 224 | 0.6643 | 0.6773 |
| copying | 224 | 0.6400 | 0.6552 |
| **all** | **448** | **0.6520** | **0.6620** |

P2 against P1 (`848f312`, = S0+S1) is 0.6520 where P2 against P0 is 0.6458.
The accessor and the pin bump together account for essentially none of the
improvement; S2 owns it.

### The three memory-strata failures, named

| stratum | sub-gate | baseline | candidate | limit |
| --- | --- | ---: | ---: | ---: |
| `3blocks` / nonmoving | allocated | 106,542,632 | 109,426,872 | 108,677,581 |
| `3blocks` / copying | allocated | 106,542,632 | 109,426,872 | 108,677,581 |
| `flat200-1` / copying | **copied** | 4,747,760 | 4,870,488 | 4,846,811 |

An earlier revision of this document described these as "`3blocks` allocated
plus two copied-byte strata". That was wrong: two of the three are `3blocks`'s
allocated gate under each collector, and there is exactly one copied-byte
failure. MADs are zero, so these are deterministic, not noise.

**They are attributed, not waived.** A normalize-only driver
(`bench/pure-borrow/stats-probe/NormalizeOnly.hs`) parses a CNF, deep-forces
only the normalized clause list, and exits; run at P1 and P2 under `+RTS -s` it
isolates the fold's true cost:

| case | P1 | P2 | Δ (normalization) | whole-program P0→P2 |
| --- | ---: | ---: | ---: | ---: |
| `3blocks` | 51,351,504 | 54,235,744 | **+2,884,240** | **+2,884,240** |
| `flat200-1` | 10,727,808 | 11,233,632 | **+505,824** | **+505,824** |
| `php-7-6` | 826,520 | 834,408 | **+7,888** | **+7,888** |
| `uf100-01` | 2,512,040 | 2,550,120 | +38,080 | +40,440 |
| `uf20-01` | 653,152 | 653,408 | +256 | −624 |

On the three cases that matter the whole-program increase equals the measured
normalization cost **to the byte**. Nothing outside the fold allocates more.
`3blocks`'s 2.7% rise buys a 25× mutator-time drop, and the port still allocates
0.6594× of `main` on that case. The fold is a net allocation *win* on small
inputs (`uf20-01` −624 B, `all-binary-2` −752 B, `implication-chain-12`
−1,272 B).

The `flat200-1`/copying **copied**-bytes failure is a genuine un-waived gate
failure: it exceeds its limit by 23,677 bytes (0.5%). It is a second-order
consequence of allocating 505,824 more bytes in the same solve, and it is
recorded here as a failure rather than argued away.

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
allocates 30–64% of `main`.

**These are single observations, and the planned gate on them was not run.**
`workspace/PURE-BORROW-REWORK-PLAN.md` §6.4/§6.5 froze these seven cases as
14 *binding* supplementary strata, to be measured by a `run-holdout.mjs` /
`analyze-holdout.mjs` pair copied verbatim from the acceptance scripts. Those
runners were never written, so no paired campaign, no medians, no MADs and no
bootstrap bounds exist for this corpus. `mut_elapsed_s` is quantized to 1 ms, so
the ratios for the three `uf100` rows (0.003–0.011 s) carry little information.
One third of the plan's binding acceptance criteria is therefore **unmet, not
passed** — the table above is indicative only and should not be read as
acceptance evidence.

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

**Read this control only in the negative direction.** Once the quadratic is
gone, `root-chain-4096` is dominated by clause construction and store setup —
`buildClause` over 4,097 clauses, `V.fromList`/`U.fromList`, seeding 8,192 watch
occurrences, eleven owners in `newCDCLStore` — against roughly 4,096
assignments. Those construction paths are implemented completely differently on
the two sides. The reasoning that makes a *high* residual uninterpretable makes
the measured 0.693× equally uninterpretable as a propagation result, and the
0.693× also bundles S1. What this control does support is the negative claim it
is used for here: the 12.55× was clause preparation, because removing 68.6 ms of
predicted `nub` cost removes 70.4 ms of measured time. It does **not** support
"the port's propagation is faster than `main`", and the workload's name should
no longer be taken at face value.

## 6. Correctness evidence

- Production suite **25,225** tests (25,214 previously, plus 11 new
  normalization tests); instrumented suite **25,236**; focused Pure Borrow suite
  **14**. Run logs retained under `workspace/rework-evidence/tests/`.
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

**What the oracle does and does not cover.** The retained probe
(`bench/pure-borrow/stats-probe/StatsProbe.hs`) emits the 39 counters, the three
list fields, the model, and — added after the first post-implementation review —
the normalized clause list, variable count and clause count via
`normalizedClausesForTest`. It does **not** implement the plan's trail-contents
rolling hash. The clause list cannot be compared against `main`, which has no
equivalent accessor, so that item is P-side only; against `main` the oracle is
items 1–3. On `implication-chain-12` and `all-binary-2` — low-conflict and
UNSAT — `analysisLearnedTrace` is empty and there is no model, so the cross-side
oracle there reduces to counters alone.

## 7. Between-campaign dispersion

The identical P2 binary (`8c9e68ca…`) was measured in three campaigns. Its
allocated bytes agree to the byte across all 14 strata, but elapsed medians do
not:

| stratum | P2-vs-P0 draw | P2-vs-M draw | \|Δ\| | drift limit |
| --- | ---: | ---: | ---: | ---: |
| `3blocks` / nonmoving | 0.050 s | 0.060 s | 0.0100 | 0.0045 |

The plan's §7 drift rule is `|mᵢ − mⱼ| ≤ MADᵢ + MADⱼ + 0.001 s`, and this
**violates it**. `3blocks`/copying MUT is marginal at the same boundary
(0.016 vs 0.017, limit 0.0010). No gate verdict flips — both campaigns give
14/14 elapsed gates and the geomeans reproduce exactly from the raw CSVs — but
between-campaign dispersion of ~20% on `3blocks`/nonmoving against a
within-stratum MAD of 0.002 s means the bootstrap, which resamples only within
strata, **understates uncertainty on the single case this rework is about**.
§2's `3blocks` row quotes the slower draw (0.060 s, ratio 0.8685); the other
draw of the same binary gives 0.050/0.068 = 0.735. Both are far below the 6.82×
this case previously showed, so the conclusion is unaffected, but the figure
should be read as ≈0.74–0.87 rather than as a point estimate.

A note on evidence timestamps: every file under
`workspace/rework-evidence/campaigns/` carries an identical mtime because the
directories were copied there with `cp -r` (no `-p`) after both campaigns
finished. The campaigns themselves were run sequentially, not concurrently. The
two `run.log` files are byte-identical because the runner logs only
`collector case n/32` progress lines, which are identical by construction; they
carry no run identity and are not adequate provenance on their own — the
manifests and CSV hashes are.

## 8. Artifact hashes

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

## 9. Not done

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
