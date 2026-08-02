# Optimization parity with the polished primary CDCL solver

Date: 2026-07-26

Polished reference:
`346cec06f4f19a6acd7e885496901281072696bf`
(`konn/perf-2`)

Pure Borrow branch: `konn/pure-borrow`

## Comparison result

The Pure Borrow port already contained the primary solver's preallocated trail
and decision-level storage, explicit propagation cursor, event-driven BCP,
literal-indexed intrusive watch lists, one bulk occurrence-chain kernel, indexed
rollback boundaries, and restart/VSIDS behavior.

Two polished-primary changes were absent:

| Primary commit | Missing behavior | Pure Borrow adaptation |
| --- | --- | --- |
| `9ec4edf` | Canonical reverse-trail first-UIP using a reusable stamp array and fixed scratch prefix instead of `Data.Set` resolvents | Added a fine-grained `AnalysisWorkspace` with independent epoch, stamp, and literal-scratch owners; the transaction locally splits clauses, valuation, trail, workspace, and VSIDS, then opens rank-2 pins once around one bulk kernel |
| `346cec0` | Allocation-free deterministic ordering of learned lower literals, including least-literal tie breaking at the backjump level | Added in-place heap sort of only the used scratch prefix, exact target selection, and one exact-size learned-vector allocation |

The old Pure Borrow analyzer and its `checkUnitAt`, repeated `Set` union/filter,
latest-conflict search, and resolvent materialization path were deleted.

## Ownership audit

The adaptation does not introduce an aggregate state reference or State-shaped
runner. The production record now has this additional nested resource:

```text
CDCLStore
└── AnalysisWorkspace
    ├── epoch       fixed one-cell Word64 owner
    ├── stamps      fixed Word64 owner, one cell per variable
    └── literals    fixed Lit scratch owner, one cell per variable
```

Conflict analysis enters one `reborrowing` scope and uses typed `(.@)` splits.
The six independent buffers—clause literals, valuation, active trail, epoch,
stamps, and scratch—are exposed through rank-2 pins. The unsafe conversion is
confined to the low-level analysis kernel, which returns every pin unchanged.
VSIDS remains its own persistent `Ref` and is opened once for the complete
analysis transaction.

## Correctness evidence

- Production suite: 25,214 tests passed.
- Instrumented suite: 25,225 tests passed.
- Added parity checks cover:
  - reverse-trail pivot order and exact visit/mark counters;
  - forced epoch wrap and stamp clearing;
  - nonzero and tied backjump targets;
  - deterministic ordered learned remainders;
  - bounded-random learned-clause entailment and asserting polarity.

## Exact current-main performance evidence

The final paired `-O2` comparison uses current `main` commit
`57e6917cf61f89a6e152aa3793cc749894ae9a4d` as the baseline and candidate
commit `0a5efdd3311c19bf64666b44a47f7fbf6578ca5f`. Both clean source trees were
built explicitly at `-O2`, without a local Cabal overlay. The completed
campaign is recorded in `bench/pure-borrow/PARITY-BENCHMARK.md`:

- all 294 SAT/UNSAT results match;
- 10/14 per-case elapsed gates pass;
- combined candidate/baseline elapsed geomean: 1.1589;
- combined 95% upper confidence bound: 1.1818;
- the Pure Borrow candidate allocates less in every case/GC stratum;
- the two substantive workload failures are `flat200` and the watch-heavy
  `3blocks` case; `3blocks` is 6.82x under nonmoving GC and 8.96x under
  copying GC.

The first-UIP algorithmic gap is therefore closed on the Herbrand side. The
remaining outlier is not caused by the removed `Set` analyzer. Current evidence
localizes it only to the broader propagation path: the raw scan is direct, but
boxed per-trail-literal and `UnitRequired` resume boundaries remain.

The corrected runner deterministically generates the three synthetic cases in
ignored `workspace/tuning-corpus`, refuses content drift, validates clean
40-character commit/tree identities and captured GHC/Cabal versions, hashes
the runner, analyzer, executables, and all seven fixtures, then adds both raw
CSV hashes to a completed post-run manifest. The analyzer checks exact headers,
unique and identical row keys, result parity, and finite RTS metrics before
using the declared seed `20260726`.

The focused 4,096-occurrence architecture control measured 25.9 us for direct
IO, 375 us for the legacy linear path, and 287 us for the rank-2 Pure Borrow
path. Its variance is high and it does not reproduce the full production
enqueue/resume path; it is retained only as a control showing that the pin
architecture improves on per-operation linear access.

The replacement standalone production harness was built unchanged against the
same two exact source trees. Both instrumented trajectory verifiers passed.
Across three alternating fresh-process pairs, the complete 4,096-variable
root-propagation chain was 12.4291x baseline, while PHP(7,6) conflict analysis
and learned insertion was 0.3308x baseline. This diagnostic is not the
acceptance estimator, but it supports localization to the propagation path
without claiming intrinsic `BO` overhead or assigning the entire factor to
one inner kernel.

All raw final outputs, provenance, and manifests are kept in ignored
`workspace/pure-borrow-benchmark`. This follows the workspace-artifact policy;
the tracked rendered report records their SHA-256 hashes.
