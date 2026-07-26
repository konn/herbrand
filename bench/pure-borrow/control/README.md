# Production-path focused controls

This standalone Cabal benchmark isolates two production `CDCL.solveVarId`
paths:

- root-level watched-literal propagation through 4,096 variables; and
- conflict analysis, learned-clause insertion, backtracking, and propagation on
  `PHP(7,6)`.

The exact same tracked `Main.hs` and Cabal stanza are built once against the
polished baseline Herbrand commit and once against the Pure Borrow candidate.
The harness constructs and fully evaluates both CNFs before Tasty Bench begins,
so the measurement excludes DIMACS parsing and fixture I/O.

For each side, use an absolute temporary `cabal.project` containing the exact
Herbrand checkout and this directory's
`pure-borrow-production-controls.cabal`. Build with the recorded absolute Cabal
and GHC executables, `-O2`, no `-threaded`, no RTS `-N`, and a separate
temporary build directory. The provenance file supplied to `run-paired.mjs`
records each clean source commit/tree, exact production and instrumented
verification build commands, and the absolute path/hash of the actual Cabal
project file selecting that source. The controller independently hashes each
project and rejects a project that does not name the declared Herbrand package
and this tracked control package.

The runner verifies both clean source identities and the toolchain, hashes the
harness, package description, executables, provenance, and output CSVs, then
performs three paired fresh-process runs in alternating order. Each process
uses the same Tasty Bench arguments and must report exactly the two expected
benchmark names with finite positive timing values.

The production benchmark function rejects any result other than `Unsat`.
Before timing, a separately built verifier runs the same CNFs against an
instrumented Herbrand library. It requires decision-free propagation ending in
a classified root conflict, without learning or backtracking, for the chain;
and positive conflict, analysis, learned-literal, and ordinary backtrack counts
for PHP(7,6). The verifier binaries and their build commands are part of
provenance; their timings are not mixed into the production CSVs.

`analyze-paired.mjs` then requires the complete two-name, three-run key set and
reports paired candidate/baseline geometric-mean ratios. This focused result is
diagnostic and has no independent acceptance threshold.

These controls diagnose where whole-solver performance changes occur. The
seven-case, two-GC, 294-pair `cdcl-dry` campaign remains the acceptance
benchmark.
