# Phase 1 Pure Borrow architecture evidence

Status: historical evidence from the bounded Phase 1 spike. The production
port, complete correctness runs, and final paired benchmark now supersede this
gate record. The negative compile matrix was not completed; the user explicitly
made missing low-level Pure Borrow bricks and their performance deficiency
non-blocking for completing the Herbrand port.

## Scope

The checked implementation has:

- a strict `CDCLStore s` owner record, not `Ref (CDCLStore s)`;
- independently owned valuation, trail, level-start, clause, watch, and VSIDS
  roots;
- one strict five-field propagation split using `(.@)`;
- nested `ClauseArena` and `WatchMap` splits;
- three rank-2 growable buffer pins and one VSIDS `Ref.update`, all outside the
  occurrence worker;
- direct `BO` algorithms with no algorithm import of `BO.Unsafe`;
- a watched-literal spike with watch relocation, unit enqueue plus subsequent
  trail drain, exact current-plus-unread suffix restoration, direct clause
  conflict, and root assertion conflict;
- aggregate lender reclaim followed by independent freezing of every owner.

The growable `PinnedBuffer` is a newtype. Its logical length is fixed for the
rank-2 transaction and growth is not exported while it is live.

## Reproduction

From the migration worktree:

```text
cabal --config-file=/tmp/herbrand-pure-borrow-cabal.config \
  test herbrand-pure-borrow-test --offline
```

Result with GHC 9.12.4 and the component's `-O2` option:

```text
All 10 tests passed
```

The tests cover fixed write/read/reclaim, unboxed and boxed forced growth,
4,096 direct operations plus truncation under one pin, optimized distinct
allocations, aggregate splitting/reclaim, watch movement, a two-literal unit
chain, exact conflict suffix restoration, and root assertion conflict.

The Core build used a fresh build directory:

```text
cabal --config-file=/tmp/herbrand-pure-borrow-cabal.config \
  --builddir=/tmp/herbrand-pure-borrow-core \
  build herbrand-pure-borrow-test --offline \
  --ghc-options='-ddump-simpl -dsuppress-all -ddump-to-file'
```

In the optimized `propagateWatchSpike` entry block there are exactly four
`unsafeReadRef#` and four `unsafeWriteRef#` calls: clause literals, clause
bodies, watch-next links, and VSIDS. All occur around the complete transaction.

The `processOccurrences` Core region contains:

```text
unsafeReadRef#/unsafeWriteRef#/Header/Pinned/After: 0
readIntArray#:                                      8
writeIntArray#:                                    23
```

The worker therefore receives direct specialized buffers. It does not reopen a
growable header, reconstruct a `Header`, or thread a boxed pin per occurrence.

## Source fingerprints

These hashes identify the uncommitted spike inspected above:

```text
b0e1db8ff3da81ae820a59c9b81c20ebfd009b6d344e32be8d7cdb76e85f7c4a  fixed unboxed store
77fcdb75e5726e6b8d709da1bd8f37bba0d6ee95aaf7795f652cd1ffa7fea12c  growable unboxed store
3b075cd27589cbc047c4f19136b0b018deedeb9da6f099bbcd5e0d0f19fc75cb  growable boxed store
734fa133c49fb34a70e3c90d47efe7c317140f3bdfd6cbb26e15724b54dc4acb  aggregate store
a2640d626c6dc0e78e7d1c1249884340645e84d0a226e91d8da30ec72d36191a  propagation spike
7297c1b5ef4bfb602160220ac0fe425267b5f1a23a6e5fc6b0e6da685d7de65b  optimized tests
```

The worktree branch is `konn/pure-borrow`. Its current committed parent is
`86b77aec2ff6f638f2175e8ab220efc39bc01a20`; the working tree removes that
commit's rejected aggregate-State bridge.

## Superseded Phase 1 items

- Add Cabal-driven negative compile fixtures for escaping pins, duplicate
  labels, owner coercion/copy, and mutable/shared overlap.
- The focused comparison was superseded by the production paired benchmark in
  `FINAL-BENCHMARK.md`.
- Production Core and runtime experiments replaced the representative integer
  spike; their findings are recorded in
  `workspace/FEEDBACK-FOR-PURE-BORROW.md`.
