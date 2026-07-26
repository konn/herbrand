# Repository Guidelines

## Project Structure & Module Organization

Library modules live under `src/`. SAT solvers are in `src/Logic/Propositional/Classical/SAT/`; CDCL internals belong in `CDCL/`. Executables are under `app/`, shared helpers under `libs/`, tests under `test/`, and benchmarks under `bench/`. Keep DIMACS fixtures in `data/`.

## Agent Tooling

For Haskell work, use the [`konn/haskell-claude-marketplace`](https://github.com/konn/haskell-claude-marketplace) marketplace: invoke its `haskell` super-skill, inspect HLS diagnostics before full builds, and consult Haddock or Hoogle for APIs. Enable `haskell-format-skill` and `haskell-cabal-gild-skill`; their `PostToolUse` hooks format edited Haskell and Cabal files.

Claude Code users must add `claude-hoogle` and the marketplace, then install its Haskell, LSP, Haddock, format, and cabal-gild plugins. Cursor users must expose the same `SKILL.md` files as Agent Skills and register equivalent scripts in `.cursor/hooks.json`; Claude hook manifests are not portable. `AGENTS.md` is canonical; `CLAUDE.md` imports it.

## Build, Test, and Development Commands

Use Cabal’s nix-style workflow; `cabal.project` defines the build plan.

- `cabal build herbrand` — build the library.
- `cabal test herbrand-test` — run the Tasty suite.
- `cabal run cdcl-dry -- -i data/tests/small-01.cnf` — run the CDCL solver on a DIMACS file.
- `cabal bench herbrand-sat-bench` — benchmark SAT implementations.
- `hpack` — regenerate `herbrand.cabal` after every `package.yaml` change.

Build and test one component at a time. Do not use Stack or invoke GHC directly.

### Benchmark concurrency rule

Benchmark executables must remain single-threaded unless the benchmark explicitly measures a multithreaded implementation. Do not add GHC's `-threaded` flag to a benchmark component and do not pass the RTS `-N` flag; either changes the runtime being measured and invalidates comparisons. Record any intentional parallel configuration as a separate benchmark.

## Coding Style & Naming Conventions

Format Haskell with Fourmolu using `fourmolu.yaml` (two-space indentation), and Cabal files with `cabal-gild`. Preserve linear ownership and prefer explicit strictness in solver hot paths. Always use `(<>)`, including for list and string concatenation; never use `(++)`.

Use `UpperCamelCase` for types and modules, `lowerCamelCase` for values, and module-qualified imports where names would be ambiguous.

## Testing Guidelines

Tests use Tasty, Falsify, HUnit, and QuickCheck. Name modules `*Spec.hs` and exported tests `test_*` for `tasty-discover`. Add regression CNFs for solver bugs, compare small inputs with the brute-force solver, and verify returned models. Include focused timing and allocation results for performance changes.

## Commit & Pull Request Guidelines

Follow Conventional Commits with short imperative subjects, for example `fix: correct watched-literal updates` or `perf: reduce trail allocations`. Keep commits narrowly scoped. Every commit must include one valid `Co-authored-by: Name <email>` trailer for each LLM that materially contributed, naming the model used. Never add `Codex-Session:` trailers, session URLs, or other internal metadata.

Pull requests should explain the problem, algorithmic tradeoffs, tests run, and benchmark impact. Link relevant issues and call out dependency or generated-Cabal changes explicitly.
