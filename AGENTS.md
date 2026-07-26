# Repository Guidelines

## Project Structure & Module Organization

Library modules live in `src/`; SAT solvers are under `src/Logic/Propositional/Classical/SAT/`. Put executables in `app/`, shared helpers in `libs/`, tests in `test/`, benchmarks in `bench/`, and DIMACS fixtures in `data/`.

## Agent Tooling

Use the [`konn/haskell-claude-marketplace`](https://github.com/konn/haskell-claude-marketplace) `haskell` super-skill, HLS diagnostics, Haddock/Hoogle lookup, and format/cabal-gild `PostToolUse` hooks.

Claude Code users should install its Haskell, LSP, Haddock, Hoogle, format, and cabal-gild plugins. Cursor users must expose the same `SKILL.md` files and register equivalent scripts in `.cursor/hooks.json`; Claude hook manifests are not portable. `AGENTS.md` is canonical; `CLAUDE.md` imports it.

## Build, Test, and Development Commands

Use Cabal’s nix-style workflow:

- `cabal build herbrand` — build the library.
- `cabal test herbrand-test` — run the Tasty suite.
- `cabal run cdcl-dry -- -i data/tests/small-01.cnf` — run the CDCL solver on a DIMACS file.
- `cabal bench herbrand-sat-bench` — benchmark SAT implementations.
- `cabal-gild --io herbrand.cabal` — format the package description after every metadata change.

`herbrand.cabal` is the package source of truth; do not recreate `package.yaml` or use Hpack. Build one component at a time. Do not use Stack or invoke GHC directly.

### Benchmark concurrency rule

Keep benchmarks single-threaded unless explicitly measuring parallel code: never add GHC `-threaded` or pass RTS `-N`. Record intentional parallel configurations separately.

Time performance is the primary optimization objective. Treat allocation and residency as diagnostic constraints: prefer a faster implementation over a smaller one when measurements are sound and memory use remains practical.

## Coding Style & Naming Conventions

Format Haskell with Fourmolu using `fourmolu.yaml` (two-space indentation) and Cabal files with `cabal-gild`. Keep component module lists behind `-- cabal-gild: discover` pragmas, using `--include` or `--exclude` for public/internal and driver-module boundaries. Preserve linear ownership and use explicit strictness in hot paths. Always use `(<>)`, never `(++)`.

Use `UpperCamelCase` for types and modules, `lowerCamelCase` for values, and module-qualified imports where names would be ambiguous.

## Testing Guidelines

Tests use Tasty, Falsify, HUnit, and QuickCheck. Name modules `*Spec.hs` and exported tests `test_*`. Add regression CNFs, compare small inputs with brute force, verify returned models, and include timing evidence for performance changes.

## Commit & Pull Request Guidelines

Use narrowly scoped Conventional Commits, for example `perf: reduce trail allocations`. Include one valid `Co-authored-by: Name <email>` trailer per contributing LLM, naming its model. Never add `Codex-Session:`, session URLs, or internal metadata.

Pull requests must explain the problem, tradeoffs, tests, and benchmark impact; link issues and call out dependency or Cabal metadata changes.
