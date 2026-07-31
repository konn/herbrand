import { spawnSync } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";

if (process.argv.length !== 10) {
  console.error(
    "usage: node run-paired.mjs REPO_ROOT BASELINE_EXE CANDIDATE_EXE PROVENANCE.json ANALYZER.mjs BASELINE.csv CANDIDATE.csv MANIFEST.json",
  );
  process.exit(2);
}

const [
  ,
  ,
  repoRoot,
  baselineExe,
  candidateExe,
  provenancePath,
  analyzerPath,
  baselinePath,
  candidatePath,
  manifestPath,
] = process.argv;
const expectedResults = new Map([
  ["data/satlib/uf20-91/uf20-01.cnf", "SAT"],
  ["data/satlib/uf100-430/uf100-01.cnf", "SAT"],
  ["data/satlib/flat200-479/flat200-1.cnf", "SAT"],
  ["data/satlib/Bejing/3blocks.cnf", "SAT"],
  ["workspace/tuning-corpus/all-binary-2-unsat.cnf", "UNSAT"],
  ["workspace/tuning-corpus/implication-chain-12-unsat.cnf", "UNSAT"],
  ["workspace/tuning-corpus/php-7-6-unsat.cnf", "UNSAT"],
]);
const cases = [...expectedResults.keys()];
const gcModes = [
  ["nonmoving", "--nonmoving-gc"],
  ["copying", "--copying-gc"],
];
const header =
  "case,run,result,gc_mode,allocated_bytes,copied_bytes,max_residency_bytes,mut_elapsed_s,total_elapsed_s\n";
const pairedRunsPerStratum = 32;
const rows = { baseline: [], candidate: [] };
const executables = { baseline: baselineExe, candidate: candidateExe };
const provenance = JSON.parse(fs.readFileSync(provenancePath, "utf8"));

const generatedCases = new Map([
  [
    "workspace/tuning-corpus/all-binary-2-unsat.cnf",
    [
      "c All four binary clauses over two variables",
      "p cnf 2 4",
      "1 2 0",
      "1 -2 0",
      "-1 2 0",
      "-1 -2 0",
      "",
    ].join("\n"),
  ],
  [
    "workspace/tuning-corpus/implication-chain-12-unsat.cnf",
    [
      "c Root implication chain ending in a contradiction",
      "p cnf 12 13",
      "1 0",
      ...Array.from({ length: 11 }, (_, index) =>
        `${-(index + 1)} ${index + 2} 0`,
      ),
      "-12 0",
      "",
    ].join("\n"),
  ],
  [
    "workspace/tuning-corpus/php-7-6-unsat.cnf",
    pigeonholeCnf(7, 6),
  ],
]);

function pigeonholeCnf(pigeons, holes) {
  const clauses = [];
  for (let pigeon = 0; pigeon < pigeons; pigeon += 1) {
    clauses.push(
      Array.from(
        { length: holes },
        (_, hole) => pigeon * holes + hole + 1,
      ),
    );
  }
  for (let hole = 0; hole < holes; hole += 1) {
    for (let first = 0; first < pigeons; first += 1) {
      for (let second = first + 1; second < pigeons; second += 1) {
        clauses.push([
          -(first * holes + hole + 1),
          -(second * holes + hole + 1),
        ]);
      }
    }
  }
  return [
    `c PHP(${pigeons},${holes}): seven pigeons, six holes`,
    `p cnf ${pigeons * holes} ${clauses.length}`,
    ...clauses.map((clause) => `${clause.join(" ")} 0`),
    "",
  ].join("\n");
}

const sha256 = (file) =>
  crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex");

function capture(command, args, options = {}) {
  const result = spawnSync(command, args, {
    encoding: "utf8",
    ...options,
  });
  if (result.status !== 0) {
    throw new Error(
      `${command} ${args.join(" ")} failed:\n${result.stdout}\n${result.stderr}`,
    );
  }
  return result.stdout.trim();
}

const sha256Text = (value) =>
  crypto.createHash("sha256").update(value).digest("hex");

function validateSource(side) {
  const source = provenance[side];
  if (
    typeof source !== "object" ||
    !/^[0-9a-f]{40}$/.test(source.commit) ||
    !/^[0-9a-f]{40}$/.test(source.tree) ||
    typeof source.cleanWorktree !== "boolean" ||
    typeof source.buildCommand !== "string" ||
    source.buildCommand.length === 0 ||
    typeof source.sourceDirectory !== "string" ||
    !path.isAbsolute(source.sourceDirectory)
  ) {
    throw new Error(`invalid ${side} provenance`);
  }
  const actualCommit = capture(
    "git",
    ["rev-parse", "HEAD"],
    { cwd: source.sourceDirectory },
  );
  const actualTree = capture(
    "git",
    ["rev-parse", "HEAD^{tree}"],
    { cwd: source.sourceDirectory },
  );
  const status = capture(
    "git",
    ["status", "--porcelain=v1", "--untracked-files=all"],
    { cwd: source.sourceDirectory },
  );
  if (actualCommit !== source.commit || actualTree !== source.tree) {
    throw new Error(
      `${side} source checkout does not match its commit/tree provenance`,
    );
  }
  if (source.cleanWorktree) {
    if (status.length !== 0) {
      throw new Error(`${side} source checkout is not clean`);
    }
    return;
  }
  const patch = capture("git", ["diff", "--binary", "HEAD"], {
    cwd: source.sourceDirectory,
  });
  if (
    !/^[0-9a-f]{64}$/.test(source.statusSha256 ?? "") ||
    !/^[0-9a-f]{64}$/.test(source.patchSha256 ?? "") ||
    source.statusSha256 !== sha256Text(status) ||
    source.patchSha256 !== sha256Text(patch) ||
    typeof source.untrackedFiles !== "object" ||
    source.untrackedFiles === null
  ) {
    throw new Error(`${side} dirty-source provenance does not match`);
  }
  for (const [relative, expectedSha256] of Object.entries(
    source.untrackedFiles,
  )) {
    const absolute = path.join(source.sourceDirectory, relative);
    if (
      !/^[0-9a-f]{64}$/.test(expectedSha256) ||
      !fs.existsSync(absolute) ||
      sha256(absolute) !== expectedSha256
    ) {
      throw new Error(`${side} untracked source differs: ${relative}`);
    }
  }
}

if (
  typeof provenance.toolchain !== "object" ||
  typeof provenance.toolchain.ghcExecutable !== "string" ||
  !path.isAbsolute(provenance.toolchain.ghcExecutable) ||
  typeof provenance.toolchain.cabalExecutable !== "string" ||
  !path.isAbsolute(provenance.toolchain.cabalExecutable) ||
  provenance.toolchain.optimization !== "-O2" ||
  provenance.toolchain.concurrency !==
    "single-threaded; no -threaded or RTS -N"
) {
  throw new Error("invalid toolchain/optimization/concurrency provenance");
}
for (const executable of [
  provenance.toolchain.ghcExecutable,
  provenance.toolchain.cabalExecutable,
]) {
  if (!fs.existsSync(executable)) {
    throw new Error(`toolchain executable does not exist: ${executable}`);
  }
}
validateSource("baseline");
validateSource("candidate");

const capturedToolchain = {
  ghc: capture(provenance.toolchain.ghcExecutable, ["--numeric-version"]),
  cabal: capture(provenance.toolchain.cabalExecutable, ["--numeric-version"]),
  ghcExecutable: provenance.toolchain.ghcExecutable,
  ghcExecutableSha256: sha256(provenance.toolchain.ghcExecutable),
  cabalExecutable: provenance.toolchain.cabalExecutable,
  cabalExecutableSha256: sha256(provenance.toolchain.cabalExecutable),
  optimization: provenance.toolchain.optimization,
  concurrency: provenance.toolchain.concurrency,
};
if (
  capturedToolchain.ghc !== provenance.toolchain.ghc ||
  capturedToolchain.cabal !== provenance.toolchain.cabal
) {
  throw new Error(
    `toolchain mismatch: expected ${JSON.stringify(provenance.toolchain)}, captured ${JSON.stringify(capturedToolchain)}`,
  );
}

for (const [input, contents] of generatedCases) {
  const absolute = path.join(repoRoot, input);
  fs.mkdirSync(path.dirname(absolute), { recursive: true });
  if (!fs.existsSync(absolute)) {
    fs.writeFileSync(absolute, contents);
  } else if (fs.readFileSync(absolute, "utf8") !== contents) {
    throw new Error(`generated fixture differs from expected contents: ${input}`);
  }
}

for (const executable of Object.values(executables)) {
  if (!fs.existsSync(executable)) {
    throw new Error(`executable does not exist: ${executable}`);
  }
}
if (!fs.existsSync(analyzerPath)) {
  throw new Error(`analyzer does not exist: ${analyzerPath}`);
}
for (const input of cases) {
  if (!fs.existsSync(path.join(repoRoot, input))) {
    throw new Error(`input does not exist: ${input}`);
  }
}

const manifest = {
  provenance,
  capturedToolchain,
  hostRuntime: {
    node: process.version,
    platform: process.platform,
    architecture: process.arch,
  },
  protocol: {
    cases,
    collectors: Object.fromEntries(gcModes),
    warmupRunsPerStratum: 1,
    pairedRunsPerStratum,
    timeoutSecondsPerObservation: 120,
    order:
      "odd runs baseline/candidate; even runs candidate/baseline; fresh process per observation",
    rtsMetrics:
      "allocated bytes, copied bytes, maximum residency, elapsed MUT, elapsed total",
  },
  provenanceSha256: sha256(provenancePath),
  runnerSha256: sha256(new URL(import.meta.url)),
  analyzerSha256: sha256(analyzerPath),
  executables: {
    baseline: { path: baselineExe, sha256: sha256(baselineExe) },
    candidate: { path: candidateExe, sha256: sha256(candidateExe) },
  },
  fixtures: Object.fromEntries(
    cases.map((input) => [
      input,
      sha256(path.join(repoRoot, input)),
    ]),
  ),
  complete: false,
};

function writeManifest() {
  fs.writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
}

writeManifest();

function metric(pattern, text, label) {
  const match = text.match(pattern);
  if (!match) {
    throw new Error(`missing ${label} in RTS output:\n${text}`);
  }
  return match[1].replaceAll(",", "");
}

function runOne(side, input, run, gcMode, gcFlag) {
  const result = spawnSync(
    executables[side],
    ["-i", input, "+RTS", gcFlag, "-s", "-RTS"],
    {
      cwd: repoRoot,
      encoding: "utf8",
      maxBuffer: 16 * 1024 * 1024,
      timeout: 120_000,
    },
  );
  if (result.error?.code === "ETIMEDOUT") {
    throw new Error(
      `${side} timed out for ${input} (${gcMode}, run ${run})`,
    );
  }
  if (result.status !== 0) {
    throw new Error(
      `${side} failed for ${input} (${gcMode}, run ${run}):\n${result.stdout}\n${result.stderr}`,
    );
  }
  const answer = /Satisfiable/m.test(result.stdout)
    ? "SAT"
    : /Unsat|Unsatisfiable/m.test(result.stdout)
      ? "UNSAT"
      : null;
  if (!answer) {
    throw new Error(`missing SAT result:\n${result.stdout}`);
  }
  if (answer !== expectedResults.get(input)) {
    throw new Error(
      `${side} returned ${answer} for ${input}; expected ${expectedResults.get(input)}`,
    );
  }
  const stats = result.stderr;
  rows[side].push(
    [
      input,
      run,
      answer,
      gcMode,
      metric(/^\s*([\d,]+) bytes allocated in the heap/m, stats, "allocation"),
      metric(/^\s*([\d,]+) bytes copied during GC/m, stats, "copied bytes"),
      metric(
        /^\s*([\d,]+) bytes maximum residency/m,
        stats,
        "maximum residency",
      ),
      metric(
        /^\s*MUT\s+time\s+[\d.]+s\s+\(\s*([\d.]+)s elapsed\)/m,
        stats,
        "MUT elapsed",
      ),
      metric(
        /^\s*Total\s+time\s+[\d.]+s\s+\(\s*([\d.]+)s elapsed\)/m,
        stats,
        "total elapsed",
      ),
    ].join(","),
  );
}

function flush() {
  fs.writeFileSync(baselinePath, header + rows.baseline.join("\n") + "\n");
  fs.writeFileSync(candidatePath, header + rows.candidate.join("\n") + "\n");
}

for (const [gcMode, gcFlag] of gcModes) {
  for (const input of cases) {
    runOne("baseline", input, 0, gcMode, gcFlag);
    runOne("candidate", input, 0, gcMode, gcFlag);
    rows.baseline.pop();
    rows.candidate.pop();
    for (let run = 1; run <= pairedRunsPerStratum; run += 1) {
      const order =
        run % 2 === 0
          ? ["candidate", "baseline"]
          : ["baseline", "candidate"];
      for (const side of order) {
        runOne(side, input, run, gcMode, gcFlag);
      }
      flush();
      console.log(
        `${gcMode} ${input} ${run}/${pairedRunsPerStratum}`,
      );
    }
  }
}

flush();
manifest.artifacts = {
  baselineRawCsvSha256: sha256(baselinePath),
  candidateRawCsvSha256: sha256(candidatePath),
};
manifest.complete = true;
writeManifest();
