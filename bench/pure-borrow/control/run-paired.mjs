import { spawnSync } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";

if (process.argv.length !== 12) {
  console.error(
    "usage: node run-paired.mjs BASELINE_EXE CANDIDATE_EXE BASELINE_VERIFIER CANDIDATE_VERIFIER PROVENANCE.json BASELINE_PROJECT CANDIDATE_PROJECT BASELINE.csv CANDIDATE.csv MANIFEST.json",
  );
  process.exit(2);
}

const [
  ,
  ,
  baselineExe,
  candidateExe,
  baselineVerifier,
  candidateVerifier,
  provenancePath,
  baselineProject,
  candidateProject,
  baselinePath,
  candidatePath,
  manifestPath,
] = process.argv;
const benchmarkNames = [
  "All.production/propagation/root-chain-4096",
  "All.production/analysis-and-insertion/php-7-6",
];
const repetitions = 3;
const executables = { baseline: baselineExe, candidate: candidateExe };
const verifiers = {
  baseline: baselineVerifier,
  candidate: candidateVerifier,
};
const projectFiles = {
  baseline: baselineProject,
  candidate: candidateProject,
};
const provenance = JSON.parse(fs.readFileSync(provenancePath, "utf8"));
const sourceDirectory = path.dirname(new URL(import.meta.url).pathname);
const harnessPath = path.join(sourceDirectory, "Main.hs");
const verifierSourcePath = path.join(sourceDirectory, "Verify.hs");
const workloadsPath = path.join(sourceDirectory, "Workloads.hs");
const analyzerPath = path.join(sourceDirectory, "analyze-paired.mjs");
const packagePath = path.join(
  sourceDirectory,
  "pure-borrow-production-controls.cabal",
);
const header = "run,name,mean_ps,two_stdev_ps\n";
const rows = { baseline: [], candidate: [] };

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

function validateSource(side) {
  const source = provenance[side];
  if (
    typeof source !== "object" ||
    !/^[0-9a-f]{40}$/.test(source.commit) ||
    !/^[0-9a-f]{40}$/.test(source.tree) ||
    source.cleanWorktree !== true ||
    typeof source.controlBuildCommand !== "string" ||
    source.controlBuildCommand.length === 0 ||
    typeof source.controlVerificationBuildCommand !== "string" ||
    source.controlVerificationBuildCommand.length === 0 ||
    source.controlProjectPath !== projectFiles[side] ||
    source.controlProjectSha256 !== sha256(projectFiles[side]) ||
    typeof source.sourceDirectory !== "string" ||
    !path.isAbsolute(source.sourceDirectory)
  ) {
    throw new Error(`invalid ${side} control provenance`);
  }
  const actualCommit = capture("git", ["rev-parse", "HEAD"], {
    cwd: source.sourceDirectory,
  });
  const actualTree = capture("git", ["rev-parse", "HEAD^{tree}"], {
    cwd: source.sourceDirectory,
  });
  const status = capture(
    "git",
    ["status", "--porcelain=v1", "--untracked-files=all"],
    { cwd: source.sourceDirectory },
  );
  if (
    actualCommit !== source.commit ||
    actualTree !== source.tree ||
    status.length !== 0
  ) {
    throw new Error(
      `${side} source checkout does not match its clean commit/tree provenance`,
    );
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
for (const side of ["baseline", "candidate"]) {
  if (!fs.existsSync(executables[side])) {
    throw new Error(`${side} executable does not exist: ${executables[side]}`);
  }
  if (!fs.existsSync(verifiers[side])) {
    throw new Error(`${side} verifier does not exist: ${verifiers[side]}`);
  }
  if (!path.isAbsolute(projectFiles[side])) {
    throw new Error(`${side} control project path is not absolute`);
  }
  if (!fs.existsSync(projectFiles[side])) {
    throw new Error(`${side} control project does not exist`);
  }
  validateSource(side);
  const project = fs.readFileSync(projectFiles[side], "utf8");
  const herbrandPackage = path.join(
    provenance[side].sourceDirectory,
    "herbrand.cabal",
  );
  if (!project.includes(herbrandPackage) || !project.includes(packagePath)) {
    throw new Error(
      `${side} control project does not select the declared Herbrand source and tracked control package`,
    );
  }
}
for (const file of [
  harnessPath,
  verifierSourcePath,
  workloadsPath,
  analyzerPath,
  packagePath,
]) {
  if (!fs.existsSync(file)) {
    throw new Error(`control source does not exist: ${file}`);
  }
}

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
  throw new Error("captured control toolchain differs from provenance");
}

const temporaryDirectory = fs.mkdtempSync(
  path.join(os.tmpdir(), "herbrand-production-controls-"),
);
const manifest = {
  provenance,
  capturedToolchain,
  hostRuntime: {
    node: process.version,
    platform: process.platform,
    architecture: process.arch,
  },
  protocol: {
    benchmarkNames,
    pairedFreshProcessRuns: repetitions,
    timeoutSecondsPerProcess: 120,
    order:
      "odd runs baseline/candidate; even runs candidate/baseline; both benchmarks measured by tasty-bench in every fresh process",
    tastyBenchArguments: [
      "--stdev",
      "2",
      "--timeout",
      "30s",
      "--time-mode",
      "wall",
      "--num-threads",
      "1",
      "--color",
      "never",
      "--ansi-tricks",
      "false",
    ],
  },
  provenanceSha256: sha256(provenancePath),
  runnerSha256: sha256(new URL(import.meta.url)),
  analyzerSha256: sha256(analyzerPath),
  harnessSha256: sha256(harnessPath),
  verifierSourceSha256: sha256(verifierSourcePath),
  workloadsSha256: sha256(workloadsPath),
  packageSha256: sha256(packagePath),
  projects: Object.fromEntries(
    Object.entries(projectFiles).map(([side, file]) => [
      side,
      { path: file, sha256: sha256(file) },
    ]),
  ),
  executables: {
    baseline: { path: baselineExe, sha256: sha256(baselineExe) },
    candidate: { path: candidateExe, sha256: sha256(candidateExe) },
  },
  verifiers: {
    baseline: { path: baselineVerifier, sha256: sha256(baselineVerifier) },
    candidate: { path: candidateVerifier, sha256: sha256(candidateVerifier) },
  },
  complete: false,
};

function writeManifest() {
  fs.writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
}

function parseTastyCsv(file, side, run) {
  const [csvHeader, ...lines] = fs
    .readFileSync(file, "utf8")
    .trim()
    .split("\n");
  if (csvHeader !== "Name,Mean (ps),2*Stdev (ps)") {
    throw new Error(`${side} run ${run} has unexpected CSV header: ${csvHeader}`);
  }
  if (lines.length !== benchmarkNames.length) {
    throw new Error(
      `${side} run ${run} has ${lines.length} rows; expected ${benchmarkNames.length}`,
    );
  }
  const seen = new Set();
  for (const line of lines) {
    const values = line.split(",");
    if (values.length !== 3 || !benchmarkNames.includes(values[0])) {
      throw new Error(`${side} run ${run} has malformed row: ${line}`);
    }
    if (seen.has(values[0])) {
      throw new Error(`${side} run ${run} repeats benchmark: ${values[0]}`);
    }
    for (const value of values.slice(1)) {
      const number = Number(value);
      if (!Number.isFinite(number) || number <= 0) {
        throw new Error(`${side} run ${run} has invalid timing: ${line}`);
      }
    }
    seen.add(values[0]);
    rows[side].push(`${run},${line}`);
  }
}

function flush() {
  fs.writeFileSync(baselinePath, header + rows.baseline.join("\n") + "\n");
  fs.writeFileSync(candidatePath, header + rows.candidate.join("\n") + "\n");
}

function runOne(side, run) {
  const csvPath = path.join(temporaryDirectory, `${side}-${run}.csv`);
  const result = spawnSync(
    executables[side],
    [
      "--stdev",
      "2",
      "--timeout",
      "30s",
      "--time-mode",
      "wall",
      "--csv",
      csvPath,
      "--num-threads",
      "1",
      "--color",
      "never",
      "--ansi-tricks",
      "false",
    ],
    {
      encoding: "utf8",
      maxBuffer: 16 * 1024 * 1024,
      timeout: 120_000,
    },
  );
  if (result.error?.code === "ETIMEDOUT") {
    throw new Error(`${side} control run ${run} timed out`);
  }
  if (result.status !== 0) {
    throw new Error(
      `${side} control run ${run} failed:\n${result.stdout}\n${result.stderr}`,
    );
  }
  parseTastyCsv(csvPath, side, run);
}

writeManifest();
try {
  const verifierOutputs = Object.fromEntries(
    ["baseline", "candidate"].map((side) => [
      side,
      capture(verifiers[side], [], { timeout: 120_000 }),
    ]),
  );
  if (verifierOutputs.baseline !== verifierOutputs.candidate) {
    throw new Error(
      `baseline and candidate trajectory transcripts differ:\n--- baseline ---\n${verifierOutputs.baseline}\n--- candidate ---\n${verifierOutputs.candidate}`,
    );
  }
  manifest.verifierOutputs = Object.fromEntries(
    Object.entries(verifierOutputs).map(([side, output]) => [
      side,
      {
        stdout: output,
        sha256: crypto.createHash("sha256").update(output).digest("hex"),
      },
    ]),
  );
  writeManifest();
  for (let run = 1; run <= repetitions; run += 1) {
    const order =
      run % 2 === 0
        ? ["candidate", "baseline"]
        : ["baseline", "candidate"];
    for (const side of order) {
      runOne(side, run);
    }
    flush();
    console.log(`production controls ${run}/${repetitions}`);
  }
  manifest.outputs = {
    baseline: { path: baselinePath, sha256: sha256(baselinePath) },
    candidate: { path: candidatePath, sha256: sha256(candidatePath) },
  };
  manifest.complete = true;
  writeManifest();
} finally {
  fs.rmSync(temporaryDirectory, { recursive: true, force: true });
}
