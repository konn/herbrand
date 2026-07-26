import fs from "node:fs";

if (process.argv.length !== 6) {
  console.error(
    "usage: node analyze-paired.mjs BASELINE.csv CANDIDATE.csv REPORT.json REPORT.md",
  );
  process.exit(2);
}

const [, , baselinePath, candidatePath, jsonPath, markdownPath] = process.argv;
const bootstrapIterations = 100_000;
const confidence = 0.95;
const ucbLimit = 1.02;
const bootstrapSeed = 20_260_726;
const expectedColumns = [
  "case",
  "run",
  "result",
  "gc_mode",
  "allocated_bytes",
  "copied_bytes",
  "max_residency_bytes",
  "mut_elapsed_s",
  "total_elapsed_s",
];
const nonnegativeMetricColumns = [
  "allocated_bytes",
  "copied_bytes",
  "max_residency_bytes",
  "mut_elapsed_s",
];
const expectedResults = new Map([
  ["data/satlib/uf20-91/uf20-01.cnf", "SAT"],
  ["data/satlib/uf100-430/uf100-01.cnf", "SAT"],
  ["data/satlib/flat200-479/flat200-1.cnf", "SAT"],
  ["data/satlib/Bejing/3blocks.cnf", "SAT"],
  ["workspace/tuning-corpus/all-binary-2-unsat.cnf", "UNSAT"],
  ["workspace/tuning-corpus/implication-chain-12-unsat.cnf", "UNSAT"],
  ["workspace/tuning-corpus/php-7-6-unsat.cnf", "UNSAT"],
]);
const expectedGcModes = ["nonmoving", "copying"];
const expectedRuns = Array.from({ length: 21 }, (_, index) => index + 1);
const rowKey = (row) => `${row.case}\0${row.gc_mode}\0${row.run}`;
const expectedKeys = new Set(
  [...expectedResults.keys()].flatMap((input) =>
    expectedGcModes.flatMap((gcMode) =>
      expectedRuns.map((run) => `${input}\0${gcMode}\0${run}`),
    ),
  ),
);

const readCsv = (file, label) => {
  const [header, ...lines] = fs.readFileSync(file, "utf8").trim().split("\n");
  if (header !== expectedColumns.join(",")) {
    throw new Error(`${label} has an unexpected CSV header: ${header}`);
  }
  const rows = [];
  const byKey = new Map();
  for (const [lineIndex, line] of lines.entries()) {
    const values = line.split(",");
    if (values.length !== expectedColumns.length) {
      throw new Error(`${label} row ${lineIndex + 2} is malformed: ${line}`);
    }
    const row = Object.fromEntries(
      values.map((value, index) => [expectedColumns[index], value]),
    );
    const expectedResult = expectedResults.get(row.case);
    if (!expectedResult) {
      throw new Error(`${label} has an unexpected case: ${row.case}`);
    }
    const run = Number(row.run);
    if (!Number.isInteger(run) || run < 1 || run > 21) {
      throw new Error(`${label} has an invalid run number: ${row.run}`);
    }
    if (row.result !== expectedResult) {
      throw new Error(
        `${label} has the wrong result for ${row.case}: ${row.result}`,
      );
    }
    if (row.gc_mode !== "nonmoving" && row.gc_mode !== "copying") {
      throw new Error(`${label} has an invalid GC mode: ${row.gc_mode}`);
    }
    for (const column of nonnegativeMetricColumns) {
      const value = Number(row[column]);
      if (!Number.isFinite(value) || value < 0) {
        throw new Error(
          `${label} has an invalid ${column} value: ${row[column]}`,
        );
      }
    }
    const totalElapsed = Number(row.total_elapsed_s);
    if (!Number.isFinite(totalElapsed) || totalElapsed <= 0) {
      throw new Error(
        `${label} has an invalid total_elapsed_s value: ${row.total_elapsed_s}`,
      );
    }
    const key = rowKey(row);
    if (byKey.has(key)) {
      throw new Error(`${label} has a duplicate row key: ${key}`);
    }
    rows.push(row);
    byKey.set(key, row);
  }
  if (byKey.size !== expectedKeys.size) {
    throw new Error(
      `${label} has ${byKey.size} rows; expected ${expectedKeys.size}`,
    );
  }
  for (const key of expectedKeys) {
    if (!byKey.has(key)) {
      throw new Error(`${label} is missing required row: ${key}`);
    }
  }
  return { rows, byKey };
};

const median = (values) => {
  const sorted = values.toSorted((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 0
    ? (sorted[middle - 1] + sorted[middle]) / 2
    : sorted[middle];
};
const mad = (values) => {
  const center = median(values);
  return median(values.map((value) => Math.abs(value - center)));
};
const geometricMean = (values) =>
  Math.exp(
    values.reduce((total, value) => total + Math.log(value), 0) /
      values.length,
  );
const medianRatio = (candidateValues, baselineValues) => {
  const baselineMedian = median(baselineValues);
  return baselineMedian === 0
    ? null
    : median(candidateValues) / baselineMedian;
};
const quantile = (values, probability) => {
  const sorted = values.toSorted((left, right) => left - right);
  const position = (sorted.length - 1) * probability;
  const lower = Math.floor(position);
  const fraction = position - lower;
  return (
    sorted[lower] +
    fraction *
      (sorted[Math.min(lower + 1, sorted.length - 1)] - sorted[lower])
  );
};
const makeRandom = (seed) => {
  let state = seed >>> 0;
  return () => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) / 0x1_0000_0000;
  };
};
const { rows: baseline, byKey: baselineByKey } = readCsv(
  baselinePath,
  "baseline",
);
const { rows: candidate, byKey: candidateByKey } = readCsv(
  candidatePath,
  "candidate",
);
if (baseline.length !== candidate.length) {
  throw new Error(
    `row count mismatch: baseline=${baseline.length}, candidate=${candidate.length}`,
  );
}
for (const key of baselineByKey.keys()) {
  if (!candidateByKey.has(key)) {
    throw new Error(`candidate is missing baseline row: ${key}`);
  }
}
for (const key of candidateByKey.keys()) {
  if (!baselineByKey.has(key)) {
    throw new Error(`baseline is missing candidate row: ${key}`);
  }
}

const paired = candidate.map((candidateRow) => {
  const baselineRow = baselineByKey.get(rowKey(candidateRow));
  if (!baselineRow || baselineRow.result !== candidateRow.result) {
    throw new Error(`missing or mismatched baseline row: ${rowKey(candidateRow)}`);
  }
  const baselineElapsed = Number(baselineRow.total_elapsed_s);
  const candidateElapsed = Number(candidateRow.total_elapsed_s);
  if (!(baselineElapsed > 0) || !(candidateElapsed > 0)) {
    throw new Error(`non-positive elapsed time: ${rowKey(candidateRow)}`);
  }
  return {
    case: candidateRow.case,
    gcMode: candidateRow.gc_mode,
    run: Number(candidateRow.run),
    result: candidateRow.result,
    baseline: baselineRow,
    candidate: candidateRow,
    elapsedRatio: candidateElapsed / baselineElapsed,
    logElapsedRatio: Math.log(candidateElapsed / baselineElapsed),
  };
});

const strata = new Map();
for (const pair of paired) {
  const key = `${pair.case}\0${pair.gcMode}`;
  strata.set(key, [...(strata.get(key) ?? []), pair]);
}
if (
  strata.size !== 14 ||
  [...strata.values()].some((rows) => rows.length !== 21)
) {
  throw new Error("expected 14 case/GC strata with 21 pairs each");
}

const numberField = (rows, side, field) =>
  rows.map((row) => Number(row[side][field]));
const summaries = [...strata.values()].map((rows) => {
  const baselineElapsed = numberField(rows, "baseline", "total_elapsed_s");
  const candidateElapsed = numberField(rows, "candidate", "total_elapsed_s");
  const baselineAllocated = numberField(rows, "baseline", "allocated_bytes");
  const candidateAllocated = numberField(rows, "candidate", "allocated_bytes");
  const baselineCopied = numberField(rows, "baseline", "copied_bytes");
  const candidateCopied = numberField(rows, "candidate", "copied_bytes");
  const baselineMutation = numberField(rows, "baseline", "mut_elapsed_s");
  const candidateMutation = numberField(rows, "candidate", "mut_elapsed_s");
  const baselineResidency = numberField(
    rows,
    "baseline",
    "max_residency_bytes",
  );
  const candidateResidency = numberField(
    rows,
    "candidate",
    "max_residency_bytes",
  );
  const baselineMedian = median(baselineElapsed);
  const candidateMedian = median(candidateElapsed);
  const baselineMad = mad(baselineElapsed);
  const candidateMad = mad(candidateElapsed);
  const elapsedLimit =
    1.05 * baselineMedian + baselineMad + candidateMad + 0.001;
  return {
    case: rows[0].case,
    gcMode: rows[0].gcMode,
    result: rows[0].result,
    runs: rows.length,
    baselineMedianElapsedSeconds: baselineMedian,
    baselineMadElapsedSeconds: baselineMad,
    candidateMedianElapsedSeconds: candidateMedian,
    candidateMadElapsedSeconds: candidateMad,
    pairedElapsedGeometricMeanRatio: geometricMean(
      rows.map((row) => row.elapsedRatio),
    ),
    baselineMedianMutationSeconds: median(baselineMutation),
    candidateMedianMutationSeconds: median(candidateMutation),
    medianMutationTimeRatio: medianRatio(candidateMutation, baselineMutation),
    baselineMedianAllocatedBytes: median(baselineAllocated),
    candidateMedianAllocatedBytes: median(candidateAllocated),
    medianAllocationRatio: medianRatio(candidateAllocated, baselineAllocated),
    baselineMedianCopiedBytes: median(baselineCopied),
    candidateMedianCopiedBytes: median(candidateCopied),
    medianCopiedRatio: medianRatio(candidateCopied, baselineCopied),
    baselineMedianResidencyBytes: median(baselineResidency),
    candidateMedianResidencyBytes: median(candidateResidency),
    medianResidencyRatio: medianRatio(candidateResidency, baselineResidency),
    elapsedLimitSeconds: elapsedLimit,
    elapsedGatePass: candidateMedian <= elapsedLimit,
  };
});

const aggregate = (label, selectedStrata, seed) => {
  const observedLogs = selectedStrata.flatMap((rows) =>
    rows.map((row) => row.logElapsedRatio),
  );
  const random = makeRandom(seed);
  const bootstrapRatios = [];
  for (let iteration = 0; iteration < bootstrapIterations; iteration += 1) {
    let total = 0;
    let count = 0;
    for (const rows of selectedStrata) {
      for (let draw = 0; draw < rows.length; draw += 1) {
        total +=
          rows[Math.floor(random() * rows.length)].logElapsedRatio;
        count += 1;
      }
    }
    bootstrapRatios.push(Math.exp(total / count));
  }
  const ratio = Math.exp(
    observedLogs.reduce((total, value) => total + value, 0) /
      observedLogs.length,
  );
  const upperConfidenceBound = quantile(bootstrapRatios, confidence);
  return {
    label,
    pairs: observedLogs.length,
    pairedElapsedGeometricMeanRatio: ratio,
    upperConfidenceBound,
    confidence,
    bootstrapIterations,
    bootstrapMethod:
      "percentile bootstrap, resampling paired runs within each case/GC stratum",
    ucbLimit,
    ucbGatePass: upperConfidenceBound <= ucbLimit,
  };
};

const stratumRows = [...strata.values()];
const aggregates = [
  aggregate(
    "nonmoving",
    stratumRows.filter((rows) => rows[0].gcMode === "nonmoving"),
    bootstrapSeed,
  ),
  aggregate(
    "copying",
    stratumRows.filter((rows) => rows[0].gcMode === "copying"),
    bootstrapSeed,
  ),
  aggregate("all", stratumRows, bootstrapSeed),
];
const report = {
  baselinePath,
  candidatePath,
  expectedPairs: 294,
  observedPairs: paired.length,
  bootstrapSeed,
  allResultsMatch: true,
  allPerCaseElapsedGatesPass: summaries.every((row) => row.elapsedGatePass),
  allAggregateUcbGatesPass: aggregates.every((row) => row.ucbGatePass),
  summaries,
  aggregates,
};
fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`);

const format = (value, digits = 4) =>
  value === null ? "n/a" : Number(value).toFixed(digits);
const markdown = [
  "# Pure Borrow paired benchmark",
  "",
  `- Results matched: ${report.allResultsMatch}`,
  `- Per-case elapsed gates: ${summaries.filter((row) => row.elapsedGatePass).length}/${summaries.length}`,
  `- Aggregate UCB gates: ${aggregates.filter((row) => row.ucbGatePass).length}/${aggregates.length}`,
  "",
  "| Aggregate | Pairs | Geomean ratio | 95% UCB | Limit | Pass |",
  "| --- | ---: | ---: | ---: | ---: | :---: |",
  ...aggregates.map(
    (row) =>
      `| ${row.label} | ${row.pairs} | ${format(row.pairedElapsedGeometricMeanRatio)} | ${format(row.upperConfidenceBound)} | ${format(row.ucbLimit)} | ${row.ucbGatePass ? "yes" : "no"} |`,
  ),
  "",
  "| Case | GC | Allocation ratio | Copied ratio | Residency ratio | MUT ratio | Baseline MUT (s) | Candidate MUT (s) | Elapsed ratio | Baseline median (s) | Candidate median (s) | Gate |",
  "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |",
  ...summaries.map(
    (row) =>
      `| ${row.case} | ${row.gcMode} | ${format(row.medianAllocationRatio)} | ${format(row.medianCopiedRatio)} | ${format(row.medianResidencyRatio)} | ${format(row.medianMutationTimeRatio)} | ${format(row.baselineMedianMutationSeconds, 3)} | ${format(row.candidateMedianMutationSeconds, 3)} | ${format(row.pairedElapsedGeometricMeanRatio)} | ${format(row.baselineMedianElapsedSeconds, 3)} | ${format(row.candidateMedianElapsedSeconds, 3)} | ${row.elapsedGatePass ? "yes" : "no"} |`,
  ),
  "",
  `UCB method: ${aggregates[0].bootstrapMethod}; seed ${bootstrapSeed}; ${bootstrapIterations} deterministic resamples.`,
  "",
].join("\n");
fs.writeFileSync(markdownPath, markdown);
console.log(markdown);
