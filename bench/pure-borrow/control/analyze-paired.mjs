import fs from "node:fs";

if (process.argv.length !== 6) {
  console.error(
    "usage: node analyze-paired.mjs BASELINE.csv CANDIDATE.csv REPORT.json REPORT.md",
  );
  process.exit(2);
}

const [, , baselinePath, candidatePath, jsonPath, markdownPath] = process.argv;
const benchmarkNames = [
  "All.production/propagation/root-chain-4096",
  "All.production/analysis-and-insertion/php-7-6",
];
const repetitions = [1, 2, 3];
const expectedHeader = "run,name,mean_ps,two_stdev_ps";
const expectedKeys = new Set(
  repetitions.flatMap((run) =>
    benchmarkNames.map((name) => `${run}\0${name}`),
  ),
);

function readCsv(file, label) {
  const [header, ...lines] = fs.readFileSync(file, "utf8").trim().split("\n");
  if (header !== expectedHeader) {
    throw new Error(`${label} has unexpected CSV header: ${header}`);
  }
  const byKey = new Map();
  for (const line of lines) {
    const [runText, name, meanText, stdevText] = line.split(",");
    const run = Number(runText);
    const mean = Number(meanText);
    const twoStdev = Number(stdevText);
    const key = `${run}\0${name}`;
    if (
      !repetitions.includes(run) ||
      !benchmarkNames.includes(name) ||
      !Number.isFinite(mean) ||
      mean <= 0 ||
      !Number.isFinite(twoStdev) ||
      twoStdev <= 0 ||
      byKey.has(key)
    ) {
      throw new Error(`${label} has invalid row: ${line}`);
    }
    byKey.set(key, { run, name, mean, twoStdev });
  }
  if (byKey.size !== expectedKeys.size) {
    throw new Error(
      `${label} has ${byKey.size} rows; expected ${expectedKeys.size}`,
    );
  }
  for (const key of expectedKeys) {
    if (!byKey.has(key)) {
      throw new Error(`${label} is missing row: ${key}`);
    }
  }
  return byKey;
}

const median = (values) => {
  const sorted = values.toSorted((left, right) => left - right);
  return sorted[Math.floor(sorted.length / 2)];
};
const geometricMean = (values) =>
  Math.exp(
    values.reduce((total, value) => total + Math.log(value), 0) /
      values.length,
  );
const baseline = readCsv(baselinePath, "baseline");
const candidate = readCsv(candidatePath, "candidate");
const summaries = benchmarkNames.map((name) => {
  const pairs = repetitions.map((run) => {
    const baselineRow = baseline.get(`${run}\0${name}`);
    const candidateRow = candidate.get(`${run}\0${name}`);
    return {
      run,
      baselineMeanPicoseconds: baselineRow.mean,
      candidateMeanPicoseconds: candidateRow.mean,
      candidateBaselineRatio: candidateRow.mean / baselineRow.mean,
    };
  });
  return {
    name,
    pairs,
    baselineMedianPicoseconds: median(
      pairs.map((pair) => pair.baselineMeanPicoseconds),
    ),
    candidateMedianPicoseconds: median(
      pairs.map((pair) => pair.candidateMeanPicoseconds),
    ),
    pairedGeometricMeanRatio: geometricMean(
      pairs.map((pair) => pair.candidateBaselineRatio),
    ),
  };
});
const report = {
  protocol:
    "diagnostic focused production control; 3 alternating fresh-process pairs; not an acceptance gate",
  summaries,
  combinedPairedGeometricMeanRatio: geometricMean(
    summaries.flatMap((summary) =>
      summary.pairs.map((pair) => pair.candidateBaselineRatio),
    ),
  ),
};

fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`);
const markdown = [
  "# Focused production-control comparison",
  "",
  "Diagnostic only; the 294-pair whole-solver campaign is the acceptance benchmark.",
  "",
  "| workload | baseline median | candidate median | paired candidate/baseline geomean |",
  "| --- | ---: | ---: | ---: |",
  ...summaries.map(
    (summary) =>
      `| ${summary.name} | ${(summary.baselineMedianPicoseconds / 1e9).toFixed(3)} ms | ${(summary.candidateMedianPicoseconds / 1e9).toFixed(3)} ms | ${summary.pairedGeometricMeanRatio.toFixed(4)}x |`,
  ),
  "",
  `Combined equal-observation geomean: ${report.combinedPairedGeometricMeanRatio.toFixed(4)}x.`,
  "",
].join("\n");
fs.writeFileSync(markdownPath, markdown);
