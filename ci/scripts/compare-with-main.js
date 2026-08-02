module.exports = async ({
  core,
  github,
  fetch,
  io,
  exec,
  context,
  bench_name,
  threshold,
  inputs,
}) => {
  const fs = require("fs");

  // Keep older binaries from rediscovering fixtures added for the test suite.
  const benchmarkPatterns = {
    "herbrand-sat-bench":
      "($0 ~ /CDCL/) && ($0 !~ /uf20-91-full/) && " +
      "(($0 ~ /huge/) || ($0 ~ /Sudoku/) || ($0 ~ /Bejing/) || " +
      "($0 ~ /flat200-479/) || ($0 ~ /uf100-430/) || ($0 ~ /uf20-91/))",
  };
  const benchmarkPattern = benchmarkPatterns[bench_name];

  let target_repo;
  let target_branch;
  let target_sha;
  let base_csv_path;
  const current_run_id = context.runId;
  let source_branch;
  if (context.eventName == "pull_request") {
    const pull = context.payload.pull_request;
    source_branch = pull.head.ref;
    target_repo = pull.base.repo;
    context.payload.repository.target_branch = pull.base.ref;
    target_sha = pull.base.sha;
  } else if (
    context.eventName == "workflow_dispatch" &&
    inputs.baseline != ""
  ) {
    source_branch = context.ref;
    target_sha = inputs.baseline;
    target_repo = context.payload.repository;
  } else {
    source_branch = "main";
    target_branch = context.ref;
    target_repo = context.payload.repository;
  }
  const {
    owner: { login: target_owner },
    name: target_repo_name,
  } = target_repo;
  let filter = {
    owner: target_owner,
    repo: target_repo_name,
    workflow_id: "haskell.yml",
    branch: target_branch,
    sort: "created_at",
  };
  if (target_sha !== undefined) {
    filter.head_sha = target_sha;
  }
  // A baseline is a nice-to-have, not a requirement. Build artifacts are
  // uploaded with `retention-days: 1`, so any run more than a day after the
  // target's build gets `HttpError: Artifact has expired` here. Treat every
  // failure in this block as "no baseline available" and fall through to
  // benchmarking the current build alone, so the job still produces a CSV,
  // an SVG and a report showing the current results.
  try {
    const {
      data: { total_count: run_count, workflow_runs: runs },
    } = await github.rest.actions.listWorkflowRuns(filter);
    if (run_count != 0) {
      const target_run = runs[0];
      const target_run_id = target_run.id;
      core.info(`Comparing results with: Run #${target_run_id}`);
      const {
        data: { artifacts },
      } = await github.request(runs[0].artifacts_url);
      const csvArt = artifacts.find(
        (art) => art.name == "artifact-ghc-9.12.4"
      );
      if (csvArt === undefined) {
        core.info("No baseline artifact found on the target run.");
      } else if (csvArt.expired) {
        // Reported by the API before we try to download, so prefer this to
        // waiting for downloadArtifact to throw.
        core.info(`Baseline artifact ${csvArt.id} has expired.`);
      } else {
        core.info(`Downloading artifact: ${csvArt.id}`);
        const { url } = await github.rest.actions.downloadArtifact({
          owner: target_owner,
          repo: target_repo_name,
          artifact_id: csvArt.id,
          archive_format: "zip",
        });
        core.info(`Downloading from: ${url}`);
        const base_commit = target_run.head_sha;
        const response = await fetch(url, { compress: true });
        const body = Buffer.from(await response.arrayBuffer());
        const base_art_dir = `base-artifacts-${base_commit.slice(0, 7)}`;
        const base_csv_dir = `base-csv-${base_commit.slice(0, 7)}`;
        io.mkdirP(base_art_dir);
        io.mkdirP(base_csv_dir);
        const zip_path = `${base_art_dir}/artifacts.zip`;
        fs.writeFileSync(zip_path, body);
        await exec.exec("unzip", [zip_path, "-d", base_art_dir]);
        await exec.exec("tar", [
          "xvf",
          `${base_art_dir}/artifact-ghc-9.12.4.tar.zst`,
          `--directory=${base_art_dir}`,
        ]);

        const candidate_csv_path = `${base_csv_dir}/${bench_name}.csv`;
        const base_svg_path = `${base_csv_dir}/${bench_name}.svg`;
        core.info("Running the original benchmark first...");
        const base_args = [
          "-j1",
          "--csv",
          candidate_csv_path,
          "--svg",
          base_svg_path,
        ];
        if (benchmarkPattern !== undefined) {
          base_args.push("--pattern", benchmarkPattern);
        }
        await exec.exec(
          `${base_art_dir}/artifact-ghc-9.12.4/benchs/${bench_name}`,
          base_args,
          { ignoreReturnCode: true }
        );
        // The baseline binary runs with ignoreReturnCode, so verify it really
        // produced a CSV. Passing --baseline a missing path would fail the
        // current benchmark too.
        if (!fs.existsSync(candidate_csv_path)) {
          throw new Error(
            `baseline binary produced no CSV at ${candidate_csv_path}`
          );
        }
        base_csv_path = candidate_csv_path;
        core.setOutput("baseline-csv", base_csv_path);

        core.info(`Original CSV written to: ${base_csv_path}`);
        const commit = (
          await github.rest.git.getCommit({
            owner: target_owner,
            repo: target_repo_name,
            commit_sha: base_commit,
          })
        ).data;
        const baseline_desc = `${target_run.head_sha.slice(0, 7)} (${
          target_run.head_branch
        }): ${commit.message}`;
        core.setOutput("baseline-desc", baseline_desc);
      }
    }
  } catch (error) {
    core.warning(
      `No baseline comparison: ${error.message}. ` +
        "Reporting the current results only."
    );
    base_csv_path = undefined;
  }

  // Leave both outputs defined-but-empty when there is no baseline: the
  // "Generate Report" step gates its --baseline flags on `[[ -n ... ]]`.
  if (base_csv_path === undefined) {
    core.setOutput("baseline-csv", "");
    core.setOutput("baseline-desc", "");
  }

  const bench_args = ["-j1"];
  const exe = `./artifact-ghc-9.12.4/benchs/${bench_name}`;
  if (benchmarkPattern !== undefined) {
    bench_args.push("--pattern", benchmarkPattern);
  }
  if (base_csv_path !== undefined) {
    exec.exec("head", ["-n", 5, base_csv_path]);
    core.info(`Taking benchmark comparing with ${base_csv_path}`);
    bench_args.push("--baseline", base_csv_path);
  }
  if (threshold != undefined && threshold > 0) {
    bench_args.push("--fail-if-slower", threshold);
  }
  core.info(`Executing: ${exe} ${bench_args.join(" ")}`);
  await exec.exec(exe, bench_args);
};
