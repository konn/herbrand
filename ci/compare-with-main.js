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
    const csvArt = artifacts.find((art) => art.name == `artifacts`);
    if (csvArt !== undefined) {
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
      const body = await response.buffer();
      const base_art_dir = `base-artifacts-${base_commit.slice(0, 7)}`;
      const base_csv_dir = `base-csv-${base_commit.slice(0, 7)}`;
      io.mkdirP(base_art_dir);
      io.mkdirP(base_csv_dir);
      const zip_path = `${base_art_dir}/artifacts.zip`;
      fs.writeFileSync(zip_path, body);
      await exec.exec("unzip", [zip_path, "-d", base_art_dir]);
      await exec.exec("tar", [
        "xvf",
        `${base_art_dir}/artifacts.tar.zst`,
        `--directory=${base_art_dir}`,
      ]);

      base_csv_path = `${base_csv_dir}/${bench_name}.csv`;
      const base_svg_path = `${base_csv_dir}/${bench_name}.svg`;
      core.info("Running the original benchmark first...");
      // FIXME: Checkout data directory for completeness
      await exec.exec(
        `${base_art_dir}/artifacts/benchs/${bench_name}`,
        ["-j1", "--csv", base_csv_path, "--svg", base_svg_path],
        { ignoreReturnCode: true }
      );
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

  const bench_args = ["-j1"];
  const exe = `./artifacts/benchs/${bench_name}`;
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
