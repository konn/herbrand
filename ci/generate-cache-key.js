module.exports = async ({ core, glob, os, ghc, projects, prefix }) => {
  function build_keys(comps) {
    const fallbacks = comps
      .reduce((accum, cur) => [accum[0].concat([cur])].concat(accum), [[]])
      .slice(1, -1)
      .map((e) => e.concat("").join("-"));

    return { key: comps.join("-"), restore: fallbacks.join("\n") };
  }
  core.info(`os: ${JSON.stringify(os)}`);
  core.info(`ghc: ${JSON.stringify(ghc)}`);
  core.info(`projects: ${JSON.stringify(projects)}`);
  core.info(`prefix: ${JSON.stringify(prefix)}`);

  prefix = prefix == null ? "" : `${prefix}-`;
  core.info(`New prefix: ${JSON.stringify(prefix)}`);
  projects =
    projects == null
      ? ["cabal.project", "cabal.project", "cabal.project.freeze"]
      : projects;
  core.info(`New projects: ${JSON.stringify(projects)}`);
  const project_hash = await glob.hashFiles(...projects);
  core.info(`project_hash: ${JSON.stringify(project_hash)}`);
  core.setOutput("project", project_hash);

  const package_hash = await glob.hashFiles("**/package.yaml", "**/*.cabal");
  core.info(`package_hash: ${JSON.stringify(package_hash)}`);
  core.setOutput("package", package_hash);

  const source_hash = await glob.hashFiles(
    "**/*.hs",
    "**/*.lhs",
    "**/*.hsig",
    "**/*.hs-boot",
    "**/*.c",
    "**/*.h",
    "**/*.chs",
    "**/*.hsc"
  );
  core.info(`source_hash: ${JSON.stringify(source_hash)}`);
  core.setOutput("source", source_hash);

  const store_prefix = `${prefix}store-${os}-${ghc}`;
  core.info(`store_prefix: ${JSON.stringify(store_prefix)}`);
  core.setOutput("store-prefix", store_prefix);
  const store_keys = build_keys([store_prefix, project_hash, package_hash]);
  core.setOutput("store", store_keys.key);
  core.setOutput("store-restore", store_keys.restore);
  core.info(`store: ${JSON.stringify(store)}`);
  core.info(`store-restore: ${JSON.stringify(store_restore)}`);

  const dist_prefix = `${prefix}dist-${os}-${ghc}`;
  core.info(`dist_prefix: ${JSON.stringify(dist_prefix)}`);
  core.setOutput("dist-prefix", dist_prefix);
  const dist_key_comps = [dist_prefix, project_hash, package_hash, source_hash];
  const dist_keys = build_keys(dist_key_comps);
  core.setOutput("dist", dist_keys.key);
  core.setOutput("dist-restore", dist_keys.restore);
  core.info(`dist: ${JSON.stringify(store)}`);
  core.info(`dist-restore: ${JSON.stringify(dist_restore)}`);
};
