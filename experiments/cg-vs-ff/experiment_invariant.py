#! /usr/bin/env python

import os
import shutil

import project


REPO = project.get_repo_base()
BENCHMARKS_DIR = os.environ["DOWNWARD_BENCHMARKS"]
SCP_LOGIN = "myname@myserver.com"
REMOTE_REPOS_DIR = "/infai/seipp/projects" # updated
# If REVISION_CACHE is None, the default ./data/revision-cache is used.
REVISION_CACHE = os.environ.get("DOWNWARD_REVISION_CACHE")
if project.REMOTE:
    SUITE = project.SUITE_OPTIMAL_STRIPS_WIHTOUT_STORAGE # remove task where objects with either are present.
    # Remove spider --> vampire has problem with variable with different types for two predicates
    ENV = project.BaselSlurmEnvironment(email="my.name@myhost.ch")
else:
    #SUITE = ["depot:p01.pddl"] # project.SUITE_OPTIMAL_STRIPS
    SUITE = ["depot:p01.pddl", "grid:prob01.pddl", "gripper:prob01.pddl", "blocks:probBLOCKS-4-0.pddl", "woodworking-opt08-strips:p01.pddl"]
    ENV = project.LocalEnvironment(processes=1)

CONFIGS = [
    ("all_actions", []),
    ("limited_grounding", ["--translate-options", "--limited-grounding"])
]
BUILD_OPTIONS = []
DRIVER_OPTIONS = ["--overall-time-limit", "5m", "--translate"]
REVS = [
    ("main", "main"),
]
ATTRIBUTES = [
    "error",
    "run_dir",
    "action_length",
    "translator_time_computing_schematic_group",
    # "search_start_time",
    # "search_start_memory",
    # "total_time",
    # "h_values",
    # "coverage",
    # "expansions",
    # "memory",
    # project.EVALUATIONS_PER_TIME,
]

exp = project.FastDownwardExperiment(environment=ENV, revision_cache=REVISION_CACHE)
for config_nick, config in CONFIGS:
    for rev, rev_nick in REVS:
        algo_name = f"{rev_nick}:{config_nick}" if rev_nick else config_nick
        exp.add_algorithm(
            algo_name,
            REPO,
            rev,
            config,
            build_options=BUILD_OPTIONS,
            driver_options=DRIVER_OPTIONS,
        )
exp.add_suite(BENCHMARKS_DIR, SUITE)

exp.add_parser(exp.EXITCODE_PARSER)
exp.add_parser(exp.TRANSLATOR_PARSER)
#exp.add_parser(exp.SINGLE_SEARCH_PARSER)
exp.add_parser(project.DIR / "parser.py")
#exp.add_parser(exp.PLANNER_PARSER)

exp.add_step("build", exp.build)
exp.add_step("start", exp.start_runs)
exp.add_fetcher(name="fetch")

# if not project.REMOTE:
#     exp.add_step("remove-eval-dir", shutil.rmtree, exp.eval_dir, ignore_errors=True)
    #project.add_scp_step(exp, SCP_LOGIN, REMOTE_REPOS_DIR)

project.add_absolute_report(
    exp, attributes=ATTRIBUTES
    #exp, attributes=ATTRIBUTES, filter=[project.add_evaluations_per_time]
)

attributes = ["action_length", "translator_time_computing_schematic_group"]
pairs = [
    ("main:limited_grounding", "main:all_actions"),
]
suffix = "-rel" if project.RELATIVE else ""
for algo1, algo2 in pairs:
    for attr in attributes:
        exp.add_report(
            project.ScatterPlotReport(
                relative=project.RELATIVE,
                get_category=None if project.TEX else lambda run1, run2: run1["domain"],
                attributes=[attr],
                filter_algorithm=[algo1, algo2],
                #filter=[project.add_evaluations_per_time],
                format="tex" if project.TEX else "png",
            ),
            name=f"{exp.name}-{algo1}-vs-{algo2}-{attr}{suffix}",
        )

exp.run_steps()
