from driver import arguments
from builds.release.bin.translate import pddl_parser, options, normalize, instantiate, fact_groups


def main():
    args = arguments.parse_args()
    task = pddl_parser.open(domain_filename=options.domain, task_filename=options.task)
    normalize.normalize(task)
    (relaxed_reachable, atoms, actions, goal_list, axioms,
     reachable_action_params) = instantiate.explore(task)
    groups, mutex_groups, translation_key = fact_groups.compute_groups(
            task, atoms, reachable_action_params)


if __name__ == '__main__':
    main()