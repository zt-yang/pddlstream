from __future__ import print_function

import copy
import sys
import time
import signal

from pddlstream.algorithms.algorithm import parse_problem, reset_globals
from pddlstream.algorithms.advanced import enforce_simultaneous, identify_non_producers
from pddlstream.algorithms.common import SolutionStore
from pddlstream.algorithms.constraints import PlanConstraints
from pddlstream.algorithms.disabled import push_disabled, reenable_disabled, process_stream_plan
from pddlstream.algorithms.disable_skeleton import create_disabled_axioms
from pddlstream.algorithms.diverse import PRIOR_PLANS
#from pddlstream.algorithms.downward import has_costs
from pddlstream.algorithms.incremental import process_stream_queue
from pddlstream.algorithms.instantiation import Instantiator
from pddlstream.algorithms.refinement import iterative_plan_streams, get_optimistic_solve_fn
from pddlstream.algorithms.scheduling.plan_streams import OptSolution
from pddlstream.algorithms.reorder import reorder_stream_plan
from pddlstream.algorithms.skeleton import SkeletonQueue
from pddlstream.algorithms.visualization import reset_visualizations, create_visualizations, \
    has_pygraphviz, log_plans, log_actions, set_visualizations_false
from pddlstream.language.constants import is_plan, get_length, str_from_plan, INFEASIBLE, str_from_action
from pddlstream.language.fluent import compile_fluent_streams
from pddlstream.language.function import Function, Predicate
from pddlstream.language.optimizer import ComponentStream
from pddlstream.algorithms.recover_optimizers import combine_optimizers
from pddlstream.language.statistics import load_stream_statistics, dump_online_statistics, \
    write_stream_statistics, compute_plan_effort
from pddlstream.language.stream import Stream, StreamResult, PartialInputs, StreamInfo
from pddlstream.language.external import never_defer
from pddlstream.utils import INF, implies, str_from_object, safe_zip

def get_negative_externals(externals):
    negative_predicates = list(filter(lambda s: type(s) is Predicate, externals)) # and s.is_negative()
    negated_streams = list(filter(lambda s: isinstance(s, Stream) and s.is_negated, externals))
    return negative_predicates + negated_streams

def partition_externals(externals, verbose=False):
    functions = list(filter(lambda s: type(s) is Function, externals))
    negative = get_negative_externals(externals)
    optimizers = list(filter(lambda s: isinstance(s, ComponentStream) and (s not in negative), externals))
    streams = list(filter(lambda s: s not in (functions + negative + optimizers), externals))
    if verbose:
        print('Streams: {}\nFunctions: {}\nNegated: {}\nOptimizers: {}'.format(
            streams, functions, negative, optimizers))
    return streams, functions, negative, optimizers

##################################################

def recover_optimistic_outputs(stream_plan):
    if not is_plan(stream_plan):
        return stream_plan
    new_mapping = {}
    new_stream_plan = []
    for result in stream_plan:
        new_result = result.remap_inputs(new_mapping)
        new_stream_plan.append(new_result)
        if isinstance(new_result, StreamResult):
            opt_result = new_result.instance.opt_results[0] # TODO: empty if disabled
            new_mapping.update(safe_zip(new_result.output_objects, opt_result.output_objects))
    return new_stream_plan

def check_dominated(skeleton_queue, stream_plan):
    if not is_plan(stream_plan):
        return True
    for skeleton in skeleton_queue.skeletons:
        # TODO: has stream_plans and account for different output object values
        if frozenset(stream_plan) <= frozenset(skeleton.stream_plan):
            print(stream_plan)
            print(skeleton.stream_plan)
    raise NotImplementedError()

def set_all_opt_gen_fn(externals, unique=None, verbose=False):
    # TODO: move to parse_problem?
    if unique is None:
        return
    # from pddlstream.language.stream import DEFAULT_UNIQUE
    # from pddlstream.algorithms.meta import set_unique
    # set_unique(externals)
    if verbose:
        print('focused.py : set_all_opt_gen_fn')
    for i, external in enumerate(externals):
        if isinstance(external, Stream):
            # TODO: apply only if not in stream_map?
            #external.info.opt_gen_fn.unique = unique
            external.info.opt_gen_fn = PartialInputs(unique=unique)
            external.info.defer_fn = never_defer
            #external.info = StreamInfo(opt_gen_fn=PartialInputs(unique=unique))
            external.setup_opt_gen_fns(external.info.opt_gen_fn)
        if verbose:
            print(i, external) ## , external.info

##################################################

# class PlanDataset(object): # Optimistic
#     # TODO: integrate with SolutionStore?
#     def __init__(self):
#         pass
#     def add_plan(self, ):
#         pass

def satisfy_optimistic_plan(store, domain, opt_solutions, use_feedback=False, use_contexts=False, max_time=10):
    # TODO: create a new store
    # TODO: could pass domain=None
    # TODO: reuse instantiation
    #stream_plan, opt_plan, cost = opt_solution
    #if not is_plan(opt_plan):
    #    return None
    if not opt_solutions:
        return None
    externals = {result.external for stream_plan, _, _ in opt_solutions for result in stream_plan}
    for external in externals:
        external.get_complexity = lambda num_calls: 0

    store.solutions = []
    skeleton_queue = SkeletonQueue(store, domain, disable=use_feedback, use_contexts=use_contexts)
    for stream_plan, opt_plan, cost in opt_solutions:
        skeleton_queue.new_skeleton(stream_plan, opt_plan, cost)
    skeleton_queue.process(complexity_limit=-1, max_time=max_time)
    skeleton_queue.greedily_process()
    #plan = store.best_plan
    solution = store.extract_solution()
    # TODO: need to reset the complexity (but not the opt fn)
    # TODO: discard if same plan ignoring action order

    # TODO: need to condition on new stream plan to use the result
    store.solutions = []
    for external in externals:
        external.get_complexity = lambda num_calls: 0
        for instance in external.instances.values():
            instance._generator = None # All generators are wrapped to function calls
            instance.history = []
            instance.results_history = []
            instance.enumerated = False
            instance.reset()
            # for results in instance.results_history:
            #     print(results)
        #external.instances.clear()
        #external.reset()
    #reset_globals()
    # TODO: generator for making multiple plans
    return solution

##################################################


def solve_abstract(problem, constraints=PlanConstraints(), stream_info={},
                   unique_optimistic=None, use_feedback=True, replan_actions=set(),
                   unit_costs=False, success_cost=INF,
                   max_time=INF, max_iterations=INF, max_memory=INF,
                   initial_complexity=0, complexity_step=1, max_complexity=INF,
                   max_skeletons=INF, search_sample_ratio=0, bind=True, max_failures=0,
                   unit_efforts=False, max_effort=INF, effort_weight=None, reorder=True,
                   visualize=False, log_failures=True, verbose=True,
                   fc=None, domain_modifier=None, world=None, plan_dataset=None, max_solutions=1,
                   evaluation_time=30, stream_planning_timeout=5, total_planning_timeout=360,
                   max_evaluation_plans=20, max_complexity_limit=5, **search_kwargs):
    """
    Solves a PDDLStream problem by first planning with optimistic stream outputs and then querying streams
    :param problem: a PDDLStream problem
    :param constraints: PlanConstraints on the set of legal solutions
    :param stream_info: a dictionary from stream name to StreamInfo altering how individual streams are handled
    :param replan_actions: the actions declared to induce replanning for the purpose of deferred stream evaluation

    :param unit_costs: use unit action costs rather than numeric costs
    :param success_cost: the exclusive (strict) upper bound on plan cost to successfully terminate

    :param max_time: the maximum runtime
    :param max_iterations: the maximum number of search iterations
    :param max_memory: the maximum amount of memory

    :param initial_complexity: the initial stream complexity limit
    :param complexity_step: the increase in the stream complexity limit per iteration
    :param max_complexity: the maximum stream complexity limit

    :param max_skeletons: the maximum number of plan skeletons (max_skeletons=None indicates not adaptive)
    :param search_sample_ratio: the desired ratio of sample time / search time when max_skeletons!=None
    :param bind: if True, propagates parameter bindings when max_skeletons=None
    :param max_failures: the maximum number of stream failures before switching phases when max_skeletons=None

    :param unit_efforts: use unit stream efforts rather than estimated numeric efforts
    :param max_effort: the maximum amount of stream effort
    :param effort_weight: a multiplier for stream effort compared to action costs
    :param reorder: if True, reorder stream plans to minimize the expected sampling overhead

    :param visualize: if True, draw the constraint network and stream plan as a graphviz file
    :param verbose: if True, print the result of each stream application
    :param search_kwargs: keyword args for the search subroutine

    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan (INF if no plan), and evaluations is init expanded
        using stream applications
    """
    # TODO: select whether to search or sample based on expected success rates
    # TODO: no optimizers during search with relaxed_stream_plan
    # TODO: locally optimize only after a solution is identified
    # TODO: replan with a better search algorithm after feasible
    # TODO: change the search algorithm and unit costs based on the best cost
    from pybullet_tools.logging_utils import myprint as print
    debug_label = 'focused |'
    log_time = debug_label + " sequencing time: {time_sequencing} | sampling time: {time_sampling}"

    use_skeletons = (max_skeletons is not None)
    #assert implies(use_skeletons, search_sample_ratio > 0)
    eager_disabled = (effort_weight is None)  # No point if no stream effort biasing
    num_iterations = eager_calls = 0
    complexity_limit = initial_complexity

    evaluations, goal_exp, domain, externals = parse_problem(
        problem, stream_info=stream_info, constraints=constraints,
        unit_costs=unit_costs, unit_efforts=unit_efforts)
    print(f'\n\n{debug_label} | number of evaluations: {len(evaluations)}\n')
    if domain_modifier is not None:
        domain, externals = domain_modifier((domain, externals))
    set_all_opt_gen_fn(externals, unique=unique_optimistic, verbose=False)

    identify_non_producers(externals)
    enforce_simultaneous(domain, externals)
    compile_fluent_streams(domain, externals)
    # TODO: make effort_weight be a function of the current cost
    # if (effort_weight is None) and not has_costs(domain):
    #     effort_weight = 1

    # load_stream_statistics(externals)
    if visualize and not has_pygraphviz():
        visualize = False
        print('\n\n\n\nWarning, visualize=True requires pygraphviz. Setting visualize=False\n\n\n\n')
    if log_failures or visualize:
        reset_visualizations()
    else:
        set_visualizations_false()

    streams, functions, negative, optimizers = partition_externals(externals, verbose=verbose)
    eager_externals = list(filter(lambda e: e.info.eager, externals))
    positive_externals = streams + functions + optimizers
    has_optimizers = bool(optimizers) # TODO: deprecate
    assert implies(has_optimizers, use_skeletons)

    ################

    store = SolutionStore(evaluations, max_time, success_cost, verbose, max_memory=max_memory)
    skeleton_queue = SkeletonQueue(store, domain if use_feedback else None, disable=use_feedback and not has_optimizers)
    disabled = set() # Max skeletons after a solution

    PRIOR_PLANS.clear() # TODO(caelan): better way of handling this
    start_time = time.time()
    num_solutions = None
    time_sequencing = 0
    time_sampling = 0
    while (not store.is_terminated()) and (num_iterations < max_iterations) and (complexity_limit <= max_complexity):
        num_iterations += 1
        eager_instantiator = Instantiator(eager_externals, evaluations) # Only update after an increase?
        if eager_disabled:
            push_disabled(eager_instantiator, disabled)
        if eager_externals:
            eager_calls += process_stream_queue(eager_instantiator, store,
                                                complexity_limit=complexity_limit, verbose=verbose)

        ################

        print('\nIteration: {} | Complexity: {} | Skeletons: {} | Skeleton Queue: {} | Disabled: {} | Evaluations: {} | '
              'Eager Calls: {} | Cost: {:.3f} | Search Time: {:.3f} | Sample Time: {:.3f} | Total Time: {:.3f}'.format(
            num_iterations, complexity_limit, len(skeleton_queue.skeletons), len(skeleton_queue), len(disabled),
            len(evaluations), eager_calls, store.best_cost, store.search_time, store.sample_time, store.elapsed_time()))
        optimistic_solve_fn = get_optimistic_solve_fn(goal_exp, domain, negative,
                                                      replan_actions=replan_actions, reachieve=use_skeletons,
                                                      max_cost=min(store.best_cost, constraints.max_cost),
                                                      max_effort=max_effort, effort_weight=effort_weight, **search_kwargs)

        start_diverse = time.time()
        # TODO: just set unit effort for each stream beforehand
        opt_solutions = INFEASIBLE
        if (max_skeletons is None) or (len(skeleton_queue.skeletons) < max_skeletons):
            disabled_axioms = create_disabled_axioms(skeleton_queue) if has_optimizers else []
            if disabled_axioms:
                domain.axioms.extend(disabled_axioms)
            print(f'\n\nlog | number of evaluations {num_iterations}: {len(evaluations)}\n')

            ################################## function with a timeout #################################
            signal.signal(signal.SIGALRM, timeout_handler)
            signal.alarm(stream_planning_timeout)
            import traceback
            try:
                opt_solutions = iterative_plan_streams(evaluations, positive_externals, optimistic_solve_fn,
                                                       complexity_limit, save_streams_txt=visualize,
                                                       max_effort=max_effort)
            except Exception as ex:
                traceback.print_exc()
                # if "TIMEOUT" in ex:
                #     print("Gotcha!")
                # else:
                #     print("We're gonna need a bigger boat!")
                opt_solutions = INFEASIBLE
                print(f"\nTimed out iterative_plan_streams() in {stream_planning_timeout} sec\n")
            finally:
                signal.alarm(0)

            ###################################################################################
            for axiom in disabled_axioms:
                domain.axioms.remove(axiom)

        time_sequencing += time.time() - start_diverse

        if plan_dataset is not None:
            print('\n\nCount Diverse Time: {:.3f}'.format(time.time() - start_diverse))
            if not isinstance(opt_solutions, bool):
                print(f'Count Diverse Plans: {len(opt_solutions)}\n\n\n\n')

        # TODO: sample-pose ahead of sample-grasp
        #print(opt_solutions, not eager_instantiator, not skeleton_queue, not disabled, len(skeleton_queue))
        #print(skeleton_queue.queue)
        if opt_solutions is INFEASIBLE:
            opt_solutions = []
            if (not eager_instantiator) and (not skeleton_queue) and (not disabled):
                print(debug_label, 'opt_solutions is INFEASIBLE')
                print(log_time.format(time_sequencing=time_sequencing, time_sampling=time_sampling))
                return None

        if not opt_solutions:
            print('No plans: increasing complexity from {} to {}'.format(complexity_limit, complexity_limit+complexity_step))
            if complexity_limit > max_complexity_limit:
                return None
            complexity_limit += complexity_step
            if not eager_disabled:
                reenable_disabled(evaluations, domain, disabled)

        else:
            if fc is not None:
                action_plans = [opt_plan.action_plan for _, opt_plan, _ in opt_solutions]
                scores = fc(action_plans)
                scored_solutions = list(zip(opt_solutions, scores))
                scored_solutions = [m for m in scored_solutions if m[1] != 'skip']
                scored_solutions.sort(key=lambda item: item[1], reverse=True)
                filtered = []
                for i, (opt_solution, score) in enumerate(scored_solutions):
                    stream_plan, opt_plan, cost = opt_solution
                    action_plan = opt_plan.action_plan
                    action_plan = [action for action in action_plan if action.name != 'move_base']
                    if not isinstance(score, str):
                        feasible = bool(score)
                        if score > 0.5 and (opt_solution, score) not in filtered:
                            filtered.append((opt_solution, score))
                            print(f'{i + 1}/{len(scored_solutions)}) Score: {score} | Feasible: {feasible} | '
                                  f'Cost: {cost} | Length: {len(action_plan)} | Plan: {action_plan}')
                if len(filtered) <= 1:
                    for i, (opt_solution, score) in enumerate(scored_solutions):
                        stream_plan, opt_plan, cost = opt_solution
                        action_plan = opt_plan.action_plan
                        action_plan = [action for action in action_plan if action.name != 'move_base']
                        feasible = bool(score)
                        if score > 0.25:
                            filtered.append((opt_solution, score))
                            print(f'{i + 1}/{len(scored_solutions)}) Score: {score} | Feasible: {feasible} | '
                                  f'Cost: {cost} | Length: {len(action_plan)} | Plan: {action_plan}\n')
                        if not isinstance(score, str):
                            feasible = bool(score)
                            if score > 0.0001 and (opt_solution, score) not in filtered:
                                filtered.append((opt_solution, score))
                                print(f'{i + 1}/{len(scored_solutions)}) Score: {score} | Feasible: {feasible} | '
                                      f'Cost: {cost} | Length: {len(action_plan)} | Plan: {action_plan}')
                opt_solutions = []
                if len(filtered) > 0:
                    opt_solutions, _ = zip(*filtered)

        ## ICRA 2022
        # search_sample_ratio = 1
        if evaluation_time < 0:
            print(debug_label, 'evaluation_time < 0')
            print(log_time.format(time_sequencing=time_sequencing, time_sampling=time_sampling))
            return None

        for i, opt_solution in enumerate(opt_solutions):
            stream_plan, opt_plan, cost = opt_solution
            #stream_plan = replan_with_optimizers(evaluations, stream_plan, domain, externals) or stream_plan
            stream_plan[:] = combine_optimizers(evaluations, stream_plan)
            #stream_plan = get_synthetic_stream_plan(stream_plan, # evaluations
            #                                       [s for s in synthesizers if not s.post_only])
            #stream_plan = recover_optimistic_outputs(stream_plan)
            if reorder:
                # TODO: this blows up memory wise for long stream plans
                stream_plan[:] = reorder_stream_plan(store, stream_plan)

            #for i, result in enumerate(stream_plan):
            #    result.context = stream_plan[i:]

            num_optimistic = sum(r.optimistic for r in stream_plan) if stream_plan else 0
            action_plan = opt_plan.action_plan if is_plan(opt_plan) else opt_plan

            # --------------------------------------

            ## YANG for debugging
            if isinstance(stream_plan, list):
                stream_plan_str = ''
                index = 0
                for n in stream_plan:
                    index += 1
                    stream_plan_str += f'\n   {index} > ' + str(n)
            else:
                stream_plan_str = stream_plan

            if isinstance(action_plan, list):
                from pybullet_tools.bullet_utils import print_action_plan
                action_plan_str = print_action_plan(action_plan, stream_plan, world=world)
            else:
                action_plan_str = 'None'

            # --------------------------------------

            print('{}/{}) Stream plan ({}, {}, {:.3f}): {}\nAction plan ({}, {:.3f}): {}\n'.format(
                i, len(opt_solutions),
                get_length(stream_plan), num_optimistic, compute_plan_effort(stream_plan), stream_plan_str, ## stream_plan,
                get_length(action_plan), cost, action_plan_str))  ## , str_from_plan(action_plan)))

            ## saved all skeletons attempted to refine and all failed streams
            if log_failures:
                log_actions(stream_plan, action_plan, num_iterations)

            ## visualize constraint graphs
            if visualize:
                create_visualizations(evaluations, stream_plan, num_iterations)

            start_sampling = time.time()
            if plan_dataset is not None:
                solution = None
                if evaluation_time is not None:
                    solution = satisfy_optimistic_plan(store, domain, opt_solutions=[opt_solution], max_time=evaluation_time)
                time_sampling += time.time() - start_sampling
                plan_dataset.append((opt_solution, solution))
                num_plans = len(plan_dataset)
                if num_plans > max_evaluation_plans:
                    return None
                num_solutions = sum((soln is not None) and is_plan(soln[0]) for _, soln in plan_dataset)
                print(f'Plans: {num_plans} | Solutions: {num_solutions} | evaluation_time: {evaluation_time} sec '
                      f'| Actual time: {round(time_sampling, 2)} sec\n')
                if solution is not None and is_plan(solution[0]):
                    print(f'\n\n----------------------------------------\n\n')
                    print(debug_label, f'Solution ({num_solutions}), {max_solutions - num_solutions} solutions to go')
                    print(f'\n\n----------------------------------------\n\n')
                    if num_solutions >= max_solutions:
                        # write_stream_statistics(externals, verbose=True)
                        #return store.extract_solution() # TODO: return plan_dataset

                        dump_online_statistics(externals)
                        print(debug_label, '!!! num_solutions >= max_solutions !!!')
                        print(log_time.format(time_sequencing=time_sequencing, time_sampling=time_sampling))
                        return solution
                continue

            ## TODO: check plan feasibility here
            if fc is not None:
                if not fc(action_plan):
                    complexity_limit += complexity_step
                    print(debug_label, 'Skip planning according to', fc.__class__.__name__)
                    continue

            ################

            #print(stream_plan_complexity(evaluations, stream_plan))
            if not use_skeletons:
                process_stream_plan(store, domain, disabled, stream_plan, opt_plan, cost, bind=bind, max_failures=max_failures)
                continue

            ################

            # TODO(caelan): add all skeletons and process
            #optimizer_plan = replan_with_optimizers(evaluations, stream_plan, domain, optimizers)
            optimizer_plan = None
            if optimizer_plan is not None:
                # TODO: post process a bound plan
                print('Optimizer plan ({}, {:.3f}): {}'.format(
                    get_length(optimizer_plan), compute_plan_effort(optimizer_plan), optimizer_plan))
                skeleton_queue.new_skeleton(optimizer_plan, opt_plan, cost)
            else:
                skeleton_queue.new_skeleton(stream_plan, opt_plan, cost)

        allocated_sample_time = (search_sample_ratio * store.search_time) - store.sample_time \
            if len(skeleton_queue.skeletons) <= max_skeletons else INF

        # YANG for debugging
        # print('\n\n!! allocated_sample_time', allocated_sample_time, 20, '\n\n')
        # allocated_sample_time = 20
        skeleton_queue.process(complexity_limit=complexity_limit, max_time=allocated_sample_time)
        ## ICRA 2022
        # skeleton_queue.process(complexity_limit=-1, max_time=allocated_sample_time)
        # if skeleton_queue.process(stream_plan, opt_plan, cost, complexity_limit, allocated_sample_time) is INFEASIBLE:
        #     break

        print(f'\n\nfocused.py | time.time() - start_time = {round(time.time() - start_time, 2)} '
              f'(timeout = {total_planning_timeout})', )
        if time.time() - start_time > total_planning_timeout:
            print('\n\n--------- TIMEOUT --------\n\n')
            break
        # print('(not store.is_terminated())', (not store.is_terminated()))
        # print('(num_iterations < max_iterations)', (num_iterations < max_iterations))
        # print('(complexity_limit <= max_complexity)', (complexity_limit <= max_complexity))
        # print('plan_dataset', plan_dataset is not None)
        # print('num_solutions', num_solutions)
    ################

    summary = store.export_summary()
    summary.update({
        'iterations': num_iterations,
        'complexity': complexity_limit,
        'skeletons': len(skeleton_queue.skeletons),
    })
    print('Summary: {}'.format(str_from_object(summary, ndigits=3))) # TODO: return the summary

    # from zzz.logging import write_stream_statistics
    write_stream_statistics(externals, verbose=True)
    print(log_time.format(time_sequencing=time_sequencing, time_sampling=time_sampling))
    return store.extract_solution()


solve_focused = solve_abstract # TODO: deprecate solve_focused

##################################################

def solve_focused_original(problem, fail_fast=False, **kwargs):
    """
    Solves a PDDLStream problem by first planning with optimistic stream outputs and then querying streams
    :param problem: a PDDLStream problem
    :param fail_fast: whether to switch phases as soon as a stream fails
    :param kwargs: keyword args for solve_focused
    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan, and evaluations is init but expanded
        using stream applications
    """
    max_failures = 0 if fail_fast else INF
    return solve_abstract(problem, max_skeletons=None, search_sample_ratio=None,
                          bind=False, max_failures=max_failures, **kwargs)

def solve_binding(problem, fail_fast=False, **kwargs):
    """
    Solves a PDDLStream problem by first planning with optimistic stream outputs and then querying streams
    :param problem: a PDDLStream problem
    :param fail_fast: whether to switch phases as soon as a stream fails
    :param kwargs: keyword args for solve_focused
    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan, and evaluations is init but expanded
        using stream applications
    """
    max_failures = 0 if fail_fast else INF
    return solve_abstract(problem, max_skeletons=None, search_sample_ratio=None,
                          bind=True, max_failures=max_failures, **kwargs)

def solve_adaptive(problem, max_skeletons=INF, search_sample_ratio=1, **kwargs):
    """
    Solves a PDDLStream problem by first planning with optimistic stream outputs and then querying streams
    :param problem: a PDDLStream problem
    :param max_skeletons: the maximum number of plan skeletons to consider
    :param search_sample_ratio: the desired ratio of search time / sample time
    :param kwargs: keyword args for solve_focused
    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan, and evaluations is init but expanded
        using stream applications
    """
    max_skeletons = INF if max_skeletons is None else max_skeletons
    #search_sample_ratio = clip(search_sample_ratio, lower=0) # + EPSILON
    #assert search_sample_ratio > 0
    return solve_abstract(problem, max_skeletons=max_skeletons, search_sample_ratio=search_sample_ratio,
                          bind=None, max_failures=None, **kwargs)

def solve_hierarchical(problem, **kwargs):
    """
    Solves a PDDLStream problem by first planning with optimistic stream outputs and then querying streams
    :param problem: a PDDLStream problem
    :param search_sample_ratio: the desired ratio of sample time / search time
    :param kwargs: keyword args for solve_focused
    :return: a tuple (plan, cost, evaluations) where plan is a sequence of actions
        (or None), cost is the cost of the plan, and evaluations is init but expanded
        using stream applications
    """
    return solve_adaptive(problem, max_skeletons=1, search_sample_ratio=INF, # TODO: rename to sample_search_ratio
                          bind=None, max_failures=None, **kwargs)


##########################################

def timeout_handler(num, stack):
    print(f"setting timeout_handler for {num}")
    raise Exception("TIMEOUT")
