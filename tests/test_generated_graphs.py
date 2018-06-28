import z3

from equitable_coloring.core import check_state
from equitable_coloring.core import procedure_P

from .generate_graph import make_graph_from_solver
from .generate_graph import make_hard_prob
from .generate_graph import make_params_from_graph


def test_hard_prob():
    # Tests for two levels of recursion.
    # See test-graphs/a_2_b_3_recurse.png for the nearly-equitable graph.
    edge_vars, constrs, F = make_hard_prob(num_colors=5,
                                           num_nodes_each_color=5,
                                           a=2)
    S = z3.Solver()
    S.add(*constrs)
    S.check()

    G = make_graph_from_solver(edge_vars=edge_vars, solver=S, F=F)
    params = make_params_from_graph(G=G, F=F)

    procedure_P(V_minus=0, V_plus=5 - 1,
                **params)
    check_state(**params)
