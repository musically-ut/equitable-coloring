import networkx as nx
import z3

from equitable_coloring.utils import is_coloring
from equitable_coloring.utils import make_C_from_F


def make_hard_prob(num_colors, num_nodes_each_color, a):
    num_nodes = num_colors * num_nodes_each_color
    b = num_colors - a
    s = num_nodes_each_color

    F = {
        k: k // s
        for k in range(num_nodes)
    }

    F[s - 1] = num_colors - 1  # V- == 0, V+ == num_colors - 1
    C = make_C_from_F(F)

    edge_vars = {
        (i, j): z3.Int('e_{}_{}'.format(i, j))
        for i in range(num_nodes) for j in range(num_nodes)
    }

    constrs = []

    # edge variables can only take values {0, 1}
    constrs += [v >= 0 for v in edge_vars.values()]
    constrs += [v <= 1 for v in edge_vars.values()]

    # edges are undirected
    constrs += [edge_vars[i, j] == edge_vars[j, i]
                for i in range(num_nodes) for j in range(num_nodes)]

    # maximum degree <= num_nodes - 1
    constrs += [sum(edge_vars[i, j] for j in range(num_nodes)) < num_colors
                for i in range(num_nodes)]

    # no self-loops
    constrs += [edge_vars[i, i] == 0 for i in range(num_nodes)]

    # no edges within colors
    constrs += [sum([edge_vars[i, j] for i in C[k] for j in C[k]]) == 0
                for k in range(num_colors)]

    # First `a` colors belong in `A_cal`
    for c1 in range(0, a):
        c1_in_A_cal_constrs = []
        for u in C[c1]:
            for c2 in range(0, a):
                if c1 != c2:
                    N_u_c2 = sum(edge_vars[u, v] for v in C[c2])
                    c1_in_A_cal_constrs.append(N_u_c2 == 0)
        constrs.append(z3.Or(*c1_in_A_cal_constrs))

    # Last `b` colors are _not_ in `A_cal`
    for c1 in range(num_colors - b, num_colors):
        c1_not_in_A_cal_constrs = []
        for u in C[c1]:
            for c2 in range(0, a):
                N_u_c2 = sum(edge_vars[u, v] for v in C[c2])
                c1_not_in_A_cal_constrs.append(N_u_c2 > 0)
        constrs.append(z3.And(*c1_not_in_A_cal_constrs))

    return edge_vars, constrs, F


def add_harder_constraints(edge_vars, constrs, F, a, a_prime):
    """Add constraints which make the graph a test for Case 2 by removing
    solo-edges which witness an edge in H[A_cal] for the last `a_prime`
    colors."""

    C = make_C_from_F(F)
    num_colors = len(C)

    for c1 in range(a - a_prime, a):
        for u in C[c1]:
            u_no_witness = []
            # Either `u` doesn't witness an edge in H[A_cal]
            for c2 in range(0, a):
                if c2 != c1:
                    # u had an edge to some color in c2
                    u_no_witness.append(sum(edge_vars[u, v] for v in C[c2]) > 0)

            # Or `u` does not have a solo neighbor `y` in B such that `y` has
            # only one neighbor in `c1`
            u_no_solo = []
            for c2 in range(a, num_colors):
                for v in C[c2]:
                    # u_no_solo.append(z3.Not(
                    #     z3.And(
                    #         # z3.And(*[edge_vars[u, v2] == (0 if v2 != v else 1) for v2 in C[c2]]),  # N_X(u) == 1
                    #         # Departing from the algorithm in the paper.
                    #         # sum(edge_vars[u, v2] for v2 in C[c2]) > 0,
                    #         sum(edge_vars[v, u2] for u2 in C[c1]) == 1  # N_W(y) == 1
                    #     )
                    # ))
                    u_no_solo.append(
                        z3.Or(
                            edge_vars[v, u] == 0,
                            sum(edge_vars[v, u2] for u2 in C[c1]) > 1
                        )
                    )

            constrs.append(z3.Or(z3.And(*u_no_witness), z3.And(*u_no_solo)))


def make_graph_from_solver(edge_vars, solver, F=None):
    """Solves the given problem and returns a networkX graph."""
    # solver = z3.Solver()
    # solver.add(*constrs)

    # assert solver.check() == z3.sat

    try:
        model = solver.model()
    except z3.Z3Exception:
        print('Checking the solver as it had not been executed.')
        solver.check()

    G = nx.Graph()
    for (i, j), v in edge_vars.items():
        if i < j and model[v] == 1:
            G.add_edge(i, j)

    if F is not None:
        assert is_coloring(G, coloring=F)
    return G
