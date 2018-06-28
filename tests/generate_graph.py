import networkx as nx
import z3

from equitable_coloring.core import is_coloring
from equitable_coloring.core import make_C_from_F
from equitable_coloring.core import make_H_from_C_N
from equitable_coloring.core import make_N_from_L_C


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


def make_graph_from_solver(edge_vars, solver, F=None):
    """Solves the given problem and returns a networkX graph."""
    # solver = z3.Solver()
    # solver.add(*constrs)

    assert solver.check() == z3.sat

    model = solver.model()
    G = nx.Graph()
    for (i, j), v in edge_vars.items():
        if i < j and model[v] == 1:
            G.add_edge(i, j)

    if F is not None:
        assert is_coloring(G, coloring=F)
    return G


def make_params_from_graph(G, F):
    """Returns {N, L, H, C} from the given graph."""
    num_nodes = len(G)
    L = {u: [] for u in range(num_nodes)}
    for (u, v) in G.edges:
        L[u].append(v)
        L[v].append(u)

    C = make_C_from_F(F)
    N = make_N_from_L_C(L, C)
    H = make_H_from_C_N(C, N)

    return {
        'N': N,
        'F': F,
        'C': C,
        'H': H,
        'L': L,
    }
