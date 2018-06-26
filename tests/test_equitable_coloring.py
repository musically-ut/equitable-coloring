from collections import defaultdict

import networkx as nx

from equitable_coloring import equitable_color
from equitable_coloring.core import check_state
from equitable_coloring.core import is_coloring
from equitable_coloring.core import is_equitable
from equitable_coloring.core import max_degree
from equitable_coloring.core import procedure_P


def test_is_coloring():
    G = nx.Graph()
    G.add_edges_from([(0, 1), (1, 2)])
    coloring = {0: 0, 1: 1, 2: 0}
    assert is_coloring(G, coloring)

    coloring[0] = 1
    assert not is_coloring(G, coloring)


def test_is_equitable():
    G = nx.Graph()
    G.add_edges_from([(0, 1), (1, 2)])
    coloring = {0: 0, 1: 1, 2: 0}
    assert is_equitable(G, coloring)

    G.add_edges_from([(2, 3), (2, 4), (2, 5)])
    coloring[3] = 1
    coloring[4] = 1
    coloring[5] = 1
    assert is_coloring(G, coloring)
    assert not is_equitable(G, coloring)


def test_equitable_color():
    G = nx.fast_gnp_random_graph(n=10, p=0.2, seed=42)
    coloring = equitable_color(G, max_degree(G) + 1)
    assert is_equitable(G, coloring)


def test_equitable_color_empty():
    G = nx.empty_graph()
    coloring = equitable_color(G, max_degree(G) + 1)
    assert is_equitable(G, coloring)


def test_equitable_color_large():
    G = nx.fast_gnp_random_graph(100, 0.1, seed=42)
    coloring = equitable_color(G, max_degree(G) + 1)
    assert is_equitable(G, coloring, num_colors=max_degree(G) + 1)


# def test_equitable_color_larger():
#     N = 500
#     # for idx in range(0, 40, 20):
#     idx = 20
#     p = idx * 0.01
#     seed = idx * 9 + 42
#     G = nx.fast_gnp_random_graph(N, p, seed=seed)
#     coloring = equitable_color(G, max_degree(G) + 1)
#     assert is_equitable(G, coloring), \
#         "Failed for N = {}, p = {}, seed = {}".format(N, p, seed)


def test_hard_case():
    # Hand crafted case to avoid the easy case.
    L = {
        0: [2, 5],
        1: [3, 4],
        2: [0, 8],
        3: [1, 7],
        4: [1, 6],
        5: [0, 6],
        6: [4, 5],
        7: [3],
        8: [2],
    }

    F = {
        # Color 0
        0: 0,
        1: 0,

        # Color 1
        2: 1,
        3: 1,
        4: 1,
        5: 1,

        # Color 2
        6: 2,
        7: 2,
        8: 2,
    }

    C = defaultdict(lambda: [])
    for node, color in F.items():
        C[color].append(node)

    N = {(node, color): sum(1 for v in L[node] if v in C[color])
         for node in range(9) for color in range(3)}

    H = {(c1, c2): sum(1 for node in C[c1] if N[(node, c2)] == 0)
         for c1 in C.keys() for c2 in C.keys()}

    procedure_P(V_minus=0, V_plus=1, N=N, H=H, F=F, C=C, L=L)

    check_state(N=N, H=H, F=F, C=C)
