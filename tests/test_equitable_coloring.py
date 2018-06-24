import networkx as nx

from equitable_coloring import equitable_color
from equitable_coloring.core import is_coloring
from equitable_coloring.core import is_equitable
from equitable_coloring.core import max_degree


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
    assert is_equitable(G, coloring)


def test_equitable_color_coverage():
    N = 500
    for idx in range(0, 40, 20):
        p = idx * 0.01
        seed = idx * 9 + 42
        G = nx.fast_gnp_random_graph(N, p, seed=seed)
        coloring = equitable_color(G, max_degree(G) + 1)
        assert is_equitable(G, coloring), \
            "Failed for N = {}, p = {}, seed = {}".format(N, p, seed)
