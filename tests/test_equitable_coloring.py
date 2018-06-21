import networkx as nx
from equitable_coloring import equitable_color
from equitable_coloring.core import is_coloring, is_equitable, max_degree


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
