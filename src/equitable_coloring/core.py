import networkx as nx
from collections import defaultdict


def is_coloring(G, coloring):
    """Determine if the coloring is a valid coloring for the graph G."""
    # Verify that the coloring is valid.
    for (s, d) in G.edges:
        if coloring[s] == coloring[d]:
            return False
    return True


def is_equitable(G, coloring):
    """Determines if the coloring is valid and equitable for the graph G."""

    if not is_coloring(G, coloring):
        return False

    # Verify whether it is equitable.
    color_set_size = defaultdict(int)
    for color in coloring.values():
        color_set_size[color] += 1

    # If there are less then 2 distinct values, the coloring cannot be equitable
    all_set_sizes = set(color_set_size.values())
    if len(all_set_sizes) > 2:
        return False

    a, b = list(all_set_sizes)
    return abs(a - b) <= 1


def equitable_color(G, r):
    """Provides equitable r-coloring for nodes of G in polynomial time iff deg(G) <= r - 1.
     The algorithm is described in [1]_.

     Attempts to color a graph using r colors, where no neighbours of a node can
     have same color as the node itself and the number of nodes with each color
     differ by at most 1.

     Parameters
     ----------
     G : NetworkX graph

     r : number of colors to use
        This number must be at least one more than the maximum degree of nodes
        in the graph.

     Returns
     -------
     A dictionary with keys representing nodes and values representing
     corresponding coloring.

     Examples
     --------
     >>> from equitable_coloring import equitable_color
     >>> G = nx.cycle_graph(4)
     >>> d = equitable_color(G, r=3)
     >>> d in [{0: 0, 1: 1, 2: 0, 3: 1}, {0: 1, 1: 0, 2: 1, 3: 0}] # TODO: Fix
     False

     References
     ----------
     .. [1] H.A. KIERSTEAD and A.V. KOSTOCHKA: A short proof of the Hajnal-Szemeredi
     theorem on equitable colouring. Combinatorics, Probability and Computing, 17(2),
     (2008), 265-270.
    """
    pass

