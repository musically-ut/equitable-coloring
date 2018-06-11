import networkx as nx


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

