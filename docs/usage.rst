=====
Usage
=====

To use equitable-coloring in a project::

        >>> import networkx as nx
        >>> from equitable_coloring import equitable_color, is_equitable
        >>> G = nx.cycle_graph(4)
        >>> d = equitable_color(G, num_colors=3)
        >>> is_equitable(d)
        True
