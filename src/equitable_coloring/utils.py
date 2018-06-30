from collections import defaultdict


def check_state(L, N, H, F, C):
    s = len(C[0])
    num_colors = len(C.keys())

    assert all(u in L[v] for u in L.keys() for v in L[u])
    assert all(F[u] != F[v] for u in L.keys() for v in L[u])
    assert all(len(L[u]) < num_colors for u in L.keys())
    assert all(len(C[x]) == s for x in C)
    assert all(H[(c1, c2)] >= 0 for c1 in C.keys() for c2 in C.keys())
    assert all(N[(u, F[u])] == 0 for u in F.keys())


def make_C_from_F(F):
    C = defaultdict(lambda: [])
    for node, color in F.items():
        C[color].append(node)

    return C


def make_N_from_L_C(L, C):
    nodes = L.keys()
    colors = C.keys()
    return {(node, color): sum(1 for v in L[node] if v in C[color])
            for node in nodes for color in colors}


def make_H_from_C_N(C, N):
    return {(c1, c2): sum(1 for node in C[c1] if N[(node, c2)] == 0)
            for c1 in C.keys() for c2 in C.keys()}


def max_degree(G):
    """Get the maximum degree of any node in G."""
    return max([G.degree(node) for node in G.nodes]) if len(G.nodes) > 0 else 0


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


def is_coloring(G, coloring):
    """Determine if the coloring is a valid coloring for the graph G."""
    # Verify that the coloring is valid.
    for (s, d) in G.edges:
        if coloring[s] == coloring[d]:
            return False
    return True


def is_equitable(G, coloring, num_colors=None):
    """Determines if the coloring is valid and equitable for the graph G."""

    if not is_coloring(G, coloring):
        return False

    # Verify whether it is equitable.
    color_set_size = defaultdict(int)
    for color in coloring.values():
        color_set_size[color] += 1

    if num_colors is not None:
        for color in range(num_colors):
            if color not in color_set_size:
                # These colors do not have any vertices attached to them.
                color_set_size[color] = 0

    # If there are more than 2 distinct values, the coloring cannot be equitable
    all_set_sizes = set(color_set_size.values())
    if len(all_set_sizes) == 0 and num_colors is None:  # Was an empty graph
        return True
    elif len(all_set_sizes) == 1:
        return True
    elif len(all_set_sizes) == 2:
        a, b = list(all_set_sizes)
        return abs(a - b) <= 1
    else:   # len(all_set_sizes) > 2:
        return False
