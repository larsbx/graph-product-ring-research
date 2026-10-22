"""Exact ordinary (unoriented, unrooted, not necessarily induced) cube cycles."""
from math import comb, factorial


def canonical_patterns(length=14):
    """Restricted-growth flip words; histogram by number of used coordinates.

    First occurrences are 0,1,... . Only final return may revisit a vertex.
    Hamming distance to zero is a necessary lower bound on remaining steps.
    """
    if length < 4 or length % 2:
        raise ValueError('length must be even and at least four')
    counts = [0] * (length // 2 + 1)
    seen = {0}

    def visit(vertex, used, depth):
        if depth == length:
            if vertex == 0:
                counts[used] += 1
            return
        remaining = length - depth
        if vertex.bit_count() > remaining:
            return
        for coordinate in range(min(used + 1, length // 2)):
            nxt = vertex ^ (1 << coordinate)
            if nxt == 0:
                if remaining == 1:
                    visit(nxt, used, depth + 1)
                continue
            if nxt in seen:
                continue
            seen.add(nxt)
            visit(nxt, max(used, coordinate + 1), depth + 1)
            seen.remove(nxt)

    visit(0, 0, 0)
    return counts


def support_cycles(patterns, length):
    result = []
    for k, count in enumerate(patterns):
        value, remainder = divmod((1 << k) * factorial(k) * count, 2 * length)
        if remainder:
            raise ValueError('nonintegral cycle normalization')
        result.append(value)
    return result


def cube_total(n, support):
    return sum((1 << (n-k)) * comb(n, k) * support[k]
               for k in range(min(n + 1, len(support))))


def support_defect(n, totals):
    """Inclusion-exclusion at the vertex-count character epsilon(K2)=2."""
    return sum((-2) ** (n-j) * comb(n, j) * totals[j] for j in range(n+1))
