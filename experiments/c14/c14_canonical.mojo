"""Mojo-first independent 14-cycle hypercube enumeration.

Enumerates restricted-growth coordinate-flip words of length 14, with
first appearances labeled 0,1,2,... and each intermediate vertex visited
exactly once. The 14th step returns to 0. Result P[k] is the number of
oriented length-14 flip words using exactly k coordinates, modulo all
coordinate relabelings (but not modulo rotation or reversal).

For Q_n the ordinary UNLABELED cycle count equals
    2^n / 28 * sum_{k=1..min(n,7)} C(n,k) k! P[k]
Mojo 1.x style based on the estate's finite-math-kernels executables.

NOTE: this file has not been compiled here (Mojo SDK unavailable).
"""


def enumerate_words(step: Int, used: Int, vertex: Int,
                    mut visited: List[Bool], mut patterns: List[Int]):
    if step == 14:
        if vertex == 0:
            patterns[used] += 1
        return
    var last = used
    if last > 6:
        last = 6
    for color in range(last + 1):
        var next_used = used
        if color == used:
            next_used += 1
        var next_vertex = vertex ^ (1 << color)
        if step == 13:
            if next_vertex == 0:
                patterns[next_used] += 1
            continue
        if next_vertex == 0 or visited[next_vertex]:
            continue
        visited[next_vertex] = True
        enumerate_words(step + 1, next_used, next_vertex, visited, patterns)
        visited[next_vertex] = False


def main():
    var visited = List[Bool]()
    for _ in range(128):
        visited.append(False)
    visited[0] = True
    var patterns = List[Int]()
    for _ in range(8):
        patterns.append(0)
    enumerate_words(0, 0, 0, visited, patterns)
    for k in range(4, 8):
        print("P", k, patterns[k])
