// Independent vertex DFS: no coordinate relabelling or support reconstruction.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>

std::array<bool, 128> visited{};
std::array<std::uint64_t, 8> histogram{};
int dimension, length;

void dfs(int vertex, int depth, unsigned support) {
    if (depth == length - 1) {
        // Close by an actual cube edge; zero was marked visited at entry.
        if (vertex && (vertex & (vertex - 1)) == 0) {
            unsigned final_support = support | unsigned(vertex);
            ++histogram[__builtin_popcount(final_support)];
        }
        return;
    }
    // Deliberately no parity/distance pruning: independent adjacency traversal.
    for (int c = 0; c < dimension; ++c) {
        int next = vertex ^ (1 << c);
        if (!visited[next]) {
            visited[next] = true;
            dfs(next, depth + 1, support | (1u << c));
            visited[next] = false;
        }
    }
}

int main(int argc, char** argv) {
    if (argc != 3) return 2;
    dimension = std::stoi(argv[1]); length = std::stoi(argv[2]);
    if (dimension < 1 || dimension > 7 || length < 4 || length > 14 || length % 2)
        return 2;
    // Fix only the first edge 0 -> 1. Coordinate symmetry restores n choices.
    visited[0] = visited[1] = true;
    dfs(1, 1, 1);
    std::uint64_t total = 0;
    for (int k = 0; k <= dimension; ++k) {
        std::uint64_t rooted = histogram[k] * dimension;
        // 2 orientations * length roots per cycle, and 2^n origin choices.
        std::uint64_t numerator = rooted * (1u << dimension);
        if (numerator % (2 * length)) throw std::runtime_error("normalization");
        auto cycles = numerator / (2 * length);
        total += cycles;
        std::cout << k << ' ' << rooted << ' ' << cycles << '\n';
    }
    std::cout << "total " << total << '\n';
}
