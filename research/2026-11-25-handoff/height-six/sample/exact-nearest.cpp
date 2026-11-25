// Build with c++ -std=c++20 -O3. Read decompressed masks on standard input.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <optional>
#include <vector>

struct Mask {
    std::uint64_t index, low, high;
};

int distance(const Mask& a, const Mask& b) {
    return std::popcount(a.low ^ b.low) + std::popcount(a.high ^ b.high);
}

int main() {
    std::vector<Mask> rows;
    std::optional<Mask> first, second;
    Mask row;
    while (std::cin >> row.index >> row.low >> row.high) {
        if ((!rows.empty() && row.index <= rows.back().index) || row.high >= 64) return 1;
        if (row.index == 1005166825) first = row;
        if (row.index == 1008991053) second = row;
        rows.push_back(row);
    }
    if (!std::cin.eof() || rows.size() != 163458 || !first || !second) return 1;
    int best = distance(*first, *second);
    if (best != 7) return 1;
    std::uint64_t tests = 0;
    // Any pair differing in fewer than seven bits agrees on an entire block.
    for (int block = 0; block < 7; ++block) {
        std::array<std::vector<std::size_t>, 1024> buckets;
        for (std::size_t i = 0; i < rows.size(); ++i) {
            const auto& m = rows[i];
            unsigned key = 0;
            for (int j = 0; j < 10; ++j) {
                int bit = 17 * (10 * block + j) % 70;
                auto word = bit < 64 ? m.low : m.high;
                key |= ((word >> (bit % 64)) & 1U) << j;
            }
            for (auto earlier : buckets[key]) {
                ++tests;
                int d = distance(m, rows[earlier]);
                if (d < best) best = d;
            }
            buckets[key].push_back(i);
        }
    }
    std::cout << rows.size() << " masks, minimum distance " << best
              << ", " << tests << " bucket pair comparisons\n";
    return best == 7 && tests == 262773441 ? 0 : 1;
}
