#include <cassert>
#include <cstdint>
#include <iostream>

using u128 = unsigned __int128;

static u128 ipow(u128 a, unsigned e) {
  u128 r = 1;
  for (unsigned i = 0; i < e; ++i) r *= a;
  return r;
}

static bool boundary(std::uint64_t c, std::uint64_t target_num = 262146) {
  u128 C = c;
  return ipow(C, 3) * 262143u < u128(target_num) * ipow(C - 1, 3);
}

static void check_ratio_bounds(std::uint64_t t) {
  u128 T = t;
  u128 p5 = ipow(T,4) + ipow(T,3) + ipow(T,2) + T + 1;
  u128 p6 = ipow(T,2) - T + 1;
  // Exact cross-multiplication over positive denominators.
  assert((ipow(T,2) + 1) * (T - 1) < T * p6);
  assert(p5 * (T - 1) < T * (ipow(T,4) + 1));
}

int main() {
  for (std::uint64_t t : {2ULL, 3ULL, 17ULL, 87383ULL, 262145ULL, 1000003ULL})
    check_ratio_bounds(t);

  u128 diff = u128(262146) * ipow(u128(262144),3)
            - u128(262143) * ipow(u128(262145),3);
  assert(diff == 524289u);
  assert(boundary(262145));
  assert(!boundary(262144));
  assert(!boundary(262145, 262145));

  std::cout << "PASS independent __int128 checker\n";
  std::cout << "boundary_cross_difference=524289\n";
  std::cout << "mutations_rejected=2/2\n";
}
