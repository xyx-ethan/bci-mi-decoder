#include <boost/multiprecision/cpp_int.hpp>
#include <cassert>
#include <iostream>
using boost::multiprecision::cpp_int;

static cpp_int ipow(cpp_int a, unsigned e) {
  cpp_int r = 1;
  while (e) {
    if (e & 1U) r *= a;
    a *= a;
    e >>= 1U;
  }
  return r;
}

static bool boundary(long long c, long long target_num = 262146) {
  cpp_int C = c;
  return ipow(C, 3) * 262143 < cpp_int(target_num) * ipow(C - 1, 3);
}

static void check_ratio_bounds(long long t) {
  cpp_int T = t;
  cpp_int p5 = ipow(T,4) + ipow(T,3) + ipow(T,2) + T + 1;
  cpp_int p6 = ipow(T,2) - T + 1;
  // R3(t) < t/(t-1), cross-multiplied over positive denominators.
  assert((ipow(T,2) + 1) * (T - 1) < T * p6);
  // R4(t) < t/(t-1), cross-multiplied over positive denominators.
  assert(p5 * (T - 1) < T * (ipow(T,4) + 1));
}

int main() {
  for (long long t : {2LL, 3LL, 17LL, 87383LL, 262145LL, 1000003LL})
    check_ratio_bounds(t);

  cpp_int diff = cpp_int(262146) * ipow(cpp_int(262144),3)
               - cpp_int(262143) * ipow(cpp_int(262145),3);
  assert(diff == 524289);
  assert(boundary(262145));
  assert(!boundary(262144));
  assert(!boundary(262145, 262145));

  std::cout << "PASS independent cpp_int checker\n";
  std::cout << "boundary_cross_difference=" << diff << "\n";
  std::cout << "mutations_rejected=2/2\n";
}
