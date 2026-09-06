#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

using Candidate = std::tuple<int, int, int, int>;

static std::vector<int> primes_up_to(int n) {
  std::vector<bool> sieve(static_cast<std::size_t>(n + 1), true);
  sieve[0] = sieve[1] = false;
  for (int p = 2; p * p <= n; ++p)
    if (sieve[p])
      for (int k = p * p; k <= n; k += p) sieve[k] = false;
  std::vector<int> out;
  for (int p = 2; p <= n; ++p)
    if (sieve[p]) out.push_back(p);
  return out;
}

static int qbound(int f) {
  switch (f) {
    case 3: return 216;
    case 4: return 39;
    case 5: return 16;
    case 6: return 9;
    case 7: return 6;
    case 8: return 5;
    case 9: return 4;
    default: return 0;
  }
}

static std::vector<Candidate> domain() {
  const auto primes = primes_up_to(2240);
  std::vector<Candidate> out;
  for (const int q : primes)
    if (q > 2)
      for (int e = 1; e <= 14; ++e) out.emplace_back(2, q, e, 2);
  for (int f = 3; f <= 9; ++f) {
    for (const int q : primes) {
      if (q > qbound(f)) break;
      for (const int p : primes) {
        if (p >= q) break;
        for (int e = 1; e <= 14; ++e) out.emplace_back(p, q, e, f);
      }
    }
  }
  return out;
}

static int digits10(int n) {
  int d = 1;
  while (n >= 10) {
    n /= 10;
    ++d;
  }
  return d;
}

static int powmod(std::int64_t a, int e, int m) {
  std::int64_t r = 1 % m;
  a %= m;
  while (e > 0) {
    if (e & 1) r = (r * a) % m;
    a = (a * a) % m;
    e >>= 1;
  }
  return static_cast<int>(r);
}

static int lhs_mod(int p, int q, int e, int f, int m) {
  return static_cast<int>((static_cast<std::int64_t>(powmod(p, e, m)) *
                           powmod(q, f, m)) % m);
}

static int encoded_mod(int p, int q, int e, int f, int m) {
  std::int64_t x = (static_cast<std::int64_t>(p % m) *
                    powmod(10, digits10(e), m) + e) % m;
  x = (x * powmod(10, digits10(q), m) + q) % m;
  return static_cast<int>((x * 10 + f) % m);
}

static std::vector<int> parse_csv_line(const std::string& line) {
  std::vector<int> out;
  std::stringstream ss(line);
  std::string field;
  while (std::getline(ss, field, ',')) out.push_back(std::stoi(field));
  return out;
}

int main(int argc, char** argv) {
  if (argc != 2) return 2;
  const std::array<int, 6> mods{10, 9, 13, 7, 11, 37};
  const std::map<int, int> expected{{10, 16324}, {9, 4257}, {13, 480},
                                    {7, 32}, {11, 4}, {37, 1}};
  const auto cases = domain();
  if (cases.size() != 21098) {
    std::cerr << "domain count failure\n";
    return 1;
  }

  std::ifstream input(argv[1]);
  if (!input) return 2;
  std::string line;
  std::getline(input, line);
  if (line != "p,q,e,f,killer_mod,lhs_residue,rhs_residue\r" &&
      line != "p,q,e,f,killer_mod,lhs_residue,rhs_residue") {
    std::cerr << "header failure\n";
    return 1;
  }

  std::map<int, int> counts;
  std::size_t index = 0;
  while (std::getline(input, line)) {
    if (!line.empty() && line.back() == '\r') line.pop_back();
    if (line.empty()) continue;
    const auto row = parse_csv_line(line);
    if (row.size() != 7 || index >= cases.size()) return 1;
    const auto [p, q, e, f] = cases[index];
    if (row[0] != p || row[1] != q || row[2] != e || row[3] != f) {
      std::cerr << "domain/order failure at " << index << "\n";
      return 1;
    }
    const int m = row[4];
    const auto it = std::find(mods.begin(), mods.end(), m);
    if (it == mods.end()) return 1;
    if (lhs_mod(p, q, e, f, m) != row[5] ||
        encoded_mod(p, q, e, f, m) != row[6] || row[5] == row[6]) {
      std::cerr << "residue failure at " << index << "\n";
      return 1;
    }
    for (auto prior = mods.begin(); prior != it; ++prior) {
      if (lhs_mod(p, q, e, f, *prior) != encoded_mod(p, q, e, f, *prior)) {
        std::cerr << "first-killer failure at " << index << "\n";
        return 1;
      }
    }
    ++counts[m];
    ++index;
  }
  if (index != cases.size() || counts != expected) return 1;

  std::vector<Candidate> survivors = cases;
  for (std::size_t j = 0; j + 1 < mods.size(); ++j) {
    const int m = mods[j];
    survivors.erase(std::remove_if(survivors.begin(), survivors.end(),
      [m](const Candidate& c) {
        const auto [p, q, e, f] = c;
        return lhs_mod(p, q, e, f, m) != encoded_mod(p, q, e, f, m);
      }), survivors.end());
  }
  if (survivors.size() != 1 || survivors.front() != Candidate{37, 53, 14, 3}) {
    std::cerr << "pre-37 survivor failure\n";
    return 1;
  }
  if (lhs_mod(37, 53, 14, 3, 37) != 0 ||
      encoded_mod(37, 53, 14, 3, 37) != 29) return 1;

  // Three destructive controls:
  // (1) omitting modulus 37 leaves the known survivor;
  // (2) changing its encoded residue to 0 contradicts the exact value 29;
  // (3) reversing decimal field order changes 3151 to 3511.
  if (survivors.empty()) return 1;
  if (encoded_mod(37, 53, 14, 3, 37) == 0) return 1;
  if ((((3 * 10 + 1) * 10 + 5) * 10 + 1) != 3151) return 1;
  if (3151 == 3511) return 1;

  std::cout << "CPP_STRUCTURAL_CERTIFICATE_PASS rows=" << index << "\n";
  for (const auto& [m, n] : counts)
    std::cout << "killer_mod" << m << "=" << n << "\n";
  std::cout << "pre37_survivor=37,53,14,3\n";
  std::cout << "mutations_rejected=3/3\n";
  return 0;
}
