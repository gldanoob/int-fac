#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <map>
#include <pari/pari.h>
#include <string>
#include <vector>
using namespace std;
using Key = array<long, 3>;
struct Field {
  GEN disc, poly, div, mult;
  unsigned long mask;
  map<Key, bool> cache;
  bool split(GEN p, const vector<GEN> &roots) {
    pari_sp cp = avma;
    GEN root = gen_1;
    for (int j = 0; j < (int)roots.size(); j++)
      if (mask >> j & 1)
        root = Fp_mul(root, roots[j], p);
    root = Fp_mul(Fp_div(root, div, p), mult, p);
    GEN b = mod2(root) == mod2(disc) ? root : addii(root, p);
    GEN c = diviiexact(subii(sqri(b), disc), shifti(p, 2));
    GEN f = qfbred(mkqfb(p, b, c, disc));
    Key key = {itos(gel(f, 1)), itos(gel(f, 2)), itos(gel(f, 3))};
    auto it = cache.find(key);
    if (it == cache.end())
      it = cache.emplace(key, lg(FpX_roots(FpX_red(poly, p), p)) > 1).first;
    avma = cp;
    return it->second;
  }
};
int main(int argc, char **argv) {
  if (argc != 6)
    return 1;
  long begin = atol(argv[1]), end = atol(argv[2]);
  pari_init(128000000, 500000);
  ifstream in(argv[3]);
  string sa, sb, sc;
  in >> sa >> sb >> sc;
  GEN A = strtoi(sa.c_str()), B = strtoi(sb.c_str()), C = strtoi(sc.c_str());
  int nf;
  in >> nf;
  vector<Field> fields;
  for (int i = 0; i < nf; i++) {
    long d, a, b, c;
    in >> d >> a >> b >> c;
    string f = "x^3+(" + to_string(c) + ")*x^2+(" + to_string(b) + ")*x+(" +
               to_string(a) + ")";
    fields.push_back({stoi(d), gp_read_str(f.c_str()), gen_1, gen_1, 0, {}});
  }
  ifstream sin(argv[5]);
  int nb;
  sin >> nb;
  vector<GEN> basis;
  for (int j = 0; j < nb; j++) {
    long v;
    sin >> v;
    basis.push_back(stoi(v));
  }
  for (Field &f : fields) {
    string v;
    long mult;
    sin >> f.mask >> v >> mult;
    f.div = strtoi(v.c_str());
    f.mult = stoi(mult);
  }
  FILE *out = fopen(argv[4], "w");
  const long lim = 1000000, block = 250000;
  vector<bool> comp(lim + 1);
  vector<pair<long, long>> sieve;
  for (long r = 2; r <= lim; r++)
    if (!comp[r]) {
      if (r * r <= lim)
        for (long t = r * r; t <= lim; t += r)
          comp[t] = true;
      ulong a = umodiu(A, r), b = umodiu(B, r), c = umodiu(C, r);
      if (r == 2) {
        for (int j = 0; j < 2; j++)
          if ((a * j + b * j + c) % 2 == 0)
            sieve.push_back({r, j});
      } else if (!a) {
        if (b)
          sieve.push_back({r, Fl_mul(r - c, Fl_inv(b, r), r)});
        else if (!c)
          return 2;
      } else {
        ulong disc = Fl_sub(Fl_mul(b, b, r), Fl_mul(4, Fl_mul(a, c, r), r), r);
        if (disc && krouu(disc, r) < 0)
          continue;
        ulong root = disc ? Fl_sqrt(disc, r) : 0,
              iv = Fl_inv(Fl_add(a, a, r), r);
        sieve.push_back({r, Fl_mul(Fl_sub(root, b, r), iv, r)});
        if (root)
          sieve.push_back({r, Fl_mul(Fl_neg(Fl_add(root, b, r), r), iv, r)});
      }
    }
  pari_sp cp = avma;
  long count = 0;
  for (long start = begin; start < end; start += block) {
    long size = min(block, end - start);
    vector<char> skip(size);
    for (auto [r, root] : sieve)
      for (long k = (root + r - start % r) % r; k < size; k += r)
        skip[k] = 1;
    for (long k = 0; k < size; k++)
      if (!skip[k]) {
        avma = cp;
        long j = start + k;
        GEN p = addii(C, mului(j, addii(B, mului(j, A))));
        if (!BPSW_psp(p))
          continue;
        vector<GEN> roots;
        for (GEN d : basis)
          roots.push_back(Fp_sqrt(modii(d, p), p));
        unsigned long lo = 0, hi = 0;
        for (int z = 0; z < nf; z++)
          if (!fields[z].split(p, roots)) {
            if (z < 64)
              lo |= 1UL << z;
            else
              hi |= 1UL << (z - 64);
          }
        fprintf(out, "%ld %lu %lu\n", j, lo, hi);
        count++;
      }
    fflush(out);
    fprintf(stderr, "BLOCK %ld count %ld\n", start + size, count);
    fflush(stderr);
  }
  fclose(out);
}
