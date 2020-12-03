#https://en.wikipedia.org/wiki/Shamir%27s_Secret_Sharing#Python_example
"""
The following Python implementation of Shamir's Secret Sharing is
released into the Public Domain under the terms of CC0 and OWFa:
https://creativecommons.org/publicdomain/zero/1.0/
http://www.openwebfoundation.org/legal/the-owf-1-0-agreements/owfa-1-0

See the bottom few lines for usage. Tested on Python 2 and 3.
"""

from __future__ import division
from __future__ import print_function

import random
import functools

# 12th Mersenne Prime
# (for this application we want a known prime number as close as
# possible to our security level; e.g.  desired security level of 128
# bits -- too large and all the ciphertext is large; too small and
# security is compromised)
_PRIME = 2 ** 127 - 1
# 13th Mersenne Prime is 2**521 - 1

_RINT = functools.partial(random.SystemRandom().randint, 0)

#Could use Fermat's primality test first to potentially save time
#https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes
def is_safe_prime(n, k):
  #if (n % 3) != 2: return False #if (n % 6) != 5: return False
  if (n % 12) != 11: return False #n > 7
  #assert jacobi(3, n) == 1 and jacobi(12, n) == 1
  return is_all_prime([(n - 1) >> 1, n], [k >> 2, k >> 1])
  #return is_prime((n - 1) >> 1, k >> 2) and is_prime(n, k >> 1)
#https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
def is_all_prime(nl, kl): #Miller-Rabin test for k rounds
  if any(n < 3 or (n & 1) == 0 for n in nl): return False
  r, d, idxs = [1 for _ in nl], [n - 1 for n in nl], [i for i in range(len(nl))]
  for i in idxs:
    while d[i] & 1 == 0: #write n as 2^r*d where d odd
      r[i] += 1; d[i] >>= 1
  while len(idxs) != 0:
    if any(not miller_rabin(nl[i], d[i], r[i]) for i in idxs): return False
    for i in idxs: kl[i] -= 1
    idxs = [i for i in idxs if kl[i] != 0]
  return True #probably prime
def is_prime(n, k): #Miller-Rabin test for k rounds
  return is_all_prime([n], [k])
  if n < 3 or (n & 1) == 0: return False
  r, d = 1, n - 1
  while d & 1 == 0:
    r += 1; d >>= 1
  while k != 0:
    k -= 1
    if not miller_rabin(n, d, r): return False
  return True #probably prime
def miller_rabin(n, d, r):
  a = random.randint(2, n - 2)
  x = pow(a, d, n)
  if x == 1 or x == n - 1: return True
  for _ in range(r - 1):
    x = pow(x, 2, n)
    if x == n - 1: return True
  else: return False #composite
def find_prime(slambda, tester=is_prime):
  while True:
    p = random.randint(1 << slambda, 1 << (slambda+1))
    if tester(p, slambda): return p
def mhp_psetup(slambda, tau):
  #RSA - generate 2 safe/Sophie Germain primes
  p = find_prime(slambda, is_safe_prime)
  q = find_prime(slambda, is_safe_prime)
  n = p * q
  gtilda = random.randint(0, n)
  #https://en.wikipedia.org/wiki/Euler%27s_totient_function#Computing_Euler's_totient_function
  phi = (p - 1) * (q - 1)
  twopowtau = (1 << tau) % (phi >> 1)
  g = -pow(gtilda, 2, n) % n
  if jacobi(g, n) != 1: raise ValueError
  h = pow(g, twopowtau, n)
  return tau, n, g, h
def mhp_pgen(pp, s):
  tau, n, g, h = pp
  r = random.randint(1, n * n)
  return pow(g, r, n), (pow(h, r, n) * s) % n
def mhp_psolve(pp, z):
  tau, n, g, h = pp
  u, v = z
  twopowtau = (1 << tau)
  #print(n, u, v, twopowtau)
  w = pow(u, twopowtau, n)
  invw = _extended_gcd(w, n)
  return (v * invw[0]) % n
def mhp_eval(mult, pp, zs):
  tau, n, g, h = pp
  utilda, vtilda = 1, 1
  for u, v in zs:
    utilda, vtilda = mult(utilda, u) % n, mult(vtilda, v) % n
  return utilda, vtilda
def rand_j_n(n):
  while True:
    p = random.randint(0, n)
    if jacobi(p, n) == 1: return p
#https://en.wikipedia.org/wiki/Jacobi_symbol
def jacobi(n, k):
  if k <= 0 or k % 2 == 0: raise ValueError
  n %= k
  t = 1
  while n != 0:
    while n % 2 == 0:
      n //= 2
      r = k % 8
      if r == 3 or r == 5: t = -t
    n, k = k, n
    if n % 4 == 3 and k % 4 == 3: t = -t
    n %= k
  return t if k == 1 else 0
def _eval_at(poly, x, prime):
    """Evaluates polynomial (coefficient tuple) at x, used to generate a
    shamir pool in make_random_shares below.
    """
    accum = 0
    for coeff in reversed(poly):
        accum *= x
        accum += coeff
        accum %= prime
    return accum

def make_random_shares(minimum, shares, prime=_PRIME):
    """
    Generates a random shamir pool, returns the secret and the share
    points.
    """
    if minimum > shares:
        raise ValueError("Pool secret would be irrecoverable.")
    poly = [_RINT(prime - 1) for i in range(minimum)]
    points = [(i, _eval_at(poly, i, prime))
              for i in range(1, shares + 1)]
    return poly[0], points

def _extended_gcd(a, b):
    """
    Division in integers modulus p means finding the inverse of the
    denominator modulo p and then multiplying the numerator by this
    inverse (Note: inverse of A is B such that A*B % p == 1) this can
    be computed via extended Euclidean algorithm
    http://en.wikipedia.org/wiki/Modular_multiplicative_inverse#Computation
    """
    x = 0
    last_x = 1
    y = 1
    last_y = 0
    while b != 0:
        quot = a // b
        a, b = b, a % b
        x, last_x = last_x - quot * x, x
        y, last_y = last_y - quot * y, y
    return last_x, last_y

def _divmod(num, den, p):
    """Compute num / den modulo prime p

    To explain what this means, the return value will be such that
    the following is true: den * _divmod(num, den, p) % p == num
    """
    inv, _ = _extended_gcd(den, p)
    return num * inv

#multiplication via Karatsuba or faster method...
def mulpoly(poly1, poly2, p): #Kronecker substitution...
  lp1, lp2 = len(poly1), len(poly2)
  result = [0 for _ in range(lp1+lp2-1)]
  for i in range(len(poly1)):
    for j in range(len(poly2)):
      result[i + j] = (result[i + j] + (poly1[i] * poly2[j]) % p) % p
  return result
def addpoly(poly1, poly2, p):
  lp1, lp2 = len(poly1), len(poly2)
  result = [0 for _ in range(max(lp1, lp2))]
  for i in range(len(result)):
    offs1, offs2, offsr = lp1 - 1 - i, lp2 - 1 - i, len(result) - 1 - i
    if i >= lp2: result[offsr] = poly1[offs1]; continue
    if i >= lp1: result[offsr] = poly2[offs2]; continue
    result[offsr] += (poly1[offs1] + poly2[offs2]) % p
  return result
def _lagrange_to_poly(x_s, y_s, p):
  k = len(x_s)
  assert k == len(set(x_s)), "points must be distinct"
  poly = []
  for i in range(k):
    num, den = [y_s[i]], 1
    for l in range(k):
      if i == l: continue
      num = mulpoly([1, -x_s[l]], num, p)
      den *= (x_s[i] - x_s[l]) % p
    inv, _ = _extended_gcd(den, p)
    poly = addpoly(mulpoly(num, [inv], p), poly, p)
  return list(reversed(poly))
def _lagrange_interpolate(x, x_s, y_s, p):
    """
    Find the y-value for the given x, given n (x, y) points;
    k points will define a polynomial of up to kth order.
    """
    k = len(x_s)
    assert k == len(set(x_s)), "points must be distinct"
    def PI(vals):  # upper-case PI -- product of inputs
        accum = 1
        for v in vals:
            accum *= v
        return accum
    nums = []  # avoid inexact division
    dens = []
    for i in range(k):
        others = list(x_s)
        cur = others.pop(i)
        nums.append(PI(x - o for o in others))
        dens.append(PI(cur - o for o in others))
    den = PI(dens)
    #print(nums, dens)
    num = sum([_divmod(nums[i] * den * y_s[i] % p, dens[i], p)
               for i in range(k)])
    return (_divmod(num, den, p) + p) % p

def recover_secret(shares, prime=_PRIME):
    """
    Recover the secret from share points
    (x, y points on the polynomial).
    """
    if len(shares) < 2:
        raise ValueError("need at least two shares")
    x_s, y_s = zip(*shares)
    return _lagrange_interpolate(0, x_s, y_s, prime)

def main():
    """Main function"""
    """
    pp = mhp_psetup(128, 128)
    s = rand_j_n(pp[1])
    print("Secret: ", s)
    z = mhp_pgen(pp, s)
    scomp = mhp_psolve(pp, z)
    ztilda = mhp_eval(lambda a, b: a * b, pp, [z])
    print("Secret recovered: ", scomp)
    """
    def mhp_test(pp):
      n, d = 4, 3
      r = 4
      m = r + d
      s = rand_j_n(pp[1])
      print("Secret", s)
      #while True:
      #  p = find_prime(s.bit_length()+1)
      #  if p > s and p > n: break
      #print(pp[1].bit_length(), p.bit_length(), s.bit_length())
      p = pp[1]
      y = [rand_j_n(pp[1]) for _ in range(m)]
      poly = [s] + [rand_j_n(pp[1]) for _ in range(r-1)]
      si = [_eval_at(poly, y[i], p) for i in range(r+1)]
      #si = [_eval_at(poly, y[i], p) % pp[1] for i in range(r+1+1)]
      assert poly == _lagrange_to_poly(y[1:r+1], si[1:], p)
      assert s == _lagrange_interpolate(0, y[:r+1], si, p)
      fakes = [rand_j_n(pp[1]) for _ in range(m - r)]
      si = si + fakes
      assert len(si) == m + 1
      subshares = [[] for _ in si]
      puzzles = [[] for _ in si]
      for i in range(m):
        prod = 1
        for q in range(n-1):
          subshares[i].append(rand_j_n(pp[1]))
          puzzles[i].append(mhp_pgen(pp, subshares[i][q]))
          prod = (prod * subshares[i][q]) % pp[1]
        inv = _extended_gcd(prod, pp[1])
        subshares[i].append((si[i+1] * inv[0]) % pp[1])
        puzzles[i].append(mhp_pgen(pp, subshares[i][n-1]))
      sk = []
      for i in range(m):
        prod = 1
        for q in range(n):
          prod = (prod * subshares[i][q]) % pp[1]
        sk.append(prod)
      assert sk == si[1:]
      s0 = si[0]
      #print([mhp_psolve(pp, mhp_pgen(pp, si[i])) for i in range(m)])
      sk = [mhp_psolve(pp, mhp_eval(lambda a, b: a * b, pp, puzzles[i])) for i in range(m)]
      for k in range(m):
        polyprime = _lagrange_to_poly(y[1:1+1+k], sk[:1+k], p)
        print("Secret recovered: ", _lagrange_interpolate(0, y[1:1+1+k], sk[:1+k], p))
        ver = _eval_at(polyprime, y[0], p) == s0
        print("Verification check: ", ver)
        if ver == True: break
        if k >= r: assert False
    import timeit
    output = []
    for slambda in [128, 256, 512, 1024, 2048, 4096]:
      for tau in [1024*1024, 1024*1024*2, 1024*1024*4, 1024*1024*8]:
        pp = mhp_psetup(slambda, tau)
        output.append((slambda, tau, timeit.timeit(lambda: mhp_test(pp), number=1)))
        print(output[-1])
    print(output)
#Warm-up problem from https://www.youtube.com/watch?v=0Hl75Pap6iY
#https://rosettacode.org/wiki/Chinese_remainder_theorem#Python_3.6
def chinese_remainder(n, a):
    from functools import reduce
    sum = 0
    prod = reduce(lambda a, b: a*b, n)
    for n_i, a_i in zip(n, a):
        p = prod // n_i
        sum += a_i * mul_inv(p, n_i) * p
    return sum % prod
def mul_inv(a, b):
    b0 = b
    x0, x1 = 0, 1
    if b == 1: return 1
    while a > 1:
        q = a // b
        a, b = b, a%b
        x0, x1 = x1 - q * x0, x0
    if x1 < 0: x1 += b0
    return x1
#https://www.rookieslab.com/posts/extended-euclid-algorithm-to-find-gcd-bezouts-coefficients-python-cpp-code
def extended_euclid_gcd(a, b):
    """
    Returns a list `result` of size 3 where:
    Referring to the equation ax + by = gcd(a, b)
        result[0] is gcd(a, b)
        result[1] is x
        result[2] is y 
    """
    s = 0; old_s = 1
    t = 1; old_t = 0
    r = b; old_r = a

    while r != 0:
        quotient = old_r//r # In Python, // operator performs integer or floored division
        # This is a pythonic way to swap numbers
        # See the same part in C++ implementation below to know more
        old_r, r = r, old_r - quotient*r
        old_s, s = s, old_s - quotient*s
        old_t, t = t, old_t - quotient*t
    return [old_r, old_s, old_t]
#https://codereview.stackexchange.com/questions/1526/finding-all-k-subset-partitions
def subsets_k(collection, k): yield from partition_k(collection, k, k)
def partition_k(collection, min, k):
  if len(collection) == 1:
    yield [ collection ]
    return

  first = collection[0]
  for smaller in partition_k(collection[1:], min - 1, k):
    if len(smaller) > k: continue
    # insert `first` in each of the subpartition's subsets
    if len(smaller) >= min:
      for n, subset in enumerate(smaller):
        yield smaller[:n] + [[ first ] + subset]  + smaller[n+1:]
    # put `first` in its own subset 
    if len(smaller) < k: yield [ [ first ] ] + smaller
def solve_num_theory():
  import math
  lbound = int(math.sqrt(100000))
  print([(m,m*m) for (m, n) in ((n,(n-1)*(n+1)/1001) for n in range(lbound, 999)) if int(n)==n])
  factors = [] #7*11*13=1001
  for i in range(2, int(math.sqrt(1001))):
    if 1001 % i == 0: factors.append(i)
  print([(k, k*k) for k in (chinese_remainder(factors, [1 if (1 << j) & i != 0 else -1 for j in range(len(factors))]) for i in range(1<<len(factors))) if k >= lbound and k <= 999])
  for s1, s2 in subsets_k(factors, 2):
    s1, s2 = math.prod(s1), math.prod(s2)
    gcdbezout = extended_euclid_gcd(s2, s1)
    assert gcdbezout[0] == 1
    for t in range((1-gcdbezout[1])//s1, (s1-gcdbezout[1])//s1+1):
      b, a = (s1 * t + gcdbezout[1]*2), (s2 * t - gcdbezout[2] * 2)
      assert s2 * b - s1 * a == 2 and s1*a+1==s2*b-1
      res = -(s1*a+1) if s1*a+1 < 0 else s1*a+1
      if res >= lbound:
        print(s1, s2, gcdbezout, t, a, b, a * b, res, res * res)
solve_num_theory()
"""
    secret, shares = make_random_shares(minimum=3, shares=6)

    print('Secret:                                                     ',
          secret)
    print('Shares:')
    if shares:
        for share in shares:
            print('  ', share)

    print('Secret recovered from minimum subset of shares:             ',
          recover_secret(shares[:3]))
    print('Secret recovered from a different minimum subset of shares: ',
          recover_secret(shares[-3:]))
    """
if __name__ == '__main__':
    main()
    
