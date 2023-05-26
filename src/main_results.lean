import selberg

theorem fundamental_theorem_simple (s : sieve) (y : ℝ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 
    := sieve.selberg_bound_simple

