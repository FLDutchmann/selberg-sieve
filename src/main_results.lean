/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import selberg

open_locale big_operators arithmetic_function

theorem fundamental_theorem_simple (s : sieve) (y : ℝ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ω d) * |s.R d| else 0 
    := s.selberg_bound_simple y hy
