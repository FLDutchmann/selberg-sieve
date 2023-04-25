import sieve


noncomputable theory

open_locale big_operators classical sieve

open finset real nat sieve.upper_bound_sieve

namespace sieve

@[simp]
def selberg_bounding_sum_at_level (s : sieve) (y : ℕ) : ℝ := 
  ∑ l in s.P.divisors, ite ((l*l:ℝ) ≤ y) (s.g l) 0  

def selberg_weights (s: sieve) (y : ℕ) : ℕ → ℝ := 
  λ d, ite ( (¬squarefree d) ∨ s.ω d = 0 ) 0 
  (d/s.ω d * s.g d * μ d / selberg_bounding_sum_at_level s y 
   * ∑ m in s.P.divisors, ite ((m:ℝ)^2 ≤ y / d^2 ∧ m.gcd d = 1) (s.g m) 0 )

--Important facts about the selberg weights
lemma selberg_weights_eq_dvds_sum (s: sieve) (y: ℕ) (d : ℕ) :
  s.ω d/d * s.selberg_weights y d = 1/s.selberg_bounding_sum_at_level y * μ d * 
                                    ∑ l in s.P.divisors, ite (l^2 ≤ y ∧ d ∣ l) (s.g l) 0 := sorry 

lemma selberg_weights_diagonalisation(s : sieve) (y: ℕ) (l : ℕ):
    ∑ d in s.P.divisors, ite (l ∣ d) (s.ω d / d * s.selberg_weights y d) 0 
  = s.g l * μ l / s.selberg_bounding_sum_at_level y := sorry


def selberg_μ_plus (s: sieve) (y : ℕ) : ℕ → ℝ  := lambda_squared_of_weights (s.selberg_weights y)

lemma weight_one_of_selberg (s: sieve) (y: ℕ) : s.selberg_weights y 1 = 1 := sorry

def selberg_ub_sieve (s: sieve) (y : ℕ) : upper_bound_sieve := ⟨ 
  s.selberg_μ_plus y,
  upper_moebius_of_lambda_sq (s.selberg_weights y) (s.weight_one_of_selberg y) ⟩ 


namespace selberg
-- prove for general lambda squared sieves
lemma main_sum_eq_diag_quad_form (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) :
  s.main_sum (s.selberg_μ_plus y) = ∑ l in s.P.divisors, 
              1/s.g l * (∑ d in s.P.divisors, ite (l ∣ d) (s.ω d/d * s.selberg_weights y d) 0)^2 := sorry 
 
lemma selberg_bound_simple_main_sum (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) :
  s.main_sum (s.selberg_μ_plus y) =  1 / (s.selberg_bounding_sum_at_level y) := sorry


lemma selberg_bound_weights (s : sieve) (hω_size : axiom_size_1 s) (y : ℕ) :
  ∀ n:ℕ, |s.selberg_weights y n| ≤ 1 := sorry

lemma selberg_bound_μ_plus (s : sieve) (hω_size : axiom_size_1 s) (y : ℕ) :
  ∀ n:ℕ, |s.selberg_μ_plus n| ≤ 3 ^ ν(n) := sorry

lemma selberg_bound_simple_err_sum (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) : 
  s.err_sum (s.selberg_μ_plus y) ≤ ∑ d in s.P.divisors, ite ((d:ℝ) ≤ y) (3^(ν d) * |s.R d|) 0 := sorry


theorem selberg_bound_simple (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, ite ((d:ℝ) ≤ y) (3^(ν d) * |s.R d|) 0 := 
  sorry 


end selberg

end sieve