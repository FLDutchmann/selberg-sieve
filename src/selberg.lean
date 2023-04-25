import sieve


noncomputable theory

open_locale big_operators classical sieve

open finset real nat sieve.upper_bound_sieve

namespace sieve

set_option profiler true

@[simp]
def selberg_bounding_sum_at_level (s : sieve) (y : ℕ) : ℝ := 
  ∑ l in s.P.divisors, if (l*l:ℝ) ≤ y then s.g l else 0  

def selberg_weights (s: sieve) (y : ℕ) : ℕ → ℝ := 
  λ d, if (d ∣ s.P) 
  then (d/s.ω d * s.g d * μ d / selberg_bounding_sum_at_level s y 
   * ∑ m in s.P.divisors, if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0 ) 
  else 0

--Important facts about the selberg weights
lemma selberg_weights_eq_dvds_sum (s: sieve) (y: ℕ) (d : ℕ) :
  s.ω d/d * s.selberg_weights y d = 1/s.selberg_bounding_sum_at_level y * μ d * 
                                    ∑ l in s.P.divisors, if d ∣ l ∧ l^2 ≤ y then s.g l else 0 :=
begin
  by_cases h_dvd : d ∣ s.P, 
  swap, -- if ¬d ∣ s.P then both sides are zero
  { dsimp only [selberg_weights], rw if_neg h_dvd,
    rw sum_eq_zero, ring,
    intros l hl, rw mem_divisors at hl,
    rw if_neg, push_neg, intro h,
    exfalso, exact h_dvd (dvd_trans h hl.left), },
  
  dsimp only [selberg_weights],
  let S := s.selberg_bounding_sum_at_level y,
  have hω_cancel : (s.ω d/↑d) * (↑d/s.ω d) = 1,
  { rw div_mul_div_cancel, rw div_self,
    apply ne_of_gt, exact s.hω_pos_of_dvd_P h_dvd,
    rw cast_ne_zero,
    exact ne_zero_of_dvd_ne_zero s.hP_ne_zero h_dvd, },
  have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.hP_ne_zero h_dvd,
  
  rw if_pos h_dvd,
  have := 
  calc  s.ω d/↑d * (↑d/s.ω d * s.g d * ↑(μ d) / S 
                * ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0))

      = ((1/S) * (((s.ω d/↑d) * (↑d/s.ω d)) * s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0))) 
        : by ring 

  ... = (1/S) * (s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0)) 
        : by { rw hω_cancel, ring },
  rw this, clear this,
  
  suffices: (s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0))
          = μ d * ∑ l in s.P.divisors, if d ∣ l ∧ l^2 ≤ y then s.g l else 0,
  { rw this, ring }, 
  
  calc s.g d * ↑(μ d) * ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then s.g m else 0)

      = ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then  s.g d * ↑(μ d) * s.g m else 0)
        : by {
          rw mul_sum, apply sum_congr rfl, intros d hd,
          rw ite_mul_zero_right, }
  
  ... = ∑ m in s.P.divisors, (if (m*d)^2 ≤ y ∧ m.coprime d then  s.g (m*d) * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq _ _ iff.rfl,
          intro h, rw s.hg_mult.right m d h.right.right, ring,}

  ... = ∑ m l in s.P.divisors, (if l=m*d ∧ ((m*d)^2 ≤ y ∧ m.coprime d) then  s.g (m*d) * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros m hm,
          rw aux.sum_intro, intro h,
          rw mem_divisors at *,
          split,
          exact coprime.mul_dvd_of_dvd_of_dvd h.right hm.left h_dvd,
          exact s.hP_ne_zero, }    

  ... = ∑ l m in s.P.divisors, (if m=l/d ∧ d ∣ l ∧ (l^2 ≤ y) then  s.g l * ↑(μ d) else 0)
        : by { 
          rw sum_comm, apply sum_congr rfl, intros l hl,
          apply sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq,
          split,
          { intro h, split,  rw nat.div_eq_of_eq_mul_left _ h.left, 
            rw zero_lt_iff, exact hd_ne_zero, split,
            use m, rw h.left, ring, rw h.left, exact h.right.left,  },
          { intro h, rcases h with ⟨ hmld, hdl, hly⟩,
            have hmdl : m*d=l,
            { rw hmld, rw nat.div_mul_cancel hdl, },
            split, rw hmdl,
            split, rw hmdl, exact hly,
            apply aux.coprime_of_mul_squarefree, rw hmdl, 
            exact s.sqfree_of_mem_dvd_P hl }, 
          intro h, rw h.left.left, }

  ... = ∑ l in s.P.divisors, (if d ∣ l ∧ (l^2 ≤ y) then  s.g l * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros l hl,
          rw ←aux.sum_intro,
          intro h, rw mem_divisors at *, split,
          calc l / d ∣ l : nat.div_dvd_of_dvd h.left
                 ... ∣ s.P : hl.left,
          exact hl.right }

  ... = μ d * ∑ l in s.P.divisors, if d ∣ l ∧ l^2 ≤ y then s.g l else 0 
        : by { 
          conv{ to_lhs, congr, skip, funext, rw ite_mul_zero_left},
          rw ←sum_mul, ring }

end

lemma selberg_weights_diagonalisation(s : sieve) (y: ℕ) (l : ℕ):
    ∑ d in s.P.divisors, (if l ∣ d then s.ω d / d * s.selberg_weights y d else 0) 
  = s.g l * μ l / s.selberg_bounding_sum_at_level y := 
begin
  sorry
end


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
              1/s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d/d * s.selberg_weights y d else 0)^2 := sorry 
 
lemma selberg_bound_simple_main_sum (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) :
  s.main_sum (s.selberg_μ_plus y) =  1 / (s.selberg_bounding_sum_at_level y) := sorry


lemma selberg_bound_weights (s : sieve) (hω_size : axiom_size_1 s) (y : ℕ) :
  ∀ n:ℕ, |s.selberg_weights y n| ≤ 1 := sorry

lemma selberg_bound_μ_plus (s : sieve) (hω_size : axiom_size_1 s) (y : ℕ) :
  ∀ n:ℕ, |s.selberg_μ_plus n| ≤ 3 ^ ν(n) := sorry

lemma selberg_bound_simple_err_sum (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) : 
  s.err_sum (s.selberg_μ_plus y) ≤ ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := sorry


theorem selberg_bound_simple (s : sieve) (hω_size : axiom_size_1 s) 
                      (y : ℕ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := 
  sorry 


end selberg

end sieve