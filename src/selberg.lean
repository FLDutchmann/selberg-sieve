import sieve


noncomputable theory

open_locale big_operators classical sieve

open finset real nat sieve.upper_bound_sieve

namespace sieve

set_option profiler true

@[simp]
def selberg_bounding_sum_at_level (s : sieve) (y : ℝ) : ℝ := 
  ∑ l in s.P.divisors, if (l:ℝ)^2 ≤ y then s.g l else 0  

lemma selberg_bounding_sum_pos (s: sieve) (y : ℝ) (hy: 1 ≤ y):
  0 < s.selberg_bounding_sum_at_level y :=
begin
  dsimp only [selberg_bounding_sum_at_level], 
  rw ←sum_filter,
  apply sum_pos,
  intros l hl,
  rw [mem_filter, mem_divisors] at hl,
  apply s.hg_pos,
  exact hl.left.left,
  rw finset.nonempty,
  use 1, rw [mem_filter, mem_divisors],
  split, split, exact one_dvd _, exact s.hP_ne_zero,
  rw cast_one, linarith,
end

def selberg_weights (s: sieve) (y : ℝ) : ℕ → ℝ := 
  λ d, if (d ∣ s.P) 
  then (d/s.ω d * s.g d * μ d / selberg_bounding_sum_at_level s y 
   * ∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0 ) 
  else 0

--Important facts about the selberg weights
lemma selberg_weights_eq_dvds_sum (s: sieve) (y: ℝ) (d : ℕ) :
  s.ω d/d * s.selberg_weights y d = 1/s.selberg_bounding_sum_at_level y * μ d * 
                                    ∑ l in s.P.divisors, if d ∣ l ∧ (l:ℝ)^2 ≤ y then s.g l else 0 :=
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
                * ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0))

      = ((1/S) * (((s.ω d/↑d) * (↑d/s.ω d)) * s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0))) 
        : by ring 

  ... = (1/S) * (s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0)) 
        : by { rw hω_cancel, ring },
  rw this, clear this,
  
  suffices: (s.g d * ↑(μ d)  
                * ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0))
          = μ d * ∑ l in s.P.divisors, if d ∣ l ∧ (l:ℝ)^2 ≤ y then s.g l else 0,
  { rw this, ring }, 
  
  calc s.g d * ↑(μ d) * ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0)

      = ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then  s.g d * ↑(μ d) * s.g m else 0)
        : by {
          rw mul_sum, apply sum_congr rfl, intros d hd,
          rw ite_mul_zero_right, }
  
  ... = ∑ m in s.P.divisors, (if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then  s.g (m*d) * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq _ _ iff.rfl,
          intro h, rw s.hg_mult.right m d h.right.right, ring,}

  ... = ∑ m l in s.P.divisors, (if l=m*d ∧ ((m*d:ℝ)^2 ≤ y ∧ m.coprime d) then  s.g (m*d) * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros m hm,
          rw aux.sum_intro, intro h,
          rw mem_divisors at *,
          split,
          exact coprime.mul_dvd_of_dvd_of_dvd h.right hm.left h_dvd,
          exact s.hP_ne_zero, }    

  ... = ∑ l m in s.P.divisors, (if m=l/d ∧ d ∣ l ∧ ((l:ℝ)^2 ≤ y) then  s.g l * ↑(μ d) else 0)
        : by { 
          rw sum_comm, apply sum_congr rfl, intros l hl,
          apply sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq,
          split,
          { intro h, split,  rw nat.div_eq_of_eq_mul_left _ h.left, 
            rw zero_lt_iff, exact hd_ne_zero, split,
            use m, rw h.left, ring, rw h.left, rw cast_mul, exact h.right.left,  },
          { intro h, rcases h with ⟨ hmld, hdl, hly⟩,
            have hmdl : m*d=l,
            { rw hmld, rw nat.div_mul_cancel hdl, },
            split, rw hmdl,
            split, rw ←cast_mul, rw hmdl, exact hly,
            apply aux.coprime_of_mul_squarefree, rw hmdl, 
            exact s.sqfree_of_mem_dvd_P hl }, 
          intro h, rw h.left.left, }

  ... = ∑ l in s.P.divisors, (if d ∣ l ∧ ((l:ℝ)^2 ≤ y) then  s.g l * ↑(μ d) else 0)
        : by {
          apply sum_congr rfl, intros l hl,
          rw ←aux.sum_intro,
          intro h, rw mem_divisors at *, split,
          calc l / d ∣ l : nat.div_dvd_of_dvd h.left
                 ... ∣ s.P : hl.left,
          exact hl.right }

  ... = μ d * ∑ l in s.P.divisors, if d ∣ l ∧ (l:ℝ)^2 ≤ y then s.g l else 0 
        : by { 
          conv{ to_lhs, congr, skip, funext, rw ite_mul_zero_left},
          rw ←sum_mul, ring }

end

lemma selberg_weights_diagonalisation(s : sieve) (y: ℝ) (l : ℕ) (hl: l ∈ s.P.divisors):
    ∑ d in s.P.divisors, (if l ∣ d then s.ω d / d * s.selberg_weights y d else 0) 
  = if (l:ℝ)^2 ≤ y then s.g l * μ l / s.selberg_bounding_sum_at_level y else 0 := 
begin
  let S := s.selberg_bounding_sum_at_level y,

  calc ∑ d in s.P.divisors, (if l ∣ d then s.ω d / d * s.selberg_weights y d else 0) 
      
      = ∑ d in s.P.divisors, (if l ∣ d then 1/S * μ d * ∑ k in s.P.divisors, (if d ∣ k ∧ (k:ℝ)^2 ≤ y then s.g k else 0) else 0)
        : by conv{ to_lhs, congr, skip, funext, rw selberg_weights_eq_dvds_sum, }
      
  ... = ∑ d k in s.P.divisors, (if l ∣ d ∧ d ∣ k ∧ (k:ℝ)^2 ≤ y  then  s.g k * (1/S) * μ d else 0)
        : by { 
          apply sum_congr rfl, intros d hd, 
          rw ←boole_mul,rw mul_sum, rw mul_sum, 
          apply sum_congr rfl, intros k hk, 
          rw ←ite_mul_zero_right, rw ←ite_and_mul_zero,
          apply aux.ite_eq_of_iff_eq, refl,
          intro h, ring,  }
  
  ... = ∑ k in s.P.divisors, (if (k:ℝ)^2 ≤ y then  (∑ d in s.P.divisors, if l ∣ d ∧ d ∣ k  then μ d else 0) * s.g k * (1/S) else 0)
        : by {
          rw sum_comm, apply sum_congr rfl, intros k hk,
          conv{to_rhs, rw ←boole_mul},
          rw sum_mul,rw sum_mul, rw mul_sum,
          apply sum_congr rfl, intros d hd,
          conv{to_rhs, congr, skip, rw ←ite_mul_zero_left, rw ←ite_mul_zero_left,}, 
          rw ←ite_and_mul_zero, 
          apply aux.ite_eq_of_iff_eq,
          split,
          { rintros ⟨ hld, hdk, hky ⟩, exact ⟨hky, hld, hdk⟩, },
          { rintros ⟨ hky, hld, hdk ⟩, exact ⟨hld, hdk, hky⟩, },
          intro h, ring }
   
  ... = ∑ k in s.P.divisors, if k=l ∧ (l:ℝ)^2 ≤ y then s.g l * μ l / S else 0 
        : by {
          apply sum_congr rfl, intros k hk,
          rw aux.moebius_inv_dvd_lower_bound_real s.hP l k,
          rw ←ite_mul_zero_left, rw ←ite_mul_zero_left,
          rw ←ite_and,
          apply aux.ite_eq_of_iff_eq,
          split, 
          { rintros ⟨hky, hlk⟩, rw hlk, exact ⟨rfl, hky⟩ },
          { rintros ⟨hkl, hly⟩, rw hkl, exact ⟨hly, rfl⟩ },
          intro h, rw h.left.right, ring,
          rw mem_divisors at hk, exact hk.left, }
  
  ... = if (l:ℝ)^2 ≤ y then s.g l * μ l / S else 0 
        : by { rw ←aux.sum_intro, intro h, exact hl } 
end


def selberg_μ_plus (s: sieve) (y : ℝ) : ℕ → ℝ  := lambda_squared_of_weights (s.selberg_weights y)

lemma weight_one_of_selberg (s: sieve) (y: ℝ) (hy: 1 ≤ y): s.selberg_weights y 1 = 1 := 
begin
  dsimp only [selberg_weights],
  rw if_pos,
  rw s.hω_mult.left,
  rw s.hg_mult.left,
  rw cast_one, rw arithmetic_function.moebius_apply_one, rw int.cast_one, rw mul_one, rw div_one, rw mul_one,
  have : s.selberg_bounding_sum_at_level y = ∑ (m : ℕ) in s.P.divisors, ite ((↑m * 1) ^ 2 ≤ y ∧ m.coprime 1) (s.g m) 0,
  { dsimp only [selberg_bounding_sum_at_level], rw sum_congr rfl, intros l hl,
    apply aux.ite_eq_of_iff_eq, simp, intro h, refl, },
  rw ←this, apply one_div_mul_cancel,
  apply ne_of_gt, exact s.selberg_bounding_sum_pos y hy,
  exact one_dvd _,
end

def selberg_ub_sieve (s: sieve) (y : ℝ) (hy : 1 ≤ y): upper_bound_sieve := ⟨ 
  s.selberg_μ_plus y,
  upper_moebius_of_lambda_sq (s.selberg_weights y) (s.weight_one_of_selberg y hy) ⟩ 


namespace selberg
-- proved for general lambda squared sieves
lemma main_sum_eq_diag_quad_form (s : sieve) (y : ℝ) :
  s.main_sum (s.selberg_μ_plus y) = ∑ l in s.P.divisors, 
              1/s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d/d * s.selberg_weights y d else 0)^2 := 
begin 
  apply lambda_sq_main_sum_eq_diag_quad_form,
end
 
lemma selberg_bound_simple_main_sum (s : sieve) (y : ℝ) (hy: 1 ≤ y) :
  s.main_sum (s.selberg_μ_plus y) =  1 / (s.selberg_bounding_sum_at_level y) := 
begin
  let S :=  s.selberg_bounding_sum_at_level y,
  rw main_sum_eq_diag_quad_form,
  calc  ∑ l in s.P.divisors, 1 / s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d / ↑d * s.selberg_weights y d else 0) ^ 2
     
      = ∑ l in s.P.divisors, 1 / s.g l * (if (l:ℝ)^2 ≤ y then s.g l * μ l / S else 0 )^2
        : by {
          apply sum_congr rfl, intros l hl,
          rw s.selberg_weights_diagonalisation y l hl, }

  ... = ∑ l in s.P.divisors, 1/ s.g l * if (l:ℝ)^2 ≤ y then (s.g l)^2 * (1/S)^2 else 0 
        : by {
          apply sum_congr rfl, intros l hl,
          rw sq,
          rw ←ite_and_mul_zero,
          rw aux.ite_eq_of_iff_eq, tauto,

          intro h,
          calc  s.g l * ↑(μ l) / S * (s.g l * ↑(μ l) / S)
               = s.g l ^ 2 * ↑(μ l)^2 *(1/ S)^2 : by ring
           ... = s.g l ^ 2 * (1/ S)^2 
                 : by { 
                   rw ←int.cast_pow, rw aux.moebius_sq_eq_one_of_squarefree (s.sqfree_of_mem_dvd_P hl), 
                   rw int.cast_one, ring } }  
  
  ... = ∑ l in s.P.divisors, (if (l:ℝ)^2 ≤ y then s.g l else 0) * (1/S)^2 
        : by {
          apply sum_congr rfl, intros l hl,
          rw ite_mul_zero_left, rw ←mul_assoc,
          rw ←ite_mul_zero_right, rw (sq $ s.g l), rw ←mul_assoc,
          rw mem_divisors at hl,
          rw one_div_mul_cancel, rw one_mul, apply ne_of_gt, exact s.hg_pos l hl.left, }

  ... = 1/S  
        : by{
          rw ←sum_mul, rw sq, rw ←mul_assoc, 
          calc S * (1/S) * (1/S) = 1/S 
          : by {rw mul_one_div_cancel, ring, apply ne_of_gt, 
                apply s.selberg_bounding_sum_pos y hy } },
  
end


lemma selberg_bound_weights (s : sieve) (y : ℝ) :
  ∀ n:ℕ, |s.selberg_weights y n| ≤ 1 := sorry

lemma selberg_bound_μ_plus (s : sieve) (y : ℝ) :
  ∀ n:ℕ, |s.selberg_μ_plus n| ≤ 3 ^ ν(n) := sorry

lemma selberg_bound_simple_err_sum (s : sieve) (y : ℝ) (hy: 1 ≤ y) : 
  s.err_sum (s.selberg_μ_plus y) ≤ ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := sorry


theorem selberg_bound_simple (s : sieve) (y : ℝ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := 
  sorry 


end selberg

end sieve