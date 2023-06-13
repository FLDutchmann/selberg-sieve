/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import sieve


noncomputable theory

open_locale big_operators classical sieve

open finset real nat sieve.upper_bound_sieve

namespace sieve

--set_option profiler true

@[simp]
def selberg_bounding_sum_at_level (s : sieve) (y : ℝ) : ℝ := 
  ∑ l in s.P.divisors, if (l:ℝ)^2 ≤ y then s.g l else 0  

lemma selberg_bounding_sum_nonneg (s: sieve) (y : ℝ):
  0 ≤ s.selberg_bounding_sum_at_level y :=
begin
  dsimp only [selberg_bounding_sum_at_level], 
  rw ←sum_filter,
  apply sum_nonneg,
  intros l hl,
  rw [mem_filter, mem_divisors] at hl,
  apply le_of_lt, apply s.hg_pos,
  exact hl.left.left,
end


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

lemma selberg_weights_eq_zero (s : sieve) (y : ℝ) (d : ℕ) (hd : ¬(d:ℝ)^2 ≤ y) : 
  s.selberg_weights y d = 0 :=
begin
  dsimp only [selberg_weights],
  by_cases h:d∣s.P,
  swap, 
  rw if_neg h,
  rw if_pos h,
  rw [mul_eq_zero_of_right _],
  rw [finset.sum_eq_zero], intros m hm,
  rw if_neg, 
  push_neg,
  intro hyp,
  exfalso,
  apply absurd hd,
  push_neg,
  calc ↑d^2 ≤ (↑m)^2 * (↑d)^2 : _
        ... ≤ y : _,
  have : 1 ≤ (m:ℝ), 
  { norm_cast,
    rw succ_le_iff,
    rw mem_divisors at hm,
    rw zero_lt_iff,
    exact ne_zero_of_dvd_ne_zero hm.2 hm.1 },
  apply le_mul_of_one_le_left,
  exact sq_nonneg d,
  rw one_le_sq_iff,
  linarith, linarith,
  rw ←mul_pow,
  exact hyp,
end

lemma selberg_weight_mul_mu_nonneg (s: sieve) (y : ℝ) (d : ℕ) (hdP : d ∣ s.P):
  0 ≤ s.selberg_weights y d * μ d :=
begin
  dsimp only [selberg_weights],
  rw if_pos hdP, rw mul_assoc,
  conv{ to_rhs, congr, skip, rw mul_comm, }, rw ←mul_assoc, 
  apply mul_nonneg, rw div_eq_mul_inv, rw mul_comm,
  rw ←mul_assoc, apply mul_nonneg, rw mul_comm, rw mul_assoc,
  apply mul_nonneg, apply mul_nonneg,
  apply div_nonneg,
  rw ←cast_zero, rw cast_le, apply nat.zero_le,
  apply le_of_lt, exact s.hω_pos_of_dvd_P hdP,
  apply le_of_lt, apply s.hg_pos d hdP,
  rw ←sq, apply sq_nonneg,
  rw inv_nonneg, exact s.selberg_bounding_sum_nonneg y,
  apply sum_nonneg, intros m hm,
  by_cases h : (↑m * ↑d) ^ 2 ≤ y ∧ m.coprime d,
  rw if_pos h, apply le_of_lt, exact s.hg_pos m (mem_divisors.mp hm).left,
  rw if_neg h,
end

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

theorem selberg_μ_plus_eq_zero (s: sieve) (y: ℝ) (d: ℕ) (hd: ¬ ↑d ≤ y): 
 s.selberg_μ_plus y d = 0 :=
begin
  apply lambda_squared_of_weights_eq_zero_of_support _ y _ d hd,
  apply s.selberg_weights_eq_zero,
end

def selberg_ub_sieve (s: sieve) (y : ℝ) (hy : 1 ≤ y): upper_bound_sieve := ⟨ 
  s.selberg_μ_plus y,
  upper_moebius_of_lambda_sq (s.selberg_weights y) (s.weight_one_of_selberg y hy) ⟩ 


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

example (m n P: ℕ) (hm : m ∣ P) (hn : n ∣ P) (hc : m.coprime n) : m*n ∣ P := coprime.mul_dvd_of_dvd_of_dvd hc hm hn

example (x y z: ℝ ) (hx : 0 < x) (h : y ≤ z) : (x * y ≤ x * z) := (mul_le_mul_left hx).mpr h

lemma selberg_bound_weights (s : sieve) (y : ℝ) (hy : 1 ≤ y) :
  ∀ d:ℕ, |s.selberg_weights y d| ≤ 1 := 
begin
  let S := s.selberg_bounding_sum_at_level y,
  let lam := s.selberg_weights y,
  intro d,
  by_cases hdP : d ∣ s.P,
  swap,
  { dsimp only [selberg_weights],
    rw if_neg hdP, simp only [zero_le_one, abs_zero] },
  have : S ≥ lam d * ↑(μ d)  * S,  
  calc  (∑ l in s.P.divisors, if (l:ℝ)^2 ≤ y then s.g l else 0)  

      = ∑ k l in s.P.divisors, if k = d.gcd l ∧ (l:ℝ)^2 ≤ y then s.g l else 0
        : by {
          rw sum_comm, apply sum_congr rfl, intros l hl,
          rw ←aux.sum_intro s.P.divisors ((l:ℝ)^2 ≤ y),
          intro h_le, rw mem_divisors,
          split, exact dvd_trans (nat.gcd_dvd_left d l) hdP, exact s.hP_ne_zero, }

  ... = ∑ k m l in s.P.divisors, if l=m*k ∧ m.coprime k ∧ k = d.gcd (m*k) ∧ (m*k:ℝ)^2 ≤ y then s.g m * s.g k else 0
        : by {
          apply sum_congr rfl, intros k hk, rw sum_comm, apply sum_congr rfl, intros l hl,
          rw aux.sum_intro s.P.divisors _ _ (l/k), 
          apply sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq, split,
          { rintros ⟨hmlk, hkdl, hly⟩, 
            have : l=m*k,
            { rw mul_comm, apply nat.eq_mul_of_div_eq_right,
              rw hkdl, apply (nat.gcd_dvd_right d l), exact eq_comm.mp hmlk },
            split, exact this,
            split, apply aux.coprime_of_mul_squarefree, rw ←this, exact s.sqfree_of_mem_dvd_P hl,
            split, rw ←this, exact hkdl,
            rw ←cast_mul, rw ←this, exact hly },
          { rintros ⟨hlmk, hmk, hkd, hmky⟩,
            split, rw eq_comm, apply nat.div_eq_of_eq_mul_left, rw zero_lt_iff,
            rw mem_divisors at hk, apply ne_zero_of_dvd_ne_zero s.hP_ne_zero hk.left,
            exact hlmk, split, rw ←hlmk at hkd, exact hkd,
            rw ←cast_mul at hmky, rw hlmk, exact hmky },
          intro h, rw h.right.left, apply s.hg_mult.right m k h.right.right.left,
          intro h, rw h.left, rw mem_divisors at *, split, 
          exact dvd_trans (div_dvd_of_dvd $ nat.gcd_dvd_right d l) hl.left, exact s.hP_ne_zero,
          intro n, apply classical.prop_decidable }
 
  ... = ∑ k in s.P.divisors, s.g k 
      * ∑ m in s.P.divisors, if m.coprime k ∧ k = d.gcd (m*k) ∧ (m*k:ℝ)^2 ≤ y then s.g m else 0
        : by {
          apply sum_congr rfl, intros k hk, rw mul_sum, apply sum_congr rfl, intros m hm,
          conv{to_rhs, rw mul_comm}, rw ←ite_mul_zero_left, rw aux.sum_intro,
          intro h, rw mem_divisors at *, split, apply coprime.mul_dvd_of_dvd_of_dvd h.left,
          exact hm.left, exact hk.left, exact s.hP_ne_zero, }  
        
  ... = ∑ k in s.P.divisors, if k ∣ d then s.g k
      * ∑ m in s.P.divisors, (if m.coprime k ∧ k = d.gcd (m*k) ∧ (m*k:ℝ)^2 ≤ y then s.g m else 0) else 0
        : by {
          apply sum_congr rfl, intros k hk, 
          by_cases hkd : k ∣ d,
          { rw if_pos hkd },
          { rw if_neg hkd, rw sum_eq_zero, ring,
            intros m hm, rw if_neg, push_neg, intros hmk hgcd, exfalso, 
            have h : d.gcd (m*k) ∣ d := nat.gcd_dvd_left d (m*k),
            rw ←hgcd at h, exact hkd h, } }

  ... = ∑ k in s.P.divisors, if k ∣ d then s.g k 
      * ∑ m in s.P.divisors, if (m*k:ℝ)^2 ≤ y ∧ m.coprime d  then s.g m else 0 else 0
        : by {
          rw sum_congr rfl, intros k hk, apply aux.ite_eq_of_iff_eq, exact iff.rfl,
          intro h, rw sum_congr rfl, intros m hm,
          apply aux.ite_eq_of_iff_eq,
          split,
          { rintros ⟨hmk, hkd, hmky⟩, split, swap,
            cases h.left with r hr,
            rw hr at hkd, rw mul_comm at hkd, rw nat.gcd_mul_right at hkd,
            have hk_zero : 0 < k,
            { rw zero_lt_iff, apply ne_zero_of_dvd_ne_zero _ h.left,
              apply ne_zero_of_dvd_ne_zero s.hP_ne_zero hdP, },
            have : r.coprime m,
            calc r.gcd m = r.gcd m * k / k : by rw nat.mul_div_cancel _ hk_zero
                     ... = k / k           : by rw ←hkd
                     ... = 1               : nat.div_self hk_zero,
            rw hr, apply coprime.mul_right hmk (coprime_comm.mp this),
            exact hmky, },
          { rintros ⟨hmky, hmd⟩, split, 
            apply coprime.coprime_dvd_right h.left, exact hmd, split,
            cases h.left with r hr, rw hr, rw mul_comm, rw nat.gcd_mul_right,
            have : r.coprime m, apply coprime.coprime_dvd_left (_:r∣d), rw coprime_comm,
            exact hmd, use k, rw hr, ring,
            dsimp only [coprime] at this, rw this, ring, 
            exact hmky },
          exact (λ_, rfl), }
        

  ... ≥ ∑ k in s.P.divisors, if k ∣ d then s.g k 
      * ∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0 else 0
        : by {
          rw ge_iff_le, apply sum_le_sum, intros k hk,
          by_cases hkd : k ∣ d,
          swap, 
          { rw if_neg hkd, rw if_neg hkd },
          rw if_pos hkd, rw if_pos hkd,
          apply (mul_le_mul_left (s.hg_pos k _)).mpr,
          apply sum_le_sum, intros m hm,
          
          have hmk: 0 ≤ (m:ℝ) * ↑k,
          { rw ←cast_mul, rw ←cast_zero, rw cast_le, apply nat.zero_le },
          have hmd: (m:ℝ) * ↑k ≤ (m:ℝ) * ↑d,
          { rw ←cast_mul, rw ←cast_mul, rw cast_le, 
            apply nat.mul_le_mul_of_nonneg_left, apply le_of_dvd _ hkd,
            rw zero_lt_iff, apply ne_zero_of_dvd_ne_zero s.hP_ne_zero hdP, },

          by_cases h: (↑m * ↑d)^2 ≤ y ∧ m.coprime d,
          { rw if_pos h,
                      
            have h' : (↑m * ↑k)^2 ≤ y ∧ m.coprime d ,
            split, swap, exact h.right,
            calc (↑m * ↑k)^2 ≤ (↑m * ↑d)^2 : by { apply sq_le_sq', linarith, linarith }
                         ... ≤ y           : h.left,
            rw if_pos h', },
          { rw if_neg h,
            by_cases h_if : (↑m * ↑k) ^ 2 ≤ y ∧ m.coprime d,
            rw if_pos h_if, apply le_of_lt, apply s.hg_pos _ (mem_divisors.mp hm).left,
            rw if_neg h_if },
          exact (mem_divisors.mp hk).left }
  
  ... = (∑ k in s.P.divisors, if k ∣ d then s.g k else 0)
      * ∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0
        : by { rw sum_mul, apply sum_congr rfl, intros k hk, rw ite_mul_zero_left }
        
  ... = s.g d * (↑d/s.ω d) * ∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d  then s.g m else 0
        : by { rw s.conv_g_eq hdP }

  ... = (↑d/s.ω d) * s.g d * μ d / S * (∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d  then s.g m else 0)
        * μ d * S
        : by { 
          conv{ to_lhs, rw ←one_mul (s.g d), rw ←int.cast_one, 
          rw ←aux.moebius_sq_eq_one_of_squarefree (squarefree.squarefree_of_dvd hdP s.hP), rw int.cast_pow,
          rw ←one_mul (s.g d) }, rw ←div_self (_:S≠0), ring, 
          apply ne_of_gt, exact s.selberg_bounding_sum_pos y hy }

  ... = (if (d ∣ s.P) then (d/s.ω d * s.g d * μ d / S 
       * ∑ m in s.P.divisors, if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.g m else 0 ) else 0) * ↑(μ d) *  S 
        : by { rw if_pos hdP },
  conv at this { to_lhs, rw ←one_mul S},
  replace this : 1 ≥ lam d * μ d,
  apply le_of_mul_le_mul_of_pos_right this (s.selberg_bounding_sum_pos y hy),
  rw ge_iff_le at this,
  have h := s.selberg_weight_mul_mu_nonneg y d hdP,
  rw ←abs_of_nonneg h at this,  
  calc |lam d| = |lam d| * |μ d| 
                 : by { rw ←int.cast_abs, rw aux.abs_moebius_eq_one_of_squarefree, 
                        rw int.cast_one, rw mul_one, exact s.sqfree_of_dvd_P hdP, }
           ... = |lam d * μ d| : by rw abs_mul
           ... ≤ 1 : this
end


lemma selberg_bound_μ_plus (s : sieve) (y : ℝ) (hy : 1 ≤ y) (n : ℕ) (hn : n ∈ s.P.divisors) :
 |s.selberg_μ_plus y n| ≤ 3 ^ ν(n) := 
begin
  let f : ℕ → ℕ → ℝ := λ (x y : ℕ), if n=x.lcm y then 1 else 0,
  let lam := s.selberg_weights y,
  dsimp only [selberg_μ_plus, lambda_squared_of_weights],
  calc |∑ d1 d2 in n.divisors, if n=d1.lcm d2 then lam d1 * lam d2 else 0 |
         ≤ ∑ d1 in n.divisors, |∑ d2 in n.divisors, if n=d1.lcm d2 then lam d1 * lam d2 else 0 | : _
     ... ≤ ∑ d1 d2 in n.divisors, | if n=d1.lcm d2 then lam d1 * lam d2 else 0 | : _
     ... ≤ ∑ d1 d2 in n.divisors, f d1 d2 : _ 
     ... = (n.divisors ×ˢ n.divisors).sum (λp, f p.fst p.snd) : _
     ... = finset.card ((n.divisors ×ˢ n.divisors).filter (λ (p:ℕ×ℕ), n=p.fst.lcm p.snd)) : _
     ... = 3^ν n          : _,
  apply abs_sum_le_sum_abs,
  apply sum_le_sum, intros d1 hd1, apply abs_sum_le_sum_abs,
  apply sum_le_sum, intros d1 hd1, apply sum_le_sum, intros d2 hd2,
  rw [apply_ite abs, abs_zero, abs_mul],
  dsimp only [f], by_cases h:n=d1.lcm d2,
  rw [if_pos h, if_pos h], 
  apply mul_le_one (s.selberg_bound_weights y hy d1) (abs_nonneg $ lam d2) (s.selberg_bound_weights y hy d2),
  rw [if_neg h, if_neg h],
  rw [←finset.sum_product'], 
  dsimp only [f],
  rw [←sum_filter, finset.sum_const, nat.smul_one_eq_coe],
  rw [aux.card_lcm_eq (s.sqfree_of_mem_dvd_P hn), cast_pow, nat.cast_bit1, algebra_map.coe_one],
end

#check nat.smul_one_eq_coe
lemma selberg_bound_simple_err_sum (s : sieve) (y : ℝ) (hy: 1 ≤ y) : 
  s.err_sum (s.selberg_μ_plus y) ≤ ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := 
begin
  dsimp only [err_sum],
  apply sum_le_sum, intros d hd,
  by_cases h : ↑d ≤ y,
  { rw if_pos h,
    apply mul_le_mul _ le_rfl (abs_nonneg $ s.R d) (pow_nonneg _ $ ν d), 
    apply s.selberg_bound_μ_plus y hy d hd,
    linarith },
  { rw if_neg h,
    rw s.selberg_μ_plus_eq_zero y d h,
    rw [abs_zero, zero_mul] },
end


theorem selberg_bound_simple (s : sieve) (y : ℝ) (hy: 1 ≤ y) :
  s.sifted_sum ≤ s.X / (s.selberg_bounding_sum_at_level y) 
               + ∑ d in s.P.divisors, if (d:ℝ) ≤ y then 3^(ν d) * |s.R d| else 0 := 
begin
  let μ_plus := s.selberg_ub_sieve y hy,
  calc s.sifted_sum ≤ s.X * s.main_sum μ_plus + s.err_sum μ_plus : s.upper_bound_main_err μ_plus
                ... ≤ _ : _,
  apply add_le_add,
  have : ⇑μ_plus = s.selberg_μ_plus y := rfl,
  rw this, clear this,
  rw [s.selberg_bound_simple_main_sum y hy, mul_one_div],
  refine s.selberg_bound_simple_err_sum y hy,
end


end sieve