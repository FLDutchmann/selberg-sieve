/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import algebra.big_operators.basic
import algebra.squarefree
import analysis.asymptotics.asymptotics
import number_theory.arithmetic_function
import aux_results

noncomputable theory

open_locale big_operators classical

open finset real nat aux

-- one should think of a as weights given to the elements of A,
-- values of a n for n not in A do not affect any of the results
structure sieve := 
  mk :: (A : finset ℕ) (P : ℕ) (hP : squarefree P) 
        (a : ℕ → ℝ) (ha_nonneg : ∀ n:ℕ, 0 ≤ a n) 
        (X : ℝ) (ω : ℕ → ℝ)

namespace sieve

@[simp]
def mult_sum (s: sieve) (d : ℕ) : ℝ := ∑ n in s.A, ite (d ∣ n) (s.a n) 0

-- A_d = ω(d)/d X + R_d
@[simp]
def R (s : sieve) (d : ℕ) : ℝ := s.mult_sum d - (s.ω d / d * s.X)

lemma mult_sum_eq_main_err (s : sieve) (d : ℕ) : s.mult_sum d = s.ω d / d * s.X + s.R d := 
begin 
  dsimp,
  ring,
end

def sifted_sum (s: sieve): ℝ := ∑ d in s.A, ite (s.P.coprime d) (s.a d) 0  

@[simp]
def ν := arithmetic_function.card_distinct_factors
@[simp]
def δ (n : ℕ) : ℝ := ite (n = 1) 1 0
@[simp]
def μ := arithmetic_function.moebius


theorem sifted_sum_as_delta(s : sieve): 
  s.sifted_sum = ∑ d in s.A, s.a d * δ (nat.gcd s.P d) := 
begin 
  cases s with A P hP a ha_pos X ω,
  dsimp only [sifted_sum],
  apply sum_congr rfl,
  intros d hd,

  dsimp only [nat.coprime, δ] at *,
  by_cases h: P.gcd d = 1,
  { rw if_pos h,
    rw if_pos h,
    ring },
  { rw if_neg h,
    rw if_neg h,
    ring },
end

lemma hP_ne_zero (s : sieve) : s.P ≠ 0 := squarefree.ne_zero s.hP

lemma sqfree_of_dvd_P (s:sieve) {d : ℕ} (hd : d ∈ s.P.divisors) : squarefree d := begin
  simp only [nat.mem_divisors, ne.def] at hd,
  exact squarefree.squarefree_of_dvd hd.left s.hP,  
end

-- The two axioms needed for the simple form of the selberg bound
def axiom_mult (s : sieve) : Prop := s.ω 1 = 1 ∧ ∀(x y : ℕ), x.coprime y → s.ω (x*y) = s.ω x * s.ω y   
def axiom_size_1 (s : sieve) : Prop := ∀p:ℕ, p.prime → (0 ≤ s.ω p ∧ s.ω p < p) 

-- Used in statement of the simple form of the selberg bound
def g (s : sieve) (d : ℕ) : ℝ := s.ω(d)/d * ∏ p in d.factors.to_finset, 1/(1-s.ω(p)/p) 
-- S = ∑_{l|P, l≤√y} g(l)

-- Facts about g
set_option profiler true
lemma rec_g_eq_conv_moebius_omega (s : sieve) (l : ℕ) (hl : squarefree l) :
  1 / s.g l = ∑ d in s.P.divisors, ite (d ∣ l) ((μ $ l/d) * d / s.ω d) 0 := 
begin
  suffices : 1 / s.g l = ∑ d in l.divisors, (μ $ l/d) * d / s.ω d, 
  { rw this, sorry },
  dsimp only [g],
  simp only [one_div, mul_inv, inv_div, inv_inv, finset.prod_congr, finset.prod_inv_distrib], 
  apply nat.strong_induction_on l,
  intros l_ind h_ind,
  by_cases h_zero : l_ind = 0,
  sorry{ rw h_zero, simp? }, -- slow
  by_cases h_one : l_ind = 1,
  sorry{ rw h_one, simp, rw if_neg s.hP_ne_zero, },
  let p:= l_ind.min_fac,
  have hp : p.prime := min_fac_prime h_one,
  have h_dvd : p ∣ l_ind := min_fac_dvd l_ind,
  cases h_dvd with k hk,
  have hkl : k ∣ l_ind,
  { use p, rw hk, ring, },
  rw hk,
  sorry,
  
end

lemma omega_eq_conv_rec_g (s : sieve) (d : ℕ) :
  (d:ℝ) / s.ω d = ∑ l in s.P.divisors, ite (l ∣ d) (1/s.g l) 0 := sorry


--def upper_bound_sieve_of_level (y : ℕ) (μ_plus : ℕ → ℝ) : Prop := 
--  ∀n:ℕ, (n:ℝ) > y → μ_plus n = 0   ∧   ∀n:ℕ, δ n ≤ ∑ d in n.divisors, μ_plus d 

def upper_moebius (μ_plus : ℕ → ℝ) : Prop := ∀n:ℕ, δ n ≤ ∑ d in n.divisors, μ_plus d


structure upper_bound_sieve :=
  mk :: (μ_plus : ℕ → ℝ) (hμ_plus : upper_moebius μ_plus)

instance ub_to_μ_plus : has_coe_to_fun upper_bound_sieve (λ _, ℕ → ℝ) := 
{ coe := λ ub, ub.μ_plus } 

def main_sum (s: sieve) (μ_plus: ℕ → ℝ) : ℝ := ∑ d in s.P.divisors, μ_plus d * s.ω d / d   

def err_sum (s: sieve) (μ_plus: ℕ → ℝ): ℝ := ∑ d in s.P.divisors, |μ_plus d| * |s.R d|  
--def upper_bound_sieve (μ_plus : ℕ → ℝ) : Prop := 
--  ∀n:ℕ, δ n ≤ ∑ d in n.divisors, μ_plus d 

theorem upper_bound_of_upper_bound_sieve (s : sieve) 
    (μ_plus : upper_bound_sieve) : 
  s.sifted_sum ≤ ∑ d in s.P.divisors, μ_plus d * s.mult_sum d :=
begin
  have hμ : ∀n, δ n ≤ ∑ d in n.divisors, μ_plus d := μ_plus.hμ_plus,

  rw sifted_sum_as_delta,
  calc ∑ n in s.A, s.a n * δ (s.P.gcd n) 

     ≤ ∑ n in s.A, s.a n * ∑ d in (s.P.gcd n).divisors, μ_plus d 
       : by {
          apply finset.sum_le_sum,
          intros n hnA,
          exact mul_le_mul_of_nonneg_left (hμ (s.P.gcd n)) (s.ha_nonneg n) }

 ... = ∑ n in s.A, ∑ d in (s.P.gcd n).divisors, s.a n * μ_plus d 
       : by {
          apply sum_congr rfl, intros n hnA,
          exact mul_sum } 

 ... = ∑ n in s.A, ∑ d in s.P.divisors, ite (d ∣ n) (s.a n * μ_plus d) 0 
       : by {
          apply sum_congr rfl, intros n hnA,
          apply sum_over_dvd s.hP_ne_zero (gcd_dvd s.P n).left,
          { intros d hd,
            have : ¬ d ∣ n,
            { by_contra h,
              exact hd.right (nat.dvd_gcd_iff.mpr ⟨hd.left, h⟩) },
            exact if_neg this },
          { intros d hd,
            have : d ∣ n := dvd_trans hd (gcd_dvd s.P n).right,
            exact if_pos this } } 

 ... = ∑ d in s.P.divisors, ∑ n in s.A,  ite (d ∣ n) (s.a n * μ_plus d) 0 : finset.sum_comm

 ... = ∑ d in s.P.divisors, ∑ n in s.A, μ_plus d * ite (d ∣ n) (s.a n) 0 
       : by {
          apply sum_congr rfl, intros d hdP,
          apply sum_congr rfl, intros n hnA,
          rw ite_mul_zero_left, ring, }

 ... = ∑ d in s.P.divisors, μ_plus d * ∑ n in s.A, ite (d ∣ n) (s.a n) 0 
       : by {
          apply sum_congr rfl, intros d hdP,
          rw eq_comm,
          apply mul_sum, }
end


theorem upper_bound_main_err (s: sieve) (μ_plus : upper_bound_sieve) :
  s.sifted_sum ≤ s.X * s.main_sum μ_plus + s.err_sum μ_plus := 
begin
  dsimp only [main_sum, err_sum],
  
  have err_bound : ∑ d in s.P.divisors, μ_plus d * s.R d  ≤ ∑ d in s.P.divisors, |μ_plus d| * |s.R d|,
  { calc ∑ d in s.P.divisors, μ_plus d * s.R d 
      
      ≤ |∑ d in s.P.divisors, μ_plus d * s.R d| : le_abs.mpr (or.intro_left _ le_rfl)

  ... ≤ ∑ d in s.P.divisors, |μ_plus d * s.R d| : abs_sum_le_sum_abs (λd, μ_plus d * s.R d) s.P.divisors

  ... = ∑ d in s.P.divisors, |μ_plus d| * |s.R d| 
        : by { 
          apply sum_congr rfl, intros d hdP,
          exact abs_mul (μ_plus d) (s.R d) } },

  calc s.sifted_sum ≤ ∑ d in s.P.divisors, μ_plus d * s.mult_sum d : s.upper_bound_of_upper_bound_sieve μ_plus
                ... = ∑ d in s.P.divisors, μ_plus d * (s.ω d / d * s.X + s.R d) 
                      : by {
                        apply sum_congr rfl, intros d hdP,
                        rw s.mult_sum_eq_main_err,
                      }
                      
                ... = ∑ d in s.P.divisors, (μ_plus d * s.ω d / d * s.X + μ_plus d * s.R d) 
                      : by { apply sum_congr rfl, intros d hdP, ring }

                ... = ∑ d in s.P.divisors, μ_plus d * s.ω d / d * s.X 
                    + ∑ d in s.P.divisors, μ_plus d * s.R d        
                      : sum_add_distrib

                ... = s.X * ∑ d in s.P.divisors, μ_plus d * s.ω d / ↑d 
                    + ∑ d in s.P.divisors, μ_plus d * s.R d 
                      : by { rw ←sum_mul, rw mul_comm, }

                ... ≤ s.X * ∑ d in s.P.divisors, μ_plus d * s.ω d / ↑d 
                    + ∑ d in s.P.divisors, |μ_plus d| * |s.R d| : by linarith, 
end


def lambda_squared_of_weights (weights : ℕ → ℝ) : ℕ → ℝ := 
  λd,  ∑ d1 d2 in d.divisors, ite (d = nat.lcm d1 d2) (weights d1 * weights d2) 0


lemma lambda_sq_main_sum_eq_quad_form (s: sieve) (h_mult : s.axiom_mult) (y : ℕ) (w : ℕ → ℝ) :
  s.main_sum (lambda_squared_of_weights w) = ∑ d1 d2 in s.P.divisors, 
            s.ω d1/d1 * w d1 * s.ω d2/d2 * w d2 * (d1.gcd d2)/s.ω(d1.gcd d2) := 
begin
  --dsimp only [main_sum, lambda_squared_of_weights],

  calc ∑ d in s.P.divisors, (∑ d1 d2 in d.divisors, ite (d = d1.lcm d2) (w d1 * w d2) 0) * s.ω d / ↑d
      = ∑ d in s.P.divisors, (∑ d1 d2 in d.divisors, ite (d = d1.lcm d2) (w d1 * w d2) 0) * (s.ω d / ↑d) 
        : by { apply sum_congr rfl, intros d hdP, ring }
  
  ... = ∑ d in s.P.divisors, ∑ d1 d2 in d.divisors, (ite (d = d1.lcm d2) (w d1 * w d2) 0 * (s.ω d / ↑d)) 
        : by {apply sum_congr rfl, intros d hdP, rw sum_mul, apply sum_congr rfl, intros d1 hd1d, rw sum_mul }

  ... = ∑ d in s.P.divisors, ∑ d1 d2 in d.divisors, ite (d = d1.lcm d2) (w d1 * w d2 * s.ω d / ↑d) 0 
        : by { 
          apply sum_congr rfl, intros d hdP, apply sum_congr rfl, intros d1 hd1, apply sum_congr rfl, intros d2 hd2,
          rw ←ite_mul_zero_left, 
          apply ite_eq_of_iff_eq _ _ iff.rfl,
          rintro ⟨h, _⟩, ring, }

  ... = ∑ d d1 in s.P.divisors, ∑ d2 in d.divisors, ite (d = d1.lcm d2) (w d1 * w d2 * s.ω d / ↑d) 0
        : by {
          apply sum_congr rfl, intros d hdP,
          apply sum_over_dvd s.hP_ne_zero,
          { rw mem_divisors at hdP, exact hdP.left },
          { intros d1 hd1,
            apply sum_eq_zero,
            intros d2 hd2,
            have : d ≠ d1.lcm d2,
            { by_contra h, rw h at hd1, exact hd1.right (nat.dvd_lcm_left d1 d2), },
            rw if_neg this },
          { intros d1 hd1, refl, } } 

  ... = ∑ d d1 d2 in s.P.divisors, ite (d = d1.lcm d2) (w d1 * w d2 * s.ω d / ↑d) 0
        : by {
          apply sum_congr rfl, intros d hdP,
          apply sum_congr rfl, intros d1 hd1P,
          apply sum_over_dvd s.hP_ne_zero,     
          { rw mem_divisors at hdP, exact hdP.left }, 
          { intros d2 hd2, 
            have : d ≠ d1.lcm d2,
            { by_contra h, rw h at hd2, exact hd2.right (nat.dvd_lcm_right d1 d2) },
            rw if_neg this },
          { exact λ_ _, rfl, } }

  
  ... = ∑ d1 d2 d in s.P.divisors, ite (d = d1.lcm d2) (w d1 * w d2 * s.ω d / ↑d) 0 
        : by { rw sum_comm, apply sum_congr rfl, intros d1 hd1, rw sum_comm, }

  ... = ∑ d1 d2 d in s.P.divisors, ite (d = d1.lcm d2 ∧ true) (w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2)) 0 
        : by { 
          apply sum_congr rfl, intros d1 hd1P, apply sum_congr rfl, intros d2 hd2, apply sum_congr rfl, intros d hd,
          apply ite_eq_of_iff_eq,
          { rw and_true },
          rintros ⟨h, _⟩, rw ←h, }
      
  ... = ∑ d1 d2 in s.P.divisors, ite (true) (w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2)) 0 
        : by {
          apply sum_congr rfl, intros d1 hd1P, apply sum_congr rfl, intros d2 hd2P,
          rw ←sum_intro s.P.divisors true (w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2)) ,
          rw mem_divisors at hd1P hd2P,
          intro _, 
          rw mem_divisors, split,
          exact nat.lcm_dvd_iff.mpr ⟨hd1P.left, hd2P.left⟩,
          exact hd1P.right }

  ... = ∑ d1 d2 in s.P.divisors, (w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2))
        : by { 
          apply sum_congr rfl, intros d1 _, apply sum_congr rfl, intros d2 _,
          rw if_pos trivial, } 

  ... = ∑ d1 d2 in s.P.divisors, s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2) 
      : by {
          apply sum_congr rfl, intros d1 hd1P, apply sum_congr rfl, intros d2 hd2P,
          have : s.ω (d1.lcm d2) = s.ω d1 * s.ω d2 / s.ω (d1.gcd d2),
          { by_cases h_zero : s.ω (d1.gcd d2) = 0,
            { rw h_zero, simp only [div_zero],
              have : d1.gcd d2 ∣ d1.lcm d2,
              calc  d1.gcd d2 ∣ d1        : nat.gcd_dvd_left d1 d2
                          ... ∣ d1.lcm d2 : nat.dvd_lcm_left d1 d2,
              exact multiplicative_zero_of_zero_dvd s.ω h_mult.right 
                 (lcm_squarefree_of_squarefree (s.sqfree_of_dvd_P hd1P) (s.sqfree_of_dvd_P hd2P)) this h_zero, },
            { rw eq_div_iff_mul_eq h_zero, rw eq_comm,
              exact mult_gcd_lcm_of_squarefree s.ω h_mult.right d1 d2 (s.sqfree_of_dvd_P hd1P) (s.sqfree_of_dvd_P hd2P) } },

          rw this,
          
          dsimp only [nat.lcm],
          rw nat.cast_div (aux.gcd_dvd_mul d1 d2),
          rw nat.cast_mul,
          
          calc   w d1 * w d2 * (s.ω d1 * s.ω d2 / s.ω (d1.gcd d2)) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) 
               =   w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) : by ring
           ... =   w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / (↑d1 * ↑d2) * ↑(d1.gcd d2) : by rw ←div_mul
           ... =   w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / ↑d1 / ↑d2 * ↑(d1.gcd d2) : by rw ←div_div                         
           ... = s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2) : by ring,
          
          rw cast_ne_zero, apply ne_zero_of_dvd_ne_zero _ (nat.gcd_dvd_left d1 d2), 
          simp only [nat.mem_divisors] at hd1P, exact ne_zero_of_dvd_ne_zero hd1P.right hd1P.left, }

end
 

lemma lambda_sq_main_sum_eq_diag_quad_form (s: sieve) (h_mult : s.axiom_mult) (y : ℕ) (w : ℕ → ℝ) :
  s.main_sum (lambda_squared_of_weights w) = ∑ l in s.P.divisors, 
            1/(s.g l) * ∑ d in s.P.divisors, ite (l∣d) (s.ω d/d * w d) 0 := sorry

  

--TODO: TIDY UP PROOF
theorem upper_moebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) : 
  upper_moebius $ lambda_squared_of_weights weights :=
begin
  dsimp [upper_moebius, lambda_squared_of_weights],
  intro n, 
  have h_sq: ∑ d in n.divisors, ∑ d1 d2 in d.divisors, ite (d = nat.lcm d1 d2) (weights d1 * weights d2) 0
          = (∑ d in n.divisors, weights d)^2,
  { 
    rw sq,
    rw mul_sum,
    rw conv_lambda_sq_larger_sum weights n,

    rw sum_comm,
    apply sum_congr rfl,
    intros d1 hd1,
    rw sum_mul,

    rw sum_comm,
    apply sum_congr rfl,
    intros d2 hd2,
    rw ← sum_filter (λ (a : ℕ), a = d1.lcm d2),
    rw sum_eq_single (d1.lcm d2),
    { ring },
    { intros b hb_in hb_neq,
      simp at hb_in,
      exfalso,
      cases hb_in with hb_div hb_eq,
      exact hb_neq hb_eq,
     },
     {intro h_lcm,
      simp at h_lcm hd1 hd2,
      cases hd1 with hd1 hn1,
      cases hd2 with hd2 hn2,
      have hn' : n = 0,
      exact h_lcm (nat.lcm_dvd hd1 hd2),
      contradiction, }
     },

  rw h_sq, 
  by_cases hn: n=1,
  { rw if_pos hn,
    have : (∑ d in n.divisors, weights d) = (weights 1),
    { apply sum_eq_single 1,
      { intros b hb_dvd hb_none,
        exfalso,
        rw hn at hb_dvd,
        simp at hb_dvd,
        exact hb_none hb_dvd,
       }, 
      { intro h,
        simp at h,
        rw h at hn,
        contradiction, } },
    rw this,
    rw hw,
    ring_nf, },
  { rw if_neg hn, 
    apply sq_nonneg, }
end
 

--def lambda_squared_sieve_of_weights 
--  (s: sieve) (weights : ℕ → ℝ) (hw: weights 1 = 1) : upper_bound_sieve := 
 -- ⟨s, lambda_squared_of_weights weights, upper_moebius_of_lambda_sq weights hw⟩ 

--end upper_bound_sieve

end sieve