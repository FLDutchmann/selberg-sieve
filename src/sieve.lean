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

set_option profiler true
-- one should think of a as weights given to the elements of A,
-- values of a n for n not in A do not affect any of the results
structure sieve := 
  mk :: (A : finset ℕ) (P : ℕ) (hP : squarefree P) 
        (a : ℕ → ℝ) (ha_nonneg : ∀ n:ℕ, 0 ≤ a n) 
        (X : ℝ) (ω : ℕ → ℝ) 
        (hω_mult : multiplicative ω)
        (hω_pos_of_prime : ∀(p:ℕ), p.prime → p ∣ P → 0 < ω p )

namespace sieve

lemma hP_ne_zero (s : sieve) : s.P ≠ 0 := squarefree.ne_zero s.hP

lemma sqfree_of_mem_dvd_P (s:sieve) {d : ℕ} (hd : d ∈ s.P.divisors) : squarefree d := 
begin
  simp only [nat.mem_divisors, ne.def] at hd,
  exact squarefree.squarefree_of_dvd hd.left s.hP,  
end

lemma hω_pos_of_dvd_P (s: sieve) {d: ℕ} (hl : d ∣ s.P) : 0 < s.ω d := 
begin

  calc 0 < ∏ p in d.factors.to_finset, s.ω p 
           : by {
              apply prod_pos,
              intros p hpd, rw list.mem_to_finset at hpd,
              have hp_prime : p.prime := prime_of_mem_factors hpd,
              have hp_dvd : p ∣ s.P := dvd_trans (dvd_of_mem_factors hpd) hl,
              exact (s.hω_pos_of_prime p hp_prime hp_dvd), }

     ... = s.ω d : prod_factors_of_mult s.ω s.hω_mult (squarefree.squarefree_of_dvd hl s.hP),
end

lemma hω_ne_zero_of_mem_dvd_P (s: sieve) {d: ℕ} (hd : d ∈ s.P.divisors) : s.ω d ≠ 0 :=
begin
  apply ne_of_gt,
  rw mem_divisors at hd,
  apply hω_pos_of_dvd_P s hd.left,
end

@[simp]
def mult_sum (s: sieve) (d : ℕ) : ℝ := ∑ n in s.A, if d ∣ n then s.a n else 0

-- A_d = ω(d)/d X + R_d
@[simp]
def R (s : sieve) (d : ℕ) : ℝ := s.mult_sum d - (s.ω d / d * s.X)

lemma mult_sum_eq_main_err (s : sieve) (d : ℕ) : s.mult_sum d = s.ω d / d * s.X + s.R d := 
begin 
  dsimp,
  ring,
end

def sifted_sum (s: sieve): ℝ := ∑ d in s.A, if s.P.coprime d then s.a d else 0  

@[simp]
def ν := arithmetic_function.card_distinct_factors
@[simp]
def δ (n : ℕ) : ℝ := if n = 1 then 1 else 0
--@[simp]
--def μ := arithmetic_function.moebius


localized "notation (name := moebius)
  `μ` := nat.arithmetic_function.moebius" in sieve

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


-- The size axioms needed for the simple form of the selberg bound
def axiom_size_1 (s : sieve) : Prop := ∀p:ℕ, p.prime → p ∣ s.P → (s.ω p < p) 

def drop_prime_of_axiom_size_1 (s : sieve) (h_size : s.axiom_size_1) :
  ∀d:ℕ, d ∣ s.P → d ≠ 1 → (s.ω d < d) :=  
begin
  intros d hdP hd_ne_one,
  have hd_sq : squarefree d := squarefree.squarefree_of_dvd hdP s.hP,
  calc s.ω d = ∏ p in d.factors.to_finset, s.ω p : eq_comm.mp (prod_factors_of_mult s.ω s.hω_mult hd_sq)

         ... < ∏ p in d.factors.to_finset, ↑p
          : by { 
            have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.hP_ne_zero hdP,
            apply prod_le_prod_of_nonempty,
            { intros p hp, rw list.mem_to_finset at hp,
              rw mem_factors hd_ne_zero at hp, 
              apply s.hω_pos_of_prime p hp.left (dvd_trans hp.right hdP)},
            { intros p hpd, rw list.mem_to_finset at hpd, rw mem_factors hd_ne_zero at hpd,
              apply h_size p hpd.left (dvd_trans hpd.right hdP) },

            { dsimp [finset.nonempty],
              conv{congr, funext, rw list.mem_to_finset, rw nat.mem_factors hd_ne_zero, },
              exact nat.exists_prime_and_dvd hd_ne_one, } }

         ... = ↑d 
          : by { 
            rw prod_factors_of_mult, split, push_cast, ring,
            intros _ _ _, 
            calc ↑(x*y) = ↑x*↑y : by rw cast_mul, 
            exact hd_sq, }


end

lemma hω_over_d_mult (s : sieve) :
  multiplicative (λ d, s.ω d / ↑d) := 
begin
  apply div_mult_of_mult,
  exact s.hω_mult,
  exact coe_mult,
  intros n hn, 
  rw nat.cast_ne_zero,
  exact ne_of_gt hn,
end

-- Used in statement of the simple form of the selberg bound
def g (s : sieve) (d : ℕ) : ℝ := s.ω(d)/d * ∏ p in d.factors.to_finset, 1/(1-s.ω(p)/p) 
-- S = ∑_{l|P, l≤√y} g(l)
 
-- Facts about g
lemma zero_lt_g_of_ax_size(s : sieve) (l : ℕ) (hl : l ∣ s.P) 
 (h_size : s.axiom_size_1) :
  0 < s.g l :=
begin
  have hl_sq : squarefree l := squarefree.squarefree_of_dvd hl s.hP, 
  dsimp only [g],
  apply mul_pos,
  apply div_pos,
  apply lt_of_le_of_ne,
  apply le_of_lt,
  exact (s.hω_pos_of_dvd_P hl),  
  apply ne_comm.mp, apply ne_of_gt, exact s.hω_pos_of_dvd_P hl,
  suffices : 0 < l, exact cast_pos.mpr this,
  rw zero_lt_iff, exact squarefree.ne_zero hl_sq,
  
  apply prod_pos,
  intros p hp,
  rw one_div_pos,
  rw list.mem_to_finset at hp,
  have hp_prime: p.prime,
  { exact prime_of_mem_factors hp },
  have hp_dvd : p ∣ s.P,
  { calc p ∣ l   : nat.dvd_of_mem_factors hp
       ... ∣ s.P : hl }, 
  have : s.ω p < p,
  { exact (h_size p hp_prime hp_dvd) },
  have hp_pos : 0 < (p:ℝ),
  { suffices : 0 < p, {exact cast_pos.mpr this}, 
    exact nat.prime.pos hp_prime },
  have hp_ne_zero : (p:ℝ) ≠ 0 := ne_comm.mp (ne_of_lt hp_pos),
  rw ←zero_lt_mul_right hp_pos,
  calc 0 < ↑p - s.ω p : by linarith only [this]
     ... = (1-s.ω p / ↑p ) * ↑p 
     : by { conv{to_lhs, rw ←(div_mul_cancel (s.ω p) hp_ne_zero: s.ω p / p * p = s.ω p )}, ring},
end

lemma rec_g_eq_conv_moebius_omega (s : sieve) (l : ℕ) (hl : squarefree l) 
  (hω_nonzero : s.ω l ≠ 0): --(h_size : s.axiom_size_1) :
  1 / s.g l = ∑ d in l.divisors, ((μ $ l/d) * (d / s.ω d)) := 
begin
  dsimp only [g],
  simp only [one_div, mul_inv, inv_div, inv_inv, finset.prod_congr, finset.prod_inv_distrib], 
  rw prod_eq_moebius_sum (λ d, s.ω d/(d:ℝ)),
  { rw mul_sum, 
    calc ∑ d in l.divisors, ↑l / s.ω l * (↑(μ d) * (s.ω d / ↑d))
       = ∑ d in l.divisors, ↑(μ d) * (↑l/↑d) * (s.ω d / s.ω l) 
         : by { apply sum_congr rfl, intros d hd, ring }

   ... = ∑ d in l.divisors, ↑(μ d) * ↑(l/d) * (1 / (s.ω l / s.ω d))
         : by {
            apply sum_congr rfl, intros d hd,
            rw mem_divisors at hd,
            rw ←nat.cast_div hd.left,
            rw one_div_div,
            rw nat.cast_ne_zero,
            exact ne_zero_of_dvd_ne_zero hd.right hd.left } 

   ... = ∑ d in l.divisors, ↑(μ d) * (↑(l/d) / s.ω (l/d)) 
         : by { 
            apply sum_congr rfl, intros d hd,
            rw mem_divisors at hd,
            rw div_mult_of_dvd_squarefree s.ω s.hω_mult l d hd.left hl,
            ring,
            revert hω_nonzero, contrapose!,
            exact multiplicative_zero_of_zero_dvd s.ω s.hω_mult hl hd.left }
   
   ... = l.divisors.sum (λd, ↑(μ d) * (↑(l/d) / s.ω (l/d))) : rfl

   ... = l.divisors.sum (λd, μ (l/d) * (↑d / s.ω d)) 
         : by {
            rw ←nat.sum_divisors_antidiagonal (λd e : ℕ, ↑(μ d) * (↑e/s.ω e)),
            rw ←nat.sum_divisors_antidiagonal' (λd e : ℕ, ↑(μ d) * (↑e/s.ω e)) } },


  exact s.hω_over_d_mult,
  exact hl,
end

lemma omega_eq_conv_rec_g (s : sieve) (d : ℕ) (hdP : d ∣ s.P ) :
  (d:ℝ) / s.ω d = ∑ l in s.P.divisors, if l ∣ d then 1/s.g l else 0 := 
begin -- Problem, these identities only hold on l ∣ P, so can't use standard moebius inversion results,
  rw eq_comm,
  calc  ∑ l in s.P.divisors, (if l ∣ d then 1/s.g l else 0)
        
      = ∑ l in s.P.divisors, if l ∣ d then ∑ k in l.divisors, ((μ $ l/k) * (k / s.ω k)) else 0
        : by {
          apply sum_congr rfl, intros l hl, 
          rw s.rec_g_eq_conv_moebius_omega l (s.sqfree_of_mem_dvd_P hl) (s.hω_ne_zero_of_mem_dvd_P hl) }
        
    ... = ∑ l in s.P.divisors, if l ∣ d then ∑ k in s.P.divisors, (if k∣l then (μ $ l/k) * (k / s.ω k) else 0) else 0 
          : by { 
            apply sum_congr rfl, intros l hl,
            rw mem_divisors at hl, rw ←sum_over_dvd_ite s.hP_ne_zero hl.left }
    
    ... = ∑ l in s.P.divisors, (∑ k in s.P.divisors, if k∣l then (μ $ l/k) * (k / s.ω k) else 0) * if l ∣ d then 1 else 0 
          : by conv{ to_rhs, congr, skip, funext, rw mul_boole }

    ... = ∑ l k in s.P.divisors, (if k∣l then (μ $ l/k) * (k / s.ω k) else 0) * (if l ∣ d then 1 else 0) 
          : by { apply sum_congr rfl, intros l hl, rw sum_mul }
    
    ... = ∑ k l in s.P.divisors, if k∣l ∧ l ∣ d then (μ $ l/k) * (k / s.ω k) else 0
          : by {
            rw sum_comm, 
            apply sum_congr rfl, intros l hl,
            apply sum_congr rfl, intros k hk,
            rw ←ite_and_mul_zero,
            apply ite_eq_of_iff_eq _ _ iff.rfl, intro _, ring }
    
    ... = ∑ k l in s.P.divisors, (if k∣l ∧ l ∣ d then (μ l/μ k) else 0) * (k / s.ω k)
          : by {
            conv{ to_rhs, congr, skip, funext, conv{congr, skip, funext, conv{rw ←ite_mul_zero_left}} },
            apply sum_congr rfl, intros k hk, apply sum_congr rfl, intros l hl,
            apply ite_eq_of_iff_eq _ _ iff.rfl,
            rintros ⟨h, _⟩,
            have := nat.arithmetic_function.is_multiplicative_moebius,  
            calc  (λ x:ℕ, (μ x:ℝ)) (l/k) * ((k:ℝ) / s.ω k)
                = ↑(μ l) / ↑(μ k) * (↑k / s.ω k) 
                : by { -- SLOW SLOW SLOW SLOW
                  rw div_mult_of_dvd_squarefree (λ x, ↑(μ x)),
                  split, simp,
                  intros x y hxy, norm_cast,
                  apply nat.arithmetic_function.is_multiplicative.map_mul_of_coprime this hxy, 
                  exact h.left,
                  exact s.sqfree_of_mem_dvd_P hl,
                  suffices : μ k ≠ 0, simpa using this,
                  
                  apply arithmetic_function.moebius_ne_zero_iff_squarefree.mpr,
                  exact s.sqfree_of_mem_dvd_P hk, } }

    ... = ∑ k in s.P.divisors, (∑ l in s.P.divisors, if k ∣ l ∧ l ∣ d then μ l else 0) / μ k * (k / s.ω k)
          : by {
            apply sum_congr rfl, intros k hk,
            conv{ to_lhs, congr, skip, funext, rw div_eq_mul_inv, rw ite_mul_zero_left,},
            rw ←sum_mul, rw ←sum_mul,  rw ←div_eq_mul_inv }

    ... = ∑ k in s.P.divisors, (if k = d then μ k else 0) / μ k * (k / s.ω k)
          : by {
            apply sum_congr rfl, intros k hk, rw ←int.cast_zero, 
            conv{to_lhs, congr, congr, congr, skip, funext, conv{rw ←int.cast_ite}}, rw ←int.cast_sum,
            rw (rfl : μ = arithmetic_function.moebius),
            classical,
            rw moebius_inv_dvd_lower_bound s.hP k d hdP,
            rw ←int.cast_ite }
            
    ... = ↑d / s.ω d 
          : by{
            rw finset.sum_eq_single d,
            rw if_pos rfl, rw div_self, ring,
            rw int.cast_ne_zero, 
            apply arithmetic_function.moebius_ne_zero_iff_squarefree.mpr,
            exact squarefree.squarefree_of_dvd hdP s.hP,
            intros k hk hkd, rw if_neg hkd, ring,
            intro hd, rw mem_divisors at hd, 
            exfalso, push_neg at hd,
            exact s.hP_ne_zero (hd hdP) }
end

def upper_moebius (μ_plus : ℕ → ℝ) : Prop := ∀n:ℕ, δ n ≤ ∑ d in n.divisors, μ_plus d


structure upper_bound_sieve :=
  mk :: (μ_plus : ℕ → ℝ) (hμ_plus : upper_moebius μ_plus)

instance ub_to_μ_plus : has_coe_to_fun upper_bound_sieve (λ _, ℕ → ℝ) := 
{ coe := λ ub, ub.μ_plus } 

def main_sum (s: sieve) (μ_plus: ℕ → ℝ) : ℝ := ∑ d in s.P.divisors, μ_plus d * s.ω d / d   

def err_sum (s: sieve) (μ_plus: ℕ → ℝ): ℝ := ∑ d in s.P.divisors, |μ_plus d| * |s.R d|  

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

 ... = ∑ n in s.A, ∑ d in s.P.divisors, if d ∣ n then s.a n * μ_plus d else 0 
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

 ... = ∑ d in s.P.divisors, ∑ n in s.A,  if d ∣ n then s.a n * μ_plus d else 0 : finset.sum_comm

 ... = ∑ d in s.P.divisors, ∑ n in s.A, μ_plus d * if d ∣ n then s.a n else 0 
       : by {
          apply sum_congr rfl, intros d hdP,
          apply sum_congr rfl, intros n hnA,
          rw ite_mul_zero_left, ring, }

 ... = ∑ d in s.P.divisors, μ_plus d * ∑ n in s.A, if d ∣ n then s.a n else 0 
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
  λd,  ∑ d1 d2 in d.divisors, if d = nat.lcm d1 d2 then weights d1 * weights d2 else 0


lemma lambda_sq_main_sum_eq_quad_form (s: sieve) (y : ℕ) (w : ℕ → ℝ) :
  s.main_sum (lambda_squared_of_weights w) = ∑ d1 d2 in s.P.divisors, 
            s.ω d1/d1 * w d1 * s.ω d2/d2 * w d2 * (d1.gcd d2)/s.ω(d1.gcd d2) := 
begin
  --dsimp only [main_sum, lambda_squared_of_weights],

  calc ∑ d in s.P.divisors, (∑ d1 d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * s.ω d / ↑d
      = ∑ d in s.P.divisors, (∑ d1 d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * (s.ω d / ↑d) 
        : by { apply sum_congr rfl, intros d hdP, ring }
  
  ... = ∑ d in s.P.divisors, ∑ d1 d2 in d.divisors, (if d = d1.lcm d2 then w d1 * w d2 else 0) * (s.ω d / ↑d) 
        : by {apply sum_congr rfl, intros d hdP, rw sum_mul, apply sum_congr rfl, intros d1 hd1d, rw sum_mul }

  ... = ∑ d in s.P.divisors, ∑ d1 d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 
        : by { 
          apply sum_congr rfl, intros d hdP, apply sum_congr rfl, intros d1 hd1, apply sum_congr rfl, intros d2 hd2,
          rw ←ite_mul_zero_left, 
          apply ite_eq_of_iff_eq _ _ iff.rfl,
          rintro ⟨h, _⟩, ring, }

  ... = ∑ d d1 in s.P.divisors, ∑ d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0
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

  ... = ∑ d d1 d2 in s.P.divisors, if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0
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

  
  ... = ∑ d1 d2 d in s.P.divisors, if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 
        : by { rw sum_comm, apply sum_congr rfl, intros d1 hd1, rw sum_comm, }

  ... = ∑ d1 d2 d in s.P.divisors, if d = d1.lcm d2 ∧ true then w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2) else 0 
        : by { 
          apply sum_congr rfl, intros d1 hd1P, apply sum_congr rfl, intros d2 hd2, apply sum_congr rfl, intros d hd,
          apply ite_eq_of_iff_eq,
          { rw and_true },
          rintros ⟨h, _⟩, rw ←h, }
      
  ... = ∑ d1 d2 in s.P.divisors, if true then w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2) else 0 
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
              exact multiplicative_zero_of_zero_dvd s.ω s.hω_mult
                 (lcm_squarefree_of_squarefree (s.sqfree_of_mem_dvd_P hd1P) (s.sqfree_of_mem_dvd_P hd2P)) this h_zero, },
            { rw eq_div_iff_mul_eq h_zero, rw eq_comm,
              exact mult_gcd_lcm_of_squarefree s.ω s.hω_mult d1 d2 (s.sqfree_of_mem_dvd_P hd1P) (s.sqfree_of_mem_dvd_P hd2P) } },

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
 

lemma lambda_sq_main_sum_eq_diag_quad_form (s: sieve) (y : ℕ) (w : ℕ → ℝ) :
  s.main_sum (lambda_squared_of_weights w) = ∑ l in s.P.divisors, 
            1/(s.g l) * (∑ d in s.P.divisors, if l∣d then s.ω d/d * w d else 0)^2 := 
begin
  rw s.lambda_sq_main_sum_eq_quad_form y w,
  calc  ∑ d1 d2 in s.P.divisors, s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2)

      = ∑ d1 d2 in s.P.divisors, (↑(d1.gcd d2) / s.ω (d1.gcd d2)) * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) 
        : by {
          apply sum_congr rfl, intros d1 hd1, apply sum_congr rfl, intros d2 hd2,
          ring }

  ... = ∑ d1 d2 in s.P.divisors, (∑ l in s.P.divisors, if l ∣ d1.gcd d2 then 1/s.g l else 0) 
                               * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) 
        : by {
          apply sum_congr rfl, intros d1 hd1, apply sum_congr rfl, intros d2 hd2,
          rw mem_divisors at hd1 hd2,
          rw s.omega_eq_conv_rec_g (d1.gcd d2) (dvd_trans (nat.gcd_dvd_left d1 d2) (hd1.left)) }
  
  ... = ∑ d1 d2 l in s.P.divisors, if l ∣ d1.gcd d2 then 1/s.g l * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0 
        : by {
          apply sum_congr rfl, intros d1 hd1, apply sum_congr rfl, intros d2 hd2,
          rw sum_mul, rw sum_mul,
          apply sum_congr rfl, intros l hl,
          rw ←ite_mul_zero_left, rw ←ite_mul_zero_left }

  ... = ∑ l d1 d2 in s.P.divisors, if l ∣ d1 ∧ l ∣ d2 then 1/s.g l * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0 
        : by {
          conv{to_rhs, rw sum_comm}, apply sum_congr rfl, intros d1 hd1,
          conv{to_rhs, rw sum_comm}, apply sum_congr rfl, intros d2 hd2,
          apply sum_congr rfl, intros l hl,
          apply ite_eq_of_iff_eq,
          exact dvd_gcd_iff,
          exact λ_, rfl }

  ... = ∑ l in s.P.divisors, 1/s.g l * ∑ d1 d2 in s.P.divisors, if l ∣ d1 ∧ l ∣ d2 then (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0 
        : by { 
          apply sum_congr rfl, intros l hl,
          rw mul_sum, apply sum_congr rfl, intros d1 hd1,
          rw mul_sum, apply sum_congr rfl, intros d2 hd2,
          rw ←ite_mul_zero_right, rw mul_assoc, }
  
  ... = ∑ l in s.P.divisors, 1 / s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d / ↑d * w d else 0)^2 
        : by {
          apply sum_congr rfl, intros l hl,
          suffices : ∑ d1 d2 in s.P.divisors, (if l ∣ d1 ∧ l ∣ d2 then (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0) 
                   = (∑ d in s.P.divisors, if l ∣ d then s.ω d / ↑d * w d else 0)^2, rw this,
          rw sq,
          rw mul_sum, apply sum_congr rfl, intros d1 hd1,
          rw sum_mul, apply sum_congr rfl, intros d2 hd2,
          rw ite_and_mul_zero, ring, }
end

  

--TODO: TIDY UP PROOF
theorem upper_moebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) : 
  upper_moebius $ lambda_squared_of_weights weights :=
begin
  dsimp [upper_moebius, lambda_squared_of_weights],
  intro n, 
  have h_sq: (∑ d in n.divisors, ∑ d1 d2 in d.divisors, if d = nat.lcm d1 d2 then weights d1 * weights d2 else 0)
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