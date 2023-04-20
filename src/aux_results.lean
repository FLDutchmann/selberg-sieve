/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import algebra.big_operators.basic
import algebra.squarefree
import analysis.asymptotics.asymptotics
import number_theory.arithmetic_function
noncomputable theory

open_locale big_operators classical arithmetic_function

open nat nat.arithmetic_function finset tactic.interactive

namespace aux
lemma neq_lcm_of_ndvd {d1 d2 d n : ℕ} (hn: d ∣ n ∧ ¬ n = 0) : (d1 ∣ d → d = 0)  →  ¬ d = d1.lcm d2 :=
begin
  contrapose!,
  intro h,
  rw h,
  split,
  exact d1.dvd_lcm_left d2,
  rw ←h,
  by_contra hd,
  rw hd at hn,
  exact hn.right (zero_dvd_iff.mp hn.left),
end

-- Rephrasing sum_subset_zero_on_sdiff for our context
lemma sum_over_dvd  {α : Type _} [ring α] {P : ℕ} (hP: P ≠ 0) {n : ℕ} (hn : n ∣ P) {f g: ℕ → α} (hf : ∀d:ℕ, d∣P ∧ ¬ d∣n → f d = 0) (hfg : ∀d:ℕ, d∣n → f d = g d): 
  ∑ d in n.divisors, g d = ∑ d in P.divisors, f d   := begin

  apply sum_subset_zero_on_sdiff,
  { exact nat.divisors_subset_of_dvd hP hn,},
  { intros d hd,
    simp at hd,
    specialize hf d,
    have h := ne_zero_of_dvd_ne_zero hP hn,
    apply hf,
    split,
    exact hd.left.left,
    by_contra hd_dvd_n,
    exact h (hd.right hd_dvd_n), },
  { intros d hd,
    simp at hd,
    rw eq_comm,
    apply hfg d,
    exact hd.left, }
end

lemma sum_intro {α : Type _} [ring α] (s : finset ℕ) (p : Prop) [decidable p] (x: α) (d : ℕ) [Π k: ℕ, decidable (k = d ∧ p)] (hd : p → d ∈ s) : 
  ite p x 0 = ∑ k in s, ite (k = d ∧ p) x 0 := 
begin
  by_cases hp : p,
  { rw if_pos hp,
    rw sum_eq_single_of_mem d (hd hp), 
    rw if_pos (⟨rfl, hp⟩: d=d ∧ p),
    intros b hbs hbd, 
    have : ¬(b=d ∧ p),
    push_neg, contrapose!, intro _, exact hbd,
    rw if_neg this, },
  { rw if_neg hp,
    rw sum_eq_zero,
    intros k hk,
    have : ¬(k=d∧p),
    push_neg, intro _, exact hp,
    rw if_neg this, }
end

lemma conv_lambda_sq_larger_sum (weights : ℕ → ℝ) (n : ℕ) : 
    ∑ d in n.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors, ite (d = nat.lcm d1 d2) (weights d1 * weights d2) 0
  = ∑ d in n.divisors, ∑ d1 in n.divisors, ∑ d2 in n.divisors, ite (d = nat.lcm d1 d2) (weights d1 * weights d2) 0 :=
begin
  apply sum_congr rfl,
  intros d hd,
  simp at hd,
  have h_subset : d.divisors ⊆ n.divisors,
  { exact nat.divisors_subset_of_dvd hd.right hd.left },
  have h_zero : ∀ (x : ℕ), x ∈ n.divisors \ d.divisors → ∑ (d2 : ℕ) in n.divisors, ite (d = x.lcm d2) (weights x * weights d2) 0 = 0,
  { intros d1 hd1, 
    apply sum_eq_zero,
    intros d2 hd2,
    rw if_neg,
    simp at hd1,
    exact neq_lcm_of_ndvd hd hd1.right, },
  apply sum_subset_zero_on_sdiff h_subset h_zero,
  intros d1 hd1,
  apply sum_subset_zero_on_sdiff h_subset,
  { intros d2 hd2,
    apply if_neg,
    simp at hd2,
    rw nat.lcm_comm,
    exact neq_lcm_of_ndvd hd hd2.right, },
  { intros d2 hd2,
    refl, }

end
#check @sum_eq_iff_sum_mul_moebius_eq
theorem moebius_inv(n : ℕ) : ∑ d in n.divisors, μ(d) = ite (n=1) 1 0 := 
begin
  by_cases hn : 0<n,
  
  { apply nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq.mpr,
    intros m hm,
    have hm': (m,1) ∈ m.divisors_antidiagonal,
    { apply nat.mem_divisors_antidiagonal.mpr,
      simp,
      linarith only [hm], },

    rw sum_eq_single_of_mem (⟨m,1⟩:ℕ×ℕ) hm', 
    simp,
    intros b hb_pair hb_neq,
    have h_snd : b.snd ≠ 1,
    { by_contra hb_snd,
      have := mem_divisors_antidiagonal.mp hb_pair,
      cases this with h_prod _,
      rw hb_snd at h_prod,
      simp at h_prod,
      simp at hb_neq,
      have hb_eq : b=(m,1) := prod.eq_iff_fst_eq_snd_eq.mpr ⟨h_prod, hb_snd⟩,
      exact hb_neq hb_eq},
    rw if_neg h_snd,
    ring,
    exact hn,
    },
  
  { simp at hn,
    rw if_neg (show ¬n=1, by linarith only [hn]),
    have : n.divisors = ∅,
    { rw hn, refl },
    rw this,
    apply sum_empty }
end

example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
begin
  exact zero_lt_iff,
end

lemma ite_eq_of_iff {α : Type} {p q : Prop} (hpq : p ↔ q) [decidable p] [decidable q] {x y : α} 
  : ite p x y = ite q x y :=
begin
  by_cases h:p,
  { rw if_pos h,
    rw hpq at h,
    rw if_pos h, },
  { rw if_neg h,
    rw hpq at h,
    rw if_neg h, }
end


lemma ite_eq_of_iff_eq {α : Type} [has_zero α] {p q : Prop} (x y : α) (hpq : p ↔ q) [decidable p] [decidable q]  (h_eq : p∧q → x=y) 
  : ite p x 0 = ite q y 0 :=
begin
  by_cases h:p,
  { rw if_pos h,
    specialize h_eq ⟨h, hpq.mp h⟩,
    rw h_eq,
    rw hpq at h,
    rw if_pos h, },
  { rw if_neg h,
    rw hpq at h,
    rw if_neg h, }
end

lemma coprime_of_mul_squarefree (x y : ℕ) (h: squarefree $ x*y) : x.coprime y := 
begin
  by_contra h_ncop,
  rw nat.prime.not_coprime_iff_dvd at h_ncop,
  cases h_ncop with p hp,
  rcases hp with ⟨hpp, hpx, hpy⟩,

  cases hpx with r hx,
  cases hpy with s hy,
  have : p*p ∣ x*y,
  use r*s,
  rw hy, rw hx, ring,
  rw nat.squarefree_iff_prime_squarefree  at h,
  specialize h p hpp,
  exact h this,
end

lemma dvd_iff_mul_of_dvds {P: ℕ} (k d l m: ℕ) (hd: d ∈ P.divisors) : k = d/l ∧ l ∣ d ∧ d ∣ m ↔ d = k*l ∧ d ∣ m := 
begin
  split,
  { intro h, 
    rcases h with ⟨hk_eq, hl_dvd_d, hd_dvd_m⟩,
    split,
    rw hk_eq, rw eq_comm,
    exact nat.div_mul_cancel hl_dvd_d,
    exact hd_dvd_m },
  { intro h,
    cases h with hd_eq hd_dvd_m,
    split,
    have : 0 < l,
    { rw zero_lt_iff,
      simp at hd,
      by_contra h, rw h at hd_eq, simp at hd_eq,
      rw hd_eq at hd, simp at hd, exact hd }, 
    rw hd_eq, rw eq_comm, exact nat.mul_div_cancel k this,
    split,
    use k, rw hd_eq, ring,
    exact hd_dvd_m }
end

lemma divisors_filter_dvd {P : ℕ} (n : ℕ) (hP : P ≠ 0) (hn : n ∣ P) 
  : P.divisors.filter(λk, k ∣ n) = n.divisors := 
begin
  ext k, split,
  intro hk,
  simp at hk, simp,
  split, exact hk.right,
  exact ne_zero_of_dvd_ne_zero hk.left.right hn, 
  
  intro hk,
  simp at hk, simp,
  exact ⟨⟨nat.dvd_trans hk.left hn, hP⟩, hk.left⟩,
end

set_option profiler true
theorem moebius_inv_dvd_lower_bound {P : ℕ} (hP : squarefree P) (l m : ℕ) (hm: m ∣ P) : 
  ∑ d in P.divisors, ite (l ∣ d ∧ d ∣ m) (μ d) 0 = ite (l=m) (μ l) 0 := 
begin
  have hP_ne_zero : P ≠ 0 := squarefree.ne_zero hP,
  have hm_ne_zero : m ≠ 0 := ne_zero_of_dvd_ne_zero hP_ne_zero hm,
  have hl_zero_lt_of_dvd_m : l ∣ m → 0 < l := λhdvd, zero_lt_iff.mpr $ ne_zero_of_dvd_ne_zero hm_ne_zero hdvd,


  calc  ∑ d in P.divisors, ite (l ∣ d ∧ d ∣ m)  (μ d) 0
      = ∑ d k in P.divisors, ite (k = d/l ∧ l ∣ d ∧ d ∣ m) (μ d) 0   
        : by { 
          apply sum_congr rfl, intros d hd, 
          have : l ∣ d ∧ d ∣ m → d/l ∈ P.divisors,
          { intro h_dvd, 
            simp only [mem_divisors], simp only [mem_divisors] at hd,
            split,
            exact nat.dvd_trans (div_dvd_of_dvd h_dvd.left) hd.left,
            exact hd.right, },
          exact sum_intro P.divisors (l ∣ d ∧ d ∣ m) (μ d) (d/l) this, }

  ... = ∑ d k in P.divisors, ite (d = k*l ∧ d ∣ m) (μ $ k*l) 0
        : by {
          apply sum_congr rfl, intros d hd,
          apply sum_congr rfl, intros k hk,
          have h_iff: k = d/l ∧ l ∣ d ∧ d ∣ m ↔ d = k*l ∧ d ∣ m 
            := dvd_iff_mul_of_dvds k d l m hd,
          have h_eq: (k = d/l ∧ l ∣ d ∧ d ∣ m) ∧ (d = k*l ∧ d ∣ m) → (μ d) = (μ (k*l)),
          { intro h, rw h.right.left, },
          apply ite_eq_of_iff_eq  (μ d) (μ $ k*l) h_iff h_eq, }

  ... = ∑ k d in P.divisors, ite (d = k*l ∧ d ∣ m) (μ $ k*l) 0 : sum_comm 

  ... = ∑ k d in P.divisors, ite (d = k*l ∧ k*l ∣ m) (μ $ k*l) 0 
        : by {
          apply sum_congr rfl, intros k hk,
          apply sum_congr rfl, intros d hd,
          apply ite_eq_of_iff,
          split,
          intro h, split,
          exact h.left, rw ← h.left, exact h.right,
          intro h, split,
          exact h.left, rw h.left, exact h.right, } 

  ... = ∑ k in P.divisors, ite (k*l ∣ m) (μ $ k*l) 0
        : by { 
          apply sum_congr rfl, intros k hk,
          rw eq_comm,
          rw sum_intro,
          intro h_klm,
          simp only [mem_divisors], split,
          exact nat.dvd_trans h_klm hm,
          simp only [mem_divisors] at hk,
          exact hk.right, } 

  ... = ∑ k in P.divisors, ite (k*l ∣ m) ((μ k) * (μ l))  0 
        : by {
          apply sum_congr rfl, intros k hk,
          apply ite_eq_of_iff_eq,
          exact iff.rfl,
          intro h, cases h with h _,
          have mult := is_multiplicative_moebius,
          apply is_multiplicative.map_mul_of_coprime mult,
          apply coprime_of_mul_squarefree k l,
          have : k*l ∣ P,
          calc k*l ∣ m : h
                ... ∣ P : hm,
          exact squarefree.squarefree_of_dvd this hP }

  ... = ∑ k in P.divisors, ite (k ∣ m/l ∧ l ∣ m) ((μ k) * (μ l))  0 
        : by {
          apply sum_congr rfl, intros k hk,
          apply ite_eq_of_iff,
          split, intro h, split, 
          rw mul_comm at h,
          exact nat.dvd_div_of_mul_dvd h,
          calc l ∣ k*l : by {use k, ring}
             ... ∣ m   : h,
          intro h,
          have hl_ne_zero: 0 < l := hl_zero_lt_of_dvd_m h.right,
          have: m = m/l * l,
          rw nat.div_mul_cancel h.right,
          rw this,
          exact (nat.mul_dvd_mul_iff_right hl_ne_zero).mpr h.left,  }

  ... = ∑ k in P.divisors, ite (k ∣ m/l)  (ite (l ∣ m) ((μ k) * (μ l)) 0)  0 
        : sum_congr rfl (λk (hk:k∈P.divisors),ite_and (k ∣ m/l) (l∣ m) ((μ k) * (μ l)) 0) 

  ... = ∑ k in P.divisors.filter(λk, k ∣ m/l), ite (l ∣ m) ((μ k) * (μ l)) 0
        : eq_comm.mp $ sum_filter (λk, k ∣ m/l) (λk,ite (l ∣ m) ((μ k) * (μ l)) 0)

  ... = ∑ k in (m/l).divisors, ite (l ∣ m) ((μ k) * (μ l)) 0 
        : by {
          by_cases hlm: l ∣ m,
          { have hmlP : m/l ∣ P := nat.dvd_trans (div_dvd_of_dvd hlm) hm,
            have : P.divisors.filter(λk, k ∣ m/l) = (m/l).divisors 
              := divisors_filter_dvd (m/l) hP_ne_zero hmlP,
            apply sum_congr this (λx hx, rfl) },
          { have :∀ s: finset ℕ,  ∀k, k ∈ s → ite (l ∣ m) ((μ k * μ l)) 0 = 0,
            intros s k hk, apply if_neg hlm,
            rw finset.sum_eq_zero (this $ (m/l).divisors),
            exact finset.sum_eq_zero (this $ P.divisors.filter (λ (k : ℕ), k ∣ m / l)) } }   

  ... = ∑ k in (m/l).divisors, ite (l∣ m) (μ l) 0 * (μ k)  
        : by {
          apply sum_congr rfl, intros k hk,
          rw ite_mul_zero_right, ring, }

  ... = ite (l ∣ m) (μ l) 0 * ∑ k in (m/l).divisors, μ k : by { rw mul_sum, }

  ... = ite (l ∣ m) (μ l) 0 * ite (m/l=1) 1 0 : by rw moebius_inv

  ... = ite (l=m) (μ l * 1) 0 
        : by {
          have : l=m ↔ (l ∣ m ∧ m/l = 1),
          { split,
            intro h_eq,
            rw h_eq, split, exact dvd_rfl, 
            exact nat.div_self (zero_lt_iff.mpr hm_ne_zero),
            intro hlm,
            calc l = m / l * l : by {rw hlm.right, exact eq_comm.mp (one_mul l) } 
               ... = m : nat.div_mul_cancel hlm.left },
          
          rw ite_eq_of_iff this,
          rw ite_and_mul_zero (l ∣ m) (m/l = 1) }

  ... = ite (l=m) (μ l) 0 : ite_eq_of_iff_eq (μ l * 1) (μ l) iff.rfl (λh, mul_one (μ l)),   
end 

example (a b n : ℕ) (hab : a ∣ b) : a ^ n ∣ b ^ n := pow_dvd_pow_of_dvd hab n

lemma lcm_squarefree_of_squarefree {n m : ℕ} (hn : squarefree n) (hm : squarefree m) : squarefree (n.lcm m) := by {
  have hn_ne_zero := squarefree.ne_zero hn,
  have hm_ne_zero := squarefree.ne_zero hm,
  have hlcm_ne_zero := lcm_ne_zero hn_ne_zero hm_ne_zero,
  rw nat.squarefree_iff_factorization_le_one hn_ne_zero at hn,
  rw nat.squarefree_iff_factorization_le_one hm_ne_zero at hm,
  rw nat.squarefree_iff_factorization_le_one hlcm_ne_zero,
  rw nat.factorization_lcm hn_ne_zero hm_ne_zero,
  intro p,
  simp only [finsupp.sup_apply, sup_le_iff],
  exact ⟨hn p, hm p⟩,

  -- COMMENT OF SHAME:
  /-
  dsimp only [squarefree] at *,
  intros x hx,
  rw nat.is_unit_iff,
  rw nat.eq_one_iff_not_exists_prime_dvd,
  intros p hp,
  by_contra hpx,
  have hp2 : p^2 ∣ n.lcm m,
  calc p^2 ∣ x^2 : pow_dvd_pow_of_dvd hpx 2
       ... = x*x : sq x
       ... ∣ n.lcm m : hx, 
  have : 2 ≤ (n.lcm m).factorization p,
  { exact (prime.pow_dvd_iff_le_factorization hp (nat.lcm_ne_zero (hn_ne_zero) (hm_ne_zero))).mp hp2, },
  rw nat.factorization_lcm hn_ne_zero hm_ne_zero at this,
  simp only [finsupp.sup_apply, le_sup_iff] at this,
  have casework : ∀(r:ℕ), (∀(x:ℕ), (x*x ∣ r → is_unit x)) → (2 ≤ (r.factorization) p) → false,
  { intros r hr hr2, 
    rw ←prime.pow_dvd_iff_le_factorization hp (squarefree.ne_zero hr) at hr2,
    rw sq at hr2,
    specialize hr p,  specialize hr hr2,
    rw nat.is_unit_iff at hr,
    exact (nat.prime.ne_one hp) hr, },

  cases this with hn_sq hm_sq,
  { exact casework n hn hn_sq },
  { exact casework m hm hm_sq }, -/
}



example (n m : ℕ) (h : squarefree (n*m)) : n.coprime m := coprime_of_mul_squarefree n m h

lemma mult_gcd_lcm_of_squarefree (f: ℕ → ℝ) (h_mult: ∀(a b:ℕ), a.coprime b → f(a*b) = f a * f b) (x y : ℕ) (hx : squarefree x) (hy : squarefree y)
: f x * f y = f(x.lcm y) * f(x.gcd y) := begin
  have hgcd : squarefree (x.gcd y),
  { apply squarefree.squarefree_of_dvd _ hx, exact nat.gcd_dvd_left x y, },
  dsimp only [nat.lcm],
  have hassoc : x * y / x.gcd y = x * (y / x.gcd y),
  { exact nat.mul_div_assoc x (nat.gcd_dvd_right x y)},
  rw hassoc,
  have hx_cop_yg : x.coprime (y/x.gcd y),
  { apply coprime_of_mul_squarefree,
    rw ←hassoc, exact lcm_squarefree_of_squarefree hx hy },
  rw h_mult x (y/ x.gcd y) hx_cop_yg,
  have : (y / x.gcd y).coprime (x.gcd y),
  { apply coprime_of_mul_squarefree,
    rw nat.div_mul_cancel (nat.gcd_dvd_right x y), 
    exact hy },
  rw mul_assoc,
  rw ←h_mult _ _ this, 
  rw nat.div_mul_cancel (nat.gcd_dvd_right x y),
end 

lemma gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m*n :=
begin
  calc m.gcd n ∣ m     : nat.gcd_dvd_left m n
           ... ∣ m * n : ⟨n, rfl⟩, 
end

lemma multiplicative_zero_of_zero_dvd (f: ℕ → ℝ) (h_mult: ∀(a b:ℕ), a.coprime b → f(a*b) = f a * f b) (m n : ℕ) (hmn : m ∣ n) (h_zero : f m = 0)
 : f m = 0 :=
begin
  
end 
end aux