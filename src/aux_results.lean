/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import algebra.big_operators.basic
import algebra.squarefree
import analysis.asymptotics.asymptotics
import number_theory.arithmetic_function
import tactic.induction
import data.list.func
noncomputable theory

open_locale big_operators classical arithmetic_function

open nat nat.arithmetic_function finset tactic.interactive

namespace aux

def multiplicative (f : ℕ → ℝ) : Prop := 
  f 1 = 1 ∧ ∀(x y : ℕ), x.coprime y → f (x*y) = f x * f y


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
  ∑ d in n.divisors, g d = ∑ d in P.divisors, f d   := 
begin

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

lemma sum_over_dvd_ite  {α : Type _} [ring α] {P : ℕ} (hP: P ≠ 0) {n : ℕ} (hn : n ∣ P) {f: ℕ → α}: 
  ∑ d in n.divisors, f d = ∑ d in P.divisors, if d ∣ n then f d else 0   := 
begin
  apply sum_subset_zero_on_sdiff,
  { exact nat.divisors_subset_of_dvd hP hn,},
  { intros d hd,
    apply if_neg,
    rw [finset.mem_sdiff, nat.mem_divisors, nat.mem_divisors] at hd,
    push_neg at hd,
    by_contra h,
    have : n=0 := hd.right h,
    exact (ne_zero_of_dvd_ne_zero hP hn) this },
  { intros d hd,
    rw if_pos,
    rw mem_divisors at hd,
    exact hd.left }
end

lemma sum_intro {α : Type _} [ring α] (s : finset ℕ) (p : Prop) [decidable p] (x: α) (d : ℕ) [Π k: ℕ, decidable (k = d ∧ p)] (hd : p → d ∈ s) : 
  (if p then x else 0) = ∑ k in s, if k = d ∧ p then x else 0 := 
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
   (∑ d in n.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = nat.lcm d1 d2 then weights d1 * weights d2 else 0)
  = ∑ d in n.divisors, ∑ d1 in n.divisors, ∑ d2 in n.divisors, if d = nat.lcm d1 d2 then weights d1 * weights d2 else 0 :=
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

theorem moebius_inv(n : ℕ) : ∑ d in n.divisors, μ(d) = if n=1 then 1 else 0 := 
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

lemma ite_eq_of_iff {α : Type} {p q : Prop} (hpq : p ↔ q) [decidable p] [decidable q] {x y : α} 
  : (if p then x else y) = if q then x else y :=
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
  : (if p then x else 0) = if q then y else 0 :=
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

--set_option profiler true
theorem moebius_inv_dvd_lower_bound {P : ℕ} (hP : squarefree P) (l m : ℕ) (hm: m ∣ P) : 
  ∑ d in P.divisors, (if l ∣ d ∧ d ∣ m then μ d else 0) = if l=m then μ l else 0 := 
begin
  have hP_ne_zero : P ≠ 0 := squarefree.ne_zero hP,
  have hm_ne_zero : m ≠ 0 := ne_zero_of_dvd_ne_zero hP_ne_zero hm,
  have hl_zero_lt_of_dvd_m : l ∣ m → 0 < l := λhdvd, zero_lt_iff.mpr $ ne_zero_of_dvd_ne_zero hm_ne_zero hdvd,


  calc  ∑ d in P.divisors, (if l ∣ d ∧ d ∣ m then μ d else 0)
      = ∑ d k in P.divisors, if k = d/l ∧ l ∣ d ∧ d ∣ m then μ d else 0   
        : by { 
          apply sum_congr rfl, intros d hd, 
          have : l ∣ d ∧ d ∣ m → d/l ∈ P.divisors,
          { intro h_dvd, 
            simp only [mem_divisors], simp only [mem_divisors] at hd,
            split,
            exact nat.dvd_trans (div_dvd_of_dvd h_dvd.left) hd.left,
            exact hd.right, },
          exact sum_intro P.divisors (l ∣ d ∧ d ∣ m) (μ d) (d/l) this, }

  ... = ∑ d k in P.divisors, if d = k*l ∧ d ∣ m then μ $ k*l else 0
        : by {
          apply sum_congr rfl, intros d hd,
          apply sum_congr rfl, intros k hk,
          have h_iff: k = d/l ∧ l ∣ d ∧ d ∣ m ↔ d = k*l ∧ d ∣ m 
            := dvd_iff_mul_of_dvds k d l m hd,
          have h_eq: (k = d/l ∧ l ∣ d ∧ d ∣ m) ∧ (d = k*l ∧ d ∣ m) → (μ d) = (μ (k*l)),
          { intro h, rw h.right.left, },
          apply ite_eq_of_iff_eq  (μ d) (μ $ k*l) h_iff h_eq, }

  ... = ∑ k d in P.divisors, if d = k*l ∧ d ∣ m then μ $ k*l else 0 : sum_comm 

  ... = ∑ k d in P.divisors, if d = k*l ∧ k*l ∣ m then μ $ k*l else 0 
        : by {
          apply sum_congr rfl, intros k hk,
          apply sum_congr rfl, intros d hd,
          apply ite_eq_of_iff,
          split,
          intro h, split,
          exact h.left, rw ← h.left, exact h.right,
          intro h, split,
          exact h.left, rw h.left, exact h.right, } 

  ... = ∑ k in P.divisors, if k*l ∣ m then μ $ k*l else 0
        : by { 
          apply sum_congr rfl, intros k hk,
          rw eq_comm,
          rw sum_intro,
          intro h_klm,
          simp only [mem_divisors], split,
          exact nat.dvd_trans h_klm hm,
          simp only [mem_divisors] at hk,
          exact hk.right, } 

  ... = ∑ k in P.divisors, if k*l ∣ m then (μ k) * (μ l) else 0 
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

  ... = ∑ k in P.divisors, if k ∣ m/l ∧ l ∣ m then (μ k) * (μ l) else 0 
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

  ... = ∑ k in P.divisors, if k ∣ m/l then  (if l ∣ m then (μ k) * (μ l) else 0) else 0 
        : sum_congr rfl (λk (hk:k∈P.divisors),ite_and (k ∣ m/l) (l∣ m) ((μ k) * (μ l)) 0) 

  ... = ∑ k in P.divisors.filter(λk, k ∣ m/l), if l ∣ m then (μ k) * (μ l) else 0
        : eq_comm.mp $ sum_filter (λk, k ∣ m/l) (λk,ite (l ∣ m) ((μ k) * (μ l)) 0)

  ... = ∑ k in (m/l).divisors, if l ∣ m then (μ k) * (μ l) else 0 
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

  ... = ∑ k in (m/l).divisors, (if l∣ m then μ l else 0) * μ k  
        : by {
          apply sum_congr rfl, intros k hk,
          rw ite_mul_zero_right, ring, }

  ... = (if l ∣ m then μ l else 0) * ∑ k in (m/l).divisors, μ k : by { rw mul_sum, }

  ... = (if l ∣ m then μ l else 0) * if m/l=1 then 1 else 0 : by rw moebius_inv

  ... = if l=m then μ l * 1 else 0 
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

  ... = if l=m then μ l else 0 : ite_eq_of_iff_eq (μ l * 1) (μ l) iff.rfl (λh, mul_one (μ l)),   
end 

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : squarefree P) (l m : ℕ) (hm: m ∣ P) : 
  ∑ d in P.divisors, (if l ∣ d ∧ d ∣ m then (μ d:ℝ) else 0) = if l=m then (μ l:ℝ) else 0 := 
begin
  norm_cast,
  apply moebius_inv_dvd_lower_bound hP l m hm,
end


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
}



example (n m : ℕ) (h : squarefree (n*m)) : n.coprime m := coprime_of_mul_squarefree n m h

lemma mult_gcd_lcm_of_squarefree (f: ℕ → ℝ) (h_mult: multiplicative f) (x y : ℕ) (hx : squarefree x) (hy : squarefree y)
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
  rw h_mult.right x (y/ x.gcd y) hx_cop_yg,
  have : (y / x.gcd y).coprime (x.gcd y),
  { apply coprime_of_mul_squarefree,
    rw nat.div_mul_cancel (nat.gcd_dvd_right x y), 
    exact hy },
  rw mul_assoc,
  rw ←h_mult.right _ _ this, 
  rw nat.div_mul_cancel (nat.gcd_dvd_right x y),
end 

lemma gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m*n :=
begin
  calc m.gcd n ∣ m     : nat.gcd_dvd_left m n
           ... ∣ m * n : ⟨n, rfl⟩, 
end

lemma multiplicative_zero_of_zero_dvd (f: ℕ → ℝ) (h_mult: multiplicative f) {m n : ℕ} (h_sq : squarefree n) (hmn : m ∣ n) (h_zero : f m = 0)
 : f n = 0 :=
begin
  cases hmn with k hk,
  rw hk,
  rw hk at h_sq,
  have : m.coprime k := coprime_of_mul_squarefree m k h_sq,
  rw h_mult.right m k this,
  rw h_zero, simp only [zero_mul, eq_self_iff_true],
end 

example (t : finset ℕ) : t.val.prod = t.prod id := prod_val t

lemma prod_subset_factors_of_mult(f: ℕ → ℝ) (h_mult: multiplicative f) {l : ℕ} (hl : squarefree l):
 ∀(t: finset ℕ), t ⊆ l.factors.to_finset → ∏ (a : ℕ) in t, f a = f t.val.prod := 
begin
  intro t, intro ht, rw prod_val t, revert ht, apply finset.induction_on t, 
  intro h, 
  simp only [eq_self_iff_true, finset.prod_empty, finset.empty_val, multiset.prod_zero, h_mult.left],
  rename t α,
  intros p t hpt h_ind h_sub,
  have ht_sub : t ⊆ l.factors.to_finset,
  { exact finset.subset.trans (finset.subset_insert p t) h_sub, },
  have hl_primes : ∀(a:ℕ), a ∈ l.factors.to_finset → a.prime,
  { intros a hal,
    rw list.mem_to_finset at hal, 
    exact nat.prime_of_mem_factors hal, }, 
  have ht_primes : ∀(a:ℕ), a∈t → a.prime,
  { intros a ha, apply hl_primes a,
    apply mem_of_subset ht_sub ha, }, 
  have hp_prime : p.prime,
  { apply hl_primes p, apply mem_of_subset h_sub, exact mem_insert_self p t, },
  have hp_cop : p.coprime (t.prod id),
  { rw nat.prime.coprime_iff_not_dvd hp_prime, 
    rw prime.dvd_finset_prod_iff (nat.prime_iff.mp hp_prime) id,
    push_neg, intros a ha, by_contra hpa,
    rw id.def at hpa, 
    have : p=a := eq_comm.mp ((nat.prime.dvd_iff_eq (ht_primes a ha) (nat.prime.ne_one hp_prime) ).mp hpa),
    rw this at hpt,
    exact hpt ha, }, 
  specialize h_ind ht_sub,
  calc  ∏ (a : ℕ) in insert p t, f a 
      = f p * ∏ (a : ℕ) in t, f a : prod_insert hpt
  
  ... = f p * f (t.prod id) : by { rw h_ind }
  
  ... = f (p * ∏ a in t, a) : by {rw h_mult.right p (∏ a in t, a) hp_cop, refl,}
  
  ... = f (∏ a in (insert p t), a) : by {rw ←prod_insert hpt, }
end

lemma eq_prod_set_factors_of_squarefree {l:ℕ} (hl : squarefree l) :
  l.factors.to_finset.val.prod = l :=
begin
  suffices : l.factors.to_finset.val = l.factors, 
  {rw this, rw multiset.coe_prod, exact prod_factors (squarefree.ne_zero hl) },
  ext p,
  rw list.to_finset_val,
  rw multiset.coe_count, rw multiset.coe_count,
  rw list.count_dedup,
  rw eq_comm,
  apply list.count_eq_of_nodup,
  apply (squarefree_iff_nodup_factors _).mp hl,
  exact squarefree.ne_zero hl,
end

lemma prod_factors_of_mult (f: ℕ → ℝ) (h_mult: multiplicative f) {l : ℕ} (hl : squarefree l):
  ∏ (a : ℕ) in l.factors.to_finset, f a = f l := 
begin
  rw prod_subset_factors_of_mult f h_mult hl l.factors.to_finset finset.subset.rfl,
  suffices : l.factors.to_finset.val.prod = l, rw this,
  exact eq_prod_set_factors_of_squarefree hl,
end

lemma prod_add_mult (f: ℕ → ℝ) (h_mult: multiplicative f) {l : ℕ} (hl : squarefree l):
  ∏ p in l.factors.to_finset, (1+f p) = ∑ d in l.divisors, f d := 
begin
  conv { to_lhs, congr, skip, funext, rw add_comm, },
  rw finset.prod_add,
  conv { to_lhs, congr, skip, funext, conv { congr, skip, rw prod_eq_one (λ _ _, rfl) }, rw mul_one, },

  have : l.divisors.filter squarefree = l.divisors,
  { ext x, split,
    apply filter_subset,
    intro hx, simp only [finset.mem_filter], split, 
    exact hx, rw mem_divisors at hx, exact squarefree.squarefree_of_dvd hx.left hl,},
  conv{ to_rhs, congr, rw ←this, },

  rw nat.sum_divisors_filter_squarefree,
  
  have hfact_eq : l.factors.to_finset.powerset = (unique_factorization_monoid.normalized_factors l).to_finset.powerset,
  { rw nat.factors_eq,  simp, }, 
  
  apply sum_congr hfact_eq,
   
  intros t ht,
  rw ←hfact_eq at ht, 
  rw mem_powerset at ht,
  exact prod_subset_factors_of_mult f h_mult hl t ht,

  exact squarefree.ne_zero hl,
end

lemma prod_eq_moebius_sum (f: ℕ → ℝ) (h_mult: multiplicative f) {l : ℕ} (hl : squarefree l):
  ∏ p in l.factors.to_finset, (1-f p) = ∑ d in l.divisors, μ d * f d := 
begin
  suffices : ∏ p in l.factors.to_finset, ((1:ℝ) + (λ(x:ℕ), ((μ x):ℝ) * f x ) p) = ∑ d in l.divisors, μ d * f d,
  { rw ← this, 
    apply prod_congr rfl, intros p hp, 
    rw list.mem_to_finset at hp,
    have hp_prime : p.prime, 
    { apply prime_of_mem_factors hp, },

    calc 1 - f p = 1 + μ p * f p : by{ 
        rw arithmetic_function.moebius_apply_prime hp_prime, 
        push_cast, ring,}, },

  apply prod_add_mult,
  { split, 
    calc (μ 1:ℝ) * f 1 = 1 : by {
      rw arithmetic_function.moebius_apply_one, 
      rw h_mult.left, push_cast, ring,},
    intros a b hab,
    calc  (μ (a*b):ℝ) * f (a*b) 
        = (μ a * μ b) * (f a * f b) 
          : by {
            rw arithmetic_function.is_multiplicative_moebius.right hab,
            rw h_mult.right a b hab, push_cast,} 
       
    ... = (μ a:ℝ)*f a *((μ b:ℝ) * f b) : by ring, },
  exact hl,
end 

lemma prod_le_prod_of_nonempty {t : finset ℕ} (f g : ℕ → ℝ) 
  (hf : ∀n:ℕ, n∈t → 0 < f n)  (hfg : ∀n:ℕ, n∈t → f n < g n) (h_ne : t.nonempty) :
  ∏ p in t, f p  < ∏ p in t, g p  :=
begin
  have hg : ∀n:ℕ, n∈t → 0 < g n,
  { intros n hn, exact lt_trans (hf n hn) (hfg n hn) },
  revert h_ne hf hg hfg,
  apply finset.induction_on t,
  simp,
  intros q s hqs h_ind _ _ _ _,
  have hq_in : q ∈ insert q s,
  { rw finset.mem_insert, exact or.intro_left (q∈s) (rfl:q=q),  },
  rw prod_insert hqs,
  rw prod_insert hqs,
  apply mul_lt_mul,
  exact hfg q hq_in,
  by_cases hs_ne : s.nonempty,
  { apply le_of_lt,
    apply h_ind hs_ne,
    { intros n hn, apply hf, rw mem_insert, exact or.intro_right (n=q) hn, },
    { intros n hn, apply hg, rw mem_insert, exact or.intro_right (n=q) hn, },
    { intros n hn, apply hfg, rw mem_insert, exact or.intro_right (n=q) hn, }, },
  { suffices : s=∅, rw this, simp only [le_refl, finset.prod_empty],
    rw not_nonempty_iff_eq_empty at hs_ne, exact hs_ne, },
  apply prod_pos, intros p hps, apply hf p, rw mem_insert, exact or.intro_right (p=q) hps,
  apply le_of_lt, exact hg q hq_in,
end

lemma div_mult_of_dvd_squarefree (f : ℕ → ℝ) (h_mult: multiplicative f)
  (l d : ℕ) (hdl : d ∣ l) (hl : squarefree l) (hd: f d ≠ 0): f l / f d = f (l/d) :=
begin
  apply div_eq_of_eq_mul hd,
  have : l/d * d = l,
  { apply nat.div_mul_cancel hdl },
  rw ←h_mult.right,
  rw this,
  apply coprime_of_mul_squarefree,
  rw this, exact hl,
end

lemma div_mult_of_mult {f g : ℕ → ℝ} (hf : multiplicative f) (hg : multiplicative g) (hg_zero: ∀n:ℕ, 0 < n → g n ≠ 0) :
  multiplicative (f/g) :=
begin
  split,
  calc (f/g) 1 = f 1 / g 1 : rfl
           ... = 1 : by {rw hf.left, rw hg.left, ring},
  intros x y hxy,
  calc (f/g) (x*y) = f (x*y) / g (x*y) : rfl
               ... = f x * f y / (g x * g y) : by {rw hf.right x y hxy, rw hg.right x y hxy, }
               ... = f x/g x * (f y/g y) : by {rw ←div_div, ring,}
               ... = (f/g) x * (f/g) y : rfl
end

lemma coe_mult : multiplicative (λ(n:ℕ), (n:ℝ)) :=
begin
  split, exact nat.cast_one,
  intros x y hxy,
  calc ↑(x*y) = ↑x * ↑y : cast_mul x y,
end

lemma mult_mul_of_mult (f g : ℕ → ℝ) (hf : multiplicative f) (hg : multiplicative g) : multiplicative (f*g) :=
begin
  split,
  dsimp only [multiplicative] at *,
  calc f 1 * g 1 = 1 : by { rw hf.left, rw hg.left, ring },
  intros x y hxy,
  calc (f $ x*y) * (g $ x*y) = f x * g x * (f y * g y) : by {rw hf.right x y hxy, rw hg.right x y hxy, ring,}
end


lemma mult_prod_factors (f : ℕ → ℝ) : multiplicative (λd, ∏ p in d.factors.to_finset, f p) :=
begin
  split,
  simp,
  intros x y hxy,
  simp,
  have h_union : (x*y).factors.to_finset = x.factors.to_finset ∪ y.factors.to_finset,
  { ext p, rw list.mem_to_finset, rw ←list.to_finset_union, rw list.mem_to_finset, 
    exact nat.mem_factors_mul_of_coprime hxy p, },
  have h_disj : disjoint x.factors.to_finset y.factors.to_finset,
  { rw list.disjoint_to_finset_iff_disjoint, exact nat.coprime_factors_disjoint hxy, },

  rw ←finset.prod_disj_union h_disj, rw finset.disj_union_eq_union, rw h_union,
end

lemma moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : squarefree l) : 
  (μ l)^2 = 1 :=
begin
  rw arithmetic_function.moebius_apply_of_squarefree hl,
  rw ←pow_mul, rw mul_comm, rw pow_mul, rw neg_one_sq, rw one_pow,
end
lemma abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : squarefree l) : 
  |μ l| = 1 :=
begin
  rw arithmetic_function.moebius_apply_of_squarefree hl,
  rw abs_pow, simp,
end

theorem eq_one_of_prod_eq_one {α : Type _} (s : finset α) (f : α → ℕ) (hp: ∏ i in s, f i = 1) : ∀ i∈s, f i = 1 := 
begin
  revert hp,
  apply finset.induction_on s,
  simp,
  intros j s hj h_ind heq_one i hi,
  rw finset.prod_insert hj at heq_one,
  rw mem_insert at hi,
  cases hi,
  { rw hi, exact nat.eq_one_of_mul_eq_one_right heq_one, },
  exact h_ind (nat.eq_one_of_mul_eq_one_left heq_one) i hi,
end

theorem fintype_eq_one_of_prod_eq_one {α : Type _} [fintype α] (f : α → ℕ) (hp: ∏ i in finset.univ, f i = 1) : ∀ i, f i = 1 := 
begin
  intro i,
  apply eq_one_of_prod_eq_one finset.univ f hp,
  exact mem_univ i,
end


lemma prime_dvd_prod {α : Type _} {p : ℕ} (hp : p.prime) {s : finset α} (f : α → ℕ) (h_prod : p ∣ ∏ i in s, f i ) :
  ∃ i, p ∣ f i := 
begin
  revert h_prod,
  apply finset.induction_on s,
  rw [prod_empty], intro hp_one, exfalso, rw nat.dvd_one at hp_one, exact nat.prime.ne_one hp hp_one,
  intros a s ha ih hprod,
  rw [prod_insert ha, nat.prime.dvd_mul hp] at hprod,
  cases hprod,
  use a, exact hprod, exact ih hprod,
end


theorem card_distinct_factors_eq_card_factors_of_squarefree {n : ℕ} (hn : squarefree n) :
  ω n = Ω n := 
(arithmetic_function.card_distinct_factors_eq_card_factors_iff_squarefree $ squarefree.ne_zero hn).mpr hn


def tuples_with_prod (h d P : ℕ) : finset (fin h → ℕ) :=
  ((fintype.pi_finset (λ(i: fin h), P.divisors))
     .filter (λ (s:fin h → ℕ), ∏ i, s i = d))

@[simp]
def mem_tuples_with_prod {h d P : ℕ} {s : fin h → ℕ } : 
  s ∈ tuples_with_prod h d P ↔ (∀ i, s i ∈ P.divisors) ∧ ∏ i, s i = d :=
begin
  dsimp only [tuples_with_prod],
  rw [mem_filter, fintype.mem_pi_finset],
end

-- Perhaps there is a better way to do this with partitions, but the proof isn't too bad
-- |{(d1, ..., dh) : d1*...*dh = d}| = h^ω(d)
theorem card_tuples_with_prod {P d : ℕ} (hP: squarefree P) (hdP : d ∣ P) (h : ℕ) :
    (tuples_with_prod h d P).card = h^ω d :=
begin
  revert hdP, 
  dsimp only [tuples_with_prod],
  apply nat.strong_induction_on d,
  clear d, intro d,
  intros h_ind hdP,

  have hd_sqfree : squarefree d := squarefree.squarefree_of_dvd hdP hP,
  have hd_zero : d ≠ 0 := squarefree.ne_zero hd_sqfree, 
  have hP_ne_zero : P ≠ 0 := squarefree.ne_zero hP,
  by_cases h_1 : d = 1,
  { rw h_1, rw (show h ^ ω 1 = 1, by simp only [eq_self_iff_true, pow_zero, nat.arithmetic_function.card_distinct_factors_one]),
    
    
    apply card_eq_one.mpr, use (λ _, 1),
    ext, rw [mem_singleton, mem_filter, fintype.mem_pi_finset], split,
    { intro h, ext, apply fintype_eq_one_of_prod_eq_one a h.right },
    { intro h, rw h, split, intro i,  rw one_mem_divisors, exact squarefree.ne_zero hP,
      apply prod_eq_one, intros _ _, refl } },
  have := exists_prime_and_dvd h_1,
  rcases this with ⟨p, ⟨hp_prime, hp_dvd⟩⟩,

  let S := tuples_with_prod h d P,
  let Sp_dvd : (fin h) → (finset _) := λj, S.filter(λ(s : fin h → ℕ), p ∣ s j ),
  
  have hunion :  finset.univ.bUnion Sp_dvd = S,
  { ext s, rw mem_bUnion, split,
    { rintros ⟨i, _, hi⟩, rw mem_filter at hi, exact hi.1, },
    intro hs,
    rw mem_tuples_with_prod at hs,
    rw [←hs.2] at hp_dvd,
    rw [←finset.to_list_to_finset univ, list.prod_to_finset s _, prime.dvd_prod_iff] at hp_dvd,
    rcases hp_dvd with ⟨si, ⟨hsi, hpsi⟩⟩,
    rw list.mem_map at hsi,
    rcases hsi with ⟨i, ⟨_ , hsi⟩⟩,
    use i, split, exact mem_univ i,
    rw mem_filter,
    rw ←hsi at hpsi,
    exact ⟨ mem_tuples_with_prod.mpr hs, hpsi⟩,  
    rw ←nat.prime_iff, exact hp_prime,
    apply finset.nodup_to_list, },

  have hdisj : ∀(i:fin h), i ∈ (finset.univ:finset$fin h) → ∀(j:fin h), j ∈ (finset.univ:finset$fin h) → 
               i≠j → disjoint (Sp_dvd i) (Sp_dvd j),
  { intros i _ j _ hij,
    rw disjoint_iff_ne,
    intros s hs t ht,
    rw [mem_filter, mem_tuples_with_prod] at hs ht,
    by_contra hst,
    rw hst at hs,
    have : (t i).coprime (t j),
    { apply coprime_of_mul_squarefree,
      apply squarefree.squarefree_of_dvd _ hd_sqfree,
      calc t i * t j ∣ t i * t j * ∏ k in (univ.erase i).erase j, t k : ⟨∏ k in (univ.erase i).erase j, t k, rfl⟩
                 ... = t i * ∏ k in univ.erase i, t k : by {
                      rw [mul_assoc, mul_prod_erase],
                      rw mem_erase,
                      exact ⟨ne_comm.mp hij, mem_univ j⟩ }
                 ... = d : by rw [mul_prod_erase _ _ (mem_univ i), hs.1.2],},
    apply absurd this,
    rw nat.prime.not_coprime_iff_dvd, 
    use p, exact ⟨hp_prime, hs.2, ht.2⟩, },
  dsimp only [S, tuples_with_prod] at hunion, 
  rw ←hunion,
  rw finset.card_bUnion hdisj,
  cases hp_dvd with k hk,
  have hp_dvd : p ∣ d, { use k, exact hk },
  have hp_ne_zero : p ≠ 0 := ne_zero_of_dvd_ne_zero hd_zero hp_dvd,
  have hp_pos : 0 < p := (zero_lt_iff.mpr hp_ne_zero),

  let f : fin h → Π(s: fin h → ℕ ), s ∈ tuples_with_prod h k P → (fin h → ℕ) :=
    λ i s hs, (λ j, if i=j then p*s j else s j),

  have himg : ∀ i s (hs : s ∈ tuples_with_prod h k P), f i s hs ∈ Sp_dvd i,
  { intros i s hs, 
    rw mem_tuples_with_prod at hs, 
    rw [mem_filter, mem_tuples_with_prod], dsimp only [f], split, split,
    intro j,
    by_cases hij : i=j,
    { rw if_pos hij, 
      rw mem_divisors,
      split, 
      calc p * s j ∣ p * ∏ j,  s j : by{
        rw mul_dvd_mul_iff_left hp_ne_zero,
        apply finset.dvd_prod_of_mem s (mem_univ j) }
               ... = d : by rw [hs.2, hk]
               ... ∣ P : hdP,
      exact hP_ne_zero, },
    { rw if_neg hij, exact hs.1 j,},
    calc ∏ (j : fin h), ite (i = j) (p * s j) (s j)
           = p * s i * ∏ j in univ.erase i, s j : by {
            rw ←mul_prod_erase univ _ (mem_univ i),
            rw [if_pos rfl],
            apply congr_arg (λ x, p * s i * x),
            apply prod_congr rfl, intros j hj,
            rw [mem_erase, ne_comm] at hj,
            rw if_neg hj.1, }
       ... = d : by rw [mul_assoc, mul_prod_erase _ _ (mem_univ i), hs.2, hk],
    rw if_pos rfl, use s i },

  have hinj : ∀ i s t (hs : s ∈ tuples_with_prod h k P) (ht : t ∈ tuples_with_prod h k P),
     f i s hs = f i t ht → s = t,
  { intros i s t hs ht hfst, funext j,
    by_cases hij : i=j,
    { rw ←mul_right_inj' hp_ne_zero,
      calc  p * s j = f i s hs j : (eq_comm.mp $ if_pos hij)
                ... = f i t ht j : by rw hfst
                ... = p * t j    : if_pos hij },
    { calc s j = f i s hs j : (eq_comm.mp $ if_neg hij)
           ... = f i t ht j : by rw hfst
           ... = t j        : if_neg hij } },


  have hsurj : ∀ i t (ht : t ∈ Sp_dvd i), (∃ s (hs : s∈tuples_with_prod h k P), f i s hs  = t),
  { intros i t ht,
    rw mem_filter at ht, dsimp only [f],
    dsimp only [S] at ht,
    rw mem_tuples_with_prod at ht,
    let s := λj, if i=j then t j / p else t j,
    use s, split, 
    rw mem_tuples_with_prod, split,
    intro j, 
    dsimp only [s],
    by_cases hij : i=j,
    { rw if_pos hij, 
      rw mem_divisors,
      split, rw ←hij,
      calc _ ∣ t i : div_dvd_of_dvd ht.2
         ... ∣ P : (mem_divisors.mp (ht.1.1 i)).1,
      exact squarefree.ne_zero hP },
    { rw if_neg hij, exact ht.1.1 j },
    dsimp only [s],
    calc  ∏ j, ite (i=j) (t j / p) (t j) 
        = t i / p * ∏ j in univ.erase i, t j : by {
          rw ←finset.mul_prod_erase univ s (mem_univ i),
          dsimp only [s], rw if_pos rfl,
          apply congr_arg (λ x, t i / p * x),
          apply prod_congr rfl, intros j hj,
          rw [mem_erase, ne_comm] at hj,
          rw if_neg hj.1 }
    ... = t i * (∏ j in univ.erase i, t j) / p : by {
          conv{to_rhs, rw mul_comm}, 
          rw [nat.mul_div_assoc _ ht.2, mul_comm] }
    ... = d / p : by rw [finset.mul_prod_erase univ t (mem_univ i), ht.1.2]
    ... = k     : by { rw hk, exact nat.mul_div_cancel_left k hp_pos },
    funext j,
    dsimp only [s],
    by_cases hij : i=j,
    { rw [if_pos hij, if_pos hij, nat.mul_div_cancel'],
      rw ←hij, exact ht.2 },
    { rw [if_neg hij, if_neg hij] } },

  have hd_sq : squarefree d := squarefree.squarefree_of_dvd hdP hP,
  have hk_dvd : k ∣ d, { use p, rw mul_comm, exact hk },
  have hk_sq : squarefree k := 
    squarefree.squarefree_of_dvd hk_dvd hd_sq,
  

  calc  ∑ i, (Sp_dvd i).card
      = ∑ (i : fin h), (tuples_with_prod h k P).card 
        : by { 
          apply sum_congr rfl, intros i _, rw eq_comm, 
          apply finset.card_congr (f i) (himg i) (hinj i) (hsurj i),}
  ... = h ^ ω d 
        : by {
          rw fin.sum_const,
          dsimp only [tuples_with_prod],
          rw [h_ind k _ _, smul_eq_mul, ←pow_succ],
          rw [card_distinct_factors_eq_card_factors_of_squarefree hd_sq,
              card_distinct_factors_eq_card_factors_of_squarefree hk_sq,
              ←arithmetic_function.card_factors_apply_prime hp_prime,
              ←nat.arithmetic_function.card_factors_mul, mul_comm, hk],
          exact squarefree.ne_zero hk_sq, exact nat.prime.ne_zero hp_prime,
          apply lt_of_le_of_ne, apply le_of_dvd _ hk_dvd, rw zero_lt_iff, exact hd_zero,
          rw [←one_mul k, hk], apply ne_of_lt, apply mul_lt_mul, exact prime.one_lt hp_prime,
          exact le_rfl, rw zero_lt_iff, exact squarefree.ne_zero hk_sq,
          exact zero_le p,
          calc k ∣ d : by {use p, rw hk, ring,}
           ...   ∣ P : hdP },

end

lemma nat_lcm_mul_left (a b c : ℕ) : (a*b).lcm (a*c) = a * b.lcm c :=
begin
    rw [←lcm_eq_nat_lcm, lcm_mul_left],
    dsimp, rw mul_one,
    rw [lcm_eq_nat_lcm],
end

lemma prod3 (a : fin 3 → ℕ) : ∏ i, a i = a 0 * a 1 * a 2 :=
begin
  rw [fin.prod_univ_succ, fin.prod_univ_succ, fin.prod_univ_succ],
  ring,
end

theorem card_lcm_eq {n : ℕ} (hn : squarefree n) : 
  finset.card ((n.divisors ×ˢ n.divisors).filter (λ (p:ℕ×ℕ), n=p.fst.lcm p.snd)) = 3^ω n :=
begin
  rw [←card_tuples_with_prod hn dvd_rfl 3, eq_comm],
  have hn_ne_zero : n ≠ 0 := squarefree.ne_zero hn,

  let f : Π (a : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n), (ℕ × ℕ) :=
    λ a ha, (a 0 * a 1, a 0 * a 2),

  have hprod : ∀(a : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n),  a 0 * a 1 * a 2 = n,
  { intros a ha, rw mem_tuples_with_prod at ha,
    rw [←ha.2, prod3 a], },
  have ha_ne_zero :  ∀(a : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n) (i : fin 3), a i ≠ 0,
  { intros a ha i, rw mem_tuples_with_prod at ha,
    by_contra hai,
    rw finset.prod_eq_zero (mem_univ i) hai at ha,
    exact hn_ne_zero (eq_comm.mp ha.2),},

  have h_img : ∀ (a : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n), 
    f a ha ∈ filter (λ (p : ℕ × ℕ), n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors),
  { intros a ha,
    rw [mem_filter, finset.mem_product, mem_divisors, mem_divisors],
    split, split, split,
    calc a 0 * a 1 ∣ a 0 * a 1 * a 2 : by use a 2
               ... = n : hprod a ha, 
    exact hn_ne_zero, split,
    calc a 0 * a 2 ∣ a 0 * a 1 * a 2 : by {use a 1, ring}
               ... = n : hprod a ha,  
    exact hn_ne_zero,
    dsimp,
    rw [nat_lcm_mul_left, nat.coprime.lcm_eq_mul, ←hprod a ha],
    ring,
    apply coprime_of_mul_squarefree,
    apply squarefree.squarefree_of_dvd _ hn,
    calc a 1 * a 2 ∣ a 0 * a 1 * a 2 : by {use a 0, ring}
               ... = n : hprod a ha },

  have h_inj : ∀ (a b : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n) 
    (hb : b ∈ tuples_with_prod 3 n n), f a ha = f b hb → a = b,
  { intros a b ha hb hfab,
    dsimp only [f] at hfab,
    cases prod.mk.inj hfab with hfab1 hfab2,

    have hab2 : a 2 = b 2,
    { have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2,
      conv{to_rhs, rw hfab1}, 
      rw [hprod a ha, hprod b hb],
      rw [←mul_right_inj'],
      exact hprods, 
      apply mul_ne_zero (ha_ne_zero a ha 0) (ha_ne_zero a ha 1) },
    have hab0 : a 0 = b 0,
    { rw[←mul_left_inj'],
      rw hab2 at hfab2,
      exact hfab2, exact ha_ne_zero b hb 2, },
    have hab1 : a 1 = b 1,
    { rw[←mul_right_inj'],
      rw hab0 at hfab1,
      exact hfab1, exact ha_ne_zero b hb 0, },
    funext i,
    fin_cases i,
    all_goals { assumption } },

  have h_surj : ∀ (b : ℕ × ℕ), b ∈ filter (λ (p : ℕ × ℕ), 
    n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors) → 
    (∃ (a : fin 3 → ℕ) (ha : a ∈ tuples_with_prod 3 n n), f a ha = b),
  { intros b hb,
    let g := b.fst.gcd b.snd,
    let a := (λ i : fin 3, if i = 0 then g else if i = 1 then b.fst/g else b.snd/g),
    have ha : a ∈ tuples_with_prod 3 n n,
    { rw [mem_tuples_with_prod],
      rw [mem_filter, finset.mem_product] at hb,
      have hbfst_dvd : b.fst ∣ n := (mem_divisors.mp hb.1.1).1,
      have hbsnd_dvd : b.snd ∣ n := (mem_divisors.mp hb.1.2).1,
      split,
      intro i, rw mem_divisors, fin_cases i,
      split,
      calc b.fst.gcd b.snd ∣ b.fst : nat.gcd_dvd_left b.fst b.snd
                      ...  ∣ n : hbfst_dvd,
      exact hn_ne_zero,
      split,
      calc b.fst / g ∣ b.fst : div_dvd_of_dvd (nat.gcd_dvd_left b.fst b.snd)
              ...    ∣ n : hbfst_dvd,
      exact hn_ne_zero,
      split,
      calc b.snd / g ∣ b.snd : div_dvd_of_dvd (nat.gcd_dvd_right b.fst b.snd)
              ...    ∣ n : hbsnd_dvd,
      exact hn_ne_zero,
      rw prod3 a,
      dsimp only [a],
      have h10: (1:fin 3) ≠ 0,
      { rw fin.ne_iff_vne, norm_num, },
      have h20: (2:fin 3) ≠ 0,
      { rw fin.ne_iff_vne, norm_num, },
      have h21: (2:fin 3) ≠ 1,
      { rw fin.ne_iff_vne, norm_num, },
      rw [if_neg h10, if_pos rfl, if_pos rfl, if_neg h20, if_neg h21, hb.2],
      calc  g * (b.fst / g) * (b.snd / g) 
          = b.fst * (b.snd / g) : by rw nat.mul_div_cancel_left' (nat.gcd_dvd_left _ _)
      ... = b.fst * b.snd / g : _,
      rw nat.mul_div_assoc b.fst (nat.gcd_dvd_right b.fst b.snd) },
    use a, use ha,
    dsimp only [f, a],
    rw if_pos rfl,
    apply prod.ext,
    calc  g * (if 1 = 0 then g else if 1=1 then b.fst/g else (b.snd/g))
        = g * (b.fst/g) : by simp
    ... = b.fst : _,
    apply nat.mul_div_cancel' (nat.gcd_dvd_left b.fst b.snd),
    calc  g * (if 2=0 then g else if 2=1 then b.fst/g else b.snd/g)
        = g * (b.snd/g) : by simp
    ... = b.snd : _,
    apply nat.mul_div_cancel' (nat.gcd_dvd_right b.fst b.snd) },
  apply finset.card_congr f h_img h_inj h_surj,
  
end

lemma nat_sq_mono {a b : ℕ} (h : a ≤ b) : a^2 ≤ b^2 := pow_mono_right 2 h 

end aux