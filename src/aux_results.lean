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

example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
begin
  exact zero_lt_iff,
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

-- finset.prod_add   nat.sum_divisors_filter_squarefree 
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

end aux