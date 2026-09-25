/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.Abel


/-!
# Right division in a coefficient-left derivation Ore model

This file is the next structural layer after `ore_derivation.lean`.  It does
not identify a presented Weyl algebra with this model.  It builds the finite
normal-form algebra needed for that identification: the normal form of
`x^i * b`, the right product of a normal polynomial by a monomial `b*x^j`,
and the leading-term fact which drives right division by a monic polynomial.

The coefficient ring is allowed to be noncommutative.  No commutative
polynomial division theorem is used.
-/

@[expose] public section

namespace AlgebraicAnalysis

noncomputable section

/-- A derivation used to define a coefficient-left Ore normal form. -/
structure OreDivisionDerivation (B : Type*) [Ring B] where
  /-- The underlying additive derivation map. -/
  toFun : B → B
  /-- The derivation preserves zero. -/
  map_zero' : toFun 0 = 0
  /-- The derivation preserves addition. -/
  map_add' : ∀ a b, toFun (a + b) = toFun a + toFun b
  /-- The Leibniz rule. -/
  leibniz' : ∀ a b, toFun (a * b) = a * toFun b + toFun a * b

instance {B : Type*} [Ring B] : CoeFun (OreDivisionDerivation B) (fun _ => B → B) :=
  ⟨OreDivisionDerivation.toFun⟩

namespace OreDivisionDerivation

variable {B : Type*} [Ring B] (D : OreDivisionDerivation B)

@[simp]
theorem map_zero : D 0 = 0 := D.map_zero'

@[simp]
theorem map_add (a b : B) : D (a + b) = D a + D b := D.map_add' a b

@[simp]
theorem leibniz (a b : B) : D (a * b) = a * D b + D a * b := D.leibniz' a b

lemma map_nsmul (a : B) (n : ℕ) : D (n • a) = n • D a := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, map_add, ih]

end OreDivisionDerivation

namespace OreDivision

variable {B : Type*} [Ring B] (D : OreDivisionDerivation B)

/-- The coefficient-left normal form of `x^i*b` under `x*b=b*x+D(b)`. -/
def push (b : B) (i : ℕ) : Polynomial B :=
  ∑ k ∈ Finset.range (i + 1),
    Polynomial.monomial (i - k) (Nat.choose i k • (D^[k]) b)

lemma push_coeff (b : B) (i n : ℕ) :
    (OreDivision.push D b i).coeff n =
      ∑ k ∈ Finset.range (i + 1),
        if i - k = n then Nat.choose i k • (D^[k]) b else 0 := by
  simp [push,  Polynomial.coeff_monomial]

lemma push_degree_le (b : B) (i : ℕ) : (OreDivision.push D b i).degree ≤ (i : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [push_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : i - k = n
  · have hn' : i < n := by exact_mod_cast hn
    have hle : i - k ≤ i := Nat.sub_le _ _
    omega
  · simp [hki]

lemma push_coeff_top (b : B) (i : ℕ) : (OreDivision.push D b i).coeff i = b := by
  rw [push_coeff]
  rw [Finset.sum_eq_single 0 (by
    intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hk_lt : k < i + 1 := Finset.mem_range.mp hk
    have hk_le : k ≤ i := by omega
    have hi_pos : 0 < i := lt_of_lt_of_le hkpos hk_le
    have hki : i - k ≠ i := Nat.ne_of_lt (Nat.sub_lt hi_pos hkpos)
    simp [hki]) (by simp)]
  simp

lemma push_eq_zero_of (b : B) (i : ℕ) (h : b = 0) : OreDivision.push D b i = 0 := by
  subst b
  have hiter : ∀ n : ℕ, (D^[n]) 0 = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        simp [ih, OreDivisionDerivation.map_zero]
  simp [push, hiter]

/-- Right multiplication of a normal polynomial by the monomial `b*x^j`.

The definition is coefficientwise and finite.  It is deliberately not the
ordinary multiplication of `Polynomial B`: the inner `push` expansion is the
derivation correction for moving `b` through powers of `x`.
-/
def rightTerm (i : ℕ) (a b : B) (j : ℕ) : Polynomial B :=
  ∑ k ∈ Finset.range (i + 1),
    Polynomial.monomial (i - k + j)
      (a * (Nat.choose i k • (D^[k]) b))

/-- Right multiplication by one coefficient-monomial. -/
def rightMulMonomial (p : Polynomial B) (b : B) (j : ℕ) : Polynomial B :=
  p.sum (fun i a => rightTerm D i a b j)

lemma rightMulMonomial_coeff (p : Polynomial B) (b : B) (j n : ℕ) :
    (rightMulMonomial D p b j).coeff n =
      ∑ i ∈ p.support, ∑ k ∈ Finset.range (i + 1),
        if i - k + j = n then
          p.coeff i * (Nat.choose i k • (D^[k]) b) else 0 := by
  simp [rightMulMonomial, rightTerm,
    Polynomial.coeff_monomial, Polynomial.sum_def]

lemma rightTerm_zero (i : ℕ) (b : B) (j : ℕ) : rightTerm D i 0 b j = 0 := by
  simp [rightTerm]

lemma rightTerm_add_left (i : ℕ) (a₁ a₂ b : B) (j : ℕ) :
    rightTerm D i (a₁ + a₂) b j =
      rightTerm D i a₁ b j + rightTerm D i a₂ b j := by
  simp only [rightTerm, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_add]

lemma rightMulMonomial_add_left (p q : Polynomial B) (b : B) (j : ℕ) :
    rightMulMonomial D (p + q) b j =
      rightMulMonomial D p b j + rightMulMonomial D q b j := by
  apply Polynomial.sum_add_index
  · intro i
    exact rightTerm_zero D i b j
  · intro i a₁ a₂
    exact rightTerm_add_left D i a₁ a₂ b j

lemma iterate_add (n : ℕ) (b₁ b₂ : B) :
    (D^[n]) (b₁ + b₂) = (D^[n]) b₁ + (D^[n]) b₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (D^[n + 1]) (b₁ + b₂) = D ((D^[n]) (b₁ + b₂)) :=
          Function.iterate_succ_apply' D n (b₁ + b₂)
        _ = D ((D^[n]) b₁ + (D^[n]) b₂) := by rw [ih]
        _ = D ((D^[n]) b₁) + D ((D^[n]) b₂) := D.map_add _ _
        _ = (D^[n + 1]) b₁ + (D^[n + 1]) b₂ := by
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

lemma iterate_zero (n : ℕ) : (D^[n]) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (D^[n + 1]) 0 = D ((D^[n]) 0) := Function.iterate_succ_apply' D n 0
        _ = D 0 := by rw [ih]
        _ = 0 := D.map_zero

lemma rightMulMonomial_add_right (p : Polynomial B) (b₁ b₂ : B) (j : ℕ) :
    rightMulMonomial D p (b₁ + b₂) j =
      rightMulMonomial D p b₁ j + rightMulMonomial D p b₂ j := by
  apply Polynomial.ext
  intro n
  rw [rightMulMonomial_coeff, Polynomial.coeff_add,
    rightMulMonomial_coeff, rightMulMonomial_coeff]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hEq : i - k + j = n
  · simp only [ite_eq_left hEq, iterate_add, nsmul_add, mul_add]
  · simp [hEq]

lemma rightMulMonomial_zero_right (p : Polynomial B) (j : ℕ) :
    rightMulMonomial D p 0 j = 0 := by
  apply Polynomial.ext
  intro n
  rw [rightMulMonomial_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro k hk
  simp [iterate_zero]

/-- The product `d*q` of a normal polynomial by a normal right quotient. -/
def rightMul (d q : Polynomial B) : Polynomial B :=
  q.sum (fun j c => rightMulMonomial D d c j)

lemma rightMul_add (d q₁ q₂ : Polynomial B) :
    rightMul D d (q₁ + q₂) = rightMul D d q₁ + rightMul D d q₂ := by
  apply Polynomial.sum_add_index
  · intro j
    exact rightMulMonomial_zero_right D d j
  · intro j c₁ c₂
    exact rightMulMonomial_add_right D d c₁ c₂ j

lemma rightMul_zero (d : Polynomial B) : rightMul D d 0 = 0 := by
  simp [rightMul, Polynomial.sum_def]

/-- The additive map given by right multiplication by a fixed normal form. -/
def rightMulAddHom (d : Polynomial B) : Polynomial B →+ Polynomial B where
  toFun := rightMul D d
  map_zero' := rightMul_zero D d
  map_add' := rightMul_add D d

lemma rightMul_sub (d q₁ q₂ : Polynomial B) :
    rightMul D d (q₁ - q₂) = rightMul D d q₁ - rightMul D d q₂ := by
  exact map_sub (rightMulAddHom D d) q₁ q₂

lemma rightMul_monomial (d : Polynomial B) (c : B) (j : ℕ) :
    rightMul D d (Polynomial.monomial j c) =
      rightMulMonomial D d c j := by
  by_cases hc : c = 0
  · subst c
    simp [rightMul, Polynomial.sum_def, rightMulMonomial_zero_right]
  · unfold rightMul
    rw [Polynomial.sum_def, Polynomial.support_monomial j hc]
    simp [Polynomial.coeff_monomial]

lemma rightMulMonomial_degree_le (p : Polynomial B) (b : B) (j : ℕ) :
    (rightMulMonomial D p b j).degree ≤ (p.natDegree + j : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [rightMulMonomial_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hEq : i - k + j = n
  · have hn' : p.natDegree + j < n := by exact_mod_cast hn
    have hi_le : i ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
    have hle : i - k + j ≤ p.natDegree + j := by
      omega
    omega
  · simp [hEq]

lemma rightMulMonomial_coeff_top (p : Polynomial B) (hp : p ≠ 0)
    (b : B) (j : ℕ) :
    (rightMulMonomial D p b j).coeff (p.natDegree + j) =
      p.leadingCoeff * b := by
  rw [rightMulMonomial_coeff]
  have htop : p.natDegree ∈ p.support :=
    Polynomial.natDegree_mem_support_of_nonzero hp
  rw [Finset.sum_eq_single p.natDegree (by
    intro i hi hne
    apply Finset.sum_eq_zero
    intro k hk
    have hi_le : i ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
    have hi_lt : i < p.natDegree := lt_of_le_of_ne hi_le hne
    have hne_sub : i - k ≠ p.natDegree := by omega
    simp [hne_sub]) (by simp [htop])]
  rw [Finset.sum_eq_single 0 (by
    intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hk_lt : k < p.natDegree + 1 := Finset.mem_range.mp hk
    have hk_le : k ≤ p.natDegree := by omega
    have hNpos : 0 < p.natDegree := lt_of_lt_of_le hkpos hk_le
    have hne_sub : p.natDegree - k ≠ p.natDegree :=
      Nat.ne_of_lt (Nat.sub_lt hNpos hkpos)
    simp [hne_sub]) (by simp)]
  rw [Nat.sub_zero]
  simp only [ite_true, Nat.choose_zero_right, Function.iterate_zero_apply,
    one_nsmul,  Polynomial.leadingCoeff]

lemma rightMul_degree_le (d q : Polynomial B) :
    (rightMul D d q).degree ≤ (d.natDegree + q.natDegree : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [rightMul, Polynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Polynomial.coeff_eq_zero_of_degree_lt
  have hj_le : j ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hdeg : (rightMulMonomial D d (q.coeff j) j).degree ≤
      (d.natDegree + j : WithBot ℕ) :=
    rightMulMonomial_degree_le D d (q.coeff j) j
  have hbound : (d.natDegree + j : WithBot ℕ) ≤
      (d.natDegree + q.natDegree : WithBot ℕ) := by
    exact_mod_cast Nat.add_le_add_left hj_le d.natDegree
  exact lt_of_le_of_lt hdeg (lt_of_le_of_lt hbound hn)

lemma rightMul_coeff_top [Nontrivial B] (d q : Polynomial B)
    (hd : d.Monic) (hq : q ≠ 0) :
    (rightMul D d q).coeff (d.natDegree + q.natDegree) = q.leadingCoeff := by
  rw [rightMul, Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  have hqtop : q.natDegree ∈ q.support :=
    Polynomial.natDegree_mem_support_of_nonzero hq
  rw [Finset.sum_eq_single q.natDegree (by
    intro j hj hne
    have hj_le : j ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    have hj_lt : j < q.natDegree := lt_of_le_of_ne hj_le hne
    have hdeg : (rightMulMonomial D d (q.coeff j) j).degree ≤
        (d.natDegree + j : WithBot ℕ) :=
      rightMulMonomial_degree_le D d (q.coeff j) j
    have hlt : (d.natDegree + j : WithBot ℕ) <
        (d.natDegree + q.natDegree : WithBot ℕ) := by
      exact_mod_cast Nat.add_lt_add_left hj_lt d.natDegree
    have hzero : (rightMulMonomial D d (q.coeff j) j).coeff
        (d.natDegree + q.natDegree) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg hlt)
    exact hzero) (by simp [hqtop])]
  have hd0 : d ≠ 0 := hd.ne_zero
  rw [rightMulMonomial_coeff_top D d hd0 (q.coeff q.natDegree) q.natDegree,
    hd.leadingCoeff, one_mul]
  rfl

lemma rightMul_degree_eq [Nontrivial B] (d q : Polynomial B)
    (hd : d.Monic) (hq : q ≠ 0) :
    (rightMul D d q).degree = (d.natDegree + q.natDegree : WithBot ℕ) := by
  have hle := rightMul_degree_le D d q
  have htop : (rightMul D d q).coeff (d.natDegree + q.natDegree) =
      q.leadingCoeff := rightMul_coeff_top D d q hd hq
  have hq0 : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hge : (d.natDegree + q.natDegree : WithBot ℕ) ≤
      (rightMul D d q).degree := by
    by_contra hnot
    have hlt0 : (rightMul D d q).degree <
        (d.natDegree + q.natDegree : WithBot ℕ) := lt_of_not_ge hnot
    have hlt : (rightMul D d q).degree <
        ((d.natDegree + q.natDegree : ℕ) : WithBot ℕ) := by
      have heq : (d.natDegree + q.natDegree : WithBot ℕ) =
          ((d.natDegree + q.natDegree : ℕ) : WithBot ℕ) :=
        (WithBot.coe_add d.natDegree q.natDegree).symm
      rwa [heq] at hlt0
    have hz := Polynomial.coeff_eq_zero_of_degree_lt hlt
    exact hq0 (by rw [← htop, hz])
  exact le_antisymm hle hge

theorem rightMul_injective [Nontrivial B] (d : Polynomial B) (hd : d.Monic) :
    Function.Injective (rightMul D d) := by
  intro q₁ q₂ hq
  by_contra hne
  have hdiff : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hne
  have hz : rightMul D d (q₁ - q₂) = 0 := by
    rw [rightMul_sub, hq, sub_self]
  have hdeg := rightMul_degree_eq D d (q₁ - q₂) hd hdiff
  rw [hz] at hdeg
  have hne : (⊥ : WithBot ℕ) ≠
      (d.natDegree + (q₁ - q₂).natDegree : WithBot ℕ) := by
    have heq : (d.natDegree + (q₁ - q₂).natDegree : WithBot ℕ) =
        ((d.natDegree + (q₁ - q₂).natDegree : ℕ) : WithBot ℕ) :=
      (WithBot.coe_add d.natDegree (q₁ - q₂).natDegree).symm
    rw [heq]
    exact WithBot.bot_ne_coe
  exact hne hdeg

/-! The leading-degree theorem packages the strict filtered-intersection
property needed by the relative principal-source construction.  This is an
Ore-polynomial filtration statement; it is deliberately not identified here
with the Bernstein filtration on the Weyl algebra. -/

theorem rightMul_degree_le_iff [Nontrivial B] (d q : Polynomial B)
    (hd : d.Monic) (n : ℕ) :
    (rightMul D d q).degree ≤ (n : WithBot ℕ) ↔
      q = 0 ∨ d.natDegree + q.natDegree ≤ n := by
  constructor
  · intro h
    by_cases hq : q = 0
    · exact Or.inl hq
    · right
      have hdeg := rightMul_degree_eq D d q hd hq
      rw [hdeg] at h
      exact_mod_cast h
  · intro h
    rcases h with hzero | hq
    · subst q
      simp [rightMul_zero]
    · by_cases hq0 : q = 0
      · subst q
        simp [rightMul_zero]
      · have hdeg := rightMul_degree_eq D d q hd hq0
        rw [hdeg]
        exact_mod_cast hq

lemma remainder_degree_lt (d r : Polynomial B)
    (hr : r = 0 ∨ r.natDegree < d.natDegree) :
    r.degree < (d.natDegree : WithBot ℕ) := by
  rcases hr with rfl | hr
  · exact WithBot.bot_lt_coe _
  · by_cases hr0 : r = 0
    · subst r
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree hr0]
      exact_mod_cast hr

theorem right_division_unique [Nontrivial B] (d p q₁ q₂ r₁ r₂ : Polynomial B)
    (hd : d.Monic)
    (h₁ : p = rightMul D d q₁ + r₁)
    (h₂ : p = rightMul D d q₂ + r₂)
    (hr₁ : r₁ = 0 ∨ r₁.natDegree < d.natDegree)
    (hr₂ : r₂ = 0 ∨ r₂.natDegree < d.natDegree) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have heq : rightMul D d q₁ + r₁ = rightMul D d q₂ + r₂ :=
    h₁.symm.trans h₂
  have hrel : rightMul D d (q₁ - q₂) = r₂ - r₁ := by
    rw [rightMul_sub]
    apply (sub_eq_iff_eq_add).2
    calc
      rightMul D d q₁ =
          (rightMul D d q₂ + r₂) - r₁ :=
        (eq_sub_iff_add_eq).2 heq
      _ = (r₂ - r₁) + rightMul D d q₂ := by abel
  have hrdiff : (r₂ - r₁).degree < (d.natDegree : WithBot ℕ) := by
    have h₁deg := remainder_degree_lt d r₁ hr₁
    have h₂deg := remainder_degree_lt d r₂ hr₂
    exact lt_of_le_of_lt (Polynomial.degree_sub_le r₂ r₁) (max_lt h₂deg h₁deg)
  have hqeq : q₁ = q₂ := by
    by_contra hne
    have hdiff : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hne
    have hleft := rightMul_degree_eq D d (q₁ - q₂) hd hdiff
    have hleft_ge : (d.natDegree : WithBot ℕ) ≤
        (rightMul D d (q₁ - q₂)).degree := by
      rw [hleft]
      apply le_add_of_nonneg_right
      exact_mod_cast (Nat.zero_le (q₁ - q₂).natDegree)
    have hright_ge : (d.natDegree : WithBot ℕ) ≤ (r₂ - r₁).degree := by
      rw [← hrel]
      exact hleft_ge
    exact (not_le_of_gt hrdiff) hright_ge
  have hrEq : r₁ = r₂ := by
    apply add_left_cancel (b := r₁) (a := rightMul D d q₂)
    simpa [hqeq] using heq
  exact ⟨hqeq, hrEq⟩

lemma cancel_degree_lt [Nontrivial B] (d p : Polynomial B) (hd : d.Monic)
    (hp : p ≠ 0) (hdeg : d.natDegree ≤ p.natDegree) :
    (p - rightMulMonomial D d p.leadingCoeff
      (p.natDegree - d.natDegree)).degree < p.degree := by
  let c : B := p.leadingCoeff
  let j : ℕ := p.natDegree - d.natDegree
  let q : Polynomial B := rightMulMonomial D d c j
  have hd0 : d ≠ 0 := hd.ne_zero
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hsum : d.natDegree + j = p.natDegree := by
    dsimp [j]
    exact Nat.add_sub_of_le hdeg
  have hq_le : q.degree ≤ (p.natDegree : WithBot ℕ) := by
    dsimp [q, c, j]
    have h := rightMulMonomial_degree_le D d p.leadingCoeff
      (p.natDegree - d.natDegree)
    have hcast : (d.natDegree : WithBot ℕ) +
        (p.natDegree - d.natDegree : WithBot ℕ) =
        (p.natDegree : WithBot ℕ) := by
      exact_mod_cast (Nat.add_sub_of_le hdeg)
    rw [hcast] at h
    exact h
  have hq_top : q.coeff p.natDegree = c := by
    dsimp [q]
    rw [← hsum,
      rightMulMonomial_coeff_top D d hd0 c j, hd.leadingCoeff, one_mul]
  have hq0 : q ≠ 0 := by
    intro hqzero
    have hz := congrArg (fun z : Polynomial B => z.coeff p.natDegree) hqzero
    change q.coeff p.natDegree = 0 at hz
    rw [hq_top] at hz
    exact hc0 hz
  have hq_ge : (p.natDegree : WithBot ℕ) ≤ q.degree := by
    by_contra hnot
    have hlt : q.degree < (p.natDegree : WithBot ℕ) := lt_of_not_ge hnot
    have hz : q.coeff p.natDegree = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt hlt
    exact hc0 (by rw [← hq_top, hz])
  have hq_degree : q.degree = (p.natDegree : WithBot ℕ) :=
    le_antisymm hq_le hq_ge
  have hp_degree : p.degree = (p.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hp
  have hleading : p.leadingCoeff = q.leadingCoeff := by
    change p.coeff p.natDegree = q.coeff q.natDegree
    have hq_nat : q.natDegree = p.natDegree := by
      have hq_degree_nat : (q.natDegree : WithBot ℕ) =
          (p.natDegree : WithBot ℕ) := by
        rw [← Polynomial.degree_eq_natDegree hq0]
        exact hq_degree
      exact_mod_cast hq_degree_nat
    rw [hq_nat, hq_top]
    rfl
  exact Polynomial.degree_sub_lt_left (hp_degree.trans hq_degree.symm) hp hleading

theorem right_division_exists [Nontrivial B] (d p : Polynomial B) (hd : d.Monic) :
    ∃ q r : Polynomial B,
      p = rightMul D d q + r ∧ (r = 0 ∨ r.natDegree < d.natDegree) := by
  let P : ℕ → Prop := fun n =>
    ∀ p : Polynomial B, p.natDegree = n →
      ∃ q r : Polynomial B,
        p = rightMul D d q + r ∧ (r = 0 ∨ r.natDegree < d.natDegree)
  have hall : P p.natDegree := by
    refine Nat.strong_induction_on p.natDegree ?_
    intro n ih
    dsimp [P]
    intro p hpN
    by_cases hp0 : p = 0
    · subst p
      exact ⟨0, 0, by simp [rightMul], Or.inl rfl⟩
    by_cases hsmall : p.natDegree < d.natDegree
    · exact ⟨0, p, by simp [rightMul], Or.inr hsmall⟩
    · have hlarge : d.natDegree ≤ p.natDegree := Nat.le_of_not_gt hsmall
      let c : B := p.leadingCoeff
      let j : ℕ := p.natDegree - d.natDegree
      let rm : Polynomial B := rightMulMonomial D d c j
      have hcancel : (p - rm).degree < p.degree := by
        dsimp [rm, c, j]
        exact cancel_degree_lt D d p hd hp0 hlarge
      by_cases hrem0 : p - rm = 0
      · refine ⟨Polynomial.monomial j c, 0, ?_, Or.inl rfl⟩
        rw [rightMul_monomial]
        dsimp [rm] at hrem0 ⊢
        simpa [add_zero] using (sub_eq_zero.mp hrem0)
      · have hremN : (p - rm).natDegree < p.natDegree :=
          Polynomial.natDegree_lt_natDegree hrem0 hcancel
        have hremN' : (p - rm).natDegree < n := by
          rw [← hpN]
          exact hremN
        obtain ⟨q, r, hqr, hrr⟩ :=
          ih (p - rm).natDegree hremN' (p - rm) rfl
        refine ⟨Polynomial.monomial j c + q, r, ?_, hrr⟩
        calc
          p = rm + (p - rm) := by abel
          _ = rm + (rightMul D d q + r) := by rw [hqr]
          _ = rightMul D d (Polynomial.monomial j c + q) + r := by
            rw [rightMul_add, rightMul_monomial]
            dsimp [rm]
            abel
  dsimp [P] at hall
  exact hall p rfl

/-- An ambient ring in which the Ore relation is represented. -/
structure OreAmbient (B A : Type*) [Ring B] [Ring A]
    (D : OreDivisionDerivation B) where
  /-- The coefficient-ring embedding. -/
  embed : B →+* A
  /-- The element representing the Ore variable. -/
  x : A
  /-- The defining relation in the ambient ring. -/
  relation : ∀ b, x * embed b = embed b * x + embed (D b)

namespace OreAmbient

variable {B A : Type*} [Ring B] [Ring A]
  (D : OreDivisionDerivation B) (O : OreAmbient B A D)

/-- The inner derivation `a ↦ p*a-a*p`, used to formalize the iterated
commutator expansion of a power of `p`. -/
def commutatorDerivation (p : A) : OreDivisionDerivation A where
  toFun a := p * a - a * p
  map_zero' := by simp
  map_add' a b := by noncomm_ring
  leibniz' a b := by noncomm_ring

/-- The ambient Ore presentation for an inner derivation. -/
def commutatorAmbient (p : A) :
    OreAmbient A A (commutatorDerivation p) where
  embed := RingHom.id A
  x := p
  relation := by
    intro a
    change p * a = a * p + (p * a - a * p)
    noncomm_ring

/-- A term in the iterated commutator expansion. -/
def term (b : B) (i j : ℕ) : A :=
  O.embed ((D^[i]) b) * O.x ^ j

lemma push_term (b : B) (i j : ℕ) :
    O.x * term D O b i j = term D O b i (j + 1) + term D O b (i + 1) j := by
  dsimp [term]
  calc
    O.x * (O.embed ((D^[i]) b) * O.x ^ j) =
        (O.x * O.embed ((D^[i]) b)) * O.x ^ j := by rw [mul_assoc]
    _ = (O.embed ((D^[i]) b) * O.x +
          O.embed (D ((D^[i]) b))) * O.x ^ j := by rw [O.relation]
    _ = O.embed ((D^[i]) b) * O.x ^ (j + 1) +
          O.embed ((D^[i + 1]) b) * O.x ^ j := by
      rw [add_mul, mul_assoc, ← pow_succ', Function.iterate_succ_apply']

lemma mul_nsmul_left (a u : A) (n : ℕ) :
    a * (n • u) = n • (a * u) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, mul_add, ih]

lemma nsmul_mul_right (a u : A) (n : ℕ) :
    (n • a) * u = n • (a * u) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, add_mul, ih]

/-- The normal-order expansion of `x^n * embed b`. -/
def expansion (b : B) (n : ℕ) : A :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    n.choose ij.1 • term D O b ij.1 ij.2

theorem pow_mul (b : B) (n : ℕ) :
    O.x ^ n * O.embed b = expansion D O b n := by
  induction n with
  | zero =>
      simp [expansion, term]
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, expansion, Finset.mul_sum]
      simp_rw [mul_nsmul_left O.x, O.push_term, smul_add]
      rw [Finset.sum_add_distrib, expansion]
      rw [Finset.sum_antidiagonal_choose_succ_nsmul]
      have hsecond :
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            n.choose ij.1 • term D O b (ij.1 + 1) ij.2) =
            ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
              n.choose ij.2 • term D O b (ij.1 + 1) ij.2 := by
        apply Finset.sum_congr rfl
        intro ij hij
        have hsum : ij.1 + ij.2 = n :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have hi : ij.1 ≤ n := by omega
        rw [← Nat.choose_symm hi]
        rw [show n - ij.1 = ij.2 by omega]
      rw [hsecond]

/-- A single coefficient moved through a power of the Ore variable. -/
def reverseTerm (b : B) (i j : ℕ) : A :=
  O.x ^ j * O.embed ((D^[i]) b)

/-- A signed term for the reverse normal-order expansion. -/
def reverseSignedTerm (b : B) (i j : ℕ) : A :=
  (-1 : A) ^ i * reverseTerm D O b i j

/-- The reverse normal-order expansion of `x^n * embed b`. -/
def reverseExpansion (b : B) (n : ℕ) : A :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    n.choose ij.1 • reverseSignedTerm D O b ij.1 ij.2

lemma reverseTerm_mul (b : B) (i j : ℕ) :
    reverseTerm D O b i j * O.x =
      reverseTerm D O b i (j + 1) - reverseTerm D O b (i + 1) j := by
  dsimp [reverseTerm]
  have hmove : O.embed ((D^[i]) b) * O.x =
      O.x * O.embed ((D^[i]) b) - O.embed (D ((D^[i]) b)) := by
    rw [O.relation]
    noncomm_ring
  rw [show O.x ^ j * O.embed ((D^[i]) b) * O.x =
      O.x ^ j * (O.embed ((D^[i]) b) * O.x) by rw [mul_assoc], hmove,
    mul_sub, pow_succ']
  rw [← mul_assoc, ← pow_succ, pow_succ']
  rw [← Function.iterate_succ_apply' D i b,
    ← Function.iterate_succ_apply D i b]

lemma reverseSignedTerm_mul (b : B) (i j : ℕ) :
    reverseSignedTerm D O b i j * O.x =
      reverseSignedTerm D O b i (j + 1) +
        reverseSignedTerm D O b (i + 1) j := by
  dsimp [reverseSignedTerm]
  rw [mul_assoc, reverseTerm_mul, mul_sub, pow_succ']
  noncomm_ring

theorem reverse_mul (b : B) (n : ℕ) :
    O.embed b * O.x ^ n = reverseExpansion D O b n := by
  induction n with
  | zero =>
      simp [reverseExpansion, reverseSignedTerm, reverseTerm]
  | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, reverseExpansion, Finset.sum_mul]
      simp_rw [nsmul_mul_right, reverseSignedTerm_mul]
      simp_rw [nsmul_add]
      unfold reverseExpansion
      have hsecond :
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            n.choose ij.1 • reverseSignedTerm D O b (ij.1 + 1) ij.2) =
            ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
              n.choose ij.2 • reverseSignedTerm D O b (ij.1 + 1) ij.2 := by
        apply Finset.sum_congr rfl
        intro ij hij
        have hsum : ij.1 + ij.2 = n :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have hi : ij.1 ≤ n := by omega
        rw [← Nat.choose_symm hi]
        rw [show n - ij.1 = ij.2 by omega]
      rw [Finset.sum_add_distrib, hsecond]
      exact (Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => reverseSignedTerm D O b i j) n).symm

theorem commutator_pow_mul (p a : A) (m : ℕ) :
    p ^ m * a =
      OreAmbient.expansion (commutatorDerivation p) (commutatorAmbient p) a m := by
  exact OreAmbient.pow_mul (commutatorDerivation p) (commutatorAmbient p) a m

theorem commutator_pow_mul_explicit (p a : A) (m : ℕ) :
    p ^ m * a =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
        m.choose ij.1 • (((commutatorDerivation p)^[ij.1]) a * p ^ ij.2) := by
  simpa [OreAmbient.expansion, term, commutatorAmbient] using
    (commutator_pow_mul (A := A) p a m)

theorem commutator_pow_succ (p x : A)
    (hpx : p * x - x * p = 1) (r : ℕ) :
    p * x ^ (r + 1) - x ^ (r + 1) * p = (r + 1) • x ^ r := by
  induction r with
  | zero => simpa using hpx
  | succ r ih =>
      calc
        p * x ^ (r + 1 + 1) - x ^ (r + 1 + 1) * p =
            (p * x ^ (r + 1) - x ^ (r + 1) * p) * x +
              x ^ (r + 1) * (p * x - x * p) := by
                noncomm_ring
        _ = ((r + 1) • x ^ r) * x + x ^ (r + 1) * 1 := by rw [ih, hpx]
        _ = (r + 2) • x ^ (r + 1) := by
              rw [mul_one, nsmul_mul_right, pow_succ']
              have hpow : x ^ r * x = x * x ^ r := by
                rw [← pow_succ, pow_succ']
              rw [hpow]
              simp only [succ_nsmul]

theorem commutator_iterate_pow_of_le (p x : A)
    (hpx : p * x - x * p = 1) (j n : ℕ) (hjn : j ≤ n) :
    (((commutatorDerivation p)^[j]) (x ^ n)) =
      n.descFactorial j • x ^ (n - j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      have hjn' : j ≤ n := by omega
      rw [Function.iterate_succ_apply', ih n hjn']
      have hpow : x ^ (n - j) = x ^ ((n - j - 1) + 1) := by
        congr 1
        omega
      have hcomm :
          (commutatorDerivation p) (x ^ (n - j)) =
            (n - j) • x ^ (n - j - 1) := by
        change p * x ^ (n - j) - x ^ (n - j) * p = _
        rw [hpow]
        have hsub : n - j - 1 + 1 = n - j := by omega
        simpa only [hsub] using commutator_pow_succ p x hpx (n - j - 1)
      rw [OreDivisionDerivation.map_nsmul, hcomm, smul_smul,
        Nat.descFactorial_succ]
      rw [show n - (j + 1) = n - j - 1 by omega, Nat.mul_comm]

theorem commutator_iterate_pow_of_lt (p x : A)
    (hpx : p * x - x * p = 1) (j n : ℕ) (hnj : n < j) :
    (((commutatorDerivation p)^[j]) (x ^ n)) = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hj : n < j
      · rw [Function.iterate_succ_apply', ih hj]
        simp [commutatorDerivation]
      · have hjeq : j = n := by omega
        rw [Function.iterate_succ_apply', hjeq,
          commutator_iterate_pow_of_le p x hpx n n le_rfl]
        simp? [commutatorDerivation]
        rw [Nat.cast_comm]
        simp

theorem commutator_iterate_pow (p x : A)
    (hpx : p * x - x * p = 1) (j n : ℕ) :
    (((commutatorDerivation p)^[j]) (x ^ n)) =
      if j ≤ n then n.descFactorial j • x ^ (n - j) else 0 := by
  by_cases hjn : j ≤ n
  · simp [hjn, commutator_iterate_pow_of_le p x hpx j n hjn]
  · have hnj : n < j := Nat.lt_of_not_ge hjn
    simp [hjn, commutator_iterate_pow_of_lt p x hpx j n hnj]

theorem commutator_pow_mul_pow (p x : A)
    (hpx : p * x - x * p = 1) (k r : ℕ) :
    p ^ k * x ^ r =
      ∑ i ∈ Finset.range (k + 1),
        if i ≤ r then
          (k.choose i * r.descFactorial i) •
            (x ^ (r - i) * p ^ (k - i))
        else 0 := by
  rw [commutator_pow_mul_explicit]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => k.choose i •
      (((commutatorDerivation p)^[i]) (x ^ r) * p ^ j)) k]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hir : i ≤ r
  · rw [commutator_iterate_pow p x hpx i r]
    simp only [ite_eq_left hir]
    rw [show k - i = (k - i) by rfl]
    simp [
       mul_assoc]
  · rw [commutator_iterate_pow p x hpx i r]
    simp [hir]

/-! ### p-free monic corner

The quotient by the image of right multiplication by `p` keeps only the
p-free term of the normal-ordering expansion.  The following theorem isolates
the monic contribution; lower coefficient terms are handled by the separate
Newton arithmetic lemmas in `a2_newton_bound.lean`.
-/

/-- The linear map given by right multiplication by `p`. -/
def pRightMulLinear {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (p : A) : A →ₗ[k] A where
  toFun z := z * p
  map_add' x y := by
    change (x + y) * p = x * p + y * p
    rw [add_mul]
  map_smul' c x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [mul_assoc]

/-- The range of right multiplication by `p`. -/
def pRightMulRange {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (p : A) : Submodule k A :=
  LinearMap.range (pRightMulLinear p)

lemma pRightMulRange_mem_of_mul_p {k A : Type*} [Field k] [Ring A]
    [Algebra k A] (p z : A) : z * p ∈ pRightMulRange (k := k) p := by
  exact ⟨z, rfl⟩

theorem pfree_power_of_le {k A : Type*} [Field k] [Ring A]
    [Algebra k A] (p x : A) (hpx : p * x - x * p = 1)
    (u n : ℕ) (hun : u ≤ n) :
    Submodule.mkQ (pRightMulRange (k := k) p) (p ^ u * x ^ n) =
      (n.descFactorial u : k) •
        Submodule.mkQ (pRightMulRange (k := k) p) (x ^ (n - u)) := by
  rw [commutator_pow_mul_pow p x hpx u n]
  rw [map_sum]
  rw [Finset.sum_eq_single u]
  · simp only [hun, ↓reduceIte, Nat.choose_self,  one_mul,
       nsmul_eq_mul,  Nat.sub_self, pow_zero, mul_one]
    change Submodule.Quotient.mk
        (↑(n.descFactorial u) * x ^ (n - u)) =
      (n.descFactorial u : k) • Submodule.Quotient.mk (x ^ (n - u))
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    simp [Algebra.smul_def]
  · intro i hi hik
    simp only [Finset.mem_range] at hi
    have hlt : i < u := by omega
    have hpow : p ^ (u - i) = p ^ (u - i - 1) * p := by
      calc
        p ^ (u - i) = p ^ ((u - i - 1) + 1) := by congr 1; omega
        _ = p ^ (u - i - 1) * p := by rw [pow_succ]
    have hmem : x ^ (n - i) * p ^ (u - i) ∈
        pRightMulRange (k := k) p := by
      rw [hpow]
      simpa [mul_assoc] using
        (pRightMulRange_mem_of_mul_p (k := k) p
          (x ^ (n - i) * p ^ (u - i - 1)))
    have hzero : Submodule.mkQ (pRightMulRange (k := k) p)
        (x ^ (n - i) * p ^ (u - i)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (pRightMulRange (k := k) p)).2 hmem
    simp only [ite_eq_left (by omega : i ≤ n), map_nsmul, hzero, smul_zero]
  · simp

theorem pfree_monic_corner {k A : Type*} [Field k] [Ring A]
    [Algebra k A] (p x : A) (hpx : p * x - x * p = 1)
    (m r : ℕ) :
    Submodule.mkQ (pRightMulRange (k := k) p) (p ^ m * x ^ (m + r)) =
      (Nat.choose m m * (m + r).descFactorial m : k) •
        Submodule.mkQ (pRightMulRange (k := k) p) (x ^ r) := by
  rw [commutator_pow_mul_pow p x hpx m (m + r)]
  rw [map_sum]
  rw [Finset.sum_eq_single m]
  · simp only [Nat.choose_self, Nat.le_add_right, ↓reduceIte, Nat.sub_self,
      Nat.cast_one, one_mul,  nsmul_eq_mul]
    simp only [Submodule.mkQ_apply, pow_zero, Nat.add_sub_cancel_left, mul_one]
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    simp [Algebra.smul_def]
  · intro i hi him
    simp only [Finset.mem_range] at hi
    have hpos : 0 < m - i := by omega
    have hpow : p ^ (m - i) = p ^ (m - i - 1) * p := by
      calc
        p ^ (m - i) = p ^ ((m - i - 1) + 1) := by congr 1; omega
        _ = p ^ (m - i - 1) * p := by rw [pow_succ]
    have hmem : x ^ (m + r - i) * p ^ (m - i) ∈
        pRightMulRange (k := k) p := by
      rw [hpow]
      simpa [mul_assoc] using
        (pRightMulRange_mem_of_mul_p (k := k) p
          (x ^ (m + r - i) * p ^ (m - i - 1)))
    have hzero : Submodule.mkQ (pRightMulRange (k := k) p)
        (x ^ (m + r - i) * p ^ (m - i)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (pRightMulRange (k := k) p)).2 hmem
    simp only [ite_eq_left (by omega : i ≤ m + r), map_nsmul, hzero, smul_zero]
  · simp

lemma commutatorDerivation_mul_left (p b y : A)
    (hpb : p * b = b * p) :
    commutatorDerivation p (b * y) = b * commutatorDerivation p y := by
  change p * (b * y) - (b * y) * p = b * (p * y - y * p)
  rw [show p * (b * y) - (b * y) * p = (p * b) * y - b * (y * p) by
    noncomm_ring, hpb]
  noncomm_ring

theorem commutator_iterate_mul_left (p b y : A)
    (hpb : p * b = b * p) (j : ℕ) :
    ((commutatorDerivation p)^[j]) (b * y) =
      b * ((commutatorDerivation p)^[j]) y := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih,
        commutatorDerivation_mul_left p b _ hpb]
      congr 1
      rw [Function.iterate_succ_apply']

theorem commutator_iterate_add (p : A) (j : ℕ) (a b : A) :
    ((commutatorDerivation p)^[j]) (a + b) =
      ((commutatorDerivation p)^[j]) a +
        ((commutatorDerivation p)^[j]) b := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        ((commutatorDerivation p)^[j + 1]) (a + b) =
            (commutatorDerivation p)
              (((commutatorDerivation p)^[j]) (a + b)) := by
                rw [Function.iterate_succ_apply']
        _ = (commutatorDerivation p)
              (((commutatorDerivation p)^[j]) a +
                ((commutatorDerivation p)^[j]) b) := by rw [ih]
        _ = (commutatorDerivation p) (((commutatorDerivation p)^[j]) a) +
              (commutatorDerivation p) (((commutatorDerivation p)^[j]) b) := by
                change p * (((commutatorDerivation p)^[j]) a +
                    ((commutatorDerivation p)^[j]) b) -
                  ((((commutatorDerivation p)^[j]) a +
                    ((commutatorDerivation p)^[j]) b) * p) = _
                change p * (((commutatorDerivation p)^[j]) a +
                    ((commutatorDerivation p)^[j]) b) -
                  ((((commutatorDerivation p)^[j]) a +
                    ((commutatorDerivation p)^[j]) b) * p) =
                  (p * ((commutatorDerivation p)^[j]) a -
                    ((commutatorDerivation p)^[j]) a * p) +
                  (p * ((commutatorDerivation p)^[j]) b -
                    ((commutatorDerivation p)^[j]) b * p)
                noncomm_ring
        _ = ((commutatorDerivation p)^[j + 1]) a +
              ((commutatorDerivation p)^[j + 1]) b := by
                rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem commutator_iterate_sum (p : A) (j : ℕ)
    (s : Finset ℕ) (f : ℕ → A) :
    ((commutatorDerivation p)^[j]) (∑ i ∈ s, f i) =
      ∑ i ∈ s, ((commutatorDerivation p)^[j]) (f i) := by
  induction s using Finset.induction_on with
  | empty =>
      have hz : ∀ n : ℕ, ((commutatorDerivation p)^[n]) 0 = 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Function.iterate_succ_apply']
            change p * (((commutatorDerivation p)^[n]) 0) -
              (((commutatorDerivation p)^[n]) 0) * p = 0
            rw [ih]
            simp
      rw [Finset.sum_empty, Finset.sum_empty]
      exact hz j
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, commutator_iterate_add, ih,
        Finset.sum_insert ha]

theorem commutator_iterate_eval_monomial_of_le
    (p b : B) (n j : ℕ) (hpb : ∀ c : B,
      O.embed p * O.embed c = O.embed c * O.embed p)
    (hDp : D p = -1) (hjn : j ≤ n) :
    (((commutatorDerivation (O.embed p))^[j])
        (O.embed b * O.x ^ n)) =
      O.embed b * (n.descFactorial j • O.x ^ (n - j)) := by
  have hpx : O.embed p * O.x - O.x * O.embed p = 1 := by
    rw [O.relation p, hDp]
    simp
  calc
    ((commutatorDerivation (O.embed p))^[j])
        (O.embed b * O.x ^ n) =
        O.embed b *
          ((commutatorDerivation (O.embed p))^[j]) (O.x ^ n) := by
            exact commutator_iterate_mul_left (O.embed p) (O.embed b)
              (O.x ^ n) (hpb b) j
    _ = O.embed b * (n.descFactorial j • O.x ^ (n - j)) := by
          rw [commutator_iterate_pow_of_le (O.embed p) O.x hpx j n hjn]

theorem commutator_iterate_eval_monomial
    (p b : B) (n j : ℕ) (hpb : ∀ c : B,
      O.embed p * O.embed c = O.embed c * O.embed p)
    (hDp : D p = -1) :
    (((commutatorDerivation (O.embed p))^[j])
        (O.embed b * O.x ^ n)) =
      if j ≤ n then
        O.embed b * (n.descFactorial j • O.x ^ (n - j))
      else 0 := by
  have hpx : O.embed p * O.x - O.x * O.embed p = 1 := by
    rw [O.relation p, hDp]
    simp
  rw [commutator_iterate_mul_left (O.embed p) (O.embed b)
    (O.x ^ n) (hpb b) j]
  rw [commutator_iterate_pow (O.embed p) O.x hpx j n]
  by_cases hjn : j ≤ n <;> simp [hjn]

/-- Evaluation of a normal polynomial in an ambient Ore ring. -/
def eval (p : Polynomial B) : A :=
  p.sum (fun i b => O.embed b * O.x ^ i)

theorem commutator_iterate_eval (p : A) (q : Polynomial B) (j : ℕ) :
    ((commutatorDerivation p)^[j]) (eval D O q) =
      ∑ i ∈ q.support,
        ((commutatorDerivation p)^[j])
          (O.embed (q.coeff i) * O.x ^ i) := by
  unfold eval
  rw [Polynomial.sum_def]
  exact commutator_iterate_sum p j q.support
    (fun i => O.embed (q.coeff i) * O.x ^ i)

lemma eval_zero : eval D O 0 = 0 := by
  simp [eval, Polynomial.sum_def]

lemma eval_add (p q : Polynomial B) :
    eval D O (p + q) = eval D O p + eval D O q := by
  unfold eval
  apply Polynomial.sum_add_index
  · intro i
    simp
  · intro i a b
    rw [map_add, add_mul]

/-- The additive evaluation homomorphism. -/
def evalAddHom : Polynomial B →+ A where
  toFun := eval D O
  map_zero' := eval_zero D O
  map_add' := eval_add D O

lemma eval_monomial (b : B) (j : ℕ) :
    eval D O (Polynomial.monomial j b) = O.embed b * O.x ^ j := by
  by_cases hb : b = 0
  · subst b
    simp [eval, Polynomial.sum_def]
  · unfold eval
    rw [Polynomial.sum_def, Polynomial.support_monomial j hb]
    simp [Polynomial.coeff_monomial]

/-- The coefficient-left normal form of an iterated commutator. -/
def commutatorNormal (q : Polynomial B) (j : ℕ) : Polynomial B :=
  ∑ i ∈ q.support,
    if j ≤ i then
      Polynomial.monomial (i - j) (i.descFactorial j • q.coeff i)
    else 0

lemma commutatorNormal_degree_le (q : Polynomial B) (j : ℕ) :
    (commutatorNormal q j).degree ≤ (q.natDegree - j : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  have hn' : q.natDegree - j < n := by exact_mod_cast hn
  unfold commutatorNormal
  change (Polynomial.lcoeff B n)
      (∑ i ∈ q.support,
        if j ≤ i then
          Polynomial.monomial (i - j) (i.descFactorial j • q.coeff i)
        else 0) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi_le : i ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
  by_cases hji : j ≤ i
  · simp only [ite_eq_left hji]
    change (Polynomial.monomial (i - j)
      (i.descFactorial j • q.coeff i)).coeff n = 0
    rw [Polynomial.coeff_monomial]
    simp [show i - j ≠ n by omega]
  · simp [hji]

lemma commutatorNormal_coeff_top [Nontrivial B] (q : Polynomial B) (j : ℕ)
    (hq : q.Monic) (hjn : j ≤ q.natDegree) :
    (commutatorNormal q j).coeff (q.natDegree - j) =
      q.natDegree.descFactorial j • (1 : B) := by
  unfold commutatorNormal
  change (Polynomial.lcoeff B (q.natDegree - j))
      (∑ i ∈ q.support,
        if j ≤ i then
          Polynomial.monomial (i - j) (i.descFactorial j • q.coeff i)
        else 0) = _
  rw [map_sum]
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [Finset.sum_eq_single q.natDegree (by
    intro i hi hne
    have hi_le : i ≤ q.natDegree :=
      Polynomial.le_natDegree_of_mem_supp i hi
    have hi_lt : i < q.natDegree := lt_of_le_of_ne hi_le hne
    by_cases hji : j ≤ i
    · have hneq : i - j ≠ q.natDegree - j := by omega
      simp [hji, hneq, Polynomial.coeff_monomial]
    · simp [hji]) (by
      intro hnot
      exact (hnot (Polynomial.natDegree_mem_support_of_nonzero hq0)).elim)]
  simp [hjn,  hq.leadingCoeff]

theorem commutator_iterate_eval_eq_eval_normal
    (p : B) (q : Polynomial B) (j : ℕ)
    (hpb : ∀ c : B,
      O.embed p * O.embed c = O.embed c * O.embed p)
    (hDp : D p = -1) :
    ((commutatorDerivation (O.embed p))^[j]) (eval D O q) =
      eval D O (commutatorNormal q j) := by
  rw [commutator_iterate_eval]
  change (∑ i ∈ q.support,
      ((commutatorDerivation (O.embed p))^[j])
        (O.embed (q.coeff i) * O.x ^ i)) =
    (evalAddHom D O) (∑ i ∈ q.support,
      if j ≤ i then
        Polynomial.monomial (i - j) (i.descFactorial j • q.coeff i)
      else 0)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hji : j ≤ i
  · simp only [ite_eq_left hji]
    rw [commutator_iterate_eval_monomial D O p (q.coeff i) i j hpb hDp]
    rw [ite_eq_left hji]
    change O.embed (q.coeff i) *
        (i.descFactorial j • O.x ^ (i - j)) =
      eval D O (Polynomial.monomial (i - j)
        (i.descFactorial j • q.coeff i))
    rw [eval_monomial]
    simp []
    simp [Nat.cast_comm, mul_assoc]
  · rw [commutator_iterate_eval_monomial D O p (q.coeff i) i j hpb hDp]
    simp [hji]

lemma eval_push_eq_expansion (b : B) (n : ℕ) :
    eval D O (OreDivision.push D b n) = expansion D O b n := by
  change (evalAddHom D O) (OreDivision.push D b n) = expansion D O b n
  unfold OreDivision.push
  rw [map_sum]
  change (∑ k ∈ Finset.range (n + 1),
      eval D O (Polynomial.monomial (n - k)
        (Nat.choose n k • (D^[k]) b))) = expansion D O b n
  simp_rw [eval_monomial]
  simp only [map_nsmul, smul_mul_assoc]
  unfold expansion
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • term D O b i j) n]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

theorem eval_push (b : B) (n : ℕ) :
    eval D O (OreDivision.push D b n) = O.x ^ n * O.embed b := by
  rw [eval_push_eq_expansion, (pow_mul D O b n).symm]

lemma eval_rightTerm (i : ℕ) (a b : B) (j : ℕ) :
    eval D O (rightTerm D i a b j) =
      (O.embed a * O.x ^ i) * (O.embed b * O.x ^ j) := by
  change (evalAddHom D O) (rightTerm D i a b j) = _
  unfold rightTerm
  rw [map_sum]
  change (∑ k ∈ Finset.range (i + 1),
      eval D O (Polynomial.monomial (i - k + j)
        (a * (Nat.choose i k • (D^[k]) b)))) = _
  simp_rw [eval_monomial]
  simp only [map_nsmul, map_mul]
  calc
    ∑ k ∈ Finset.range (i + 1),
        O.embed a * (Nat.choose i k • O.embed ((D^[k]) b)) *
          O.x ^ (i - k + j) =
        O.embed a *
          (∑ k ∈ Finset.range (i + 1),
            Nat.choose i k •
              (O.embed ((D^[k]) b) * O.x ^ (i - k)) * O.x ^ j) := by
            simp_rw [mul_assoc, smul_mul_assoc]
            rw [← Finset.mul_sum]
            apply congrArg (fun z => O.embed a * z)
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_add]
            simp only [mul_assoc]
    _ = O.embed a *
          ((O.x ^ i * O.embed b) * O.x ^ j) := by
            rw [← Finset.sum_mul]
            congr 1
            apply congrArg (fun z => z * O.x ^ j)
            change (∑ k ∈ Finset.range (i + 1),
              i.choose k • term D O b k (i - k)) = O.x ^ i * O.embed b
            rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun u v => i.choose u • term D O b u v) i]
            change expansion D O b i = O.x ^ i * O.embed b
            exact (pow_mul D O b i).symm
    _ = (O.embed a * O.x ^ i) * (O.embed b * O.x ^ j) := by
            noncomm_ring

lemma eval_rightMulMonomial (p : Polynomial B) (b : B) (j : ℕ) :
    eval D O (rightMulMonomial D p b j) =
      eval D O p * (O.embed b * O.x ^ j) := by
  change (evalAddHom D O) (rightMulMonomial D p b j) = _
  unfold rightMulMonomial
  change (evalAddHom D O) (∑ i ∈ p.support,
      rightTerm D i (p.coeff i) b j) = _
  rw [map_sum]
  change (∑ i ∈ p.support,
      eval D O (rightTerm D i (p.coeff i) b j)) = _
  simp_rw [eval_rightTerm]
  unfold eval
  rw [Polynomial.sum_def, Finset.sum_mul]

lemma eval_rightMul (d q : Polynomial B) :
    eval D O (rightMul D d q) = eval D O d * eval D O q := by
  change (evalAddHom D O) (rightMul D d q) = _
  unfold rightMul
  change (evalAddHom D O) (∑ j ∈ q.support,
      rightMulMonomial D d (q.coeff j) j) = _
  rw [map_sum]
  change (∑ j ∈ q.support,
      eval D O (rightMulMonomial D d (q.coeff j) j)) = _
  simp_rw [eval_rightMulMonomial]
  unfold eval
  simp only [Polynomial.sum_def]
  rw [Finset.mul_sum]

theorem eval_right_division_sound [Nontrivial B] (d p : Polynomial B)
    (hd : d.Monic) :
    ∃ q r : Polynomial B,
      eval D O p = eval D O d * eval D O q + eval D O r ∧
        (r = 0 ∨ r.natDegree < d.natDegree) := by
  obtain ⟨q, r, hdecomp, hrem⟩ := right_division_exists D d p hd
  refine ⟨q, r, ?_, hrem⟩
  rw [hdecomp, eval_add D O, eval_rightMul D O]

end OreAmbient

end OreDivision

end
end AlgebraicAnalysis
