/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStrictLevels
public import Mathlib.Tactic

/-!
# One-point Stepanov grids

At an arbitrary exhaustive place, a finite family of nonzero functions with
pairwise distinct principal-divisor orders is linearly independent over the
constant field.  Applying this to products whose pole orders use a
mixed-radix encoding gives the one-point Stepanov grid.

The distinguished place is not assumed to have degree one.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance onePointStepanovGridConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance onePointStepanovGridConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype K] [DecidableEq K] in
/-- Multiplication by a nonzero constant does not change the order at an
exhaustive place. -/
theorem finiteExtensionPrincipalDivisor_smul_apply [Finite K]
    (P : FiniteExtensionPlace K L) (c : K) (x : L)
    (hc : c ≠ 0) (hx : x ≠ 0) :
    finiteExtensionPrincipalDivisor K L (c • x) P =
      finiteExtensionPrincipalDivisor K L x P := by
  classical
  have hcL : algebraMap K L c ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K L).injective.ne hc
  rw [Algebra.smul_def,
    finiteExtensionPrincipalDivisor_mul K L _ _ hcL hx,
    finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc]
  simp

omit [Fintype K] [DecidableEq K] in
/-- If one summand has strictly smaller order than the other, then the sum is
nonzero and has the smaller order. -/
theorem finiteExtensionPrincipalDivisor_add_eq_left_of_lt
    (P : FiniteExtensionPlace K L) (x y : L)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxyOrder : finiteExtensionPrincipalDivisor K L x P <
      finiteExtensionPrincipalDivisor K L y P) :
    x + y ≠ 0 ∧
      finiteExtensionPrincipalDivisor K L (x + y) P =
        finiteExtensionPrincipalDivisor K L x P := by
  have hxy : x + y ≠ 0 := by
    intro hzero
    have hyx : y = -x :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hzero)
    have hneg := finiteExtensionPrincipalDivisor_neg_apply K L x hx P
    rw [hyx, hneg] at hxyOrder
    exact (lt_irrefl _ hxyOrder)
  have hlower := finiteExtensionPrincipalDivisor_add_ge_min
    K L x y hx hy hxy P
  rw [min_eq_left (le_of_lt hxyOrder)] at hlower
  have hreverse := finiteExtensionPrincipalDivisor_add_ge_min
    K L (x + y) (-y) hxy (neg_ne_zero.mpr hy)
      (by simpa only [add_neg_cancel_right] using hx) P
  rw [show (x + y) + (-y) = x by ring,
    finiteExtensionPrincipalDivisor_neg_apply K L y hy P] at hreverse
  have hsumLeY :
      finiteExtensionPrincipalDivisor K L (x + y) P ≤
        finiteExtensionPrincipalDivisor K L y P := by
    by_contra hnot
    have hyLeSum : finiteExtensionPrincipalDivisor K L y P ≤
        finiteExtensionPrincipalDivisor K L (x + y) P := le_of_not_ge hnot
    rw [min_eq_right hyLeSum] at hreverse
    omega
  rw [min_eq_left hsumLeY] at hreverse
  exact ⟨hxy, le_antisymm hreverse hlower⟩

omit [Fintype K] [DecidableEq K] in
/-- If every summand has order strictly above `a`, then their finite sum is
either zero or also has order strictly above `a`. -/
theorem finiteExtensionPrincipalDivisor_sum_eq_zero_or_gt
    {ι : Type*} (P : FiniteExtensionPlace K L)
    (S : Finset ι) (f : ι → L) (a : ℤ)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (horder : ∀ i ∈ S, a < finiteExtensionPrincipalDivisor K L (f i) P) :
    (∑ i ∈ S, f i) = 0 ∨
      ((∑ i ∈ S, f i) ≠ 0 ∧
        a < finiteExtensionPrincipalDivisor K L (∑ i ∈ S, f i) P) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      have hi0 : f i ≠ 0 := hf i (Finset.mem_insert_self i S)
      have hiOrder : a < finiteExtensionPrincipalDivisor K L (f i) P :=
        horder i (Finset.mem_insert_self i S)
      have hrest := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => horder j (Finset.mem_insert_of_mem hj))
      rcases hrest with hrestZero | ⟨hrest0, hrestOrder⟩
      · rw [hrestZero, add_zero]
        exact Or.inr ⟨hi0, hiOrder⟩
      · by_cases hsum : f i + ∑ j ∈ S, f j = 0
        · exact Or.inl hsum
        · refine Or.inr ⟨hsum, ?_⟩
          have hlower := finiteExtensionPrincipalDivisor_add_ge_min
            K L (f i) (∑ j ∈ S, f j) hi0 hrest0 hsum P
          exact (lt_min hiOrder hrestOrder).trans_le hlower

omit [Fintype K] [DecidableEq K] in
/-- A unique least-order term controls a finite sum. -/
theorem finiteExtensionPrincipalDivisor_sum_eq_of_unique_min
    {ι : Type*} (P : FiniteExtensionPlace K L)
    (S : Finset ι) (f : ι → L) (i : ι) (hi : i ∈ S)
    (hf : ∀ j ∈ S, f j ≠ 0)
    (hmin : ∀ j ∈ S, j ≠ i →
      finiteExtensionPrincipalDivisor K L (f i) P <
        finiteExtensionPrincipalDivisor K L (f j) P) :
    (∑ j ∈ S, f j) ≠ 0 ∧
      finiteExtensionPrincipalDivisor K L (∑ j ∈ S, f j) P =
        finiteExtensionPrincipalDivisor K L (f i) P := by
  classical
  let T := S.erase i
  let r : L := ∑ j ∈ T, f j
  have hrest := finiteExtensionPrincipalDivisor_sum_eq_zero_or_gt
    K L P T f (finiteExtensionPrincipalDivisor K L (f i) P)
    (fun j hj => hf j (Finset.mem_of_mem_erase hj))
    (fun j hj => hmin j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj))
  have hsum : (∑ j ∈ S, f j) = f i + r := by
    rw [← Finset.sum_erase_add S f hi]
    simp only [T, r]
    ac_rfl
  rcases hrest with hrestZero | ⟨hrest0, hrestOrder⟩
  · change r = 0 at hrestZero
    rw [hsum, hrestZero, add_zero]
    exact ⟨hf i hi, rfl⟩
  · change r ≠ 0 at hrest0
    change finiteExtensionPrincipalDivisor K L (f i) P <
      finiteExtensionPrincipalDivisor K L r P at hrestOrder
    rw [hsum]
    exact finiteExtensionPrincipalDivisor_add_eq_left_of_lt
      K L P (f i) r (hf i hi) hrest0 hrestOrder

omit [Fintype K] [DecidableEq K] in
/-- A finite family of nonzero functions with pairwise distinct orders at one
exhaustive place is linearly independent over the constant field. -/
theorem linearIndependent_of_injective_finiteExtensionPrincipalDivisor_order [Finite K]
    {ι : Type*} [Finite ι]
    (P : FiniteExtensionPlace K L) (f : ι → L)
    (hf : ∀ i, f i ≠ 0)
    (horder : Function.Injective
      (fun i => finiteExtensionPrincipalDivisor K L (f i) P)) :
    LinearIndependent K f := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hrelation
  by_contra hnotZero
  push Not at hnotZero
  obtain ⟨i0, hi0⟩ := hnotZero
  let S : Finset ι := Finset.univ.filter (fun i => c i ≠ 0)
  have hSnonempty : S.Nonempty := by
    exact ⟨i0, by simp [S, hi0]⟩
  obtain ⟨i, hiS, hileast⟩ := S.exists_min_image
    (fun j => finiteExtensionPrincipalDivisor K L (f j) P) hSnonempty
  let term : ι → L := fun j => c j • f j
  have hterm0 : ∀ j ∈ S, term j ≠ 0 := by
    intro j hj
    have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
    change c j • f j ≠ 0
    rw [Algebra.smul_def]
    exact mul_ne_zero
      (by simpa only [map_zero] using (algebraMap K L).injective.ne hcj)
      (hf j)
  have htermOrder (j : ι) (hj : j ∈ S) :
      finiteExtensionPrincipalDivisor K L (term j) P =
        finiteExtensionPrincipalDivisor K L (f j) P := by
    exact finiteExtensionPrincipalDivisor_smul_apply
      K L P (c j) (f j) (Finset.mem_filter.mp hj).2 (hf j)
  have htermMin : ∀ j ∈ S, j ≠ i →
      finiteExtensionPrincipalDivisor K L (term i) P <
        finiteExtensionPrincipalDivisor K L (term j) P := by
    intro j hj hji
    rw [htermOrder i hiS, htermOrder j hj]
    exact lt_of_le_of_ne (hileast j hj)
      (fun heq => hji (horder heq).symm)
  have hsumNonzero :=
    (finiteExtensionPrincipalDivisor_sum_eq_of_unique_min
      K L P S term i hiS hterm0 htermMin).1
  apply hsumNonzero
  calc
    (∑ j ∈ S, term j) = ∑ j, term j := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _hjUniv hjNotS
      have hcj : c j = 0 := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          not_ne_iff] at hjNotS
        exact hjNotS
      simp [term, hcj]
    _ = 0 := by simpa only [term] using hrelation

/-- Mixed-radix encoding of two pole-order digits. -/
def onePointStepanovMixedOrder
    {ι κ : Type*} (d : ι → ℕ) (e : κ → ℕ) (s : ℕ)
    (ij : ι × κ) : ℕ :=
  d ij.1 + s * e ij.2

/-- If the first digit is strictly below the radix, the mixed pole-order
encoding is injective. -/
theorem onePointStepanovMixedOrder_injective
    {ι κ : Type*} (d : ι → ℕ) (e : κ → ℕ) (s : ℕ)
    (hd : Function.Injective d) (he : Function.Injective e)
    (hdigit : ∀ i, d i < s) :
    Function.Injective (onePointStepanovMixedOrder d e s) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le (d i)) (hdigit i)
  have hdEq : d i = d i' := by
    have hmod := congrArg (fun n : ℕ => n % s) h
    simpa only [onePointStepanovMixedOrder, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hdigit i), Nat.mod_eq_of_lt (hdigit i')] using hmod
  have hi : i = i' := hd hdEq
  subst i'
  have heEq : e j = e j' := by
    have hmul : s * e j = s * e j' := Nat.add_left_cancel h
    exact Nat.eq_of_mul_eq_mul_left hs hmul
  exact Prod.ext rfl (he heEq)

omit [Fintype K] [DecidableEq K] in
/-- Exact order of a product in the one-point Stepanov grid. -/
theorem onePointStepanovGrid_order
    {ι κ : Type*} (P : FiniteExtensionPlace K L)
    (f : ι → L) (g : κ → L) (d : ι → ℕ) (e : κ → ℕ) (s : ℕ)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hfOrder : ∀ i, finiteExtensionPrincipalDivisor K L (f i) P =
      -(d i : ℤ))
    (hgOrder : ∀ j, finiteExtensionPrincipalDivisor K L (g j) P =
      -(e j : ℤ))
    (ij : ι × κ) :
    finiteExtensionPrincipalDivisor K L
        (f ij.1 * (g ij.2) ^ s) P =
      -(onePointStepanovMixedOrder d e s ij : ℤ) := by
  rw [finiteExtensionPrincipalDivisor_mul K L _ _
      (hf ij.1) (pow_ne_zero s (hg ij.2)),
    finiteExtensionPrincipalDivisor_pow K L _ (hg ij.2) s]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    hfOrder, hgOrder, onePointStepanovMixedOrder]
  push_cast
  ring

omit [Fintype K] [DecidableEq K] in
/-- Two strict-level families whose first pole-order digit is below `s`
produce a linearly independent Stepanov product grid. -/
theorem onePointStepanovGrid_linearIndependent [Finite K]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : FiniteExtensionPlace K L)
    (f : ι → L) (g : κ → L) (d : ι → ℕ) (e : κ → ℕ) (s : ℕ)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hfOrder : ∀ i, finiteExtensionPrincipalDivisor K L (f i) P =
      -(d i : ℤ))
    (hgOrder : ∀ j, finiteExtensionPrincipalDivisor K L (g j) P =
      -(e j : ℤ))
    (hd : Function.Injective d) (he : Function.Injective e)
    (hdigit : ∀ i, d i < s) :
    LinearIndependent K (fun ij : ι × κ => f ij.1 * (g ij.2) ^ s) := by
  classical
  apply linearIndependent_of_injective_finiteExtensionPrincipalDivisor_order
    K L P
  · intro ij
    exact mul_ne_zero (hf ij.1) (pow_ne_zero s (hg ij.2))
  · intro ij ij' horderEq
    apply onePointStepanovMixedOrder_injective d e s hd he hdigit
    have hcast :
        -(onePointStepanovMixedOrder d e s ij : ℤ) =
          -(onePointStepanovMixedOrder d e s ij' : ℤ) := by
      rw [← onePointStepanovGrid_order K L P f g d e s
          hf hg hfOrder hgOrder ij,
        ← onePointStepanovGrid_order K L P f g d e s
          hf hg hfOrder hgOrder ij']
      exact horderEq
    exact_mod_cast (neg_inj.mp hcast)

end

end BGS.HasseWeil
