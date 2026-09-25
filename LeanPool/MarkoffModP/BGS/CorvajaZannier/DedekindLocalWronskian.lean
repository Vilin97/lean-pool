/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPlaceOrder
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.WronskianChangeParameter
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Wronskian order estimates at a Dedekind DVR place

This file proves the determinant-level local estimate directly in a fraction
field equipped with a height-one-place order.  It avoids passage to Laurent
series: the only local input is a DVR-preserving derivation which sends a
chosen uniformizer to one.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators
open IsDedekindDomain Multiplicative WithZero

variable {R L : Type*} [CommRing R] [IsDedekindDomain R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The order of a finite product is the sum of the orders, including zero
factors via `WithTop`. -/
theorem finitePlaceOrderTop_finset_prod
    {ι : Type*} [DecidableEq ι] (v : HeightOneSpectrum R)
    (s : Finset ι) (g : ι → L) :
    finitePlaceOrderTop v (∏ i ∈ s, g i) =
      ∑ i ∈ s, finitePlaceOrderTop v (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, Finset.sum_insert, ha, not_false_eq_true]
      rw [finitePlaceOrderTop_mul, ih]

/-- If every summand has order at least `b`, then their finite sum also has
order at least `b`.  This is the cancellation step in the determinant
estimate. -/
theorem le_finitePlaceOrderTop_finset_sum_of_forall
    {ι : Type*} [DecidableEq ι] (v : HeightOneSpectrum R)
    (b : WithTop ℤ) (s : Finset ι) (g : ι → L)
    (h : ∀ i ∈ s, b ≤ finitePlaceOrderTop v (g i)) :
    b ≤ finitePlaceOrderTop v (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      have haBound : b ≤ finitePlaceOrderTop v (g a) :=
        h a (Finset.mem_insert_self a s)
      have hsBound : b ≤ finitePlaceOrderTop v (∑ i ∈ s, g i) := by
        apply ih
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      exact (le_min haBound hsBound).trans
        (finitePlaceOrderTop_add_ge_min v (g a) (∑ i ∈ s, g i))

/-- Multiplication by an integer coefficient cannot decrease finite-place
order.  This handles the permutation signs in the Leibniz determinant
formula. -/
theorem finitePlaceOrderTop_le_intCast_mul
    (v : HeightOneSpectrum R) (z : ℤ) (x : L) :
    finitePlaceOrderTop v x ≤ finitePlaceOrderTop v ((z : L) * x) := by
  rw [finitePlaceOrderTop_mul]
  have hz : (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (z : L) := by
    simpa using finitePlaceOrderTop_algebraMap_nonnegative
      (L := L) v (z : R)
  calc
    finitePlaceOrderTop v x = 0 + finitePlaceOrderTop v x := by simp
    _ ≤ finitePlaceOrderTop v (z : L) + finitePlaceOrderTop v x :=
      add_le_add hz le_rfl

private theorem coe_sum_int_finset
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

private theorem coe_sum_int
    {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    (((∑ i, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, ((g i : ℤ) : WithTop ℤ) := by
  classical
  exact coe_sum_int_finset Finset.univ g

section DVR

variable [IsDiscreteValuationRing R]
variable {C : Type*} [Field C] [Algebra C R] [Algebra C L]
  [IsScalarTower C R L]

/-- An indexed ordinary-derivation Wronskian over the fraction field.  The
function `ε` records the derivative order assigned to each row. -/
def indexedDedekindLocalWronskian
    {ι : Type*} [Fintype ι] (D : Derivation C L L)
    (ε : ι → ℕ) (f : ι → L) : Matrix ι ι L :=
  fun i j ↦ ((D : L → L)^[ε i]) (f j)

/-- Apply a constant scalar matrix to the columns of an indexed fraction-field
family. -/
def indexedDedekindLocalColumnCombination
    {ι : Type*} [Fintype ι] (f : ι → L) (A : Matrix ι ι C) : ι → L :=
  fun j ↦ ∑ i, A i j • f i

private theorem derivation_iterate_sum_smul
    {ι : Type*} [Fintype ι] (D : Derivation C L L)
    (r : ℕ) (a : ι → C) (f : ι → L) :
    ((D : L → L)^[r]) (∑ i, a i • f i) =
      ∑ i, a i • ((D : L → L)^[r]) (f i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp_rw [Function.iterate_succ_apply']
      rw [ih, map_sum]
      simp

/-- Constant column operations commute with the indexed DVR Wronskian. -/
theorem indexedDedekindLocalWronskian_columnCombination
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Derivation C L L) (ε : ι → ℕ) (f : ι → L)
    (A : Matrix ι ι C) :
    indexedDedekindLocalWronskian D ε
        (indexedDedekindLocalColumnCombination f A) =
      indexedDedekindLocalWronskian D ε f *
        A.map (algebraMap C L) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [indexedDedekindLocalWronskian,
    indexedDedekindLocalColumnCombination, Matrix.map_apply]
  rw [derivation_iterate_sum_smul]
  simp only [Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- A determinant-one constant column operation preserves the indexed DVR
Wronskian determinant. -/
theorem indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Derivation C L L) (ε : ι → ℕ) (f : ι → L)
    (A : Matrix ι ι C) (hA : A.det = 1) :
    (indexedDedekindLocalWronskian D ε
      (indexedDedekindLocalColumnCombination f A)).det =
        (indexedDedekindLocalWronskian D ε f).det := by
  rw [indexedDedekindLocalWronskian_columnCombination, Matrix.det_mul]
  have hdetmap : (A.map (algebraMap C L)).det = 1 := by
    calc
      (A.map (algebraMap C L)).det = algebraMap C L A.det := by
        simpa using ((algebraMap C L).map_det A).symm
      _ = 1 := by rw [hA, map_one]
  rw [hdetmap, mul_one]

omit [IsDedekindDomain R] [IsFractionRing R L] [IsDiscreteValuationRing R]
    [Algebra C R] [IsScalarTower C R L] in
private theorem derivation_iterate_algebraMap_exists
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (m : ℕ) (r : R) :
    ∃ s : R, ((D : L → L)^[m]) (algebraMap R L r) = algebraMap R L s := by
  induction m with
  | zero => exact ⟨r, rfl⟩
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨s, hs⟩ := ih
      rw [hs]
      exact hDIntegral s

omit [Algebra C R] [IsScalarTower C R L] in
/-- For any DVR-preserving derivation, the indexed Wronskian determinant has
order at least the sum of its column orders minus the sum of its row
derivative orders.  Cancellation in the determinant expansion is included. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (ε : ι → ℕ) (f : ι → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (indexedDedekindLocalWronskian D ε f).det := by
  rw [Matrix.det_apply']
  apply le_finitePlaceOrderTop_finset_sum_of_forall
  intro σ _
  let term : L :=
    ((Equiv.Perm.sign σ : ℤ) : L) *
      ∏ i, indexedDedekindLocalWronskian D ε f (σ i) i
  change
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v term
  calc
    (∑ j, finitePlaceOrderTop v (f j)) +
          ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) =
        ∑ j, (finitePlaceOrderTop v (f j) +
          ((-(ε (σ j) : ℤ) : ℤ) : WithTop ℤ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← coe_sum_int]
      congr 1
      rw [Finset.sum_neg_distrib]
      congr 1
      exact (Equiv.sum_comp σ (fun i ↦ (ε i : ℤ))).symm
    _ ≤ ∑ j, finitePlaceOrderTop v
        (((D : L → L)^[ε (σ j)]) (f j)) := by
      gcongr with j
      exact finitePlaceOrderTop_derivation_iterate_ge_sub_nat_of_preserves
        v π hπ hπIdeal D hDIntegral (ε (σ j)) (f j)
    _ = finitePlaceOrderTop v
        (∏ i, indexedDedekindLocalWronskian D ε f (σ i) i) := by
      rw [finitePlaceOrderTop_finset_prod]
      rfl
    _ ≤ finitePlaceOrderTop v term := by
      exact finitePlaceOrderTop_le_intCast_mul v
        (Equiv.Perm.sign σ : ℤ)
        (∏ i, indexedDedekindLocalWronskian D ε f (σ i) i)

omit [Algebra C R] [IsScalarTower C R L] in
/-- The normalized-uniformizer form retained for compatibility with the
existing local-parameter API. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (_hDπ : D (algebraMap R L π) = 1)
    (ε : ι → ℕ) (f : ι → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (indexedDedekindLocalWronskian D ε f).det :=
  finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
    v π hπ hπIdeal D hDIntegral ε f

omit [IsDiscreteValuationRing R] [Algebra C R] [IsScalarTower C R L] in
/-- If every column is represented by an element of the DVR and the
derivation preserves the DVR, then the indexed Wronskian determinant is
regular.  This is the direct DVR analogue of the regular local auxiliary
case. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_nonnegative_of_integral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (ε : ι → ℕ) (f : ι → L)
    (hfIntegral : ∀ j, ∃ r : R, f j = algebraMap R L r) :
    (0 : WithTop ℤ) ≤
      finitePlaceOrderTop v (indexedDedekindLocalWronskian D ε f).det := by
  rw [Matrix.det_apply']
  apply le_finitePlaceOrderTop_finset_sum_of_forall
  intro σ _
  let term : L :=
    ((Equiv.Perm.sign σ : ℤ) : L) *
      ∏ i, indexedDedekindLocalWronskian D ε f (σ i) i
  change (0 : WithTop ℤ) ≤ finitePlaceOrderTop v term
  calc
    (0 : WithTop ℤ) = ∑ _i : ι, (0 : WithTop ℤ) := by simp
    _ ≤ ∑ i, finitePlaceOrderTop v
        (indexedDedekindLocalWronskian D ε f (σ i) i) := by
      gcongr with i
      obtain ⟨r, hr⟩ := hfIntegral i
      obtain ⟨s, hs⟩ := derivation_iterate_algebraMap_exists
        D hDIntegral (ε (σ i)) r
      have hentry : indexedDedekindLocalWronskian D ε f (σ i) i =
          algebraMap R L s := by
        simp only [indexedDedekindLocalWronskian, hr, hs]
      rw [hentry]
      exact finitePlaceOrderTop_algebraMap_nonnegative (L := L) v s
    _ = finitePlaceOrderTop v
        (∏ i, indexedDedekindLocalWronskian D ε f (σ i) i) := by
      rw [finitePlaceOrderTop_finset_prod]
    _ ≤ finitePlaceOrderTop v term := by
      exact finitePlaceOrderTop_le_intCast_mul v
        (Equiv.Perm.sign σ : ℤ)
        (∏ i, indexedDedekindLocalWronskian D ε f (σ i) i)

omit [Algebra C R] [IsScalarTower C R L] in
/-- The indexed determinant estimate after a determinant-one constant column
operation, assuming only that the derivation preserves the DVR. -/
theorem
  finitePlaceOrderTop_dedekindLocalWronskian_det_lower_bound_after_columnCombination_of_preserves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (ε : ι → ℕ) (f : ι → L) (A : Matrix ι ι C) (hA : A.det = 1) :
    (∑ j, finitePlaceOrderTop v
        (indexedDedekindLocalColumnCombination f A j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (indexedDedekindLocalWronskian D ε f).det := by
  rw [← indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
    D ε f A hA]
  exact finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
    v π hπ hπIdeal D hDIntegral ε
      (indexedDedekindLocalColumnCombination f A)

omit [Algebra C R] [IsScalarTower C R L] in
/-- The indexed determinant estimate after a determinant-one constant column
operation.  This normalized form is retained for the local-parameter API. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_after_columnCombination
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (hDπ : D (algebraMap R L π) = 1)
    (ε : ι → ℕ) (f : ι → L) (A : Matrix ι ι C) (hA : A.det = 1) :
    (∑ j, finitePlaceOrderTop v
        (indexedDedekindLocalColumnCombination f A j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (indexedDedekindLocalWronskian D ε f).det := by
  rw [← indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
    D ε f A hA]
  exact finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound
    v π hπ hπIdeal D hDIntegral hDπ ε
      (indexedDedekindLocalColumnCombination f A)

/-- Change of parameter for an indexed ordinary Wronskian whose derivative
orders are `0, ..., n - 1`, transported along an explicit equivalence. -/
theorem indexedDedekindLocalWronskian_det_changeParameter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) (ε : ι → ℕ)
    (hε : ∀ i, ε i = (e i : ℕ))
    (D E : Derivation C L L) (a : L) (hD : D = a • E)
    (f : ι → L) :
    (indexedDedekindLocalWronskian D ε f).det =
      a ^ n.choose 2 * (indexedDedekindLocalWronskian E ε f).det := by
  let g : Fin n → L := fun j ↦ f (e.symm j)
  have hreindexD : Matrix.reindex e e
      (indexedDedekindLocalWronskian D ε f) =
        BGS.Algebra.derivationWronskian D g := by
    ext i j
    change ((D : L → L)^[ε (e.symm i)]) (f (e.symm j)) =
      (D.toLinearMap ^ (i : ℕ)) (f (e.symm j))
    rw [hε]
    simp only [e.apply_symm_apply]
    induction i.1 with
    | zero => simp
    | succ r ih =>
        rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ih]
        rfl
  have hreindexE : Matrix.reindex e e
      (indexedDedekindLocalWronskian E ε f) =
        BGS.Algebra.derivationWronskian E g := by
    ext i j
    change ((E : L → L)^[ε (e.symm i)]) (f (e.symm j)) =
      (E.toLinearMap ^ (i : ℕ)) (f (e.symm j))
    rw [hε]
    simp only [e.apply_symm_apply]
    induction i.1 with
    | zero => simp
    | succ r ih =>
        rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ih]
        rfl
  calc
    (indexedDedekindLocalWronskian D ε f).det =
        (Matrix.reindex e e
          (indexedDedekindLocalWronskian D ε f)).det := by
      rw [Matrix.det_reindex_self]
    _ = (BGS.Algebra.derivationWronskian D g).det := by rw [hreindexD]
    _ = a ^ n.choose 2 *
        (BGS.Algebra.derivationWronskian E g).det :=
      derivationWronskian_det_changeParameter D E a hD g
    _ = a ^ n.choose 2 *
        (Matrix.reindex e e
          (indexedDedekindLocalWronskian E ε f)).det := by rw [hreindexE]
    _ = a ^ n.choose 2 *
        (indexedDedekindLocalWronskian E ε f).det := by
      rw [Matrix.det_reindex_self]

omit [Algebra C R] [IsScalarTower C R L] in
/-- Indexed scaled-derivation estimate.  The equivalence certifies that the
row orders are precisely the ordinary derivative orders, so the scalar costs
the expected triangular exponent. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_scaled_preserves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) (ε : ι → ℕ)
    (hε : ∀ i, ε i = (e i : ℕ))
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L) (c : L)
    (hScaledIntegral : ∀ r : R, ∃ s : R,
      (c • D) (algebraMap R L r) = algebraMap R L s)
    (f : ι → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
      n.choose 2 • finitePlaceOrderTop v c +
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D ε f).det := by
  calc
    (∑ j, finitePlaceOrderTop v (f j)) +
          ((-(∑ i, (ε i : ℤ)) : ℤ) : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian (c • D) ε f).det :=
      finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
        v π hπ hπIdeal (c • D) hScaledIntegral ε f
    _ = finitePlaceOrderTop v
        (c ^ n.choose 2 *
          (indexedDedekindLocalWronskian D ε f).det) := by
      rw [indexedDedekindLocalWronskian_det_changeParameter
        e ε hε (c • D) D c rfl f]
    _ = n.choose 2 • finitePlaceOrderTop v c +
        finitePlaceOrderTop v
          (indexedDedekindLocalWronskian D ε f).det := by
      rw [finitePlaceOrderTop_mul, finitePlaceOrderTop_pow]

/-- The ordinary `n × n` Wronskian, with derivative orders
`0, ..., n - 1`. -/
def dedekindLocalWronskian {n : ℕ}
    (D : Derivation C L L) (f : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  indexedDedekindLocalWronskian D (fun i ↦ i.1) f

/-- The direct Dedekind-local Wronskian is definitionally the ordinary
derivation Wronskian used by the change-of-parameter theorem. -/
theorem dedekindLocalWronskian_eq_derivationWronskian
    (D : Derivation C L L) {n : ℕ} (f : Fin n → L) :
    dedekindLocalWronskian D f = BGS.Algebra.derivationWronskian D f := by
  ext i j
  change ((D : L → L)^[i.1]) (f j) = (D.toLinearMap ^ i.1) (f j)
  induction i.1 with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ih]
      rfl

/-- Change of parameter for the direct Dedekind-local Wronskian.  In
particular this permits replacing a global derivation by a DVR-preserving
scalar multiple while recording the exact triangular valuation cost. -/
theorem dedekindLocalWronskian_det_changeParameter
    (D E : Derivation C L L) (a : L) (hD : D = a • E)
    {n : ℕ} (f : Fin n → L) :
    (dedekindLocalWronskian D f).det =
      a ^ n.choose 2 * (dedekindLocalWronskian E f).det := by
  rw [dedekindLocalWronskian_eq_derivationWronskian,
    dedekindLocalWronskian_eq_derivationWronskian]
  exact derivationWronskian_det_changeParameter D E a hD f

omit [Algebra C R] [IsScalarTower C R L] in
/-- For a DVR-preserving derivation, the ordinary Wronskian loses at most the
triangular number `n * (n - 1) / 2` from the sum of its column orders. -/
theorem finitePlaceOrderTop_dedekindLocalWronskian_det_lower_bound_of_preserves
    {n : ℕ}
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (f : Fin n → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (dedekindLocalWronskian D f).det := by
  convert finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
    v π hπ hπIdeal D hDIntegral (fun i : Fin n => i.1) f using 1
  · congr 2
    apply congrArg Neg.neg
    rw [Fin.sum_univ_eq_sum_range, ← Nat.cast_sum]
    exact congrArg (fun x : ℕ => (x : ℤ)) (Finset.sum_range_id n).symm
  · rfl

omit [Algebra C R] [IsScalarTower C R L] in
/-- A scalar multiple of the ambient derivation may be used to obtain a
DVR-preserving local derivation.  The right side records exactly the order of
the scalar to the Wronskian triangular exponent; no false formula for
iterates of `c • D` is used. -/
theorem finitePlaceOrderTop_dedekindLocalWronskian_det_lower_bound_of_scaled_preserves
    {n : ℕ}
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L) (c : L)
    (hScaledIntegral : ∀ r : R, ∃ s : R,
      (c • D) (algebraMap R L r) = algebraMap R L s)
    (f : Fin n → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
      n.choose 2 • finitePlaceOrderTop v c +
        finitePlaceOrderTop v (dedekindLocalWronskian D f).det := by
  calc
    (∑ j, finitePlaceOrderTop v (f j)) +
          ((-(n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
        finitePlaceOrderTop v
          (dedekindLocalWronskian (c • D) f).det :=
      finitePlaceOrderTop_dedekindLocalWronskian_det_lower_bound_of_preserves
        v π hπ hπIdeal (c • D) hScaledIntegral f
    _ = finitePlaceOrderTop v
        (c ^ n.choose 2 * (dedekindLocalWronskian D f).det) := by
      rw [dedekindLocalWronskian_det_changeParameter (c • D) D c rfl f]
    _ = n.choose 2 • finitePlaceOrderTop v c +
        finitePlaceOrderTop v (dedekindLocalWronskian D f).det := by
      rw [finitePlaceOrderTop_mul, finitePlaceOrderTop_pow]

omit [Algebra C R] [IsScalarTower C R L] in
/-- The ordinary Wronskian loses at most the triangular number
`n * (n - 1) / 2` from the sum of its column orders.  This normalized form is
retained for the local-parameter API. -/
theorem finitePlaceOrderTop_dedekindLocalWronskian_det_lower_bound
    {n : ℕ}
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (hDπ : D (algebraMap R L π) = 1)
    (f : Fin n → L) :
    (∑ j, finitePlaceOrderTop v (f j)) +
        ((-(n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop v (dedekindLocalWronskian D f).det := by
  convert finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound
    v π hπ hπIdeal D hDIntegral hDπ (fun i : Fin n ↦ i.1) f using 1
  · congr 2
    apply congrArg Neg.neg
    rw [Fin.sum_univ_eq_sum_range, ← Nat.cast_sum]
    exact congrArg (fun x : ℕ ↦ (x : ℤ)) (Finset.sum_range_id n).symm
  · rfl

end DVR

end

end BGS.CorvajaZannier
