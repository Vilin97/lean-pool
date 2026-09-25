/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.RandomField

/-! # Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Symmetric coefficient fields

This file contains the lightweight pointwise symmetry API used to specialize the
general nonsymmetric coarse-graining definitions to symmetric coefficient
fields.
-/

/-- A coefficient field is symmetric if each pointwise coefficient matrix is
symmetric. -/
def IsSymmetricCoeffField {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ x, (a x).IsSymm

namespace IsSymmetricCoeffField

theorem apply {d : ℕ} {a : CoeffField d} (ha : IsSymmetricCoeffField a)
    (x : Vec d) :
    (a x).IsSymm :=
  ha x

theorem translateCoeffField {d : ℕ} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a) (z : Vec d) :
    IsSymmetricCoeffField (Homogenization.translateCoeffField z a) := by
  intro x
  exact ha (fun i => x i + z i)

end IsSymmetricCoeffField

theorem isSymmetricCoeffField_iff_matTranspose_eq {d : ℕ} {a : CoeffField d} :
    IsSymmetricCoeffField a ↔ ∀ x, matTranspose (a x) = a x := by
  constructor
  · intro ha x
    simpa [matTranspose] using (ha x).eq
  · intro h x
    rw [Matrix.IsSymm]
    simpa [matTranspose] using h x

theorem adjointCoeffField_eq_self_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} (ha : IsSymmetricCoeffField a) :
    adjointCoeffField a = a := by
  funext x
  simpa [adjointCoeffField] using
    (isSymmetricCoeffField_iff_matTranspose_eq.mp ha x)

theorem symmPart_eq_self_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} (ha : IsSymmetricCoeffField a) (x : Vec d) :
    symmPart (a x) = a x := by
  ext i j
  simp [symmPart, (ha x).apply i j]

theorem skewPart_eq_zero_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} (ha : IsSymmetricCoeffField a) (x : Vec d) :
    skewPart (a x) = 0 := by
  ext i j
  simp [skewPart, (ha x).apply i j]

theorem symmCoeffField_eq_self_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} (ha : IsSymmetricCoeffField a) :
    symmCoeffField a = a := by
  funext x
  exact symmPart_eq_self_of_isSymmetricCoeffField ha x

theorem skewCoeffField_eq_zero_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} (ha : IsSymmetricCoeffField a) :
    skewCoeffField a = 0 := by
  funext x
  exact skewPart_eq_zero_of_isSymmetricCoeffField ha x

end

end Homogenization
