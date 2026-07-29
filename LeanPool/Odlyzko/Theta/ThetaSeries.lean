/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.DualLattice
public import LeanPool.Odlyzko.Theta.GaussianSummability

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

/-- A lattice theta used in the Odlyzko-bound argument. -/
noncomputable def latticeTheta
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  ∑' x : L, latticeGaussian a (x : E)

section

variable [NormedSpace ℝ E]

theorem latticeTheta_map_linearIsometryEquiv
    (L : Submodule ℤ E) (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) :
    latticeTheta
        (L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap) a =
      latticeTheta L a := by
  let eZ : E ≃ₗ[ℤ] E := e.toLinearEquiv.restrictScalars ℤ
  let eL :
      L ≃ₗ[ℤ] L.map eZ.toLinearMap :=
    Submodule.equivMapOfInjective eZ.toLinearMap eZ.injective L
  rw [latticeTheta, latticeTheta, ← eL.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  unfold latticeGaussian
  rw [show ((eL.toEquiv x : L.map eZ.toLinearMap) : E) = e x by rfl,
    e.norm_map]

theorem summable_latticeTheta [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) :=
  summable_latticeGaussian L ha

end

/-- A dual lattice theta used in the Odlyzko-bound argument. -/
noncomputable def dualLatticeTheta [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  latticeTheta (dualLattice L) a

end NumberField.Odlyzko
