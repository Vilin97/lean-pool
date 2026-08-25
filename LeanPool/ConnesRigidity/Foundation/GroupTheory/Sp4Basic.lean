/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Conceptual finite proofs for the natural Sp₄(F₂) action in Zhou §§2 and 6.
Mathlib supplies the symplectic-matrix carrier and its standard module action.
-/
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.Field.ZMod
import LeanPool.ConnesRigidity.Foundation.LinearAlgebra.QuadraticCocycle

/-!
# The natural `Sp₄(𝔽₂)` action

This module gives the conceptual finite proof that `Sp₄(𝔽₂)` acts
transitively on nonzero vectors. It realizes the action with symplectic
transvections and keeps the exhaustive normal-subgroup certificate separate.
-/

namespace Connes
namespace Sp4

/-- Characteristic-two scalar field. Paper: §§2, 6. -/
abbrev F := ZMod 2
/-- Symplectic group carrier. Paper: §§2, 6. -/
abbrev Group := Matrix.symplecticGroup (Fin 2) F

private abbrev Matrix4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private def allMatrices : Finset Matrix4 := Finset.univ

private def symplecticMatrices : Finset Matrix4 :=
  allMatrices.filter (fun A =>
    A * Matrix.J (Fin 2) F * A.transpose = Matrix.J (Fin 2) F)

instance : Fintype Group :=
  Fintype.subtype symplecticMatrices (by
    intro x
    simp [Group, symplecticMatrices, allMatrices, Matrix.symplecticGroup])

private abbrev V := OpenAIPort.ModTwoSpace

private def pairing (v w : V) : F :=
  OpenAIPort.modTwoSymplecticForm v w

private def transvectionMatrix (u : V) : Matrix4 :=
  1 + Matrix.vecMulVec u ((Matrix.J (Fin 2) F).mulVec u)

private theorem transvectionMatrix_mem :
    ∀ u : V, transvectionMatrix u ∈ Matrix.symplecticGroup (Fin 2) F := by
  decide

private def transvection (u : V) : Group :=
  ⟨transvectionMatrix u, transvectionMatrix_mem u⟩

private theorem transvection_apply (u v : V) :
    transvection u • v = v + pairing v u • u := by
  decide +revert

private theorem pairing_self (v : V) : pairing v v = 0 := by
  decide +revert

private theorem pairing_add_right (u v w : V) :
    pairing u (v + w) = pairing u v + pairing u w := by
  exact OpenAIPort.modTwoSymplecticForm_add_right u v w

private theorem pairing_one_bridge :
    ∀ v : V, v ≠ 0 → ∀ w : V, w ≠ 0 → pairing v w = 0 →
      ∃ z : V, pairing v z = 1 ∧ pairing z w = 1 := by
  decide

/-- Nonzero-vector transitivity. Paper: §2. -/
theorem transitive_on_nonzero_vectors :
    ∀ v : OpenAIPort.ModTwoSpace, v ≠ 0 →
      ∀ w : OpenAIPort.ModTwoSpace, w ≠ 0 →
        ∃ g : Group, g • v = w := by
  intro v hv w hw
  by_cases hvw : pairing v w = 0
  · obtain ⟨z, hvz, hzw⟩ := pairing_one_bridge v hv w hw hvw
    refine ⟨transvection (z + w) * transvection (v + z), ?_⟩
    rw [mul_smul]
    rw [transvection_apply (v + z) v]
    rw [pairing_add_right, pairing_self, zero_add, hvz, one_smul]
    rw [show v + (v + z) = z by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
    rw [transvection_apply]
    rw [pairing_add_right, pairing_self, zero_add, hzw, one_smul]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · have hvw' : pairing v w = 1 := (isUnit_iff_ne_zero.mpr hvw).eq_one
    refine ⟨transvection (v + w), ?_⟩
    rw [transvection_apply, pairing_add_right, pairing_self, zero_add,
      hvw', one_smul]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end Sp4
end Connes
