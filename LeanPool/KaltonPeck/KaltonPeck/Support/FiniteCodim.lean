/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
public import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.RadicalQuotient

/-!
# Finite-codimensional symplectic reduction

This file relates symplectic orthogonals to finite codimension, constructs the relevant quotient
forms, and proves the finite-codimensional parity theorem.
-/

@[expose] public section

namespace KaltonPeck.Support.FiniteCodim

noncomputable
section

/-- Orthogonal dimensions and the double orthogonal in a strong symplectic Banach space.

Blueprint: `lem:strong-orthogonals`; audit: `AUX-STRONG-ORTHOGONAL-DIMENSIONS`. -/
theorem strongOrthogonals {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (W : Submodule ℝ X)
    [IsClosed (W : Set X)] [FiniteDimensional ℝ (X ⧸ W)] :
    FiniteDimensional ℝ (omega.toContinuousAlternatingForm.orthogonal W) ∧
      Module.finrank ℝ (omega.toContinuousAlternatingForm.orthogonal W) =
        Module.finrank ℝ (X ⧸ W) ∧
      omega.toContinuousAlternatingForm.orthogonal
          (omega.toContinuousAlternatingForm.orthogonal W) = W := by
  let B := omega.toContinuousAlternatingForm
  let orthToAnn : B.orthogonal W →ₗ[ℝ] Forms.continuousAnnihilator W :=
    { toFun := fun x => ⟨omega.toDual x, by exact x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  have hInjective : Function.Injective orthToAnn := by
    intro x y hxy
    apply Subtype.ext
    apply omega.toDual.injective
    exact congrArg Subtype.val hxy
  have hSurjective : Function.Surjective orthToAnn := by
    intro phi
    let x : X := omega.toDual.symm (phi : StrongDual ℝ X)
    have hx : x ∈ B.orthogonal W := by
      change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ)) W.subtypeL).comp
        B.toDual) x = 0
      change ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ)) W.subtypeL)
        (omega.toDual x) = 0
      rw [show omega.toDual x = (phi : StrongDual ℝ X) by
        exact omega.toDual.apply_symm_apply _]
      exact phi.property
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact omega.toDual.apply_symm_apply _
  let eOrth : B.orthogonal W ≃ₗ[ℝ] Forms.continuousAnnihilator W :=
    LinearEquiv.ofBijective orthToAnn ⟨hInjective, hSurjective⟩
  let hAnn : FiniteDimensional ℝ (Forms.continuousAnnihilator W) :=
    FiniteDimensional.of_surjective
      (Forms.quotientDualEquivAnnihilator W).toLinearMap
      (Forms.quotientDualEquivAnnihilator W).surjective
  let hOrth : FiniteDimensional ℝ (B.orthogonal W) :=
    FiniteDimensional.of_injective (V₂ := Forms.continuousAnnihilator W)
      orthToAnn hInjective
  let eCont : StrongDual ℝ (X ⧸ W) ≃ₗ[ℝ] Module.Dual ℝ (X ⧸ W) :=
    (LinearMap.toContinuousLinearMap :
      Module.Dual ℝ (X ⧸ W) ≃ₗ[ℝ] StrongDual ℝ (X ⧸ W)).symm
  have hFinrank : Module.finrank ℝ (B.orthogonal W) = Module.finrank ℝ (X ⧸ W) := by
    calc
      Module.finrank ℝ (B.orthogonal W) =
          Module.finrank ℝ (Forms.continuousAnnihilator W) := eOrth.finrank_eq
      _ = Module.finrank ℝ (StrongDual ℝ (X ⧸ W)) :=
        (Forms.quotientDualEquivAnnihilator W).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℝ (Module.Dual ℝ (X ⧸ W)) := eCont.finrank_eq
      _ = Module.finrank ℝ (X ⧸ W) := Subspace.dual_finrank_eq
  have hSkew (x y : X) : omega.toDual x y = -omega.toDual y x := by
    have h := omega.alternating (x + y)
    simp only [map_add, add_apply, omega.alternating, add_zero, zero_add] at h
    linarith
  have hDouble : B.orthogonal (B.orthogonal W) = W := by
    ext x
    constructor
    · intro hx
      have hxAnn : ∀ phi : Forms.continuousAnnihilator W,
          (phi : StrongDual ℝ X) x = 0 := by
        intro phi
        let z : X := omega.toDual.symm (phi : StrongDual ℝ X)
        have hz : z ∈ B.orthogonal W := by
          change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
            W.subtypeL).comp B.toDual) z = 0
          change ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
            W.subtypeL) (omega.toDual z) = 0
          rw [show omega.toDual z = (phi : StrongDual ℝ X) by
            exact omega.toDual.apply_symm_apply _]
          exact phi.property
        have hxz : omega.toDual x z = 0 := by
          change (((ContinuousLinearMap.flip
            (ContinuousLinearMap.compL ℝ (B.orthogonal W) X ℝ))
              (B.orthogonal W).subtypeL).comp B.toDual) x = 0 at hx
          exact DFunLike.congr_fun hx ⟨z, hz⟩
        calc
          (phi : StrongDual ℝ X) x = omega.toDual z x := by
            rw [show omega.toDual z = (phi : StrongDual ℝ X) by
              exact omega.toDual.apply_symm_apply _]
          _ = -omega.toDual x z := hSkew z x
          _ = 0 := by rw [hxz, neg_zero]
      exact (Set.ext_iff.mp (Forms.continuousDoubleAnnihilator W inferInstance) x).mp hxAnn
    · intro hx
      change (((ContinuousLinearMap.flip
        (ContinuousLinearMap.compL ℝ (B.orthogonal W) X ℝ))
          (B.orthogonal W).subtypeL).comp B.toDual) x = 0
      apply ContinuousLinearMap.ext
      intro z
      have hz := z.property
      change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
        W.subtypeL).comp B.toDual) z = 0 at hz
      have hzx : omega.toDual z x = 0 := DFunLike.congr_fun hz ⟨x, hx⟩
      change omega.toDual x (z : X) = 0
      rw [hSkew, hzx, neg_zero]
  exact ⟨hOrth, hFinrank, hDouble⟩

/-- Parity of codimension and restricted radical in a strong symplectic Banach space.

Blueprint: `lem:strong-codim-parity`; audit: `LEM-STRONG-SYMPLECTIC-CODIM-PARITY`. -/
theorem strongCodimParity {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (W : Submodule ℝ X)
    [IsClosed (W : Set X)] [FiniteDimensional ℝ (X ⧸ W)] :
    Nat.ModEq 2 (Module.finrank ℝ (X ⧸ W))
      (Module.finrank ℝ (omega.toContinuousAlternatingForm.restrictedRadical W)) := by
  let B := omega.toContinuousAlternatingForm
  let O := B.orthogonal W
  obtain ⟨hOFinite, hODim, hDouble⟩ := strongOrthogonals omega W
  let : FiniteDimensional ℝ O := hOFinite
  let c := B.restrict O
  obtain ⟨_, hMod⟩ := FiniteParity.finiteContinuousAlternatingRankEven c
  let radicalEquiv : c.radical ≃ₗ[ℝ] B.restrictedRadical W :=
    { toFun := fun x => ⟨x, by
          constructor
          · rw [← hDouble]
            exact x.property
          · exact x.val.property⟩
      invFun := fun r => ⟨⟨r, r.property.2⟩, by
          change (r : X) ∈ B.orthogonal O
          rw [hDouble]
          exact r.property.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro r; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  rw [← hODim]
  rw [← radicalEquiv.finrank_eq]
  change Nat.ModEq 2 (Module.finrank ℝ O) (Module.finrank ℝ c.radical)
  exact Nat.ModEq.symm hMod

/-- Finite-codimensional parity for a Fredholm alternating form.

Blueprint: `thm:finite-codim-parity`; audit: `LEM-FINCODIM-PARITY` and
`AUX-FINCODIM-PARITY-ARITHMETIC`. -/
theorem finiteCodimParity {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) (E : Submodule ℝ X) [IsClosed (E : Set X)]
    [FiniteDimensional ℝ (X ⧸ E)] :
    FiniteDimensional ℝ (eta.restrictedRadical E) ∧
      Nat.ModEq 2 (Module.finrank ℝ (X ⧸ E))
        (Module.finrank ℝ eta.radical + Module.finrank ℝ (eta.restrictedRadical E)) := by
  let data := radicalQuotient eta hReflexive hFredholm E
  let : FiniteDimensional ℝ (eta.restrictedRadical E) :=
    data.restrictedRadicalFiniteDimensional
  refine ⟨inferInstance, ?_⟩
  let Q := Submodule.map eta.radical.mkQ (E ⊔ eta.radical)
  let : IsClosed (Q : Set (X ⧸ eta.radical)) := data.quotientImageClosed
  let : FiniteDimensional ℝ ((X ⧸ eta.radical) ⧸ Q) :=
    data.quotientImageFiniteCodimensional
  have hStrong := strongCodimParity
    (fredholmQuotientStrong eta hReflexive hFredholm).form Q
  have hRadical := data.radicalFinrank
  have hCodim := data.codimFinrank
  dsimp only [Q] at hStrong
  unfold Nat.ModEq at hStrong ⊢
  omega

end

end KaltonPeck.Support.FiniteCodim

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
