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
public import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Duality and symplectic adjoints

This file develops continuous annihilators, quotient-dual equivalences, reflexivity induced by
strong symplectic forms, and the basic algebraic API for symplectic adjoints.
-/

@[expose] public section

namespace KaltonPeck.Support.Forms

noncomputable
section

/-- Continuous functionals on `X` that vanish on the subspace `W`.

Blueprint support for `lem:double-annihilator` and `lem:quotient-dual`; audit:
`DEF-ANNIHILATOR`. -/
def continuousAnnihilator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Submodule ℝ X) : Submodule ℝ (StrongDual ℝ X) := by
  exact ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL).ker

/-- Hahn--Banach continuous double-annihilator theorem for a closed subspace.

Blueprint: `lem:double-annihilator`; audit: `AUX-CONT-DOUBLE-ANNIHILATOR`. -/
theorem continuousDoubleAnnihilator {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (W : Submodule ℝ X)
    (hW : IsClosed (W : Set X)) :
    {x : X | ∀ φ : continuousAnnihilator W, (φ : StrongDual ℝ X) x = 0} = (W : Set X) := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨f, u, hfW, hfx⟩ := geometric_hahn_banach_closed_point W.convex hW hnot
    have hvanish : ∀ w : W, f w = 0 := by
      intro w
      by_contra hne
      have hmem : ((u + 1) / f w) • (w : X) ∈ W := W.smul_mem _ w.property
      have hlt := hfW _ hmem
      have heq : f (((u + 1) / f w) • (w : X)) = u + 1 := by
        simp [hne]
      rw [heq] at hlt
      linarith
    let φ : continuousAnnihilator W :=
      ⟨f, by
        change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) f = 0
        apply ContinuousLinearMap.ext
        intro w
        exact hvanish w⟩
    have hzero : f x = 0 := hx φ
    have hu := hfW 0 W.zero_mem
    simp only [map_zero] at hu
    linarith
  · intro hx φ
    have hφ := φ.property
    change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) φ.val = 0 at hφ
    exact DFunLike.congr_fun hφ ⟨x, hx⟩

/-- Pullback along the quotient map as a continuous equivalence with the annihilator.

Blueprint: `lem:quotient-dual`; audit: `AUX-CONT-QUOTIENT-DUAL-ANNIHILATOR`. -/
def quotientDualEquivAnnihilator {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (W : Submodule ℝ X)
    [hW : IsClosed (W : Set X)] :
    StrongDual ℝ (X ⧸ W) ≃L[ℝ] continuousAnnihilator W := by
  have hWComplete : IsComplete (W : Set X) := hW.isComplete
  letI : IsClosed (W : Set X) := hWComplete.isClosed
  let pullback : StrongDual ℝ (X ⧸ W) →L[ℝ] continuousAnnihilator W :=
    ((ContinuousLinearMap.compL ℝ X (X ⧸ W) ℝ).flip W.mkQL).codRestrict
      (continuousAnnihilator W) (fun φ => by
        change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL)
          (((ContinuousLinearMap.compL ℝ X (X ⧸ W) ℝ).flip W.mkQL) φ) = 0
        apply ContinuousLinearMap.ext
        intro x
        change φ (Submodule.Quotient.mk (x : X)) = 0
        rw [(Submodule.Quotient.mk_eq_zero W).2 x.property, map_zero])
  let inverseLinear : continuousAnnihilator W →ₗ[ℝ] StrongDual ℝ (X ⧸ W) :=
    { toFun := fun φ => W.liftQL (φ : StrongDual ℝ X) (by
        intro x hx
        have hφ := φ.property
        change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) φ.val = 0 at hφ
        exact DFunLike.congr_fun hφ ⟨x, hx⟩)
      map_add' := by
        intro φ ψ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl
      map_smul' := by
        intro a φ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl }
  have hinverse_bound : ∀ φ : continuousAnnihilator W, ‖inverseLinear φ‖ ≤ 1 * ‖φ‖ := by
    intro φ
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro q
    let f : NormedAddGroupHom X ℝ :=
      φ.val.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖φ‖
        (fun x => φ.val.le_opNorm x)
    have hf : ‖f‖ ≤ ‖φ‖ :=
      NormedAddGroupHom.opNorm_le_bound f (norm_nonneg φ) (fun x => φ.val.le_opNorm x)
    have hzero : ∀ x ∈ W.toAddSubgroup, f x = 0 := by
      intro x hx
      have hφ := φ.property
      change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) φ.val = 0 at hφ
      exact DFunLike.congr_fun hφ ⟨x, hx⟩
    calc
      ‖inverseLinear φ q‖ ≤ ‖f‖ * ‖q‖ := by
        exact QuotientAddGroup.norm_lift_apply_le f hzero q
      _ ≤ ‖φ‖ * ‖q‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg q)
  let inverse : continuousAnnihilator W →L[ℝ] StrongDual ℝ (X ⧸ W) :=
    LinearMap.mkContinuous (E := continuousAnnihilator W) (F := StrongDual ℝ (X ⧸ W))
      (σ := RingHom.id ℝ) inverseLinear 1 hinverse_bound
  let e : StrongDual ℝ (X ⧸ W) ≃ₗ[ℝ] continuousAnnihilator W :=
    { toFun := pullback
      invFun := inverse
      left_inv := by
        intro φ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl
      right_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        rfl
      map_add' := pullback.map_add
      map_smul' := pullback.map_smul }
  exact ContinuousLinearEquiv.mk e pullback.continuous inverse.continuous

/-- Evaluation formula for pullback along the quotient map.

Blueprint: `lem:quotient-dual`; audit: `AUX-CONT-QUOTIENT-DUAL-ANNIHILATOR`. -/
theorem quotientDualEquivAnnihilator_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (W : Submodule ℝ X)
    [hW : IsClosed (W : Set X)] (φ : StrongDual ℝ (X ⧸ W)) (x : X) :
    ((quotientDualEquivAnnihilator W φ : continuousAnnihilator W) : StrongDual ℝ X) x =
      φ (Submodule.Quotient.mk x) := by
  rfl

/-- The transpose identity that relates a strong alternating form to the double-dual inclusion.

Blueprint: `lem:strong-reflexive`; audit: `AUX-STRONG-SYMPLECTIC-REFLEXIVE`. -/
theorem strongSymplecticTransposeInclusion {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (ω : StrongSymplecticForm X) :
    (transpose ω.toDual.toContinuousLinearMap).comp
        (NormedSpace.inclusionInDoubleDual ℝ X) =
      -ω.toDual.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  change ω.toDual y x = -ω.toDual x y
  have h := ω.alternating (x + y)
  simp only [map_add, add_apply, ω.alternating, add_zero, zero_add] at h
  linarith

/-- Every strong symplectic real Banach space is reflexive.

Blueprint: `lem:strong-reflexive`; audit: `AUX-STRONG-SYMPLECTIC-REFLEXIVE`. -/
theorem strongSymplecticReflexive {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (ω : StrongSymplecticForm X) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X) := by
  intro F
  let z : X := ω.toDual.symm ((transpose ω.toDual.toContinuousLinearMap) F)
  refine ⟨-z, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  let y : X := ω.toDual.symm f
  have hy : ω.toDual y = f := ω.toDual.apply_symm_apply f
  change f (-z) = F f
  rw [← hy]
  change ω.toDual y (-z) = F (ω.toDual y)
  rw [map_neg]
  have h := ω.alternating (y + z)
  simp only [map_add, add_apply, ω.alternating, add_zero, zero_add] at h
  have hskew : -ω.toDual y z = ω.toDual z y := by linarith
  rw [hskew]
  change
    ω.toDual (ω.toDual.symm ((transpose ω.toDual.toContinuousLinearMap) F)) y =
      F (ω.toDual y)
  rw [ω.toDual.apply_symm_apply]
  rfl

/-- The symplectic adjoint of the identity is the identity.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) : ω.adjoint 1 = 1 := by
  have hadj (T : X →L[ℝ] X) (x y : X) :
      ω.toDual (ω.adjoint T x) y = ω.toDual x (T y) := by
    change ω.toDual (ω.toDual.symm ((transpose T) (ω.toDual x))) y = _
    rw [ω.toDual.apply_symm_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  apply ω.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  rw [hadj]
  rfl

/-- The symplectic adjoint is additive.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) (A B : X →L[ℝ] X) :
    ω.adjoint (A + B) = ω.adjoint A + ω.adjoint B := by
  have hadj (T : X →L[ℝ] X) (x y : X) :
      ω.toDual (ω.adjoint T x) y = ω.toDual x (T y) := by
    change ω.toDual (ω.toDual.symm ((transpose T) (ω.toDual x))) y = _
    rw [ω.toDual.apply_symm_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  apply ω.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  rw [hadj]
  simp only [add_apply, map_add, hadj]

/-- The symplectic adjoint commutes with real scalar multiplication.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) (a : ℝ) (A : X →L[ℝ] X) :
    ω.adjoint (a • A) = a • ω.adjoint A := by
  have hadj (T : X →L[ℝ] X) (x y : X) :
      ω.toDual (ω.adjoint T x) y = ω.toDual x (T y) := by
    change ω.toDual (ω.toDual.symm ((transpose T) (ω.toDual x))) y = _
    rw [ω.toDual.apply_symm_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  apply ω.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  rw [hadj]
  simp only [smul_apply, map_smul, hadj]

/-- The symplectic adjoint reverses composition.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) (A B : X →L[ℝ] X) :
    ω.adjoint (A * B) = ω.adjoint B * ω.adjoint A := by
  have hadj (T : X →L[ℝ] X) (x y : X) :
      ω.toDual (ω.adjoint T x) y = ω.toDual x (T y) := by
    change ω.toDual (ω.toDual.symm ((transpose T) (ω.toDual x))) y = _
    rw [ω.toDual.apply_symm_apply]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  apply ω.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  rw [hadj]
  change ω.toDual x ((A.comp B) y) = ω.toDual (ω.adjoint B (ω.adjoint A x)) y
  rw [hadj, hadj]
  rfl

/-- Taking the symplectic adjoint twice returns the original operator.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_involutive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) (A : X →L[ℝ] X) :
    ω.adjoint (ω.adjoint A) = A := by
  have hadj (T : X →L[ℝ] X) (x y : X) :
      ω.toDual (ω.adjoint T x) y = ω.toDual x (T y) := by
    change ω.toDual (ω.toDual.symm ((transpose T) (ω.toDual x))) y = _
    rw [ω.toDual.apply_symm_apply]
    rfl
  have hskew (x y : X) : ω.toDual x y = -ω.toDual y x := by
    have h := ω.alternating (x + y)
    simp only [map_add, add_apply, ω.alternating, add_zero, zero_add] at h
    linarith
  apply ContinuousLinearMap.ext
  intro x
  apply ω.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  calc
    ω.toDual (ω.adjoint (ω.adjoint A) x) y =
        ω.toDual x (ω.adjoint A y) := hadj _ _ _
    _ = -ω.toDual (ω.adjoint A y) x := hskew _ _
    _ = -ω.toDual y (A x) := congrArg Neg.neg (hadj _ _ _)
    _ = ω.toDual (A x) y := (hskew _ _).symm

/-- Evaluation identity characterizing the symplectic adjoint.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (ω : StrongSymplecticForm X) (A : X →L[ℝ] X) (x y : X) :
    ω.toDual (ω.adjoint A x) y = ω.toDual x (A y) := by
  change ω.toDual (ω.toDual.symm ((transpose A) (ω.toDual x))) y = _
  rw [ω.toDual.apply_symm_apply]
  rfl

end

end KaltonPeck.Support.Forms

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
