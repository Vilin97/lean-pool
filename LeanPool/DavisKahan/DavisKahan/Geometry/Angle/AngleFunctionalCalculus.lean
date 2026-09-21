/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus

/-!
# The literal operator angle of Davis--Kahan

The accepted sine theorem uses the positive sine operator directly.  The 1970
paper first defines a Hermitian operator angle and then applies scalar
trigonometric functions to it.  This file restores that literal object without
changing the already verified theorem.

For complex Hilbert spaces the canonical angle is
`arcsin |P_U - P_V|` through continuous functional calculus.  Its spectrum is
contained in `[0, pi / 2]`, and applying sine recovers exactly the accepted
sine operator.  For real Hilbert spaces the literal angle is the same object
on the canonical complexification; this is the construction used elsewhere in
the repository for real operator functional calculus.
-/

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The symmetric sine operator is a positive contraction. -/
theorem norm_sinAngleOperatorC_le_one (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorC U V‖ ≤ 1 := by
  rw [norm_sinAngleOperatorC]
  show ‖(U.starProjection - V.starProjection : E →L[ℂ] E)‖ ≤ 1
  rw [Submodule.norm_starProjection_sub_eq_max]
  apply max_le
  · calc
      ‖(1 - V.starProjection) ∘L U.starProjection‖
          ≤ ‖1 - V.starProjection‖ * ‖U.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - V.starProjection : E →L[ℂ] E) = Vᗮ.starProjection from
          (Submodule.starProjection_orthogonal' V).symm]
        exact mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  · calc
      ‖(1 - U.starProjection) ∘L V.starProjection‖
          ≤ ‖1 - U.starProjection‖ * ‖V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - U.starProjection : E →L[ℂ] E) = Uᗮ.starProjection from
          (Submodule.starProjection_orthogonal' U).symm]
        exact mul_le_mul Uᗮ.starProjection_norm_le V.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring

/-- The real spectrum of the positive sine operator lies in `[0,1]`. -/
theorem spectrum_sinAngleOperatorC_subset_Icc (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (sinAngleOperatorC U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg (sinAngleOperatorC_nonneg U V) hx, ?_⟩
  have habs : |x| ≤ ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hx
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  refine le_trans (le_abs_self x) (habs.trans ?_)
  calc ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ ≤ 1 * 1 :=
        mul_le_mul (norm_sinAngleOperatorC_le_one U V) hone (norm_nonneg _)
          zero_le_one
    _ = 1 := by ring

/-- The literal Hermitian operator angle between two closed complex subspaces. -/
noncomputable def angleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.arcsin (sinAngleOperatorC U V)

/-- The literal operator angle is self-adjoint. -/
theorem isSelfAdjoint_angleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (angleOperatorC U V) := by
  exact cfc_predicate Real.arcsin (sinAngleOperatorC U V)

/-- The literal operator angle is nonnegative. -/
theorem angleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ angleOperatorC U V := by
  apply cfc_nonneg
  intro x hx
  exact Real.arcsin_nonneg.mpr
    ((spectrum_sinAngleOperatorC_subset_Icc U V hx).1)

/-- Applying sine by functional calculus recovers the accepted sine operator
exactly, not merely an operator with the same norm. -/
theorem cfc_sin_angleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (angleOperatorC U V) = sinAngleOperatorC U V := by
  have hsa : IsSelfAdjoint (sinAngleOperatorC U V) :=
    isSelfAdjoint_sinAngleOperatorC U V
  have harcsin : ContinuousOn Real.arcsin
      (spectrum ℝ (sinAngleOperatorC U V)) :=
    Real.continuous_arcsin.continuousOn
  have hsin : ContinuousOn Real.sin
      (Real.arcsin '' spectrum ℝ (sinAngleOperatorC U V)) :=
    Real.continuous_sin.continuousOn
  rw [angleOperatorC,
    ← cfc_comp Real.sin Real.arcsin (sinAngleOperatorC U V)
      hsa hsin harcsin]
  calc
    cfc (Real.sin ∘ Real.arcsin) (sinAngleOperatorC U V)
        = cfc (fun x : ℝ => x) (sinAngleOperatorC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_sinAngleOperatorC_subset_Icc U V hx
      exact Real.sin_arcsin (by linarith [hxi.1]) (by linarith [hxi.2])
    _ = sinAngleOperatorC U V := cfc_id' ℝ _

/-- The ambient `cos Θ`, obtained by applying `cos` to the Hermitian operator
angle.  Unlike the directed `directedCosAngleOperatorC`, which is the modulus of
`P_V P_U`, this carries every principal angle of the pair. -/
noncomputable def cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.cos (angleOperatorC U V)

/-- The literal angle has spectrum in the canonical interval. -/
theorem spectrum_angleOperatorC_subset_Icc (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (angleOperatorC U V) ⊆ Set.Icc 0 (Real.pi / 2) := by
  intro y hy
  rw [angleOperatorC,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := sinAngleOperatorC U V) (isSelfAdjoint_sinAngleOperatorC U V)
      Real.continuous_arcsin.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_sinAngleOperatorC_subset_Icc U V hx
  exact ⟨Real.arcsin_nonneg.mpr hxi.1,
    Real.arcsin_le_pi_div_two x⟩

/-- Functional-calculus Pythagoras for the literal angle. -/
theorem sinAngleOperatorC_sq_add_cosAngleOperatorC_sq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperatorC U V * sinAngleOperatorC U V +
      cosAngleOperatorC U V * cosAngleOperatorC U V =
        ContinuousLinearMap.id ℂ E := by
  rw [← cfc_sin_angleOperatorC, cosAngleOperatorC,
    ← cfc_mul Real.sin Real.sin (angleOperatorC U V)
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn,
    ← cfc_mul Real.cos Real.cos (angleOperatorC U V)
      Real.continuous_cos.continuousOn Real.continuous_cos.continuousOn,
    ← cfc_add (a := angleOperatorC U V)
      (fun x : ℝ => Real.sin x * Real.sin x)
      (fun x : ℝ => Real.cos x * Real.cos x)
      ((Real.continuous_sin.mul Real.continuous_sin).continuousOn)
      ((Real.continuous_cos.mul Real.continuous_cos).continuousOn)]
  calc
    cfc (fun x : ℝ => Real.sin x * Real.sin x +
        Real.cos x * Real.cos x) (angleOperatorC U V)
        = cfc (fun _ : ℝ => 1) (angleOperatorC U V) := by
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    _ = ContinuousLinearMap.id ℂ E := by
      have ha : IsSelfAdjoint (angleOperatorC U V) :=
        isSelfAdjoint_angleOperatorC U V
      exact cfc_const_one ℝ _

/-! ### Proposition 3.5's projection commutations, at bounded infinite dimension

`Θ` commutes with `P` and with `Q`.  The finite-dimensional `RCLike` forms of
these are `TauCeti.DavisKahan.FiniteDimensional.angleOperator_comm_projection` and its right
companion; the two below are the same assertions for the bounded complex angle
`angleOperatorC`, where the dimension is arbitrary.

Both reduce to one two-idempotent identity.  `sin Θ = |P_U - P_V|` is the
functional-calculus square root of the Gram operator
`(P_U - P_V)⋆(P_U - P_V) = (P_U - P_V)²`, and for idempotent `p`, `q`,

```text
(p - q)² p  =  p - p q p  =  p (p - q)²,
```

with the mirror identity for `q`.  Commutation then passes to the square root
and to `Θ = arcsin (sin Θ)` by `Commute.cfcₙ_nnreal` and `Commute.cfc_real`; no
acuteness, finite dimension, or spectral hypothesis is used. -/

/-- The projector difference is self-adjoint, so its Gram operator is its
square. -/
theorem adjoint_starProjection_sub (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.starProjection - V.starProjection : E →L[ℂ] E).adjoint =
      U.starProjection - V.starProjection := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact ((isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)).star_eq

/-- **`sin Θ` commutes with `P`.**  See the section note: the content is
`(p - q)² p = p (p - q)²` for idempotents. -/
theorem commute_sinAngleOperatorC_starProjection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (sinAngleOperatorC U V) U.starProjection := by
  have hgram : Commute
      ((U.starProjection - V.starProjection : E →L[ℂ] E).adjoint ∘L
        (U.starProjection - V.starProjection)) U.starProjection := by
    rw [adjoint_starProjection_sub U V]
    set p : E →L[ℂ] E := U.starProjection with hpdef
    set q : E →L[ℂ] E := V.starProjection with hqdef
    have hp : p * p = p := U.isIdempotentElem_starProjection
    have hq : q * q = q := V.isIdempotentElem_starProjection
    show (p - q) * (p - q) * p = p * ((p - q) * (p - q))
    have key : (p - q) * (p - q) * p - p * ((p - q) * (p - q)) =
        ((p * p - p) * q - q * (p * p - p)) + ((q * q - q) * p - p * (q * q - q)) := by
      noncomm_ring
    rw [hp, hq] at key
    simp only [sub_self, zero_mul, mul_zero, add_zero] at key
    exact sub_eq_zero.mp key
  rw [sinAngleOperatorC, ContinuousLinearMap.modulus_def]
  exact Commute.cfcₙ_nnreal hgram _

/-- **`sin Θ` commutes with `Q`.**  The mirror of
`commute_sinAngleOperatorC_starProjection`. -/
theorem commute_sinAngleOperatorC_starProjection_right (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (sinAngleOperatorC U V) V.starProjection := by
  have hgram : Commute
      ((U.starProjection - V.starProjection : E →L[ℂ] E).adjoint ∘L
        (U.starProjection - V.starProjection)) V.starProjection := by
    rw [adjoint_starProjection_sub U V]
    set p : E →L[ℂ] E := U.starProjection with hpdef
    set q : E →L[ℂ] E := V.starProjection with hqdef
    have hp : p * p = p := U.isIdempotentElem_starProjection
    have hq : q * q = q := V.isIdempotentElem_starProjection
    show (p - q) * (p - q) * q = q * ((p - q) * (p - q))
    have key : (p - q) * (p - q) * q - q * ((p - q) * (p - q)) =
        ((p * p - p) * q - q * (p * p - p)) + ((q * q - q) * p - p * (q * q - q)) := by
      noncomm_ring
    rw [hp, hq] at key
    simp only [sub_self, zero_mul, mul_zero, add_zero] at key
    exact sub_eq_zero.mp key
  rw [sinAngleOperatorC, ContinuousLinearMap.modulus_def]
  exact Commute.cfcₙ_nnreal hgram _

/-- **Davis--Kahan Proposition 3.5: `Θ` commutes with `P`**, for the bounded
complex angle operator at arbitrary dimension. -/
theorem commute_angleOperatorC_starProjection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (angleOperatorC U V) U.starProjection := by
  rw [angleOperatorC]
  exact Commute.cfc_real (commute_sinAngleOperatorC_starProjection U V) Real.arcsin

/-- **Davis--Kahan Proposition 3.5: `Θ` commutes with `Q`**, for the bounded
complex angle operator at arbitrary dimension. -/
theorem commute_angleOperatorC_starProjection_right (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (angleOperatorC U V) V.starProjection := by
  rw [angleOperatorC]
  exact Commute.cfc_real (commute_sinAngleOperatorC_starProjection_right U V) Real.arcsin

section Real

open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahan.Angle.Real

variable {ER : Type*} [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
  [CompleteSpace ER]

/-! The real algebra structure and the real continuous functional calculus on the
complexified operator algebra are `scoped instance`s of
`RealComplexification`, opened below.  They used to be reinstalled
here as a second `local instance`, which made them a *different declaration* from the
one the imported lemmas are stated against; see lane `{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.RealComplexification

/-- The literal real operator angle, represented canonically on the
complexification. -/
noncomputable def angleOperatorRC (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification ER →L[ℂ] RealComplexification ER :=
  angleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Applying sine to the real angle recovers the complexification of the real
projection-difference sine operator. -/
theorem cfc_sin_angleOperatorRC (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (angleOperatorRC U V) = sinAngleOperatorRC U V :=
  cfc_sin_angleOperatorC _ _

/-- The real angle has the same canonical spectral interval. -/
theorem spectrum_angleOperatorRC_subset_Icc (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (angleOperatorRC U V) ⊆ Set.Icc 0 (Real.pi / 2) :=
  spectrum_angleOperatorC_subset_Icc _ _

end Real

end

end DavisKahan.Angle
end TauCeti
