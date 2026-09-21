/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.Exponential
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.VectorAngle

/-!
# Proposition 3.5, the eigenvector clause: `∠(x, U x) = θ`

Davis--Kahan's Proposition 3.5 makes six printed assertions.  Four are the
commutations of `Θ` with `P`, `Q`, `J` and `U`; one is the maximal-subspace
characterization of the eigenspace `Ω({θ})H` in the acute case; and the sixth,
proved here, is

> for every eigenvalue `θ`, the eigenvectors `x` satisfy `∠(x, U x) = θ`.

The angle is the paper's **(1.14)**, the vector angle
`arccos (Re ⟪y, x⟫ / (‖x‖ ‖y‖))`, and *not* its (1.15) line angle, which divides
by the modulus instead.  `TauCeti.vectorAngle` is (1.14) and
`TauCeti.vectorAngle_eq_angle_rclikeToReal` identifies it with Mathlib's
`InnerProductGeometry.angle`, so the two normalizations are the same one.

## The calculation

On an angle eigenvector everything is scalar.  `Θ = arcsin (sin Θ)` and
`cos Θ = cos (arcsin (sin Θ))` are both functional calculi of the *same* operator
`sin Θ`, so `TauCeti.selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul`
transfers the eigenvector of `Θ` to each of them without naming an eigenbasis:

* `sinAngleOperator_apply_of_angleOperator_apply` — `sin Θ x = (sin θ) x`;
* `directRotationCosine_apply_of_angleOperator_apply` — `cos Θ x = (cos θ) x`.

Then `U = cos Θ + J sin Θ` (`directRotation_eq_cos_add_J_sin`) gives
`U x = (cos θ) x + (sin θ) J x`, and `J` contributes nothing to the real part
because it is skew-adjoint (`adjoint_angleComplexStructure`).  So
`Re ⟪U x, x⟫ = cos θ ‖x‖²`, while `‖U x‖ = ‖x‖` because `U` is unitary, and the
angle is `arccos (cos θ) = θ`.

`J² = -1` is **not** used, and is in fact false globally: `J` vanishes on the
zero-angle kernel, and the correct identity is `J² = -(sin Θ)(sin Θ)⁺`
(`angleComplexStructure_comp_self`).  Skew-adjointness, unlike that identity,
holds on the whole space, which is why the real part vanishes at every `x`.

The range constraint `θ ∈ [0, π/2]` is not assumed.  It is derived: an eigenvalue
of `arcsin (sin Θ)` on a nonzero vector really is an arcsine
(`TauCeti.exists_eigenvalue_of_calculus_apply_eq_smul`), hence lies in
`[-π/2, π/2]`, and positivity of `sin Θ` removes the negative half.  This matters
because `arccos (cos θ) = θ` is false outside `[0, π]`.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

variable (U V : Submodule 𝕜 E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **`J` is skew-adjoint**: `J⋆ = -J`.

`J = (U - cos Θ)(sin Θ)⁺`.  The left factor is the skew part of a unitary, so its
adjoint is `U⁻¹ - cos Θ = -(U - cos Θ)` by `U + U⁻¹ = 2 cos Θ`; the right factor
is self-adjoint because `sin Θ` is, and the two commute.

This holds on the whole space, including the zero-angle kernel where `J` is zero
by convention.  It is the property Proposition 3.5's eigenvector clause needs;
the complex-structure identity `J² = -(sin Θ)(sin Θ)⁺` is the one that does *not*
extend to the kernel. -/
theorem adjoint_angleComplexStructure (hacute : IsAcute U V) :
    LinearMap.adjoint (angleComplexStructure U V hacute) =
      -angleComplexStructure U V hacute := by
  have hsym : (sinAngleOperator U V).IsSymmetric := isSymmetric_sinAngleOperator U V
  have hCsym : (directRotationCosine U V).IsSymmetric :=
    (TauCeti.isPositive_operatorAbs (canonicalIntertwiner U V)).isSymmetric
  have hAD : ((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
      sinAngleOperator U V =
      sinAngleOperator U V ∘ₗ
        ((directRotation U V hacute).toLinearMap - directRotationCosine U V) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub,
      directRotation_comm_sinAngleOperator U V hacute,
      directRotationCosine_comm_sinAngleOperator U V]
  have hGD : ((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
      TauCeti.moorePenroseInverse (sinAngleOperator U V) =
      TauCeti.moorePenroseInverse (sinAngleOperator U V) ∘ₗ
        ((directRotation U V hacute).toLinearMap - directRotationCosine U V) :=
    TauCeti.moorePenroseInverse_comm_of_isSymmetric hsym hAD
  have hsum : (directRotation U V hacute).toLinearMap +
      (directRotation U V hacute).symm.toLinearMap =
      (2 : 𝕜) • directRotationCosine U V := by
    rw [directRotationCosine_eq_half_smul_add U V hacute, smul_smul,
      mul_inv_cancel₀ (two_ne_zero : (2 : 𝕜) ≠ 0), one_smul]
  have hSC : (directRotation U V hacute).symm.toLinearMap - directRotationCosine U V =
      -((directRotation U V hacute).toLinearMap - directRotationCosine U V) := by
    have h2 : (directRotation U V hacute).symm.toLinearMap =
        (2 : 𝕜) • directRotationCosine U V -
          (directRotation U V hacute).toLinearMap := by
      rw [← hsum]; abel
    rw [h2, two_smul]; abel
  have hDadj : LinearMap.adjoint
      ((directRotation U V hacute).toLinearMap - directRotationCosine U V) =
      -((directRotation U V hacute).toLinearMap - directRotationCosine U V) := by
    rw [map_sub, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, hCsym.adjoint_eq, hSC]
  have hGadj : LinearMap.adjoint (TauCeti.moorePenroseInverse (sinAngleOperator U V)) =
      TauCeti.moorePenroseInverse (sinAngleOperator U V) :=
    TauCeti.adjoint_moorePenroseInverse_of_isSymmetric hsym
  show LinearMap.adjoint
      (((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
        TauCeti.moorePenroseInverse (sinAngleOperator U V)) =
      -(((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
        TauCeti.moorePenroseInverse (sinAngleOperator U V))
  rw [LinearMap.adjoint_comp, hGadj, hDadj, LinearMap.comp_neg, ← hGD]

/-- **`J` has vanishing real quadratic form**: `Re ⟪J x, x⟫ = 0` for every `x`.

Immediate from skew-adjointness: `⟪J x, x⟫ = -⟪x, J x⟫` and the two inner
products have the same real part. -/
theorem re_inner_angleComplexStructure_apply_self (hacute : IsAcute U V) (x : E) :
    RCLike.re (inner 𝕜 (angleComplexStructure U V hacute x) x) = 0 := by
  have h1 : inner 𝕜 x (LinearMap.adjoint (angleComplexStructure U V hacute) x) =
      inner 𝕜 (angleComplexStructure U V hacute x) x :=
    LinearMap.adjoint_inner_right _ _ _
  rw [adjoint_angleComplexStructure U V hacute, LinearMap.neg_apply,
    inner_neg_right] at h1
  have h2 : RCLike.re (inner 𝕜 x (angleComplexStructure U V hacute x)) =
      RCLike.re (inner 𝕜 (angleComplexStructure U V hacute x) x) :=
    inner_re_symm (𝕜 := 𝕜) _ _
  have h3 := congrArg (RCLike.re (K := 𝕜)) h1
  rw [map_neg] at h3
  linarith

/-- **`sin Θ` acts on an angle eigenvector by `sin θ`.**

`Θ` and `sin Θ` are two symbols — `arcsin` and the identity — of the *same*
operator `sin Θ`, and `sin (arcsin s) = s` on the spectrum, which lies in
`[-1, 1]` by `sinAngleOperator_eigenvalues_mem_Icc`. -/
theorem sinAngleOperator_apply_of_angleOperator_apply {x : E} {θ : ℝ}
    (hx : angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    sinAngleOperator U V x = ((Real.sin θ : ℝ) : 𝕜) • x := by
  have hsym : (sinAngleOperator U V).IsSymmetric := isSymmetric_sinAngleOperator U V
  have hcalc : TauCeti.selfAdjointFunctionalCalculus hsym Real.arcsin x =
      ((θ : ℝ) : 𝕜) • x := by
    rw [← angleOperator_eq_calculus U V hsym]; exact hx
  have h := TauCeti.selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul
    hsym Real.arcsin id hcalc (fun i hi => by
      have hmem := sinAngleOperator_eigenvalues_mem_Icc U V hsym i
      show hsym.eigenvalues rfl i = Real.sin θ
      rw [← hi, Real.sin_arcsin hmem.1 hmem.2])
  rwa [TauCeti.selfAdjointFunctionalCalculus_id hsym] at h

/-- **`cos Θ` acts on an angle eigenvector by `cos θ`.**

Same transfer, with the symbol `s ↦ cos (arcsin s)` that
`directRotationCosine_eq_calculus` identifies with the positive cosine. -/
theorem directRotationCosine_apply_of_angleOperator_apply {x : E} {θ : ℝ}
    (hx : angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    directRotationCosine U V x = ((Real.cos θ : ℝ) : 𝕜) • x := by
  have hsym : (sinAngleOperator U V).IsSymmetric := isSymmetric_sinAngleOperator U V
  have hcalc : TauCeti.selfAdjointFunctionalCalculus hsym Real.arcsin x =
      ((θ : ℝ) : 𝕜) • x := by
    rw [← angleOperator_eq_calculus U V hsym]; exact hx
  rw [directRotationCosine_eq_calculus U V hsym]
  exact TauCeti.selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul
    hsym Real.arcsin _ hcalc (fun i hi => by
      show Real.cos (Real.arcsin (hsym.eigenvalues rfl i)) = Real.cos θ
      rw [hi])

/-- **An eigenvalue of `Θ` on a nonzero vector lies in `[0, π/2]`.**

`Θ = arcsin (sin Θ)`, so the eigenvalue is a value of `arcsin` and lies in
`[-π/2, π/2]`; and `sin Θ` is positive, so `sin θ ‖x‖² ≥ 0` forces `sin θ ≥ 0`
and hence `θ = arcsin (sin θ) ≥ 0`.  Nothing here is a hypothesis on `θ`. -/
theorem angleOperator_eigenvalue_mem_Icc {x : E} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    θ ∈ Set.Icc 0 (Real.pi / 2) := by
  have hsym : (sinAngleOperator U V).IsSymmetric := isSymmetric_sinAngleOperator U V
  have hcalc : TauCeti.selfAdjointFunctionalCalculus hsym Real.arcsin x =
      ((θ : ℝ) : 𝕜) • x := by
    rw [← angleOperator_eq_calculus U V hsym]; exact hx
  obtain ⟨i, hi⟩ :=
    TauCeti.exists_eigenvalue_of_calculus_apply_eq_smul hsym Real.arcsin hx0 hcalc
  have hIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := hi ▸ Real.arcsin_mem_Icc _
  have hpos : (sinAngleOperator U V).IsPositive :=
    TauCeti.isPositive_operatorAbs (projection U - projection V)
  have hnn := hpos.re_inner_nonneg_left x
  rw [sinAngleOperator_apply_of_angleOperator_apply U V hx, inner_smul_left,
    RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at hnn
  have hxnorm : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hsq : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hsin0 : 0 ≤ Real.sin θ :=
    le_of_mul_le_mul_right (by simpa using hnn) hsq
  refine ⟨?_, hIcc.2⟩
  rw [← Real.arcsin_sin hIcc.1 hIcc.2]
  exact Real.arcsin_nonneg.mpr hsin0

/-- **Davis--Kahan Proposition 3.5, eigenvector clause.**

If the angle operator `Θ` scales `x ≠ 0` by `θ`, the direct rotation moves `x`
through exactly the angle `θ`:

```text
∠(x, U x) = θ.
```

The angle is the paper's (1.14) vector angle, which
`TauCeti.vectorAngle_eq_angle_rclikeToReal` identifies with Mathlib's
`InnerProductGeometry.angle`; it is *not* the (1.15) angle between the lines
`[x]` and `[U x]`, which uses the modulus of the inner product and would give a
different number.

`IsAcute` is not an extra hypothesis on the clause: it is the hypothesis under
which the paper's direct rotation exists and is unique (Proposition 3.1), so it
is what makes `U` a well-defined object here at all. -/
theorem vectorAngle_directRotation_eq_of_angleOperator_apply (hacute : IsAcute U V)
    {x : E} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (directRotation U V hacute x) = θ := by
  have hIcc := angleOperator_eigenvalue_mem_Icc U V hx0 hx
  have hRx : directRotation U V hacute x =
      ((Real.cos θ : ℝ) : 𝕜) • x +
        ((Real.sin θ : ℝ) : 𝕜) • angleComplexStructure U V hacute x := by
    have h := LinearMap.congr_fun (directRotation_eq_cos_add_J_sin U V hacute) x
    rw [LinearMap.add_apply, LinearMap.comp_apply,
      directRotationCosine_apply_of_angleOperator_apply U V hx,
      sinAngleOperator_apply_of_angleOperator_apply U V hx, map_smul] at h
    exact h
  have hinner : RCLike.re (inner 𝕜 (directRotation U V hacute x) x) =
      Real.cos θ * ‖x‖ ^ 2 := by
    rw [hRx, inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_ofReal,
      RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq,
      re_inner_angleComplexStructure_apply_self U V hacute x, mul_zero, add_zero]
  refine TauCeti.vectorAngle_eq_of_re_inner_eq hx0
    ((directRotation U V hacute).norm_map x) hIcc.1 ?_ hinner
  have := Real.pi_pos
  linarith [hIcc.2]

end DavisKahan.FiniteDimensional
end TauCeti
