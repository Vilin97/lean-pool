/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.Proposition35Infinite
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute

/-! # Proposition35Nonacute -/

@[expose] public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-!
# Nonacute operator-angle commutation for Davis--Kahan Section 3

This module extends the arbitrary-dimensional operator-angle geometry from the acute direct
rotation to an arbitrary completed direct rotation.  A chosen isometric equivalence between the
crossed defect spaces determines the completed rotation `W`.  Its skew part

`D = W - cos Θ`

has modulus `sin Θ`, so its polar partial isometry is the paper's quarter turn on the regular
part together with the chosen defect rotation.  The main point here is that the whole construction
commutes with the operator angle:

* `W` commutes with `cos Θ`, hence with `sin Θ` and `Θ`;
* `D` and `|D| = sin Θ` commute with `Θ`;
* commutation therefore passes to the polar partial isometry of `D` by the general polar
  commutation theorem in `ForTauCeti`;
* because `D` is skew-adjoint, its polar phase squares to `-1` on the polar initial space, and
  `Θ` takes values in that space, giving the global identity `J² Θ = -Θ`.

No finite-dimensionality, compactness, spectral discreteness, or acuteness assumption is used.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Proposition35

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The paper quarter turn attached to a chosen completed nonacute direct rotation.  It is the
polar partial isometry of the skew part `W - cos Θ`, hence vanishes on the zero-angle subspace. -/
noncomputable def section3NonacuteQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  (nonacuteDirectRotation U V J - section3CosAngleOperator U V).polarPartial

/-- Every completed nonacute direct rotation commutes with `cos Θ`. -/
theorem nonacuteDirectRotation_comm_cosine
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (nonacuteDirectRotation U V J) (section3CosAngleOperator U V) := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue U V]
  exact nonacuteDirectRotation_comm_absoluteValue U V J

/-- Every completed nonacute direct rotation commutes with `sin Θ`. -/
theorem nonacuteDirectRotation_comm_sine
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (nonacuteDirectRotation U V J) (section3SinAngleOperator U V) := by
  have hC := nonacuteDirectRotation_comm_cosine U V J
  have hS2 : Commute
      (section3SinAngleOperator U V * section3SinAngleOperator U V)
      (nonacuteDirectRotation U V J) := by
    have hpy := section3Sin_sq_add_cos_sq U V
    have hs : section3SinAngleOperator U V * section3SinAngleOperator U V =
        1 - section3CosAngleOperator U V * section3CosAngleOperator U V :=
      eq_sub_of_add_eq hpy
    rw [hs]
    exact (Commute.one_left _).sub_left (hC.symm.mul_left hC.symm)
  exact (TauCeti.commute_of_commute_mul_self
    (section3SinAngleOperator_nonneg U V) hS2).symm

/-- The operator angle commutes with every completed nonacute direct rotation. -/
theorem section3AngleOperator_comm_nonacuteDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (section3AngleOperator U V) (nonacuteDirectRotation U V J) := by
  rw [section3AngleOperator]
  exact Commute.cfc_real (nonacuteDirectRotation_comm_sine U V J).symm Real.arcsin

/-- The skew part of every completed nonacute direct rotation has modulus exactly `sin Θ`. -/
theorem modulus_nonacuteDirectRotation_sub_cosine
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (nonacuteDirectRotation U V J - section3CosAngleOperator U V).modulus =
      section3SinAngleOperator U V := by
  let W := nonacuteDirectRotation U V J
  let C := section3CosAngleOperator U V
  let S := section3SinAngleOperator U V
  let D := W - C
  have hunit : W ∈ unitary (H →L[𝕜] H) :=
    nonacuteDirectRotation_mem_unitary U V J
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum0 := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hsum : W + star W = C + C := by
    simpa [W, C, hCeq] using hsum0
  have hWC : Commute W C := by
    simpa [W, C] using nonacuteDirectRotation_comm_cosine U V J
  have hWC' : W * C = C * W := hWC.eq
  have hstarW : star W = C + C - W := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hsum
  have hWstarW : (C + C - W) * W = 1 := by
    rw [← hstarW]
    exact Unitary.star_mul_self_of_mem hunit
  have hpy := section3Sin_sq_add_cos_sq U V
  have hpy' : S * S + C * C = 1 := by
    simpa [S, C] using hpy
  have hCsa : star C = C :=
    (cfc_predicate Real.cos (section3AngleOperator U V)).star_eq
  have hgram : star D * D = S * S := by
    dsimp [D]
    rw [star_sub, hCsa, hstarW]
    calc
      (C + C - W - C) * (W - C) = (C + C - W) * W - C * C := by
        noncomm_ring [hWC']
      _ = 1 - C * C := by rw [hWstarW]
      _ = S * S := (eq_sub_of_add_eq hpy').symm
  have hS0 : 0 ≤ S := section3SinAngleOperator_nonneg U V
  have hmod : S = D.modulus := by
    refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq hS0 ?_
    have hgram' : S * S = star D * D := hgram.symm
    rw [ContinuousLinearMap.star_eq_adjoint] at hgram'
    simpa only [ContinuousLinearMap.mul_def] using hgram'
  exact hmod.symm

/-- The skew part of a completed nonacute direct rotation is skew-adjoint. -/
theorem star_nonacuteDirectRotation_sub_cosine
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (nonacuteDirectRotation U V J - section3CosAngleOperator U V) =
      -(nonacuteDirectRotation U V J - section3CosAngleOperator U V) := by
  let W := nonacuteDirectRotation U V J
  let C := section3CosAngleOperator U V
  have hCsa : star C = C :=
    (cfc_predicate Real.cos (section3AngleOperator U V)).star_eq
  have hsum0 := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum : W + star W = C + C := by
    simpa [W, C, hCeq] using hsum0
  have hsW : star W = C + C - W := by
    rw [← hsum]
    abel
  rw [star_sub, show star W = C + C - W from hsW, hCsa]
  abel

/-- The angle operator takes values in the polar initial space of the skew part of every completed
nonacute direct rotation.  Equivalently, the quarter turn is a genuine complex structure on every
vector reached by `Θ`, while remaining zero on the zero-angle kernel. -/
theorem section3AngleOperator_apply_mem_nonacuteSkewPolarInitial
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    section3AngleOperator U V x ∈
      (nonacuteDirectRotation U V J - section3CosAngleOperator U V).polarInitial := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hmod := modulus_nonacuteDirectRotation_sub_cosine U V J
  have hkerDsin : LinearMap.ker D.toLinearMap =
      LinearMap.ker (section3SinAngleOperator U V).toLinearMap := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have hz := D.modulus_apply_eq_zero_iff z
    simpa [D, hmod] using hz.symm
  have hkerDtheta : LinearMap.ker D.toLinearMap =
      LinearMap.ker (section3AngleOperator U V).toLinearMap :=
    hkerDsin.trans (ker_section3AngleOperator_eq_ker_sine U V).symm
  rw [D.polarInitial_eq_orthogonal_ker, hkerDtheta]
  have hself : (section3AngleOperator U V).adjoint = section3AngleOperator U V :=
    (section3AngleOperator_isSelfAdjoint U V).adjoint_eq
  have horth : (section3AngleOperator U V).rangeᗮ =
      (section3AngleOperator U V).ker := by
    rw [(section3AngleOperator U V).orthogonal_range, hself]
  have horthEq : (section3AngleOperator U V).kerᗮ =
      (section3AngleOperator U V).range.topologicalClosure := by
    calc
      (section3AngleOperator U V).kerᗮ =
          (section3AngleOperator U V).rangeᗮᗮ := by rw [horth]
      _ = (section3AngleOperator U V).range.topologicalClosure :=
        Submodule.orthogonal_orthogonal_eq_closure _
  rw [horthEq]
  exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- On the support of the angle, the nonacute quarter turn squares to `-1`.  Globally this is the
operator identity `J² Θ = -Θ`, the form needed for the dimension-free exponential calculation. -/
theorem section3NonacuteQuarterTurn_sq_comp_angleOperator
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    section3NonacuteQuarterTurn U V J ∘L section3NonacuteQuarterTurn U V J ∘L
        section3AngleOperator U V =
      -section3AngleOperator U V := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hskewStar := star_nonacuteDirectRotation_sub_cosine U V J
  have hskew : D.adjoint = -D := by
    simpa [D, ContinuousLinearMap.star_eq_adjoint] using hskewStar
  ext x
  have hx := section3AngleOperator_apply_mem_nonacuteSkewPolarInitial U V J x
  have hquarter :=
    ContinuousLinearMap.polarPartial_apply_polarPartial_apply_of_mem_of_adjoint_eq_neg
      (M := D) hskew hx
  simpa [D, section3NonacuteQuarterTurn, ContinuousLinearMap.comp_apply] using hquarter

/-- The full nonacute polar resolution `W = cos Θ + J sin Θ`. -/
theorem nonacuteDirectRotation_eq_cos_add_quarterTurn_sin
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      section3CosAngleOperator U V +
        section3NonacuteQuarterTurn U V J ∘L section3SinAngleOperator U V := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hmod := modulus_nonacuteDirectRotation_sub_cosine U V J
  have hpolar := D.polarPartial_comp_modulus
  have hD : section3NonacuteQuarterTurn U V J ∘L section3SinAngleOperator U V = D := by
    rw [section3NonacuteQuarterTurn, ← hmod]
    exact hpolar
  rw [hD]
  dsimp [D]
  abel

/-- The operator angle commutes with the quarter turn of every completed
nonacute direct rotation. -/
theorem section3AngleOperator_comm_nonacuteQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (section3AngleOperator U V) (section3NonacuteQuarterTurn U V J) := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hθW := section3AngleOperator_comm_nonacuteDirectRotation U V J
  have hθC : Commute (section3AngleOperator U V) (section3CosAngleOperator U V) := by
    rw [section3CosAngleOperator]
    exact (Commute.cfc_real (Commute.refl (section3AngleOperator U V)) Real.cos).symm
  have hθD : Commute (section3AngleOperator U V) D :=
    hθW.sub_right hθC
  have hmod := modulus_nonacuteDirectRotation_sub_cosine U V J
  have hθmod : Commute (section3AngleOperator U V) D.modulus := by
    rw [hmod]
    rw [section3AngleOperator]
    exact Commute.cfc_real (Commute.refl (section3SinAngleOperator U V)) Real.arcsin
  have h := ContinuousLinearMap.commute_polarPartial_of_commute hθD hθmod
  simpa [D, section3NonacuteQuarterTurn] using h

/-! ## The eigenvector clause at the completed nonacute scope

Davis and Kahan restrict only the *third* clause of Proposition 3.5 to the acute case.  The
statement that an angle eigenvector is rotated through exactly its eigenvalue is made under the
standing Section 3 hypotheses, which admit the completed direct rotation selected by a
crossed-defect isometry.  These two theorems supply it at that scope. -/

/-- The skew part of a completed nonacute direct rotation has vanishing real quadratic form.

This is the nonacute twin of `re_inner_section3DirectRotation_sub_cosine_apply_self`, and it is
where skew-adjointness of `W - cos Θ` (`star_nonacuteDirectRotation_sub_cosine`) enters: a
skew-adjoint operator has purely imaginary quadratic form, so its real part vanishes. -/
theorem re_inner_nonacuteDirectRotation_sub_cosine_apply_self
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    RCLike.re ⟪(nonacuteDirectRotation U V J - section3CosAngleOperator U V) x, x⟫_𝕜 = 0 := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hstar : star D = -D := star_nonacuteDirectRotation_sub_cosine U V J
  have h1 : ⟪D x, x⟫_𝕜 = ⟪x, star D x⟫_𝕜 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_right D x x).symm
  rw [hstar, neg_apply, inner_neg_right] at h1
  have hre := congrArg RCLike.re h1
  have hsym : RCLike.re ⟪x, D x⟫_𝕜 = RCLike.re ⟪D x, x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) x (D x)
  rw [map_neg, hsym] at hre
  linarith

/-- **Davis--Kahan 1970, Proposition 3.5, eigenvector clause, at the completed nonacute
scope.**

If `Θ x = θ x` with `x ≠ 0`, then the vector angle from `x` to `W x` is exactly `θ`, for
**every** completed direct rotation `W = nonacuteDirectRotation U V J`.  No acuteness, no
finite dimensionality, no restriction to `θ < π/2`, and no weakening to an inequality.

The right-angle endpoint `θ = π/2` needs no separate argument, and it is worth saying why,
since that is the case acuteness exists to exclude.  Every genuine angle eigenvalue lies in
`[0, π/2]` (`section3AngleOperator_eigenvalue_mem_Icc`), and the proof only ever uses
`re ⟪W x, x⟫ = cos θ ‖x‖²` together with `‖W x‖ = ‖x‖`.  At `θ = π/2` that reads
`re ⟪W x, x⟫ = 0`, which is exactly what the completed rotation does on the crossed defect
spaces: it carries `x` to a vector orthogonal to it, and `arccos 0 = π/2`.  The clause is
therefore uniform in `θ`, and the crossed-defect isometry `J` enters only through the
unitarity of `W` and the skew-adjointness of `W - cos Θ`. -/
theorem vectorAngle_nonacuteDirectRotation_eq_of_angleOperator_apply
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (nonacuteDirectRotation U V J x) = θ := by
  have hIcc := section3AngleOperator_eigenvalue_mem_Icc U V hx0 hx
  have hCx := section3CosAngleOperator_apply_of_angleOperator_apply U V hx0 hx
  have hWx : nonacuteDirectRotation U V J x =
      ((Real.cos θ : ℝ) : 𝕜) • x +
        (nonacuteDirectRotation U V J - section3CosAngleOperator U V) x := by
    rw [sub_apply, hCx]
    abel
  have hinner : RCLike.re ⟪nonacuteDirectRotation U V J x, x⟫_𝕜 =
      Real.cos θ * ‖x‖ ^ 2 := by
    rw [hWx, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
      re_inner_nonacuteDirectRotation_sub_cosine_apply_self U V J x, add_zero]
  refine TauCeti.vectorAngle_eq_of_re_inner_eq hx0
    (ContinuousLinearMap.norm_map_of_mem_unitary
      (nonacuteDirectRotation_mem_unitary U V J) x) hIcc.1 ?_ hinner
  linarith [hIcc.2, Real.pi_pos]

end

end Proposition35
end DavisKahan
end TauCeti
