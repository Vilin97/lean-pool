/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationAcute
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.FixedCosineSubspace
-- supplies the fixed-cosine eigenspace this file identifies with `Ω({θ})H`, together
-- with the `halmosCosineSq` commutation lemmas underneath it.
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
-- supplies `TauCeti.IsAcute` and `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, which this
-- file used to receive indirectly through the former `DavisKahan.Section3`.
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.VectorAngle
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PositiveSqrt
import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.PositiveSquareRootCommute
import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Proposition35Infinite -/

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Proposition 3.5 in arbitrary Hilbert dimension

This module gives the bounded infinite-dimensional operator-angle geometry used
in Proposition 3.5 of Davis--Kahan (1970), over either real or complex Hilbert
spaces.  The finite-dimensional development constructs the quarter turn by a
Moore--Penrose inverse.  Here the paper's construction is recovered directly:
if `W` is the acute direct rotation, `C` its positive cosine and `S = sin Θ`,
then the skew part `D = W - C` has modulus `S`; the quarter turn is the polar
partial isometry of `D`.  Thus it vanishes on `ker Θ`, exactly as in the paper,
and `W = C + J S`.

No compactness or pure-point-spectrum hypothesis is used.  Eigenvectors enter
only in the two clauses of Proposition 3.5 that are themselves conditional on
an eigenvalue.
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

/-- The positive ambient sine `sin Θ = |P_U-P_V|`. -/
noncomputable def section3SinAngleOperator : H →L[𝕜] H :=
  (U.starProjection - V.starProjection).modulus

/-- The literal bounded operator angle `Θ = arcsin |P_U-P_V|`. -/
noncomputable def section3AngleOperator : H →L[𝕜] H :=
  cfc Real.arcsin (section3SinAngleOperator U V)

/-- The positive cosine `cos Θ`, defined from the literal angle. -/
noncomputable def section3CosAngleOperator : H →L[𝕜] H :=
  cfc Real.cos (section3AngleOperator U V)

/-- The direct rotation at the paper's acute hypothesis. -/
noncomputable def section3DirectRotation : H →L[𝕜] H :=
  spectraCanonicalPolarFactor U V

/-- The paper's quarter turn `J`.  It is the polar partial isometry in the
resolution `W - cos Θ = J sin Θ`, hence is zero on the zero-angle space. -/
noncomputable def section3QuarterTurn : H →L[𝕜] H :=
  (section3DirectRotation U V - section3CosAngleOperator U V).polarPartial

/-- The eigenspace `Ω({θ}) H` of the bounded operator angle. -/
noncomputable def section3AngleEigenspace (θ : ℝ) : Submodule 𝕜 H :=
  Module.End.eigenspace (section3AngleOperator U V).toLinearMap ((θ : ℝ) : 𝕜)

/-! ## The sine and the literal angle -/

/-- The sine operator is positive. -/
theorem section3SinAngleOperator_nonneg :
    0 ≤ section3SinAngleOperator U V :=
  (U.starProjection - V.starProjection).modulus_nonneg

/-- The sine operator is self-adjoint. -/
theorem section3SinAngleOperator_isSelfAdjoint :
    IsSelfAdjoint (section3SinAngleOperator U V) :=
  (U.starProjection - V.starProjection).modulus_isSelfAdjoint

/-- The sine operator is a contraction. -/
theorem norm_section3SinAngleOperator_le_one :
    ‖section3SinAngleOperator U V‖ ≤ 1 := by
  rw [section3SinAngleOperator, ContinuousLinearMap.norm_modulus]
  rw [Submodule.norm_starProjection_sub_eq_max]
  apply max_le
  · calc
      ‖(1 - V.starProjection) ∘L U.starProjection‖
          ≤ ‖1 - V.starProjection‖ * ‖U.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - V.starProjection : H →L[𝕜] H) = Vᗮ.starProjection from
          (Submodule.starProjection_orthogonal' V).symm]
        exact mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  · calc
      ‖(1 - U.starProjection) ∘L V.starProjection‖
          ≤ ‖1 - U.starProjection‖ * ‖V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - U.starProjection : H →L[𝕜] H) = Uᗮ.starProjection from
          (Submodule.starProjection_orthogonal' U).symm]
        exact mul_le_mul Uᗮ.starProjection_norm_le V.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring

/-- The positive sine operator is bounded above by the identity. -/
theorem section3SinAngleOperator_le_one :
    section3SinAngleOperator U V ≤ (1 : H →L[𝕜] H) := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  have hsa : IsSelfAdjoint
      ((1 : H →L[𝕜] H) - section3SinAngleOperator U V) :=
    (IsSelfAdjoint.one _).sub (section3SinAngleOperator_isSelfAdjoint U V)
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply, inner_sub_left,
    one_apply_eq_self, map_sub, inner_self_eq_norm_sq]
  have hSx : ‖section3SinAngleOperator U V x‖ ≤ ‖x‖ := by
    calc
      ‖section3SinAngleOperator U V x‖
          ≤ ‖section3SinAngleOperator U V‖ * ‖x‖ :=
        (section3SinAngleOperator U V).le_opNorm x
      _ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_section3SinAngleOperator_le_one U V) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hinner :
      RCLike.re ⟪section3SinAngleOperator U V x, x⟫_𝕜 ≤ ‖x‖ ^ 2 := by
    calc
      RCLike.re ⟪section3SinAngleOperator U V x, x⟫_𝕜
          ≤ ‖⟪section3SinAngleOperator U V x, x⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖section3SinAngleOperator U V x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right hSx (norm_nonneg x)
      _ = ‖x‖ ^ 2 := by ring
  linarith

/-- The real spectrum of `sin Θ` lies in `[0,1]`. -/
theorem spectrum_section3SinAngleOperator_subset_Icc :
    spectrum ℝ (section3SinAngleOperator U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg (section3SinAngleOperator_nonneg U V) hx, ?_⟩
  have hle :
      section3SinAngleOperator U V ≤
        algebraMap ℝ (H →L[𝕜] H) (1 : ℝ) := by
    rw [map_one]
    exact section3SinAngleOperator_le_one U V
  exact (le_algebraMap_iff_spectrum_le
    (R := ℝ) (a := section3SinAngleOperator U V) (r := (1 : ℝ))
    (ha := section3SinAngleOperator_isSelfAdjoint U V)).mp hle x hx

/-- The literal angle is self-adjoint. -/
theorem section3AngleOperator_isSelfAdjoint :
    IsSelfAdjoint (section3AngleOperator U V) := by
  exact cfc_predicate Real.arcsin (section3SinAngleOperator U V)

/-- The literal angle is nonnegative. -/
theorem section3AngleOperator_nonneg :
    0 ≤ section3AngleOperator U V := by
  apply cfc_nonneg
  intro x hx
  exact Real.arcsin_nonneg.mpr
    ((spectrum_section3SinAngleOperator_subset_Icc U V hx).1)

/-- Functional calculus recovers the positive sine exactly. -/
theorem cfc_sin_section3AngleOperator :
    cfc Real.sin (section3AngleOperator U V) = section3SinAngleOperator U V := by
  have hsa := section3SinAngleOperator_isSelfAdjoint U V
  rw [section3AngleOperator,
    ← cfc_comp Real.sin Real.arcsin (section3SinAngleOperator U V)
      hsa Real.continuous_sin.continuousOn Real.continuous_arcsin.continuousOn]
  calc
    cfc (Real.sin ∘ Real.arcsin) (section3SinAngleOperator U V)
        = cfc (fun x : ℝ => x) (section3SinAngleOperator U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_section3SinAngleOperator_subset_Icc U V hx
      exact Real.sin_arcsin (by linarith [hxi.1]) (by linarith [hxi.2])
    _ = section3SinAngleOperator U V := cfc_id' ℝ _

/-- The operator angle and its sine have the same kernel.  This records the zero-angle
support without any pure-point-spectrum assumption. -/
theorem ker_section3AngleOperator_eq_ker_sine :
    LinearMap.ker (section3AngleOperator U V).toLinearMap =
      LinearMap.ker (section3SinAngleOperator U V).toLinearMap := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hθ
    by_cases hx0 : x = 0
    · simp [hx0]
    have hθ' : section3AngleOperator U V x = ((0 : ℝ) : 𝕜) • x := by
      simpa using hθ
    have hs := TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
      (section3AngleOperator_isSelfAdjoint U V) hx0 hθ'
      Real.sin Real.continuous_sin
    rw [cfc_sin_section3AngleOperator U V] at hs
    simpa using hs
  · intro hs
    by_cases hx0 : x = 0
    · simp [hx0]
    have hs' : section3SinAngleOperator U V x = ((0 : ℝ) : 𝕜) • x := by
      simpa using hs
    have hθ := TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
      (section3SinAngleOperator_isSelfAdjoint U V) hx0 hs'
      Real.arcsin Real.continuous_arcsin
    rw [section3AngleOperator]
    simpa using hθ

/-- The angle spectrum lies in the canonical interval `[0, π/2]`. -/
theorem spectrum_section3AngleOperator_subset_Icc :
    spectrum ℝ (section3AngleOperator U V) ⊆ Set.Icc 0 (Real.pi / 2) := by
  intro y hy
  rw [section3AngleOperator,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := section3SinAngleOperator U V)
      (section3SinAngleOperator_isSelfAdjoint U V)
      Real.continuous_arcsin.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_section3SinAngleOperator_subset_Icc U V hx
  exact ⟨Real.arcsin_nonneg.mpr hxi.1, Real.arcsin_le_pi_div_two x⟩

/-- Operator Pythagoras for the literal sine and cosine. -/
theorem section3Sin_sq_add_cos_sq :
    section3SinAngleOperator U V * section3SinAngleOperator U V +
      section3CosAngleOperator U V * section3CosAngleOperator U V = 1 := by
  rw [← cfc_sin_section3AngleOperator U V, section3CosAngleOperator,
    ← cfc_mul Real.sin Real.sin (section3AngleOperator U V)
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn,
    ← cfc_mul Real.cos Real.cos (section3AngleOperator U V)
      Real.continuous_cos.continuousOn Real.continuous_cos.continuousOn,
    ← cfc_add (a := section3AngleOperator U V)
      (fun x : ℝ => Real.sin x * Real.sin x)
      (fun x : ℝ => Real.cos x * Real.cos x)
      ((Real.continuous_sin.mul Real.continuous_sin).continuousOn)
      ((Real.continuous_cos.mul Real.continuous_cos).continuousOn)]
  calc
    cfc (fun x : ℝ => Real.sin x * Real.sin x + Real.cos x * Real.cos x)
        (section3AngleOperator U V)
        = cfc (fun _ : ℝ => 1) (section3AngleOperator U V) := by
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    _ = 1 := by
      have ha : IsSelfAdjoint (section3AngleOperator U V) :=
        section3AngleOperator_isSelfAdjoint U V
      exact cfc_const_one ℝ _

/-- `cos Θ` is nonnegative on the canonical angle spectrum. -/
theorem section3CosAngleOperator_nonneg :
    0 ≤ section3CosAngleOperator U V := by
  rw [section3CosAngleOperator]
  apply cfc_nonneg
  intro x hx
  have hI := spectrum_section3AngleOperator_subset_Icc U V hx
  exact Real.cos_nonneg_of_mem_Icc
    ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hI.1, hI.2⟩

/-! ## Identification with the Halmos cosine -/

/-- The square of `sin Θ` is the Halmos sine square. -/
theorem section3SinAngleOperator_mul_self_eq_halmosSineSq :
    section3SinAngleOperator U V * section3SinAngleOperator U V =
      halmosSineSq U V := by
  rw [section3SinAngleOperator, ContinuousLinearMap.modulus_mul_self]
  have hadj : (U.starProjection - V.starProjection : H →L[𝕜] H).adjoint =
      U.starProjection - V.starProjection := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_sub,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq]
  rw [hadj]
  simpa only [ContinuousLinearMap.mul_def] using
    (halmosSineSq_eq_projection_sub_sq U V).symm

/-- The modulus of the canonical intertwiner squares to the Halmos cosine
square, over either real or complex scalars. -/
theorem section3CanonicalAbsoluteValue_mul_self_eq_halmosCosineSq :
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) *
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) =
      halmosCosineSq U V := by
  rw [ContinuousLinearMap.modulus_mul_self_eq_star_mul_self, star_spectraCanonicalIntertwiner]
  let P : H →L[𝕜] H := U.starProjection
  let Pc : H →L[𝕜] H := (Uᗮ).starProjection
  let Q : H →L[𝕜] H := V.starProjection
  let Qc : H →L[𝕜] H := (Vᗮ).starProjection
  change (P * Q + Pc * Qc) * (Q * P + Qc * Pc) =
    P * Q * P + Pc * Qc * Pc
  have hQ : Q * Q = Q := by simp [Q]
  have hQQc : Q * Qc = 0 := by simp [Q, Qc]
  have hQcQ : Qc * Q = 0 := by simp [Q, Qc]
  have hQc : Qc * Qc = Qc := by simp [Qc]
  calc
    (P * Q + Pc * Qc) * (Q * P + Qc * Pc)
        = (P * Q) * (Q * P) + (P * Q) * (Qc * Pc) +
            (Pc * Qc) * (Q * P) + (Pc * Qc) * (Qc * Pc) := by noncomm_ring
    _ = P * Q * P + Pc * Qc * Pc := by
      rw [mul_assoc P Q (Q * P), ← mul_assoc Q Q P, hQ,
        mul_assoc P Q (Qc * Pc), ← mul_assoc Q Qc Pc, hQQc,
        mul_assoc Pc Qc (Q * P), ← mul_assoc Qc Q P, hQcQ,
        mul_assoc Pc Qc (Qc * Pc), ← mul_assoc Qc Qc Pc, hQc]
      simp only [mul_assoc, zero_mul, mul_zero, add_zero]

/-- The literal `cos Θ` has square equal to the Halmos cosine square. -/
theorem section3CosAngleOperator_mul_self_eq_halmosCosineSq :
    section3CosAngleOperator U V * section3CosAngleOperator U V =
      halmosCosineSq U V := by
  have hpy := section3Sin_sq_add_cos_sq U V
  have hs := section3SinAngleOperator_mul_self_eq_halmosSineSq U V
  have hh := halmosCosineSq_add_sineSq U V
  have h1 : section3CosAngleOperator U V * section3CosAngleOperator U V =
      1 - section3SinAngleOperator U V * section3SinAngleOperator U V :=
    eq_sub_of_add_eq' hpy
  have h2 : halmosCosineSq U V = 1 - halmosSineSq U V :=
    eq_sub_of_add_eq hh
  rw [h1, hs, ← h2]

/-- The literal functional-calculus cosine is exactly the positive modulus of
the canonical intertwiner. -/
theorem section3CosAngleOperator_eq_canonicalAbsoluteValue :
    section3CosAngleOperator U V =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  have habs0 := ContinuousLinearMap.modulus_nonneg (spectraCanonicalIntertwiner U V)
  have hcos0 := section3CosAngleOperator_nonneg U V
  have hsquare := section3CosAngleOperator_mul_self_eq_halmosCosineSq U V
  have habssquare := section3CanonicalAbsoluteValue_mul_self_eq_halmosCosineSq U V
  calc
    section3CosAngleOperator U V
        = CFC.sqrt (halmosCosineSq U V) :=
          (CFC.sqrt_unique hsquare hcos0).symm
    _ = ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) :=
          CFC.sqrt_unique habssquare habs0

/-! ## Symmetry under interchange of the subspaces -/

/-- Interchanging the subspaces leaves `sin Θ` unchanged. -/
theorem section3SinAngleOperator_symm :
    section3SinAngleOperator V U = section3SinAngleOperator U V := by
  rw [section3SinAngleOperator, section3SinAngleOperator]
  have hneg : V.starProjection - U.starProjection = -(U.starProjection - V.starProjection) := by
    abel
  rw [hneg, ContinuousLinearMap.modulus_neg]

/-- Interchanging the subspaces leaves the bounded operator angle unchanged. -/
theorem section3AngleOperator_symm :
    section3AngleOperator V U = section3AngleOperator U V := by
  rw [section3AngleOperator, section3AngleOperator, section3SinAngleOperator_symm U V]

/-- Interchanging the subspaces leaves `cos Θ` unchanged. -/
theorem section3CosAngleOperator_symm :
    section3CosAngleOperator V U = section3CosAngleOperator U V := by
  rw [section3CosAngleOperator, section3CosAngleOperator, section3AngleOperator_symm U V]

/-- Interchanging the subspaces takes the canonical direct rotation to its adjoint. -/
theorem section3DirectRotation_swap :
    section3DirectRotation V U = star (section3DirectRotation U V) := by
  rw [section3DirectRotation, section3DirectRotation]
  exact (canonicalPolarFactor_adjoint_swap_from_polar U V).symm

/-! ## The four commutations -/

/-- `sin Θ` commutes with the source projection. -/
theorem section3SinAngleOperator_comm_projection :
    Commute (section3SinAngleOperator U V) (U.starProjection) := by
  exact TauCeti.commute_of_commute_mul_self
    (section3SinAngleOperator_nonneg U V)
    (by
      rw [section3SinAngleOperator_mul_self_eq_halmosSineSq]
      exact halmosSineSq_commute_projection U V)

/-- `sin Θ` commutes with the target projection. -/
theorem section3SinAngleOperator_comm_projection_right :
    Commute (section3SinAngleOperator U V) (V.starProjection) := by
  have hsinQ : Commute (halmosSineSq U V) (V.starProjection) := by
    have hcosQ := halmosCosineSq_commute_projection_right U V
    have hs : halmosSineSq U V = 1 - halmosCosineSq U V :=
      eq_sub_of_add_eq' (halmosCosineSq_add_sineSq U V)
    rw [hs]
    exact (Commute.one_left (V.starProjection)).sub_left hcosQ
  exact TauCeti.commute_of_commute_mul_self
    (section3SinAngleOperator_nonneg U V)
    (by rwa [section3SinAngleOperator_mul_self_eq_halmosSineSq])

/-- Proposition 3.5: `Θ` commutes with `P`. -/
theorem section3AngleOperator_comm_projection :
    Commute (section3AngleOperator U V) (U.starProjection) := by
  rw [section3AngleOperator]
  exact Commute.cfc_real (section3SinAngleOperator_comm_projection U V) Real.arcsin

/-- Proposition 3.5: `Θ` commutes with `Q`. -/
theorem section3AngleOperator_comm_projection_right :
    Commute (section3AngleOperator U V) (V.starProjection) := by
  rw [section3AngleOperator]
  exact Commute.cfc_real (section3SinAngleOperator_comm_projection_right U V) Real.arcsin

omit [CompleteSpace H] in
private theorem add_self_cancel {a b : H →L[𝕜] H} (h : a + a = b + b) : a = b := by
  let twoUnit : 𝕜ˣ := Units.mk0 2 (by norm_num)
  apply smul_left_cancel twoUnit
  change (2 : 𝕜) • a = (2 : 𝕜) • b
  simpa only [two_smul 𝕜] using h

/-- In the acute case the direct rotation commutes with the positive cosine. -/
theorem section3DirectRotation_comm_cosine (hacute : TauCeti.IsAcute U V) :
    Commute (section3DirectRotation U V) (section3CosAngleOperator U V) := by
  obtain ⟨hUV, hVU⟩ := (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute)
  let W := section3DirectRotation U V
  let C := section3CosAngleOperator U V
  have hunit : W ∈ unitary (H →L[𝕜] H) :=
    spectraCanonicalPolarFactor_mem_unitary U V hUV hVU
  have hsum0 := polarFactor_add_star_eq_two_absoluteValue U V
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum : W + star W = C + C := by
    simpa [W, C, section3DirectRotation, hCeq] using hsum0
  have hcommStar : Commute W (star W) := by
    rw [commute_iff_eq]
    exact (Unitary.mul_star_self_of_mem hunit).trans
      (Unitary.star_mul_self_of_mem hunit).symm
  have hcommSum : Commute W (W + star W) :=
    (Commute.refl W).add_right hcommStar
  have hcommDouble : Commute W (C + C) := by rwa [← hsum]
  have hleft : W * C + W * C = C * W + C * W := by
    simpa [mul_add, add_mul] using hcommDouble.eq
  rw [commute_iff_eq]
  exact add_self_cancel hleft

/-- In the acute case the direct rotation commutes with `sin Θ`. -/
theorem section3DirectRotation_comm_sine (hacute : TauCeti.IsAcute U V) :
    Commute (section3DirectRotation U V) (section3SinAngleOperator U V) := by
  have hC := section3DirectRotation_comm_cosine U V hacute
  have hS2 : Commute
      (section3SinAngleOperator U V * section3SinAngleOperator U V)
      (section3DirectRotation U V) := by
    have hpy := section3Sin_sq_add_cos_sq U V
    have hs : section3SinAngleOperator U V * section3SinAngleOperator U V =
        1 - section3CosAngleOperator U V * section3CosAngleOperator U V :=
      eq_sub_of_add_eq hpy
    rw [hs]
    exact (Commute.one_left _).sub_left (hC.symm.mul_left hC.symm)
  exact (TauCeti.commute_of_commute_mul_self
    (section3SinAngleOperator_nonneg U V) hS2).symm

/-- Proposition 3.5: `Θ` commutes with the direct rotation `U`. -/
theorem section3AngleOperator_comm_directRotation (hacute : TauCeti.IsAcute U V) :
    Commute (section3AngleOperator U V) (section3DirectRotation U V) := by
  rw [section3AngleOperator]
  exact Commute.cfc_real (section3DirectRotation_comm_sine U V hacute).symm Real.arcsin

/-! ## The quarter turn -/

/-- The skew part `W - cos Θ` is skew-adjoint. -/
theorem star_section3DirectRotation_sub_cosine :
    star (section3DirectRotation U V - section3CosAngleOperator U V) =
      -(section3DirectRotation U V - section3CosAngleOperator U V) := by
  let W := section3DirectRotation U V
  let C := section3CosAngleOperator U V
  have hCsa : star C = C :=
    (cfc_predicate Real.cos (section3AngleOperator U V)).star_eq
  have hsum0 := polarFactor_add_star_eq_two_absoluteValue U V
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum : W + star W = C + C := by
    simpa [W, C, section3DirectRotation, hCeq] using hsum0
  have hsW : star W = C + C - W := by
    rw [← hsum]; abel
  rw [star_sub, show star W = C + C - W from hsW, hCsa]
  abel

/-- Interchanging the subspaces negates the canonical quarter turn. -/
theorem section3QuarterTurn_symm :
    section3QuarterTurn V U = -section3QuarterTurn U V := by
  rw [section3QuarterTurn, section3QuarterTurn]
  have hD :
      section3DirectRotation V U - section3CosAngleOperator V U =
        -(section3DirectRotation U V - section3CosAngleOperator U V) := by
    rw [section3DirectRotation_swap U V, section3CosAngleOperator_symm U V]
    have hCstar :
        star (section3CosAngleOperator U V) = section3CosAngleOperator U V :=
      (cfc_predicate Real.cos (section3AngleOperator U V)).star_eq
    calc
      star (section3DirectRotation U V) - section3CosAngleOperator U V =
          star (section3DirectRotation U V) - star (section3CosAngleOperator U V) := by
        rw [hCstar]
      _ = -(section3DirectRotation U V - section3CosAngleOperator U V) := by
        simpa only [star_sub] using star_section3DirectRotation_sub_cosine U V
  rw [hD, ContinuousLinearMap.polarPartial_neg]

/-- The skew part has modulus exactly `sin Θ`. -/
theorem modulus_section3DirectRotation_sub_cosine (hacute : TauCeti.IsAcute U V) :
    (section3DirectRotation U V - section3CosAngleOperator U V).modulus =
      section3SinAngleOperator U V := by
  obtain ⟨hUV, hVU⟩ := TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute
  let W := section3DirectRotation U V
  let C := section3CosAngleOperator U V
  let S := section3SinAngleOperator U V
  let D := W - C
  have hunit : W ∈ unitary (H →L[𝕜] H) :=
    spectraCanonicalPolarFactor_mem_unitary U V hUV hVU
  have hWC := section3DirectRotation_comm_cosine U V hacute
  have hWC' : W * C = C * W := by
    simpa [W, C] using hWC.eq
  have hsum0 := polarFactor_add_star_eq_two_absoluteValue U V
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum : W + star W = C + C := by
    simpa [W, C, section3DirectRotation, hCeq] using hsum0
  have hgram : star D * D = S * S := by
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

/-- The paper's polar resolution `W = cos Θ + J sin Θ`. -/
theorem section3DirectRotation_eq_cos_add_quarterTurn_sin (hacute : TauCeti.IsAcute U V) :
    section3DirectRotation U V =
      section3CosAngleOperator U V +
        section3QuarterTurn U V ∘L section3SinAngleOperator U V := by
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hmod := modulus_section3DirectRotation_sub_cosine U V hacute
  have hpolar := D.polarPartial_comp_modulus
  have hD : section3QuarterTurn U V ∘L section3SinAngleOperator U V = D := by
    rw [section3QuarterTurn, ← hmod]
    exact hpolar
  rw [hD]
  dsimp [D]
  abel

/-- Proposition 3.5: `Θ` commutes with the quarter turn `J`. -/
theorem section3AngleOperator_comm_quarterTurn (hacute : TauCeti.IsAcute U V) :
    Commute (section3AngleOperator U V) (section3QuarterTurn U V) := by
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hθW := section3AngleOperator_comm_directRotation U V hacute
  have hθC : Commute (section3AngleOperator U V) (section3CosAngleOperator U V) := by
    rw [section3CosAngleOperator]
    exact (Commute.cfc_real (Commute.refl (section3AngleOperator U V)) Real.cos).symm
  have hθD : Commute (section3AngleOperator U V) D := by
    exact hθW.sub_right hθC
  have hmod := modulus_section3DirectRotation_sub_cosine U V hacute
  have hθmod : Commute (section3AngleOperator U V) D.modulus := by
    rw [hmod]
    rw [section3AngleOperator]
    exact Commute.cfc_real (Commute.refl (section3SinAngleOperator U V)) Real.arcsin
  have h := ContinuousLinearMap.commute_polarPartial_of_commute hθD hθmod
  simpa [D, section3QuarterTurn] using h

/-! ## Eigenvectors -/

omit [CompleteSpace H] in
private theorem eq_of_smul_eq_smul_right {α β : 𝕜} {x : H} (hx : x ≠ 0)
    (h : α • x = β • x) : α = β := by
  have hz : (α - β) • x = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with hzero | hxzero
  · exact sub_eq_zero.mp hzero
  · exact (hx hxzero).elim

/-- `sin Θ` acts on an angle eigenvector by the scalar sine. -/
theorem section3SinAngleOperator_apply_of_angleOperator_apply {x : H} {θ : ℝ}
    (hx0 : x ≠ 0)
    (hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    section3SinAngleOperator U V x = ((Real.sin θ : ℝ) : 𝕜) • x := by
  rw [← cfc_sin_section3AngleOperator U V]
  exact TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
    (section3AngleOperator_isSelfAdjoint U V) hx0 hx Real.sin Real.continuous_sin

/-- `cos Θ` acts on an angle eigenvector by the scalar cosine. -/
theorem section3CosAngleOperator_apply_of_angleOperator_apply {x : H} {θ : ℝ}
    (hx0 : x ≠ 0)
    (hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    section3CosAngleOperator U V x = ((Real.cos θ : ℝ) : 𝕜) • x := by
  rw [section3CosAngleOperator]
  exact TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
    (section3AngleOperator_isSelfAdjoint U V) hx0 hx Real.cos Real.continuous_cos

/-- Every genuine eigenvalue of the operator angle lies in `[0,π/2]`. -/
theorem section3AngleOperator_eigenvalue_mem_Icc {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    θ ∈ Set.Icc 0 (Real.pi / 2) := by
  have hsx := section3SinAngleOperator_apply_of_angleOperator_apply U V hx0 hx
  have hback : section3AngleOperator U V x =
      ((Real.arcsin (Real.sin θ) : ℝ) : 𝕜) • x := by
    rw [section3AngleOperator]
    exact TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
      (section3SinAngleOperator_isSelfAdjoint U V) hx0 hsx
      Real.arcsin Real.continuous_arcsin
  rw [hx] at hback
  have hscalar : ((θ : ℝ) : 𝕜) = ((Real.arcsin (Real.sin θ) : ℝ) : 𝕜) :=
    eq_of_smul_eq_smul_right hx0 hback
  have hreal : θ = Real.arcsin (Real.sin θ) :=
    RCLike.ofReal_injective (K := 𝕜) hscalar
  have hnn := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (section3SinAngleOperator_nonneg U V)).re_inner_nonneg_left x
  rw [hsx, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq] at hnn
  have hxnorm : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hsin0 : 0 ≤ Real.sin θ :=
    le_of_mul_le_mul_right (by simpa using hnn) hxnorm
  have harc := Real.arcsin_mem_Icc (Real.sin θ)
  rw [hreal]
  exact ⟨Real.arcsin_nonneg.mpr hsin0, harc.2⟩

/-- The skew part has vanishing real quadratic form. -/
theorem re_inner_section3DirectRotation_sub_cosine_apply_self (x : H) :
    RCLike.re ⟪(section3DirectRotation U V - section3CosAngleOperator U V) x, x⟫_𝕜 = 0 := by
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hstar : star D = -D := by
    simpa [D] using star_section3DirectRotation_sub_cosine U V
  have h1 : ⟪D x, x⟫_𝕜 = ⟪x, star D x⟫_𝕜 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_right D x x).symm
  rw [hstar, neg_apply, inner_neg_right] at h1
  have hre := congrArg RCLike.re h1
  have hsym : RCLike.re ⟪x, D x⟫_𝕜 = RCLike.re ⟪D x, x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) x (D x)
  rw [map_neg, hsym] at hre
  linarith

/-- Proposition 3.5 eigenvector clause: an angle eigenvector is rotated through
exactly its angle eigenvalue. -/
theorem vectorAngle_section3DirectRotation_eq_of_angleOperator_apply
    (hacute : TauCeti.IsAcute U V) {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (section3DirectRotation U V x) = θ := by
  obtain ⟨hUV, hVU⟩ := TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute
  have hIcc := section3AngleOperator_eigenvalue_mem_Icc U V hx0 hx
  have hCx := section3CosAngleOperator_apply_of_angleOperator_apply U V hx0 hx
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hWx : section3DirectRotation U V x =
      ((Real.cos θ : ℝ) : 𝕜) • x + D x := by
    dsimp [D]
    rw [sub_apply, hCx]
    abel
  have hinner : RCLike.re ⟪section3DirectRotation U V x, x⟫_𝕜 =
      Real.cos θ * ‖x‖ ^ 2 := by
    rw [hWx, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
      re_inner_section3DirectRotation_sub_cosine_apply_self U V x, add_zero]
  have hunit := spectraCanonicalPolarFactor_mem_unitary U V hUV hVU
  refine TauCeti.vectorAngle_eq_of_re_inner_eq hx0
    (ContinuousLinearMap.norm_map_of_mem_unitary hunit x) hIcc.1 ?_ hinner
  linarith [hIcc.2, Real.pi_pos]

/-! ## The printed maximal eigenspace -/

omit [CompleteSpace H] in
private theorem positive_square_eigenvector
    {A : H →L[𝕜] H} (hA : 0 ≤ A) {x : H} {c : ℝ} (hc : 0 ≤ c)
    (hsq : A (A x) = ((c ^ 2 : ℝ) : 𝕜) • x) :
    A x = ((c : ℝ) : 𝕜) • x := by
  have hApos : (A : H →ₗ[𝕜] H).IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA).toLinearMap
  have hsq' : (A : H →ₗ[𝕜] H) ((A : H →ₗ[𝕜] H) x) =
      (((c : ℝ) : 𝕜) * ((c : ℝ) : 𝕜)) • x := by
    change A (A x) = (((c : ℝ) : 𝕜) * ((c : ℝ) : 𝕜)) • x
    rw [hsq, pow_two, RCLike.ofReal_mul]
  exact LinearMap.IsPositive.apply_eq_smul_of_apply_apply_eq_smul hApos hc hsq'

/-- The angle eigenspace equals the fixed-cosine Halmos eigenspace at every
actual acute angle eigenvalue. -/
theorem section3AngleEigenspace_eq_fixedCosineSubspace
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (section3AngleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    section3AngleEigenspace U V θ = fixedCosineSubspace U V (Real.cos θ) := by
  obtain ⟨x, hxmem, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hθ
  have hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hθI := section3AngleOperator_eigenvalue_mem_Icc U V hx0 hx
  have hc0 : 0 < Real.cos θ := by
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hθI.1, hθI.2⟩
    refine lt_of_le_of_ne hc ?_
    intro hzero
    obtain ⟨hUV, hVU⟩ := TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute
    have hCx := section3CosAngleOperator_apply_of_angleOperator_apply U V hx0 hx
    have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
    have hk : x ∈ LinearMap.ker
        (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)).toLinearMap := by
      rw [LinearMap.mem_ker, ← hCeq]
      change section3CosAngleOperator U V x = 0
      rw [hCx, ← hzero]
      simp
    rw [ker_spectraCanonicalAbsoluteValue_eq_bot U V hUV hVU] at hk
    exact hx0 (by simpa using hk)
  ext y
  constructor
  · intro hy
    rw [mem_fixedCosineSubspace]
    by_cases hy0 : y = 0
    · subst y
      simp
    have hyEig : section3AngleOperator U V y = ((θ : ℝ) : 𝕜) • y :=
      Module.End.mem_eigenspace_iff.mp hy
    have hCy := section3CosAngleOperator_apply_of_angleOperator_apply U V hy0 hyEig
    have hC2 := section3CosAngleOperator_mul_self_eq_halmosCosineSq U V
    have happ := congrArg (fun T : H →L[𝕜] H => T y) hC2
    simp only [mul_apply_eq_comp, hCy, map_smul, smul_smul] at happ
    simpa only [pow_two, RCLike.ofReal_mul] using happ.symm
  · intro hy
    have hfixed := (mem_fixedCosineSubspace U V (Real.cos θ) y).mp hy
    by_cases hy0 : y = 0
    · subst y
      simp [section3AngleEigenspace]
    have hC2 := section3CosAngleOperator_mul_self_eq_halmosCosineSq U V
    have hsq : section3CosAngleOperator U V (section3CosAngleOperator U V y) =
        (((Real.cos θ) ^ 2 : ℝ) : 𝕜) • y := by
      have happ := congrArg (fun T : H →L[𝕜] H => T y) hC2
      simp only [mul_apply_eq_comp] at happ
      rw [happ]
      simpa only [pow_two, RCLike.ofReal_mul] using hfixed
    have hCy := positive_square_eigenvector
      (section3CosAngleOperator_nonneg U V) (le_of_lt hc0) hsq
    have hpy := section3Sin_sq_add_cos_sq U V
    have hSinSq : section3SinAngleOperator U V (section3SinAngleOperator U V y) =
        (((Real.sin θ) ^ 2 : ℝ) : 𝕜) • y := by
      have happ := congrArg (fun T : H →L[𝕜] H => T y) hpy
      simp only [add_apply, mul_apply_eq_comp, hCy, map_smul, smul_smul,
        one_apply_eq_self] at happ
      have htrig : (1 : ℝ) - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      have hcast : (1 : 𝕜) - (((Real.cos θ) ^ 2 : ℝ) : 𝕜) =
          (((Real.sin θ) ^ 2 : ℝ) : 𝕜) := by
        exact_mod_cast htrig
      have happ' :
          section3SinAngleOperator U V (section3SinAngleOperator U V y) +
              (((Real.cos θ) ^ 2 : ℝ) : 𝕜) • y = y := by
        simpa only [pow_two, RCLike.ofReal_mul] using happ
      calc
        section3SinAngleOperator U V (section3SinAngleOperator U V y) =
            y - (((Real.cos θ) ^ 2 : ℝ) : 𝕜) • y := eq_sub_of_add_eq happ'
        _ = ((1 : 𝕜) - (((Real.cos θ) ^ 2 : ℝ) : 𝕜)) • y := by
          rw [sub_smul, one_smul]
        _ = (((Real.sin θ) ^ 2 : ℝ) : 𝕜) • y := by rw [hcast]
    have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi
      hθI.1 (hθI.2.trans (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))
    have hSy := positive_square_eigenvector
      (section3SinAngleOperator_nonneg U V) hsin0 hSinSq
    have hθy := TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul
      (section3SinAngleOperator_isSelfAdjoint U V) hy0 hSy
      Real.arcsin Real.continuous_arcsin
    rw [← section3AngleOperator] at hθy
    have hasin : Real.arcsin (Real.sin θ) = θ := by
      exact Real.arcsin_sin
        ((neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hθI.1) hθI.2
    rw [hasin] at hθy
    exact Module.End.mem_eigenspace_iff.mpr hθy

/-- Proposition 3.5's maximal-subspace clause, now stated on the actual
operator-angle eigenspace `Ω({θ})H` in arbitrary dimension. -/
theorem proposition3_5_angleEigenspace_maximal
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (section3AngleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    IsFixedCosineReducingSubspace U V (section3AngleEigenspace U V θ)
        (Real.cos θ) ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M (Real.cos θ) →
          M ≤ section3AngleEigenspace U V θ := by
  obtain ⟨x, hxmem, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hθ
  have hx : section3AngleOperator U V x = ((θ : ℝ) : 𝕜) • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hθI := section3AngleOperator_eigenvalue_mem_Icc U V hx0 hx
  have hc0 : 0 < Real.cos θ := by
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hθI.1, hθI.2⟩
    refine lt_of_le_of_ne hc ?_
    intro hzero
    obtain ⟨hUV, hVU⟩ := TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute
    have hCx := section3CosAngleOperator_apply_of_angleOperator_apply U V hx0 hx
    have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
    have hk : x ∈ LinearMap.ker
        (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)).toLinearMap := by
      rw [LinearMap.mem_ker, ← hCeq]
      change section3CosAngleOperator U V x = 0
      rw [hCx, ← hzero]
      simp
    rw [ker_spectraCanonicalAbsoluteValue_eq_bot U V hUV hVU] at hk
    exact hx0 (by simpa using hk)
  have heq := section3AngleEigenspace_eq_fixedCosineSubspace U V hacute hθ
  rw [heq]
  exact proposition3_5_fixedAngle_maximal U V (Real.cos θ) hc0

end

end Proposition35
end DavisKahan
end TauCeti
