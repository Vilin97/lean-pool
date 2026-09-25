/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityEndpoint
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.UnitDescendantSup
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarAlgebra
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds.Apex
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

/-! # Uniform Ellipticity Bridge -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Uniform ellipticity bridge for the Section 5.7 endpoint

This file turns a law-level almost-sure uniform ellipticity support condition
into the `Γ_∞` endpoint used by the public quenched theorem.
-/

/-- A law is supported on coefficient fields with one uniform ellipticity
window on every triadic cube. -/
structure UniformEllipticityBounds {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (lam Lam : ℝ) : Prop where
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aee_elliptic :
    ∀ᵐ a ∂P,
      ∀ Q : TriadicCube d,
        Ch04.AEEllipticOn lam Lam (openCubeSet Q) a

namespace UniformEllipticityBounds

variable {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {lam Lam : ℝ}

/-- The uniform support hypothesis implies the Chapter 4 local ellipticity
support condition. -/
theorem ae_locallyUniformlyEllipticField
    (hUE : UniformEllipticityBounds P lam Lam) :
    ∀ᵐ a ∂P, Ch04.AELocallyUniformlyEllipticField a := by
  filter_upwards [hUE.aee_elliptic] with a ha Q
  exact ⟨lam, Lam, hUE.lam_pos, hUE.lam_le_Lam, ha Q⟩

/-- Forget the fixed constants in the uniform support hypothesis. -/
theorem toAELocallyUniformlyEllipticLaw
    (hUE : UniformEllipticityBounds P lam Lam) :
    Ch04.AELocallyUniformlyEllipticLaw P :=
  hUE.ae_locallyUniformlyEllipticField

end UniformEllipticityBounds

/-- A one-cube Chapter 2 coefficient object using prescribed ellipticity
constants.  This avoids losing the displayed constants to `Classical.choose`
inside the generic Chapter 4 bridge. -/
noncomputable def coeffOnOfUniformAEEllipticOn {d : ℕ}
    (a : RegCoeffField d) (Q : TriadicCube d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hQ : Ch04.AEEllipticOn lam Lam (openCubeSet Q) a) :
    Ch02.CoeffOn (Ch02.cubeDomain Q) where
  toCoeffField := a
  lam := lam
  Lam := Lam
  lam_pos := hlam
  lam_le_Lam := hle
  aeStronglyMeasurable := by
    intro i j
    simpa [Ch02.cubeDomain_coe] using
      IsAEEllipticFieldOn.aestronglyMeasurable_restrictCoeffField_apply
        hQ i j
  aeElliptic := by
    simpa [Ch02.cubeDomain_coe] using
      IsAEEllipticFieldOn.ae_isEllipticMatrix hQ

@[simp]
theorem coeffOnOfUniformAEEllipticOn_toCoeffField {d : ℕ}
    (a : RegCoeffField d) (Q : TriadicCube d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hQ : Ch04.AEEllipticOn lam Lam (openCubeSet Q) a) :
    (coeffOnOfUniformAEEllipticOn a Q hlam hle hQ).toCoeffField = a :=
  rfl

/-- The Chapter 2 family associated to fixed law-level uniform ellipticity
constants. -/
noncomputable def triadicCoeffFamilyOfUniformEllipticity {d : ℕ}
    (a : RegCoeffField d) {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ Q : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet Q) a) :
    Ch02.TriadicCoeffFamily d where
  coeffOn := fun Q => coeffOnOfUniformAEEllipticOn a Q hlam hle (ha Q)
  restrictsTo_of_subset := by
    intro Q R _hsub
    change a =ᵐ[volumeMeasureOn (Ch02.cubeDomain R : Set (Vec d))] a
    exact Filter.EventuallyEq.rfl

theorem triadicCoeffFamilyOfAELocallyUniformlyEllipticField_aeeq_uniform
    {d : ℕ} {a : RegCoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ Q : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet Q) a)
    (hlocal : Ch04.AELocallyUniformlyEllipticField a) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal)
      (triadicCoeffFamilyOfUniformEllipticity a hlam hle ha) := by
  intro Q
  change a =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))] a
  exact Filter.EventuallyEq.rfl

/-- Deterministic upper-block constant coming from pointwise uniform
ellipticity. -/
noncomputable def uniformUpperBlockConst (d : ℕ) (lam Lam : ℝ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ (2 : ℕ)

/-- Deterministic lower-inverse block constant coming from pointwise uniform
ellipticity. -/
noncomputable def uniformLowerInvBlockConst (d : ℕ) (lam : ℝ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹

theorem uniformUpperBlockConst_nonneg {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    0 ≤ uniformUpperBlockConst d lam Lam := by
  have hLam_nonneg : 0 ≤ Lam := hlam.le.trans hle
  unfold uniformUpperBlockConst
  positivity

theorem uniformLowerInvBlockConst_nonneg {d : ℕ} {lam : ℝ}
    (hlam : 0 < lam) :
    0 ≤ uniformLowerInvBlockConst d lam := by
  unfold uniformLowerInvBlockConst
  positivity

private theorem maxDescendantBMatrixNormAtScale_le_uniform_of_uniformEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ T : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet T) a)
    (n : ℕ) :
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ))
        (triadicCoeffFamilyOfUniformEllipticity a hlam hle ha) ≤
      uniformUpperBlockConst d lam Lam := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfUniformEllipticity a hlam hle ha
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) A := by
    simpa [A, F, triadicCoeffFamilyOfUniformEllipticity,
      coeffOnOfUniformAEEllipticOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
        ≤ Homogenization.maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A := by
          exact Ch02.maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
            F Q hk
    _ ≤ uniformUpperBlockConst d lam Lam := by
          simpa [uniformUpperBlockConst, A] using
            maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              Q A hEll hData n

private theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform_of_uniformEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ T : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet T) a)
    (n : ℕ) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ))
        (triadicCoeffFamilyOfUniformEllipticity a hlam hle ha) ≤
      uniformLowerInvBlockConst d lam := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfUniformEllipticity a hlam hle ha
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) A := by
    simpa [A, F, triadicCoeffFamilyOfUniformEllipticity,
      coeffOnOfUniformAEEllipticOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
        ≤ Homogenization.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A := by
          exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
            F Q hk
    _ ≤ uniformLowerInvBlockConst d lam := by
          simpa [uniformLowerInvBlockConst, A] using
            maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              Q A hEll hData n

private theorem tsum_geometricWeight_one_mul_le_const
    {H : ℕ → ℝ} {s C : ℝ} (hs : 0 < s)
    (hH_nonneg : ∀ n : ℕ, 0 ≤ H n)
    (hH_le : ∀ n : ℕ, H n ≤ C) :
    (∑' n : ℕ, geometricWeight s 1 n * H n) ≤ C := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hsumH :
      Summable (fun n : ℕ => geometricWeight s 1 n * H n) :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := C) hs1 hH_nonneg hH_le
  have hsumC :
      Summable (fun n : ℕ => geometricWeight s 1 n * C) :=
    (Homogenization.summable_geometricWeight (s := s) (q := 1) hs1).mul_right C
  have hterm :
      ∀ n : ℕ, geometricWeight s 1 n * H n ≤ geometricWeight s 1 n * C := by
    intro n
    exact mul_le_mul_of_nonneg_left (hH_le n)
      (geometricWeight_nonneg n hs1.le)
  calc
    (∑' n : ℕ, geometricWeight s 1 n * H n)
        ≤ ∑' n : ℕ, geometricWeight s 1 n * C :=
          Summable.tsum_le_tsum hterm hsumH hsumC
    _ = C := by
          rw [tsum_mul_right, Homogenization.tsum_geometricWeight_eq_one hs1]
          ring

/-- A sample satisfying fixed uniform ellipticity bounds has bounded upper
multiscale ellipticity on every cube. -/
theorem LambdaSqCoeffField_finite_one_le_of_uniformEllipticitySample
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {lam Lam s : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ T : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet T) a)
    (hs : 0 < s) :
    Ch04.LambdaSqCoeffField Q s (.finite 1) a ≤
      uniformUpperBlockConst d lam Lam := by
  classical
  let hlocal : Ch04.AELocallyUniformlyEllipticField a :=
    fun T => ⟨lam, Lam, hlam, hle, ha T⟩
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfUniformEllipticity a hlam hle ha
  have hAEEq :
      Ch02.TriadicCoeffFamily.AEEq
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal)
        F := by
    simpa [F] using
      triadicCoeffFamilyOfAELocallyUniformlyEllipticField_aeeq_uniform
        (a := a) hlam hle ha hlocal
  have hEq :
      Ch04.LambdaSqCoeffField Q s (.finite 1) a =
        Ch02.LambdaSq Q s (.finite 1) F := by
    simpa [Ch04.LambdaSqCoeffField, hlocal, F] using
      Ch02.LambdaSq_eq_ofAEEq hAEEq Q s (.finite 1)
  have hsplit :
      Ch02.LambdaSq Q s (.finite 1) F ≤
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F :=
    Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
      Q F hs
  have hsum_le :
      (∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F) ≤
        uniformUpperBlockConst d lam Lam := by
    exact
      tsum_geometricWeight_one_mul_le_const
        (H := fun n : ℕ =>
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F)
        hs
        (fun n =>
          Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
            (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F)
        (fun n =>
          maxDescendantBMatrixNormAtScale_le_uniform_of_uniformEllipticity
            Q a hlam hle ha n)
  calc
    Ch04.LambdaSqCoeffField Q s (.finite 1) a =
        Ch02.LambdaSq Q s (.finite 1) F := hEq
    _ ≤ ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F := hsplit
    _ ≤ uniformUpperBlockConst d lam Lam := hsum_le

/-- A sample satisfying fixed uniform ellipticity bounds has bounded inverse
lower multiscale ellipticity on every cube. -/
theorem lambdaSqCoeffField_finite_one_inv_le_of_uniformEllipticitySample
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {lam Lam s : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ha : ∀ T : TriadicCube d,
      Ch04.AEEllipticOn lam Lam (openCubeSet T) a)
    (hs : 0 < s) :
    (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ ≤
      uniformLowerInvBlockConst d lam := by
  classical
  let hlocal : Ch04.AELocallyUniformlyEllipticField a :=
    fun T => ⟨lam, Lam, hlam, hle, ha T⟩
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfUniformEllipticity a hlam hle ha
  have hAEEq :
      Ch02.TriadicCoeffFamily.AEEq
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal)
        F := by
    simpa [F] using
      triadicCoeffFamilyOfAELocallyUniformlyEllipticField_aeeq_uniform
        (a := a) hlam hle ha hlocal
  have hEq :
      (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ =
        (Ch02.lambdaSq Q s (.finite 1) F)⁻¹ := by
    simpa [Ch04.lambdaSqCoeffField, hlocal, F] using
      congrArg Inv.inv (Ch02.lambdaSq_eq_ofAEEq hAEEq Q s (.finite 1))
  have hsplit :
      (Ch02.lambdaSq Q s (.finite 1) F)⁻¹ ≤
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              Q (Q.scale - (n : ℤ)) F :=
    Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
      Q F hs
  have hsum_le :
      (∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            Q (Q.scale - (n : ℤ)) F) ≤
        uniformLowerInvBlockConst d lam := by
    exact
      tsum_geometricWeight_one_mul_le_const
        (H := fun n : ℕ =>
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            Q (Q.scale - (n : ℤ)) F)
        hs
        (fun n =>
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
            (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F)
        (fun n =>
          maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform_of_uniformEllipticity
            Q a hlam hle ha n)
  calc
    (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ =
        (Ch02.lambdaSq Q s (.finite 1) F)⁻¹ := hEq
    _ ≤ ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              Q (Q.scale - (n : ℤ)) F := hsplit
    _ ≤ uniformLowerInvBlockConst d lam := hsum_le

private theorem integrable_pow_of_ae_nonneg_le_const
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {X : RegCoeffField d → ℝ}
    [IsFiniteMeasure P]
    {C : ℝ} (ξ : ℕ)
    (hC : 0 ≤ C) (hX_nonneg : ∀ a, 0 ≤ X a)
    (hX_aemeas : AEMeasurable X P)
    (hX_le : X ≤ᵐ[P] fun _ => C) :
    Integrable (fun a : RegCoeffField d => X a ^ ξ) P := by
  refine Integrable.mono' (integrable_const (C ^ ξ))
    (hX_aemeas.pow_const ξ).aestronglyMeasurable ?_
  filter_upwards [hX_le] with a ha
  have hCpow_nonneg : 0 ≤ C ^ ξ := pow_nonneg hC ξ
  have hpow_le : X a ^ ξ ≤ C ^ ξ :=
    pow_le_pow_left₀ (hX_nonneg a) ha ξ
  simpa [Real.norm_eq_abs, abs_of_nonneg (hX_nonneg a),
    abs_of_nonneg hCpow_nonneg] using hpow_le

theorem LambdaSqCoeffField_pow_integrable_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam s : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (Q : TriadicCube d) (hs : 0 < s) (ξ : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ ξ) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := uniformUpperBlockConst d lam Lam
  have hC : 0 ≤ C := by
    simpa [C] using uniformUpperBlockConst_nonneg hUE.lam_pos hUE.lam_le_Lam
  have hX_nonneg :
      ∀ a : RegCoeffField d, 0 ≤ Ch04.LambdaSqCoeffField Q s (.finite 1) a :=
    fun a => Ch04.LambdaSqCoeffField_finite_nonneg Q a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hX_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch04.LambdaSqCoeffField Q s (.finite 1) a) P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one Q hs
  have hX_le :
      (fun a : RegCoeffField d => Ch04.LambdaSqCoeffField Q s (.finite 1) a)
        ≤ᵐ[P] fun _ => C := by
    filter_upwards [hUE.aee_elliptic] with a ha
    simpa [C] using
      LambdaSqCoeffField_finite_one_le_of_uniformEllipticitySample
        Q a hUE.lam_pos hUE.lam_le_Lam ha hs
  exact integrable_pow_of_ae_nonneg_le_const ξ hC hX_nonneg hX_aemeas hX_le

theorem lambdaSqCoeffField_inv_pow_integrable_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam s : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (Q : TriadicCube d) (hs : 0 < s) (ξ : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ ξ) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := uniformLowerInvBlockConst d lam
  have hC : 0 ≤ C := by
    simpa [C] using uniformLowerInvBlockConst_nonneg hUE.lam_pos
  have hX_nonneg :
      ∀ a : RegCoeffField d, 0 ≤ (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ :=
    fun a => inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hX_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs
  have hX_le :
      (fun a : RegCoeffField d =>
          (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹)
        ≤ᵐ[P] fun _ => C := by
    filter_upwards [hUE.aee_elliptic] with a ha
    simpa [C] using
      lambdaSqCoeffField_finite_one_inv_le_of_uniformEllipticitySample
        Q a hUE.lam_pos hUE.lam_le_Lam ha hs
  exact integrable_pow_of_ae_nonneg_le_const ξ hC hX_nonneg hX_aemeas hX_le

private theorem annealedMomentRoot_const_one
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} (_hξ : 1 ≤ ξ) :
    Ch04.annealedMomentRoot P ξ (fun _ : RegCoeffField d => 1) = 1 := by
  simp [Ch04.annealedMomentRoot]

theorem LambdaMomentAtScale_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam s : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (n : ℤ) (hs : 0 < s) {ξ : ℕ} (hξ : 1 ≤ ξ) :
    Ch04.LambdaMomentAtScale P n s ξ ≤
      uniformUpperBlockConst d lam Lam := by
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := uniformUpperBlockConst d lam Lam
  have hC : 0 ≤ C := by
    simpa [C] using uniformUpperBlockConst_nonneg hUE.lam_pos hUE.lam_le_Lam
  let X : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d n) s (.finite 1) a
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d n) a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hY_nonneg : ∀ a : RegCoeffField d, 0 ≤ (1 : ℝ) := fun _ => by norm_num
  have hX_aemeas : AEMeasurable X P := by
    simpa [X] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d n) hs
  have hY_abs_int :
      Integrable (fun a : RegCoeffField d => |(1 : ℝ)| ^ ξ) P := by
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), one_pow] using
      (integrable_const (1 : ℝ) :
        Integrable (fun _ : RegCoeffField d => (1 : ℝ)) P)
  have hXY : X ≤ᵐ[P] fun _ : RegCoeffField d => C * (1 : ℝ) := by
    filter_upwards [hUE.aee_elliptic] with a ha
    simpa [X, C] using
      LambdaSqCoeffField_finite_one_le_of_uniformEllipticitySample
        (originCube d n) a hUE.lam_pos hUE.lam_le_Lam ha hs
  have hroot :=
    Section52.section52_annealedMomentRoot_le_const_mul_of_ae_le
      (P := P) (ξ := ξ) (c := C) (X := X)
      (Y := fun _ : RegCoeffField d => 1)
      hξ hC hX_nonneg hY_nonneg hX_aemeas hY_abs_int hXY
  calc
    Ch04.LambdaMomentAtScale P n s ξ =
        Ch04.annealedMomentRoot P ξ X := by rfl
    _ ≤ C * Ch04.annealedMomentRoot P ξ (fun _ : RegCoeffField d => 1) := hroot
    _ = C := by rw [annealedMomentRoot_const_one (P := P) hξ]; ring

theorem lambdaInvMomentAtScale_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam s : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (n : ℤ) (hs : 0 < s) {ξ : ℕ} (hξ : 1 ≤ ξ) :
    Ch04.lambdaInvMomentAtScale P n s ξ ≤
      uniformLowerInvBlockConst d lam := by
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := uniformLowerInvBlockConst d lam
  have hC : 0 ≤ C := by
    simpa [C] using uniformLowerInvBlockConst_nonneg hUE.lam_pos
  let X : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d n) s (.finite 1) a)⁻¹
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d n) a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hY_nonneg : ∀ a : RegCoeffField d, 0 ≤ (1 : ℝ) := fun _ => by norm_num
  have hX_aemeas : AEMeasurable X P := by
    simpa [X] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d n) hs
  have hY_abs_int :
      Integrable (fun a : RegCoeffField d => |(1 : ℝ)| ^ ξ) P := by
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), one_pow] using
      (integrable_const (1 : ℝ) :
        Integrable (fun _ : RegCoeffField d => (1 : ℝ)) P)
  have hXY : X ≤ᵐ[P] fun _ : RegCoeffField d => C * (1 : ℝ) := by
    filter_upwards [hUE.aee_elliptic] with a ha
    simpa [X, C] using
      lambdaSqCoeffField_finite_one_inv_le_of_uniformEllipticitySample
        (originCube d n) a hUE.lam_pos hUE.lam_le_Lam ha hs
  have hroot :=
    Section52.section52_annealedMomentRoot_le_const_mul_of_ae_le
      (P := P) (ξ := ξ) (c := C) (X := X)
      (Y := fun _ : RegCoeffField d => 1)
      hξ hC hX_nonneg hY_nonneg hX_aemeas hY_abs_int hXY
  calc
    Ch04.lambdaInvMomentAtScale P n s ξ =
        Ch04.annealedMomentRoot P ξ X := by rfl
    _ ≤ C * Ch04.annealedMomentRoot P ξ (fun _ : RegCoeffField d => 1) := hroot
    _ = C := by rw [annealedMomentRoot_const_one (P := P) hξ]; ring

theorem originBlockIntegrableAtScale_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam sUpper sLower : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {ξ : ℕ} (hξ : 1 ≤ ξ) (n : ℕ) :
    Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P := by
  exact
    hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
      (originCube d (n : ℤ)) hsUpper hsLower hξ
      (LambdaSqCoeffField_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsUpper ξ)
      (lambdaSqCoeffField_inv_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsLower ξ)

theorem barSigmaAtScale_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam sUpper sLower : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {ξ : ℕ} (hξ : 1 ≤ ξ) (n : ℕ) :
    hP.barSigmaAtScale hStruct (n : ℤ) ≤
      uniformUpperBlockConst d lam Lam := by
  have hBlock :
      ∀ n : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    originBlockIntegrableAtScale_of_uniformEllipticityBounds
      hP hUE hsUpper hsLower hξ
  have hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^
              ξ) P :=
    fun n =>
      LambdaSqCoeffField_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsUpper ξ
  have hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^
              ξ) P :=
    fun n =>
      lambdaSqCoeffField_inv_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsLower ξ
  have hbar :
      hP.barSigmaAtScale hStruct (n : ℤ) ≤
        Ch04.LambdaMomentAtScale P (n : ℤ) sUpper ξ :=
    hP.barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
      hStruct hsUpper hsLower hξ hBlock
      (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (n : ℤ)) hsUpper)
      (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (n : ℤ)) hsLower)
      hUpperPowInt hLowerPowInt n
  exact hbar.trans
    (LambdaMomentAtScale_le_of_uniformEllipticityBounds
      hP hUE (n : ℤ) hsUpper hξ)

theorem barSigmaStarAtScale_inv_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam sUpper sLower : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {ξ : ℕ} (hξ : 1 ≤ ξ) (n : ℕ) :
    (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ ≤
      uniformLowerInvBlockConst d lam := by
  have hBlock :
      ∀ n : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    originBlockIntegrableAtScale_of_uniformEllipticityBounds
      hP hUE hsUpper hsLower hξ
  have hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^
              ξ) P :=
    fun n =>
      LambdaSqCoeffField_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsUpper ξ
  have hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^
              ξ) P :=
    fun n =>
      lambdaSqCoeffField_inv_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (n : ℤ)) hsLower ξ
  have hstar :
      (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P (n : ℤ) sLower ξ :=
    hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
      hStruct hsUpper hsLower hξ hBlock
      (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (n : ℤ)) hsUpper)
      (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (n : ℤ)) hsLower)
      hUpperPowInt hLowerPowInt n
  exact hstar.trans
    (lambdaInvMomentAtScale_le_of_uniformEllipticityBounds
      hP hUE (n : ℤ) hsLower hξ)

theorem barSigmaAtScale_pos_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam sUpper sLower : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {ξ : ℕ} (hξ : 1 ≤ ξ) (n : ℕ) :
    0 < hP.barSigmaAtScale hStruct (n : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    originBlockIntegrableAtScale_of_uniformEllipticityBounds
      hP hUE hsUpper hsLower hξ n
  exact hP.barSigmaAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
    hStruct hBlock

private theorem barSigmaStarAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (n : ℕ)
    (hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P) :
    0 < hP.barSigmaStarAtScale hStruct (n : ℤ) := by
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (n : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (n : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (n : ℤ)]
  exact inv_pos.mpr hInv

private theorem barSigmaStarAtScale_le_barSigmaAtScale_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (n : ℕ)
    (hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
      hP.barSigmaAtScale hStruct (n : ℤ) := by
  let b := hP.barSigmaAtScale hStruct (n : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (n : ℤ)
  have hc_pos : 0 < c := by
    simpa [c] using
      barSigmaStarAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct n hBlock
  have htheta : 1 ≤ b * c⁻¹ := by
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b, c] using
      Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct (n : ℤ) hBlock
  calc
    hP.barSigmaStarAtScale hStruct (n : ℤ) = c := rfl
    _ = c * 1 := by ring
    _ ≤ c * (b * c⁻¹) := mul_le_mul_of_nonneg_left htheta hc_pos.le
    _ = b := by field_simp [hc_pos.ne']
    _ = hP.barSigmaAtScale hStruct (n : ℤ) := rfl

theorem barSigmaAtScale_inv_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam sUpper sLower : ℝ} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hUE : UniformEllipticityBounds P lam Lam)
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {ξ : ℕ} (hξ : 1 ≤ ξ) (n : ℕ) :
    (hP.barSigmaAtScale hStruct (n : ℤ))⁻¹ ≤
      uniformLowerInvBlockConst d lam := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    originBlockIntegrableAtScale_of_uniformEllipticityBounds
      hP hUE hsUpper hsLower hξ n
  have hb_pos :
      0 < hP.barSigmaAtScale hStruct (n : ℤ) :=
    hP.barSigmaAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
      hStruct hBlock
  have hc_pos :
      0 < hP.barSigmaStarAtScale hStruct (n : ℤ) :=
    barSigmaStarAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct n hBlock
  have hc_le_b :
      hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
        hP.barSigmaAtScale hStruct (n : ℤ) :=
    barSigmaStarAtScale_le_barSigmaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct n hBlock
  have hb_inv_le_hc_inv :
      (hP.barSigmaAtScale hStruct (n : ℤ))⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ :=
    (inv_le_inv₀ hb_pos hc_pos).2 hc_le_b
  exact hb_inv_le_hc_inv.trans
    (barSigmaStarAtScale_inv_le_of_uniformEllipticityBounds
      hP hStruct hUE hsUpper hsLower hξ n)

/-- Deterministic endpoint size produced by uniform ellipticity. -/
noncomputable def mainResultsThetaHat (d : ℕ) (lam Lam : ℝ) : ℝ :=
  1 +
    uniformLowerInvBlockConst d lam * uniformUpperBlockConst d lam Lam +
      uniformUpperBlockConst d lam Lam * uniformLowerInvBlockConst d lam

theorem mainResultsThetaHat_pos {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    0 < mainResultsThetaHat d lam Lam := by
  have hUpper : 0 ≤ uniformUpperBlockConst d lam Lam :=
    uniformUpperBlockConst_nonneg hlam hle
  have hLower : 0 ≤ uniformLowerInvBlockConst d lam :=
    uniformLowerInvBlockConst_nonneg hlam
  have hprod₁ :
      0 ≤ uniformLowerInvBlockConst d lam * uniformUpperBlockConst d lam Lam :=
    mul_nonneg hLower hUpper
  have hprod₂ :
      0 ≤ uniformUpperBlockConst d lam Lam * uniformLowerInvBlockConst d lam :=
    mul_nonneg hUpper hLower
  unfold mainResultsThetaHat
  linarith

/-- Uniform ellipticity bounds the normalized unit-cube `Γ_∞` observable
almost surely. -/
theorem gammaSigmaUnitEllipticityObservable_le_of_uniformEllipticityBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {lam Lam : ℝ}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hUE : UniformEllipticityBounds P lam Lam)
    {sUpper sLower : ℝ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) :
    gammaSigmaUnitEllipticityObservable hP hStruct sUpper sLower
      ≤ᵐ[P] fun _ => mainResultsThetaHat d lam Lam := by
  let CU : ℝ := uniformUpperBlockConst d lam Lam
  let CI : ℝ := uniformLowerInvBlockConst d lam
  let b : ℝ := hP.barSigmaAtScale hStruct (0 : ℤ)
  have hCU : 0 ≤ CU := by
    simpa [CU] using uniformUpperBlockConst_nonneg hUE.lam_pos hUE.lam_le_Lam
  have hCI : 0 ≤ CI := by
    simpa [CI] using uniformLowerInvBlockConst_nonneg hUE.lam_pos
  have hb_pos : 0 < b := by
    simpa [b] using
      barSigmaAtScale_pos_of_uniformEllipticityBounds
        hP hStruct hUE hsUpper hsLower (by norm_num : 1 ≤ (1 : ℕ)) 0
  have hb_le : b ≤ CU := by
    simpa [b, CU] using
      barSigmaAtScale_le_of_uniformEllipticityBounds
        hP hStruct hUE hsUpper hsLower (by norm_num : 1 ≤ (1 : ℕ)) 0
  have hb_inv_le : b⁻¹ ≤ CI := by
    simpa [b, CI] using
      barSigmaAtScale_inv_le_of_uniformEllipticityBounds
        hP hStruct hUE hsUpper hsLower (by norm_num : 1 ≤ (1 : ℕ)) 0
  filter_upwards [hUE.aee_elliptic] with a ha
  let L : ℝ := Ch04.LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a
  let Linv : ℝ := (Ch04.lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using
      Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hsUpper
        (by norm_num : (1 : ℝ) ≤ 1)
  have hLinv_nonneg : 0 ≤ Linv := by
    simpa [Linv] using
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hsLower
          (by norm_num : (1 : ℝ) ≤ 1))
  have hL_le : L ≤ CU := by
    simpa [L, CU] using
      LambdaSqCoeffField_finite_one_le_of_uniformEllipticitySample
        (originCube d 0) a hUE.lam_pos hUE.lam_le_Lam ha hsUpper
  have hLinv_le : Linv ≤ CI := by
    simpa [Linv, CI] using
      lambdaSqCoeffField_finite_one_inv_le_of_uniformEllipticitySample
        (originCube d 0) a hUE.lam_pos hUE.lam_le_Lam ha hsLower
  have hUpperTerm : b⁻¹ * L ≤ CI * CU :=
    mul_le_mul hb_inv_le hL_le hL_nonneg hCI
  have hLowerTerm : b * Linv ≤ CU * CI :=
    mul_le_mul hb_le hLinv_le hLinv_nonneg hCU
  have hsum : b⁻¹ * L + b * Linv ≤ CI * CU + CU * CI :=
    add_le_add hUpperTerm hLowerTerm
  have htheta :
      CI * CU + CU * CI ≤ mainResultsThetaHat d lam Lam := by
    unfold mainResultsThetaHat
    dsimp [CU, CI]
    linarith
  calc
    gammaSigmaUnitEllipticityObservable hP hStruct sUpper sLower a =
        b⁻¹ * L + b * Linv := by
          simp [gammaSigmaUnitEllipticityObservable, b, L, Linv, hb_pos]
    _ ≤ CI * CU + CU * CI := hsum
    _ ≤ mainResultsThetaHat d lam Lam := htheta

namespace UniformEllipticityBounds

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {lam Lam : ℝ}

/-- Uniform ellipticity supplies the older Chapter 5 `(P4)` package for any
admissible parameter record. -/
noncomputable def toQuantitativeCoarseGrainedEllipticity
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    QuantitativeCoarseGrainedEllipticity P where
  sUpper := params.sUpper
  sLower := params.sLower
  xi := params.xi
  two_le_dim := params.two_le_dim
  sUpper_nonneg := params.sUpper_nonneg
  sUpper_lt_one := params.sUpper_lt_one
  sLower_nonneg := params.sLower_nonneg
  sLower_lt_one := params.sLower_lt_one
  xi_gt_two_mul_dim := params.xi_gt_two_mul_dim
  sum_lt_one := params.sum_lt_one
  dim_div_xi_lt_min := params.dim_div_xi_lt_min
  upper_moment_integrable := by
    simpa using
      LambdaSqCoeffField_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (0 : ℤ)) params.sUpper_pos params.xi
  lower_inv_moment_integrable := by
    simpa using
      lambdaSqCoeffField_inv_pow_integrable_of_uniformEllipticityBounds
        hP hUE (originCube d (0 : ℤ)) params.sLower_pos params.xi

@[simp]
theorem toQuantitativeCoarseGrainedEllipticity_params
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hUE.toQuantitativeCoarseGrainedEllipticity hP params).params = params := by
  rfl

/-- Uniform ellipticity gives the `σ = ∞` endpoint with the older quantitative
parameter record. -/
noncomputable def toGammaInfinityCoarseGrainedEllipticity
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    GammaInfinityCoarseGrainedEllipticity P hP hStruct where
  params := params
  thetaHat := mainResultsThetaHat d lam Lam
  thetaHat_pos := mainResultsThetaHat_pos hUE.lam_pos hUE.lam_le_Lam
  bound := by
    simpa using
      gammaSigmaUnitEllipticityObservable_le_of_uniformEllipticityBounds
        hP hStruct hUE params.sUpper_pos params.sLower_pos

@[simp]
theorem toGammaInfinityCoarseGrainedEllipticity_params
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hUE.toGammaInfinityCoarseGrainedEllipticity hP hStruct params).params =
      params := rfl

/-- Uniform ellipticity gives the manuscript-facing `σ = ∞` endpoint with no
exposed finite moment exponent. -/
noncomputable def toGammaInfinityCoarseGrainedEllipticityNoXi
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : GammaCoarseGrainedEllipticityParams d) :
    GammaInfinityCoarseGrainedEllipticityNoXi P hP hStruct where
  params := params
  thetaHat := mainResultsThetaHat d lam Lam
  thetaHat_pos := mainResultsThetaHat_pos hUE.lam_pos hUE.lam_le_Lam
  bound := by
    simpa using
      gammaSigmaUnitEllipticityObservable_le_of_uniformEllipticityBounds
        hP hStruct hUE params.sUpper_pos params.sLower_pos

@[simp]
theorem toGammaInfinityCoarseGrainedEllipticityNoXi_params
    (hUE : UniformEllipticityBounds P lam Lam)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (params : GammaCoarseGrainedEllipticityParams d) :
    (hUE.toGammaInfinityCoarseGrainedEllipticityNoXi hP hStruct params).params =
      params := rfl

end UniformEllipticityBounds

end

end Section57
end Ch05
end Book
end Homogenization
