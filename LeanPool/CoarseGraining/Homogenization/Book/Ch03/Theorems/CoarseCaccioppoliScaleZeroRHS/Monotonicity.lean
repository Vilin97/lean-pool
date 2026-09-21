/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroRHS

/-! # Monotonicity -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli RHS monotonicity helpers

This child file contains the scalar monotonicity lemmas which let the
scale-zero bridge enlarge public Caccioppoli RHS constants.

## Audit tag

Claim: if a public RHS constant is enlarged after multiplication by a
dimension-only factor, the boundary and centered-interior scale-zero RHS terms
enlarge accordingly.

Downstream target: `CoarseCaccioppoliScaleZeroBridge.lean`.  This file is
internal bridge plumbing only and introduces no public `*Theory` surface.
-/

noncomputable section

open scoped ENNReal

private theorem rhs_const_mul_rpow_le_rpow_of_mul_le
    {M x y p : ℝ} (hM : 1 ≤ M) (hx : 0 ≤ x) (hMxy : M * x ≤ y)
    (hp : 1 ≤ p) :
    M * Real.rpow x p ≤ Real.rpow y p := by
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hMx_nonneg : 0 ≤ M * x := mul_nonneg hM_nonneg hx
  have hM_le_Mp : M ≤ Real.rpow M p := by
    simpa using Real.self_le_rpow_of_one_le hM hp
  have hxpow_nonneg : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx p
  have hleft : M * Real.rpow x p ≤ Real.rpow M p * Real.rpow x p :=
    mul_le_mul_of_nonneg_right hM_le_Mp hxpow_nonneg
  have hmul_rpow : Real.rpow M p * Real.rpow x p = Real.rpow (M * x) p :=
    (Real.mul_rpow hM_nonneg hx).symm
  calc
    M * Real.rpow x p ≤ Real.rpow M p * Real.rpow x p := hleft
    _ = Real.rpow (M * x) p := hmul_rpow
    _ ≤ Real.rpow y p :=
      Real.rpow_le_rpow hMx_nonneg hMxy (by linarith)

private theorem caccioppoliPrefactor_mul_const_le_of_mul_constant_le
    {d : ℕ} [NeZero d] {M C₁ C₂ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    M * caccioppoliPrefactor C₁ Q a s t ≤
      caccioppoliPrefactor C₂ Q a s t := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let F : ℝ :=
    Real.rpow s (-(2 * s / σ)) *
      Real.rpow (Ch02.ThetaRatio Q s t a) (s / σ) *
      Ch02.LambdaS Q s a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  have hp_ge_one : 1 ≤ p := by
    have hdiv_nonneg : 0 ≤ 4 * s / σ := by positivity
    dsimp [p]
    linarith
  have hbase_nonneg : 0 ≤ C₁ / σ := div_nonneg hC₁ hσ_pos.le
  have hbase_le : M * (C₁ / σ) ≤ C₂ / σ := by
    calc
      M * (C₁ / σ) = (M * C₁) / σ := by ring
      _ ≤ C₂ / σ := div_le_div_of_nonneg_right hMC₁C₂ hσ_pos.le
  have hpow :
      M * Real.rpow (C₁ / σ) p ≤ Real.rpow (C₂ / σ) p :=
    rhs_const_mul_rpow_le_rpow_of_mul_le hM hbase_nonneg hbase_le hp_ge_one
  have htheta_nonneg : 0 ≤ Ch02.ThetaRatio Q s t a :=
    Ch02.ThetaRatio_nonneg Q a hs ht
  have hLambda_nonneg : 0 ≤ Ch02.LambdaS Q s a := by
    unfold Ch02.LambdaS
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hscale_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg htheta_nonneg _))
        hLambda_nonneg)
      hscale_nonneg
  calc
    M * caccioppoliPrefactor C₁ Q a s t =
        (M * Real.rpow (C₁ / σ) p) * F := by
      simp [F, p, σ, caccioppoliPrefactor, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.rpow (C₂ / σ) p * F :=
      mul_le_mul_of_nonneg_right hpow hF_nonneg
    _ = caccioppoliPrefactor C₂ Q a s t := by
      simp [F, p, σ, caccioppoliPrefactor, mul_assoc, mul_left_comm, mul_comm]

theorem boundaryCaccioppoliRHS_mul_const_le_of_mul_constant_le
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t M C₁ C₂ : ℝ}
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    M * boundaryCaccioppoliRHS C₁ s t u ≤
      boundaryCaccioppoliRHS C₂ s t u := by
  have hu :
      0 ≤ boundaryCaccioppoliParentL2Sq u := by
    rw [boundaryCaccioppoliParentL2Sq_eq_harmonicL2Sq_pointwise u]
    exact
      coarseCaccioppoliHarmonicL2Sq_nonneg Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic
  have hpref :
      M * caccioppoliPrefactor C₁ Q a s t ≤
        caccioppoliPrefactor C₂ Q a s t :=
    caccioppoliPrefactor_mul_const_le_of_mul_constant_le
      (Q := Q) (a := a) (s := s) (t := t)
      (M := M) (C₁ := C₁) (C₂ := C₂)
      hM hC₁ hMC₁C₂ hs ht hst
  calc
    M * boundaryCaccioppoliRHS C₁ s t u =
        (M * caccioppoliPrefactor C₁ Q a s t) *
          boundaryCaccioppoliParentL2Sq u := by
      simp [boundaryCaccioppoliRHS, mul_assoc]
    _ ≤ caccioppoliPrefactor C₂ Q a s t *
          boundaryCaccioppoliParentL2Sq u := by
      exact mul_le_mul_of_nonneg_right hpref hu
    _ = boundaryCaccioppoliRHS C₂ s t u := by
      simp [boundaryCaccioppoliRHS]

theorem interiorCaccioppoliRHS_mul_const_le_of_mul_constant_le
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t M C₁ C₂ : ℝ}
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    M * interiorCaccioppoliRHS C₁ Q a s t u ≤
      interiorCaccioppoliRHS C₂ Q a s t u := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hu :
      0 ≤ interiorCaccioppoliParentOscillationL2Sq Q a u := by
    rw [interiorCaccioppoliParentOscillationL2Sq_eq_harmonicL2Sq_pointwise_normalizeMeanZero
      (Q := Q) (a := a) u]
    exact
      coarseCaccioppoliHarmonicL2Sq_nonneg Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic.normalizeMeanZero
  have hpref :
      M * caccioppoliPrefactor C₁ Q a s t ≤
        caccioppoliPrefactor C₂ Q a s t :=
    caccioppoliPrefactor_mul_const_le_of_mul_constant_le
      (Q := Q) (a := a) (s := s) (t := t)
      (M := M) (C₁ := C₁) (C₂ := C₂)
      hM hC₁ hMC₁C₂ hs ht hst
  calc
    M * interiorCaccioppoliRHS C₁ Q a s t u =
        (M * caccioppoliPrefactor C₁ Q a s t) *
          interiorCaccioppoliParentOscillationL2Sq Q a u := by
      simp [interiorCaccioppoliRHS, mul_assoc]
    _ ≤
        caccioppoliPrefactor C₂ Q a s t *
          interiorCaccioppoliParentOscillationL2Sq Q a u := by
      exact mul_le_mul_of_nonneg_right hpref hu
    _ = interiorCaccioppoliRHS C₂ Q a s t u := by
      simp [interiorCaccioppoliRHS]

end

end Ch03
end Book
end Homogenization
