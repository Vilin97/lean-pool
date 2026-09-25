/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSScalar

/-! # Public RHSMonotonicity -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public RHS monotonicity for coarse Caccioppoli with RHS

This file contains the scalar constant-enlargement lemmas for the public
boundary Caccioppoli RHS with forcing.

## Audit tag

Claim: increasing the displayed public RHS constants increases the homogeneous
and forced Caccioppoli prefactors, and therefore the full public with-RHS
boundary quantity.

Downstream target: `CoarseCaccioppoliRHS/FinalBounds.lean`.  This is scalar
bridge plumbing only and introduces no public `*Theory` package.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- The homogeneous Caccioppoli prefactor is nonnegative in the theorem range.
-/
theorem caccioppoliPrefactor_nonneg
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ caccioppoliPrefactor C Q a s t := by
  rw [caccioppoliPrefactor_eq_caccioppoliWithRHSPrefactor_mul_lambdaS_scale
    (C := C) (Q := Q) (a := a) hs ht hst]
  have hP :
      0 ≤ caccioppoliWithRHSPrefactor C Q a s t :=
    caccioppoliWithRHSPrefactor_nonneg hC_nonneg hs ht hst
  have hlambda : 0 ≤ Ch02.lambdaS Q t a := by
    unfold Ch02.lambdaS
    exact (Ch02.lambdaSq_finite_pos Q a ht
      (by norm_num : (1 : ℝ) ≤ 1)).le
  have hscale :
      0 ≤ Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  exact mul_nonneg hP (mul_nonneg hlambda hscale)

/-- If the base constant is enlarged by a multiplicative factor, then the
corresponding real-power factor absorbs one copy of that factor. -/
theorem rhs_const_mul_rpow_le_rpow_of_mul_le {M x y p : ℝ}
    (hM : 1 ≤ M) (hx : 0 ≤ x) (hMxy : M * x ≤ y) (hp : 1 ≤ p) :
    M * Real.rpow x p ≤ Real.rpow y p := by
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM
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

/-- Multiplicative enlargement of the dimension constant absorbs the same
constant multiple of the homogeneous Caccioppoli prefactor. -/
theorem caccioppoliPrefactor_mul_const_le_of_mul_constant_le
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

/-- Multiplicative enlargement also absorbs the same constant multiple of the
forced Caccioppoli prefactor. -/
theorem caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
    {d : ℕ} [NeZero d] {M C₁ C₂ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    M * caccioppoliWithRHSPrefactor C₁ Q a s t ≤
      caccioppoliWithRHSPrefactor C₂ Q a s t := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let eθ : ℝ := (1 - t) / σ
  let F : ℝ :=
    Real.rpow s (-(2 * s / σ)) *
      Real.rpow (Ch02.ThetaRatio Q s t a) eθ
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
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg htheta_nonneg _)
  calc
    M * caccioppoliWithRHSPrefactor C₁ Q a s t =
        (M * Real.rpow (C₁ / σ) p) * F := by
      simp [F, p, eθ, σ, caccioppoliWithRHSPrefactor,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.rpow (C₂ / σ) p * F :=
      mul_le_mul_of_nonneg_right hpow hF_nonneg
    _ = caccioppoliWithRHSPrefactor C₂ Q a s t := by
      simp [F, p, eθ, σ, caccioppoliWithRHSPrefactor,
        mul_assoc, mul_left_comm, mul_comm]

/-- Multiplicative enlargement of the public constant absorbs the same
constant multiple of the entire displayed forced RHS. -/
theorem boundaryCaccioppoliWithRHSRHS_mul_const_le_of_mul_constant_le
    {d : ℕ} [NeZero d] {M C₁ C₂ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    M * boundaryCaccioppoliWithRHSRHS C₁ s t u ≤
      boundaryCaccioppoliWithRHSRHS C₂ s t u := by
  let P₁ : ℝ := caccioppoliWithRHSPrefactor C₁ Q a s t
  let P₂ : ℝ := caccioppoliWithRHSPrefactor C₂ Q a s t
  let A : ℝ :=
    Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      boundaryForcedCaccioppoliParentL2Sq u
  let B : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP :
      M * P₁ ≤ P₂ := by
    dsimp [P₁, P₂]
    exact caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      hM hC₁ hMC₁C₂ hs ht hst
  have hA_nonneg : 0 ≤ A := by
    have hlambda : 0 ≤ Ch02.lambdaS Q t a := by
      unfold Ch02.lambdaS
      exact (Ch02.lambdaSq_finite_pos Q a ht
        (by norm_num : (1 : ℝ) ≤ 1)).le
    have hscale :
        0 ≤ Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hparent :
        0 ≤ boundaryForcedCaccioppoliParentL2Sq u :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) u.toH1.toFun
        (measurableSet_openCubeSet Q)
    dsimp [A]
    exact mul_nonneg (mul_nonneg hlambda hscale) hparent
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA_nonneg hB_nonneg
  calc
    M * boundaryCaccioppoliWithRHSRHS C₁ s t u =
        (M * P₁) * (A + B) := by
          dsimp [P₁, A, B]
          unfold boundaryCaccioppoliWithRHSRHS
          ring_nf
          simp [mul_left_comm, mul_comm]
    _ ≤ P₂ * (A + B) := mul_le_mul_of_nonneg_right hP hsum_nonneg
    _ = boundaryCaccioppoliWithRHSRHS C₂ s t u := by
          rfl

end

end Ch03
end Book
end Homogenization
