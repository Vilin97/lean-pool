/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.FinalBounds

/-! # Bridges -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Internal Parent-L2 Bounds for Coarse Caccioppoli with RHS

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: prove the parent-`L²` estimate for the zero-trace corrector and expose
only the raw bound consumed by the public theorem package.

Downstream target: `CoarseCaccioppoliRHS/Theory.lean`.  This file should not
spawn public bridge packages or parallel theorem theories.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Analytic bridge needed to finish the boundary Caccioppoli estimate with
right-hand side.

All decomposition and scalar absorption steps in this file reduce the final
public theorem to this dimension-only estimate for the zero-trace corrector.
The bridge is intentionally stated with the coarse lower ellipticity
`lambdaS`, not with the raw witness constants stored in `CoeffOn`. -/
private structure CoarseCaccioppoliRHSParentL2Bridge
    (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) ρ).toH1Function.toFun ≤
            K *
              ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)

/-- Zero-trace value estimate needed for the faithful proof of the corrector
parent `L²` bridge.

This is the analytic replacement for the manuscript's ordinary Poincare plus
uniform-ellipticity line.  It controls the full zero-trace value on the parent
cube by the public negative-Besov norm of its gradient, with the expected
`(1 - 2t)^{-1}` scale summation loss and no raw `CoeffOn` constants. -/
private structure CoarseCaccioppoliRHSZeroTraceValueBridge
    (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t < 1 / 2 →
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) ρ).toH1Function.toFun ≤
            C * (1 - 2 * t)⁻¹ *
              (scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
                (fun x => ρ.toH10.toH1Function.grad x)) ^ 2

/-- Proved zero-trace value bridge for the forced Caccioppoli corrector.

The proof uses only the coarse negative-Besov gradient norm.  It combines the
top-scale zero-trace value estimate above with the public normalization
identities, then spends the geometric summation loss as `(1 - 2t)^{-1}`. -/
private theorem coarseCaccioppoliRHSZeroTraceValueBridge
    {d : ℕ} [NeZero d] :
    CoarseCaccioppoliRHSZeroTraceValueBridge d := by
  let Kd : ℝ := (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ) +
    2 * (3 : ℝ) ^ ((d : ℝ) + 1)
  let C : ℝ := 5 * Kd ^ 2 + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith [sq_nonneg Kd]
  refine ⟨⟨C, hC_pos, ?_⟩⟩
  intro Q a t g ρ ht ht_lt
  let f : Vec d → ℝ := fun x => ρ.toH10.toH1Function.toFun x
  let F : Vec d → Vec d := fun x => ρ.toH10.toH1Function.grad x
  let W : ℝ := cubeBesovScaleWeight (1 : ℝ) Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) f
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q (2 * t) F
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹)
  have hvalue :=
    cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      (Q := Q) (t := t) ρ.toH10 ht ht_lt
  have hvalue' : W * L ≤ (Kd * G) * N := by
    dsimp [W, L, N, G, Kd, f, F]
    exact hvalue
  have hWL_nonneg : 0 ≤ W * L := by
    exact mul_nonneg (by dsimp [W]; exact cubeBesovScaleWeight_nonneg 1 Q)
      (by dsimp [L]; exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f)
  have hvalue_sq : (W * L) ^ 2 ≤ ((Kd * G) * N) ^ 2 :=
    pow_le_pow_left₀ hWL_nonneg hvalue' 2
  have hscale2 :
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = W ^ 2 := by
    dsimp [W]
    calc
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))
          =
        cubeBesovScaleWeight (2 : ℝ) Q := by
          simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
      _ = cubeBesovScaleWeight (1 : ℝ) Q *
            cubeBesovScaleWeight (1 : ℝ) Q := by
          rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
          norm_num
      _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by
          ring
  have hnorm_eq :
      normalizedL2SqOnSet (openCubeSet Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun = L ^ 2 := by
    have hmem : MeasureTheory.MemLp
        (fun x =>
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) ρ).toH1Function.memL2_normalizedCubeMeasure
    have h := normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q
      (fun x =>
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function.toFun x) hmem
    dsimp [L, f]
    simpa [boundaryForcedCaccioppoliCorrectorOpenH10_toFun] using h
  have hr : 0 < 1 - 2 * t := by linarith
  have hr_le : 1 - 2 * t ≤ 1 := by linarith
  have hpow_lt_one : Real.rpow (3 : ℝ) (-(1 - 2 * t)) < 1 := by
    simpa [Real.rpow_eq_pow] using
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith : -(1 - 2 * t) < 0)
  have hden_pos : 0 < 1 - Real.rpow (3 : ℝ) (-(1 - 2 * t)) := by
    linarith
  have harg : -2 * ((1 / 2 : ℝ) - t) = -(1 - 2 * t) := by ring
  have hinv_nonneg_G :
      0 ≤ (1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹ := by
    rw [harg]
    exact inv_nonneg.mpr hden_pos.le
  have hG_sq : G ^ 2 ≤ 5 * (1 - 2 * t)⁻¹ := by
    have hs := Ch02.inv_one_sub_rpow_three_neg_le_five_inv hr hr_le
    calc
      G ^ 2 =
          (Real.sqrt
            ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹)) ^ 2 := by
          rfl
      _ = (1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹ :=
          Real.sq_sqrt hinv_nonneg_G
      _ = (1 - Real.rpow (3 : ℝ) (-(1 - 2 * t)))⁻¹ := by
          rw [harg]
      _ ≤ 5 * (1 - 2 * t)⁻¹ := hs
  have hN_sq_nonneg : 0 ≤ N ^ 2 := sq_nonneg N
  have hKd_sq_nonneg : 0 ≤ Kd ^ 2 := sq_nonneg Kd
  have hCcoef : 5 * Kd ^ 2 ≤ C := by
    dsimp [C]
    linarith
  have hrinv_nonneg : 0 ≤ (1 - 2 * t)⁻¹ := inv_nonneg.mpr hr.le
  have hsq_bound :
      ((Kd * G) * N) ^ 2 ≤ C * (1 - 2 * t)⁻¹ * N ^ 2 := by
    calc
      ((Kd * G) * N) ^ 2 = Kd ^ 2 * G ^ 2 * N ^ 2 := by
          ring
      _ ≤ Kd ^ 2 * (5 * (1 - 2 * t)⁻¹) * N ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hG_sq hKd_sq_nonneg) hN_sq_nonneg
      _ = (5 * Kd ^ 2) * (1 - 2 * t)⁻¹ * N ^ 2 := by
          ring
      _ ≤ C * (1 - 2 * t)⁻¹ * N ^ 2 := by
          have hcoef_scaled :
              (5 * Kd ^ 2) * (1 - 2 * t)⁻¹ ≤ C * (1 - 2 * t)⁻¹ :=
            mul_le_mul_of_nonneg_right hCcoef hrinv_nonneg
          exact mul_le_mul_of_nonneg_right hcoef_scaled hN_sq_nonneg
  have hN_eq :
      scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2) F = N := by
    dsimp [N, F]
    rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
  calc
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        normalizedL2SqOnSet (openCubeSet Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun
        = W ^ 2 * L ^ 2 := by
          rw [hscale2, hnorm_eq]
    _ = (W * L) ^ 2 := by
          ring
    _ ≤ ((Kd * G) * N) ^ 2 := hvalue_sq
    _ ≤ C * (1 - 2 * t)⁻¹ * N ^ 2 := hsq_bound
    _ =
      C * (1 - 2 * t)⁻¹ *
        (scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          (fun x => ρ.toH10.toH1Function.grad x)) ^ 2 := by
        rw [hN_eq]

/-- The zero-trace value bridge, together with the already-proved public RHS
Poincare theorem, supplies the coarse parent `L²` bridge needed by the final
Caccioppoli-with-RHS assembly. -/
private theorem coarseCaccioppoliRHSParentL2Bridge_of_zeroTraceValueBridge
    {d : ℕ} [NeZero d]
    (hvalue : CoarseCaccioppoliRHSZeroTraceValueBridge d) :
    CoarseCaccioppoliRHSParentL2Bridge d := by
  rcases hvalue.exists_constant with ⟨Cv, hCv_pos, hvalue_bound⟩
  rcases (coarsePoincareRHSTheory (d := d)).exists_constant with
    ⟨Cp, hCp_pos, hgrad_bound, henergy_bound⟩
  let H : ℝ := Cp ^ 2 + Cp
  let A : ℝ := (25 * Real.exp 4) ^ 2
  let K : ℝ := Cv * (H ^ 2 * A)
  have hCp_nonneg : 0 ≤ Cp := le_of_lt hCp_pos
  have hH_pos : 0 < H := by
    dsimp [H]
    nlinarith [sq_nonneg Cp]
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos hCv_pos (mul_pos (sq_pos_of_pos hH_pos) hA_pos)
  refine ⟨⟨K, hK_pos, ?_⟩⟩
  intro Q a t g ρ ht ht_lt hg
  let U : ForcedCubeSolution Q a g :=
    boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) ρ
  let V : ZeroTraceForcedCubeSolution Q a g :=
    boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution
      (Q := Q) (a := a) ρ
  let N : ℝ :=
    scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
      (fun x => ρ.toH10.toH1Function.grad x)
  let B : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let L₂ : ℝ := Ch02.lambdaSq Q t (.finite 2) a
  let L₁ : ℝ := Ch02.lambdaS Q t a
  let T : ℝ := Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B
  let F : ℝ := Real.rpow t (-8 : ℝ) * Real.rpow L₁ (-1 : ℝ) * B ^ 2
  have htwo_t_pos : 0 < 2 * t := by nlinarith
  have htwo_t_lt_one : 2 * t < 1 := by nlinarith
  have hL₁_nonneg : 0 ≤ L₁ := by
    dsimp [L₁]
    unfold Ch02.lambdaS
    exact (Ch02.lambdaSq_finite_pos Q a ht
      (by norm_num : (1 : ℝ) ≤ 1)).le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (Q := Q) (s := 2 * t) (g := g) hg
  have hL₂_nonneg : 0 ≤ L₂ := by
    dsimp [L₂]
    exact (Ch02.lambdaSq_finite_pos Q a ht
      (by norm_num : (1 : ℝ) ≤ 2)).le
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hL₂_nonneg _)) hB_nonneg
  have hgrad_eq :
      scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          (forcedSolutionGradientField U) = N := by
    change scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          ((boundaryForcedCaccioppoliCorrectorForcedCubeSolution
            (Q := Q) (a := a) ρ).toH1.grad) =
        scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          (fun x => ρ.toH10.toH1Function.grad x)
    rw [boundaryForcedCaccioppoliCorrectorForcedCubeSolution_grad]
  have hgrad_forced :
      scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          (forcedSolutionGradientField U) ≤
        coarsePoincareWithRHSGradientRHS Cp Q a (2 * t) g U :=
    hgrad_bound U htwo_t_pos htwo_t_lt_one hg
  have hgrad_raw :
      N ≤ coarsePoincareWithRHSGradientRHS Cp Q a (2 * t) g U := by
    rw [← hgrad_eq]
    exact hgrad_forced
  have henergy_forced :
      forcedSolutionEnergyNorm Q a U ≤
        zeroDirichletEnergyWithRHSRHS Cp Q a t g := by
    change forcedSolutionEnergyNorm Q a
        (boundaryForcedCaccioppoliCorrectorForcedCubeSolution
          (Q := Q) (a := a) ρ) ≤
      zeroDirichletEnergyWithRHSRHS Cp Q a t g
    rw [boundaryForcedCaccioppoliCorrectorForcedCubeSolution_energyNorm_eq]
    exact henergy_bound V ht ht_lt hg
  have hrhs_le_T :
      coarsePoincareWithRHSGradientRHS Cp Q a (2 * t) g U ≤ H * T := by
    dsimp [H, T, B, L₂]
    exact coarsePoincareWithRHSGradientRHS_le_corrector_forceScale
      (C := Cp) hCp_nonneg (Q := Q) (a := a) (t := t) (g := g)
      U ht ht_lt hg henergy_forced
  have hN_le : N ≤ H * T := hgrad_raw.trans hrhs_le_T
  have hN_forced_nonneg :
      0 ≤ scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
          (forcedSolutionGradientField U) := by
    rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
    exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q (2 * t)
      (forcedSolutionGradientField U)
      (forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove
        U htwo_t_pos)
  have hN_nonneg : 0 ≤ N := by
    rw [← hgrad_eq]
    exact hN_forced_nonneg
  have hN_sq : N ^ 2 ≤ (H * T) ^ 2 := by
    exact pow_le_pow_left₀ hN_nonneg hN_le 2
  have hscalar : L₁ * T ^ 2 ≤ A * F := by
    dsimp [L₁, T, L₂, A, F, B]
    exact lambdaS_mul_tpow_lambdaSqTwo_inv_sq_le_forceTime
      (Q := Q) (a := a) (t := t) (B := B) ht ht_lt
  have hgrad_sq : L₁ * N ^ 2 ≤ (H ^ 2 * A) * F := by
    calc
      L₁ * N ^ 2 ≤ L₁ * (H * T) ^ 2 :=
        mul_le_mul_of_nonneg_left hN_sq hL₁_nonneg
      _ = H ^ 2 * (L₁ * T ^ 2) := by ring
      _ ≤ H ^ 2 * (A * F) :=
        mul_le_mul_of_nonneg_left hscalar (sq_nonneg H)
      _ = (H ^ 2 * A) * F := by ring
  have hvalue0 :
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        Cv * (1 - 2 * t)⁻¹ * N ^ 2 := by
    dsimp [N]
    exact hvalue_bound ρ ht ht_lt
  have hden_pos : 0 < 1 - 2 * t := by linarith
  have hCv_den_nonneg : 0 ≤ Cv * (1 - 2 * t)⁻¹ := by
    exact mul_nonneg hCv_pos.le (inv_nonneg.mpr hden_pos.le)
  calc
    Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        normalizedL2SqOnSet (openCubeSet Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun ≤
      Cv * (1 - 2 * t)⁻¹ * (L₁ * N ^ 2) := by
        dsimp [L₁]
        calc
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) ρ).toH1Function.toFun =
            Ch02.lambdaS Q t a *
              (Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) ρ).toH1Function.toFun) := by ring
          _ ≤ Ch02.lambdaS Q t a *
                (Cv * (1 - 2 * t)⁻¹ * N ^ 2) :=
              mul_le_mul_of_nonneg_left hvalue0 hL₁_nonneg
          _ = Cv * (1 - 2 * t)⁻¹ *
                (Ch02.lambdaS Q t a * N ^ 2) := by ring
    _ ≤ Cv * (1 - 2 * t)⁻¹ * ((H ^ 2 * A) * F) :=
        mul_le_mul_of_nonneg_left hgrad_sq hCv_den_nonneg
    _ = K *
        ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
        dsimp [K, F, L₁, B]
        rw [div_eq_mul_inv]
        ring

/-- Proved coarse parent `L²` bound for the zero-trace corrector. -/
theorem zeroTraceCorrectorParentL2_le_forceScale
    {d : ℕ} [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) ρ).toH1Function.toFun ≤
            K *
              ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) :=
  (coarseCaccioppoliRHSParentL2Bridge_of_zeroTraceValueBridge
    coarseCaccioppoliRHSZeroTraceValueBridge).exists_constant

end

end Ch03
end Book
end Homogenization
