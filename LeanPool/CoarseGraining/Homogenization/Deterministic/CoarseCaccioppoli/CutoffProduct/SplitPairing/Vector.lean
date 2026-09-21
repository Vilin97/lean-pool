/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.CenteredProduct
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.SplitPairing.Scalar

/-! # Vector -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_note_terms_of_contDiff_component_vector_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    {Bu1 BuS Bavg Bcirc1 BcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hfluxNeg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu1)
    (hfluxNegS : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ BuS)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1) +
          cubeBesovScaleWeight 1 Q * Bavg) * BgConst)) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS) +
              cubeBesovScaleWeight s Q * Bavg) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  have hconst :=
    abs_cubeAverage_vecDot_cubeAverage_scalar_smul_le_collapsed_note_terms_of_contDiff_component_bound
      Q flux u ξ hB hflux hu hξLp hBgConst hBavg havg hfluxNeg1 hξ hderiv hBgConst_bound
  have hcent :=
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_note_terms_of_contDiff_component_vector_bound
      Q s flux u G ξ hB hs0 hs1 hflux hu hG hξLp hBgCent hBavg hC hBcircS havg
      hfluxNegS hproj hξ hderiv hGcirc1 hGcircS hBgCent_bound
  have hconstVecInfty :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) ∞ (normalizedCubeMeasure Q) := by
    simpa [Pi.smul_apply] using! hξLp.const_smul (cubeAverage Q u)
  have hconstVec2 :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hconstVecInfty.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hcentVec2 :
      MeasureTheory.MemLp (fun x => (u x - cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    simpa [cubeFluctuation] using!
      hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) huFluct
  have hfluxComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => flux x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp flux i hflux
  have hconstComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ((cubeAverage Q u) • ξ x) i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hconstVec2
  have hcentComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ((u x - cubeAverage Q u) • ξ x) i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hcentVec2
  have hIntConstComp :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => flux x i * (((cubeAverage Q u) • ξ x) i))
          (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (hfluxComp i).integrable_mul (hconstComp i)
  have hIntCentComp :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => flux x i * (((u x - cubeAverage Q u) • ξ x) i))
          (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (hfluxComp i).integrable_mul (hcentComp i)
  have hIntConst :
      MeasureTheory.Integrable
        (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))
        (normalizedCubeMeasure Q) := by
    simpa [vecDot] using
      (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hIntConstComp i))
  have hIntCent :
      MeasureTheory.Integrable
        (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))
        (normalizedCubeMeasure Q) := by
    simpa [vecDot] using
      (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hIntCentComp i))
  have hsplitFun :
      (fun x => vecDot (flux x) (u x • ξ x)) =
        (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x) +
          vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
    funext x
    calc
      vecDot (flux x) (u x • ξ x)
          = vecDot (flux x) (((cubeAverage Q u) + (u x - cubeAverage Q u)) • ξ x) := by
              congr 1
              ring_nf
      _ = vecDot (flux x) ((cubeAverage Q u) • ξ x + (u x - cubeAverage Q u) • ξ x) := by
            rw [add_smul]
      _ = vecDot (flux x) ((cubeAverage Q u) • ξ x) +
            vecDot (flux x) ((u x - cubeAverage Q u) • ξ x) := by
              simp [vecDot, Finset.sum_add_distrib, mul_add]
  have hsplit :
      cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x)) =
        cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
          cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
    calc
      cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))
          = ∫ x, vecDot (flux x) (u x • ξ x) ∂ normalizedCubeMeasure Q := by
              rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      _ = ∫ x,
            (vecDot (flux x) ((cubeAverage Q u) • ξ x) +
              vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))
            ∂ normalizedCubeMeasure Q := by
              exact congrArg (fun f => ∫ x, f x ∂ normalizedCubeMeasure Q) hsplitFun
      _ = ∫ x, vecDot (flux x) ((cubeAverage Q u) • ξ x) ∂ normalizedCubeMeasure Q +
            ∫ x, vecDot (flux x) ((u x - cubeAverage Q u) • ξ x) ∂ normalizedCubeMeasure Q := by
              rw [MeasureTheory.integral_add hIntConst hIntCent]
      _ = cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
            cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
              rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
                ← cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        = |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
            cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| := by
              rw [hsplit]
    _ ≤ |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))| +
          |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| := by
            exact abs_add_le _ _
    _ ≤
      (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1) +
            cubeBesovScaleWeight 1 Q * Bavg) * BgConst)) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS) +
              cubeBesovScaleWeight s Q * Bavg) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
            exact add_le_add hconst hcent

/-- Vector projected-Poincare version of the sharp split pairing estimate. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_contDiff_component_vector_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    {Bu1 BuS Bavg Bcirc1 BcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hfluxNeg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu1)
    (hfluxNegS : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ BuS)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1)) *
          BgConst) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS)) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  have hconst :=
    abs_cubeAverage_vecDot_cubeAverage_scalar_smul_le_collapsed_sharp_note_terms_of_contDiff_component_bound
      Q flux u ξ hB hflux hu hξLp hBgConst hfluxNeg1 hξ hderiv hBgConst_bound
  have hcent :=
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_contDiff_component_vector_bound
      Q s flux u G ξ hB hs0 hs1 hflux hu hG hξLp hBgCent hBavg hC hBcircS havg
      hfluxNegS hproj hξ hderiv hGcirc1 hGcircS hBgCent_bound
  have hconstVecInfty :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) ∞ (normalizedCubeMeasure Q) := by
    simpa [Pi.smul_apply] using! hξLp.const_smul (cubeAverage Q u)
  have hconstVec2 :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hconstVecInfty.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hcentVec2 :
      MeasureTheory.MemLp (fun x => (u x - cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    simpa [cubeFluctuation] using!
      hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) huFluct
  have hfluxComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => flux x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp flux i hflux
  have hconstComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ((cubeAverage Q u) • ξ x) i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hconstVec2
  have hcentComp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ((u x - cubeAverage Q u) • ξ x) i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hcentVec2
  have hIntConstComp :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => flux x i * (((cubeAverage Q u) • ξ x) i))
          (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (hfluxComp i).integrable_mul (hconstComp i)
  have hIntCentComp :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => flux x i * (((u x - cubeAverage Q u) • ξ x) i))
          (normalizedCubeMeasure Q) := by
    intro i
    simpa using! (hfluxComp i).integrable_mul (hcentComp i)
  have hIntConst :
      MeasureTheory.Integrable
        (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))
        (normalizedCubeMeasure Q) := by
    simpa [vecDot] using
      (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hIntConstComp i))
  have hIntCent :
      MeasureTheory.Integrable
        (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))
        (normalizedCubeMeasure Q) := by
    simpa [vecDot] using
      (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hIntCentComp i))
  have hsplitFun :
      (fun x => vecDot (flux x) (u x • ξ x)) =
        (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x) +
          vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
    funext x
    calc
      vecDot (flux x) (u x • ξ x)
          = vecDot (flux x) (((cubeAverage Q u) + (u x - cubeAverage Q u)) • ξ x) := by
              congr 1
              ring_nf
      _ = vecDot (flux x) ((cubeAverage Q u) • ξ x + (u x - cubeAverage Q u) • ξ x) := by
            rw [add_smul]
      _ = vecDot (flux x) ((cubeAverage Q u) • ξ x) +
            vecDot (flux x) ((u x - cubeAverage Q u) • ξ x) := by
              simp [vecDot, Finset.sum_add_distrib, mul_add]
  have hsplit :
      cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x)) =
        cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
          cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
    calc
      cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))
          = ∫ x, vecDot (flux x) (u x • ξ x) ∂ normalizedCubeMeasure Q := by
              rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      _ = ∫ x,
            (vecDot (flux x) ((cubeAverage Q u) • ξ x) +
              vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))
            ∂ normalizedCubeMeasure Q := by
              exact congrArg (fun f => ∫ x, f x ∂ normalizedCubeMeasure Q) hsplitFun
      _ = ∫ x, vecDot (flux x) ((cubeAverage Q u) • ξ x) ∂ normalizedCubeMeasure Q +
            ∫ x, vecDot (flux x) ((u x - cubeAverage Q u) • ξ x) ∂ normalizedCubeMeasure Q := by
              rw [MeasureTheory.integral_add hIntConst hIntCent]
      _ = cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
            cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x)) := by
              rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
                ← cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        = |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x)) +
            cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| := by
              rw [hsplit]
    _ ≤ |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))| +
          |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| := by
            exact abs_add_le _ _
    _ ≤
      (d : ℝ) *
          (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1)) *
            BgConst) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS)) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
            exact add_le_add hconst hcent

theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_note_terms_of_contDiff_component_vector_effective_constant
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    {Bu1 BuS Bavg Bcirc1 BcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hfluxNeg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu1)
    (hfluxNegS : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ BuS)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1) +
          cubeBesovScaleWeight 1 Q * Bavg) * BgConst)) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS) +
              cubeBesovScaleWeight s Q * Bavg) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  have hBgCent_bound_vec :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ BgCent := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hBgCent_bound
  have hraw :=
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_note_terms_of_contDiff_component_vector_bound
      Q s flux u G ξ hB hs0 hs1 hflux hu hG hξLp hBgConst hBgCent hBavg hC
      hBcircS havg hfluxNeg1 hfluxNegS hproj hξ hderiv hGcirc1 hGcircS
      hBgConst_bound hBgCent_bound_vec
  simpa [mul_assoc, mul_left_comm, mul_comm] using hraw

/-- Effective-constant wrapper for the sharp vector split estimate. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_contDiff_component_vector_effective_constant
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    {Bu1 BuS Bavg Bcirc1 BcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hfluxNeg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu1)
    (hfluxNegS : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ BuS)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu1)) *
          BgConst) +
        ((d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * BuS)) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  have hBgCent_bound_vec :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ BgCent := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hBgCent_bound
  have hraw :=
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_contDiff_component_vector_bound
      Q s flux u G ξ hB hs0 hs1 hflux hu hG hξLp hBgConst hBgCent hBavg hC
      hBcircS havg hfluxNeg1 hfluxNegS hproj hξ hderiv hGcirc1 hGcircS
      hBgConst_bound hBgCent_bound_vec
  simpa [mul_assoc, mul_left_comm, mul_comm] using hraw

/-- Energy-coefficient form of the split local Caccioppoli pairing.

The previous theorem keeps the five Besov/average bounds as raw constants.
This wrapper records the next downstream shape: each of those bounds is a
coefficient times one common local energy scale `E`.  The radius/coefficient
bookkeeping can now substitute the Chapter-2/coarse-Poincare coefficients
without reopening the cutoff-product proof. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_split_energy_coefficients_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {Aflux1 AfluxS Aavg Acirc1 AcircS E B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hAavg : 0 ≤ Aavg) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Aavg * E)
    (hfluxNeg1 :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Aflux1 * E)
    (hfluxNegS :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ AfluxS * E)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hgCirc1 :
      ∀ N : ℕ, cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Acirc1 * E)
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ AcircS * E)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * (AcircS * E)))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * (Aflux1 * E)) +
          cubeBesovScaleWeight 1 Q * (Aavg * E)) * BgConst)) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E)) +
              cubeBesovScaleWeight s Q * (Aavg * E)) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_note_terms_of_contDiff_component_bound
      (Q := Q) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (Bu1 := Aflux1 * E) (BuS := AfluxS * E) (Bavg := Aavg * E)
      (Bcirc1 := Acirc1 * E) (BcircS := AcircS * E)
      (B := B) (C := C) (BgConst := BgConst) (BgCent := BgCent)
      hB hs0 hs1 hflux hu hg hξLp hBgConst hBgCent
      (mul_nonneg hAavg hE) hC havg hfluxNeg1 hfluxNegS hproj hξ hderiv
      hgCirc1 hgCircS hBgConst_bound hBgCent_bound

/-- Vector projected-Poincare version of
`abs_cubeAverage_vecDot_scalar_smul_le_split_energy_coefficients_of_contDiff_component_bound`.

This is the coefficient-times-energy wrapper for the descendant/local
Caccioppoli pairing used by the harmonic-vector endpoint. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_energy_coefficients_of_contDiff_component_vector_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    {Aflux1 AfluxS Aavg Acirc1 AcircS E B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hAavg : 0 ≤ Aavg) (hE : 0 ≤ E) (hC : 0 ≤ C) (hAcircS : 0 ≤ AcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Aavg * E)
    (hfluxNeg1 :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Aflux1 * E)
    (hfluxNegS :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ AfluxS * E)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Acirc1 * E)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * E)
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * (AcircS * E)))) ≤ BgCent) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * (Aflux1 * E)) +
          cubeBesovScaleWeight 1 Q * (Aavg * E)) * BgConst)) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E)) +
              cubeBesovScaleWeight s Q * (Aavg * E)) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_note_terms_of_contDiff_component_vector_effective_constant
      (Q := Q) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (Bu1 := Aflux1 * E) (BuS := AfluxS * E) (Bavg := Aavg * E)
      (Bcirc1 := Acirc1 * E) (BcircS := AcircS * E)
      (B := B) (C := C) (BgConst := BgConst) (BgCent := BgCent)
      hB hs0 hs1 hflux hu hG hξLp hBgConst hBgCent
      (mul_nonneg hAavg hE) hC (mul_nonneg hAcircS hE)
      havg hfluxNeg1 hfluxNegS hproj hξ hderiv hGcirc1 hGcircS
      hBgConst_bound hBgCent_bound

end

end Homogenization
