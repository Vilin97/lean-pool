/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.CenteredProduct
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Bounds

/-! # Centered Product Full Dual -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
# Full-dual centered cutoff-product estimates

This sidecar keeps `CenteredProduct.lean` under the preferred size ceiling while
recording the corrected full-dual replacement for the `L²` half of the centered
cutoff-product estimate.  The local-multiscale theorem below also discharges
the positive-Besov scalar tail from the matching finite-depth Poincare estimate,
which is the analytic input needed by the Section 3.1 small-cube bridge.
-/

theorem
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_fullDualL2_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (ξ : Vec d → Vec d) {B C Bcirc1 Bpos : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfull :
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs1 : s < 1) (hC : 0 ≤ C) (hBcirc1 : 0 ≤ Bcirc1)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1)
    (hpos :
      cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤ Bpos) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ * Bpos) := by
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q s N u ξ hB hu hξLp hξ hderiv
  have hraw :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) :=
    cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_dualFullVectorPoincareEstimate
      Q s N u G hu hfull hG hs1 hC hBcirc1 hGcirc1
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hterm1 :
      cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u)
        ≤
      cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) :=
    mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
  have hterm2 :
      cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)
        ≤
      cubeLpNorm Q ∞ ξ * Bpos :=
    mul_le_mul_of_nonneg_left hpos (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x)
        ≤
      2 * (cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
            simpa [cubeFluctuation] using! hpartial
    _ ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ * Bpos) := by
            exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)

theorem
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_fullDual_localMultiscale_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (ξ : Vec d → Vec d) {B C Bcirc1 BcircS : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfull :
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hlocal :
      CubeLocalMultiscalePoincareVectorEstimate Q
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hBcirc1 : 0 ≤ Bcirc1) (hBcircS : 0 ≤ BcircS)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) := by
  have hnoteC_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (Real.rpow_nonneg (by positivity) _)
  have hpos :
      cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤
        cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) *
            ((Fintype.card (Fin d) : ℝ) * BcircS)) := by
    simpa [mul_assoc] using
      CubeLocalMultiscalePoincareVectorEstimate.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs_of_component_bound
        (Q := Q)
        (s := s)
        (C := ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (Bcirc := BcircS) (u := u) (G := G) (M := N)
        hlocal hs0 hnoteC_nonneg hBcircS hGcircS
  exact
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_fullDualL2_cutoff_terms
      (Q := Q) (s := s) (N := N) (u := u) (G := G) (ξ := ξ)
      (B := B) (C := C) (Bcirc1 := Bcirc1)
      (Bpos :=
        cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) *
            ((Fintype.card (Fin d) : ℝ) * BcircS)))
      hB hu hfull hG hξLp hξ hderiv hs1 hC hBcirc1 hGcirc1 hpos

/-- Componentwise dual-test bound for the centered cutoff product, using the
full-dual Poincare estimate and the full-circ infinite-depth positive
Poincare route. -/
theorem
    cubeBesovDualTestNorm_two_one_component_centered_scalar_smul_le_fullDual_fullCirc_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (ξ : Vec d → Vec d) (i : Fin d) {B C Bcirc1 BcircS : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfull : ∀ M : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G M)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hBcirc1 : 0 ≤ Bcirc1) (hBcircS : 0 ≤ BcircS)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ BcircS) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q (fun y => (u y - cubeAverage Q u) • ξ y) x i) ≤
      cubeBesovScaleWeight s Q *
        (2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) *
                ((Fintype.card (Fin d) : ℝ) * BcircS))))) := by
  classical
  let v : Vec d → ℝ := cubeFluctuation Q u
  let prod : Vec d → Vec d := fun x => v x • ξ x
  let L2B : ℝ :=
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc1))
  let PosB : ℝ :=
    cubeBesovScaleWeight (-s) Q *
      ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        (1 - (3 : ℝ) ^ (-s))⁻¹) *
        ((Fintype.card (Fin d) : ℝ) * BcircS))
  have hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hprodMem :
      MeasureTheory.MemLp prod (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [prod] using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv
  have hconj :
      cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have havg :
      cubeAverage Q (fun x => cubeFluctuationVec Q prod x i) = 0 := by
    simpa [cubeFluctuation_component_eq_cubeFluctuationVec_component Q prod i] using
      cubeAverage_cubeFluctuation Q (fun x => prod x i)
  have hL2partial :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N v ≤ L2B := by
    simpa [v, L2B] using
      cubeL2ScalarPartialSeminormTwo_fluctuation_le_note_rhs_of_dualFullVectorPoincareEstimate
        Q s N u G hu (hfull N) hG hs1 hC hBcirc1 hGcirc1
  have hCfull_nonneg : 0 ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) := by
    exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hgeom_nonneg : 0 ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hgeom_large : 1 ≤ (3 / 2 : ℝ) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hr_nonneg : 0 ≤ (3 : ℝ) ^ (-s) :=
      Real.rpow_nonneg (by positivity) _
    have hden_pos : 0 < 1 - (3 : ℝ) ^ (-s) := by linarith
    have hinv_ge_one : 1 ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
      exact (one_le_inv₀ hden_pos).mpr (by linarith)
    calc
      (1 : ℝ) ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := hinv_ge_one
      _ ≤ (3 / 2 : ℝ) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
            exact le_mul_of_one_le_left hgeom_nonneg (by norm_num)
  have hposDepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q s v j ≤ PosB := by
    intro j hj
    have hlocalFull :
        CubeLocalFullCircPoincareVectorEstimate Q
          (C * (3 : ℝ) ^ ((d : ℝ) + 1)) v G N :=
      (hfull N).to_localFullCircEstimate hG hC
    have hdepth :
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j ≤
          (C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ∑ i : Fin d,
              cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => G x i) := by
      exact
        cubeBesovDepthSeminorm_two_le_sum_circNorm_of_vector_local_full_circ_bound
          Q s (C * (3 : ℝ) ^ ((d : ℝ) + 1)) v G j hs0.le hs1 hCfull_nonneg hG
          (by
            intro R hR
            exact hlocalFull j hj R hR)
    have hcircNorm : ∀ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) ≤
          BcircS := by
      intro i
      exact
        cubeBesovCircNorm_le_of_forall_partialNorm_le
          Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
          (by norm_num) (hGcircS i)
    have hsum :
        ∑ i : Fin d,
            cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i) ≤
          (Fintype.card (Fin d) : ℝ) * BcircS := by
      calc
        ∑ i : Fin d,
            cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i)
            ≤ ∑ _i : Fin d, BcircS := by
              exact Finset.sum_le_sum fun i _ => hcircNorm i
        _ = (Fintype.card (Fin d) : ℝ) * BcircS := by
              simp
    have hdepth_bound :
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j ≤
          (C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * BcircS) :=
      hdepth.trans (mul_le_mul_of_nonneg_left hsum hCfull_nonneg)
    have hlarge :
        (C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * BcircS) ≤
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) *
            ((Fintype.card (Fin d) : ℝ) * BcircS) := by
      have htail_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) * BcircS :=
        mul_nonneg hcard_nonneg hBcircS
      have hfront :
          C * (3 : ℝ) ^ ((d : ℝ) + 1) ≤
            ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹ := by
        calc
          C * (3 : ℝ) ^ ((d : ℝ) + 1)
              = 1 * (C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by ring
          _ ≤ ((3 / 2 : ℝ) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
                (C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_right hgeom_large hCfull_nonneg
          _ = ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹ := by ring
      exact mul_le_mul_of_nonneg_right hfront htail_nonneg
    calc
      cubeBesovPositiveScalarDepthSeminorm Q s v j
          = cubeBesovScaleWeight (-s) Q *
              cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
            rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
      _ ≤ cubeBesovScaleWeight (-s) Q *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)) := by
            exact mul_le_mul_of_nonneg_left (hdepth_bound.trans hlarge)
              (cubeBesovScaleWeight_nonneg (-s) Q)
      _ = PosB := by
            simp [PosB, mul_assoc, mul_left_comm, mul_comm]
  have hcomponentTop :
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q prod x i) ≤
        cubeBesovScaleWeight s Q *
          (2 * (cubeScaleFactor Q * B * L2B + cubeLpNorm Q ∞ ξ * PosB)) := by
    unfold cubeBesovPartialSeminormTop
    refine Finset.sup'_le
      (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
      (f := fun j =>
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞)
          (fun x => cubeFluctuationVec Q prod x i) j) ?_
    intro j hj
    have hprodDepthEq :
        cubeBesovPositiveVectorDepthSeminorm Q s (cubeFluctuationVec Q prod) j =
          cubeBesovPositiveVectorDepthSeminorm Q s prod j := by
      simpa [cubeFluctuationVec] using!
        cubeBesovPositiveVectorDepthSeminorm_sub_const
          Q s prod (cubeAverageVec Q prod) j
          (by
            intro R hR
            exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR hprodMem)
    have hdepthProd :
        cubeBesovPositiveVectorDepthSeminorm Q s prod j ≤
          2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
      simpa [prod, v] using
        cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
          Q s j v ξ hB hv hξLp hξ hderiv
    have hL2depth :
        cubeL2ScalarDepthSeminorm Q (s - 1) v j ≤
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N v := by
      have hsq :
          (cubeL2ScalarDepthSeminorm Q (s - 1) v j) ^ (2 : ℕ) ≤
            (cubeL2ScalarPartialSeminormTwo Q (s - 1) N v) ^ (2 : ℕ) := by
        rw [sq_cubeL2ScalarPartialSeminormTwo]
        exact Finset.single_le_sum
          (fun k _ => sq_nonneg (cubeL2ScalarDepthSeminorm Q (s - 1) v k)) hj
      have hleft_nonneg : 0 ≤ cubeL2ScalarDepthSeminorm Q (s - 1) v j :=
        cubeL2ScalarDepthSeminorm_nonneg Q (s - 1) v j
      have hright_nonneg : 0 ≤ cubeL2ScalarPartialSeminormTwo Q (s - 1) N v :=
        Real.sqrt_nonneg _
      nlinarith
    have hinner :
        cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j ≤
          cubeScaleFactor Q * B * L2B + cubeLpNorm Q ∞ ξ * PosB := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hL2depth.trans hL2partial)
          (mul_nonneg (cubeScaleFactor_nonneg Q) hB))
        (mul_le_mul_of_nonneg_left (hposDepth j hj) (cubeLpNorm_nonneg Q ∞ ξ))
    calc
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞)
          (fun x => cubeFluctuationVec Q prod x i) j
          ≤ cubeBesovScaleWeight s Q *
              cubeBesovPositiveVectorDepthSeminorm Q s (cubeFluctuationVec Q prod) j := by
            exact cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
              Q s (cubeFluctuationVec Q prod) i j
              (memLp_cubeFluctuationVec Q prod hprodMem)
      _ = cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s prod j := by
            rw [hprodDepthEq]
      _ ≤ cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j)) := by
            exact mul_le_mul_of_nonneg_left hdepthProd (cubeBesovScaleWeight_nonneg s Q)
      _ ≤ cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * L2B + cubeLpNorm Q ∞ ξ * PosB)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner (by norm_num))
              (cubeBesovScaleWeight_nonneg s Q)
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
    N (fun x => cubeFluctuationVec Q (fun y => (u y - cubeAverage Q u) • ξ y) x i) hconj]
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    Q s (cubeBesovConjExponent (2 : ℝ≥0∞)) N
    (fun x => cubeFluctuationVec Q (fun y => (u y - cubeAverage Q u) • ξ y) x i)
    (by
      simpa [prod, v, cubeFluctuation] using havg)]
  rw [hpConj]
  change
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q prod x i) ≤
      cubeBesovScaleWeight s Q *
        (2 * (cubeScaleFactor Q * B * L2B + cubeLpNorm Q ∞ ξ * PosB))
  exact hcomponentTop

theorem
    cubeBesovPositiveVectorSeminormTwo_centered_scalar_smul_le_fullDualL2_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (ξ : Vec d → Vec d) {B C Bcirc1 Bpos : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs1 : s < 1) (hC : 0 ≤ C) (hBcirc1 : 0 ≤ Bcirc1)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) ≤ Bpos) :
    cubeBesovPositiveVectorSeminormTwo Q s
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ * Bpos) := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound (Q := Q) (s := s)
    (u := fun x => (u x - cubeAverage Q u) • ξ x) ?_
  intro N
  exact
    cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_fullDualL2_cutoff_terms
      Q s N u G ξ hB hu (hfull N) hG hξLp hξ hderiv hs1 hC hBcirc1
      hGcirc1 (hpos N)

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_average_note_terms_of_partialBounds_of_dualFullVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcirc1 : 0 ≤ Bcirc1)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc1) := by
    exact
      cubeLpNorm_two_le_note_rhs_of_meanZero_dualFullVectorPoincareEstimate
        Q 0 (cubeFluctuation Q u) G (hfull 0) hG
        (cubeAverage_cubeFluctuation Q u) hC hBcirc1 hGcirc1
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_dualFullVectorPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bg Bavg Bcirc1 C : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcirc1 : 0 ≤ Bcirc1)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => G x i) ≤ Bcirc1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds
      Q s flux (cubeFluctuation Q u) ξ hs hflux huFluct hξLp hBg hBavg havg hneg
      (by
        intro N
        simpa [cubeFluctuation] using hpos N)
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc1) := by
    exact
      cubeLpNorm_two_le_note_rhs_of_meanZero_dualFullVectorPoincareEstimate
        Q 0 (cubeFluctuation Q u) G (hfull 0) hG
        (cubeAverage_cubeFluctuation Q u) hC hBcirc1 hGcirc1
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) := by
    exact mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) := by
      exact mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_dualFull_fullCirc
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bg Bavg Bcirc1 BcircS B C : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (hBcirc1 : 0 ≤ Bcirc1) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have huFluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x =>
          cubeFluctuationVec Q
            (fun y => cubeFluctuation Q u y • ξ y) x i) ≤
        cubeBesovScaleWeight s Q * Bg := by
    intro i N
    exact le_trans
      (cubeBesovDualTestNorm_two_one_component_centered_scalar_smul_le_fullDual_fullCirc_cutoff_terms
        Q s N u G ξ i hB hu hfull hG hξLp hξ hderiv hs0 hs1 hC hBcirc1 hBcircS
        hGcirc1 hGcircS)
      (mul_le_mul_of_nonneg_left hBg_bound (cubeBesovScaleWeight_nonneg s Q))
  have hmain :=
    abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_dualTestBounds
      Q s flux (cubeFluctuation Q u) ξ hs0 hflux huFluct hξLp hBg hBavg havg hneg hdual
  have hfluctL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc1) := by
    exact
      cubeLpNorm_two_le_note_rhs_of_meanZero_dualFullVectorPoincareEstimate
        Q 0 (cubeFluctuation Q u) G (hfull 0) hG
        (cubeAverage_cubeFluctuation Q u) hC hBcirc1 hGcirc1
  have havgInner :
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
        cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)) :=
    mul_le_mul_of_nonneg_left hfluctL2 (cubeLpNorm_nonneg Q ∞ ξ)
  have havgTerm :
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)))
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hinner :
        Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))
          ≤
        Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) :=
      mul_le_mul_of_nonneg_left havgInner hBavg
    exact mul_le_mul_of_nonneg_left hinner hd_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))|
        ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              simpa [cubeFluctuation] using hmain
    _ ≤
      (d : ℝ) *
          (Bavg * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
              exact add_le_add havgTerm le_rfl

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_dualFull_localMultiscale
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bavg Bcirc1 BcircS B C Bg : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (hBcirc1 : 0 ≤ Bcirc1) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hlocal : ∀ N : ℕ,
      CubeLocalMultiscalePoincareVectorEstimate Q
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg := by
    intro N
    exact le_trans
      (cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_fullDual_localMultiscale_cutoff_terms
        Q s N u G ξ hB hu (hfull N) (hlocal N) hG hξLp hξ hderiv
        hs0 hs1 hC hBcirc1 hBcircS hGcirc1 (fun i => hGcircS i N))
      hBg_bound
  exact
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_dualFullVectorPoincareEstimate
      Q s flux u G ξ hs0 hflux hu hG hξLp hBg hBavg hC hBcirc1
      havg hneg hpos hfull hGcirc1

end

end Homogenization
