/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothGraph
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspExactOverlapFullControl
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLegacyCircComparison
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactAggregationBridge
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactFiniteBridge
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactExponentBridge
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing.MainBounds
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliVectorization
import LeanPool.CoarseGraining.Homogenization.Besov.PositiveOverlapBridge

/-!
# Source negative-Besov control of the smooth fractional dual

This module uses finite block projections.  In particular, the represented
field is used only through its `L²` integrability, never through a spurious
`Lᵖ` upgrade.
-/

namespace Homogenization

open MeasureTheory
open Book.Ch03.ABK26
open scoped BigOperators ENNReal Topology

noncomputable section

/-- A finite dimension-only coefficient for the finite-projection smooth-dual
estimate. -/
noncomputable def cubeEuclideanNegativeWspSmoothDualBesovConstant (d : ℕ) : ℝ≥0∞ :=
  d * (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) *
    cubeEuclideanWspExactOverlapFullControlConstant d

private noncomputable def cubeEuclideanNegativeWspSmoothDualBesovScalarConstant
    (d : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) *
    cubeEuclideanWspExactOverlapFullControlConstant d

theorem cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top (d : ℕ) :
    cubeEuclideanNegativeWspSmoothDualBesovConstant d < ∞ := by
  unfold cubeEuclideanNegativeWspSmoothDualBesovConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)))
    (cubeEuclideanWspExactOverlapFullControlConstant_lt_top d)

private theorem smooth_coordinate_bounded_on_cube {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ cubeSet Q, |h.toField x i| ≤ C := by
  have hcont : Continuous (fun x : Vec d => h.toField x i) :=
    continuous_apply i |>.comp h.contDiff.continuous
  have hcompact : IsCompact (closure (cubeSet Q)) :=
    (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcont.abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC ⟨x, subset_closure hx, rfl⟩).trans (le_max_left _ _)

/-- A scalar-coordinate source-negative Besov bound for the smooth fractional-Sobolev dual pairing. -/
theorem ennreal_abs_cubeBesovPairing_coordinate_le_cubeEuclideanNegativeBesovESeminorm_mul_cubeEuclideanWspFull
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) (i : Fin d) :
    ENNReal.ofReal |cubeBesovPairing Q (fun x => F.toField x i)
        (fun x => h.toField x i)| ≤
      cubeEuclideanNegativeWspSmoothDualBesovScalarConstant d *
        cubeEuclideanNegativeBesovESeminorm Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
  classical
  by_cases hd : d = 0
  · exact Fin.elim0 (by simpa [hd] using i)
  have : NeZero d := ⟨hd⟩
  let hWsp := h.toCubeEuclideanWspField
  have hFmem : MeasureTheory.MemLp (fun x => F.toField x i)
      FiniteLpExponent.two.exponent (normalizedCubeMeasure Q) :=
    cubeEuclideanLp_coordinate_memLp F i
  have hFint : MeasureTheory.IntegrableOn (fun x => F.toField x i)
      (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q
      (hFmem.integrable (by norm_num))
  have hhmem : MeasureTheory.MemLp (fun x => h.toField x i)
      p.conjugate.exponent (normalizedCubeMeasure Q) := by
    simpa [hWsp] using cubeEuclideanLp_coordinate_memLp hWsp.toCubeEuclideanLpField i
  have hhint : MeasureTheory.IntegrableOn (fun x => h.toField x i)
      (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q
      (hhmem.integrable p.conjugate.one_lt.le)
  obtain ⟨Cbound, hCbound, hhbound⟩ := smooth_coordinate_bounded_on_cube h i
  let : ENNReal.HolderConjugate p.conjugate.exponent p.exponent :=
    p.holderConjugate.symm
  have hconj : cubeBesovConjExponent p.conjugate.exponent = p.exponent := by
    simpa only [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := p.conjugate.exponent) (q := p.exponent))
  have hpconj_ofReal : ENNReal.ofReal p.conjugate.exponent.toReal =
      p.conjugate.exponent := ENNReal.ofReal_toReal p.conjugate.lt_top.ne
  have hp_ofReal : ENNReal.ofReal p.exponent.toReal = p.exponent :=
    ENNReal.ofReal_toReal p.lt_top.ne
  have hhmemReal : MeasureTheory.MemLp (fun x => h.toField x i)
      (ENNReal.ofReal p.conjugate.exponent.toReal) (normalizedCubeMeasure Q) := by
    rw [hpconj_ofReal]
    exact hhmem
  have hpconj_toReal_one_le : 1 ≤ p.conjugate.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono p.conjugate.lt_top.ne p.conjugate.one_lt.le
  have hfinite : ∀ n : ℕ,
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1)
        (fun x => F.toField x i)) (fun x => h.toField x i)| ≤
        cubeEuclideanNegativeWspSmoothDualBesovScalarConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F *
            cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
    intro n
    have hFluct : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R (fun x => h.toField x i))
          p.conjugate.exponent (normalizedCubeMeasure R) := by
      intro j _ R hR
      simpa only [hpconj_ofReal] using cubeFluctuation_memLp_of_parent_memLp
        Q p.conjugate.exponent.toReal hhmemReal j R hR
    have hProj : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) (fun x => F.toField x i))
          (cubeBesovConjExponent p.conjugate.exponent) (normalizedCubeMeasure R) := by
      intro j _ R hR
      rw [hconj]
      simpa only [hp_ofReal] using cubeProjection_memLp_of_parent_descendant
        Q p.exponent.toReal (fun x => F.toField x i) (j + 1) j R hR
    have hpair :=
      abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
        Q s.1 p.conjugate.exponent p.conjugate.exponent
        (fun x => h.toField x i) (fun x => F.toField x i) n hFint
        p.conjugate.one_lt.le p.conjugate.lt_top.ne
        (by rw [hconj]; exact p.lt_top.ne)
        p.conjugate.one_lt.le p.conjugate.lt_top.ne
        (by rw [hconj]; exact p.lt_top.ne) hFluct hProj
    have hover : ENNReal.ofReal
        (cubeBesovOverlapPartialNorm Q s.1 p.conjugate.exponent p.conjugate.exponent
          n (fun x => h.toField x i)) ≤
        exactOverlapFiniteNorm (exactOverlapScalarPParameters s p.conjugate) Q
          (fun x => h.toField x i)
          (exactDualOverlapIntegrable Q p.conjugate.exponent.toReal
            hpconj_toReal_one_le hhmemReal) := by
      simpa [exactOverlapScalarPParameters, hpconj_ofReal] using
        exactAggregation_overlapPartialNorm_le_exactOverlapFiniteNorm
          (exactOverlapScalarPParameters s p.conjugate) Q
          (fun x => h.toField x i) hhmemReal n
    have hfull :=
      exactOverlapScalarPFullNorm_le_dimensionConstant_mul_cubeEuclideanWspFull
        Q s p.conjugate hWsp i
    have hfull' :
        exactOverlapFiniteNorm (exactOverlapScalarPParameters s p.conjugate) Q
          (fun x => h.toField x i)
          (exactDualOverlapIntegrable Q p.conjugate.exponent.toReal
            hpconj_toReal_one_le hhmemReal) ≤
          cubeEuclideanWspExactOverlapFullControlConstant d *
            cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
      simpa [hWsp] using hfull
    have hpartial :
        cubeBesovPartialNorm Q s.1 p.conjugate.exponent p.conjugate.exponent
          n (fun x => h.toField x i) ≤
          (3 : ℝ) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
            cubeBesovOverlapPartialNorm Q s.1 p.conjugate.exponent
              p.conjugate.exponent n (fun x => h.toField x i) :=
      cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm Q s.1
        (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.conjugate.one_lt))
          p.conjugate.lt_top.ne)
        hpconj_toReal_one_le n _
    have hpartialENN : ENNReal.ofReal
        (cubeBesovPartialNorm Q s.1 p.conjugate.exponent p.conjugate.exponent
          n (fun x => h.toField x i)) ≤
          (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
            cubeEuclideanWspExactOverlapFullControlConstant d *
              cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
      calc
        ENNReal.ofReal
            (cubeBesovPartialNorm Q s.1 p.conjugate.exponent p.conjugate.exponent
              n (fun x => h.toField x i)) ≤
            ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              cubeBesovOverlapPartialNorm Q s.1 p.conjugate.exponent
                p.conjugate.exponent n (fun x => h.toField x i)) :=
          ENNReal.ofReal_le_ofReal hpartial
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              ENNReal.ofReal
                (cubeBesovOverlapPartialNorm Q s.1 p.conjugate.exponent
                  p.conjugate.exponent n (fun x => h.toField x i)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))
              (div_nonneg (by positivity)
                (ENNReal.toReal_pos
                  (ne_of_gt (lt_trans zero_lt_one p.conjugate.one_lt))
                  p.conjugate.lt_top.ne).le)]
          norm_num
        _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              exactOverlapFiniteNorm (exactOverlapScalarPParameters s p.conjugate) Q
                (fun x => h.toField x i)
                (exactDualOverlapIntegrable Q p.conjugate.exponent.toReal
                  hpconj_toReal_one_le hhmemReal) := by
          gcongr
        _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              (cubeEuclideanWspExactOverlapFullControlConstant d *
                cubeEuclideanWspFullENorm Q s p.conjugate h.toField) := by
          gcongr
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              cubeEuclideanWspExactOverlapFullControlConstant d *
                cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by ring
    have hcirc : ENNReal.ofReal
        (cubeBesovCircPartialNorm Q s.1
          (cubeBesovConjExponent p.conjugate.exponent)
          (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
          (fun x => F.toField x i)) ≤
        cubeEuclideanNegativeBesovESeminorm Q s p F := by
      simpa only [hconj] using
        ennreal_ofReal_cubeBesovCircPartialNorm_le_cubeEuclideanNegativeBesovESeminorm
          Q s p F i (n + 1)
    have hKnonneg : 0 ≤ max 1 ((3 : ℝ) ^ s.1) :=
      zero_le_one.trans (le_max_left _ _)
    have hpartial_nonneg : 0 ≤ cubeBesovPartialNorm Q s.1
        p.conjugate.exponent p.conjugate.exponent n (fun x => h.toField x i) :=
      cubeBesovPartialNorm_nonneg Q s.1 p.conjugate.exponent p.conjugate.exponent n _
    have hpairENN : ENNReal.ofReal
        |cubeBesovPairing Q (cubeProjection Q (n + 1) (fun x => F.toField x i))
          (fun x => h.toField x i)| ≤
        max 1 ((3 : ℝ≥0∞) ^ s.1) *
          ENNReal.ofReal (cubeBesovPartialNorm Q s.1 p.conjugate.exponent
            p.conjugate.exponent n (fun x => h.toField x i)) *
          ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
            (cubeBesovConjExponent p.conjugate.exponent)
            (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
            (fun x => F.toField x i)) := by
      calc
        ENNReal.ofReal
            |cubeBesovPairing Q (cubeProjection Q (n + 1) (fun x => F.toField x i))
              (fun x => h.toField x i)| =
            ENNReal.ofReal
              |cubeBesovPairing Q (fun x => h.toField x i)
                (cubeProjection Q (n + 1) (fun x => F.toField x i))| := by
              congr 2
              simp only [cubeBesovPairing, mul_comm]
        _ ≤ ENNReal.ofReal (max 1 ((3 : ℝ) ^ s.1) *
              cubeBesovPartialNorm Q s.1 p.conjugate.exponent
                p.conjugate.exponent n (fun x => h.toField x i) *
              cubeBesovCircPartialNorm Q s.1
                (cubeBesovConjExponent p.conjugate.exponent)
                (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                (fun x => F.toField x i)) := ENNReal.ofReal_le_ofReal hpair
        _ = max 1 ((3 : ℝ≥0∞) ^ s.1) *
              ENNReal.ofReal (cubeBesovPartialNorm Q s.1 p.conjugate.exponent
                p.conjugate.exponent n (fun x => h.toField x i)) *
              ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                (cubeBesovConjExponent p.conjugate.exponent)
                (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                (fun x => F.toField x i)) := by
              rw [ENNReal.ofReal_mul (mul_nonneg hKnonneg hpartial_nonneg),
                ENNReal.ofReal_mul hKnonneg, ENNReal.ofReal_max,
                ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))
                  s.2.1.le]
              norm_num
    have hloss := exactCircLossCoefficientENNReal_rpow_le_source d s.1
      p.conjugate.exponent.toReal s.2.1.le hpconj_toReal_one_le
    have hpower : (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) ≤
        (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [s.2.2])
    calc
      ENNReal.ofReal
          |cubeBesovPairing Q (cubeProjection Q (n + 1) (fun x => F.toField x i))
            (fun x => h.toField x i)| ≤
          max 1 ((3 : ℝ≥0∞) ^ s.1) *
            ((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
              cubeEuclideanWspExactOverlapFullControlConstant d *
                cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
            cubeEuclideanNegativeBesovESeminorm Q s p F := by
          calc
            ENNReal.ofReal
                |cubeBesovPairing Q (cubeProjection Q (n + 1) (fun x => F.toField x i))
                  (fun x => h.toField x i)| ≤
                max 1 ((3 : ℝ≥0∞) ^ s.1) *
                  ENNReal.ofReal (cubeBesovPartialNorm Q s.1 p.conjugate.exponent
                    p.conjugate.exponent n (fun x => h.toField x i)) *
                  ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                    (cubeBesovConjExponent p.conjugate.exponent)
                    (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                    (fun x => F.toField x i)) := hpairENN
            _ ≤ max 1 ((3 : ℝ≥0∞) ^ s.1) *
                  ((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
                    cubeEuclideanWspExactOverlapFullControlConstant d *
                      cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
                  ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                    (cubeBesovConjExponent p.conjugate.exponent)
                    (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                    (fun x => F.toField x i)) := by
                    rw [show max 1 ((3 : ℝ≥0∞) ^ s.1) *
                        ENNReal.ofReal (cubeBesovPartialNorm Q s.1
                          p.conjugate.exponent p.conjugate.exponent n
                          (fun x => h.toField x i)) *
                        ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                          (cubeBesovConjExponent p.conjugate.exponent)
                          (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                          (fun x => F.toField x i)) =
                        max 1 ((3 : ℝ≥0∞) ^ s.1) *
                          (ENNReal.ofReal (cubeBesovPartialNorm Q s.1
                            p.conjugate.exponent p.conjugate.exponent n
                            (fun x => h.toField x i)) *
                          ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                            (cubeBesovConjExponent p.conjugate.exponent)
                            (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                            (fun x => F.toField x i))) by ac_rfl]
                    rw [show max 1 ((3 : ℝ≥0∞) ^ s.1) *
                        ((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
                          cubeEuclideanWspExactOverlapFullControlConstant d *
                            cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
                        ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                          (cubeBesovConjExponent p.conjugate.exponent)
                          (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                          (fun x => F.toField x i)) =
                        max 1 ((3 : ℝ≥0∞) ^ s.1) *
                          (((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
                            cubeEuclideanWspExactOverlapFullControlConstant d *
                              cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
                          ENNReal.ofReal (cubeBesovCircPartialNorm Q s.1
                            (cubeBesovConjExponent p.conjugate.exponent)
                            (cubeBesovConjExponent p.conjugate.exponent) (n + 1)
                            (fun x => F.toField x i))) by ac_rfl]
                    apply mul_le_mul_right
                    exact mul_le_mul_left hpartialENN _
            _ ≤ max 1 ((3 : ℝ≥0∞) ^ s.1) *
                  ((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
                    cubeEuclideanWspExactOverlapFullControlConstant d *
                      cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
                  cubeEuclideanNegativeBesovESeminorm Q s p F := by
                    gcongr
      _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) *
            cubeEuclideanWspExactOverlapFullControlConstant d *
              cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                cubeEuclideanNegativeBesovESeminorm Q s p F := by
          rw [show max 1 ((3 : ℝ≥0∞) ^ s.1) *
                ((3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal) *
                  cubeEuclideanWspExactOverlapFullControlConstant d *
                    cubeEuclideanWspFullENorm Q s p.conjugate h.toField) *
                cubeEuclideanNegativeBesovESeminorm Q s p F =
                (max 1 ((3 : ℝ≥0∞) ^ s.1) *
                  (3 : ℝ≥0∞) ^ ((d : ℝ) / p.conjugate.exponent.toReal)) *
                (cubeEuclideanWspExactOverlapFullControlConstant d *
                  cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                    cubeEuclideanNegativeBesovESeminorm Q s p F) by ac_rfl]
          rw [show (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) *
                cubeEuclideanWspExactOverlapFullControlConstant d *
                  cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                    cubeEuclideanNegativeBesovESeminorm Q s p F =
                (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) *
                  (cubeEuclideanWspExactOverlapFullControlConstant d *
                    cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                      cubeEuclideanNegativeBesovESeminorm Q s p F) by ac_rfl]
          exact mul_le_mul_left hloss _
      _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) *
            cubeEuclideanWspExactOverlapFullControlConstant d *
              cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                cubeEuclideanNegativeBesovESeminorm Q s p F := by
          rw [show (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) *
                cubeEuclideanWspExactOverlapFullControlConstant d *
                  cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                    cubeEuclideanNegativeBesovESeminorm Q s p F =
                (3 : ℝ≥0∞) ^ ((d : ℝ) + s.1) *
                  (cubeEuclideanWspExactOverlapFullControlConstant d *
                    cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                      cubeEuclideanNegativeBesovESeminorm Q s p F) by ac_rfl]
          rw [show (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) *
                cubeEuclideanWspExactOverlapFullControlConstant d *
                  cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                    cubeEuclideanNegativeBesovESeminorm Q s p F =
                (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) *
                  (cubeEuclideanWspExactOverlapFullControlConstant d *
                    cubeEuclideanWspFullENorm Q s p.conjugate h.toField *
                      cubeEuclideanNegativeBesovESeminorm Q s p F) by ac_rfl]
          exact mul_le_mul_left hpower _
      _ = cubeEuclideanNegativeWspSmoothDualBesovScalarConstant d *
            cubeEuclideanNegativeBesovESeminorm Q s p F *
              cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
          unfold cubeEuclideanNegativeWspSmoothDualBesovScalarConstant
          ac_rfl
  have hconv := tendsto_cubeBesovPairing_projection_left_of_integrableOn_of_bounded
    Q (fun x => F.toField x i) (fun x => h.toField x i) Cbound hFint hhint hCbound hhbound
  have hconvAbs : Filter.Tendsto (fun n => ENNReal.ofReal
      |cubeBesovPairing Q (cubeProjection Q (n + 1) (fun x => F.toField x i))
        (fun x => h.toField x i)|) Filter.atTop
      (𝓝 (ENNReal.ofReal |cubeBesovPairing Q (fun x => F.toField x i)
        (fun x => h.toField x i)|)) :=
    ENNReal.tendsto_ofReal (by simpa [Real.norm_eq_abs] using hconv.norm)
  exact le_of_tendsto hconvAbs (Filter.Eventually.of_forall hfinite)


theorem ennreal_abs_cubeEuclideanNormalizedSmoothPairing_le_cubeEuclideanNegativeBesovESeminorm_mul_cubeEuclideanWspFull
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      cubeEuclideanNegativeWspSmoothDualBesovConstant d *
        cubeEuclideanNegativeBesovESeminorm Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
  have hInt : ∀ i : Fin d,
      MeasureTheory.Integrable (fun x => F.toField x i * h.toField x i)
        (normalizedCubeMeasure Q) := by
    intro i
    have hF : MeasureTheory.MemLp (fun x => F.toField x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
      simpa only [FiniteLpExponent.two_exponent] using
        cubeEuclideanLp_coordinate_memLp F i
    have hh : MeasureTheory.MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
      simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using h.euclideanMemLp_two.eval_piLp i
    exact hF.integrable_mul hh
  have hpairEq : cubeEuclideanNormalizedSmoothPairing F h =
      cubeAverage Q (fun x => vecDot (F.toField x) (h.toField x)) := by
    unfold cubeEuclideanNormalizedSmoothPairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsumReal : |cubeEuclideanNormalizedSmoothPairing F h| ≤
      ∑ i, |cubeBesovPairing Q (fun x => F.toField x i) (fun x => h.toField x i)| := by
    rw [hpairEq]
    exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q F.toField h.toField hInt
  have hsumENN : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      ∑ i, ENNReal.ofReal
        |cubeBesovPairing Q (fun x => F.toField x i) (fun x => h.toField x i)| := by
    calc
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
          ENNReal.ofReal (∑ i,
            |cubeBesovPairing Q (fun x => F.toField x i) (fun x => h.toField x i)|) :=
        ENNReal.ofReal_le_ofReal hsumReal
      _ = ∑ i, ENNReal.ofReal
          |cubeBesovPairing Q (fun x => F.toField x i) (fun x => h.toField x i)| := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact abs_nonneg _
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
        ∑ i, ENNReal.ofReal
          |cubeBesovPairing Q (fun x => F.toField x i) (fun x => h.toField x i)| := hsumENN
    _ ≤ ∑ _i : Fin d, cubeEuclideanNegativeWspSmoothDualBesovScalarConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F *
            cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
      apply Finset.sum_le_sum
      intro i _
      exact ennreal_abs_cubeBesovPairing_coordinate_le_cubeEuclideanNegativeBesovESeminorm_mul_cubeEuclideanWspFull
        Q s p F h i
    _ = cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F *
            cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold cubeEuclideanNegativeWspSmoothDualBesovConstant
        cubeEuclideanNegativeWspSmoothDualBesovScalarConstant
      ac_rfl

theorem cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm
    (d : ℕ) (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F ≤
      cubeEuclideanNegativeWspSmoothDualBesovConstant d *
        cubeEuclideanNegativeBesovESeminorm Q s p F := by
  rw [cubeEuclideanNegativeWspSmoothDualENorm]
  apply iSup_le
  intro h
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| ≤
        cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F *
            cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField :=
      ennreal_abs_cubeEuclideanNormalizedSmoothPairing_le_cubeEuclideanNegativeBesovESeminorm_mul_cubeEuclideanWspFull Q s p F h.1
    _ ≤ cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F * 1 := by
      gcongr
      exact h.2
    _ = cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p F := by rw [mul_one]


end

end Homogenization
