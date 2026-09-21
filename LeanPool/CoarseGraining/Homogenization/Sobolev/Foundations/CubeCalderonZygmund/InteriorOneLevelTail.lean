/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorLocalInputs
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalStoppingFamily
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaTailControl
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaVitaliAssembly

/-!
# An interior one-level cube good-`lambda` inequality

This file assembles the global stopping family, the local one-ball comparison,
and the Vitali cover for a solution on an arbitrary open parent set.  The
comparison-parent containment and the global energy cutoff remain explicit
internal hypotheses.  Consequently, the result is an internal conditional
assembly theorem, not a source-facing Calderon--Zygmund estimate.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

/-- The one-level good-`lambda` tail bound for a solution on an open parent.

Stopping radii and the Vitali subfamily are constructed internally.  Every
local PDE input is obtained by restricting the parent weak equation. -/
theorem sqWeightedMeasure_openParent_oneLevel_tail_originCube
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (hq : 2 < q.exponent.toReal) {U : Set (Vec d)} (hU : IsOpen U)
    {m : ℤ} {sigma0 eps M level : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M) (uU : H1Function U) (H : Vec d → Vec d)
    (hH : MemVectorL2 U H)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ U →
      sigma0 * ∫ y in U,
        vecDot (uU.grad y) (euclideanGradient phi y) ∂volume =
          -∫ y in U, vecDot (H y) (euclideanGradient phi y) ∂volume)
    (hparent : ∀ x ∈ openCubeSet (originCube d m), ∀ {r : ℝ},
      0 < r →
      r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth) →
      axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) ⊆ U)
    (hcutoff :
      Real.sqrt (((2 * (cubeRadius (originCube d m) /
        (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
        ((∫ y, ‖openParentGradientExtension U uU y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y,
            ‖(sigma0⁻¹ • hilbertifyVecField
              (openParentDatumExtension U H)) y‖ ^ (2 : ℕ) ∂volume)) < level) :
    sqWeightedMeasure (openParentGradientExtension U uU) volume
        ({x | M * level < ‖openParentGradientExtension U uU x‖} ∩
          openCubeSet (originCube d m)) ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure (openParentGradientExtension U uU) volume
            ({x | level / 2 < ‖openParentGradientExtension U uU x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure
              (sigma0⁻¹ • hilbertifyVecField (openParentDatumExtension U H)) volume
              ({x | eps * level / 2 <
                ‖(sigma0⁻¹ • hilbertifyVecField
                  (openParentDatumExtension U H)) x‖} ∩ U)) := by
  let Q : Set (Vec d) := openCubeSet (originCube d m)
  let F : Vec d → HilbertVec d := openParentGradientExtension U uU
  let Hext : Vec d → Vec d := openParentDatumExtension U H
  let gext : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField Hext
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hF : MemLp F 2 volume := by
    change MemLp (U.indicator (hilbertifyVecField uU.grad)) 2 volume
    rw [memLp_indicator_iff_restrict hUmeas]
    exact memHilbertVectorL2_hilbertifyVecField uU.grad_memVectorL2
  have hHext : MemLp (hilbertifyVecField Hext) 2 volume := by
    rw [show hilbertifyVecField Hext =
      U.indicator (hilbertifyVecField H) by
        simpa only [Hext] using
          hilbertifyVecField_openParentDatumExtension U H]
    rw [memLp_indicator_iff_restrict hUmeas]
    exact memHilbertVectorL2_hilbertifyVecField hH
  have hgext : MemLp gext 2 volume := hHext.const_smul sigma0⁻¹
  have hcutoff' :
      Real.sqrt (((2 * (cubeRadius (originCube d m) /
        (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
        ((∫ y, ‖F y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖gext y‖ ^ (2 : ℕ) ∂volume)) < level := by
    simpa only [F, Hext, gext] using hcutoff
  have hlevel_pos : 0 < level :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff'
  let T : Set (Vec d) := {x | M * level < ‖F x‖} ∩ Q
  obtain ⟨D, radius, hDnull, hradius⟩ :=
    exists_globalStoppingFamily depth F gext eps M level hF hgext heps hM
      hcutoff' T (by intro x hx; exact hx.1)
  let K : ℝ≥0∞ := oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  have hvitali : sqWeightedMeasure F volume (T ∩ D) ≤
      K * oneStoppingBallTailControl F gext eps level U := by
    apply measure_le_mul_measure_of_vitali_stopping_family
      (sqWeightedMeasure F volume) (oneStoppingBallTailControl F gext eps level)
      (T ∩ D) U radius
      (cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth)) 5 K
    · intro x hx
      exact (hradius x hx).2.1
    · intro x hx
      exact (hradius x hx).1
    · norm_num
    · intro x hx
      obtain ⟨hr, hcutoffx, hstop, hlast⟩ := hradius x hx
      have hxQ : x ∈ openCubeSet (originCube d m) := hx.1.2
      have hsub := hparent x hxQ hr hcutoffx
      obtain ⟨_hF, _hHext, hlocalF, hlocalweak⟩ :=
        openParent_axisCube_inputs hU hsub uU H hH hweak
      have hball := sqWeightedMeasure_oneStoppingBall_le G hq x hr hsigma0
        heps heps_one (lt_of_lt_of_le zero_lt_one hM) hlevel_pos hcutoffx
        F Hext hF hHext
        (openParentLocalSolution U (stoppingComparisonParentCorner x (radius x) depth)
          (stoppingComparisonParentSide (radius x) depth) uU hsub)
        (by simpa only [F] using hlocalF)
        (by simpa only [Hext] using hlocalweak)
        (by simpa only [gext] using hstop)
        (by simpa only [gext] using hlast)
      have hmono :
          sqWeightedMeasure F volume ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
            sqWeightedMeasure F volume
              ({y | M * level < ‖F y‖} ∩ Metric.closedBall x (5 * radius x)) := by
        apply measure_mono
        intro y hy
        exact ⟨hy.1.1.1, hy.2⟩
      calc
        sqWeightedMeasure F volume
            ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
            sqWeightedMeasure F volume
              ({y | M * level < ‖F y‖} ∩
                Metric.closedBall x (5 * radius x)) := hmono
        _ ≤ K *
            (sqWeightedMeasure F volume
                ({y | level / 2 < ‖F y‖} ∩ Metric.closedBall x (radius x)) +
              ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
                sqWeightedMeasure gext volume
                  ({y | eps * level / 2 < ‖gext y‖} ∩
                    Metric.closedBall x (radius x))) := by
              simpa only [K, gext] using hball
        _ = K * oneStoppingBallTailControl F gext eps level
            (Metric.closedBall x (radius x)) := by
              rw [oneStoppingBallTailControl_apply F gext eps level
                measurableSet_closedBall]
    · intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
      obtain ⟨hr, hcutoffx, _hstop, _hlast⟩ := hradius x hx
      have hsub := hparent x hx.1.2 hr hcutoffx
      apply hsub
      rw [stoppingComparisonParent_axisCube_eq_ball x hr depth]
      have hpow : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
      have hmult : 1 < stoppingComparisonParentMultiplier depth := by
        rw [stoppingComparisonParentMultiplier]
        nlinarith
      exact Metric.closedBall_subset_ball (lt_mul_of_one_lt_left hr hmult) hyx
  have hnuD : sqWeightedMeasure F volume Dᶜ = 0 :=
    MeasureTheory.withDensity_absolutelyContinuous volume _ hDnull
  have hTD : sqWeightedMeasure F volume (T ∩ D) =
      sqWeightedMeasure F volume T :=
    MeasureTheory.measure_inter_conull hnuD
  have hkappa : oneStoppingBallTailControl F gext eps level U =
      sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
        ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
          sqWeightedMeasure gext volume
            ({x | eps * level / 2 < ‖gext x‖} ∩ U) :=
    oneStoppingBallTailControl_apply_ambient F gext eps level hUmeas
  change sqWeightedMeasure F volume T ≤
    oneStoppingBallCoefficient depth G *
      (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
        ENNReal.ofReal (eps ^ (2 : ℕ))) *
      (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
        ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
          sqWeightedMeasure gext volume
            ({x | eps * level / 2 < ‖gext x‖} ∩ U))
  calc
    sqWeightedMeasure F volume T =
        sqWeightedMeasure F volume (T ∩ D) := hTD.symm
    _ ≤ K * oneStoppingBallTailControl F gext eps level U := hvitali
    _ = K *
        (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure gext volume
              ({x | eps * level / 2 < ‖gext x‖} ∩ U)) := by
          rw [hkappa]
    _ = oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure gext volume
              ({x | eps * level / 2 < ‖gext x‖} ∩ U)) := by
          rfl

end CubeCalderonZygmund

end

end Homogenization
