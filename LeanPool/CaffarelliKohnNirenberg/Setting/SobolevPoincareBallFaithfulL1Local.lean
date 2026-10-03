/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantPos
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Finiteness

/-!
# Approximation lemmas for Sobolev–Poincaré on Euclidean balls

These lemmas transfer smooth Euclidean-ball Poincaré estimates to W¹,¹ data.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

private theorem euclideanBall_eq_vec3Ball_faithful {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private theorem smooth_euclideanBall_poincareL1
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) (g : Vec3 → ℝ)
    (hg : ContDiff ℝ 1 g) :
    ∫ x in euclideanBall x₀ r,
        |g x - average (volume.restrict (euclideanBall x₀ r)) g| ∂volume ≤
      poincareSobolevL1Constant.toReal *
        (volume (euclideanBall x₀ r)).toReal ^ (1 / 3 : ℝ) *
          ∫ x in euclideanBall x₀ r, ‖fderiv ℝ g x‖ ∂volume := by
  let B : Set Vec3 := euclideanBall x₀ r
  let μ : Measure Vec3 := volume.restrict B
  let f : Vec3 → ℝ := fun x => g x - average μ g
  have hvoltop : volume B < ∞ := by
    change volume (euclideanBall x₀ r) < ∞
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, Measure.restrict_apply_univ] using hvoltop
  have hfcont : Continuous f := hg.continuous.sub continuous_const
  have hfmem : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    exact memLp_euclideanBall_of_continuous hr hfcont (ENNReal.ofReal (3 / 2 : ℝ))
  have hone : MemLp (fun _ : Vec3 => (1 : ℝ)) (ENNReal.ofReal (3 : ℝ)) μ :=
    memLp_const 1
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq hpq hfmem hone
  have hconst :
      (∫ x, ‖(1 : ℝ)‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) =
        (volume B).toReal ^ (1 / 3 : ℝ) := by
    rw [integral_const]
    rw [Measure.real_def]
    simp only [Real.norm_eq_abs, abs_one]
    have hμ : μ Set.univ = volume B := by
      change (volume.restrict B) Set.univ = volume B
      exact Measure.restrict_apply_univ B
    rw [hμ]
    norm_num
  have hholder' :
      ∫ x in B, |f x| ∂volume ≤
        (∫ x in B, |f x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) *
          (volume B).toReal ^ (1 / 3 : ℝ) := by
    simpa [μ, Real.norm_eq_abs, Measure.real_def, hconst] using hholder
  have hLp :
      lpNorm f (3 / 2 : NNReal) μ =
        (∫ x, ‖f x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
    simpa using lpNorm_nnreal_eq_integral_norm_rpow
      (f := f) (μ := μ) (p := (3 / 2 : NNReal)) (by norm_num) hfcont.aestronglyMeasurable
  have hP :
      (∫ x in B, |f x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1Constant.toReal *
          ∫ x in B, ‖fderiv ℝ g x‖ ∂volume := by
    simpa [integralAverage, B, f, μ] using poincareSobolevL1_ball x₀ hr g hg
  have hP' : lpNorm f (3 / 2 : NNReal) μ ≤
      poincareSobolevL1Constant.toReal *
        ∫ x in B, ‖fderiv ℝ g x‖ ∂volume := by
    rw [hLp]
    exact hP
  calc
    ∫ x in B, |f x| ∂volume ≤
        lpNorm f (3 / 2 : NNReal) μ * (volume B).toReal ^ (1 / 3 : ℝ) := by
          rw [hLp]
          exact hholder'
    _ ≤ (poincareSobolevL1Constant.toReal *
          ∫ x in B, ‖fderiv ℝ g x‖ ∂volume) *
          (volume B).toReal ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hP' (by positivity)
    _ = poincareSobolevL1Constant.toReal *
        (volume B).toReal ^ (1 / 3 : ℝ) *
          ∫ x in B, ‖fderiv ℝ g x‖ ∂volume := by ring
    _ = _ := by simp [B]

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hclosed_1 :
    ∀ (x₀ : Vec3) {r s : ℝ},
      (0 : ℝ) < r →
        (0 : ℝ) < s →
          s < r →
            let B : Set Vec3 := euclideanBall x₀ r;
            let D : Set Vec3 := euclideanBall x₀ s;
            let ε₀ : ℝ := (r - s) / (6 : ℝ);
            ∀ x ∈ D, Metric.closedBall x ε₀ ⊆ B
    := by
  intro x₀ r s hr hs hsr B D ε₀ x hx y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
  have hxnorm : vecEuclideanNorm (x - x₀) < s :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hx
  have hyx : dist y x ≤ ε₀ := by
    simpa [Metric.mem_closedBall] using hy
  have heuc : vecEuclideanNorm (y - x) ≤ 3 * ‖y - x‖ := by
    have heq : vecEuclideanNorm (y - x) = spaceEuclideanNorm (y - x) := by
      simp [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two]
    rw [heq]
    exact euclideanNorm_le_three_mul_space_norm (y - x)
  have htri : vecEuclideanNorm (y - x₀) ≤
      vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := by
    have heq : y - x₀ = (y - x) + (x - x₀) := by abel
    rw [heq]
    exact vecEuclideanNorm_add_le _ _
  have hybound : vecEuclideanNorm (y - x) ≤ 3 * ε₀ := by
    calc
      vecEuclideanNorm (y - x) ≤ 3 * ‖y - x‖ := heuc
      _ ≤ 3 * ε₀ := by
        rw [dist_eq_norm] at hyx
        exact mul_le_mul_of_nonneg_left hyx (by norm_num)
  have hsum : vecEuclideanNorm (y - x₀) < 3 * ε₀ + s := by
    calc
      vecEuclideanNorm (y - x₀) ≤
          vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := htri
      _ < 3 * ε₀ + s := add_lt_add_of_le_of_lt hybound hxnorm
  dsimp [ε₀] at hsum
  have hsrpos : 0 < r - s := sub_pos.mpr hsr
  have hsum' : vecEuclideanNorm (y - x₀) < r := by
    nlinarith only [hsum, hsrpos]
  exact hsum'

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hweakExt_2 :
    ∀ (x₀ : Vec3) {r : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      MeasurableSet B →
        ∀ (i : Fin (3 : ℕ)),
          HasWeakPartialDerivOn B i (B.indicator (u.toFun (U := euclideanBall x₀ r)))
            (B.indicator fun (x : Vec3) => u.grad (U := euclideanBall x₀ r) x i)
    := by
  intro x₀ r u B hBmeas i φ hφ hφCompact hφSupport
  have hweak := u.hasWeakPartialDerivOn i φ hφ hφCompact hφSupport
  calc
    ∫ x in B, B.indicator u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in B, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
          apply setIntegral_congr_fun hBmeas
          intro x hx
          simp [Set.indicator_of_mem hx]
    _ = -∫ x in B, u.grad x i * φ x ∂volume := hweak
    _ = -∫ x in B, B.indicator (fun y => u.grad y i) x * φ x ∂volume := by
          congr 1
          apply setIntegral_congr_fun hBmeas
          intro x hx
          simp [Set.indicator_of_mem hx]

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hvalIntD_3 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (n : ℕ),
            MemLp (ε := ℝ)
              (fun (x : Vec (3 : ℕ)) =>
                mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                  u.toFun (U := euclideanBall x₀ r) x)
              (1 : ℝ≥0∞) μ) →
          Tendsto
              (fun (n : ℕ) =>
                lpNorm (E := ℝ)
                  (fun (x : Vec (3 : ℕ)) =>
                    mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      u.toFun (U := euclideanBall x₀ r) x)
                  (1 : ℝ≥0∞) μ)
              atTop (𝓝 (0 : ℝ)) →
            Tendsto
              (fun (n : ℕ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) =>
                  |mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      u.toFun (U := euclideanBall x₀ r) x|)
              atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hErrMem hvalLpD
  have hfun : (fun n => ∫ x in D,
      |mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x| ∂volume) =
      (fun n => lpNorm
        (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x)
        1 μ) := by
    funext n
    change ∫ x, ‖mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x‖ ∂μ = _
    rw [lpNorm_one_eq_integral_norm (hErrMem n).aestronglyMeasurable]
  rw [hfun]
  exact hvalLpD

private lemma w1p_euclideanBall_poincareL1_inner_faithful_havgDiff_4 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (n : ℕ),
            MemLp (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n))
              (1 : ℝ≥0∞) μ) →
          Integrable (u.toFun (U := euclideanBall x₀ r)) μ →
            ∀ (n : ℕ),
              average μ
                    (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)) -
                  average μ (u.toFun (U := euclideanBall x₀ r)) =
                (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) =>
                    mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      u.toFun (U := euclideanBall x₀ r) x
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hvD huInt n
  have hVInt : Integrable
      (mollify (B.indicator u.toFun) (ε n) (hεpos n)) μ :=
    memLp_one_iff_integrable.mp (hvD n)
  calc
    average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) -
        average μ u.toFun =
        average μ (fun x => mollify (B.indicator u.toFun)
          (ε n) (hεpos n) x - u.toFun x) :=
      (MeasureTheory.average_sub hVInt huInt).symm
    _ = (volume D).toReal⁻¹ *
        ∫ x in D, mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x
          ∂volume := by
      change (⨍ x in D, mollify (B.indicator u.toFun)
        (ε n) (hεpos n) x - u.toFun x ∂volume) = _
      rw [MeasureTheory.setAverage_eq]
      simp [Measure.real_def]

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hconstLp_5 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        Tendsto
            (fun (n : ℕ) =>
              average μ
                  (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)) -
                average μ (u.toFun (U := euclideanBall x₀ r)))
            atTop (𝓝 (0 : ℝ)) →
          Tendsto
            (fun (n : ℕ) =>
              lpNorm (E := ℝ)
                (fun (_ : Vec3) =>
                  average μ
                      (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)) -
                    average μ (u.toFun (U := euclideanBall x₀ r)))
                (1 : ℝ≥0∞) μ)
            atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos havgDiffTendsto
  have hnorm := (continuous_norm.tendsto 0).comp havgDiffTendsto
  have hmul := hnorm.mul_const ((volume D).toReal)
  have hformula (n : ℕ) : lpNorm (fun _ : Vec3 =>
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) - average μ u.toFun)
      1 μ =
      ‖average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) -
        average μ u.toFun‖ * (volume D).toReal := by
    rw [lpNorm_const' (μ := μ) (p := (1 : ℝ≥0∞))
      (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)]
    simp [μ, Measure.real_def]
  have hfun : (fun n => lpNorm (fun _ : Vec3 =>
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) - average μ u.toFun)
      1 μ) = (fun n =>
        ‖average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) -
          average μ u.toFun‖ * (volume D).toReal) := by
    funext n
    exact hformula n
  rw [hfun]
  convert hmul using 1 <;> simp

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hcenterErrLp_6 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (n : ℕ),
            MemLp (ε := ℝ)
              (fun (x : Vec (3 : ℕ)) =>
                mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                  u.toFun (U := euclideanBall x₀ r) x)
              (1 : ℝ≥0∞) μ) →
          Tendsto
              (fun (n : ℕ) =>
                lpNorm (E := ℝ)
                  (fun (x : Vec (3 : ℕ)) =>
                    mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      u.toFun (U := euclideanBall x₀ r) x)
                  (1 : ℝ≥0∞) μ)
              atTop (𝓝 (0 : ℝ)) →
            Tendsto
                (fun (n : ℕ) =>
                  lpNorm (E := ℝ)
                    (fun (_ : Vec3) =>
                      average μ
                          (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                            (hεpos n)) -
                        average μ (u.toFun (U := euclideanBall x₀ r)))
                    (1 : ℝ≥0∞) μ)
                atTop (𝓝 (0 : ℝ)) →
              Tendsto
                (fun (n : ℕ) =>
                  lpNorm (E := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                          average μ
                            (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                              (hεpos n)) -
                        (u.toFun (U := euclideanBall x₀ r) x -
                          average μ (u.toFun (U := euclideanBall x₀ r))))
                    (1 : ℝ≥0∞) μ)
                atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hErrMem hvalLpD hconstLp
  have hsum : Tendsto (fun n => lpNorm
      (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x)
      1 μ + lpNorm (fun _ : Vec3 =>
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) - average μ u.toFun)
        1 μ) atTop (nhds 0) := by simpa using hvalLpD.add hconstLp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => lpNorm_nonneg)
  filter_upwards [] with n
  have hsub := lpNorm_sub_le
    (f := fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x)
    (g := fun _ : Vec3 =>
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) - average μ u.toFun)
    (hErrMem n) (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hleft : (fun x =>
      (mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
        average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))) -
        (u.toFun x - average μ u.toFun)) =
      (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x -
        (average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) -
          average μ u.toFun)) := by
    funext x
    ring
  rw [hleft]
  exact hsub

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hcenterLp_7 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        Tendsto
            (fun (n : ℕ) =>
              lpNorm (E := ℝ)
                (fun (x : Vec (3 : ℕ)) =>
                  mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      average μ
                        (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                          (hεpos n)) -
                    (u.toFun (U := euclideanBall x₀ r) x -
                      average μ (u.toFun (U := euclideanBall x₀ r))))
                (1 : ℝ≥0∞) μ)
            atTop (𝓝 (0 : ℝ)) →
          (∀ (n : ℕ),
              MemLp (ε := ℝ)
                (fun (x : Vec (3 : ℕ)) =>
                  mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                    average μ
                      (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)))
                (1 : ℝ≥0∞) μ) →
            MemLp (ε := ℝ)
                (fun (x : Vec (3 : ℕ)) =>
                  u.toFun (U := euclideanBall x₀ r) x -
                    average μ (u.toFun (U := euclideanBall x₀ r)))
                (1 : ℝ≥0∞) μ →
              Tendsto
                (fun (n : ℕ) =>
                  lpNorm (E := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                        average μ
                          (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                            (hεpos n)))
                    (1 : ℝ≥0∞) μ)
                atTop
                (𝓝
                  (lpNorm (E := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      u.toFun (U := euclideanBall x₀ r) x -
                        average μ (u.toFun (U := euclideanBall x₀ r)))
                    (1 : ℝ≥0∞) μ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hcenterErrLp hcenterMem hcenterMem0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcenterErrLp
    (Eventually.of_forall fun _ => norm_nonneg _)
  filter_upwards [] with n
  have h₁ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := fun x => u.toFun x - average μ u.toFun)
    (g := fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)))
    (hcenterMem n) (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have h₂ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)))
    (g := fun x => u.toFun x - average μ u.toFun)
    hcenterMem0 (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  let qn : Vec3 → ℝ := fun x => mollify (B.indicator u.toFun)
    (ε n) (hεpos n) x - average μ (mollify (B.indicator u.toFun)
      (ε n) (hεpos n))
  let q : Vec3 → ℝ := fun x => u.toFun x - average μ u.toFun
  have hforward_eq : lpNorm (qn - q) 1 μ = lpNorm
      (fun x => qn x - q x) 1 μ := by congr 1
  have h₁' := h₁
  rw [hforward_eq] at h₁'
  have hreverse_eq : lpNorm (q - qn) 1 μ = lpNorm
      (fun x => qn x - q x) 1 μ := by
    rw [lpNorm_sub_comm]
    exact hforward_eq
  have h₂' : lpNorm qn 1 μ ≤ lpNorm q 1 μ + lpNorm (fun x => qn x - q x) 1 μ := by
    rw [hreverse_eq] at h₂
    exact h₂
  exact (abs_le).2 ⟨
    (neg_le_sub_iff_le_add).2 (by simpa [qn, q, add_comm] using h₁'),
    (sub_le_iff_le_add).2 (by simpa [qn, q, add_comm] using h₂')⟩

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hleftLimit_8 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (n : ℕ),
            MemLp (ε := ℝ)
              (fun (x : Vec (3 : ℕ)) =>
                mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                  average μ
                    (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)))
              (1 : ℝ≥0∞) μ) →
          MemLp (ε := ℝ)
              (fun (x : Vec (3 : ℕ)) =>
                u.toFun (U := euclideanBall x₀ r) x - average μ (u.toFun (U := euclideanBall x₀ r)))
              (1 : ℝ≥0∞) μ →
            Tendsto
                (fun (n : ℕ) =>
                  lpNorm (E := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                        average μ
                          (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                            (hεpos n)))
                    (1 : ℝ≥0∞) μ)
                atTop
                (𝓝
                  (lpNorm (E := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      u.toFun (U := euclideanBall x₀ r) x -
                        average μ (u.toFun (U := euclideanBall x₀ r)))
                    (1 : ℝ≥0∞) μ)) →
              Tendsto (β := ℝ)
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) =>
                    |mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                        average μ
                          (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                            (hεpos n))|)
                atTop
                (𝓝
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) =>
                    |u.toFun (U := euclideanBall x₀ r) x -
                        average μ (u.toFun (U := euclideanBall x₀ r))|))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hcenterMem hcenterMem0 hcenterLp
  have hleftEq (n : ℕ) :
      ∫ x in D,
        |mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
          average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))| ∂volume =
        lpNorm (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
          average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))) 1 μ := by
    change ∫ x, ‖mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
      average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))‖ ∂μ = _
    rw [lpNorm_one_eq_integral_norm (hcenterMem n).aestronglyMeasurable]
  have hleftEq0 :
      ∫ x in D, |u.toFun x - average μ u.toFun| ∂volume =
        lpNorm (fun x => u.toFun x - average μ u.toFun) 1 μ := by
    change ∫ x, ‖u.toFun x - average μ u.toFun‖ ∂μ = _
    rw [lpNorm_one_eq_integral_norm hcenterMem0.aestronglyMeasurable]
  have hfun : (fun n => ∫ x in D,
      |mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
        average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))| ∂volume) =
      (fun n => lpNorm (fun x => mollify (B.indicator u.toFun)
        (ε n) (hεpos n) x - average μ (mollify (B.indicator u.toFun)
        (ε n) (hεpos n))) 1 μ) := by
    funext n
    exact hleftEq n
  rw [hfun, hleftEq0]
  exact hcenterLp

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hgradExtConv_9 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      MeasurableSet D →
        D ⊆ B →
          ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            (∀ (i : Fin (3 : ℕ)),
                Tendsto
                  (fun (n : ℕ) =>
                    eLpNorm (ε := ℝ)
                      (fun (x : Vec (3 : ℕ)) =>
                        mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i)
                            (ε n) (hεpos n) x -
                          B.indicator (fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) x)
                      (1 : ℝ≥0∞) μ)
                  atTop (𝓝 (0 : ℝ≥0∞))) →
              ∀ (i : Fin (3 : ℕ)),
                Tendsto
                  (fun (n : ℕ) =>
                    eLpNorm (ε := ℝ)
                      (fun (x : Vec (3 : ℕ)) =>
                        mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i)
                            (ε n) (hεpos n) x -
                          u.grad (U := euclideanBall x₀ r) x i)
                      (1 : ℝ≥0∞) μ)
                  atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ r s u B D ε₀ ε μ hDmeas hDsubB hεpos hgradD i
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hgradD i)
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [] with n
  calc
    eLpNorm (fun x => mollify (B.indicator (fun y => u.grad y i))
        (ε n) (hεpos n) x - u.grad x i) 1 μ =
      eLpNorm (fun x => mollify (B.indicator (fun y => u.grad y i))
        (ε n) (hεpos n) x - B.indicator (fun y => u.grad y i) x) 1 μ := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hDmeas] with x hx
        simp [Set.indicator_of_mem (hDsubB hx)]
    _ ≤ eLpNorm (fun x => mollify (B.indicator (fun y => u.grad y i))
        (ε n) (hεpos n) x - B.indicator (fun y => u.grad y i) x) 1 μ := le_rfl

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hHConv_10 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (i : Fin (3 : ℕ)),
            Tendsto
              (fun (n : ℕ) =>
                lpNorm (E := ℝ)
                  (fun (x : Vec (3 : ℕ)) =>
                    mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i)
                        (ε n) (hεpos n) x -
                      u.grad (U := euclideanBall x₀ r) x i)
                  (1 : ℝ≥0∞) μ)
              atTop (𝓝 (0 : ℝ))) →
          let H : Fin (3 : ℕ) → ℕ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (n : ℕ) (x : Vec3) =>
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                  (hεpos n) x| -
              |u.grad (U := euclideanBall x₀ r) x i|;
          (∀ (n : ℕ) (i : Fin (3 : ℕ)),
              MemLp (ε := ℝ)
                (fun (x : Vec (3 : ℕ)) =>
                  mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                    (hεpos n) x)
                (1 : ℝ≥0∞) μ) →
            (∀ (i : Fin (3 : ℕ)),
                MemLp (ε := ℝ) (fun (x : Vec (3 : ℕ)) => u.grad (U := euclideanBall x₀ r) x i)
                  (1 : ℝ≥0∞) μ) →
              ∀ (i : Fin (3 : ℕ)),
                Tendsto (fun (n : ℕ) => lpNorm (H i n) (1 : ℝ≥0∞) μ) atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hgradLp H hgradMollifyMem hgradDMem i
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hgradLp i)
    (Eventually.of_forall fun _ => lpNorm_nonneg)
  filter_upwards [] with n
  have hErr : MemLp (fun x =>
      mollify (B.indicator (fun y => u.grad y i)) (ε n) (hεpos n) x -
        u.grad x i) 1 μ := (hgradMollifyMem n i).sub (hgradDMem i)
  have hmono := lpNorm_mono_real (hErr.abs) (fun x => by
    change ‖H i n x‖ ≤ |mollify
      (B.indicator (fun y => u.grad y i)) (ε n) (hεpos n) x - u.grad x i|
    exact norm_abs_sub_abs _ _)
  simpa [lpNorm_abs hErr.aestronglyMeasurable] using hmono

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hAGConv_11 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      let G : Vec3 → ℝ := w1pGradientNorm (U := euclideanBall x₀ r) u;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
          ∑ i : Fin (3 : ℕ),
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x|;
        let H : Fin (3 : ℕ) → ℕ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (n : ℕ) (x : Vec3) =>
          |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x| -
            |u.grad (U := euclideanBall x₀ r) x i|;
        (∀ (n : ℕ) (i : Fin (3 : ℕ)), MemLp (H i n) (1 : ℝ≥0∞) μ) →
          Tendsto (fun (n : ℕ) => ∑ i : Fin (3 : ℕ), lpNorm (H i n) (1 : ℝ≥0∞) μ) atTop
              (𝓝 (0 : ℝ)) →
            Tendsto (fun (n : ℕ) => lpNorm (E := ℝ) (fun (x : Vec3) => A n x - G x) (1 : ℝ≥0∞) μ)
              atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ G hεpos A H hHMem hsumH
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumH
    (Eventually.of_forall fun _ => lpNorm_nonneg)
  filter_upwards [] with n
  have hsum := lpNorm_sum_le (p := (1 : ℝ≥0∞)) (μ := μ)
    (s := (Finset.univ : Finset (Fin 3))) (fun i _ => hHMem n i)
    (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hEq : (fun x => A n x - G x) = fun x => ∑ i : Fin 3, H i n x := by
    funext x
    simp [A, G, H, w1pGradientNorm, Finset.sum_sub_distrib]
  rw [show lpNorm (fun x => A n x - G x) 1 μ =
      lpNorm (fun x => ∑ i : Fin 3, H i n x) 1 μ by
        rw [hEq]]
  exact hsum

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hAIntTendsto_12 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      let G : Vec3 → ℝ := w1pGradientNorm (U := euclideanBall x₀ r) u;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
          ∑ i : Fin (3 : ℕ),
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x|;
        (∀ (n : ℕ), MemLp (A n) (1 : ℝ≥0∞) μ) →
          MemLp G (1 : ℝ≥0∞) μ →
            Tendsto
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => A n x - G x)
                atTop (𝓝 (0 : ℝ)) →
              Tendsto (β := ℝ)
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => A n x)
                atTop
                (𝓝
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => G x))
    := by
  intro x₀ r s u B D ε₀ ε μ G hεpos A hAMem hGMem hAGSigned
  have hsum : Tendsto
      (fun n => (∫ x in D, A n x - G x ∂volume) + ∫ x in D, G x ∂volume)
      atTop (nhds (0 + ∫ x in D, G x ∂volume)) :=
    hAGSigned.add (tendsto_const_nhds)
  have hfun : (fun n => ∫ x in D, A n x ∂volume) =
      (fun n => (∫ x in D, A n x - G x ∂volume) + ∫ x in D, G x ∂volume) := by
    funext n
    have hAInt : Integrable (A n) μ := memLp_one_iff_integrable.mp (hAMem n)
    have hGInt : Integrable G μ := memLp_one_iff_integrable.mp hGMem
    change ∫ x, A n x ∂μ =
      (∫ x, (A n x - G x) ∂μ) + ∫ x, G x ∂μ
    rw [integral_sub hAInt hGInt]
    ring
  rw [hfun]
  simpa using hsum

private lemma w1p_euclideanBall_poincareL1_inner_faithful_happroxIneq_13 :
    ∀ (x₀ : Vec3) {r s : ℝ},
      (0 : ℝ) < s →
        ∀ (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
          let B : Set Vec3 := euclideanBall x₀ r;
          let D : Set Vec3 := euclideanBall x₀ s;
          let ε₀ : ℝ := (r - s) / (6 : ℝ);
          let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
          let μ : Measure Vec3 := Measure.restrict volume D;
          ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
              ∑ i : Fin (3 : ℕ),
                |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                    (hεpos n) x|;
            (∀ (n : ℕ),
                ContDiff ℝ (1 : WithTop ℕ∞)
                  (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n))) →
              (∀ (n : ℕ),
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) =>
                      norm (E := Vec (3 : ℕ) →L[ℝ] ℝ)
                        (fderiv ℝ
                          (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                            (hεpos n))
                          x))
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => A n x)) →
                ∀ (n : ℕ),
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) =>
                      |mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                          average μ
                            (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n)
                              (hεpos n))|) ≤
                    poincareSobolevL1Constant.toReal *
                        ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D) ^ (1 / 3 : ℝ) *
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => A n x
    := by
  intro x₀ r s hs u B D ε₀ ε μ hεpos A hvCont hderivInt n
  calc
    ∫ x in D,
        |mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
          average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))| ∂volume ≤
      poincareSobolevL1Constant.toReal * (volume D).toReal ^ (1 / 3 : ℝ) *
        ∫ x in D, ‖fderiv ℝ (mollify (B.indicator u.toFun)
          (ε n) (hεpos n)) x‖ ∂volume := by
        exact smooth_euclideanBall_poincareL1 x₀ hs
          (mollify (B.indicator u.toFun) (ε n) (hεpos n)) (hvCont n)
    _ = _ := by rw [hderivInt n]

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hDpos_1 :
    ∀ (x₀ : Vec3) {s : ℝ},
      (0 : ℝ) < s →
        let D : Set Vec3 := euclideanBall x₀ s;
        LT.lt (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) D : ℝ≥0∞) (∞ : ℝ≥0∞) →
          (0 : ℝ) < ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D)
    := by
  intro x₀ s hs D hvolD
  change 0 < (volume (euclideanBall x₀ s)).toReal
  have hvol : volume D ≠ 0 := by
    change volume (euclideanBall x₀ s) ≠ 0
    rw [euclideanBall_eq_vec3Ball_faithful hs, volume_vec3Ball_eq]
    positivity
  exact ENNReal.toReal_pos hvol hvolD.ne

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hεtendsto_2 :
    ∀ {r s : ℝ},
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      Tendsto ε atTop (𝓝 (0 : ℝ))
    := by
  intro r s ε₀ ε
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [add_comm] using tendsto_atTop_add_const_left atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  simpa [ε, div_eq_mul_inv] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ε₀) atTop (nhds ε₀)).mul hinv)

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hvalD_3 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      MeasurableSet D →
        D ⊆ B →
          ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                        B.indicator (u.toFun (U := euclideanBall x₀ r)) x)
                    (1 : ℝ≥0∞) volume)
                atTop (𝓝 (0 : ℝ≥0∞)) →
              Tendsto
                (fun (n : ℕ) =>
                  eLpNorm (ε := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                        u.toFun (U := euclideanBall x₀ r) x)
                    (1 : ℝ≥0∞) μ)
                atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ r s u B D ε₀ ε μ hDmeas hDsubB hεpos hvalExtConv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hvalExtConv
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [] with n
  apply (eLpNorm_congr_ae ?_).trans_le
  · exact eLpNorm_mono_measure _ Measure.restrict_le_self
  filter_upwards [ae_restrict_mem (μ := volume) hDmeas] with x hx
  simp [B, Set.indicator_of_mem (hDsubB hx)]

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hgradD_4 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        Tendsto ε atTop (𝓝 (0 : ℝ)) →
          (∀ (i : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                (B.indicator fun (x : Vec3) => u.grad (U := euclideanBall x₀ r) x i) (1 : ℝ≥0∞)
                volume) →
            ∀ (i : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  eLpNorm (ε := ℝ)
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i)
                          (ε n) (hεpos n) x -
                        B.indicator (fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) x)
                    (1 : ℝ≥0∞) μ)
                atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hεtendsto hgradExt i
  have hglobal := tendsto_eLpNorm_sub_zero_mollify (by norm_num)
    ENNReal.one_ne_top (hgradExt i) hεtendsto hεpos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hglobal
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [] with n
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hvalSigned_5 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let _ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        Tendsto
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                (Measure.restrict volume (euclideanBall x₀ s)) fun (x : Vec3) =>
                |mollify ((euclideanBall x₀ r).indicator (u.toFun (U := euclideanBall x₀ r)))
                      ((fun (n : ℕ) => (r - s) / (6 : ℝ) / ((↑n : ℝ) + (1 : ℝ))) n) (hεpos n) x -
                    u.toFun (U := euclideanBall x₀ r) x|)
            atTop (𝓝 (0 : ℝ)) →
          Tendsto
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) =>
                mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                  u.toFun (U := euclideanBall x₀ r) x)
            atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hvalIntD
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hvalIntD
    (Eventually.of_forall (fun _ => norm_nonneg _))
  filter_upwards [] with n
  simpa [μ, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm
      (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x))

private lemma w1p_euclideanBall_poincareL1_inner_faithful_havgTendsto_6 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        Tendsto
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) =>
                mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                  u.toFun (U := euclideanBall x₀ r) x)
            atTop (𝓝 (0 : ℝ)) →
          (∀ (n : ℕ),
              average μ
                    (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)) -
                  average μ (u.toFun (U := euclideanBall x₀ r)) =
                (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) =>
                    mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n) x -
                      u.toFun (U := euclideanBall x₀ r) x) →
            Tendsto
              (fun (n : ℕ) =>
                average μ
                  (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)))
              atTop (𝓝 (average μ (u.toFun (U := euclideanBall x₀ r))))
    := by
  intro x₀ r s u B D ε₀ ε μ hεpos hvalSigned havgDiff
  apply tendsto_sub_nhds_zero_iff.mp
  have hmul :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (volume D).toReal⁻¹)
      atTop (nhds ((volume D).toReal⁻¹))).mul hvalSigned
  simpa only [havgDiff, mul_zero] using hmul

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hAErrInt_7 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let μ : Measure Vec3 := Measure.restrict volume D;
      let G : Vec3 → ℝ := w1pGradientNorm (U := euclideanBall x₀ r) u;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
          ∑ i : Fin (3 : ℕ),
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x|;
        Tendsto
            (fun (n : ℕ) =>
              lpNorm (E := ℝ) (m0 := MeasurableSpace.pi (X := fun (_ : Fin (3 : ℕ)) => ℝ))
                (fun (x : Vec3) =>
                  (fun (n : ℕ) (x : Vec3) =>
                        (∑ i : Fin (3 : ℕ),
                            |mollify
                                ((euclideanBall x₀ r).indicator fun (y : Vec3) =>
                                  u.grad (U := euclideanBall x₀ r) y i)
                                ((fun (n : ℕ) => (r - s) / (6 : ℝ) / ((↑n : ℝ) + (1 : ℝ))) n)
                                (hεpos n) x| :
                          ℝ))
                      n x -
                    w1pGradientNorm (U := euclideanBall x₀ r) u x)
                (1 : ℝ≥0∞) (Measure.restrict volume (euclideanBall x₀ s)))
            atTop (𝓝 (0 : ℝ)) →
          (∀ (n : ℕ), MemLp (ε := ℝ) (fun (x : Vec3) => A n x - G x) (1 : ℝ≥0∞) μ) →
            Tendsto
              (fun (n : ℕ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) => |A n x - G x|)
              atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ G hεpos A hAGConv hAErrMem
  have hfun : (fun n => ∫ x in D, |A n x - G x| ∂volume) =
      (fun n => lpNorm (fun x => A n x - G x) 1 μ) := by
    funext n
    change ∫ x, ‖A n x - G x‖ ∂μ = _
    rw [lpNorm_one_eq_integral_norm (hAErrMem n).aestronglyMeasurable]
  rw [hfun]
  exact hAGConv

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hAGSigned_8 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let _ : Measure Vec3 := Measure.restrict volume D;
      let G : Vec3 → ℝ := w1pGradientNorm (U := euclideanBall x₀ r) u;
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
          ∑ i : Fin (3 : ℕ),
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x|;
        Tendsto
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => |A n x - G x|)
            atTop (𝓝 (0 : ℝ)) →
          Tendsto
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => A n x - G x)
            atTop (𝓝 (0 : ℝ))
    := by
  intro x₀ r s u B D ε₀ ε μ G hεpos A hAErrInt
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAErrInt
    (Eventually.of_forall fun _ => norm_nonneg _)
  filter_upwards [] with n
  simpa [μ, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (fun x => A n x - G x))

private lemma w1p_euclideanBall_poincareL1_inner_faithful_hderivNorm_9 :
    ∀ (x₀ : Vec3) {r s : ℝ} (u : W1pFunction (euclideanBall x₀ r) (1 : ℝ≥0∞)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let D : Set Vec3 := euclideanBall x₀ s;
      let ε₀ : ℝ := (r - s) / (6 : ℝ);
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let A : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) =>
          ∑ i : Fin (3 : ℕ),
            |mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                (hεpos n) x|;
        (∀ (n : ℕ) (i : Fin (3 : ℕ)) {x : Vec3},
            x ∈ D →
              (fderiv ℝ (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n))
                      x :
                    Vec (3 : ℕ) → ℝ)
                  (basisVec i) =
                mollify (B.indicator fun (y : Vec3) => u.grad (U := euclideanBall x₀ r) y i) (ε n)
                  (hεpos n) x) →
          ∀ (n : ℕ) {x : Vec3},
            x ∈ D →
              norm (E := Vec (3 : ℕ) →L[ℝ] ℝ)
                  (fderiv ℝ
                    (mollify (B.indicator (u.toFun (U := euclideanBall x₀ r))) (ε n) (hεpos n)) x) =
                A n x
    := by
  intro x₀ r s u B D ε₀ ε hεpos A hderiv n x hx
  rw [opNorm_eq_sum_abs_basis]
  simp only [A]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hderiv n i hx]

/-- Local W¹,¹ Poincaré on a compactly contained Euclidean ball. -/
theorem w1p_euclideanBall_poincareL1_inner_faithful
    (x₀ : Vec3) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (u : W1pFunction (euclideanBall x₀ r) 1) :
    ∫ x in euclideanBall x₀ s,
        |u.toFun x - average (volume.restrict (euclideanBall x₀ s)) u.toFun|
          ∂volume ≤
      poincareSobolevL1Constant.toReal *
        (volume (euclideanBall x₀ s)).toReal ^ (1 / 3 : ℝ) *
          ∫ x in euclideanBall x₀ s, w1pGradientNorm u x ∂volume := by
  classical
  let B : Set Vec3 := euclideanBall x₀ r
  let D : Set Vec3 := euclideanBall x₀ s
  let ε₀ : ℝ := (r - s) / 6
  let ε : ℕ → ℝ := fun n => ε₀ / ((n : ℝ) + 1)
  let μ : Measure Vec3 := volume.restrict D
  let G : Vec3 → ℝ := w1pGradientNorm u
  have hBopen : IsOpen B := by
    change IsOpen (euclideanBall x₀ r)
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hDopen : IsOpen D := by
    change IsOpen (euclideanBall x₀ s)
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < s ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hDmeas : MeasurableSet D := hDopen.measurableSet
  have hDsubB : D ⊆ B := by
    intro x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    exact lt_trans
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hx) hsr
  have hvolD : volume D < ∞ := by
    change volume (euclideanBall x₀ s) < ∞
    rw [euclideanBall_eq_vec3Ball_faithful hs, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, Measure.restrict_apply_univ] using hvolD
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos hε₀pos (by positivity)
  let A : ℕ → Vec3 → ℝ := fun n x =>
    ∑ i : Fin 3, |mollify (B.indicator (fun y => u.grad y i))
      (ε n) (hεpos n) x|
  have hεle : ∀ n, ε n ≤ ε₀ := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hε₀pos.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hεtendsto := @w1p_euclideanBall_poincareL1_inner_faithful_hεtendsto_2 r s
  have hclosed := @w1p_euclideanBall_poincareL1_inner_faithful_hclosed_1 x₀ r s hr hs hsr
  have hclosedn (n : ℕ) : ∀ x ∈ D, Metric.closedBall x (ε n) ⊆ B := by
    intro x hx y hy
    apply hclosed x hx
    rw [Metric.mem_closedBall] at hy ⊢
    exact hy.trans (hεle n)
  have huB : MemLp u.toFun 1 (volume.restrict B) := by
    change MemLp u.toFun 1 (volumeOn B)
    exact u.memLp
  have hgradB (i : Fin 3) :
      MemLp (fun x => u.grad x i) 1 (volume.restrict B) := by
    change MemLp (fun x => u.grad x i) 1 (volumeOn B)
    exact u.grad_memLp i
  have huExt : MemLp (B.indicator u.toFun) 1 volume :=
    (memLp_indicator_iff_restrict hBmeas).2 huB
  have hgradExt (i : Fin 3) :
      MemLp (B.indicator (fun x => u.grad x i)) 1 volume :=
    (memLp_indicator_iff_restrict hBmeas).2 (hgradB i)
  have huLoc : LocallyIntegrable (B.indicator u.toFun) volume :=
    huExt.locallyIntegrable (by norm_num)
  have hgradLoc (i : Fin 3) :
      LocallyIntegrable (B.indicator (fun x => u.grad x i)) volume :=
    (hgradExt i).locallyIntegrable (by norm_num)
  have hweakExt (i : Fin 3) := @w1p_euclideanBall_poincareL1_inner_faithful_hweakExt_2 x₀ r u
    hBmeas i
  have hvalExtConv : Tendsto
      (fun n => eLpNorm (fun x => mollify (B.indicator u.toFun)
        (ε n) (hεpos n) x - B.indicator u.toFun x) 1 volume) atTop (nhds 0) :=
    tendsto_eLpNorm_sub_zero_mollify (by norm_num) ENNReal.one_ne_top huExt
      hεtendsto hεpos
  have hvalD := @w1p_euclideanBall_poincareL1_inner_faithful_hvalD_3 x₀ r s u hDmeas hDsubB hεpos
    hvalExtConv
  have hgradD (i : Fin 3) := @w1p_euclideanBall_poincareL1_inner_faithful_hgradD_4 x₀ r s u hεpos
    hεtendsto hgradExt i
  have hvCont (n : ℕ) : ContDiff ℝ 1
      (mollify (B.indicator u.toFun) (ε n) (hεpos n)) :=
    mollify_contDiff (hεpos n) huLoc (n := 1)
  have hderiv (n : ℕ) (i : Fin 3) {x : Vec3} (hx : x ∈ D) :
      (fderiv ℝ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) x)
        (basisVec i) =
          mollify (B.indicator (fun y => u.grad y i))
            (ε n) (hεpos n) x := by
    exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn hBopen huLoc
      (hgradLoc i) (hweakExt i) (hεpos n) (hclosedn n x hx)
  have huD : MemLp u.toFun 1 μ :=
    huB.mono_measure (Measure.restrict_mono_set volume hDsubB)
  have hvD (n : ℕ) : MemLp
      (mollify (B.indicator u.toFun) (ε n) (hεpos n)) 1 μ := by
    exact memLp_euclideanBall_of_continuous hs (hvCont n).continuous 1
  have hErrMem (n : ℕ) : MemLp
      (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x)
      1 μ := (hvD n).sub huD
  have hvalLpD : Tendsto
      (fun n => lpNorm
        (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x - u.toFun x)
        1 μ) atTop (nhds 0) := tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero hvalD
  have hvalIntD := @w1p_euclideanBall_poincareL1_inner_faithful_hvalIntD_3 x₀ r s u hεpos hErrMem
    hvalLpD
  have huInt : Integrable u.toFun μ := memLp_one_iff_integrable.mp huD
  have hvalSigned := @w1p_euclideanBall_poincareL1_inner_faithful_hvalSigned_5 x₀ r s u hεpos
    hvalIntD
  have havgDiff (n : ℕ) := @w1p_euclideanBall_poincareL1_inner_faithful_havgDiff_4 x₀ r s u hεpos
    hvD huInt n
  have havgTendsto : Tendsto
      (fun n => average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)))
      atTop (nhds (average μ u.toFun)) := by
    exact @w1p_euclideanBall_poincareL1_inner_faithful_havgTendsto_6 x₀ r s u hεpos hvalSigned
      havgDiff
  have havgDiffTendsto : Tendsto
      (fun n => average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n)) -
        average μ u.toFun) atTop (nhds 0) := by
    simpa using havgTendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => average μ u.toFun)
        atTop (nhds (average μ u.toFun)))
  have hconstLp := @w1p_euclideanBall_poincareL1_inner_faithful_hconstLp_5 x₀ r s u hεpos
    havgDiffTendsto
  have hcenterErrLp := @w1p_euclideanBall_poincareL1_inner_faithful_hcenterErrLp_6 x₀ r s u hεpos
    hErrMem hvalLpD hconstLp
  have hcenterMem (n : ℕ) : MemLp
      (fun x => mollify (B.indicator u.toFun) (ε n) (hεpos n) x -
        average μ (mollify (B.indicator u.toFun) (ε n) (hεpos n))) 1 μ :=
    (hvD n).sub (memLp_const _)
  have hcenterMem0 : MemLp (fun x => u.toFun x - average μ u.toFun) 1 μ :=
    huD.sub (memLp_const _)
  have hcenterLp := @w1p_euclideanBall_poincareL1_inner_faithful_hcenterLp_7 x₀ r s u hεpos
    hcenterErrLp hcenterMem hcenterMem0
  have hleftLimit := @w1p_euclideanBall_poincareL1_inner_faithful_hleftLimit_8 x₀ r s u hεpos
    hcenterMem hcenterMem0 hcenterLp
  have hgradExtConv (i : Fin 3) := @w1p_euclideanBall_poincareL1_inner_faithful_hgradExtConv_9 x₀
    r s u hDmeas hDsubB hεpos hgradD i
  have hgradLp (i : Fin 3) : Tendsto
      (fun n => lpNorm (fun x => mollify
        (B.indicator (fun y => u.grad y i)) (ε n) (hεpos n) x - u.grad x i) 1 μ)
      atTop (nhds 0) := tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero (hgradExtConv i)
  let H : Fin 3 → ℕ → Vec3 → ℝ := fun i n x =>
    |mollify (B.indicator (fun y => u.grad y i)) (ε n) (hεpos n) x| -
      |u.grad x i|
  have hgradMollifyCont (n : ℕ) (i : Fin 3) : Continuous
      (fun x => mollify (B.indicator (fun y => u.grad y i))
        (ε n) (hεpos n) x) :=
    mollify_continuous (hεpos n) (hgradLoc i)
  have hgradMollifyMem (n : ℕ) (i : Fin 3) : MemLp
      (fun x => mollify (B.indicator (fun y => u.grad y i))
        (ε n) (hεpos n) x) 1 μ :=
    memLp_euclideanBall_of_continuous hs (hgradMollifyCont n i) 1
  have hgradDMem (i : Fin 3) : MemLp (fun x => u.grad x i) 1 μ :=
    hgradB i |>.mono_measure (Measure.restrict_mono_set volume hDsubB)
  have hHMem (n : ℕ) (i : Fin 3) : MemLp (H i n) 1 μ := by
    exact (hgradMollifyMem n i).abs.sub (hgradDMem i).abs
  have hHConv (i : Fin 3) := @w1p_euclideanBall_poincareL1_inner_faithful_hHConv_10 x₀ r s u hεpos
    hgradLp hgradMollifyMem hgradDMem i
  have hsumH : Tendsto
      (fun n => ∑ i : Fin 3, lpNorm (H i n) 1 μ) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hHConv i)
  have hAGConv := @w1p_euclideanBall_poincareL1_inner_faithful_hAGConv_11 x₀ r s u hεpos hHMem hsumH
  have hAMem (n : ℕ) : MemLp (A n) 1 μ := by
    change MemLp (fun x => ∑ i : Fin 3,
      |mollify (B.indicator (fun y => u.grad y i)) (ε n) (hεpos n) x|) 1 μ
    exact memLp_finsetSum (p := (1 : ℝ≥0∞)) (μ := μ) Finset.univ
      (fun i _ => (hgradMollifyMem n i).abs)
  have hGMem : MemLp G 1 μ := by
    change MemLp (fun x => ∑ i : Fin 3, |u.grad x i|) 1 μ
    exact memLp_finsetSum (p := (1 : ℝ≥0∞)) (μ := μ) Finset.univ
      (fun i _ => (hgradDMem i).abs)
  have hAErrMem (n : ℕ) : MemLp (fun x => A n x - G x) 1 μ :=
    (hAMem n).sub hGMem
  have hAErrInt := @w1p_euclideanBall_poincareL1_inner_faithful_hAErrInt_7 x₀ r s u hεpos hAGConv
    hAErrMem
  have hAGSigned := @w1p_euclideanBall_poincareL1_inner_faithful_hAGSigned_8 x₀ r s u hεpos hAErrInt
  have hAIntTendsto := @w1p_euclideanBall_poincareL1_inner_faithful_hAIntTendsto_12 x₀ r s u hεpos
    hAMem hGMem hAGSigned
  have hderivNorm (n : ℕ) {x : Vec3} (hx : x ∈ D) :=
    @w1p_euclideanBall_poincareL1_inner_faithful_hderivNorm_9 x₀ r s u hεpos hderiv n x hx
  have hderivInt (n : ℕ) :
      ∫ x in D, ‖fderiv ℝ (mollify (B.indicator u.toFun)
        (ε n) (hεpos n)) x‖ ∂volume = ∫ x in D, A n x ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) hDmeas] with x hx
    exact hderivNorm n hx
  have happroxIneq (n : ℕ) := @w1p_euclideanBall_poincareL1_inner_faithful_happroxIneq_13 x₀ r s
    hs u hεpos hvCont hderivInt n
  have hrightLimit := hAIntTendsto.const_mul
    (poincareSobolevL1Constant.toReal * (volume D).toReal ^ (1 / 3 : ℝ))
  have hfinal := le_of_tendsto_of_tendsto hleftLimit hrightLimit
    (Eventually.of_forall happroxIneq)
  simpa [mul_assoc] using hfinal

private theorem vec3EuclideanNorm_le_sum_absFaithful (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i : Fin 3, |v i| := by
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin 3))) (f := fun i => |v i|)
    (fun _ _ => abs_nonneg _)
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (∑ i : Fin 3, |v i|) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]
    simpa [sq_abs] using hsum
  exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg v)
    (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp hsq

/-- The coordinatewise gradient sum is controlled by the Euclidean norm in dimension three. -/
theorem sum_abs_le_sqrt_three_vec3EuclideanNormFaithful (v : Vec3) :
    (∑ i : Fin 3, |v i|) ≤ Real.sqrt 3 * vec3EuclideanNorm v := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
    (fun _ : Fin 3 => (1 : ℝ)) (fun i : Fin 3 => |v i|)
  calc
    ∑ i : Fin 3, |v i| = ∑ i : Fin 3, (1 : ℝ) * |v i| := by simp
    _ ≤ Real.sqrt (∑ i : Fin 3, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ i : Fin 3, |v i| ^ 2) := hcs
    _ = Real.sqrt 3 * vec3EuclideanNorm v := by
      rw [show (∑ i : Fin 3, (1 : ℝ) ^ 2) = 3 by norm_num]
      congr 2
      exact Finset.sum_congr rfl (fun i _ => sq_abs _)


end
end CKN
