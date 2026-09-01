/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Analytic maps into a weighted coefficient space

An ambient formal multilinear series with positive radius determines, after
choosing a smaller distinguished-variable radius `r`, an analytic map from the
base variables into `ℓ¹(ℕ, ℂ)`.  Its `k`-th coordinate is
`r ^ k * lastTaylorCoefficient p k z`.

The proof is entirely Archimedean.  It uses Mathlib's explicit
`changeOriginSeries_summable_aux₁` binomial majorant, absolute summability, and
the ordinary triangle inequality.  In particular, it does not use the
ultrametric multiplication estimates for restricted or Gauss-norm power
series.
-/


open scoped NNReal ENNReal Topology

namespace ClassicalComplexWPT

/-- The Banach space of absolutely summable complex sequences. -/
noncomputable abbrev WeightedSeq := lp (fun _ : ℕ ↦ ℂ) 1

/-- Include the base variables into the ambient space at last coordinate zero. -/
noncomputable def baseInclusion (n : ℕ) : Base n →L[ℂ] Ambient n :=
  ContinuousLinearMap.inl ℂ (Base n) ℂ

/-- Evaluate a multilinear form on copies of the last coordinate direction. -/
noncomputable def evalLast (n k : ℕ) :
    ((Ambient n)[×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ Ambient n) ℂ
    (fun _ ↦ lastDirection n)

@[simp] theorem norm_lastDirection (n : ℕ) : ‖lastDirection n‖ = 1 := by
  simp [lastDirection]

@[simp] theorem baseInclusion_apply (n : ℕ) (z : Base n) :
    baseInclusion n z = (z, 0) := rfl

theorem norm_baseInclusion_le (n : ℕ) : ‖baseInclusion n‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (baseInclusion n) (by norm_num) (fun z ↦ by
    simp [baseInclusion])

theorem norm_evalLast_le (n k : ℕ) : ‖evalLast n k‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (evalLast n k) (by norm_num) (fun q ↦ by
    simpa [evalLast, norm_lastDirection] using
      q.le_opNorm (fun _ ↦ lastDirection n))

/-- The base-variable series for the `k`th last-coordinate coefficient. -/
noncomputable def lastCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) ℂ :=
  (evalLast n k).compFormalMultilinearSeries
    ((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n))

/-- Place a scalar in sequence coordinate `k`, weighted by `r ^ k`. -/
noncomputable def weightedSingleCLM (r : ℝ≥0) (k : ℕ) :
    ℂ →L[ℂ] WeightedSeq :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 k).comp
    ((r : ℂ) ^ k • ContinuousLinearMap.id ℂ ℂ)

@[simp] theorem weightedSingleCLM_apply (r : ℝ≥0) (k : ℕ) (z : ℂ) :
    weightedSingleCLM r k z = lp.single 1 k ((r : ℂ) ^ k * z) := by
  rfl

theorem norm_weightedSingleCLM_le (r : ℝ≥0) (k : ℕ) :
    ‖weightedSingleCLM r k‖ ≤ (r : ℝ) ^ k := by
  exact ContinuousLinearMap.opNorm_le_bound (weightedSingleCLM r k)
    (pow_nonneg r.coe_nonneg k) (fun z ↦ by
      rw [weightedSingleCLM_apply, lp.norm_single (by norm_num), norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg])

/-- The weighted sequence-valued series supported in coordinate `k`. -/
noncomputable def weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  (weightedSingleCLM r k).compFormalMultilinearSeries (lastCoefficientSeries p k)

/-- Assemble all weighted last-coordinate coefficient series. -/
noncomputable def weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  fun l ↦ ∑' k : ℕ, weightedCoordinateSeries p r k l

theorem norm_lastCoefficientSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k l : ℕ) :
    ‖lastCoefficientSeries p k l‖ ≤ ‖p.changeOriginSeries k l‖ := by
  unfold lastCoefficientSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  have hpre :
      ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ ≤
        ‖p.changeOriginSeries k l‖ := by
    calc
      _ ≤ ‖p.changeOriginSeries k l‖ * ‖baseInclusion n‖ ^ l :=
        (p.changeOriginSeries k).norm_compContinuousLinearMap_le (baseInclusion n) l
      _ ≤ ‖p.changeOriginSeries k l‖ * 1 ^ l := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg (baseInclusion n)) (norm_baseInclusion_le n) l)
          (norm_nonneg (p.changeOriginSeries k l))
      _ = ‖p.changeOriginSeries k l‖ := by simp
  calc
    ‖(evalLast n k).compContinuousMultilinearMap
        (((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l)‖ ≤
        ‖evalLast n k‖ *
          ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖p.changeOriginSeries k l‖ :=
      mul_le_mul (norm_evalLast_le n k) hpre
        (norm_nonneg (((p.changeOriginSeries k).compContinuousLinearMap
          (baseInclusion n)) l)) (by norm_num)
    _ = ‖p.changeOriginSeries k l‖ := one_mul _

theorem norm_weightedCoordinateSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖ ≤
      (r : ℝ) ^ k * ‖p.changeOriginSeries k l‖ := by
  unfold weightedCoordinateSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  calc
    ‖(weightedSingleCLM r k).compContinuousMultilinearMap
        (lastCoefficientSeries p k l)‖ ≤
        ‖weightedSingleCLM r k‖ * ‖lastCoefficientSeries p k l‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ (r : ℝ) ^ k * ‖p.changeOriginSeries k l‖ :=
      mul_le_mul (norm_weightedSingleCLM_le r k) (norm_lastCoefficientSeries_le p k l)
        (norm_nonneg _) (pow_nonneg r.coe_nonneg k)

theorem nnnorm_weightedCoordinateSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖₊ ≤
      ‖p.changeOriginSeries k l‖₊ * r ^ k := by
  apply NNReal.coe_le_coe.mp
  push_cast
  simpa [mul_comm] using norm_weightedCoordinateSeries_le p r k l

@[simp] theorem weightedCoordinateSeries_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ)
    (v : Fin l → Base n) :
    weightedCoordinateSeries p r k l v =
      lp.single 1 k ((r : ℂ) ^ k *
        (p.changeOriginSeries k l) (fun i ↦ baseInclusion n (v i))
          (fun _ ↦ lastDirection n)) := by
  rfl

theorem radius_weightedLastCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (h : (‖x‖₊ + r : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) < (p.changeOrigin x).radius := by
  refine lt_of_lt_of_le ?_ p.changeOrigin_radius
  rwa [lt_tsub_iff_right, add_comm]

/-- The ordinary (Archimedean) majorant needed to sum the weighted coordinate
series.  This is extracted from Mathlib's `changeOriginSeries_summable_aux₁`;
no ultrametric inequality is used. -/
theorem summable_nnnorm_changeOriginSeries_mul_pow {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖p.changeOriginSeries k l‖₊ * r ^ k) := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨s, hs, hrs⟩
  have hsr : (s + r : ℝ≥0∞) < p.radius := by simpa [add_comm] using hrs
  let I := Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l}
  let J := Σ k m : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let e : I → J := fun q ↦ ⟨q.1, l, q.2⟩
  have he : Function.Injective e := by
    rintro ⟨k, t⟩ ⟨k', t'⟩ h
    dsimp only [e] at h
    cases h
    rfl
  have hbig : Summable (fun q : J ↦
      ‖p (q.1 + q.2.1)‖₊ * s ^ q.2.1 * r ^ q.1) :=
    p.changeOriginSeries_summable_aux₁ hsr
  have hfixedS : Summable (fun q : I ↦
      ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1) := by
    simpa [Function.comp_def, e] using NNReal.summable_comp_injective hbig he
  have hspow : s ^ l ≠ 0 := pow_ne_zero l hs.ne'
  have hfixed : Summable (fun q : I ↦ ‖p (q.1 + l)‖₊ * r ^ q.1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, hspow] using
      hfixedS.mul_right (s ^ l)⁻¹
  have houter : Summable (fun k : ℕ ↦
      ∑' t : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * r ^ k) :=
    (NNReal.summable_sigma.1 hfixed).2
  refine NNReal.summable_of_le (fun k ↦ ?_) houter
  calc
    ‖p.changeOriginSeries k l‖₊ * r ^ k ≤
        (∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) * r ^ k := by
      gcongr
      exact p.nnnorm_changeOriginSeries_le_tsum k l
    _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * r ^ k := by rw [NNReal.tsum_mul_right]

theorem summable_weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ weightedCoordinateSeries p r k l) := by
  refine Summable.of_nnnorm_bounded
    (summable_nnnorm_changeOriginSeries_mul_pow p r hr l) (fun k ↦ ?_)
  exact nnnorm_weightedCoordinateSeries_le p r k l

theorem summable_nnnorm_weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖weightedCoordinateSeries p r k l‖₊) := by
  refine NNReal.summable_of_le (fun k ↦ ?_)
    (summable_nnnorm_changeOriginSeries_mul_pow p r hr l)
  exact nnnorm_weightedCoordinateSeries_le p r k l

theorem nnnorm_weightedCoefficientSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    ‖weightedCoefficientSeries p r l‖₊ ≤
      ∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k := by
  unfold weightedCoefficientSeries
  calc
    ‖∑' k : ℕ, weightedCoordinateSeries p r k l‖₊ ≤
        ∑' k : ℕ, ‖weightedCoordinateSeries p r k l‖₊ :=
      nnnorm_tsum_le (summable_nnnorm_weightedCoordinateSeries p r hr l)
    _ ≤ ∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k := by
      apply Summable.tsum_le_tsum
      · intro k
        exact nnnorm_weightedCoordinateSeries_le p r k l
      · exact summable_nnnorm_weightedCoordinateSeries p r hr l
      · exact summable_nnnorm_changeOriginSeries_mul_pow p r hr l

theorem weightedCoefficientSeries_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) (v : Fin l → Base n) (j : ℕ) :
    weightedCoefficientSeries p r l v j =
      (r : ℂ) ^ j * (p.changeOriginSeries j l)
        (fun i ↦ baseInclusion n (v i)) (fun _ ↦ lastDirection n) := by
  let ev : ((Base n)[×l]→L[ℂ] WeightedSeq) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 j).comp
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l ↦ Base n) WeightedSeq v)
  have hsum := (summable_weightedCoordinateSeries p r hr l).hasSum.mapL ev
  change ev (∑' k : ℕ, weightedCoordinateSeries p r k l) = _
  rw [← hsum.tsum_eq]
  change (∑' k : ℕ, (lp.single 1 k ((r : ℂ) ^ k *
    (p.changeOriginSeries k l) (fun i ↦ baseInclusion n (v i))
      (fun _ ↦ lastDirection n)) : WeightedSeq) j) = _
  rw [tsum_eq_single j]
  · exact Pi.single_eq_same _ _
  · intro k hkj
    exact Pi.single_eq_of_ne' hkj _

theorem summable_changeOrigin_weighted_majorant {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    Summable (fun l : ℕ ↦
      (∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l) := by
  let J := Σ k m : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let K := Σ m k : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let e : K → J := fun q ↦ ⟨q.2.1, q.1, q.2.2⟩
  have he : Function.Injective e := by
    rintro ⟨m, k, t⟩ ⟨m', k', t'⟩ h
    dsimp only [e] at h
    cases h
    rfl
  have hbig : Summable (fun q : J ↦
      ‖p (q.1 + q.2.1)‖₊ * s ^ q.2.1 * r ^ q.1) :=
    p.changeOriginSeries_summable_aux₁ hsr
  have hswap : Summable (fun q : K ↦
      ‖p (q.2.1 + q.1)‖₊ * s ^ q.1 * r ^ q.2.1) := by
    simpa [Function.comp_def, e] using NNReal.summable_comp_injective hbig he
  have hr : (r : ℝ≥0∞) < p.radius := by
    exact (show (r : ℝ≥0∞) ≤ s + r by simp).trans_lt hsr
  have hK := NNReal.summable_sigma.1 hswap
  refine NNReal.summable_of_le (fun l ↦ ?_) hK.2
  have hKl := NNReal.summable_sigma.1 (hK.1 l)
  have hleft : Summable (fun k : ℕ ↦
      (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l) :=
    (summable_nnnorm_changeOriginSeries_mul_pow p r hr l).mul_right (s ^ l)
  calc
    (∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l =
        ∑' k : ℕ, (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l := by
      rw [NNReal.tsum_mul_right]
    _ ≤ ∑' k : ℕ, ∑' t : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * s ^ l * r ^ k := by
      apply Summable.tsum_le_tsum
      · intro k
        calc
          (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l ≤
              ((∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) *
                r ^ k) * s ^ l := by
            gcongr
            exact p.nnnorm_changeOriginSeries_le_tsum k l
          _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
              ‖p (k + l)‖₊ * s ^ l * r ^ k := by
            calc
              ((∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) *
                  r ^ k) * s ^ l =
                  (∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    ‖p (k + l)‖₊ * r ^ k) * s ^ l := by
                exact congrArg (fun x ↦ x * s ^ l)
                  (NNReal.tsum_mul_right
                    (fun _ : {t : Finset (Fin (k + l)) // t.card = l} ↦ ‖p (k + l)‖₊)
                    (r ^ k)).symm
              _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    (‖p (k + l)‖₊ * r ^ k) * s ^ l := by
                exact (NNReal.tsum_mul_right
                  (fun _ : {t : Finset (Fin (k + l)) // t.card = l} ↦
                    ‖p (k + l)‖₊ * r ^ k) (s ^ l)).symm
              _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    ‖p (k + l)‖₊ * s ^ l * r ^ k := by
                apply tsum_congr
                intro t
                ac_rfl
      · exact hleft
      · exact hKl.2
    _ = ∑' q : Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1 := by
      exact (Summable.tsum_sigma'
        (f := fun q : Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l} ↦
          ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1) hKl.1 (hK.1 l)).symm

theorem le_radius_weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    (s : ℝ≥0∞) ≤ (weightedCoefficientSeries p r).radius := by
  have hr : (r : ℝ≥0∞) < p.radius :=
    (show (r : ℝ≥0∞) ≤ s + r by simp).trans_lt hsr
  apply FormalMultilinearSeries.le_radius_of_summable_nnnorm
  refine NNReal.summable_of_le (fun l ↦ ?_)
    (summable_changeOrigin_weighted_majorant p s r hsr)
  gcongr
  exact nnnorm_weightedCoefficientSeries_le p r hr l

theorem radius_weightedCoefficientSeries_pos {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    0 < (weightedCoefficientSeries p r).radius := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨s, hs, hrs⟩
  have hsr : (s + r : ℝ≥0∞) < p.radius := by simpa [add_comm] using hrs
  exact (show (0 : ℝ≥0∞) < s by simpa using hs).trans_le
    (le_radius_weightedCoefficientSeries p s r hsr)

theorem analyticAt_weightedCoefficientSeries_sum {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 :=
  ((weightedCoefficientSeries p r).hasFPowerSeriesOnBall
    (radius_weightedCoefficientSeries_pos p r hr)).analyticAt

theorem AnalyticAt.exists_analytic_weightedCoefficientMap {n : ℕ}
    {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0),
      HasFPowerSeriesAt f p 0 ∧ 0 < r ∧
        AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 := by
  obtain ⟨p, hp⟩ := hf
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨r, hr0, hrp⟩
  have hr0' : (0 : ℝ≥0) < r := by exact_mod_cast hr0
  exact ⟨p, r, hp, hr0', analyticAt_weightedCoefficientSeries_sum p r hrp⟩

/-- On the common convergence neighborhood, the `j`-th coordinate of the
`ℓ¹`-valued analytic sum is exactly the weighted moving Taylor coefficient. -/
theorem weightedCoefficientSeries_sum_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : baseInclusion n z ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j *
        p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n) := by
  let coord : WeightedSeq →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 j
  have hqsum := ((weightedCoefficientSeries p r).summable hzq).hasSum.mapL coord
  have hzpj : baseInclusion n z ∈
      Metric.eball (0 : Ambient n) (p.changeOriginSeries j).radius := by
    exact mem_eball_zero_iff.mpr
      ((mem_eball_zero_iff.mp hzp).trans_le (p.le_changeOriginSeries_radius j))
  have hpsum : HasSum
      (fun l : ℕ ↦ (p.changeOriginSeries j l)
        (fun _ ↦ baseInclusion n z) (fun _ ↦ lastDirection n))
      (p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n)) := by
    simpa [FormalMultilinearSeries.changeOrigin, FormalMultilinearSeries.sum, evalLast] using
      ((p.changeOriginSeries j).summable hzpj).hasSum.mapL (evalLast n j)
  change coord ((weightedCoefficientSeries p r).sum z) = _
  calc
    coord ((weightedCoefficientSeries p r).sum z) =
        ∑' l : ℕ, coord (weightedCoefficientSeries p r l (fun _ ↦ z)) :=
      hqsum.tsum_eq.symm
    _ = ∑' l : ℕ, (r : ℂ) ^ j * (p.changeOriginSeries j l)
        (fun _ ↦ baseInclusion n z) (fun _ ↦ lastDirection n) := by
      congr 1
      funext l
      change weightedCoefficientSeries p r l (fun _ ↦ z) j = _
      exact weightedCoefficientSeries_apply p r hr l (fun _ ↦ z) j
    _ = (r : ℂ) ^ j *
        p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n) :=
      (hpsum.mul_left ((r : ℂ) ^ j)).tsum_eq

theorem weightedCoefficientSeries_sum_apply_lastTaylorCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : (z, 0) ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j * lastTaylorCoefficient p j z := by
  simpa [lastTaylorCoefficient] using
    weightedCoefficientSeries_sum_apply p r z j hr hzq hzp

/-- The weighted last-direction Taylor coefficients at an ambient point. -/
noncomputable def weightedLastCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) : WeightedSeq :=
  ⟨fun k ↦ (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n), by
    apply memℓp_gen
    have hs : Summable (fun k : ℕ ↦ ‖p.changeOrigin x k‖ * (r : ℝ) ^ k) :=
      (p.changeOrigin x).summable_norm_mul_pow hr
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        change ‖(r : ℂ) ^ k * ((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
          ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg r.coe_nonneg]
        have hv : ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
            ‖(p.changeOrigin x) k‖ := by
          simpa [norm_lastDirection] using
            ((p.changeOrigin x) k).le_opNorm (fun _ ↦ lastDirection n)
        calc
          (r : ℝ) ^ k * ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
              (r : ℝ) ^ k * ‖(p.changeOrigin x) k‖ :=
            mul_le_mul_of_nonneg_left hv (pow_nonneg r.coe_nonneg k)
          _ = ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k := mul_comm _ _)⟩

@[simp] theorem weightedLastCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) (k : ℕ) :
    weightedLastCoeffs p r x hr k =
      (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n) := rfl

theorem norm_weightedLastCoeffs_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) :
    ‖weightedLastCoeffs p r x hr‖ ≤
      ∑' k : ℕ, ‖p.changeOrigin x k‖ * (r : ℝ) ^ k := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one, weightedLastCoeffs_apply]
  apply Summable.tsum_le_tsum
  · intro k
    change ‖(r : ℂ) ^ k * ((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
      ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg]
    have hv : ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
        ‖(p.changeOrigin x) k‖ := by
      simpa [norm_lastDirection] using
        ((p.changeOrigin x) k).le_opNorm (fun _ ↦ lastDirection n)
    calc
      (r : ℝ) ^ k * ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
          (r : ℝ) ^ k * ‖(p.changeOrigin x) k‖ :=
        mul_le_mul_of_nonneg_left hv (pow_nonneg r.coe_nonneg k)
      _ = ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k := mul_comm _ _
  · simpa only [ENNReal.toReal_one, Real.rpow_one, weightedLastCoeffs_apply] using
      (weightedLastCoeffs p r x hr).2.summable (by norm_num)
  · exact (p.changeOrigin x).summable_norm_mul_pow hr

/-- Explicit `ℓ¹` membership and norm control, uniformly on any smaller base
ball whose radius plus the distinguished weight stays inside `p.radius`. -/
theorem exists_weightedLastCoeffs_on_baseBall {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) {z : Base n}
    (hz : z ∈ Metric.eball (0 : Base n) s) :
    ∃ c : WeightedSeq,
      (∀ k, c k = (r : ℂ) ^ k * lastTaylorCoefficient p k z) ∧
        ‖c‖ ≤ ∑' k : ℕ, ‖p.changeOrigin (z, 0) k‖ * (r : ℝ) ^ k := by
  have hz' : (‖z‖₊ : ℝ≥0∞) < s := mem_eball_zero_iff.mp hz
  have hx : (‖baseInclusion n z‖₊ + r : ℝ≥0∞) < p.radius := by
    calc
      (‖baseInclusion n z‖₊ + r : ℝ≥0∞) = ‖z‖₊ + r := by simp
      _ < s + r := ENNReal.add_lt_add_right (by simp) hz'
      _ < p.radius := hsr
  let hrx := radius_weightedLastCoeffs p r (baseInclusion n z) hx
  refine ⟨weightedLastCoeffs p r (baseInclusion n z) hrx, ?_, ?_⟩
  · intro k
    simp [lastTaylorCoefficient, weightedLastCoeffs_apply]
  · simpa using norm_weightedLastCoeffs_le p r (baseInclusion n z) hrx

end ClassicalComplexWPT
