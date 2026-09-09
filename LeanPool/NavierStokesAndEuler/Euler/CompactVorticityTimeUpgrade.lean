/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerClassicalClass
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryCauchyInterpolation
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
public import LeanPool.NavierStokesAndEuler.Euler.WeakHilbertODE
public import LeanPool.NavierStokesAndEuler.Euler.WeakTimeContinuity
public import LeanPool.NavierStokesAndEuler.Euler.DevelopmentBridge

@[expose] public section

/-!
# Time regularity from the projected weak equation

Uniform bounds for the genuine spatial Sobolev norms upgrade strong `L²`
continuity to continuity of every spatial jet. This is the interpolation
step in the Comparator bridge. In particular, its higher Sobolev
continuity conclusion is not assumed in any of its hypotheses.
-/

noncomputable section


namespace Euler.ComparatorBridge

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
  EulerSmoothSobolev Finset
open scoped ContDiff Topology NNReal

/-- A recovered smooth-`L²` representative inherits the Comparator's weak
time continuity. No continuity of its higher derivatives is used here. -/
theorem comparator_weak_pairings_continuous
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ}
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ t, (A t).field = (v · (t : ℝ))) (φ : L2) :
    Continuous (fun t => inner ℝ φ (A t).toLp) := by
  let ι : Icc (0 : ℝ) T → Ici (0 : ℝ) := fun t => ⟨t, t.property.1⟩
  have hi : Continuous ι := continuous_subtype_val.subtype_mk _
  have he (t : Icc (0 : ℝ) T) : (A t).toLp = h.velocityLp (ι t) := by
    apply Lp.ext
    filter_upwards [(A t).toLp_ae,
      (h.velocity_memLp (t : ℝ) t.property.1).coeFn_toLp] with x hx hy
    exact hx.trans ((congrFun (hA t) x).trans hy.symm)
  simpa only [Function.comp_def, ← he] using (h.velocityLp_weakly_continuous φ).comp hi

/-- The Comparator's classical divergence constraint gives the genuine
Hilbert-space solenoidal constraint on every recovered velocity slice. -/
theorem comparator_velocity_mem_solenoidal
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ}
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ t, (A t).field = (v · (t : ℝ))) (t : Icc (0 : ℝ) T) :
    (A t).toLp ∈ solenoidalSpace := by
  apply smooth_mem_solenoidal (A t).field (A t).smooth (A t).memLp
  intro x
  rw [hA t]
  exact h.div_free x t t.property.1

/-- The actual tensor Sobolev norm of a difference is controlled by the
sum of the two actual norms. -/
theorem tensorNorm_fieldSub_le (A B : SmoothL2Field Space) (q : ℕ) :
    tensorNorm q (fieldSub A B) ≤ tensorNorm q A + tensorNorm q B := by
  simp only [tensorNorm, jetLp_fieldSub, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun n _ => norm_sub_le _ _)

/-- A fixed jet is bounded by the finite tensor norm containing it. -/
theorem jetLp_norm_le_tensorNorm (A : SmoothL2Field Space) (q : ℕ) :
    ‖A.jetLp q‖ ≤ tensorNorm q A := by
  exact Finset.single_le_sum (fun n _ => norm_nonneg (A.jetLp n))
    (Finset.mem_range.mpr (Nat.lt_succ_self q))

/-- Per-order jet bounds give the finite tensor bounds used below. -/
theorem tensorNorm_uniform_of_jetLp_uniform
    {K : Type*} (A : K → SmoothL2Field Space)
    (hb : ∀ n : ℕ, ∃ M : ℝ, ∀ t, ‖(A t).jetLp n‖ ≤ M) :
    ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M := by
  classical
  intro q
  refine ⟨∑ n ∈ Finset.range (q + 1), (hb n).choose, ?_⟩
  intro t
  exact Finset.sum_le_sum (fun n _ => (hb n).choose_spec t)

/-- Strong `L²` continuity plus uniform higher spatial Sobolev bounds
implies continuity of every actual spatial `L²` jet. -/
theorem jetLp_continuous_of_toLp_continuous
    {K : Type*} [TopologicalSpace K] (A : K → SmoothL2Field Space)
    (h0 : Continuous (fun t => (A t).toLp))
    (hb : ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M) :
    ∀ q : ℕ, Continuous (fun t => (A t).jetLp q) := by
  intro q
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨M, hM⟩ := hb (2 * q)
  have hbound (t : K) : WordBound (2 * q) (M + M) (fieldSub (A t) (A s)) := by
    intro n hn w
    apply (wordBound_tensorNorm (2 * q) (fieldSub (A t) (A s)) n hn w).trans
    exact (tensorNorm_fieldSub_le (A t) (A s) (2 * q)).trans
      (add_le_add (hM t) (hM s))
  have hi (t : K) : ‖(A t).jetLp q - (A s).jetLp q‖ ≤
      wordCount q * Real.sqrt (‖(A t).toLp - (A s).toLp‖ * (M + M)) := by
    rw [← jetLp_fieldSub]
    exact (jetLp_norm_le_tensorNorm (fieldSub (A t) (A s)) q).trans
      (by simpa only [toLp_fieldSub] using
        tensorNorm_interpolate_zero (fieldSub (A t) (A s)) q (M + M) (hbound t))
  have ht : Tendsto (fun t => ‖(A t).toLp - (A s).toLp‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h0.continuousAt
  apply squeeze_zero (fun _ => norm_nonneg _) hi
  simpa only [zero_mul, Real.sqrt_zero, mul_zero] using
    ((ht.mul_const (M + M)).sqrt.const_mul (wordCount q))

/-- A bounded spatial `H²` norm bounds the projected Euler right-hand
side in `L²`. This estimate does not use time regularity. -/
theorem projectedRhs_norm_le_of_tensorNorm_le
    (A : SmoothL2Field Space) (M : ℝ) (hM : tensorNorm 2 A ≤ M) :
    ‖(projectedRhs A).toLp‖ ≤ 39 * smoothEmbeddingConstant * M ^ 2 := by
  have hM0 : 0 ≤ M := (tensorNorm_nonneg 2 A).trans hM
  have hw : WordBound 2 M A := fun n hn w =>
    (wordBound_tensorNorm 2 A n hn w).trans hM
  rw [projectedRhs_toLp, norm_neg]
  apply (solenoidalProjection_apply_norm_le _).trans
  apply (advection_norm_velocity A A ((13 * smoothEmbeddingConstant) * M)
    (wordBound_pointwise hw)).trans
  have hc : 0 ≤ (13 * smoothEmbeddingConstant) * M :=
    mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM0
  exact (mul_le_mul_of_nonneg_left
    (wordBound_derivative hw (by norm_num : 1 ≤ 2)) hc).trans_eq (by ring)

/-- Uniform spatial bounds supply a uniform bound for the projected
right-hand side even before strong time continuity has been established. -/
theorem projectedRhs_uniform_bound
    {K : Type*} (A : K → SmoothL2Field Space)
    (hb : ∃ M : ℝ, ∀ t, tensorNorm 2 (A t) ≤ M) :
    ∃ C : ℝ≥0, ∀ t, ‖(projectedRhs (A t)).toLp‖ ≤ C := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨⟨39 * smoothEmbeddingConstant * M ^ 2, ?_⟩, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg)
      (sq_nonneg M)
  · intro t
    exact projectedRhs_norm_le_of_tensorNorm_le (A t) M (hM t)

/-- A projected Euler equation tested against a dense family is enough to
recover the development's full scalar-pressure class. The hypotheses require
only weak time continuity and uniform spatial bounds; both strong `L²` time
regularity and continuity of every higher spatial Sobolev norm are proved. -/
theorem isSmoothScalarEuler_of_weak_projectedEquation
    {T : ℝ} (hT : 0 < T) (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hs : ∀ t, (A t).toLp ∈ solenoidalSpace)
    (hb : ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M)
    (D : Set solenoidalSpace) (hD : Dense D)
    (hc : ∀ φ ∈ D, Continuous (fun t => inner ℝ (φ : L2) (A t).toLp))
    (hd : ∀ φ ∈ D, ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => inner ℝ (φ : L2) (A (projIcc 0 T hT.le r)).toLp)
        (inner ℝ (φ : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t) :
    IsSmoothScalarEuler (hT := hT.le) A := by
  let u : ℝ → solenoidalSpace := fun r =>
    ⟨(A (projIcc 0 T hT.le r)).toLp, hs _⟩
  have hbs (t : Icc (0 : ℝ) T) :
      (projectedRhs (A t)).toLp ∈ solenoidalSpace := by
    rw [projectedRhs_toLp]
    exact solenoidalSpace.neg_mem (solenoidalProjection_mem _)
  let b : ℝ → solenoidalSpace := fun r =>
    ⟨(projectedRhs (A (projIcc 0 T hT.le r))).toLp, hbs _⟩
  have huc : ∀ φ ∈ D, ContinuousOn (fun r => inner ℝ φ (u r)) (Icc 0 T) := by
    intro φ hφ
    exact ((hc φ hφ).comp continuous_projIcc).continuousOn
  have hud : ∀ φ ∈ D, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun r => inner ℝ φ (u r)) (inner ℝ φ (b t)) t := by
    intro φ hφ t ht
    change HasDerivAt
      (fun r => inner ℝ (φ : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (φ : L2) (projectedRhs (A (projIcc 0 T hT.le t))).toLp) t
    rw [projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩]
    exact hd φ hφ t ht
  obtain ⟨C, hC⟩ := projectedRhs_uniform_bound A (hb 2)
  have hl : LipschitzOnWith C u (Icc 0 T) :=
    WeakHilbertODE.lipschitzOnWith_of_dense_weak_equation hD hT C huc hud
      (fun t _ => hC (projIcc 0 T hT.le t))
  have hu : Continuous (fun t : Icc (0 : ℝ) T => u t) :=
    continuousOn_iff_continuous_domRestrict.mp hl.continuousOn
  have h0 : Continuous (fun t => (A t).toLp) := by
    apply (continuous_subtype_val.comp hu).congr
    intro t
    change (A (projIcc 0 T hT.le (t : ℝ))).toLp = (A t).toLp
    rw [projIcc_of_mem hT.le t.property]
  have hA := jetLp_continuous_of_toLp_continuous A h0 hb
  have hbc : Continuous b := by
    apply Continuous.subtype_mk
    exact (continuous_toLp (fun t => projectedRhs (A t))
      (projectedRhs_continuous A hA 0)).comp continuous_projIcc
  apply (scalarEuler_iff_projected A).mpr
  refine ⟨hA, hs, ?_⟩
  intro t ht
  have hdu := WeakHilbertODE.hasDerivAt_of_dense_weak_equation
    hD huc hbc.continuousOn hud ht
  have h := solenoidalSpace.subtypeL.hasFDerivAt.comp_hasDerivAt t hdu
  change HasDerivAt (fun r => (A (projIcc 0 T hT.le r)).toLp)
    (projectedRhs (A (projIcc 0 T hT.le t))).toLp t at h
  rw [projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩] at h
  exact h

end Euler.ComparatorBridge
