/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.GlobalSourceSlice
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Extension of finite-cylinder parabolic Hölder data

A source on `(t₀,T] × X` has a unique uniform limit at `t₀` in the
bounded-continuous spatial norm.  We extend to `[t₀,T]`, clamp in time, and
obtain a bounded global `C^{0,α}` source.  The construction is linear, is a
right inverse to restriction, and has operator norm at most three.

This removes the global-source convenience hypothesis from the Euclidean
Duhamel inverse: every genuine finite-cylinder datum has a controlled global
extension.
-/

@[expose] public noncomputable section
open Real Set Filter Metric
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace ParabolicC0AlphaBanach

variable {t₀ T α : ℝ}

/-- Positive times, viewed as a dense subset of the closed time interval. -/
def positiveTimeInIcc (t₀ T : ℝ) : Set (↥(Set.Icc t₀ T)) :=
  {t | t₀ < (t : ℝ)}

/-- The positive part of a nondegenerate closed interval is dense in it. -/
theorem dense_positiveTimeInIcc (hT : t₀ < T) :
    Dense (positiveTimeInIcc t₀ T) := by
  rw [Subtype.dense_iff]
  have himage :
      ((fun t : ↥(Set.Icc t₀ T) => (t : ℝ)) '' positiveTimeInIcc t₀ T) =
        Set.Ioc t₀ T := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.2.2⟩
    · intro ht
      exact ⟨⟨t, ht.1.le, ht.2⟩, ht.1, rfl⟩
  rw [himage, closure_Ioc hT.ne]

theorem positiveTimeInIcc_mem_parabolicFiniteCylinder
    (t : positiveTimeInIcc t₀ T) (x : X) :
    ((t : ℝ), x) ∈ parabolicFiniteCylinder X t₀ T := by
  exact ⟨⟨t.2, t.1.2.2⟩, Set.mem_univ x⟩

/-- A finite-cylinder source at one positive time, as a bounded continuous
spatial function. -/
def finiteTimeSlice (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) : BoundedContinuousFunction X E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => evalCLM ((t : ℝ), x)
      (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) q)
    (by
      let v := outL q
      have hv : ContinuousOn (ParabolicC0AlphaSpace.toFun v)
          (parabolicFiniteCylinder X t₀ T) :=
        (ParabolicC0AlphaSpace.toSubmodule v).2.continuousOn hα
      have hcomp : Continuous (fun x : X =>
          ParabolicC0AlphaSpace.toFun v ((t : ℝ), x)) :=
        hv.comp_continuous (continuous_const.prodMk continuous_id)
          (fun x => positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
      convert hcomp using 1
      funext x
      calc
        evalCLM ((t : ℝ), x)
            (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) q =
          evalCLM ((t : ℝ), x)
            (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) (mk v) := by
              rw [mk_outL]
        _ = ParabolicC0AlphaSpace.toFun v ((t : ℝ), x) :=
          evalCLM_mk_apply _ _ v)
    ‖q‖
    (fun x => by
      calc
        ‖evalCLM ((t : ℝ), x)
            (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) q‖
            ≤ ‖evalCLM ((t : ℝ), x)
                (positiveTimeInIcc_mem_parabolicFiniteCylinder t x)‖ * ‖q‖ :=
          (evalCLM ((t : ℝ), x)
            (positiveTimeInIcc_mem_parabolicFiniteCylinder t x)).le_opNorm q
        _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right
          (norm_evalCLM_le _ _) (norm_nonneg q)
        _ = ‖q‖ := one_mul _)

@[simp]
theorem finiteTimeSlice_apply (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) (x : X) :
    finiteTimeSlice hα q t x =
      evalCLM ((t : ℝ), x)
        (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) q := rfl

theorem norm_finiteTimeSlice_le (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    ‖finiteTimeSlice hα q t‖ ≤ ‖q‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (finiteTimeSlice hα q t).continuous (norm_nonneg q) (fun x => by
      calc
        ‖finiteTimeSlice hα q t x‖ =
            ‖evalCLM ((t : ℝ), x)
              (positiveTimeInIcc_mem_parabolicFiniteCylinder t x) q‖ := rfl
        _ ≤ ‖evalCLM ((t : ℝ), x)
              (positiveTimeInIcc_mem_parabolicFiniteCylinder t x)‖ * ‖q‖ :=
          (evalCLM ((t : ℝ), x)
            (positiveTimeInIcc_mem_parabolicFiniteCylinder t x)).le_opNorm q
        _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right
          (norm_evalCLM_le _ _) (norm_nonneg q)
        _ = ‖q‖ := one_mul _)

theorem dist_finiteTimeSlice_le (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t τ : positiveTimeInIcc t₀ T) :
    dist (finiteTimeSlice hα q t) (finiteTimeSlice hα q τ) ≤
      ‖q‖ * |(t : ℝ) - (τ : ℝ)| ^ (α / 2) := by
  rw [BoundedContinuousFunction.dist_le
    (mul_nonneg (norm_nonneg q) (Real.rpow_nonneg (abs_nonneg _) _))]
  intro x
  simp only [finiteTimeSlice_apply, dist_eq_norm]
  have h := q.norm_eval_sub_eval_le
    (p := ((t : ℝ), x)) (z := ((τ : ℝ), x))
    (positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
    (positiveTimeInIcc_mem_parabolicFiniteCylinder τ x)
  rwa [parabolicDistance.same_space_rpow] at h

@[simp]
theorem finiteTimeSlice_zero (hα : 0 < α)
    (t : positiveTimeInIcc t₀ T) :
    finiteTimeSlice hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) t = 0 := by
  ext x
  simp [finiteTimeSlice_apply]

@[simp]
theorem finiteTimeSlice_add (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    finiteTimeSlice hα (q + r) t =
      finiteTimeSlice hα q t + finiteTimeSlice hα r t := by
  ext x
  simp [finiteTimeSlice_apply]

@[simp]
theorem finiteTimeSlice_smul (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    finiteTimeSlice hα (c • q) t = c • finiteTimeSlice hα q t := by
  ext x
  simp [finiteTimeSlice_apply]

/-- The positive-time path is uniformly continuous, uniformly all the way
down to the missing initial endpoint. -/
theorem uniformContinuous_finiteTimeSlice
    (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    UniformContinuous (finiteTimeSlice hα q) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  by_cases hq0 : ‖q‖ = 0
  · refine ⟨1, zero_lt_one, fun {t τ} _ => ?_⟩
    have h := dist_finiteTimeSlice_le hα q t τ
    rw [hq0, zero_mul] at h
    exact h.trans_lt hε
  · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq0)
    have hpow : ContinuousAt (fun u : ℝ => |u| ^ (α / 2)) 0 := by
      apply ContinuousAt.rpow
      · fun_prop
      · fun_prop
      · right
        positivity
    rw [Metric.continuousAt_iff] at hpow
    obtain ⟨δ, hδ, hδbound⟩ := hpow (ε / ‖q‖) (div_pos hε hqpos)
    refine ⟨δ, hδ, fun {t τ} htτ => ?_⟩
    have hsub : dist ((t : ℝ) - (τ : ℝ)) 0 < δ := by
      simpa [Real.dist_eq, Subtype.dist_eq] using htτ
    have hp := hδbound hsub
    have hz : (0 : ℝ) ^ (α / 2) = 0 := zero_rpow (by positivity)
    simp only [abs_zero, hz] at hp
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hp
    exact (dist_finiteTimeSlice_le hα q t τ).trans_lt
      (by simpa only [mul_comm] using (lt_div_iff₀ hqpos).mp hp)

/-- Continuous extension of the positive-time slices to the missing initial
endpoint. -/
def finiteClosedTimeSlice (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ↥(Set.Icc t₀ T) → BoundedContinuousFunction X E :=
  (dense_positiveTimeInIcc hT).extend (finiteTimeSlice hα q)

/-- The closed-time extension agrees with the original datum at every
positive time. -/
@[simp]
theorem finiteClosedTimeSlice_apply_positive
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    finiteClosedTimeSlice hT hα q t = finiteTimeSlice hα q t :=
  (dense_positiveTimeInIcc hT).extend_of_ind
    (uniformContinuous_finiteTimeSlice hα q) t

/-- The closed-time slice path is uniformly continuous. -/
theorem uniformContinuous_finiteClosedTimeSlice
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    UniformContinuous (finiteClosedTimeSlice hT hα q) :=
  (dense_positiveTimeInIcc hT).uniformContinuous_extend
    (uniformContinuous_finiteTimeSlice hα q)

theorem continuous_finiteClosedTimeSlice
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    Continuous (finiteClosedTimeSlice hT hα q) :=
  (uniformContinuous_finiteClosedTimeSlice hT hα q).continuous

/-- Every closed-time slice has the same sharp sup-norm bound as the original
finite-cylinder datum. -/
theorem norm_finiteClosedTimeSlice_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : ↥(Set.Icc t₀ T)) :
    ‖finiteClosedTimeSlice hT hα q t‖ ≤ ‖q‖ := by
  apply (dense_positiveTimeInIcc hT).induction
    (P := fun t => ‖finiteClosedTimeSlice hT hα q t‖ ≤ ‖q‖)
      (x := t)
  · intro τ hτ
    let τ' : positiveTimeInIcc t₀ T := ⟨τ, hτ⟩
    change ‖finiteClosedTimeSlice hT hα q
      (τ' : ↥(Set.Icc t₀ T))‖ ≤ ‖q‖
    rw [finiteClosedTimeSlice_apply_positive]
    exact norm_finiteTimeSlice_le hα q τ'
  · exact isClosed_le
      ((continuous_norm.comp (continuous_finiteClosedTimeSlice hT hα q)))
      continuous_const

/-- The temporal Hölder estimate survives completion at the initial time. -/
theorem dist_finiteClosedTimeSlice_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t τ : ↥(Set.Icc t₀ T)) :
    dist (finiteClosedTimeSlice hT hα q t)
        (finiteClosedTimeSlice hT hα q τ) ≤
      ‖q‖ * |(t : ℝ) - (τ : ℝ)| ^ (α / 2) := by
  let e : positiveTimeInIcc t₀ T → ↥(Set.Icc t₀ T) := Subtype.val
  have he : DenseRange e := (dense_positiveTimeInIcc hT).denseRange_val
  refine he.induction_on₂
    (p := fun t τ =>
      dist (finiteClosedTimeSlice hT hα q t)
          (finiteClosedTimeSlice hT hα q τ) ≤
        ‖q‖ * |(t : ℝ) - (τ : ℝ)| ^ (α / 2))
      (b₁ := t) (b₂ := τ) ?_ ?_
  · apply isClosed_le
    · exact ((continuous_finiteClosedTimeSlice hT hα q).comp continuous_fst).dist
        ((continuous_finiteClosedTimeSlice hT hα q).comp continuous_snd)
    · exact continuous_const.mul
        ((((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd)).abs).rpow_const
            (fun _ => Or.inr (by positivity)))
  · intro a b
    simpa [e, finiteClosedTimeSlice_apply_positive] using
      dist_finiteTimeSlice_le hα q a b

/-- The spatial Hölder estimate also survives completion in time. -/
theorem norm_finiteClosedTimeSlice_apply_sub_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : ↥(Set.Icc t₀ T)) (x y : X) :
    ‖finiteClosedTimeSlice hT hα q t x -
        finiteClosedTimeSlice hT hα q t y‖ ≤
      ‖q‖ * dist x y ^ α := by
  apply (dense_positiveTimeInIcc hT).induction
    (P := fun t =>
      ‖finiteClosedTimeSlice hT hα q t x -
          finiteClosedTimeSlice hT hα q t y‖ ≤
        ‖q‖ * dist x y ^ α) (x := t)
  · intro τ hτ
    let τ' : positiveTimeInIcc t₀ T := ⟨τ, hτ⟩
    rw [show finiteClosedTimeSlice hT hα q τ = finiteTimeSlice hα q τ' by
      simpa [τ'] using finiteClosedTimeSlice_apply_positive hT hα q τ']
    simp only [finiteTimeSlice_apply]
    have h := q.norm_eval_sub_eval_le
      (p := ((τ' : ℝ), x)) (z := ((τ' : ℝ), y))
      (positiveTimeInIcc_mem_parabolicFiniteCylinder τ' x)
      (positiveTimeInIcc_mem_parabolicFiniteCylinder τ' y)
    rwa [parabolicDistance.same_time] at h
  · apply isClosed_le
    · have hxcont : Continuous (fun t : ↥(Set.Icc t₀ T) =>
          finiteClosedTimeSlice hT hα q t x) :=
        (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp
          (continuous_finiteClosedTimeSlice hT hα q)
      have hycont : Continuous (fun t : ↥(Set.Icc t₀ T) =>
          finiteClosedTimeSlice hT hα q t y) :=
        (BoundedContinuousFunction.evalCLM ℝ y).continuous.comp
          (continuous_finiteClosedTimeSlice hT hα q)
      exact continuous_norm.comp (hxcont.sub hycont)
    · exact continuous_const

@[simp]
theorem finiteClosedTimeSlice_zero
    (hT : t₀ < T) (hα : 0 < α) :
    finiteClosedTimeSlice (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  apply (dense_positiveTimeInIcc hT).denseRange_val.equalizer
    (continuous_finiteClosedTimeSlice hT hα 0) continuous_const
  funext t
  ext x
  change finiteClosedTimeSlice hT hα
    (0 : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) t x = (0 : E)
  rw [finiteClosedTimeSlice_apply_positive]
  simp

@[simp]
theorem finiteClosedTimeSlice_add
    (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteClosedTimeSlice hT hα (q + r) =
      finiteClosedTimeSlice hT hα q + finiteClosedTimeSlice hT hα r := by
  apply (dense_positiveTimeInIcc hT).denseRange_val.equalizer
    (continuous_finiteClosedTimeSlice hT hα (q + r))
    ((continuous_finiteClosedTimeSlice hT hα q).add
      (continuous_finiteClosedTimeSlice hT hα r))
  funext t
  simp [Function.comp_apply, finiteClosedTimeSlice_apply_positive]

@[simp]
theorem finiteClosedTimeSlice_smul
    (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteClosedTimeSlice hT hα (c • q) =
      c • finiteClosedTimeSlice hT hα q := by
  apply (dense_positiveTimeInIcc hT).denseRange_val.equalizer
    (continuous_finiteClosedTimeSlice hT hα (c • q))
    ((continuous_finiteClosedTimeSlice hT hα q).const_smul c)
  funext t
  simp [Function.comp_apply, finiteClosedTimeSlice_apply_positive]

/-- Clamp time to `[t₀,T]` and evaluate the completed slice. -/
def finiteSourceExtensionFun
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) : ℝ × X → E :=
  fun z => finiteClosedTimeSlice hT hα q
    (Set.projIcc t₀ T hT.le z.1) z.2

@[simp]
theorem finiteSourceExtensionFun_zero
    (hT : t₀ < T) (hα : 0 < α) :
    finiteSourceExtensionFun (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  funext z
  simp [finiteSourceExtensionFun]

@[simp]
theorem finiteSourceExtensionFun_add
    (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtensionFun hT hα (q + r) =
      finiteSourceExtensionFun hT hα q +
        finiteSourceExtensionFun hT hα r := by
  funext z
  simp [finiteSourceExtensionFun]

@[simp]
theorem finiteSourceExtensionFun_smul
    (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtensionFun hT hα (c • q) =
      c • finiteSourceExtensionFun hT hα q := by
  funext z
  simp [finiteSourceExtensionFun]

theorem finiteSourceExtensionFun_bound
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicBoundedWith ‖q‖ (finiteSourceExtensionFun hT hα q) Set.univ := by
  intro z _hz
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (finiteClosedTimeSlice hT hα q (Set.projIcc t₀ T hT.le z.1)) z.2).trans
      (norm_finiteClosedTimeSlice_le hT hα q _)

theorem finiteSourceExtensionFun_space
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : ℝ) (x y : X) :
    ‖finiteSourceExtensionFun hT hα q (t, x) -
        finiteSourceExtensionFun hT hα q (t, y)‖ ≤
      ‖q‖ * dist x y ^ α :=
  norm_finiteClosedTimeSlice_apply_sub_le hT hα q
    (Set.projIcc t₀ T hT.le t) x y

theorem finiteSourceExtensionFun_time
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (x : X) (t τ : ℝ) :
    ‖finiteSourceExtensionFun hT hα q (t, x) -
        finiteSourceExtensionFun hT hα q (τ, x)‖ ≤
      ‖q‖ * |t - τ| ^ (α / 2) := by
  let ft := finiteClosedTimeSlice hT hα q
  let pt := Set.projIcc t₀ T hT.le t
  let pτ := Set.projIcc t₀ T hT.le τ
  calc
    ‖ft pt x - ft pτ x‖ ≤ dist (ft pt) (ft pτ) := by
      rw [dist_eq_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm (ft pt - ft pτ) x
    _ ≤ ‖q‖ * |(pt : ℝ) - (pτ : ℝ)| ^ (α / 2) :=
      dist_finiteClosedTimeSlice_le hT hα q pt pτ
    _ ≤ ‖q‖ * |t - τ| ^ (α / 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact Real.rpow_le_rpow (abs_nonneg _)
        (Set.abs_projIcc_sub_projIcc (a := t₀) (b := T)
          (c := t) (d := τ) hT.le) (by positivity)

/-- The clamped extension has global parabolic Hölder constant `2 ‖q‖`. -/
theorem finiteSourceExtensionFun_holder
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicHolderWith (2 * ‖q‖) α
      (finiteSourceExtensionFun hT hα q) Set.univ := by
  convert parabolicHolderWith_of_forall_same_time_same_space
    hα.le (norm_nonneg q) (norm_nonneg q)
    (s := (Set.univ : Set (ℝ × X)))
    (u := finiteSourceExtensionFun hT hα q)
    (fun _ _ _ _ => Set.mem_univ _)
    (fun {_t} {_x _y} _ _ =>
      finiteSourceExtensionFun_space hT hα q _ _ _)
    (fun {_x} {_t _τ} _ _ =>
      finiteSourceExtensionFun_time hT hα q _ _ _) using 1 <;> ring

theorem finiteSourceExtensionFun_c0AlphaWith
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicC0AlphaWith ‖q‖ (2 * ‖q‖) α
      (finiteSourceExtensionFun hT hα q) Set.univ :=
  ⟨finiteSourceExtensionFun_bound hT hα q,
    finiteSourceExtensionFun_holder hT hα q⟩

theorem finiteSourceExtensionFun_c0AlphaOn
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicC0AlphaOn α (finiteSourceExtensionFun hT hα q) Set.univ :=
  ⟨‖q‖, norm_nonneg q, 2 * ‖q‖, mul_nonneg (by norm_num) (norm_nonneg q),
    finiteSourceExtensionFun_c0AlphaWith hT hα q⟩

/-- The clamped global representative before separation quotienting. -/
def finiteSourceExtensionSpace
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicC0AlphaSpace X E α (Set.univ : Set (ℝ × X)) :=
  ParabolicC0AlphaSpace.ofSubmodule
    ⟨finiteSourceExtensionFun hT hα q,
      finiteSourceExtensionFun_c0AlphaOn hT hα q⟩

@[simp]
theorem finiteSourceExtensionSpace_zero
    (hT : t₀ < T) (hα : 0 < α) :
    finiteSourceExtensionSpace (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  apply Subtype.ext
  exact finiteSourceExtensionFun_zero hT hα

@[simp]
theorem finiteSourceExtensionSpace_add
    (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtensionSpace hT hα (q + r) =
      finiteSourceExtensionSpace hT hα q +
        finiteSourceExtensionSpace hT hα r := by
  apply Subtype.ext
  exact finiteSourceExtensionFun_add hT hα q r

@[simp]
theorem finiteSourceExtensionSpace_smul
    (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtensionSpace hT hα (c • q) =
      c • finiteSourceExtensionSpace hT hα q := by
  apply Subtype.ext
  exact finiteSourceExtensionFun_smul hT hα c q

/-- The clamped global representative, separation quotienting functions that
agree on the global domain. -/
def finiteSourceExtension
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  mk (finiteSourceExtensionSpace hT hα q)

@[simp]
theorem finiteSourceExtension_zero
    (hT : t₀ < T) (hα : 0 < α) :
    finiteSourceExtension (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  calc
    mk (finiteSourceExtensionSpace hT hα 0) = mk 0 := by
      rw [finiteSourceExtensionSpace_zero]
    _ = 0 := by
      simpa only [mkL_apply] using
        map_zero (mkL : ParabolicC0AlphaSpace X E α Set.univ →L[ℝ] _)

@[simp]
theorem finiteSourceExtension_add
    (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtension hT hα (q + r) =
      finiteSourceExtension hT hα q + finiteSourceExtension hT hα r := by
  change mk (finiteSourceExtensionSpace hT hα (q + r)) =
    mk (finiteSourceExtensionSpace hT hα q) +
      mk (finiteSourceExtensionSpace hT hα r)
  calc
    mk (finiteSourceExtensionSpace hT hα (q + r)) =
        mk (finiteSourceExtensionSpace hT hα q +
          finiteSourceExtensionSpace hT hα r) := by
      rw [finiteSourceExtensionSpace_add]
    _ = _ := by
      simpa only [mkL_apply] using
        map_add (mkL : ParabolicC0AlphaSpace X E α Set.univ →L[ℝ] _)
          (finiteSourceExtensionSpace hT hα q)
          (finiteSourceExtensionSpace hT hα r)

@[simp]
theorem finiteSourceExtension_smul
    (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtension hT hα (c • q) =
      c • finiteSourceExtension hT hα q := by
  change mk (finiteSourceExtensionSpace hT hα (c • q)) =
    c • mk (finiteSourceExtensionSpace hT hα q)
  calc
    mk (finiteSourceExtensionSpace hT hα (c • q)) =
        mk (c • finiteSourceExtensionSpace hT hα q) := by
      rw [finiteSourceExtensionSpace_smul]
    _ = _ := by
      simpa only [mkL_apply] using
        map_smul (mkL : ParabolicC0AlphaSpace X E α Set.univ →L[ℝ] _) c
          (finiteSourceExtensionSpace hT hα q)

@[simp]
theorem eval_finiteSourceExtension
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) (z : ℝ × X) :
    evalCLM z (Set.mem_univ z) (finiteSourceExtension hT hα q) =
      finiteSourceExtensionFun hT hα q z :=
  rfl

/-- The extension costs at most a factor three in the global `C^{0,α}` norm. -/
theorem norm_finiteSourceExtension_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ‖finiteSourceExtension hT hα q‖ ≤ 3 * ‖q‖ := by
  rw [finiteSourceExtension, norm_mk]
  change parabolicC0AlphaNorm α
    (finiteSourceExtensionFun hT hα q) Set.univ ≤ 3 * ‖q‖
  calc
    parabolicC0AlphaNorm α (finiteSourceExtensionFun hT hα q) Set.univ
        ≤ ‖q‖ + 2 * ‖q‖ :=
      parabolicC0AlphaNorm_le (norm_nonneg q)
        (mul_nonneg (by norm_num) (norm_nonneg q))
        (finiteSourceExtensionFun_c0AlphaWith hT hα q)
    _ = 3 * ‖q‖ := by ring

/-- The finite-to-global extension as a bounded linear operator. -/
def finiteSourceExtensionL
    (hT : t₀ < T) (hα : 0 < α) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  LinearMap.mkContinuous
    { toFun := finiteSourceExtension hT hα
      map_add' := finiteSourceExtension_add hT hα
      map_smul' := finiteSourceExtension_smul hT hα }
    3 (norm_finiteSourceExtension_le hT hα)

@[simp]
theorem finiteSourceExtensionL_apply
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteSourceExtensionL hT hα q = finiteSourceExtension hT hα q :=
  rfl

theorem norm_finiteSourceExtensionL_le
    (hT : t₀ < T) (hα : 0 < α) :
    ‖finiteSourceExtensionL (X := X) (E := E) hT hα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- At every point of the original positive-time cylinder, clamping does
nothing and the extension returns the original datum. -/
theorem eval_finiteSourceExtension_of_mem
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    evalCLM z (Set.mem_univ z) (finiteSourceExtension hT hα q) =
      evalCLM z hz q := by
  have ht : z.1 ∈ Set.Ioc t₀ T := hz.1
  let tz : ↥(Set.Icc t₀ T) := ⟨z.1, ht.1.le, ht.2⟩
  let tp : positiveTimeInIcc t₀ T := ⟨tz, ht.1⟩
  rw [eval_finiteSourceExtension]
  change finiteClosedTimeSlice hT hα q
      (Set.projIcc t₀ T hT.le z.1) z.2 = evalCLM z hz q
  rw [Set.projIcc_of_mem hT.le tz.2]
  change finiteClosedTimeSlice hT hα q (tp : ↥(Set.Icc t₀ T)) z.2 = _
  rw [finiteClosedTimeSlice_apply_positive]
  rfl

/-- Restricting the extension back to the finite cylinder is exactly the
identity. -/
theorem restrict_finiteSourceExtension
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    restrictL (Set.subset_univ _)
      (finiteSourceExtension hT hα q) = q := by
  apply eq_of_eval_eq
  intro z hz
  rw [evalCLM_restrictL_apply]
  exact eval_finiteSourceExtension_of_mem hT hα q z hz

/-- Operator form of the exact right-inverse identity. -/
theorem restrictL_comp_finiteSourceExtensionL
    (hT : t₀ < T) (hα : 0 < α) :
    (restrictL (X := X) (E := E) (α := α)
      (s := (Set.univ : Set (ℝ × X)))
      (t := parabolicFiniteCylinder X t₀ T)
      (Set.subset_univ _)).comp
        (finiteSourceExtensionL hT hα) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach X E α
          (parabolicFiniteCylinder X t₀ T)) := by
  ext q
  exact restrict_finiteSourceExtension hT hα q

/-- Extend data from a shorter finite cylinder to a longer one by the
canonical clamped extension, then restrict the global extension to the longer
cylinder.  The construction costs at most the universal factor three and is
independent of the length of the longer interval. -/
noncomputable def extendTerminalL
    {S T : ℝ} (hS : t₀ < S) (hST : S ≤ T) (hα : 0 < α) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ S) →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  (restrictL (X := X) (E := E) (α := α)
    (s := (Set.univ : Set (ℝ × X)))
    (t := parabolicFiniteCylinder X t₀ T) (Set.subset_univ _)).comp
      (finiteSourceExtensionL hS hα)

theorem norm_extendTerminalL_le
    {S T : ℝ} (hS : t₀ < S) (hST : S ≤ T) (hα : 0 < α) :
    ‖extendTerminalL (X := X) (E := E) hS hST hα‖ ≤ 3 := by
  calc
    ‖extendTerminalL (X := X) (E := E) hS hST hα‖ ≤
        ‖restrictL (X := X) (E := E) (α := α)
          (s := (Set.univ : Set (ℝ × X)))
          (t := parabolicFiniteCylinder X t₀ T) (Set.subset_univ _)‖ *
          ‖finiteSourceExtensionL hS hα‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 3 := mul_le_mul
      (norm_restrictL_le (Set.subset_univ _))
      (norm_finiteSourceExtensionL_le hS hα)
      (norm_nonneg _) zero_le_one
    _ = 3 := one_mul 3

/-- Restricting the canonical short-to-long extension back to the short
cylinder is exactly the original datum. -/
theorem restrict_extendTerminalL
    {S T : ℝ} (hS : t₀ < S) (hST : S ≤ T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ S)) :
    restrictL (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST)
      (extendTerminalL hS hST hα q) = q := by
  apply eq_of_eval_eq
  intro z hz
  rw [evalCLM_restrictL_apply]
  change evalCLM z _
      (restrictL (Set.subset_univ _)
        (finiteSourceExtension hS hα q)) = evalCLM z hz q
  rw [evalCLM_restrictL_apply]
  exact eval_finiteSourceExtension_of_mem hS hα q z hz

/-- Operator form of the short-cylinder retraction identity. -/
theorem restrictL_comp_extendTerminalL
    {S T : ℝ} (hS : t₀ < S) (hST : S ≤ T) (hα : 0 < α) :
    (restrictL (X := X) (E := E) (α := α)
      (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST)).comp
        (extendTerminalL hS hST hα) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach X E α
          (parabolicFiniteCylinder X t₀ S)) := by
  ext q
  exact restrict_extendTerminalL hS hST hα q

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
