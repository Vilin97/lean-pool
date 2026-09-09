/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.LpDominatedDerivative
public import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Compact smooth fields have actual smooth mixed L² translation orbits

This is a full Fréchet derivative in the four-dimensional covering space.
The compact support argument controls every small covering translation,
including its angular component, before dominated L² differentiation.
-/

noncomputable section

namespace EulerCylinderCompact

open Set MeasureTheory ContinuousLinearMap Filter EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerMetricTransport
  EulerLiftedWeakDerivative EulerPressureSpatialRegularity EulerLpDerivative
  EulerTransportDerivatives
open scoped ContDiff Topology

universe u

variable (P : ℝ) [Fact (0 < P)]

structure CompactField (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : LiftDomain P → V
  compact : HasCompactSupport field
  smooth : ∀ x, ContDiff ℝ ∞ (localFieldLift P field x)

namespace CompactField

variable {P} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] in
theorem continuous (A : CompactField P V) : Continuous A.field :=
  smoothField_continuous P A.field A.smooth

def toLp (A : CompactField P V) : CylinderL2 P V :=
  (A.continuous.memLp_of_hasCompactSupport A.compact).toLp A.field

theorem toLp_ae (A : CompactField P V) : A.toLp =ᵐ[liftMeasure P] A.field :=
  (A.continuous.memLp_of_hasCompactSupport A.compact).coeFn_toLp

def derivative (A : CompactField P V) : CompactField P (LiftTangent →L[ℝ] V) where
  field := fieldFDeriv P A.field
  compact := fieldFDeriv_compact P A.field A.compact
  smooth := fieldFDeriv_smooth P A.field A.smooth

omit [Fact (0 < P)] in
theorem derivative_bound (A : CompactField P V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x a, ‖fderiv ℝ (localFieldLift P A.field x) a‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := (A.derivative.compact.isCompact_range
    A.derivative.continuous).isBounded.exists_pos_norm_le
  refine ⟨C,hC.le,fun x a => ?_⟩
  have hx := hb (A.derivative.field (x.1+a.1,x.2+(a.2 : AddCircle P))) (mem_range_self _)
  change ‖fieldFDeriv P A.field (x.1+a.1,x.2+(a.2 : AddCircle P))‖ ≤ C at hx
  rw [fieldFDeriv,fderiv_localFieldLift_shift] at hx
  exact hx

omit [Fact (0 < P)] in
/-- One compact set contains every translate by a covering vector of norm at most one. -/
theorem translation_support (A : CompactField P V) :
    ∃ K : Set (LiftDomain P), IsCompact K ∧ tsupport A.field ⊆ K ∧
      ∀ a : LiftTangent, ‖a‖ ≤ 1 → ∀ x ∉ K, A.field (x+coveringMap P a) = 0 := by
  let K := (fun p : LiftDomain P × LiftTangent => p.1-coveringMap P p.2) ''
    (tsupport A.field ×ˢ Metric.closedBall (0 : LiftTangent) 1)
  have hK : IsCompact K := (A.compact.isCompact.prod (isCompact_closedBall _ _)).image
    (continuous_fst.sub ((coveringMap_isOpenQuotient P).continuous.comp continuous_snd))
  refine ⟨K,hK,?_,?_⟩
  · intro x hx
    refine ⟨(x,0),⟨hx,by simp⟩,?_⟩
    simp [coveringMap]
  · intro a ha x hx
    by_contra hn
    apply hx
    refine ⟨(x+coveringMap P a,a),⟨subset_tsupport A.field hn,?_⟩,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using ha
    · exact add_sub_cancel_right x (coveringMap P a)

theorem increment_bound (A : CompactField P V) :
    ∃ M : LiftDomain P → ℝ, MemLp M 2 (liftMeasure P) ∧ (∀ x, 0 ≤ M x) ∧
      ∀ a : LiftTangent, ‖a‖ ≤ 1 → ∀ x,
        ‖A.field (x+coveringMap P a)-A.field x‖ ≤ M x*‖a‖ := by
  obtain ⟨C,hC,hb⟩ := A.derivative_bound
  obtain ⟨K,hK,hsub,hshift⟩ := A.translation_support
  refine ⟨K.indicator (fun _ => C),memLp_indicator_const 2 hK.isClosed.measurableSet C
    (Or.inr hK.measure_ne_top),fun x => Set.indicator_nonneg (fun _ _ => hC) x,?_⟩
  intro a ha x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := localFieldLift P A.field x) (s := Set.univ)
      (fun b _ => (A.smooth x).differentiable (by simp) b) (fun b _ => hb x b)
      (convex_univ : Convex ℝ (Set.univ : Set LiftTangent)) (Set.mem_univ 0) (Set.mem_univ a)
    change ‖A.field (x.1+a.1,x.2+(a.2 : AddCircle P))-A.field x‖ ≤ C*‖a‖
    simpa only [localFieldLift,Prod.fst_zero,Prod.snd_zero,AddCircle.coe_zero,
      add_zero,sub_zero] using hh
  · have hzero : A.field x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hsub hs))
    simp only [hshift a ha x hx,hzero,sub_zero,norm_zero,Set.indicator_of_notMem
      hx,zero_mul,le_refl]

theorem hasFDerivAt_zero (A : CompactField P V) :
    HasFDerivAt (fun a : LiftTangent => translate P a A.toLp)
      (derivativeMap (liftMeasure P) A.derivative.toLp) 0 := by
  obtain ⟨M,hM,hM0,hb⟩ := A.increment_bound
  refine hasFDerivAt_of_dominated (liftMeasure P)
    (fun a : LiftTangent => translate P a A.toLp)
    (fun a x => A.field (x+coveringMap P a)) ?_ A.derivative.toLp ?_ M hM (Eventually.of_forall
      hM0) ?_
  · intro a
    filter_upwards [translate_ae P a A.toLp,
      (measurePreserving_translation P (coveringMap P a)).quasiMeasurePreserving.ae A.toLp_ae]
      with x ht hx
    exact ht.trans hx
  · filter_upwards [A.derivative.toLp_ae] with x hx
    rw [hx]
    exact ((A.smooth x).differentiable (by simp) 0).hasFDerivAt
  · filter_upwards [Metric.ball_mem_nhds (0 : LiftTangent) zero_lt_one] with a ha
    apply Eventually.of_forall
    intro x
    simpa only [coveringMap,Prod.fst_zero,Prod.snd_zero,AddCircle.coe_zero,Prod.mk_zero_zero,add_zero] using
      hb a ((by simpa only [Metric.mem_ball,dist_zero_right] using ha : ‖a‖ < 1).le) x

theorem derivativeMap_translation (D : CylinderL2 P (LiftTangent →L[ℝ] V)) (a : LiftTangent) :
    derivativeMap (liftMeasure P) (translate P a D) =
      (translate P a).toContinuousLinearMap.comp (derivativeMap (liftMeasure P) D) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [derivativeMap_ae (liftMeasure P) (translate P a D) v,translate_ae P a D,
    translate_ae P a (derivativeMap (liftMeasure P) D v),
    (measurePreserving_translation P (coveringMap P a)).quasiMeasurePreserving.ae
      (derivativeMap_ae (liftMeasure P) D v)] with x hm ht hv hd
  change derivativeMap (liftMeasure P) (translate P a D) v x = translate P a (derivativeMap
    (liftMeasure P) D v) x
  rw [hm,ht,hv,hd]

theorem translation_hasFDerivAt (A : CompactField P V) (a : LiftTangent) :
    HasFDerivAt (fun b : LiftTangent => translate P b A.toLp)
      (derivativeMap (liftMeasure P) (translate P a A.derivative.toLp)) a := by
  rw [derivativeMap_translation]
  exact EulerIsometricAction.hasFDerivAt_all (translate P) (translate_add P)
    A.toLp _ A.hasFDerivAt_zero a

theorem translation_fderiv (A : CompactField P V) :
    fderiv ℝ (fun a : LiftTangent => translate P a A.toLp) =
      fun a => derivativeBundling (liftMeasure P) (translate P a A.derivative.toLp) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)

private theorem translation_contDiff_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : CompactField P V),
      ContDiff ℝ n (fun a : LiftTangent => translate P a A.toLp) := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (translate_continuous P A.toLp)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt,by simp,?_⟩
    rw [A.translation_fderiv]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := CylinderL2 P (LiftTangent →L[ℝ] V)) (F := LiftTangent →L[ℝ] CylinderL2 P V)
      (derivativeBundling (liftMeasure P))).comp (ih (LiftTangent →L[ℝ] V) A.derivative)

/-- All four covering directions are differentiated in the actual L² norm. -/
theorem translation_contDiff (A : CompactField P V) :
    ContDiff ℝ ∞ (fun a : LiftTangent => translate P a A.toLp) :=
  contDiff_infty.mpr (fun n => translation_contDiff_aux n V A)

end CompactField
end EulerCylinderCompact
