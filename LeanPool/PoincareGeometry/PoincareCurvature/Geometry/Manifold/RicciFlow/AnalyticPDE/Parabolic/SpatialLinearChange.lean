/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach

/-!
# Spatial linear changes of variables on parabolic Banach spaces

This file packages precomposition by `(t,x) ↦ (t,Lx)` on both the
`C^{0,α}` and genuine `C^{2+α,1+α/2}` finite-cylinder Banach spaces.  The
first and second spatial derivatives are transformed by the chain rule;
time is unchanged.  These operators are the analytic transport used to turn
a positive-definite frozen principal part into the standard Euclidean heat
operator.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance spatialChangeFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance spatialChangeFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance spatialChangeSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance spatialChangeSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

/-- The space-time map induced by a linear spatial map. -/
def parabolicSpatialLinearMap (L : X →L[ℝ] X) : ℝ × X → ℝ × X :=
  fun z => (z.1, L z.2)

/-- A spatial linear map expands parabolic distance by at most
`max 1 ‖L‖`. -/
theorem parabolicDistance_spatialLinearMap_le
    (L : X →L[ℝ] X) (p q : ℝ × X) :
    parabolicDistance (parabolicSpatialLinearMap L p)
        (parabolicSpatialLinearMap L q) ≤
      max 1 ‖L‖ * parabolicDistance p q := by
  unfold parabolicSpatialLinearMap parabolicDistance
  apply max_le
  · calc
      Real.sqrt |p.1 - q.1| ≤
          max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := le_max_left _ _
      _ = 1 * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := by rw [one_mul]
      _ ≤ max 1 ‖L‖ * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (parabolicDistance.nonneg p q)
  · rw [dist_eq_norm, ← map_sub]
    calc
      ‖L (p.2 - q.2)‖ ≤ ‖L‖ * ‖p.2 - q.2‖ := L.le_opNorm _
      _ ≤ max 1 ‖L‖ * ‖p.2 - q.2‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ max 1 ‖L‖ * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := by
        apply mul_le_mul_of_nonneg_left _ (le_trans (norm_nonneg L) (le_max_right _ _))
        simpa [dist_eq_norm] using
          (le_max_right (Real.sqrt |p.1 - q.1|) (dist p.2 q.2))

/-- A spatial linear map preserves every finite time cylinder. -/
theorem parabolicSpatialLinearMap_mapsTo
    (L : X →L[ℝ] X) (t₀ T : ℝ) :
    MapsTo (parabolicSpatialLinearMap L)
      (parabolicFiniteCylinder X t₀ T)
      (parabolicFiniteCylinder X t₀ T) := by
  intro z hz
  simpa [parabolicFiniteCylinder, parabolicSpatialLinearMap] using hz

/-- Precomposition on a finite-cylinder `C^{0,α}` Banach space by a linear
spatial map. -/
def ParabolicC0AlphaBanach.spatialPrecompL
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : X →L[ℝ] X) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  ParabolicC0AlphaBanach.precompL hα
    (zero_le_one.trans (le_max_left _ _))
    (parabolicSpatialLinearMap_mapsTo L t₀ T)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMap_le L p q)

@[simp]
theorem ParabolicC0AlphaBanach.evalCLM_spatialPrecompL
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (u : ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T))
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (ParabolicC0AlphaBanach.spatialPrecompL hα L u) =
      ParabolicC0AlphaBanach.evalCLM (parabolicSpatialLinearMap L z)
        (parabolicSpatialLinearMap_mapsTo L t₀ T hz) u := by
  exact ParabolicC0AlphaBanach.evalCLM_precompL_apply
    hα (zero_le_one.trans (le_max_left _ _))
    (parabolicSpatialLinearMap_mapsTo L t₀ T)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMap_le L p q) z hz u

/-- Precomposition of a first derivative by a linear spatial map. -/
def precomposeFirstDerivativeL (L : X →L[ℝ] X) :
    (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ X X E).flip L

@[simp]
theorem precomposeFirstDerivativeL_apply
    (L : X →L[ℝ] X) (D : X →L[ℝ] E) (v : X) :
    precomposeFirstDerivativeL L D v = D (L v) := by
  rfl

/-- Precomposition of both inputs of a second derivative by a linear
spatial map. -/
def precomposeSecondDerivativeL (L : X →L[ℝ] X) :
    (X →L[ℝ] X →L[ℝ] E) →L[ℝ] (X →L[ℝ] X →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ X (X →L[ℝ] E) (X →L[ℝ] E)
      (precomposeFirstDerivativeL L)).comp
    ((ContinuousLinearMap.compL ℝ X X (X →L[ℝ] E)).flip L)

@[simp]
theorem precomposeSecondDerivativeL_apply
    (L : X →L[ℝ] X) (D : X →L[ℝ] X →L[ℝ] E) (v w : X) :
    precomposeSecondDerivativeL L D v w = D (L v) (L w) := by
  rfl

namespace FiniteParabolicC2AlphaAmbient

variable {t₀ T α : ℝ}

/-- The ambient four-jet change-of-variables operator. -/
def spatialPrecompL (hα : 0 ≤ α) (L : X →L[ℝ] X) :
    FiniteParabolicC2AlphaAmbient X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaAmbient X E t₀ T α := by
  let V := ParabolicC0AlphaBanach.spatialPrecompL
    (X := X) (E := E) (t₀ := t₀) (T := T) hα L
  let D0 := ParabolicC0AlphaBanach.spatialPrecompL
    (X := X) (E := X →L[ℝ] E) (t₀ := t₀) (T := T) hα L
  let D := (ParabolicC0AlphaBanach.compL
      (precomposeFirstDerivativeL (E := E) L)).comp D0
  let D20 := ParabolicC0AlphaBanach.spatialPrecompL
    (X := X) (E := X →L[ℝ] X →L[ℝ] E) (t₀ := t₀) (T := T) hα L
  let D2 := (ParabolicC0AlphaBanach.compL
      (precomposeSecondDerivativeL (E := E) L)).comp D20
  let Dt := ParabolicC0AlphaBanach.spatialPrecompL
    (X := X) (E := E) (t₀ := t₀) (T := T) hα L
  exact
    (V.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((D.comp ((ContinuousLinearMap.fst ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))).prod
        ((D2.comp ((ContinuousLinearMap.fst ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _)))).prod
          (Dt.comp ((ContinuousLinearMap.snd ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _))))))

@[simp]
theorem value_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    value (spatialPrecompL hα L q) z =
      value q (parabolicSpatialLinearMap L z) := by
  unfold value
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPrecompL hα L q).1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.spatialPrecompL hα L q.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_spatialPrecompL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceDeriv (spatialPrecompL hα L q) z =
      precomposeFirstDerivativeL L
        (spaceDeriv q (parabolicSpatialLinearMap L z)) := by
  unfold spaceDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPrecompL hα L q).2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (precomposeFirstDerivativeL L)).comp
        (ParabolicC0AlphaBanach.spatialPrecompL hα L) q.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_spatialPrecompL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceSecondDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceSecondDeriv (spatialPrecompL hα L q) z =
      precomposeSecondDerivativeL L
        (spaceSecondDeriv q (parabolicSpatialLinearMap L z)) := by
  unfold spaceSecondDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPrecompL hα L q).2.2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (precomposeSecondDerivativeL L)).comp
        (ParabolicC0AlphaBanach.spatialPrecompL hα L) q.2.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_spatialPrecompL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem timeDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    timeDeriv (spatialPrecompL hα L q) z =
      timeDeriv q (parabolicSpatialLinearMap L z) := by
  unfold timeDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPrecompL hα L q).2.2.2) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.spatialPrecompL hα L q.2.2.2) = _
  rw [ParabolicC0AlphaBanach.evalCLM_spatialPrecompL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

/-- The ambient spatial change of variables preserves the derivative-graph
compatibility conditions. -/
theorem spatialPrecompL_mem_compatibleSubmodule
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (hq : q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)) :
    spatialPrecompL hα L q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) := by
  constructor
  · intro t ht x
    have h := (hq.hasSpaceDeriv t ht (L x)).comp x L.hasFDerivAt
    convert h using 1
    · funext y
      rw [value_spatialPrecompL hα L q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceDeriv_spatialPrecompL hα L q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    let K := precomposeFirstDerivativeL (E := E) L
    have hcomp := (hq.hasSpaceSecondDeriv t ht (L x)).comp x L.hasFDerivAt
    have h := K.hasFDerivAt.comp x hcomp
    convert h using 1
    · funext y
      rw [spaceDeriv_spatialPrecompL hα L q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceSecondDeriv_spatialPrecompL hα L q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    have h := hq.hasTimeDeriv t ht (L x)
    have hnhds : Set.Ioc t₀ T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev :
        (fun s : ℝ => value (spatialPrecompL hα L q) (s, x)) =ᶠ[𝓝 t]
          fun s : ℝ => value q (s, L x) := by
      filter_upwards [hnhds] with s hs
      rw [value_spatialPrecompL hα L q (s, x)
        (by simpa [parabolicFiniteCylinder] using hs)]
      rfl
    have htIoc : (t, x) ∈ parabolicFiniteCylinder X t₀ T := by
      simp [parabolicFiniteCylinder, ht.1, ht.2.le]
    rw [timeDeriv_spatialPrecompL hα L q (t, x) htIoc]
    exact h.congr_of_eventuallyEq hev

end FiniteParabolicC2AlphaAmbient

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

/-- Bounded spatial linear precomposition on the genuine finite-cylinder
higher parabolic Banach space. -/
def spatialPrecompL (hα : 0 ≤ α) (L : X →L[ℝ] X) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach X E t₀ T α :=
  (FiniteParabolicC2AlphaAmbient.spatialPrecompL
      (X := X) (E := E) (t₀ := t₀) (T := T) hα L).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL |>.codRestrict
    (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (fun u => FiniteParabolicC2AlphaAmbient.spatialPrecompL_mem_compatibleSubmodule
      hα L u.1 u.2)

@[simp]
theorem value_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    value (spatialPrecompL hα L u) z =
      value u (parabolicSpatialLinearMap L z) := by
  exact FiniteParabolicC2AlphaAmbient.value_spatialPrecompL hα L u.1 z hz

@[simp]
theorem spaceDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceDeriv (spatialPrecompL hα L u) z =
      precomposeFirstDerivativeL L
        (spaceDeriv u (parabolicSpatialLinearMap L z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_spatialPrecompL hα L u.1 z hz

@[simp]
theorem spaceSecondDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceSecondDeriv (spatialPrecompL hα L u) z =
      precomposeSecondDerivativeL L
        (spaceSecondDeriv u (parabolicSpatialLinearMap L z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_spatialPrecompL hα L u.1 z hz

@[simp]
theorem timeDeriv_spatialPrecompL
    (hα : 0 ≤ α) (L : X →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    timeDeriv (spatialPrecompL hα L u) z =
      timeDeriv u (parabolicSpatialLinearMap L z) := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_spatialPrecompL hα L u.1 z hz

end FiniteParabolicC2AlphaBanach

/-! ## Changes between two finite-dimensional model spaces -/

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The space-time map induced by a linear map between two spatial model
spaces.  The time coordinate is unchanged. -/
def parabolicSpatialLinearMapBetween (L : Y →L[ℝ] X) : ℝ × Y → ℝ × X :=
  fun z => (z.1, L z.2)

/-- A linear spatial map between two model spaces distorts parabolic
distance by at most `max 1 ‖L‖`. -/
theorem parabolicDistance_spatialLinearMapBetween_le
    (L : Y →L[ℝ] X) (p q : ℝ × Y) :
    parabolicDistance (parabolicSpatialLinearMapBetween L p)
        (parabolicSpatialLinearMapBetween L q) ≤
      max 1 ‖L‖ * parabolicDistance p q := by
  unfold parabolicSpatialLinearMapBetween parabolicDistance
  apply max_le
  · calc
      Real.sqrt |p.1 - q.1| ≤
          max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := le_max_left _ _
      _ = 1 * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := by rw [one_mul]
      _ ≤ max 1 ‖L‖ * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (parabolicDistance.nonneg p q)
  · rw [dist_eq_norm, ← map_sub]
    calc
      ‖L (p.2 - q.2)‖ ≤ ‖L‖ * ‖p.2 - q.2‖ := L.le_opNorm _
      _ ≤ max 1 ‖L‖ * ‖p.2 - q.2‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ max 1 ‖L‖ * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) := by
        apply mul_le_mul_of_nonneg_left _
          (le_trans (norm_nonneg L) (le_max_right _ _))
        simpa [dist_eq_norm] using
          (le_max_right (Real.sqrt |p.1 - q.1|) (dist p.2 q.2))

/-- A spatial linear map between model spaces preserves the finite time
interval defining the parabolic cylinders. -/
theorem parabolicSpatialLinearMapBetween_mapsTo
    (L : Y →L[ℝ] X) (t₀ T : ℝ) :
    MapsTo (parabolicSpatialLinearMapBetween L)
      (parabolicFiniteCylinder Y t₀ T)
      (parabolicFiniteCylinder X t₀ T) := by
  intro z hz
  simpa [parabolicFiniteCylinder, parabolicSpatialLinearMapBetween] using hz

/-- Pullback of finite-cylinder `C^{0,α}` functions along a linear map
between spatial model spaces. -/
def ParabolicC0AlphaBanach.spatialPullbackL
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach Y E α (parabolicFiniteCylinder Y t₀ T) :=
  ParabolicC0AlphaBanach.precompL hα
    (zero_le_one.trans (le_max_left _ _))
    (parabolicSpatialLinearMapBetween_mapsTo L t₀ T)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMapBetween_le L p q)

@[simp]
theorem ParabolicC0AlphaBanach.evalCLM_spatialPullbackL
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T))
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (ParabolicC0AlphaBanach.spatialPullbackL hα L u) =
      ParabolicC0AlphaBanach.evalCLM (parabolicSpatialLinearMapBetween L z)
        (parabolicSpatialLinearMapBetween_mapsTo L t₀ T hz) u := by
  exact ParabolicC0AlphaBanach.evalCLM_precompL_apply
    hα (zero_le_one.trans (le_max_left _ _))
    (parabolicSpatialLinearMapBetween_mapsTo L t₀ T)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMapBetween_le L p q) z hz u

/-- Pullback of global `C^{0,α}` sources along a linear map between spatial
model spaces. -/
def ParabolicC0AlphaBanach.globalSpatialPullbackL
    {α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) :
    ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) →L[ℝ]
      ParabolicC0AlphaBanach Y E α (Set.univ : Set (ℝ × Y)) :=
  ParabolicC0AlphaBanach.precompL hα
    (zero_le_one.trans (le_max_left _ _))
    (fun _ _ => Set.mem_univ _)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMapBetween_le L p q)

@[simp]
theorem ParabolicC0AlphaBanach.evalCLM_globalSpatialPullbackL
    {α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)))
    (z : ℝ × Y) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z)
        (ParabolicC0AlphaBanach.globalSpatialPullbackL hα L u) =
      ParabolicC0AlphaBanach.evalCLM
        (parabolicSpatialLinearMapBetween L z) (Set.mem_univ _) u := by
  exact ParabolicC0AlphaBanach.evalCLM_precompL_apply
    hα (zero_le_one.trans (le_max_left _ _))
    (fun _ _ => Set.mem_univ _)
    (fun p _hp q _hq => parabolicDistance_spatialLinearMapBetween_le L p q)
    z (Set.mem_univ z) u

/-- Pullback of a first derivative along a linear map between its source
spaces. -/
def pullbackFirstDerivativeL (L : Y →L[ℝ] X) :
    (X →L[ℝ] E) →L[ℝ] (Y →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ Y X E).flip L

@[simp]
theorem pullbackFirstDerivativeL_apply
    (L : Y →L[ℝ] X) (D : X →L[ℝ] E) (v : Y) :
    pullbackFirstDerivativeL L D v = D (L v) := by
  rfl

/-- Pullback of both inputs of a second derivative along a linear map. -/
def pullbackSecondDerivativeL (L : Y →L[ℝ] X) :
    (X →L[ℝ] X →L[ℝ] E) →L[ℝ] (Y →L[ℝ] Y →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ Y (X →L[ℝ] E) (Y →L[ℝ] E)
      (pullbackFirstDerivativeL L)).comp
    ((ContinuousLinearMap.compL ℝ Y X (X →L[ℝ] E)).flip L)

@[simp]
theorem pullbackSecondDerivativeL_apply
    (L : Y →L[ℝ] X) (D : X →L[ℝ] X →L[ℝ] E) (v w : Y) :
    pullbackSecondDerivativeL L D v w = D (L v) (L w) := by
  rfl

namespace FiniteParabolicC2AlphaAmbient

variable {t₀ T α : ℝ}

/-- Pullback of an ambient four-jet between two spatial model spaces. -/
def spatialPullbackL (hα : 0 ≤ α) (L : Y →L[ℝ] X) :
    FiniteParabolicC2AlphaAmbient X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaAmbient Y E t₀ T α := by
  let V := ParabolicC0AlphaBanach.spatialPullbackL
    (X := X) (Y := Y) (E := E) (t₀ := t₀) (T := T) hα L
  let D0 := ParabolicC0AlphaBanach.spatialPullbackL
    (X := X) (Y := Y) (E := X →L[ℝ] E) (t₀ := t₀) (T := T) hα L
  let D := (ParabolicC0AlphaBanach.compL
      (pullbackFirstDerivativeL (E := E) L)).comp D0
  let D20 := ParabolicC0AlphaBanach.spatialPullbackL
    (X := X) (Y := Y) (E := X →L[ℝ] X →L[ℝ] E)
      (t₀ := t₀) (T := T) hα L
  let D2 := (ParabolicC0AlphaBanach.compL
      (pullbackSecondDerivativeL (E := E) L)).comp D20
  let Dt := ParabolicC0AlphaBanach.spatialPullbackL
    (X := X) (Y := Y) (E := E) (t₀ := t₀) (T := T) hα L
  exact
    (V.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((D.comp ((ContinuousLinearMap.fst ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))).prod
        ((D2.comp ((ContinuousLinearMap.fst ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _)))).prod
          (Dt.comp ((ContinuousLinearMap.snd ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _))))))

@[simp]
theorem value_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × Y)
    (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    value (spatialPullbackL hα L q) z =
      value q (parabolicSpatialLinearMapBetween L z) := by
  unfold value
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPullbackL hα L q).1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.spatialPullbackL hα L q.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_spatialPullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × Y)
    (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    spaceDeriv (spatialPullbackL hα L q) z =
      pullbackFirstDerivativeL L
        (spaceDeriv q (parabolicSpatialLinearMapBetween L z)) := by
  unfold spaceDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPullbackL hα L q).2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (pullbackFirstDerivativeL L)).comp
        (ParabolicC0AlphaBanach.spatialPullbackL hα L) q.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_spatialPullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceSecondDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × Y)
    (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    spaceSecondDeriv (spatialPullbackL hα L q) z =
      pullbackSecondDerivativeL L
        (spaceSecondDeriv q (parabolicSpatialLinearMapBetween L z)) := by
  unfold spaceSecondDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPullbackL hα L q).2.2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (pullbackSecondDerivativeL L)).comp
        (ParabolicC0AlphaBanach.spatialPullbackL hα L) q.2.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_spatialPullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem timeDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × Y)
    (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    timeDeriv (spatialPullbackL hα L q) z =
      timeDeriv q (parabolicSpatialLinearMapBetween L z) := by
  unfold timeDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((spatialPullbackL hα L q).2.2.2) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.spatialPullbackL hα L q.2.2.2) = _
  rw [ParabolicC0AlphaBanach.evalCLM_spatialPullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

/-- Pullback between model spaces preserves all derivative-graph
compatibility conditions. -/
theorem spatialPullbackL_mem_compatibleSubmodule
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (hq : q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)) :
    spatialPullbackL hα L q ∈ compatibleSubmodule
      (X := Y) (E := E) (t₀ := t₀) (T := T) (α := α) := by
  constructor
  · intro t ht y
    have h := (hq.hasSpaceDeriv t ht (L y)).comp y L.hasFDerivAt
    convert h using 1
    · funext y'
      rw [value_spatialPullbackL hα L q (t, y')
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceDeriv_spatialPullbackL hα L q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht y
    let K := pullbackFirstDerivativeL (E := E) L
    have hcomp := (hq.hasSpaceSecondDeriv t ht (L y)).comp y L.hasFDerivAt
    have h := K.hasFDerivAt.comp y hcomp
    convert h using 1
    · funext y'
      rw [spaceDeriv_spatialPullbackL hα L q (t, y')
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceSecondDeriv_spatialPullbackL hα L q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht y
    have h := hq.hasTimeDeriv t ht (L y)
    have hnhds : Set.Ioc t₀ T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev :
        (fun s : ℝ => value (spatialPullbackL hα L q) (s, y)) =ᶠ[𝓝 t]
          fun s : ℝ => value q (s, L y) := by
      filter_upwards [hnhds] with s hs
      rw [value_spatialPullbackL hα L q (s, y)
        (by simpa [parabolicFiniteCylinder] using hs)]
      rfl
    have htIoc : (t, y) ∈ parabolicFiniteCylinder Y t₀ T := by
      simp [parabolicFiniteCylinder, ht.1, ht.2.le]
    rw [timeDeriv_spatialPullbackL hα L q (t, y) htIoc]
    exact h.congr_of_eventuallyEq hev

end FiniteParabolicC2AlphaAmbient

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

/-- Bounded pullback between genuine finite-cylinder higher parabolic
Banach spaces. -/
def spatialPullbackL (hα : 0 ≤ α) (L : Y →L[ℝ] X) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach Y E t₀ T α :=
  (FiniteParabolicC2AlphaAmbient.spatialPullbackL
      (X := X) (Y := Y) (E := E) (t₀ := t₀) (T := T) hα L).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL |>.codRestrict
    (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
      (X := Y) (E := E) (t₀ := t₀) (T := T) (α := α))
    (fun u => FiniteParabolicC2AlphaAmbient.spatialPullbackL_mem_compatibleSubmodule
      hα L u.1 u.2)

@[simp]
theorem value_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    value (spatialPullbackL hα L u) z =
      value u (parabolicSpatialLinearMapBetween L z) := by
  exact FiniteParabolicC2AlphaAmbient.value_spatialPullbackL hα L u.1 z hz

@[simp]
theorem spaceDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    spaceDeriv (spatialPullbackL hα L u) z =
      pullbackFirstDerivativeL L
        (spaceDeriv u (parabolicSpatialLinearMapBetween L z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_spatialPullbackL hα L u.1 z hz

@[simp]
theorem spaceSecondDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    spaceSecondDeriv (spatialPullbackL hα L u) z =
      pullbackSecondDerivativeL L
        (spaceSecondDeriv u (parabolicSpatialLinearMapBetween L z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_spatialPullbackL hα L u.1 z hz

@[simp]
theorem timeDeriv_spatialPullbackL
    (hα : 0 ≤ α) (L : Y →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    timeDeriv (spatialPullbackL hα L u) z =
      timeDeriv u (parabolicSpatialLinearMapBetween L z) := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_spatialPullbackL hα L u.1 z hz

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
