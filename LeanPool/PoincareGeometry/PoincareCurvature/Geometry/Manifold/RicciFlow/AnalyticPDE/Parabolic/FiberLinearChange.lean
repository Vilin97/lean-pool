/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach

/-!
# Linear changes in the value fibre of parabolic Banach spaces

A bounded linear map on the value space acts on a parabolic four-jet by
postcomposition.  This file packages that operation on the genuine
`C^{2+α,1+α/2}` finite-cylinder Banach space and proves its pointwise chain
rules.  It is used below to pass between tensor coefficients indexed by
pairs and the curried matrix representation consumed by the Euclidean heat
solver.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[reducible] local instance fiberChangeFirstENormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance fiberChangeFirstENormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance fiberChangeFirstFNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance fiberChangeFirstFNormedSpace :
    NormedSpace ℝ (X →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance fiberChangeSecondENormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance fiberChangeSecondENormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance fiberChangeSecondFNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance fiberChangeSecondFNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

/-- Postcomposition of a first derivative by a bounded linear map on the
value fibre. -/
def postcomposeFirstDerivativeL (B : E →L[ℝ] F) :
    (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] F) :=
  ContinuousLinearMap.compL ℝ X E F B

@[simp]
theorem postcomposeFirstDerivativeL_apply
    (B : E →L[ℝ] F) (D : X →L[ℝ] E) (v : X) :
    postcomposeFirstDerivativeL B D v = B (D v) := by
  rfl

/-- Postcomposition of the value of a second derivative. -/
def postcomposeSecondDerivativeL (B : E →L[ℝ] F) :
    (X →L[ℝ] X →L[ℝ] E) →L[ℝ] (X →L[ℝ] X →L[ℝ] F) :=
  ContinuousLinearMap.compL ℝ X (X →L[ℝ] E) (X →L[ℝ] F)
    (postcomposeFirstDerivativeL B)

@[simp]
theorem postcomposeSecondDerivativeL_apply
    (B : E →L[ℝ] F) (D : X →L[ℝ] X →L[ℝ] E) (v w : X) :
    postcomposeSecondDerivativeL B D v w = B (D v w) := by
  rfl

namespace FiniteParabolicC2AlphaAmbient

variable {t₀ T α : ℝ}

/-- Postcomposition of all four entries of an ambient parabolic jet by a
bounded linear map on the value fibre. -/
def fiberPostcompL (B : E →L[ℝ] F) :
    FiniteParabolicC2AlphaAmbient X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaAmbient X F t₀ T α := by
  let V := ParabolicC0AlphaBanach.compL
    (X := X) (E := E) (F := F) (α := α)
      (s := parabolicFiniteCylinder X t₀ T) B
  let D := ParabolicC0AlphaBanach.compL
    (X := X) (E := X →L[ℝ] E) (F := X →L[ℝ] F)
    (α := α) (s := parabolicFiniteCylinder X t₀ T)
    (postcomposeFirstDerivativeL B)
  let D2 := ParabolicC0AlphaBanach.compL
    (X := X) (E := X →L[ℝ] X →L[ℝ] E)
      (F := X →L[ℝ] X →L[ℝ] F) (α := α)
      (s := parabolicFiniteCylinder X t₀ T) (postcomposeSecondDerivativeL B)
  let Dt := ParabolicC0AlphaBanach.compL
    (X := X) (E := E) (F := F) (α := α)
      (s := parabolicFiniteCylinder X t₀ T) B
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
theorem value_fiberPostcompL
    (B : E →L[ℝ] F) (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    value (fiberPostcompL B q) z = B (value q z) := by
  unfold value
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((fiberPostcompL B q).1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.compL B q.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceDeriv (fiberPostcompL B q) z =
      postcomposeFirstDerivativeL B (spaceDeriv q z) := by
  unfold spaceDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((fiberPostcompL B q).2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.compL (postcomposeFirstDerivativeL B) q.2.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem spaceSecondDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceSecondDeriv (fiberPostcompL B q) z =
      postcomposeSecondDerivativeL B (spaceSecondDeriv q z) := by
  unfold spaceSecondDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((fiberPostcompL B q).2.2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.compL (postcomposeSecondDerivativeL B) q.2.2.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp]
theorem timeDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    timeDeriv (fiberPostcompL B q) z = B (timeDeriv q z) := by
  unfold timeDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((fiberPostcompL B q).2.2.2) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.compL B q.2.2.2) = _
  rw [ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

/-- Fibre postcomposition preserves the genuine derivative-graph
compatibility conditions. -/
theorem fiberPostcompL_mem_compatibleSubmodule
    (B : E →L[ℝ] F) (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (hq : q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)) :
    fiberPostcompL B q ∈ compatibleSubmodule
      (X := X) (E := F) (t₀ := t₀) (T := T) (α := α) := by
  constructor
  · intro t ht x
    have h := B.hasFDerivAt.comp x (hq.hasSpaceDeriv t ht x)
    convert h using 1
    · funext y
      rw [value_fiberPostcompL B q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceDeriv_fiberPostcompL B q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    let K := postcomposeFirstDerivativeL (X := X) B
    have h := K.hasFDerivAt.comp x (hq.hasSpaceSecondDeriv t ht x)
    convert h using 1
    · funext y
      rw [spaceDeriv_fiberPostcompL B q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceSecondDeriv_fiberPostcompL B q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    have h := (B.hasFDerivAt.comp t (hq.hasTimeDeriv t ht x))
    have hnhds : Set.Ioc t₀ T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev :
        (fun s : ℝ => value (fiberPostcompL B q) (s, x)) =ᶠ[𝓝 t]
          fun s : ℝ => B (value q (s, x)) := by
      filter_upwards [hnhds] with s hs
      rw [value_fiberPostcompL B q (s, x)
        (by simpa [parabolicFiniteCylinder] using hs)]
    have htIoc : (t, x) ∈ parabolicFiniteCylinder X t₀ T := by
      simp [parabolicFiniteCylinder, ht.1, ht.2.le]
    rw [timeDeriv_fiberPostcompL B q (t, x) htIoc]
    have hh := h.congr_of_eventuallyEq hev
    change HasFDerivAt (fun s : ℝ => value (fiberPostcompL B q) (s, x))
      (ContinuousLinearMap.toSpanSingleton ℝ (B (timeDeriv q (t, x)))) t
    have hmaps :
        ContinuousLinearMap.toSpanSingleton ℝ (B (timeDeriv q (t, x))) =
          B.comp (ContinuousLinearMap.toSpanSingleton ℝ (timeDeriv q (t, x))) := by
      ext c
      simp
    rw [hmaps]
    exact hh

end FiniteParabolicC2AlphaAmbient

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

/-- Bounded postcomposition on the genuine finite-cylinder parabolic Banach
space. -/
def fiberPostcompL (B : E →L[ℝ] F) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach X F t₀ T α :=
  (FiniteParabolicC2AlphaAmbient.fiberPostcompL
      (X := X) (E := E) (F := F) (t₀ := t₀) (T := T) (α := α) B).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL |>.codRestrict
    (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
      (X := X) (E := F) (t₀ := t₀) (T := T) (α := α))
    (fun u => FiniteParabolicC2AlphaAmbient.fiberPostcompL_mem_compatibleSubmodule
      B u.1 u.2)

@[simp]
theorem value_fiberPostcompL
    (B : E →L[ℝ] F) (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    value (fiberPostcompL B u) z = B (value u z) := by
  exact FiniteParabolicC2AlphaAmbient.value_fiberPostcompL B u.1 z hz

@[simp]
theorem spaceDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceDeriv (fiberPostcompL B u) z =
      postcomposeFirstDerivativeL B (spaceDeriv u z) := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_fiberPostcompL B u.1 z hz

@[simp]
theorem spaceSecondDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceSecondDeriv (fiberPostcompL B u) z =
      postcomposeSecondDerivativeL B (spaceSecondDeriv u z) := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_fiberPostcompL B u.1 z hz

@[simp]
theorem timeDeriv_fiberPostcompL
    (B : E →L[ℝ] F) (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    timeDeriv (fiberPostcompL B u) z = B (timeDeriv u z) := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_fiberPostcompL B u.1 z hz

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
