/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.BKARForestFormula.BKAR.PartialDeriv

/-! # The global smoothness hypothesis

Defines `BKARContDiff ρ`, the hypothesis that `ρ` is `C^∞`
(`ContDiff ℝ (∞ : WithTop ℕ∞)`) on the finite edge-coupling space, and
derives from it the analytic facts consumed by the proof of the BKAR forest
interpolation formula (see `BKAR.Formula`): continuity and differentiability
of iterated mixed partials, and integrability of the integrands appearing in
the induction.

The classical formula requires only finitely many derivatives (`C^{|V|-1}`
suffices); assuming `C^∞` is a deliberate strengthening of the hypothesis
that keeps the analytic bookkeeping uniform in the induction.
-/

open scoped ContDiff

namespace BKAR

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The global smoothness hypothesis intended to discharge the analytic side
conditions in the BKAR induction.

It is deliberately only `C^∞` smoothness on the finite edge-parameter space;
the order/support conditions remain separate combinatorial obligations.
-/
def BKARContDiff (ρ : (Edge V → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (∞ : WithTop ℕ∞) ρ

namespace BKARContDiff

variable {ρ : (Edge V → ℝ) → ℝ}

theorem contDiff (hρ : BKARContDiff ρ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) ρ :=
  hρ

theorem continuous (hρ : BKARContDiff ρ) :
    Continuous ρ :=
  hρ.contDiff.continuous

theorem differentiable (hρ : BKARContDiff ρ) :
    Differentiable ℝ ρ :=
  hρ.contDiff.differentiable (by simp)

theorem differentiableAt (hρ : BKARContDiff ρ) (x : Edge V → ℝ) :
    DifferentiableAt ℝ ρ x :=
  hρ.differentiable.differentiableAt

theorem fderiv_contDiff (hρ : BKARContDiff ρ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fderiv ℝ ρ) :=
  hρ.contDiff.fderiv_right
    (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞)) (by simp)

theorem fderiv_apply_contDiff (hρ : BKARContDiff ρ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x : Edge V → ℝ =>
        (fderiv ℝ ρ x : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e)) :=
  hρ.fderiv_contDiff.clm_apply contDiff_const

theorem partialDeriv (hρ : BKARContDiff ρ) (e : Edge V) :
    BKARContDiff (BKAR.partialDeriv e ρ) := by
  rw [BKARContDiff, ← contDiffOn_univ] at hρ ⊢
  have hρ_global : BKARContDiff ρ := by
    rwa [BKARContDiff, ← contDiffOn_univ]
  refine (hρ_global.fderiv_apply_contDiff e).contDiffOn.congr ?_
  intro x _hx
  exact partialDeriv_of_hasFDerivAt e
    ((hρ_global.differentiableAt x).hasFDerivAt)

theorem mixedPartialList (hρ : BKARContDiff ρ) (es : List (Edge V)) :
    BKARContDiff (BKAR.mixedPartialList es ρ) := by
  induction es with
  | nil =>
      simpa [BKAR.mixedPartialList] using hρ
  | cons e es ih =>
      simpa [BKAR.mixedPartialList] using ih.partialDeriv e

theorem mixedPartialList_continuous (hρ : BKARContDiff ρ)
    (es : List (Edge V)) :
    Continuous (BKAR.mixedPartialList es ρ) :=
  (hρ.mixedPartialList es).continuous

theorem mixedPartialList_differentiableAt (hρ : BKARContDiff ρ)
    (es : List (Edge V)) (x : Edge V → ℝ) :
    DifferentiableAt ℝ (BKAR.mixedPartialList es ρ) x :=
  (hρ.mixedPartialList es).differentiableAt x

theorem mixedPartialList_continuous_comp (hρ : BKARContDiff ρ)
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) :
    Continuous (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t)) :=
  (hρ.mixedPartialList es).continuous.comp hγ

theorem mixedPartialList_intervalIntegrable_comp (hρ : BKARContDiff ρ)
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t))
      MeasureTheory.volume a b :=
  (hρ.mixedPartialList_continuous_comp es hγ).intervalIntegrable a b

end BKARContDiff

/-- A continuous one-dimensional integrand has a continuous moving-upper-bound primitive. -/
theorem intervalIntegral_continuous_primitive_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (fun b : ℝ => ∫ t in a..b, f t) :=
  intervalIntegral.continuous_primitive
    (μ := MeasureTheory.volume) (fun a b => hf.intervalIntegrable a b) a

/-- The moving-upper-bound primitive of a continuous one-dimensional integrand is integrable. -/
theorem intervalIntegral_primitive_intervalIntegrable_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume b c :=
  (intervalIntegral_continuous_primitive_of_continuous hf a).intervalIntegrable b c

/--
If an integrand is interval-integrable on `[a, b]`, then its moving primitive
from `a` is interval-integrable on the same interval.
-/
theorem intervalIntegral_primitive_intervalIntegrable_of_intervalIntegrable
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume a b :=
  (intervalIntegral.continuousOn_primitive_interval'
    (μ := MeasureTheory.volume) hf Set.left_mem_uIcc).intervalIntegrable

/--
A path of finite parameter lists with fixed length whose coordinates are all
continuous. This is the small API needed for recursive ordered-simplex
diagonals such as `prefixTs ++ [t₁] ++ [t₂]`.
-/
def ListPathContinuous {X : Type*} [TopologicalSpace X]
    (n : Nat) (tsPath : X → List ℝ) : Prop :=
  (∀ x, (tsPath x).length = n) ∧
    ∀ i : Nat, Continuous (fun x => (tsPath x).getD i 0)

namespace ListPathContinuous

theorem const {X : Type*} [TopologicalSpace X] (ts : List ℝ) :
    ListPathContinuous ts.length (fun _ : X => ts) := by
  constructor
  · intro _x
    rfl
  · intro _i
    exact continuous_const

theorem comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : Nat} {tsPath : X → List ℝ}
    (hts : ListPathContinuous n tsPath) {f : Y → X} (hf : Continuous f) :
    ListPathContinuous n (fun y : Y => tsPath (f y)) := by
  constructor
  · intro y
    exact hts.1 (f y)
  · intro i
    exact (hts.2 i).comp hf

theorem append_singleton {X : Type*} [TopologicalSpace X]
    {n : Nat} {tsPath : X → List ℝ}
    (hts : ListPathContinuous n tsPath)
    {tPath : X → ℝ} (ht : Continuous tPath) :
    ListPathContinuous (n + 1) (fun x : X => tsPath x ++ [tPath x]) := by
  constructor
  · intro x
    simp [hts.1 x]
  · intro i
    by_cases hi : i < n
    · have hfun :
          (fun x : X => (tsPath x ++ [tPath x]).getD i 0) =
            fun x : X => (tsPath x).getD i 0 := by
        funext x
        rw [List.getD_append]
        rwa [hts.1 x]
      rw [hfun]
      exact hts.2 i
    · by_cases hin : i = n
      · subst i
        have hfun :
            (fun x : X => (tsPath x ++ [tPath x]).getD n 0) =
              tPath := by
          funext x
          rw [List.getD_append_right]
          · rw [hts.1 x]
            simp
          · rw [hts.1 x]
        rw [hfun]
        exact ht
      · have hni : n ≤ i := Nat.le_of_not_gt hi
        have hnlt : n < i := lt_of_le_of_ne hni (Ne.symm hin)
        have hs : n + 1 ≤ i := Nat.succ_le_of_lt hnlt
        have hfun :
            (fun x : X => (tsPath x ++ [tPath x]).getD i 0) =
              fun _ : X => 0 := by
          funext x
          exact List.getD_eq_default (l := tsPath x ++ [tPath x])
            (d := 0) (n := i) (by
              simpa [hts.1 x] using hs)
        rw [hfun]
        exact continuous_const

end ListPathContinuous

theorem constantConfig_contDiff :
    ContDiff ℝ (∞ : WithTop ℕ∞) (constantConfig (V := V)) := by
  rw [contDiff_pi]
  intro e
  simpa [constantConfig] using!
    (contDiff_id : ContDiff ℝ (∞ : WithTop ℕ∞) (id : ℝ → ℝ))

theorem constantConfig_continuous :
    Continuous (constantConfig (V := V)) :=
  constantConfig_contDiff.continuous

theorem updateCoord_contDiff (x : Edge V → ℝ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (updateCoord x e) := by
  simpa [updateCoord] using!
    (contDiff_update (𝕜 := ℝ) (k := (∞ : WithTop ℕ∞)) x e)

namespace Forest.EdgeExtension

variable {F F' : Forest V} {e : Edge V}

theorem extendParam_continuous (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) :
    Continuous (fun t : ℝ => h.extendParam u t) := by
  apply continuous_pi
  intro e'
  by_cases he' : e'.val = e
  · have hfun :
        (fun t : ℝ => h.extendParam u t e') = id := by
      funext t
      rw [extendParam, dif_pos he']
      rfl
    rw [hfun]
    exact continuous_id
  · have hfun :
        (fun t : ℝ => h.extendParam u t e') =
          fun _ : ℝ => u ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩ := by
      funext t
      rw [extendParam, dif_neg he']
    rw [hfun]
    exact continuous_const

theorem extendParam_continuous_comp
    {X : Type*} [TopologicalSpace X] (h : EdgeExtension F F' e)
    {uPath : X → F.EdgeParam → ℝ} (hu : Continuous uPath)
    {tPath : X → ℝ} (ht : Continuous tPath) :
    Continuous (fun x : X => h.extendParam (uPath x) (tPath x)) := by
  apply continuous_pi
  intro e'
  by_cases he' : e'.val = e
  · have hfun :
        (fun x : X => h.extendParam (uPath x) (tPath x) e') =
          tPath := by
      funext x
      rw [extendParam, dif_pos he']
    rw [hfun]
    exact ht
  · have hfun :
        (fun x : X => h.extendParam (uPath x) (tPath x) e') =
          fun x : X =>
            uPath x ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩ := by
      funext x
      rw [extendParam, dif_neg he']
    rw [hfun]
    exact
      (continuous_apply
        ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩).comp hu

end Forest.EdgeExtension

namespace Forest

variable (F : Forest V)

theorem interpWithFill_contDiff (u : F.EdgeParam → ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (F.interpWithFill u) := by
  rw [contDiff_pi]
  intro e
  by_cases h : F.inSameComponent e.left e.right
  · have hfun :
        (fun t : ℝ => F.interpWithFill u t e) =
          fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right h) := by
      funext t
      rw [interpWithFill, dif_pos h]
    rw [hfun]
    exact contDiff_const
  · have hfun :
        (fun t : ℝ => F.interpWithFill u t e) = id := by
      funext t
      rw [interpWithFill, dif_neg h]
      rfl
    rw [hfun]
    exact contDiff_id

theorem interpWithFill_continuous (u : F.EdgeParam → ℝ) :
    Continuous (F.interpWithFill u) :=
  (F.interpWithFill_contDiff u).continuous

theorem paramValue_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (e : Edge V) :
    Continuous (fun x : X => F.paramValue (uPath x) e) := by
  by_cases he : e ∈ F.edges
  · have hfun :
        (fun x : X => F.paramValue (uPath x) e) =
          fun x : X => uPath x ⟨e, he⟩ := by
      funext x
      rw [paramValue_of_mem F (uPath x) he]
    rw [hfun]
    exact (continuous_apply ⟨e, he⟩).comp hu
  · have hfun :
        (fun x : X => F.paramValue (uPath x) e) =
          fun _ : X => (1 : ℝ) := by
      funext x
      rw [paramValue, dif_neg he]
    rw [hfun]
    exact continuous_const

theorem pathMinAux_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) {aPath : X → ℝ} (ha : Continuous aPath)
    (γ : List (Edge V)) :
    Continuous (fun x : X => F.pathMinAux (uPath x) (aPath x) γ) := by
  induction γ generalizing aPath with
  | nil =>
      simpa [pathMinAux] using ha
  | cons e γ ih =>
      have hmin :
          Continuous
            (fun x : X => min (aPath x) (F.paramValue (uPath x) e)) :=
        ha.min (F.paramValue_continuous_comp hu e)
      simpa [pathMinAux] using
        ih (aPath := fun x : X => min (aPath x) (F.paramValue (uPath x) e))
          hmin

theorem pathMin_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (γ : List (Edge V)) :
    Continuous (fun x : X => F.pathMin (uPath x) γ) := by
  cases γ with
  | nil =>
      simpa [pathMin] using (continuous_const : Continuous (fun _ : X => (1 : ℝ)))
  | cons e γ =>
      simpa [pathMin] using
        F.pathMinAux_continuous_comp hu
          (F.paramValue_continuous_comp hu e) γ

theorem standardInterp_continuous_comp
    {X : Type*} [TopologicalSpace X] {uPath : X → F.EdgeParam → ℝ}
    (hu : Continuous uPath) :
    Continuous (fun x : X => F.standardInterp (uPath x)) := by
  apply continuous_pi
  intro e
  by_cases h : F.inSameComponent e.left e.right
  · have hfun :
        (fun x : X => F.standardInterp (uPath x) e) =
          fun x : X => F.pathMin (uPath x) (F.pathInF e.left e.right h) := by
      funext x
      rw [standardInterp, dif_pos h]
    rw [hfun]
    exact F.pathMin_continuous_comp hu (F.pathInF e.left e.right h)
  · have hfun :
        (fun x : X => F.standardInterp (uPath x) e) =
          fun _ : X => (0 : ℝ) := by
      funext x
      rw [standardInterp, dif_neg h]
    rw [hfun]
    exact continuous_const

end Forest

theorem BKARContDiff.comp_updateCoord
    {ρ : (Edge V → ℝ) → ℝ} (hρ : BKARContDiff ρ)
    (x : Edge V → ℝ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => ρ (updateCoord x e t)) :=
  hρ.contDiff.comp (updateCoord_contDiff x e)

theorem BKARContDiff.continuous_comp_updateCoord
    {ρ : (Edge V → ℝ) → ℝ} (hρ : BKARContDiff ρ)
    (x : Edge V → ℝ) (e : Edge V) :
    Continuous (fun t : ℝ => ρ (updateCoord x e t)) :=
  (hρ.comp_updateCoord x e).continuous

theorem BKARContDiff.intervalIntegrable_comp_updateCoord
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (x : Edge V → ℝ) (e : Edge V)
    (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ρ (updateCoord x e t))
      MeasureTheory.volume a b :=
  (hρ.continuous_comp_updateCoord x e).intervalIntegrable a b

theorem BKARContDiff.mixedPartialList_interpWithFill_continuous
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    Continuous
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t)) :=
  hρ.mixedPartialList_continuous_comp es (F.interpWithFill_continuous u)

theorem BKARContDiff.mixedPartialList_interpWithFill_intervalIntegrable
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) (u : F.EdgeParam → ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_intervalIntegrable_comp es
    (F.interpWithFill_continuous u) a b

theorem BKARContDiff.mixedPartialList_standardInterp_intervalIntegrable
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) {uPath : ℝ → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.standardInterp (uPath t)))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_intervalIntegrable_comp es
    (F.standardInterp_continuous_comp hu) a b

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
