/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.BanachSpace
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# The global parabolic `C^{2+α,1+α/2}` Banach space

The higher parabolic predicates record genuine derivative witnesses, but an
operator-theoretic Schauder argument also needs a complete normed carrier.
This file constructs that carrier on the full coordinate space.

An element is a quadruple `(u, Dₓu, Dₓ²u, ∂ₜu)` in four already-complete
parabolic `C^{0,α}` Banach spaces, subject to the three genuine derivative
relations.  The derivative graph is closed: convergence in the `C^{0,α}`
norm implies uniform convergence, so the standard uniform-limit theorem for
derivatives passes all three relations to the limit.  The resulting closed
submodule is therefore a genuine Banach space.

This construction makes no regularity assumption disappear into a typeclass:
the spatial first derivative, spatial second derivative, and time derivative
are all exposed by bounded coordinate projections, and their defining
calculus identities are theorems about every element of the space.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ParabolicC0AlphaBanach

/-- The canonical everywhere-defined representative selected for a parabolic
Hölder Banach class. -/
def representative {α : ℝ} {s : Set (ℝ × X)}
    (f : ParabolicC0AlphaBanach X E α s) : ℝ × X → E :=
  ParabolicC0AlphaSpace.toFun (outL f)

/-- Evaluation of a Banach class agrees with its canonical representative at
every point of the defining domain. -/
theorem evalCLM_eq_representative {α : ℝ} {s : Set (ℝ × X)}
    (f : ParabolicC0AlphaBanach X E α s) (z : ℝ × X) (hz : z ∈ s) :
    evalCLM z hz f = representative f z := by
  rw [representative, ← evalCLM_mk_apply z hz (outL f), mk_outL]

/-- On the defining domain, the canonical representative of the class of a
carrier is the original carrier function. -/
theorem representative_mk_eq {α : ℝ} {s : Set (ℝ × X)}
    (f : ParabolicC0AlphaSpace X E α s) (z : ℝ × X) (hz : z ∈ s) :
    representative (mk f) z = ParabolicC0AlphaSpace.toFun f z := by
  rw [← evalCLM_eq_representative (mk f) z hz, evalCLM_mk_apply]

@[simp] theorem representative_zero {α : ℝ} {s : Set (ℝ × X)} (z : ℝ × X) :
    representative (0 : ParabolicC0AlphaBanach X E α s) z = 0 := by
  change ParabolicC0AlphaSpace.toFun (outL (0 : ParabolicC0AlphaBanach X E α s)) z = 0
  rw [map_zero]
  rfl

@[simp] theorem representative_add {α : ℝ} {s : Set (ℝ × X)}
    (f g : ParabolicC0AlphaBanach X E α s) (z : ℝ × X) :
    representative (f + g) z = representative f z + representative g z := by
  change ParabolicC0AlphaSpace.toFun (outL (f + g)) z =
    ParabolicC0AlphaSpace.toFun (outL f) z + ParabolicC0AlphaSpace.toFun (outL g) z
  rw [map_add]
  rfl

@[simp] theorem representative_smul {α : ℝ} {s : Set (ℝ × X)}
    (c : ℝ) (f : ParabolicC0AlphaBanach X E α s) (z : ℝ × X) :
    representative (c • f) z = c • representative f z := by
  change ParabolicC0AlphaSpace.toFun (outL (c • f)) z =
    c • ParabolicC0AlphaSpace.toFun (outL f) z
  rw [map_smul]
  rfl

/-- Norm convergence in the parabolic `C^{0,α}` Banach space implies
uniform convergence of all point evaluations on the defining domain. -/
theorem tendstoUniformly_eval_of_tendsto
    {ι : Type*} {l : Filter ι}
    {α : ℝ} {s : Set (ℝ × X)}
    {F : ι → ParabolicC0AlphaBanach X E α s}
    {f : ParabolicC0AlphaBanach X E α s}
    (hF : Tendsto F l (𝓝 f)) :
    TendstoUniformlyOn
      (fun i => representative (F i))
      (representative f) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hF ε hε)] with i hi
  intro z hz
  have heval := ParabolicC0AlphaSpace.norm_evalCLM_apply_le z hz
    (outL (F i) - outL f)
  calc
    dist (representative f z) (representative (F i) z)
        = ‖ParabolicC0AlphaSpace.evalCLM z hz (outL (F i) - outL f)‖ := by
          rw [dist_comm, map_sub, dist_eq_norm]
          rfl
    _ ≤ ‖outL (F i) - outL f‖ := heval
    _ = ‖outL (F i - f)‖ := by rw [map_sub]
    _ = ‖F i - f‖ := norm_outL (F i - f)
    _ = dist (F i) f := by rw [dist_eq_norm]
    _ < ε := hi

/-- On the full coordinate space, norm convergence gives uniform convergence
without a domain restriction. -/
theorem tendstoUniformly_eval_univ_of_tendsto
    {ι : Type*} {l : Filter ι} {α : ℝ}
    {F : ι → ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))}
    {f : ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))}
    (hF : Tendsto F l (𝓝 f)) :
    TendstoUniformly
      (fun i => representative (F i))
      (representative f) l := by
  rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformly_eval_of_tendsto (X := X) (E := E) hF

end ParabolicC0AlphaBanach

-- Use the normed-space projections as the low-level algebra/topology
-- instances for operator-valued derivatives.  This keeps the instances in
-- `HasFDerivAt` identical to those used by the Hölder Banach components.
@[reducible] local instance higherBanachFirstAddCommGroup : AddCommGroup (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup.toAddCommGroup
@[reducible] local instance higherBanachFirstModule : Module ℝ (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace.toModule
@[reducible] local instance higherBanachFirstTopologicalSpace : TopologicalSpace (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Ambient product of the value, first spatial derivative, second spatial
derivative, and time derivative `C^{0,α}` Banach spaces. -/
abbrev GlobalParabolicC2AlphaAmbient (X E : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :=
  ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) ×
    ParabolicC0AlphaBanach X (X →L[ℝ] E) α (Set.univ : Set (ℝ × X)) ×
      ParabolicC0AlphaBanach X (X →L[ℝ] X →L[ℝ] E) α (Set.univ : Set (ℝ × X)) ×
        ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X))

namespace GlobalParabolicC2AlphaAmbient

variable {α : ℝ}

/-- Value component evaluated at a space-time point. -/
def value (q : GlobalParabolicC2AlphaAmbient X E α) (z : ℝ × X) : E :=
  ParabolicC0AlphaBanach.representative q.1 z

/-- First-spatial-derivative component evaluated at a space-time point. -/
def spaceDeriv (q : GlobalParabolicC2AlphaAmbient X E α) (z : ℝ × X) : X →L[ℝ] E :=
  ParabolicC0AlphaBanach.representative q.2.1 z

/-- Second-spatial-derivative component evaluated at a space-time point. -/
def spaceSecondDeriv (q : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : X →L[ℝ] X →L[ℝ] E :=
  ParabolicC0AlphaBanach.representative q.2.2.1 z

/-- Time-derivative component evaluated at a space-time point. -/
def timeDeriv (q : GlobalParabolicC2AlphaAmbient X E α) (z : ℝ × X) : E :=
  ParabolicC0AlphaBanach.representative q.2.2.2 z

@[simp] theorem value_zero (z : ℝ × X) :
    value (0 : GlobalParabolicC2AlphaAmbient X E α) z = 0 := by
  simp [value]

@[simp] theorem value_add (q r : GlobalParabolicC2AlphaAmbient X E α) (z : ℝ × X) :
    value (q + r) z = value q z + value r z := by
  simp [value]

@[simp] theorem value_smul (c : ℝ) (q : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : value (c • q) z = c • value q z := by
  simp [value]

@[simp] theorem spaceDeriv_zero (z : ℝ × X) :
    spaceDeriv (0 : GlobalParabolicC2AlphaAmbient X E α) z = 0 := by
  simp [spaceDeriv]

@[simp] theorem spaceDeriv_add (q r : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : spaceDeriv (q + r) z = spaceDeriv q z + spaceDeriv r z := by
  simp [spaceDeriv]

@[simp] theorem spaceDeriv_smul (c : ℝ) (q : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : spaceDeriv (c • q) z = c • spaceDeriv q z := by
  simp [spaceDeriv]

@[simp] theorem spaceSecondDeriv_zero (z : ℝ × X) :
    spaceSecondDeriv (0 : GlobalParabolicC2AlphaAmbient X E α) z = 0 := by
  simp [spaceSecondDeriv]

@[simp] theorem spaceSecondDeriv_add (q r : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) :
    spaceSecondDeriv (q + r) z = spaceSecondDeriv q z + spaceSecondDeriv r z := by
  simp [spaceSecondDeriv]

@[simp] theorem spaceSecondDeriv_smul (c : ℝ)
    (q : GlobalParabolicC2AlphaAmbient X E α) (z : ℝ × X) :
    spaceSecondDeriv (c • q) z = c • spaceSecondDeriv q z := by
  simp [spaceSecondDeriv]

@[simp] theorem timeDeriv_zero (z : ℝ × X) :
    timeDeriv (0 : GlobalParabolicC2AlphaAmbient X E α) z = 0 := by
  simp [timeDeriv]

@[simp] theorem timeDeriv_add (q r : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : timeDeriv (q + r) z = timeDeriv q z + timeDeriv r z := by
  simp [timeDeriv]

@[simp] theorem timeDeriv_smul (c : ℝ) (q : GlobalParabolicC2AlphaAmbient X E α)
    (z : ℝ × X) : timeDeriv (c • q) z = c • timeDeriv q z := by
  simp [timeDeriv]

/-- The three genuine calculus relations defining a global parabolic second
jet. -/
structure IsCompatible (q : GlobalParabolicC2AlphaAmbient X E α) : Prop where
  hasSpaceDeriv : ∀ z : ℝ × X,
    HasFDerivAt (fun x : X => value q (z.1, x)) (spaceDeriv q z) z.2
  hasSpaceSecondDeriv : ∀ z : ℝ × X,
    HasFDerivAt (fun x : X => spaceDeriv q (z.1, x))
      (spaceSecondDeriv q z) z.2
  hasTimeDeriv : ∀ z : ℝ × X,
    HasDerivAt (fun t : ℝ => value q (t, z.2)) (timeDeriv q z) z.1

/-- Compatible global parabolic second jets form a linear subspace of the
four-component ambient Banach space. -/
def compatibleSubmodule : Submodule ℝ (GlobalParabolicC2AlphaAmbient X E α) where
  carrier := {q | IsCompatible q}
  zero_mem' := by
    constructor
    · intro z
      simpa using hasFDerivAt_const (x := z.2) (c := (0 : E))
    · intro z
      simpa using hasFDerivAt_const (x := z.2) (c := (0 : X →L[ℝ] E))
    · intro z
      simpa using hasDerivAt_const (x := z.1) (c := (0 : E))
  add_mem' := by
    intro q r hq hr
    constructor
    · intro z
      convert (hq.hasSpaceDeriv z).add (hr.hasSpaceDeriv z) using 1 <;> try rfl
      · funext x
        exact value_add q r (z.1, x)
      · exact spaceDeriv_add q r z
    · intro z
      convert (hq.hasSpaceSecondDeriv z).add (hr.hasSpaceSecondDeriv z) using 1 <;> try rfl
      · funext x
        exact spaceDeriv_add q r (z.1, x)
      · exact spaceSecondDeriv_add q r z
    · intro z
      convert (hq.hasTimeDeriv z).add (hr.hasTimeDeriv z) using 1 <;> try rfl
      · funext t
        exact value_add q r (t, z.2)
      · exact timeDeriv_add q r z
  smul_mem' := by
    intro c q hq
    constructor
    · intro z
      convert (hq.hasSpaceDeriv z).fun_const_smul c using 1 <;> try rfl
      · funext x
        exact value_smul c q (z.1, x)
      · exact spaceDeriv_smul c q z
    · intro z
      convert (hq.hasSpaceSecondDeriv z).fun_const_smul c using 1 <;> try rfl
      · funext x
        exact spaceDeriv_smul c q (z.1, x)
      · exact spaceSecondDeriv_smul c q z
    · intro z
      convert HasDerivAt.fun_const_smul c (hq.hasTimeDeriv z) using 1 <;> try rfl
      · funext t
        exact value_smul c q (t, z.2)
      · exact timeDeriv_smul c q z

/-- Uniform convergence of value components under ambient convergence. -/
theorem tendstoUniformly_value_of_tendsto
    {ι : Type*} {l : Filter ι}
    {F : ι → GlobalParabolicC2AlphaAmbient X E α}
    {q : GlobalParabolicC2AlphaAmbient X E α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformly (fun i => value (F i)) (value q) l := by
  have hcomp : Tendsto (fun i => (F i).1) l (𝓝 q.1) :=
    by
      change Tendsto (Prod.fst ∘ F) l (𝓝 q.1)
      exact Filter.Tendsto.comp continuousAt_fst hF
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_univ_of_tendsto
    (X := X) (E := E) hcomp

/-- Uniform convergence of first-spatial-derivative components under ambient
convergence. -/
theorem tendstoUniformly_spaceDeriv_of_tendsto
    {ι : Type*} {l : Filter ι}
    {F : ι → GlobalParabolicC2AlphaAmbient X E α}
    {q : GlobalParabolicC2AlphaAmbient X E α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformly (fun i => spaceDeriv (F i)) (spaceDeriv q) l := by
  have hcomp : Tendsto (fun i => (F i).2.1) l (𝓝 q.2.1) :=
    by
      have hsnd : Tendsto (fun i => (F i).2) l (𝓝 q.2) := by
        change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
        exact Filter.Tendsto.comp continuousAt_snd hF
      change Tendsto (Prod.fst ∘ fun i => (F i).2) l (𝓝 q.2.1)
      exact Filter.Tendsto.comp continuousAt_fst hsnd
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_univ_of_tendsto
    (X := X) (E := X →L[ℝ] E) hcomp

/-- Uniform convergence of second-spatial-derivative components under ambient
convergence. -/
theorem tendstoUniformly_spaceSecondDeriv_of_tendsto
    {ι : Type*} {l : Filter ι}
    {F : ι → GlobalParabolicC2AlphaAmbient X E α}
    {q : GlobalParabolicC2AlphaAmbient X E α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformly (fun i => spaceSecondDeriv (F i))
      (spaceSecondDeriv q) l := by
  have hcomp : Tendsto (fun i => (F i).2.2.1) l (𝓝 q.2.2.1) :=
    by
      have hsnd : Tendsto (fun i => (F i).2) l (𝓝 q.2) := by
        change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
        exact Filter.Tendsto.comp continuousAt_snd hF
      have hsnd2 : Tendsto (fun i => (F i).2.2) l (𝓝 q.2.2) := by
        change Tendsto (Prod.snd ∘ fun i => (F i).2) l (𝓝 q.2.2)
        exact Filter.Tendsto.comp continuousAt_snd hsnd
      change Tendsto (Prod.fst ∘ fun i => (F i).2.2) l (𝓝 q.2.2.1)
      exact Filter.Tendsto.comp continuousAt_fst hsnd2
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_univ_of_tendsto
    (X := X) (E := X →L[ℝ] X →L[ℝ] E) hcomp

/-- Uniform convergence of time-derivative components under ambient
convergence. -/
theorem tendstoUniformly_timeDeriv_of_tendsto
    {ι : Type*} {l : Filter ι}
    {F : ι → GlobalParabolicC2AlphaAmbient X E α}
    {q : GlobalParabolicC2AlphaAmbient X E α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformly (fun i => timeDeriv (F i)) (timeDeriv q) l := by
  have hcomp : Tendsto (fun i => (F i).2.2.2) l (𝓝 q.2.2.2) :=
    by
      have hsnd : Tendsto (fun i => (F i).2) l (𝓝 q.2) := by
        change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
        exact Filter.Tendsto.comp continuousAt_snd hF
      have hsnd2 : Tendsto (fun i => (F i).2.2) l (𝓝 q.2.2) := by
        change Tendsto (Prod.snd ∘ fun i => (F i).2) l (𝓝 q.2.2)
        exact Filter.Tendsto.comp continuousAt_snd hsnd
      change Tendsto (Prod.snd ∘ fun i => (F i).2.2) l (𝓝 q.2.2.2)
      exact Filter.Tendsto.comp continuousAt_snd hsnd2
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_univ_of_tendsto
    (X := X) (E := E) hcomp

/-- The genuine derivative-compatibility submodule is closed. -/
theorem isClosed_compatibleSubmodule :
    IsClosed (compatibleSubmodule (X := X) (E := E) (α := α) :
      Set (GlobalParabolicC2AlphaAmbient X E α)) := by
  rw [isClosed_iff_clusterPt]
  intro q hq
  let l : Filter (GlobalParabolicC2AlphaAmbient X E α) :=
    𝓝 q ⊓ 𝓟 (compatibleSubmodule (X := X) (E := E) (α := α) :
      Set (GlobalParabolicC2AlphaAmbient X E α))
  haveI : NeBot l := hq
  have htend_id : Tendsto id l (𝓝 q) := inf_le_left
  have hmem : ∀ᶠ r in l,
      r ∈ compatibleSubmodule (X := X) (E := E) (α := α) := by
    exact (Filter.le_def.mp inf_le_right) _ (mem_principal_self _)
  classical
  let F : GlobalParabolicC2AlphaAmbient X E α →
      GlobalParabolicC2AlphaAmbient X E α := fun r =>
    if hr : r ∈ compatibleSubmodule (X := X) (E := E) (α := α) then r else 0
  have hF_eq : F =ᶠ[l] id := hmem.mono fun r hr => by simp [F, hr]
  have htend : Tendsto F l (𝓝 q) := htend_id.congr' hF_eq.symm
  have hF_mem : ∀ r,
      F r ∈ compatibleSubmodule (X := X) (E := E) (α := α) := by
    intro r
    by_cases hr : r ∈ compatibleSubmodule (X := X) (E := E) (α := α)
    · simpa [F, hr]
    · simp [F, hr]
  constructor
  · intro z
    have huniform := (tendstoUniformly_spaceDeriv_of_tendsto htend).comp
      (fun x : X => (z.1, x))
    exact hasFDerivAt_of_tendstoUniformly
      (l := l)
      (f := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        fun x : X => value (F r) (z.1, x))
      (g := fun x : X => value q (z.1, x))
      (f' := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        spaceDeriv (F r) ∘ fun x : X => (z.1, x))
      (g' := spaceDeriv q ∘ fun x : X => (z.1, x))
      huniform
      (fun r x => (hF_mem r).hasSpaceDeriv (z.1, x))
      (fun x => (tendstoUniformly_value_of_tendsto htend).tendsto_at (z.1, x))
      z.2
  · intro z
    have huniform := (tendstoUniformly_spaceSecondDeriv_of_tendsto htend).comp
      (fun x : X => (z.1, x))
    exact hasFDerivAt_of_tendstoUniformly
      (l := l)
      (f := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        fun x : X => spaceDeriv (F r) (z.1, x))
      (g := fun x : X => spaceDeriv q (z.1, x))
      (f' := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        spaceSecondDeriv (F r) ∘ fun x : X => (z.1, x))
      (g' := spaceSecondDeriv q ∘ fun x : X => (z.1, x))
      huniform
      (fun r x => (hF_mem r).hasSpaceSecondDeriv (z.1, x))
      (fun x => (tendstoUniformly_spaceDeriv_of_tendsto htend).tendsto_at (z.1, x))
      z.2
  · intro z
    have huniform := (tendstoUniformly_timeDeriv_of_tendsto htend).comp
      (fun t : ℝ => (t, z.2))
    exact hasDerivAt_of_tendstoUniformly
      (l := l)
      (f := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        fun t : ℝ => value (F r) (t, z.2))
      (g := fun t : ℝ => value q (t, z.2))
      (f' := fun r : GlobalParabolicC2AlphaAmbient X E α =>
        timeDeriv (F r) ∘ fun t : ℝ => (t, z.2))
      (g' := timeDeriv q ∘ fun t : ℝ => (t, z.2))
      huniform
      (Filter.Eventually.of_forall fun r t => (hF_mem r).hasTimeDeriv (t, z.2))
      (fun t => (tendstoUniformly_value_of_tendsto htend).tendsto_at (t, z.2))
      z.1

end GlobalParabolicC2AlphaAmbient

/-- The genuine global coordinate `C^{2+α,1+α/2}` Banach space: the closed
submodule of compatible `(u, Dₓu, Dₓ²u, ∂ₜu)` quadruples. -/
def GlobalParabolicC2AlphaBanach (X E : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :=
  GlobalParabolicC2AlphaAmbient.compatibleSubmodule (X := X) (E := E) (α := α)

namespace GlobalParabolicC2AlphaBanach

variable {α : ℝ}

instance [CompleteSpace E] : CompleteSpace (GlobalParabolicC2AlphaBanach X E α) :=
  GlobalParabolicC2AlphaAmbient.isClosed_compatibleSubmodule.completeSpace_coe

/-- The underlying higher field. -/
def value (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) : E :=
  GlobalParabolicC2AlphaAmbient.value u.1 z

/-- Its genuine first spatial derivative. -/
def spaceDeriv (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) : X →L[ℝ] E :=
  GlobalParabolicC2AlphaAmbient.spaceDeriv u.1 z

/-- Its genuine second spatial derivative. -/
def spaceSecondDeriv (u : GlobalParabolicC2AlphaBanach X E α)
    (z : ℝ × X) : X →L[ℝ] X →L[ℝ] E :=
  GlobalParabolicC2AlphaAmbient.spaceSecondDeriv u.1 z

/-- Its genuine time derivative. -/
def timeDeriv (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) : E :=
  GlobalParabolicC2AlphaAmbient.timeDeriv u.1 z

/-- Every element carries its advertised first spatial derivative. -/
theorem hasFDerivAt_space (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    HasFDerivAt (fun x : X => value u (z.1, x)) (spaceDeriv u z) z.2 :=
  u.2.hasSpaceDeriv z

/-- Every element carries its advertised second spatial derivative. -/
theorem hasFDerivAt_spaceDeriv (u : GlobalParabolicC2AlphaBanach X E α)
    (z : ℝ × X) :
    HasFDerivAt (fun x : X => spaceDeriv u (z.1, x))
      (spaceSecondDeriv u z) z.2 :=
  u.2.hasSpaceSecondDeriv z

/-- Every element carries its advertised time derivative. -/
theorem hasDerivAt_time (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    HasDerivAt (fun t : ℝ => value u (t, z.2)) (timeDeriv u z) z.1 :=
  u.2.hasTimeDeriv z

/-- Bounded projection to the `C^{0,α}` value component. -/
def valueComponentL :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    (GlobalParabolicC2AlphaAmbient.compatibleSubmodule
      (X := X) (E := E) (α := α)).subtypeL

/-- Bounded projection to the `C^{0,α}` first-spatial-derivative
component. -/
def spaceDerivComponentL :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X (X →L[ℝ] E) α (Set.univ : Set (ℝ × X)) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      (GlobalParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (α := α)).subtypeL)

/-- Bounded projection to the `C^{0,α}` second-spatial-derivative
component. -/
def spaceSecondDerivComponentL :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X (X →L[ℝ] X →L[ℝ] E) α
        (Set.univ : Set (ℝ × X)) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (GlobalParabolicC2AlphaAmbient.compatibleSubmodule
          (X := X) (E := E) (α := α)).subtypeL))

/-- Bounded projection to the `C^{0,α}` time-derivative component. -/
def timeDerivComponentL :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (GlobalParabolicC2AlphaAmbient.compatibleSubmodule
          (X := X) (E := E) (α := α)).subtypeL))

@[simp] theorem valueComponentL_apply
    (u : GlobalParabolicC2AlphaBanach X E α) : valueComponentL u = u.1.1 :=
  rfl

@[simp] theorem spaceDerivComponentL_apply
    (u : GlobalParabolicC2AlphaBanach X E α) :
    spaceDerivComponentL u = u.1.2.1 :=
  rfl

@[simp] theorem spaceSecondDerivComponentL_apply
    (u : GlobalParabolicC2AlphaBanach X E α) :
    spaceSecondDerivComponentL u = u.1.2.2.1 :=
  rfl

@[simp] theorem timeDerivComponentL_apply
    (u : GlobalParabolicC2AlphaBanach X E α) : timeDerivComponentL u = u.1.2.2.2 :=
  rfl

@[simp] theorem representative_valueComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) :
    ParabolicC0AlphaBanach.representative (valueComponentL u) = value u :=
  rfl

@[simp] theorem representative_spaceDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) :
    ParabolicC0AlphaBanach.representative (spaceDerivComponentL u) = spaceDeriv u :=
  rfl

@[simp] theorem representative_spaceSecondDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) :
    ParabolicC0AlphaBanach.representative (spaceSecondDerivComponentL u) =
      spaceSecondDeriv u :=
  rfl

@[simp] theorem representative_timeDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) :
    ParabolicC0AlphaBanach.representative (timeDerivComponentL u) = timeDeriv u :=
  rfl

@[simp] theorem evalCLM_valueComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) (valueComponentL u) = value u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    representative_valueComponentL]

@[simp] theorem evalCLM_spaceDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) (spaceDerivComponentL u) =
      spaceDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    representative_spaceDerivComponentL]

@[simp] theorem evalCLM_spaceSecondDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) (spaceSecondDerivComponentL u) =
      spaceSecondDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    representative_spaceSecondDerivComponentL]

@[simp] theorem evalCLM_timeDerivComponentL
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) (timeDerivComponentL u) =
      timeDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    representative_timeDerivComponentL]

end GlobalParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
