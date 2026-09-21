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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherBanachSpace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpaceCore
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The parabolic `C^{2+α,1+α/2}` Banach space on a finite cylinder

For the Cauchy problem the relevant norm is taken on `(t₀,T] × X`, while
the classical time derivative is required on the open time interval
`(t₀,T)`.  Spatial derivatives remain genuine full Fréchet derivatives at
every time in `(t₀,T]`.  This file constructs the resulting space as a
closed derivative graph inside four parabolic `C^{0,α}` Banach spaces.

The distinction between the normed cylinder and its time interior is
essential: it gives a complete carrier without postulating a derivative at
the initial time, exactly matching the classical parabolic initial-value
problem.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance finiteCylinderFirstAddCommGroup :
    AddCommGroup (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup.toAddCommGroup
@[reducible] local instance finiteCylinderFirstModule :
    Module ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace.toModule
@[reducible] local instance finiteCylinderFirstTopologicalSpace :
    TopologicalSpace (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The positive-time finite cylinder `(t₀,T] × X`. -/
def parabolicFiniteCylinder (X : Type*) (t₀ T : ℝ) : Set (ℝ × X) :=
  Set.Ioc t₀ T ×ˢ Set.univ

@[simp] theorem mem_parabolicFiniteCylinder {t₀ T : ℝ} {z : ℝ × X} :
    z ∈ parabolicFiniteCylinder X t₀ T ↔ t₀ < z.1 ∧ z.1 ≤ T := by
  simp [parabolicFiniteCylinder]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Monotonicity of finite cylinders in their terminal time. -/
theorem parabolicFiniteCylinder_mono {t₀ S T : ℝ} (hST : S ≤ T) :
    parabolicFiniteCylinder X t₀ S ⊆ parabolicFiniteCylinder X t₀ T := by
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans hST⟩, hz.2⟩

/-- Time slices of the finite cylinder have unique derivatives. -/
theorem uniqueDiffWithinAt_timeSlice_parabolicFiniteCylinder
    {t₀ T : ℝ} {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    UniqueDiffWithinAt ℝ (timeSliceDomain (parabolicFiniteCylinder X t₀ T) z.2) z.1 := by
  have hzIoc : z.1 ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  have hslice : timeSliceDomain (parabolicFiniteCylinder X t₀ T) z.2 =
      Set.Ioc t₀ T := by
    ext s
    simp [timeSliceDomain, parabolicFiniteCylinder]
  rw [hslice]
  exact uniqueDiffOn_Ioc t₀ T z.1 hzIoc

/-- Spatial slices of the finite cylinder are the whole coordinate space and
therefore have unique Fréchet derivatives. -/
theorem uniqueDiffWithinAt_spaceSlice_parabolicFiniteCylinder
    {t₀ T : ℝ} {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    UniqueDiffWithinAt ℝ (spaceSliceDomain (parabolicFiniteCylinder X t₀ T) z.1) z.2 := by
  have ht : z.1 ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  have hslice : spaceSliceDomain (parabolicFiniteCylinder X t₀ T) z.1 =
      (Set.univ : Set X) := by
    ext x
    simp [spaceSliceDomain, parabolicFiniteCylinder, ht]
  rw [hslice]
  exact (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set X)) z.2 (Set.mem_univ z.2)

/-- Ambient product of the four `C^{0,α}` components on a finite
cylinder. -/
abbrev FiniteParabolicC2AlphaAmbient (X E : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t₀ T α : ℝ) :=
  ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) ×
    ParabolicC0AlphaBanach X (X →L[ℝ] E) α (parabolicFiniteCylinder X t₀ T) ×
      ParabolicC0AlphaBanach X (X →L[ℝ] X →L[ℝ] E) α
          (parabolicFiniteCylinder X t₀ T) ×
        ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T)

namespace FiniteParabolicC2AlphaAmbient

variable {t₀ T α : ℝ}

def value (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) : E :=
  ParabolicC0AlphaBanach.representative q.1 z

def spaceDeriv (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) : X →L[ℝ] E :=
  ParabolicC0AlphaBanach.representative q.2.1 z

def spaceSecondDeriv (q : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) : X →L[ℝ] X →L[ℝ] E :=
  ParabolicC0AlphaBanach.representative q.2.2.1 z

def timeDeriv (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) : E :=
  ParabolicC0AlphaBanach.representative q.2.2.2 z

@[simp] theorem value_zero (z : ℝ × X) :
    value (0 : FiniteParabolicC2AlphaAmbient X E t₀ T α) z = 0 := by
  simp [value]

@[simp] theorem value_add (q r : FiniteParabolicC2AlphaAmbient X E t₀ T α)
    (z : ℝ × X) : value (q + r) z = value q z + value r z := by
  simp [value]

@[simp] theorem value_smul (c : ℝ)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    value (c • q) z = c • value q z := by
  simp [value]

@[simp] theorem spaceDeriv_zero (z : ℝ × X) :
    spaceDeriv (0 : FiniteParabolicC2AlphaAmbient X E t₀ T α) z = 0 := by
  simp [spaceDeriv]

@[simp] theorem spaceDeriv_add
    (q r : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    spaceDeriv (q + r) z = spaceDeriv q z + spaceDeriv r z := by
  simp [spaceDeriv]

@[simp] theorem spaceDeriv_smul (c : ℝ)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    spaceDeriv (c • q) z = c • spaceDeriv q z := by
  simp [spaceDeriv]

@[simp] theorem spaceSecondDeriv_zero (z : ℝ × X) :
    spaceSecondDeriv (0 : FiniteParabolicC2AlphaAmbient X E t₀ T α) z = 0 := by
  simp [spaceSecondDeriv]

@[simp] theorem spaceSecondDeriv_add
    (q r : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    spaceSecondDeriv (q + r) z =
      spaceSecondDeriv q z + spaceSecondDeriv r z := by
  simp [spaceSecondDeriv]

@[simp] theorem spaceSecondDeriv_smul (c : ℝ)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    spaceSecondDeriv (c • q) z = c • spaceSecondDeriv q z := by
  simp [spaceSecondDeriv]

@[simp] theorem timeDeriv_zero (z : ℝ × X) :
    timeDeriv (0 : FiniteParabolicC2AlphaAmbient X E t₀ T α) z = 0 := by
  simp [timeDeriv]

@[simp] theorem timeDeriv_add
    (q r : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    timeDeriv (q + r) z = timeDeriv q z + timeDeriv r z := by
  simp [timeDeriv]

@[simp] theorem timeDeriv_smul (c : ℝ)
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) (z : ℝ × X) :
    timeDeriv (c • q) z = c • timeDeriv q z := by
  simp [timeDeriv]

/-- Genuine calculus compatibility for a finite-cylinder four-jet.  Time
differentiability is imposed precisely on `(t₀,T)`, whereas both spatial
derivatives are imposed for every `t ∈ (t₀,T]`. -/
structure IsCompatible
    (q : FiniteParabolicC2AlphaAmbient X E t₀ T α) : Prop where
  hasSpaceDeriv : ∀ t ∈ Set.Ioc t₀ T, ∀ x : X,
    HasFDerivAt (fun y : X => value q (t, y)) (spaceDeriv q (t, x)) x
  hasSpaceSecondDeriv : ∀ t ∈ Set.Ioc t₀ T, ∀ x : X,
    HasFDerivAt (fun y : X => spaceDeriv q (t, y))
      (spaceSecondDeriv q (t, x)) x
  hasTimeDeriv : ∀ t ∈ Set.Ioo t₀ T, ∀ x : X,
    HasDerivAt (fun s : ℝ => value q (s, x)) (timeDeriv q (t, x)) t

/-- Compatible finite-cylinder jets form a linear subspace. -/
def compatibleSubmodule :
    Submodule ℝ (FiniteParabolicC2AlphaAmbient X E t₀ T α) where
  carrier := {q | IsCompatible q}
  zero_mem' := by
    constructor
    · intro t ht x
      simpa using hasFDerivAt_const (x := x) (c := (0 : E))
    · intro t ht x
      simpa using hasFDerivAt_const (x := x) (c := (0 : X →L[ℝ] E))
    · intro t ht x
      simpa using hasDerivAt_const (x := t) (c := (0 : E))
  add_mem' := by
    intro q r hq hr
    constructor
    · intro t ht x
      convert (hq.hasSpaceDeriv t ht x).add (hr.hasSpaceDeriv t ht x) using 1 <;> try rfl
      · funext y; exact value_add q r (t, y)
      · exact spaceDeriv_add q r (t, x)
    · intro t ht x
      convert (hq.hasSpaceSecondDeriv t ht x).add
        (hr.hasSpaceSecondDeriv t ht x) using 1 <;> try rfl
      · funext y; exact spaceDeriv_add q r (t, y)
      · exact spaceSecondDeriv_add q r (t, x)
    · intro t ht x
      convert (hq.hasTimeDeriv t ht x).add (hr.hasTimeDeriv t ht x) using 1 <;> try rfl
      · funext s; exact value_add q r (s, x)
      · exact timeDeriv_add q r (t, x)
  smul_mem' := by
    intro c q hq
    constructor
    · intro t ht x
      convert (hq.hasSpaceDeriv t ht x).fun_const_smul c using 1 <;> try rfl
      · funext y; exact value_smul c q (t, y)
      · exact spaceDeriv_smul c q (t, x)
    · intro t ht x
      convert (hq.hasSpaceSecondDeriv t ht x).fun_const_smul c using 1 <;> try rfl
      · funext y; exact spaceDeriv_smul c q (t, y)
      · exact spaceSecondDeriv_smul c q (t, x)
    · intro t ht x
      convert HasDerivAt.fun_const_smul c (hq.hasTimeDeriv t ht x) using 1 <;> try rfl
      · funext s; exact value_smul c q (s, x)
      · exact timeDeriv_smul c q (t, x)

theorem tendstoUniformlyOn_value_of_tendsto
    {i : Type*} {l : Filter i}
    {F : i → FiniteParabolicC2AlphaAmbient X E t₀ T α}
    {q : FiniteParabolicC2AlphaAmbient X E t₀ T α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformlyOn (fun k => value (F k)) (value q) l
      (parabolicFiniteCylinder X t₀ T) := by
  have hcomp : Tendsto (fun k => (F k).1) l (𝓝 q.1) := by
    change Tendsto (Prod.fst ∘ F) l (𝓝 q.1)
    exact Filter.Tendsto.comp continuousAt_fst hF
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_of_tendsto
    (X := X) (E := E) hcomp

theorem tendstoUniformlyOn_spaceDeriv_of_tendsto
    {i : Type*} {l : Filter i}
    {F : i → FiniteParabolicC2AlphaAmbient X E t₀ T α}
    {q : FiniteParabolicC2AlphaAmbient X E t₀ T α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformlyOn (fun k => spaceDeriv (F k)) (spaceDeriv q) l
      (parabolicFiniteCylinder X t₀ T) := by
  have hsnd : Tendsto (fun k => (F k).2) l (𝓝 q.2) := by
    change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
    exact Filter.Tendsto.comp continuousAt_snd hF
  have hcomp : Tendsto (fun k => (F k).2.1) l (𝓝 q.2.1) := by
    change Tendsto (Prod.fst ∘ fun k => (F k).2) l (𝓝 q.2.1)
    exact Filter.Tendsto.comp continuousAt_fst hsnd
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_of_tendsto
    (X := X) (E := X →L[ℝ] E) hcomp

theorem tendstoUniformlyOn_spaceSecondDeriv_of_tendsto
    {i : Type*} {l : Filter i}
    {F : i → FiniteParabolicC2AlphaAmbient X E t₀ T α}
    {q : FiniteParabolicC2AlphaAmbient X E t₀ T α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformlyOn (fun k => spaceSecondDeriv (F k))
      (spaceSecondDeriv q) l (parabolicFiniteCylinder X t₀ T) := by
  have hsnd : Tendsto (fun k => (F k).2) l (𝓝 q.2) := by
    change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
    exact Filter.Tendsto.comp continuousAt_snd hF
  have hsnd2 : Tendsto (fun k => (F k).2.2) l (𝓝 q.2.2) := by
    change Tendsto (Prod.snd ∘ fun k => (F k).2) l (𝓝 q.2.2)
    exact Filter.Tendsto.comp continuousAt_snd hsnd
  have hcomp : Tendsto (fun k => (F k).2.2.1) l (𝓝 q.2.2.1) := by
    change Tendsto (Prod.fst ∘ fun k => (F k).2.2) l (𝓝 q.2.2.1)
    exact Filter.Tendsto.comp continuousAt_fst hsnd2
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_of_tendsto
    (X := X) (E := X →L[ℝ] X →L[ℝ] E) hcomp

theorem tendstoUniformlyOn_timeDeriv_of_tendsto
    {i : Type*} {l : Filter i}
    {F : i → FiniteParabolicC2AlphaAmbient X E t₀ T α}
    {q : FiniteParabolicC2AlphaAmbient X E t₀ T α}
    (hF : Tendsto F l (𝓝 q)) :
    TendstoUniformlyOn (fun k => timeDeriv (F k)) (timeDeriv q) l
      (parabolicFiniteCylinder X t₀ T) := by
  have hsnd : Tendsto (fun k => (F k).2) l (𝓝 q.2) := by
    change Tendsto (Prod.snd ∘ F) l (𝓝 q.2)
    exact Filter.Tendsto.comp continuousAt_snd hF
  have hsnd2 : Tendsto (fun k => (F k).2.2) l (𝓝 q.2.2) := by
    change Tendsto (Prod.snd ∘ fun k => (F k).2) l (𝓝 q.2.2)
    exact Filter.Tendsto.comp continuousAt_snd hsnd
  have hcomp : Tendsto (fun k => (F k).2.2.2) l (𝓝 q.2.2.2) := by
    change Tendsto (Prod.snd ∘ fun k => (F k).2.2) l (𝓝 q.2.2.2)
    exact Filter.Tendsto.comp continuousAt_snd hsnd2
  exact ParabolicC0AlphaBanach.tendstoUniformly_eval_of_tendsto
    (X := X) (E := E) hcomp

/-- The finite-cylinder derivative graph is closed. -/
theorem isClosed_compatibleSubmodule :
    IsClosed (compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :
      Set (FiniteParabolicC2AlphaAmbient X E t₀ T α)) := by
  rw [isClosed_iff_clusterPt]
  intro q hq
  let l : Filter (FiniteParabolicC2AlphaAmbient X E t₀ T α) :=
    𝓝 q ⊓ 𝓟 (compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :
      Set (FiniteParabolicC2AlphaAmbient X E t₀ T α))
  haveI : NeBot l := hq
  have htend_id : Tendsto id l (𝓝 q) := inf_le_left
  have hmem : ∀ᶠ r in l,
      r ∈ compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :=
    (Filter.le_def.mp inf_le_right) _ (mem_principal_self _)
  classical
  let F : FiniteParabolicC2AlphaAmbient X E t₀ T α →
      FiniteParabolicC2AlphaAmbient X E t₀ T α := fun r =>
    if hr : r ∈ compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)
    then r else 0
  have hF_eq : F =ᶠ[l] id := hmem.mono fun r hr => by simp [F, hr]
  have htend : Tendsto F l (𝓝 q) := htend_id.congr' hF_eq.symm
  have hF_mem : ∀ r,
      F r ∈ compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) := by
    intro r
    by_cases hr : r ∈ compatibleSubmodule (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)
    · simpa [F, hr]
    · simp [F, hr]
  constructor
  · intro t ht x
    have hu := (tendstoUniformlyOn_spaceDeriv_of_tendsto htend).comp
      (fun y : X => (t, y))
    have hu' : TendstoUniformly
        (fun r => spaceDeriv (F r) ∘ fun y : X => (t, y))
        (spaceDeriv q ∘ fun y : X => (t, y)) l := by
      rw [← tendstoUniformlyOn_univ]
      simpa [parabolicFiniteCylinder, ht] using hu
    exact hasFDerivAt_of_tendstoUniformly
      (f := fun r => fun y : X => value (F r) (t, y))
      (g := fun y : X => value q (t, y))
      (f' := fun r => spaceDeriv (F r) ∘ fun y : X => (t, y))
      (g' := spaceDeriv q ∘ fun y : X => (t, y)) hu'
      (fun r y => (hF_mem r).hasSpaceDeriv t ht y)
      (fun y => (tendstoUniformlyOn_value_of_tendsto htend).tendsto_at
        (by simp [parabolicFiniteCylinder, ht])) x
  · intro t ht x
    have hu := (tendstoUniformlyOn_spaceSecondDeriv_of_tendsto htend).comp
      (fun y : X => (t, y))
    have hu' : TendstoUniformly
        (fun r => spaceSecondDeriv (F r) ∘ fun y : X => (t, y))
        (spaceSecondDeriv q ∘ fun y : X => (t, y)) l := by
      rw [← tendstoUniformlyOn_univ]
      simpa [parabolicFiniteCylinder, ht] using hu
    exact hasFDerivAt_of_tendstoUniformly
      (f := fun r => fun y : X => spaceDeriv (F r) (t, y))
      (g := fun y : X => spaceDeriv q (t, y))
      (f' := fun r => spaceSecondDeriv (F r) ∘ fun y : X => (t, y))
      (g' := spaceSecondDeriv q ∘ fun y : X => (t, y)) hu'
      (fun r y => (hF_mem r).hasSpaceSecondDeriv t ht y)
      (fun y => (tendstoUniformlyOn_spaceDeriv_of_tendsto htend).tendsto_at
        (by simp [parabolicFiniteCylinder, ht])) x
  · intro t ht x
    have hu := (tendstoUniformlyOn_timeDeriv_of_tendsto htend).comp
      (fun s : ℝ => (s, x))
    have huIoc : TendstoUniformlyOn
        (fun r => timeDeriv (F r) ∘ fun s : ℝ => (s, x))
        (timeDeriv q ∘ fun s : ℝ => (s, x)) l (Set.Ioc t₀ T) := by
      simpa [parabolicFiniteCylinder] using hu
    have huIoo := huIoc.mono (Set.Ioo_subset_Ioc_self)
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo huIoo
      (Filter.Eventually.of_forall fun r s hs => (hF_mem r).hasTimeDeriv s hs x)
      (fun s hs => (tendstoUniformlyOn_value_of_tendsto htend).tendsto_at
        (by simp [parabolicFiniteCylinder, hs.1, hs.2.le])) ht

end FiniteParabolicC2AlphaAmbient

/-- The complete finite-cylinder higher parabolic space. -/
def FiniteParabolicC2AlphaBanach (X E : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t₀ T α : ℝ) :=
  FiniteParabolicC2AlphaAmbient.compatibleSubmodule
    (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

instance [CompleteSpace E] : CompleteSpace (FiniteParabolicC2AlphaBanach X E t₀ T α) :=
  FiniteParabolicC2AlphaAmbient.isClosed_compatibleSubmodule.completeSpace_coe

def value (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) : E :=
  FiniteParabolicC2AlphaAmbient.value u.1 z

def spaceDeriv (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) : X →L[ℝ] E :=
  FiniteParabolicC2AlphaAmbient.spaceDeriv u.1 z

def spaceSecondDeriv (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (z : ℝ × X) : X →L[ℝ] X →L[ℝ] E :=
  FiniteParabolicC2AlphaAmbient.spaceSecondDeriv u.1 z

def timeDeriv (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) : E :=
  FiniteParabolicC2AlphaAmbient.timeDeriv u.1 z

@[simp] theorem value_zero (z : ℝ × X) :
    value (0 : FiniteParabolicC2AlphaBanach X E t₀ T α) z = 0 := by
  exact FiniteParabolicC2AlphaAmbient.value_zero z

@[simp] theorem value_add
    (u v : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    value (u + v) z = value u z + value v z := by
  exact FiniteParabolicC2AlphaAmbient.value_add u.1 v.1 z

@[simp] theorem value_smul (c : ℝ)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    value (c • u) z = c • value u z := by
  exact FiniteParabolicC2AlphaAmbient.value_smul c u.1 z

@[simp] theorem spaceDeriv_zero (z : ℝ × X) :
    spaceDeriv (0 : FiniteParabolicC2AlphaBanach X E t₀ T α) z = 0 := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_zero z

@[simp] theorem spaceDeriv_add
    (u v : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    spaceDeriv (u + v) z = spaceDeriv u z + spaceDeriv v z := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_add u.1 v.1 z

@[simp] theorem spaceDeriv_smul (c : ℝ)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    spaceDeriv (c • u) z = c • spaceDeriv u z := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_smul c u.1 z

@[simp] theorem spaceSecondDeriv_zero (z : ℝ × X) :
    spaceSecondDeriv (0 : FiniteParabolicC2AlphaBanach X E t₀ T α) z = 0 := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_zero z

@[simp] theorem spaceSecondDeriv_add
    (u v : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    spaceSecondDeriv (u + v) z =
      spaceSecondDeriv u z + spaceSecondDeriv v z := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_add u.1 v.1 z

@[simp] theorem spaceSecondDeriv_smul (c : ℝ)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    spaceSecondDeriv (c • u) z = c • spaceSecondDeriv u z := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_smul c u.1 z

@[simp] theorem timeDeriv_zero (z : ℝ × X) :
    timeDeriv (0 : FiniteParabolicC2AlphaBanach X E t₀ T α) z = 0 := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_zero z

@[simp] theorem timeDeriv_add
    (u v : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    timeDeriv (u + v) z = timeDeriv u z + timeDeriv v z := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_add u.1 v.1 z

@[simp] theorem timeDeriv_smul (c : ℝ)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X) :
    timeDeriv (c • u) z = c • timeDeriv u z := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_smul c u.1 z

theorem hasFDerivAt_space (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : X) :
    HasFDerivAt (fun y : X => value u (t, y)) (spaceDeriv u (t, x)) x :=
  u.2.hasSpaceDeriv t ht x

theorem hasFDerivAt_spaceDeriv
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : X) :
    HasFDerivAt (fun y : X => spaceDeriv u (t, y))
      (spaceSecondDeriv u (t, x)) x :=
  u.2.hasSpaceSecondDeriv t ht x

theorem hasDerivAt_time (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioo t₀ T) (x : X) :
    HasDerivAt (fun s : ℝ => value u (s, x)) (timeDeriv u (t, x)) t :=
  u.2.hasTimeDeriv t ht x

/-- Every fixed positive-time spatial slice represented by a finite-cylinder
`C^{2+α,1+α/2}` element is genuinely twice continuously Fréchet
differentiable. -/
theorem contDiff_two_space (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) :
    ContDiff ℝ 2 (fun x : X => value u (t, x)) := by
  have hDcont : Continuous (fun x : X => spaceDeriv u (t, x)) := by
    have hc : ContinuousOn
        (ParabolicC0AlphaBanach.representative u.1.2.1)
        (parabolicFiniteCylinder X t₀ T) :=
      (ParabolicC0AlphaBanach.outL u.1.2.1).2.continuousOn hα
    have hcomp := hc.comp_continuous
      ((continuous_const : Continuous (fun _ : X => t)).prodMk continuous_id)
      (fun x : X => by simpa [parabolicFiniteCylinder] using ht)
    simpa [Function.comp_def, spaceDeriv,
      FiniteParabolicC2AlphaAmbient.spaceDeriv] using hcomp
  have hD2cont : Continuous (fun x : X => spaceSecondDeriv u (t, x)) := by
    have hc : ContinuousOn
        (ParabolicC0AlphaBanach.representative u.1.2.2.1)
        (parabolicFiniteCylinder X t₀ T) :=
      (ParabolicC0AlphaBanach.outL u.1.2.2.1).2.continuousOn hα
    have hcomp := hc.comp_continuous
      ((continuous_const : Continuous (fun _ : X => t)).prodMk continuous_id)
      (fun x : X => by simpa [parabolicFiniteCylinder] using ht)
    simpa [Function.comp_def, spaceSecondDeriv,
      FiniteParabolicC2AlphaAmbient.spaceSecondDeriv] using hcomp
  have hD1 : ContDiff ℝ 1 (fun x : X => spaceDeriv u (t, x)) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_spaceDeriv u ht x).differentiableAt, ?_⟩
    have heq : fderiv ℝ (fun x : X => spaceDeriv u (t, x)) =
        fun x => spaceSecondDeriv u (t, x) := by
      funext x
      exact (hasFDerivAt_spaceDeriv u ht x).fderiv
    rw [heq]
    exact hD2cont
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_space u ht x).differentiableAt,
    by rintro ⟨⟩, ?_⟩
  have heq : fderiv ℝ (fun x : X => value u (t, x)) =
      fun x => spaceDeriv u (t, x) := by
    funext x
    exact (hasFDerivAt_space u ht x).fderiv
  rw [heq]
  exact hD1

/-- Package a genuine second jet whose four components are parabolically
Hölder on the finite cylinder into the complete finite-cylinder Banach
space.  No derivative is reconstructed from a norm predicate: all three
calculus witnesses come from the supplied jet. -/
def ofSecondJet (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaOn α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaOn α J.spaceDeriv (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaOn α J.spaceSecondDeriv (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaOn α J.timeDeriv (parabolicFiniteCylinder X t₀ T)) :
    FiniteParabolicC2AlphaBanach X E t₀ T α := by
  let U : ParabolicC0AlphaSpace X E α (parabolicFiniteCylinder X t₀ T) :=
    ParabolicC0AlphaSpace.ofSubmodule ⟨u, hu⟩
  let Ux : ParabolicC0AlphaSpace X (X →L[ℝ] E) α
      (parabolicFiniteCylinder X t₀ T) :=
    ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceDeriv, hux⟩
  let Uxx : ParabolicC0AlphaSpace X (X →L[ℝ] X →L[ℝ] E) α
      (parabolicFiniteCylinder X t₀ T) :=
    ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceSecondDeriv, huxx⟩
  let Ut : ParabolicC0AlphaSpace X E α (parabolicFiniteCylinder X t₀ T) :=
    ParabolicC0AlphaSpace.ofSubmodule ⟨J.timeDeriv, hut⟩
  let q : FiniteParabolicC2AlphaAmbient X E t₀ T α :=
    (ParabolicC0AlphaBanach.mk U,
      ParabolicC0AlphaBanach.mk Ux,
        ParabolicC0AlphaBanach.mk Uxx,
          ParabolicC0AlphaBanach.mk Ut)
  refine ⟨q, ?_⟩
  constructor
  · intro t ht x
    have hJ : HasFDerivAt (fun y : X => u (t, y)) (J.spaceDeriv (t, x)) x := by
      apply (J.hasSpaceDeriv (z := (t, x))
        (by simp [parabolicFiniteCylinder, ht])).hasFDerivAt
      simp [spaceSliceDomain, parabolicFiniteCylinder, ht]
    have hfun : (fun y : X => FiniteParabolicC2AlphaAmbient.value q (t, y)) =
        fun y : X => u (t, y) := by
      funext y
      exact ParabolicC0AlphaBanach.representative_mk_eq U (t, y)
        (by simp [parabolicFiniteCylinder, ht])
    have hderiv : FiniteParabolicC2AlphaAmbient.spaceDeriv q (t, x) =
        J.spaceDeriv (t, x) :=
      ParabolicC0AlphaBanach.representative_mk_eq Ux (t, x)
        (by simp [parabolicFiniteCylinder, ht])
    rw [hfun, hderiv]
    exact hJ
  · intro t ht x
    have hJ : HasFDerivAt (fun y : X => J.spaceDeriv (t, y))
        (J.spaceSecondDeriv (t, x)) x := by
      apply (J.hasSpaceSecondDeriv (z := (t, x))
        (by simp [parabolicFiniteCylinder, ht])).hasFDerivAt
      simp [spaceSliceDomain, parabolicFiniteCylinder, ht]
    have hfun :
        (fun y : X => FiniteParabolicC2AlphaAmbient.spaceDeriv q (t, y)) =
          fun y : X => J.spaceDeriv (t, y) := by
      funext y
      exact ParabolicC0AlphaBanach.representative_mk_eq Ux (t, y)
        (by simp [parabolicFiniteCylinder, ht])
    have hderiv : FiniteParabolicC2AlphaAmbient.spaceSecondDeriv q (t, x) =
        J.spaceSecondDeriv (t, x) :=
      ParabolicC0AlphaBanach.representative_mk_eq Uxx (t, x)
        (by simp [parabolicFiniteCylinder, ht])
    rw [hfun, hderiv]
    exact hJ
  · intro t ht x
    have htIoc : t ∈ Set.Ioc t₀ T := ⟨ht.1, ht.2.le⟩
    have hnhds : Set.Ioc t₀ T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hJ : HasDerivAt (fun s : ℝ => u (s, x)) (J.timeDeriv (t, x)) t := by
      apply (J.hasTimeDeriv (z := (t, x))
        (by simp [parabolicFiniteCylinder, htIoc])).hasDerivAt
      have hslice :
          timeSliceDomain (parabolicFiniteCylinder X t₀ T) x = Set.Ioc t₀ T := by
        ext s
        simp [timeSliceDomain, parabolicFiniteCylinder]
      rw [hslice]
      exact hnhds
    have hev :
        (fun s : ℝ => FiniteParabolicC2AlphaAmbient.value q (s, x)) =ᶠ[𝓝 t]
          fun s : ℝ => u (s, x) := by
      filter_upwards [hnhds] with s hs
      exact ParabolicC0AlphaBanach.representative_mk_eq U (s, x)
        (by simp [parabolicFiniteCylinder, hs])
    have hderiv : FiniteParabolicC2AlphaAmbient.timeDeriv q (t, x) =
        J.timeDeriv (t, x) :=
      ParabolicC0AlphaBanach.representative_mk_eq Ut (t, x)
        (by simp [parabolicFiniteCylinder, htIoc])
    rw [hderiv]
    exact hJ.congr_of_eventuallyEq hev

@[simp] theorem value_ofSecondJet
    (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaOn α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaOn α J.spaceDeriv (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaOn α J.spaceSecondDeriv
      (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaOn α J.timeDeriv (parabolicFiniteCylinder X t₀ T))
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    value (ofSecondJet u J hu hux huxx hut) z = u z := by
  change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.mk
        (ParabolicC0AlphaSpace.ofSubmodule ⟨u, hu⟩)) z = u z
  exact ParabolicC0AlphaBanach.representative_mk_eq _ z hz

@[simp] theorem spaceDeriv_ofSecondJet
    (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaOn α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaOn α J.spaceDeriv (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaOn α J.spaceSecondDeriv
      (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaOn α J.timeDeriv (parabolicFiniteCylinder X t₀ T))
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceDeriv (ofSecondJet u J hu hux huxx hut) z = J.spaceDeriv z := by
  change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.mk
        (ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceDeriv, hux⟩)) z = J.spaceDeriv z
  exact ParabolicC0AlphaBanach.representative_mk_eq _ z hz

@[simp] theorem spaceSecondDeriv_ofSecondJet
    (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaOn α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaOn α J.spaceDeriv (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaOn α J.spaceSecondDeriv
      (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaOn α J.timeDeriv (parabolicFiniteCylinder X t₀ T))
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    spaceSecondDeriv (ofSecondJet u J hu hux huxx hut) z =
      J.spaceSecondDeriv z := by
  change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.mk
        (ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceSecondDeriv, huxx⟩)) z =
          J.spaceSecondDeriv z
  exact ParabolicC0AlphaBanach.representative_mk_eq _ z hz

@[simp] theorem timeDeriv_ofSecondJet
    (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaOn α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaOn α J.spaceDeriv (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaOn α J.spaceSecondDeriv
      (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaOn α J.timeDeriv (parabolicFiniteCylinder X t₀ T))
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    timeDeriv (ofSecondJet u J hu hux huxx hut) z = J.timeDeriv z := by
  change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.mk
        (ParabolicC0AlphaSpace.ofSubmodule ⟨J.timeDeriv, hut⟩)) z = J.timeDeriv z
  exact ParabolicC0AlphaBanach.representative_mk_eq _ z hz

/-- A common `C⁰,ᵅ` bound on the four components controls the norm of the
packaged finite-cylinder jet. -/
theorem norm_ofSecondJet_le {N : ℝ}
    (u : ℝ × X → E)
    (J : ParabolicSecondJet u (parabolicFiniteCylinder X t₀ T))
    (hu : ParabolicC0AlphaNormLe N α u (parabolicFiniteCylinder X t₀ T))
    (hux : ParabolicC0AlphaNormLe N α J.spaceDeriv
      (parabolicFiniteCylinder X t₀ T))
    (huxx : ParabolicC0AlphaNormLe N α J.spaceSecondDeriv
      (parabolicFiniteCylinder X t₀ T))
    (hut : ParabolicC0AlphaNormLe N α J.timeDeriv
      (parabolicFiniteCylinder X t₀ T)) :
    ‖ofSecondJet u J hu.c0AlphaOn hux.c0AlphaOn huxx.c0AlphaOn hut.c0AlphaOn‖ ≤ N := by
  change ‖(ParabolicC0AlphaBanach.mk
      (ParabolicC0AlphaSpace.ofSubmodule ⟨u, hu.c0AlphaOn⟩),
    ParabolicC0AlphaBanach.mk
      (ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceDeriv, hux.c0AlphaOn⟩),
    ParabolicC0AlphaBanach.mk
      (ParabolicC0AlphaSpace.ofSubmodule ⟨J.spaceSecondDeriv, huxx.c0AlphaOn⟩),
    ParabolicC0AlphaBanach.mk
      (ParabolicC0AlphaSpace.ofSubmodule ⟨J.timeDeriv, hut.c0AlphaOn⟩))‖ ≤ N
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [ParabolicC0AlphaBanach.norm_mk_ofSubmodule]
    exact parabolicC0AlphaNorm_le_of_normLe hu
  · rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [ParabolicC0AlphaBanach.norm_mk_ofSubmodule]
      exact parabolicC0AlphaNorm_le_of_normLe hux
    · rw [Prod.norm_def]
      refine max_le ?_ ?_
      · rw [ParabolicC0AlphaBanach.norm_mk_ofSubmodule]
        exact parabolicC0AlphaNorm_le_of_normLe huxx
      · rw [ParabolicC0AlphaBanach.norm_mk_ofSubmodule]
        exact parabolicC0AlphaNorm_le_of_normLe hut

/-- Bounded projection to the value component. -/
def valueComponentL :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
      (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL

/-- Bounded projection to the first spatial derivative component. -/
def spaceDerivComponentL :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X (X →L[ℝ] E) α
        (parabolicFiniteCylinder X t₀ T) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL)

/-- Bounded projection to the second spatial derivative component. -/
def spaceSecondDerivComponentL :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X (X →L[ℝ] X →L[ℝ] E) α
        (parabolicFiniteCylinder X t₀ T) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
          (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL))

/-- Bounded projection to the time derivative component. -/
def timeDerivComponentL :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
          (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)).subtypeL))

@[simp] theorem valueComponentL_apply
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) : valueComponentL u = u.1.1 := rfl

@[simp] theorem spaceDerivComponentL_apply
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    spaceDerivComponentL u = u.1.2.1 := rfl

@[simp] theorem spaceSecondDerivComponentL_apply
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    spaceSecondDerivComponentL u = u.1.2.2.1 := rfl

@[simp] theorem timeDerivComponentL_apply
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) : timeDerivComponentL u = u.1.2.2.2 := rfl

@[simp] theorem evalCLM_valueComponentL
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (valueComponentL u) = value u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative]
  rfl

@[simp] theorem evalCLM_spaceDerivComponentL
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (spaceDerivComponentL u) = spaceDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative]
  rfl

@[simp] theorem evalCLM_spaceSecondDerivComponentL
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (spaceSecondDerivComponentL u) =
      spaceSecondDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative]
  rfl

@[simp] theorem evalCLM_timeDerivComponentL
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (timeDerivComponentL u) = timeDeriv u z := by
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative]
  rfl

/-- Restrict a genuine finite-cylinder second jet to an earlier terminal
time.  All four Hölder components are restricted by the norm-nonincreasing
Banach restriction operator, while derivative compatibility is inherited
from the original jet. -/
noncomputable def restrictTerminal {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    FiniteParabolicC2AlphaBanach X E t₀ S α := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  let q : FiniteParabolicC2AlphaAmbient X E t₀ S α :=
    (ParabolicC0AlphaBanach.restrictL hsub u.1.1,
      ParabolicC0AlphaBanach.restrictL hsub u.1.2.1,
      ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.1,
      ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.2)
  refine ⟨q, ?_⟩
  have hval : ∀ z ∈ parabolicFiniteCylinder X t₀ S,
      FiniteParabolicC2AlphaAmbient.value q z = value u z := by
    intro z hz
    change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.restrictL hsub u.1.1) z =
        ParabolicC0AlphaBanach.representative u.1.1 z
    rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
      ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
    exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.1
  have hfirst : ∀ z ∈ parabolicFiniteCylinder X t₀ S,
      FiniteParabolicC2AlphaAmbient.spaceDeriv q z = spaceDeriv u z := by
    intro z hz
    change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.restrictL hsub u.1.2.1) z =
        ParabolicC0AlphaBanach.representative u.1.2.1 z
    rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
      ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
    exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.1
  have hsecond : ∀ z ∈ parabolicFiniteCylinder X t₀ S,
      FiniteParabolicC2AlphaAmbient.spaceSecondDeriv q z = spaceSecondDeriv u z := by
    intro z hz
    change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.1) z =
        ParabolicC0AlphaBanach.representative u.1.2.2.1 z
    rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
      ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
    exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.2.1
  have htime : ∀ z ∈ parabolicFiniteCylinder X t₀ S,
      FiniteParabolicC2AlphaAmbient.timeDeriv q z = timeDeriv u z := by
    intro z hz
    change ParabolicC0AlphaBanach.representative
      (ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.2) z =
        ParabolicC0AlphaBanach.representative u.1.2.2.2 z
    rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
      ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
    exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.2.2
  constructor
  · intro t ht x
    have ht' : t ∈ Set.Ioc t₀ T := ⟨ht.1, ht.2.trans hST⟩
    convert (u.2.hasSpaceDeriv t ht' x) using 1
    · funext y
      exact hval (t, y) (by simp [parabolicFiniteCylinder, ht])
    · exact hfirst (t, x) (by simp [parabolicFiniteCylinder, ht])
  · intro t ht x
    have ht' : t ∈ Set.Ioc t₀ T := ⟨ht.1, ht.2.trans hST⟩
    convert (u.2.hasSpaceSecondDeriv t ht' x) using 1
    · funext y
      exact hfirst (t, y) (by simp [parabolicFiniteCylinder, ht])
    · exact hsecond (t, x) (by simp [parabolicFiniteCylinder, ht])
  · intro t ht x
    have ht' : t ∈ Set.Ioo t₀ T := ⟨ht.1, ht.2.trans_le hST⟩
    have hd := u.2.hasTimeDeriv t ht' x
    have hmem : Set.Ioc t₀ S ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev : (fun s => FiniteParabolicC2AlphaAmbient.value q (s, x)) =ᶠ[𝓝 t]
        (fun s => value u (s, x)) := by
      filter_upwards [hmem] with s hs
      exact hval (s, x) (by simp [parabolicFiniteCylinder, hs])
    rw [htime (t, x) (by simp [parabolicFiniteCylinder, ht.1, ht.2.le])]
    exact hd.congr_of_eventuallyEq hev

@[simp] theorem value_restrictTerminal {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ S) :
    value (restrictTerminal hST u) z = value u z := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  change ParabolicC0AlphaBanach.representative
    (ParabolicC0AlphaBanach.restrictL hsub u.1.1) z =
      ParabolicC0AlphaBanach.representative u.1.1 z
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
    ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
  exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.1

@[simp] theorem spaceDeriv_restrictTerminal {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ S) :
    spaceDeriv (restrictTerminal hST u) z = spaceDeriv u z := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  change ParabolicC0AlphaBanach.representative
    (ParabolicC0AlphaBanach.restrictL hsub u.1.2.1) z =
      ParabolicC0AlphaBanach.representative u.1.2.1 z
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
    ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
  exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.1

@[simp] theorem spaceSecondDeriv_restrictTerminal {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ S) :
    spaceSecondDeriv (restrictTerminal hST u) z = spaceSecondDeriv u z := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  change ParabolicC0AlphaBanach.representative
    (ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.1) z =
      ParabolicC0AlphaBanach.representative u.1.2.2.1 z
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
    ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
  exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.2.1

@[simp] theorem timeDeriv_restrictTerminal {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ S) :
    timeDeriv (restrictTerminal hST u) z = timeDeriv u z := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  change ParabolicC0AlphaBanach.representative
    (ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.2) z =
      ParabolicC0AlphaBanach.representative u.1.2.2.2 z
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z hz,
    ← ParabolicC0AlphaBanach.evalCLM_eq_representative _ z (hsub hz)]
  exact ParabolicC0AlphaBanach.evalCLM_restrictL_apply hsub z hz u.1.2.2.2

@[simp] theorem restrictTerminal_zero {S : ℝ} (hST : S ≤ T) :
    restrictTerminal (X := X) (E := E) (t₀ := t₀) (α := α) hST 0 = 0 := by
  apply Subtype.ext
  simp [restrictTerminal]

@[simp] theorem restrictTerminal_add {S : ℝ} (hST : S ≤ T)
    (u v : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    restrictTerminal hST (u + v) = restrictTerminal hST u + restrictTerminal hST v := by
  apply Subtype.ext
  simp [restrictTerminal]

@[simp] theorem restrictTerminal_smul {S : ℝ} (hST : S ≤ T) (c : ℝ)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    restrictTerminal hST (c • u) = c • restrictTerminal hST u := by
  apply Subtype.ext
  simp [restrictTerminal]

/-- Terminal restriction is norm-nonincreasing in the full four-component
`C^{2+α,1+α/2}` norm. -/
theorem norm_restrictTerminal_le {S : ℝ} (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ‖restrictTerminal hST u‖ ≤ ‖u‖ := by
  let hsub := parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST
  change max ‖ParabolicC0AlphaBanach.restrictL hsub u.1.1‖
      (max ‖ParabolicC0AlphaBanach.restrictL hsub u.1.2.1‖
        (max ‖ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.1‖
          ‖ParabolicC0AlphaBanach.restrictL hsub u.1.2.2.2‖)) ≤
    max ‖u.1.1‖ (max ‖u.1.2.1‖ (max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖))
  apply max_le
  · exact ((ParabolicC0AlphaBanach.restrictL hsub).le_opNorm _).trans
      (by
        calc _ ≤ 1 * ‖u.1.1‖ := mul_le_mul_of_nonneg_right
              (ParabolicC0AlphaBanach.norm_restrictL_le hsub) (norm_nonneg _)
          _ = ‖u.1.1‖ := one_mul _
          _ ≤ _ := le_max_left _ _)
  · apply max_le
    · exact ((ParabolicC0AlphaBanach.restrictL hsub).le_opNorm _).trans
        (by
          calc _ ≤ 1 * ‖u.1.2.1‖ := mul_le_mul_of_nonneg_right
                (ParabolicC0AlphaBanach.norm_restrictL_le hsub) (norm_nonneg _)
            _ = ‖u.1.2.1‖ := one_mul _
            _ ≤ max ‖u.1.2.1‖ (max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖) := le_max_left _ _
            _ ≤ _ := le_max_right _ _)
    · apply max_le
      · exact ((ParabolicC0AlphaBanach.restrictL hsub).le_opNorm _).trans
          (by
            calc _ ≤ 1 * ‖u.1.2.2.1‖ := mul_le_mul_of_nonneg_right
                  (ParabolicC0AlphaBanach.norm_restrictL_le hsub) (norm_nonneg _)
              _ = ‖u.1.2.2.1‖ := one_mul _
              _ ≤ max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖ := le_max_left _ _
              _ ≤ max ‖u.1.2.1‖ (max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖) := le_max_right _ _
              _ ≤ _ := le_max_right _ _)
      · exact ((ParabolicC0AlphaBanach.restrictL hsub).le_opNorm _).trans
          (by
            calc _ ≤ 1 * ‖u.1.2.2.2‖ := mul_le_mul_of_nonneg_right
                  (ParabolicC0AlphaBanach.norm_restrictL_le hsub) (norm_nonneg _)
              _ = ‖u.1.2.2.2‖ := one_mul _
              _ ≤ max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖ := le_max_right _ _
              _ ≤ max ‖u.1.2.1‖ (max ‖u.1.2.2.1‖ ‖u.1.2.2.2‖) := le_max_right _ _
              _ ≤ _ := le_max_right _ _)

/-- Bounded terminal restriction of genuine finite-cylinder second jets. -/
noncomputable def restrictTerminalL {S : ℝ} (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach X E t₀ S α :=
  LinearMap.mkContinuous
    { toFun := restrictTerminal hST
      map_add' := restrictTerminal_add hST
      map_smul' := restrictTerminal_smul hST }
    1 (by simpa using (norm_restrictTerminal_le (X := X) (E := E) (t₀ := t₀)
      (α := α) hST))

theorem norm_restrictTerminalL_le {S : ℝ} (hST : S ≤ T) :
    ‖restrictTerminalL (X := X) (E := E) (t₀ := t₀) (α := α) hST‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- On a nondegenerate finite cylinder, a compatible parabolic second jet is
determined by its value component.  The spatial derivatives are unique on the
full Euclidean slices.  The time derivatives first agree on the open time
interval by uniqueness, and then at the terminal face by continuity. -/
theorem ext_value (hα : 0 < α) (hT : t₀ < T)
    {u v : FiniteParabolicC2AlphaBanach X E t₀ T α}
    (hvalue : ∀ z ∈ parabolicFiniteCylinder X t₀ T, value u z = value v z) :
    u = v := by
  have hU : valueComponentL u = valueComponentL v :=
    (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2 fun z hz => by
      rw [evalCLM_valueComponentL, evalCLM_valueComponentL]
      exact hvalue z hz
  have hUx_point : ∀ z ∈ parabolicFiniteCylinder X t₀ T,
      spaceDeriv u z = spaceDeriv v z := by
    rintro ⟨t, x⟩ hz
    have ht : t ∈ Set.Ioc t₀ T := by
      simpa [parabolicFiniteCylinder] using hz
    have heq : (fun y : X => value u (t, y)) = fun y : X => value v (t, y) := by
      funext y
      exact hvalue (t, y) (by simp [parabolicFiniteCylinder, ht])
    have hv := hasFDerivAt_space v ht x
    rw [← heq] at hv
    exact (hasFDerivAt_space u ht x).unique hv
  have hUx : spaceDerivComponentL u = spaceDerivComponentL v :=
    (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2 fun z hz => by
      rw [evalCLM_spaceDerivComponentL, evalCLM_spaceDerivComponentL]
      exact hUx_point z hz
  have hUxx_point : ∀ z ∈ parabolicFiniteCylinder X t₀ T,
      spaceSecondDeriv u z = spaceSecondDeriv v z := by
    rintro ⟨t, x⟩ hz
    have ht : t ∈ Set.Ioc t₀ T := by
      simpa [parabolicFiniteCylinder] using hz
    have heq : (fun y : X => spaceDeriv u (t, y)) =
        fun y : X => spaceDeriv v (t, y) := by
      funext y
      exact hUx_point (t, y) (by simp [parabolicFiniteCylinder, ht])
    have hv := hasFDerivAt_spaceDeriv v ht x
    rw [← heq] at hv
    exact (hasFDerivAt_spaceDeriv u ht x).unique hv
  have hUxx : spaceSecondDerivComponentL u = spaceSecondDerivComponentL v :=
    (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2 fun z hz => by
      rw [evalCLM_spaceSecondDerivComponentL, evalCLM_spaceSecondDerivComponentL]
      exact hUxx_point z hz
  have hUt_interior : Set.EqOn
      (fun z : ℝ × X => timeDeriv u z)
      (fun z : ℝ × X => timeDeriv v z)
      (Set.Ioo t₀ T ×ˢ Set.univ) := by
    rintro ⟨t, x⟩ hz
    have ht : t ∈ Set.Ioo t₀ T := hz.1
    have hnhds : Set.Ioc t₀ T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev : (fun s : ℝ => value u (s, x)) =ᶠ[𝓝 t]
        fun s : ℝ => value v (s, x) := by
      filter_upwards [hnhds] with s hs
      exact hvalue (s, x) (by simp [parabolicFiniteCylinder, hs])
    exact (hasDerivAt_time u ht x).unique
      ((hasDerivAt_time v ht x).congr_of_eventuallyEq hev)
  have hUt_cont_u : ContinuousOn (fun z : ℝ × X => timeDeriv u z)
      (parabolicFiniteCylinder X t₀ T) := by
    change ContinuousOn
      (ParabolicC0AlphaSpace.toFun (ParabolicC0AlphaBanach.outL (timeDerivComponentL u))) _
    exact (ParabolicC0AlphaSpace.toSubmodule
      (ParabolicC0AlphaBanach.outL (timeDerivComponentL u))).2.continuousOn hα
  have hUt_cont_v : ContinuousOn (fun z : ℝ × X => timeDeriv v z)
      (parabolicFiniteCylinder X t₀ T) := by
    change ContinuousOn
      (ParabolicC0AlphaSpace.toFun (ParabolicC0AlphaBanach.outL (timeDerivComponentL v))) _
    exact (ParabolicC0AlphaSpace.toSubmodule
      (ParabolicC0AlphaBanach.outL (timeDerivComponentL v))).2.continuousOn hα
  have hUt_point : ∀ z ∈ parabolicFiniteCylinder X t₀ T,
      timeDeriv u z = timeDeriv v z := by
    have hsub : Set.Ioo t₀ T ×ˢ (Set.univ : Set X) ⊆
        parabolicFiniteCylinder X t₀ T := by
      rintro ⟨t, x⟩ hz
      simp only [parabolicFiniteCylinder, Set.mem_prod, Set.mem_Ioc, Set.mem_univ,
        and_true] at hz ⊢
      exact ⟨hz.1, hz.2.le⟩
    have hclosure : parabolicFiniteCylinder X t₀ T ⊆
        closure (Set.Ioo t₀ T ×ˢ (Set.univ : Set X)) := by
      intro z hz
      rw [show closure (Set.Ioo t₀ T ×ˢ (Set.univ : Set X)) =
          Set.Icc t₀ T ×ˢ (Set.univ : Set X) by
        rw [closure_prod_eq, closure_Ioo (ne_of_lt hT), closure_univ]]
      exact ⟨⟨hz.1.1.le, hz.1.2⟩, Set.mem_univ z.2⟩
    exact Set.EqOn.of_subset_closure hUt_interior hUt_cont_u hUt_cont_v hsub hclosure
  have hUt : timeDerivComponentL u = timeDerivComponentL v :=
    (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2 fun z hz => by
      rw [evalCLM_timeDerivComponentL, evalCLM_timeDerivComponentL]
      exact hUt_point z hz
  apply Subtype.ext
  exact Prod.ext hU (Prod.ext hUx (Prod.ext hUxx hUt))

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
