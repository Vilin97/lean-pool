/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
/-!
# Analytic evolution layer for Ricci-DeTurck

This file starts the proof-bearing analytic layer needed for the Ricci-DeTurck
PDE part of roadmap point 4.  It deliberately proves only what follows from
mathlib's Picard-Lindelof theorem: local Banach-space evolution from verified
Lipschitz/continuity hypotheses.  The geometric Ricci-DeTurck closure still
requires a Banach chart of Riemannian metrics and parabolic estimates showing
that the Ricci-DeTurck operator satisfies these hypotheses.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-- A derivative in the compact-open sup norm differentiates a time-difference
after evaluation at a moving point.  The spatial curve only has to be continuous
at the time in question: the section derivative controls the first-order
remainder uniformly on the compact domain, and continuity of the derivative
section supplies the value at the limiting point. -/
theorem HasDerivWithinAt.continuousMap_moving_eval_sub_const
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝[s] t) (𝓝 (x t))) :
    HasDerivWithinAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) s t := by
  have hrem :
      (fun τ : ℝ ↦ (u τ - u t - (τ - t) • u') (x τ)) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    filter_upwards [Asymptotics.IsLittleO.bound hu.isLittleO hc] with τ hτ
    exact (ContinuousMap.norm_coe_le_norm (u τ - u t - (τ - t) • u') (x τ)).trans hτ
  have hderiv_eval_tendsto :
      Filter.Tendsto (fun τ : ℝ ↦ u' (x τ) - u' (x t)) (𝓝[s] t) (𝓝 0) := by
    have hu'_tendsto :
        Filter.Tendsto (fun y : K ↦ u' y) (𝓝 (x t)) (𝓝 (u' (x t))) :=
      map_continuousAt u' (x t)
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ u' (x t)) (𝓝[s] t) (𝓝 (u' (x t))) :=
      tendsto_const_nhds
    simpa using (hu'_tendsto.comp hx).sub hconst
  have hderiv_eval :
      (fun τ : ℝ ↦ u' (x τ) - u' (x t)) =o[𝓝[s] t]
        fun _ : ℝ ↦ (1 : ℝ) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hderiv_eval_tendsto
  have htime :
      (fun τ : ℝ ↦ τ - t) =O[𝓝[s] t] fun τ : ℝ ↦ τ - t :=
    Asymptotics.isBigO_refl _ _
  have hmove :
      (fun τ : ℝ ↦ (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    simpa using htime.smul_isLittleO hderiv_eval
  have htotal :
      (fun τ : ℝ ↦
        (u τ - u t - (τ - t) • u') (x τ) +
          (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t :=
    hrem.add hmove
  refine HasDerivWithinAt.of_isLittleO ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_sub] using htotal

/-- Unrestricted version of
`HasDerivWithinAt.continuousMap_moving_eval_sub_const`. -/
theorem HasDerivAt.continuousMap_moving_eval_sub_const
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {t : ℝ}
    (hu : HasDerivAt u u' t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) t := by
  rw [← hasDerivWithinAt_univ] at hu ⊢
  exact HasDerivWithinAt.continuousMap_moving_eval_sub_const hu (by simpa using hx)

/-- A forward local solution of a Banach-space evolution equation
`d u / dt = F t u` with initial value `u t₀ = u₀`. -/
structure BanachEvolutionLocalSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : ℝ → X → X) (t₀ : ℝ) (u₀ : X) where
  /-- Terminal time of the forward local solution interval. -/
  terminalTime : ℝ
  /-- The interval is genuinely forward in time. -/
  initial_lt_terminal : t₀ < terminalTime
  /-- The evolving Banach-space state. -/
  curve : ℝ → X
  /-- The initial condition. -/
  initial_eq : curve t₀ = u₀
  /-- The evolution equation on the closed local interval. -/
  equation :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ terminalTime →
      HasDerivWithinAt curve (F t (curve t)) (Icc t₀ terminalTime) t

namespace BanachEvolutionLocalSolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {t₀ : ℝ} {u₀ : X}

theorem initial_mem (sol : BanachEvolutionLocalSolution F t₀ u₀) :
    t₀ ∈ Icc t₀ sol.terminalTime :=
  ⟨le_rfl, le_of_lt sol.initial_lt_terminal⟩

theorem terminal_mem (sol : BanachEvolutionLocalSolution F t₀ u₀) :
    sol.terminalTime ∈ Icc t₀ sol.terminalTime :=
  ⟨le_of_lt sol.initial_lt_terminal, le_rfl⟩

theorem equation_initial (sol : BanachEvolutionLocalSolution F t₀ u₀) :
    HasDerivWithinAt sol.curve (F t₀ (sol.curve t₀)) (Icc t₀ sol.terminalTime) t₀ :=
  sol.equation sol.initial_mem

theorem equation_hasDerivAt_of_mem_Ioo
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt sol.curve (F t (sol.curve t)) t :=
  (sol.equation (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Interior scalar/vector projections of a Banach ODE solution satisfy the projected ODE. -/
theorem continuousLinearMap_hasDerivAt_of_mem_Ioo
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (F t (sol.curve t))) t := by
  simpa [Function.comp_def] using
    (L.hasFDerivAt.comp t
      (sol.equation_hasDerivAt_of_mem_Ioo ht).hasFDerivAt).hasDerivAt

theorem equation_hasDerivWithinAt_Ici_of_mem_Ico
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt sol.curve (F t (sol.curve t)) (Ici t) t :=
  (sol.equation (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

/-- Right-interval scalar/vector projections of a Banach ODE solution satisfy the projected ODE. -/
theorem continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (F t (sol.curve t))) (Ici t) t := by
  simpa [Function.comp_def] using
    (L.hasFDerivAt.comp_hasFDerivWithinAt t
      (sol.equation_hasDerivWithinAt_Ici_of_mem_Ico ht).hasFDerivWithinAt).hasDerivWithinAt

theorem equation_on_Icc_of_le_terminal
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT : T ≤ sol.terminalTime) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ T →
      HasDerivWithinAt sol.curve (F t (sol.curve t)) (Icc t₀ T) t := by
  intro t ht
  exact (sol.equation ⟨ht.1, le_trans ht.2 hT⟩).mono
    (Icc_subset_Icc_right hT)

theorem continuousOn_Icc_of_le_terminal
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT : T ≤ sol.terminalTime) :
    ContinuousOn sol.curve (Icc t₀ T) :=
  HasDerivWithinAt.continuousOn fun _ ht ↦
    sol.equation_on_Icc_of_le_terminal hT ht

/-- Restrict a Banach evolution local solution to any shorter forward terminal time. -/
def restrictTerminal
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    BanachEvolutionLocalSolution F t₀ u₀ where
  terminalTime := T
  initial_lt_terminal := hT₀
  curve := sol.curve
  initial_eq := sol.initial_eq
  equation := by
    intro t ht
    exact sol.equation_on_Icc_of_le_terminal hT ht

@[simp] theorem restrictTerminal_terminalTime
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).terminalTime = T :=
  rfl

@[simp] theorem restrictTerminal_curve
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).curve = sol.curve :=
  rfl

theorem eqOn_Icc_of_lipschitz
    {K : ℝ≥0} (hF : ∀ t : ℝ, LipschitzWith K (F t))
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀) :
    EqOn sol₁.curve sol₂.curve
      (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let T := min sol₁.terminalTime sol₂.terminalTime
  have hT₁ : T ≤ sol₁.terminalTime := min_le_left _ _
  have hT₂ : T ≤ sol₂.terminalTime := min_le_right _ _
  refine ODE_solution_unique (v := F) (K := K) (a := t₀) (b := T) hF
    (sol₁.continuousOn_Icc_of_le_terminal hT₁) ?_
    (sol₂.continuousOn_Icc_of_le_terminal hT₂) ?_ ?_
  · intro t ht
    exact sol₁.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₁⟩
  · intro t ht
    exact sol₂.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₂⟩
  · rw [sol₁.initial_eq, sol₂.initial_eq]

/-- Global-Lipschitz uniqueness read on any explicitly chosen shorter common terminal interval. -/
theorem eqOn_Icc_of_lipschitz_of_le_terminal
    {K : ℝ≥0} (hF : ∀ t : ℝ, LipschitzWith K (F t))
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T)
    (hT₁ : T ≤ sol₁.terminalTime) (hT₂ : T ≤ sol₂.terminalTime) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ T) := by
  let sol₁T := sol₁.restrictTerminal hT₀ hT₁
  let sol₂T := sol₂.restrictTerminal hT₀ hT₂
  have hEq := eqOn_Icc_of_lipschitz (F := F) (t₀ := t₀) (u₀ := u₀)
    (K := K) hF sol₁T sol₂T
  intro t ht
  have ht' : t ∈ Icc t₀ (min sol₁T.terminalTime sol₂T.terminalTime) := by
    exact ⟨ht.1, le_min (by simpa [sol₁T] using ht.2) (by simpa [sol₂T] using ht.2)⟩
  simpa [sol₁T, sol₂T] using hEq ht'

/-- Order-theoretic continuation bridge: if equality is available on every
prescribed shorter common terminal, then it holds on the open common interval. -/
theorem eqOn_Ico_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Ico t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  intro t ht
  rcases exists_between ht.2 with ⟨T, htT, hTcommon⟩
  have hT₀ : t₀ < T := lt_of_le_of_lt ht.1 htT
  have hT₁ : T ≤ sol₁.terminalTime :=
    le_trans (le_of_lt hTcommon) (min_le_left _ _)
  have hT₂ : T ≤ sol₂.terminalTime :=
    le_trans (le_of_lt hTcommon) (min_le_right _ _)
  exact hEq hT₀ hT₁ hT₂ ⟨ht.1, le_of_lt htT⟩

end BanachEvolutionLocalSolution

/-- A forward Banach-space local solution whose values are known to stay in a prescribed state
set. This is the form needed for local uniqueness from Lipschitz bounds on a chart domain or on
the Riemannian metric locus. -/
structure BanachEvolutionLocalSolutionIn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : ℝ → X → X) (stateSet : Set X) (t₀ : ℝ) (u₀ : X)
    extends BanachEvolutionLocalSolution F t₀ u₀ where
  /-- The solution remains in the prescribed state set on its local interval. -/
  mem_state :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ terminalTime → curve t ∈ stateSet

namespace BanachEvolutionLocalSolutionIn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X}

theorem initial_mem (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    t₀ ∈ Icc t₀ sol.terminalTime :=
  sol.toBanachEvolutionLocalSolution.initial_mem

theorem terminal_mem (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    sol.terminalTime ∈ Icc t₀ sol.terminalTime :=
  sol.toBanachEvolutionLocalSolution.terminal_mem

theorem equation_on_Icc_of_le_terminal
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT : T ≤ sol.terminalTime) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ T →
      HasDerivWithinAt sol.curve (F t (sol.curve t)) (Icc t₀ T) t :=
  sol.toBanachEvolutionLocalSolution.equation_on_Icc_of_le_terminal hT

theorem continuousOn_Icc_of_le_terminal
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT : T ≤ sol.terminalTime) :
    ContinuousOn sol.curve (Icc t₀ T) :=
  sol.toBanachEvolutionLocalSolution.continuousOn_Icc_of_le_terminal hT

theorem mem_state_on_Icc_of_le_terminal
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT : T ≤ sol.terminalTime) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ T → sol.curve t ∈ stateSet := by
  intro t ht
  exact sol.mem_state ⟨ht.1, le_trans ht.2 hT⟩

/-- Restrict a state-preserving Banach evolution local solution to any shorter forward terminal
time, preserving both the ODE and the state-set membership proof. -/
def restrictTerminal
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    BanachEvolutionLocalSolutionIn F stateSet t₀ u₀ where
  terminalTime := T
  initial_lt_terminal := hT₀
  curve := sol.curve
  initial_eq := sol.initial_eq
  equation := by
    intro t ht
    exact sol.equation_on_Icc_of_le_terminal hT ht
  mem_state := by
    intro t ht
    exact sol.mem_state_on_Icc_of_le_terminal hT ht

@[simp] theorem restrictTerminal_terminalTime
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).terminalTime = T :=
  rfl

@[simp] theorem restrictTerminal_curve
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).curve = sol.curve :=
  rfl

@[simp] theorem restrictTerminal_toBanachEvolutionLocalSolution
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toBanachEvolutionLocalSolution =
      sol.toBanachEvolutionLocalSolution.restrictTerminal hT₀ hT :=
  rfl

/-- Interior projections of a state-constrained Banach ODE solution satisfy the projected ODE. -/
theorem continuousLinearMap_hasDerivAt_of_mem_Ioo
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (F t (sol.curve t))) t :=
  sol.toBanachEvolutionLocalSolution.continuousLinearMap_hasDerivAt_of_mem_Ioo L ht

/-- Right-interval projections of a state-constrained Banach ODE solution satisfy the projected ODE. -/
theorem continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y)
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (F t (sol.curve t))) (Ici t) t :=
  sol.toBanachEvolutionLocalSolution.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico L ht

theorem eqOn_Icc_of_lipschitzOn
    {K : ℝ≥0} (hF : ∀ t : ℝ, LipschitzOnWith K (F t) stateSet)
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    EqOn sol₁.curve sol₂.curve
      (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let T := min sol₁.terminalTime sol₂.terminalTime
  have hT₁ : T ≤ sol₁.terminalTime := min_le_left _ _
  have hT₂ : T ≤ sol₂.terminalTime := min_le_right _ _
  refine ODE_solution_unique_of_mem_Icc_right
    (v := F) (s := fun _ : ℝ ↦ stateSet) (K := K) (a := t₀) (b := T)
    (fun t _ ↦ hF t)
    (sol₁.toBanachEvolutionLocalSolution.continuousOn_Icc_of_le_terminal hT₁) ?_
    ?_
    (sol₂.toBanachEvolutionLocalSolution.continuousOn_Icc_of_le_terminal hT₂) ?_
    ?_
    ?_
  · intro t ht
    exact sol₁.toBanachEvolutionLocalSolution.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₁⟩
  · intro t ht
    exact sol₁.mem_state ⟨ht.1, le_trans (le_of_lt ht.2) hT₁⟩
  · intro t ht
    exact sol₂.toBanachEvolutionLocalSolution.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₂⟩
  · intro t ht
    exact sol₂.mem_state ⟨ht.1, le_trans (le_of_lt ht.2) hT₂⟩
  · rw [sol₁.initial_eq, sol₂.initial_eq]

/-- State-set uniqueness when the Lipschitz bound is known only on the common time interval. -/
theorem eqOn_Icc_of_lipschitzOn_Icc
    {K : ℝ≥0}
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hF : ∀ t ∈ Icc t₀ (min sol₁.terminalTime sol₂.terminalTime),
      LipschitzOnWith K (F t) stateSet) :
    EqOn sol₁.curve sol₂.curve
      (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let T := min sol₁.terminalTime sol₂.terminalTime
  have hT₁ : T ≤ sol₁.terminalTime := min_le_left _ _
  have hT₂ : T ≤ sol₂.terminalTime := min_le_right _ _
  refine ODE_solution_unique_of_mem_Icc_right
    (v := F) (s := fun _ : ℝ ↦ stateSet) (K := K) (a := t₀) (b := T)
    (fun t ht ↦ hF t ⟨ht.1, le_of_lt ht.2⟩)
    (sol₁.toBanachEvolutionLocalSolution.continuousOn_Icc_of_le_terminal hT₁) ?_
    ?_
    (sol₂.toBanachEvolutionLocalSolution.continuousOn_Icc_of_le_terminal hT₂) ?_
    ?_
    ?_
  · intro t ht
    exact sol₁.toBanachEvolutionLocalSolution.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₁⟩
  · intro t ht
    exact sol₁.mem_state ⟨ht.1, le_trans (le_of_lt ht.2) hT₁⟩
  · intro t ht
    exact sol₂.toBanachEvolutionLocalSolution.equation_hasDerivWithinAt_Ici_of_mem_Ico
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₂⟩
  · intro t ht
    exact sol₂.mem_state ⟨ht.1, le_trans (le_of_lt ht.2) hT₂⟩
  · rw [sol₁.initial_eq, sol₂.initial_eq]

/-- State-set uniqueness read on any explicitly chosen shorter common terminal interval, when the
Lipschitz bound is available for all times. -/
theorem eqOn_Icc_of_lipschitzOn_of_le_terminal
    {K : ℝ≥0} (hF : ∀ t : ℝ, LipschitzOnWith K (F t) stateSet)
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T)
    (hT₁ : T ≤ sol₁.terminalTime) (hT₂ : T ≤ sol₂.terminalTime) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ T) := by
  let sol₁T := sol₁.restrictTerminal hT₀ hT₁
  let sol₂T := sol₂.restrictTerminal hT₀ hT₂
  have hEq := eqOn_Icc_of_lipschitzOn (F := F) (stateSet := stateSet)
    (t₀ := t₀) (u₀ := u₀) (K := K) hF sol₁T sol₂T
  intro t ht
  have ht' : t ∈ Icc t₀ (min sol₁T.terminalTime sol₂T.terminalTime) := by
    exact ⟨ht.1, le_min (by simpa [sol₁T] using ht.2) (by simpa [sol₂T] using ht.2)⟩
  simpa [sol₁T, sol₂T] using hEq ht'

/-- State-set uniqueness read on any explicitly chosen shorter common terminal interval, when the
Lipschitz bound is only known on that shorter interval. -/
theorem eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal
    {K : ℝ≥0}
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    {T : ℝ} (hT₀ : t₀ < T)
    (hT₁ : T ≤ sol₁.terminalTime) (hT₂ : T ≤ sol₂.terminalTime)
    (hF : ∀ t ∈ Icc t₀ T, LipschitzOnWith K (F t) stateSet) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ T) := by
  let sol₁T := sol₁.restrictTerminal hT₀ hT₁
  let sol₂T := sol₂.restrictTerminal hT₀ hT₂
  have hEq := eqOn_Icc_of_lipschitzOn_Icc (F := F) (stateSet := stateSet)
    (t₀ := t₀) (u₀ := u₀) (K := K) sol₁T sol₂T ?_
  · intro t ht
    have ht' : t ∈ Icc t₀ (min sol₁T.terminalTime sol₂T.terminalTime) := by
      exact ⟨ht.1, le_min (by simpa [sol₁T] using ht.2) (by simpa [sol₂T] using ht.2)⟩
    simpa [sol₁T, sol₂T] using hEq ht'
  · intro t ht
    have hmin_le_T : min sol₁T.terminalTime sol₂T.terminalTime ≤ T := by
      dsimp [sol₁T, sol₂T]
      exact min_le_left T T
    exact hF t ⟨ht.1, le_trans ht.2 hmin_le_T⟩

/-- Order-theoretic continuation bridge for state-preserving solutions: if
equality is available on every prescribed shorter common terminal, then it
holds on the open common interval. -/
theorem eqOn_Ico_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Ico t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact BanachEvolutionLocalSolution.eqOn_Ico_of_eqOn_Icc_of_le_terminal
    sol₁.toBanachEvolutionLocalSolution sol₂.toBanachEvolutionLocalSolution hEq

/-- State-set uniqueness on the open common interval when the Lipschitz bound is
available on every prescribed shorter common terminal interval. -/
theorem eqOn_Ico_of_lipschitzOn_Icc_of_le_terminal
    {K : ℝ≥0}
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hF : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      ∀ t ∈ Icc t₀ T, LipschitzOnWith K (F t) stateSet) :
    EqOn sol₁.curve sol₂.curve (Ico t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact eqOn_Ico_of_eqOn_Icc_of_le_terminal sol₁ sol₂ (fun hT₀ hT₁ hT₂ ↦
    eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal (F := F) (stateSet := stateSet)
      (t₀ := t₀) (u₀ := u₀) (K := K) sol₁ sol₂ hT₀ hT₁ hT₂
      (hF hT₀ hT₁ hT₂))

/-- A continuous linear map between Banach state spaces transports state-preserving solutions,
provided it maps the state set to the target state set, maps the initial condition, and commutes
with the vector fields on the source state set. -/
def mapContinuousLinearMapBetween
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G : ℝ → Y → Y} {targetStateSet : Set Y} {v₀ : Y}
    (L : X →L[ℝ] Y)
    (hL_state : ∀ x ∈ stateSet, L x ∈ targetStateSet)
    (hL_initial : L u₀ = v₀)
    (hcomm : ∀ t x, x ∈ stateSet → L (F t x) = G t (L x))
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    BanachEvolutionLocalSolutionIn G targetStateSet t₀ v₀ where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  curve := fun t ↦ L (sol.curve t)
  initial_eq := by
    rw [sol.initial_eq, hL_initial]
  equation := by
    intro t ht
    have hderiv :
        HasDerivWithinAt (fun τ ↦ L (sol.curve τ))
          (L (F t (sol.curve t))) (Icc t₀ sol.terminalTime) t := by
      simpa [Function.comp_def] using
        (L.hasFDerivAt.comp_hasFDerivWithinAt t
          (sol.toBanachEvolutionLocalSolution.equation ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa [hcomm t (sol.curve t) (sol.mem_state ht)] using hderiv
  mem_state := by
    intro t ht
    exact hL_state (sol.curve t) (sol.mem_state ht)

/-- A continuous linear symmetry of the Banach state space transports state-preserving solutions,
provided it preserves the state set, fixes the initial condition, and commutes with the vector field
on that state set. -/
def mapContinuousLinearMap
    (L : X →L[ℝ] X)
    (hL_state : MapsTo L stateSet stateSet)
    (hL_initial : L u₀ = u₀)
    (hcomm : ∀ t x, x ∈ stateSet → L (F t x) = F t (L x))
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    BanachEvolutionLocalSolutionIn F stateSet t₀ u₀ where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  curve := fun t ↦ L (sol.curve t)
  initial_eq := by
    rw [sol.initial_eq, hL_initial]
  equation := by
    intro t ht
    have hderiv :
        HasDerivWithinAt (fun τ ↦ L (sol.curve τ))
          (L (F t (sol.curve t))) (Icc t₀ sol.terminalTime) t := by
      simpa [Function.comp_def] using
        (L.hasFDerivAt.comp_hasFDerivWithinAt t
          (sol.toBanachEvolutionLocalSolution.equation ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa [hcomm t (sol.curve t) (sol.mem_state ht)] using hderiv
  mem_state := by
    intro t ht
    exact hL_state (sol.mem_state ht)

/-- If a state-preserving solution starts fixed by a continuous linear symmetry and the vector field
commutes with that symmetry on the state set, then uniqueness forces the whole solution to remain
fixed by the symmetry. This is the abstract Banach mechanism needed to later keep bilinear-form
solutions in the symmetric metric locus once the Ricci-DeTurck operator is shown to commute with
slot-swap. -/
theorem fixedBy_continuousLinearMap_of_lipschitzOn
    {K : ℝ≥0} (hF : ∀ t : ℝ, LipschitzOnWith K (F t) stateSet)
    (L : X →L[ℝ] X)
    (hL_state : MapsTo L stateSet stateSet)
    (hL_initial : L u₀ = u₀)
    (hcomm : ∀ t x, x ∈ stateSet → L (F t x) = F t (L x))
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → L (sol.curve t) = sol.curve t := by
  let mappedSol := mapContinuousLinearMap L hL_state hL_initial hcomm sol
  have hEq := eqOn_Icc_of_lipschitzOn (F := F) (stateSet := stateSet)
    (t₀ := t₀) (u₀ := u₀) (K := K) hF sol mappedSol
  intro t ht
  have hmappedTime : mappedSol.terminalTime = sol.terminalTime := by
    rfl
  have ht' : t ∈ Icc t₀ (min sol.terminalTime mappedSol.terminalTime) := by
    exact ⟨ht.1, le_min ht.2 (by rw [hmappedTime]; exact ht.2)⟩
  exact (hEq ht').symm

/-- Interval-scoped version of `fixedBy_continuousLinearMap_of_lipschitzOn`: it is enough for
the vector field to be Lipschitz on the solution's finite time interval. -/
theorem fixedBy_continuousLinearMap_of_lipschitzOn_Icc
    {K : ℝ≥0}
    (L : X →L[ℝ] X)
    (hL_state : MapsTo L stateSet stateSet)
    (hL_initial : L u₀ = u₀)
    (hcomm : ∀ t x, x ∈ stateSet → L (F t x) = F t (L x))
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hF : ∀ t ∈ Icc t₀ sol.terminalTime, LipschitzOnWith K (F t) stateSet) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → L (sol.curve t) = sol.curve t := by
  let mappedSol := mapContinuousLinearMap L hL_state hL_initial hcomm sol
  have hLipCommon :
      ∀ t ∈ Icc t₀ (min sol.terminalTime mappedSol.terminalTime),
        LipschitzOnWith K (F t) stateSet := by
    intro t ht
    exact hF t ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have hEq := eqOn_Icc_of_lipschitzOn_Icc (F := F) (stateSet := stateSet)
    (t₀ := t₀) (u₀ := u₀) (K := K) sol mappedSol hLipCommon
  intro t ht
  have hmappedTime : mappedSol.terminalTime = sol.terminalTime := by
    rfl
  have ht' : t ∈ Icc t₀ (min sol.terminalTime mappedSol.terminalTime) := by
    exact ⟨ht.1, le_min ht.2 (by rw [hmappedTime]; exact ht.2)⟩
  exact (hEq ht').symm

/-- If a continuous linear defect functional annihilates the vector field on the state set and
annihilates the initial value, then every state-preserving solution remains in the defect kernel.
This is the abstract "tangent to a closed linear constraint" mechanism needed when a geometric
evolution is known to have symmetric derivative data directly, without first constructing a global
slot-swap symmetry operator. -/
theorem continuousLinearMap_eq_zero_of_vectorField_eq_zero
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : X →L[ℝ] Y)
    (hC_initial : C u₀ = 0)
    (hC_vectorField : ∀ t x, x ∈ stateSet → C (F t x) = 0)
    (sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → C (sol.curve t) = 0 := by
  let defectCurve : ℝ → Y := fun t ↦ C (sol.curve t)
  have hderivIcc :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        HasDerivWithinAt defectCurve 0 (Icc t₀ sol.terminalTime) t := by
    intro t ht
    have hderiv :
        HasDerivWithinAt defectCurve (C (F t (sol.curve t)))
          (Icc t₀ sol.terminalTime) t := by
      simpa [defectCurve, Function.comp_def] using
        (C.hasFDerivAt.comp_hasFDerivWithinAt t
          (sol.toBanachEvolutionLocalSolution.equation ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa [hC_vectorField t (sol.curve t) (sol.mem_state ht)] using hderiv
  have hcont : ContinuousOn defectCurve (Icc t₀ sol.terminalTime) :=
    HasDerivWithinAt.continuousOn fun t ht ↦ hderivIcc ht
  have hderivIci :
      ∀ t ∈ Ico t₀ sol.terminalTime,
        HasDerivWithinAt defectCurve 0 (Ici t) t := by
    intro t ht
    have htIcc : t ∈ Icc t₀ sol.terminalTime := Ico_subset_Icc_self ht
    have hderiv :
        HasDerivWithinAt defectCurve (C (F t (sol.curve t))) (Ici t) t := by
      simpa [defectCurve, Function.comp_def] using
        (C.hasFDerivAt.comp_hasFDerivWithinAt t
          (sol.toBanachEvolutionLocalSolution.equation_hasDerivWithinAt_Ici_of_mem_Ico
            ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa [hC_vectorField t (sol.curve t) (sol.mem_state htIcc)] using hderiv
  have hconst := constant_of_has_deriv_right_zero
    (a := t₀) (b := sol.terminalTime) (f := defectCurve) hcont hderivIci
  intro t ht
  have ht0 : t₀ ∈ Icc t₀ sol.terminalTime := sol.toBanachEvolutionLocalSolution.initial_mem
  have h := hconst t ht
  simpa [defectCurve, sol.initial_eq, hC_initial] using h

end BanachEvolutionLocalSolutionIn

namespace BanachEvolutionLocalSolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {t₀ : ℝ} {u₀ : X}

/-- A Banach local solution can be shrunk to remain in any open state set containing its initial
value. This is the state-set bridge for non-autonomous Picard-Lindelof solutions. -/
theorem exists_restrict_in_isOpen
    (sol : BanachEvolutionLocalSolution F t₀ u₀)
    {stateSet : Set X}
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet) :
    ∃ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      sol'.terminalTime ≤ sol.terminalTime ∧
        ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol'.terminalTime → sol'.curve t = sol.curve t := by
  have hcont : ContinuousWithinAt sol.curve (Icc t₀ sol.terminalTime) t₀ :=
    sol.equation_initial.continuousWithinAt
  have hnear :
      {t : ℝ | sol.curve t ∈ stateSet} ∈ 𝓝[Icc t₀ sol.terminalTime] t₀ := by
    exact hcont.eventually_mem (hstate_open.mem_nhds (by simpa [sol.initial_eq] using hu₀))
  rcases Metric.mem_nhdsWithin_iff.mp hnear with ⟨δ, hδ, hδsub⟩
  let η := min (sol.terminalTime - t₀) δ / 2
  have hηpos : 0 < η := by
    dsimp [η]
    have hterm : 0 < sol.terminalTime - t₀ := sub_pos.mpr sol.initial_lt_terminal
    have hmin : 0 < min (sol.terminalTime - t₀) δ := lt_min hterm hδ
    linarith
  have hη_le_terminal_sub : η ≤ sol.terminalTime - t₀ := by
    dsimp [η]
    have hterm : 0 < sol.terminalTime - t₀ := sub_pos.mpr sol.initial_lt_terminal
    have hmin : 0 < min (sol.terminalTime - t₀) δ := lt_min hterm hδ
    have hη_le_min : min (sol.terminalTime - t₀) δ / 2 ≤
        min (sol.terminalTime - t₀) δ := by
      linarith
    exact le_trans hη_le_min (min_le_left _ _)
  have hη_lt_δ : η < δ := by
    dsimp [η]
    have hterm : 0 < sol.terminalTime - t₀ := sub_pos.mpr sol.initial_lt_terminal
    have hmin : 0 < min (sol.terminalTime - t₀) δ := lt_min hterm hδ
    have hη_lt_min : min (sol.terminalTime - t₀) δ / 2 <
        min (sol.terminalTime - t₀) δ := by
      linarith
    exact lt_of_lt_of_le hη_lt_min (min_le_right _ _)
  let T := t₀ + η
  have hTgt : t₀ < T := by
    dsimp [T]
    linarith
  have hTle : T ≤ sol.terminalTime := by
    dsimp [T]
    linarith
  refine ⟨{
    terminalTime := T
    initial_lt_terminal := hTgt
    curve := sol.curve
    initial_eq := sol.initial_eq
    equation := by
      intro t ht
      exact (sol.equation ⟨ht.1, le_trans ht.2 hTle⟩).mono
        (Icc_subset_Icc_right hTle)
    mem_state := by
      intro t ht
      have hdist : dist t t₀ < δ := by
        rw [Real.dist_eq]
        have hnonneg : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
        rw [abs_of_nonneg hnonneg]
        have hleη : t - t₀ ≤ η := by
          dsimp [T] at ht
          linarith [ht.2]
        linarith
      have htbig : t ∈ Icc t₀ sol.terminalTime := ⟨ht.1, le_trans ht.2 hTle⟩
      exact hδsub ⟨by simpa [Metric.mem_ball] using hdist, htbig⟩ }, hTle, by
    intro t _ht
    rfl⟩

end BanachEvolutionLocalSolution

/-- Picard-Lindelof produces a forward Banach-space local solution on any verified forward
interval.  This is the reusable ODE core needed after the Ricci-DeTurck PDE has been placed in a
Banach chart and its local Lipschitz bounds have been proved. -/
theorem IsPicardLindelof.exists_banachEvolutionLocalSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K) :
    Nonempty (BanachEvolutionLocalSolution F t₀ u₀) := by
  rcases hF.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨u, hu_init, hu_eq⟩
  exact ⟨{
    terminalTime := T
    initial_lt_terminal := hT
    curve := u
    initial_eq := hu_init
    equation := by
      intro t ht
      exact hu_eq t ht }⟩

/-- Picard-Lindelof plus openness of the state set gives a state-preserving forward local solution
after shrinking the interval. -/
theorem IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_mem_isOpen
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet) :
    Nonempty (BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) := by
  rcases IsPicardLindelof.exists_banachEvolutionLocalSolution hT hF with ⟨sol⟩
  rcases sol.exists_restrict_in_isOpen hstate_open hu₀ with ⟨sol', _hTle, _hcurve⟩
  exact ⟨sol'⟩

/-- Picard-Lindelof plus an open state set and a Lipschitz bound on that state set gives local
existence and uniqueness on the common interval among state-preserving solutions. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K Kstate : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (F t) stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_mem_isOpen hT hF
    hstate_open hu₀ with ⟨sol⟩
  exact ⟨sol, fun sol' ↦ BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn hLip sol sol'⟩

/-- Picard-Lindelof plus an open state set and a Lipschitz bound only on the Picard time interval
gives local existence and uniqueness on common intervals. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K Kstate : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (F t) stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases hF.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨u, hu_init, hu_eq⟩
  let baseSol : BanachEvolutionLocalSolution F t₀ u₀ :=
    { terminalTime := T
      initial_lt_terminal := hT
      curve := u
      initial_eq := hu_init
      equation := by
        intro t ht
        exact hu_eq t ht }
  rcases baseSol.exists_restrict_in_isOpen hstate_open hu₀ with ⟨sol, hsolT, _hcurve⟩
  refine ⟨sol, fun sol' ↦ ?_⟩
  refine BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc (K := Kstate) sol sol' ?_
  intro t ht
  have hmin_le_T : min sol.terminalTime sol'.terminalTime ≤ T :=
    le_trans (min_le_left _ _) hsolT
  exact hLip t ⟨ht.1, le_trans ht.2 hmin_le_T⟩

/-- Strengthened interval-scoped Picard-Lindelof/state-set theorem retaining the fact that the
constructed state-preserving solution was obtained by restricting the Picard solution to a subinterval
of `Icc t₀ T`. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc_terminal_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K Kstate : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (F t) stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases hF.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨u, hu_init, hu_eq⟩
  let baseSol : BanachEvolutionLocalSolution F t₀ u₀ :=
    { terminalTime := T
      initial_lt_terminal := hT
      curve := u
      initial_eq := hu_init
      equation := by
        intro t ht
        exact hu_eq t ht }
  rcases baseSol.exists_restrict_in_isOpen hstate_open hu₀ with ⟨sol, hsolT, _hcurve⟩
  refine ⟨sol, hsolT, fun sol' ↦ ?_⟩
  refine BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc (K := Kstate) sol sol' ?_
  intro t ht
  have hmin_le_T : min sol.terminalTime sol'.terminalTime ≤ T :=
    le_trans (min_le_left _ _) hsolT
  exact hLip t ⟨ht.1, le_trans ht.2 hmin_le_T⟩

/-- Picard-Lindelof plus an open state set and Lipschitz bounds on every
prescribed shorter terminal gives local existence and open-common-interval
uniqueness. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K Kstate : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T →
      ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate (F t) stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
        EqOn sol.curve sol'.curve (Ico t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases hF.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨u, hu_init, hu_eq⟩
  let baseSol : BanachEvolutionLocalSolution F t₀ u₀ :=
    { terminalTime := T
      initial_lt_terminal := hT
      curve := u
      initial_eq := hu_init
      equation := by
        intro t ht
        exact hu_eq t ht }
  rcases baseSol.exists_restrict_in_isOpen hstate_open hu₀ with ⟨sol, hsolT, _hcurve⟩
  refine ⟨sol, hsolT, fun sol' ↦ ?_⟩
  exact BanachEvolutionLocalSolutionIn.eqOn_Ico_of_lipschitzOn_Icc_of_le_terminal
    (F := F) (stateSet := stateSet) (t₀ := t₀) (u₀ := u₀) (K := Kstate) sol sol'
    (fun hS₀ hS₁ _hS₂ t ht ↦ hLip hS₀ (le_trans hS₁ hsolT) t ht)

/-- A `C^1` autonomous Banach-space vector field admits a forward local solution. This removes
manual Picard-Lindelof constants from the common autonomous case; a geometric Ricci-DeTurck
operator can use this once it has been realized as a `C^1` vector field in a Banach chart. -/
theorem exists_autonomous_banachEvolutionLocalSolution_of_contDiffAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : X → X} {t₀ : ℝ} {u₀ : X}
    (hF : ContDiffAt ℝ 1 F u₀) :
    Nonempty (BanachEvolutionLocalSolution (fun _ : ℝ ↦ F) t₀ u₀) := by
  rcases hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀ with
    ⟨u, hu₀, ε, hε, hu_eq⟩
  let T := t₀ + ε / 2
  have hT : t₀ < T := by
    dsimp [T]
    linarith
  exact ⟨{
    terminalTime := T
    initial_lt_terminal := hT
    curve := u
    initial_eq := hu₀
    equation := by
      intro t ht
      have ht_open : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
        dsimp [T] at ht
        constructor
        · linarith [ht.1, hε]
        · linarith [ht.2, hε]
      exact (hu_eq t ht_open).hasDerivWithinAt }⟩

/-- A `C^1` autonomous Banach-space vector field admits a forward local solution that stays in any
open state set containing the initial value, after shrinking the time interval. This is the
metric-locus preservation bridge needed once the finite-cover metric locus is used as the state
set for Ricci-DeTurck. -/
theorem exists_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_mem_isOpen
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X}
    (hF : ContDiffAt ℝ 1 F u₀) (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet) :
    Nonempty (BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ F) stateSet t₀ u₀) := by
  rcases hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀ with
    ⟨u, hu_init, ε, hε, hu_eq⟩
  have ht₀_open : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  have hcont : ContinuousAt u t₀ :=
    (hu_eq t₀ ht₀_open).continuousAt
  have hu_init_mem : u t₀ ∈ stateSet := by
    simpa [hu_init] using hu₀
  have hnear : ∀ᶠ t in 𝓝 t₀, u t ∈ stateSet :=
    hcont.eventually_mem (hstate_open.mem_nhds hu_init_mem)
  rcases Metric.eventually_nhds_iff.mp hnear with ⟨δ, hδ, hδmem⟩
  let η := min ε δ / 2
  have hηpos : 0 < η := by
    dsimp [η]
    have hmin : 0 < min ε δ := lt_min hε hδ
    linarith
  have hη_lt_ε : η < ε := by
    dsimp [η]
    have hmin_le : min ε δ ≤ ε := min_le_left _ _
    linarith
  have hη_lt_δ : η < δ := by
    dsimp [η]
    have hmin_le : min ε δ ≤ δ := min_le_right _ _
    linarith
  let T := t₀ + η
  have hT : t₀ < T := by
    dsimp [T]
    linarith
  exact ⟨{
    terminalTime := T
    initial_lt_terminal := hT
    curve := u
    initial_eq := hu_init
    equation := by
      intro t ht
      have ht_open : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
        dsimp [T] at ht
        constructor
        · linarith [ht.1, hε]
        · linarith [ht.2, hη_lt_ε]
      exact (hu_eq t ht_open).hasDerivWithinAt
    mem_state := by
      intro t ht
      have hdist : dist t t₀ < δ := by
        rw [Real.dist_eq]
        have hnonneg : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
        rw [abs_of_nonneg hnonneg]
        dsimp [T] at ht
        have hle : t - t₀ ≤ η := by linarith [ht.2]
        linarith
      exact hδmem hdist }⟩

/-- A globally Lipschitz autonomous `C^1` Banach vector field has a forward local solution that is
unique on the common interval among all forward local solutions with the same initial value. -/
theorem exists_unique_autonomous_banachEvolutionLocalSolution_of_contDiffAt_lipschitz
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : X → X} {t₀ : ℝ} {u₀ : X} {K : ℝ≥0}
    (hF : ContDiffAt ℝ 1 F u₀) (hLip : LipschitzWith K F) :
    ∃ sol : BanachEvolutionLocalSolution (fun _ : ℝ ↦ F) t₀ u₀,
      ∀ sol' : BanachEvolutionLocalSolution (fun _ : ℝ ↦ F) t₀ u₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases exists_autonomous_banachEvolutionLocalSolution_of_contDiffAt hF with ⟨sol⟩
  exact ⟨sol, fun sol' ↦
    BanachEvolutionLocalSolution.eqOn_Icc_of_lipschitz
      (F := fun _ : ℝ ↦ F) (K := K) (fun _ ↦ hLip) sol sol'⟩

/-- A `C^1` autonomous vector field that is Lipschitz on an open state set containing the initial
value has a state-preserving forward local solution, unique on common intervals among all
state-preserving solutions. -/
theorem exists_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_lipschitzOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X} {K : ℝ≥0}
    (hF : ContDiffAt ℝ 1 F u₀) (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : LipschitzOnWith K F stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ F) stateSet t₀ u₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ F) stateSet t₀ u₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases exists_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_mem_isOpen
    hF hstate_open hu₀ with ⟨sol⟩
  exact ⟨sol, fun sol' ↦
    BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn
      (F := fun _ : ℝ ↦ F) (K := K) (fun _ ↦ hLip) sol sol'⟩

/-- A `C^1` autonomous Banach vector field has a smaller open state neighborhood on which the
state-preserving local solution is unique. This replaces a global Lipschitz-on-state-set hypothesis by
the local Lipschitz neighborhood supplied by `ContDiffAt`, and is the analytic reduction needed when a
Ricci-DeTurck chart estimate is only local around the initial metric. -/
theorem exists_open_subset_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_mem_isOpen
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X}
    (hF : ContDiffAt ℝ 1 F u₀) (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet) :
    ∃ localStateSet : Set X,
      IsOpen localStateSet ∧ u₀ ∈ localStateSet ∧ localStateSet ⊆ stateSet ∧
      ∃ K : ℝ≥0, LipschitzOnWith K F localStateSet ∧
        ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ F) localStateSet t₀ u₀,
          ∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ F) localStateSet t₀ u₀,
            EqOn sol.curve sol'.curve
              (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases hF.exists_lipschitzOnWith with ⟨K, lipschitzSet, hlipschitzSet, hLip⟩
  have hstate_nhds : stateSet ∈ 𝓝 u₀ := hstate_open.mem_nhds hu₀
  have hcommon_nhds : stateSet ∩ lipschitzSet ∈ 𝓝 u₀ :=
    Filter.inter_mem (f := 𝓝 u₀) hstate_nhds hlipschitzSet
  rcases mem_nhds_iff.mp hcommon_nhds with
    ⟨localStateSet, hlocal_sub, hlocal_open, hu_local⟩
  have hlocal_state : localStateSet ⊆ stateSet := fun x hx ↦ (hlocal_sub hx).1
  have hlocal_lipschitz : localStateSet ⊆ lipschitzSet := fun x hx ↦ (hlocal_sub hx).2
  have hLip_local : LipschitzOnWith K F localStateSet := hLip.mono hlocal_lipschitz
  rcases exists_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_lipschitzOn
      (F := F) (stateSet := localStateSet) (t₀ := t₀) (u₀ := u₀) (K := K)
      hF hlocal_open hu_local hLip_local with
    ⟨sol, huniq⟩
  exact ⟨localStateSet, hlocal_open, hu_local, hlocal_state, K, hLip_local, sol, huniq⟩

namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance bilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance bilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
/-- Each bilinear-form coordinate component of a finite-cover Banach
metric-section solution satisfies the projected ODE as a whole continuous
bilinear form, before applying it to two vectors.  This is the readout shape
needed by the time-only variational gauge-pullback bridge. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) t := by
  let L :=
    coordReadoutContinuousLinearMap
      (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover i x
  simpa [L] using
    (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht)

/-- Right-interval version of
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`.
Coordinate components of the finite-cover Banach metric-section solution satisfy
the projected ODE as whole bilinear-form readouts, as a one-sided derivative on
`Ici t`. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) (Ici t) t := by
  let L :=
    coordReadoutContinuousLinearMap
      (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover i x
  simpa [L] using
    (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht)

/-- Interior moving-point version of
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`.
The finite-cover Banach derivative is first read as a whole compact coordinate
component, so the time-difference may be evaluated at a moving compact point
without differentiating the point curve. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using HasDerivAt.continuousMap_moving_eval_sub_const hcomponent hx

/-- Right-interval moving-point version of
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico`. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using HasDerivWithinAt.continuousMap_moving_eval_sub_const hcomponent hx

/-- Each scalar bilinear-coordinate component of a finite-cover Banach metric-section solution
satisfies the projected ODE.  This removes the last abstract readout from coordinate-level
Picard-to-metric derivative statements: the readout is the concrete finite-cover coordinate
evaluation supplied by `RiemannianSection`. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivAt_of_mem_Ioo
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) t := by
  let L :=
    coordBilinearFormReadoutContinuousLinearMap
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x u v
  simpa [L] using
    (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht)

/-- Right-interval version of
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivAt_of_mem_Ioo`.  Coordinate
components of the finite-cover Banach metric-section solution satisfy the projected ODE as a
one-sided derivative on `Ici t`. -/
theorem BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivWithinAt_Ici_of_mem_Ico
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) (Ici t) t := by
  let L :=
    coordBilinearFormReadoutContinuousLinearMap
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x u v
  simpa [L] using
    (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht)

/-- The existing finite-cover positive-definite metric locus is now a valid open state set for the
ambient continuous-section Banach evolution core: any `C^1` locally modeled vector field that is
Lipschitz on that open locus has a positive-definite-locus-preserving forward local solution,
unique among positive-definite-locus-preserving solutions.

This is still not the Ricci-DeTurck PDE theorem; it is the ambient Banach/open-state bridge that
the Ricci-DeTurck operator must instantiate after its `C^1`/Lipschitz parabolic estimates are
proved. The theorem below upgrades this to the symmetric-section Banach carrier. -/
theorem exists_unique_in_positiveDefiniteLocus_of_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact exists_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_lipschitzOn
    hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Symmetric finite-cover metric-locus bridge.  The vector field evolves in the closed submodule of
pointwise symmetric bilinear-form sections, and the open state set is the positive-definite locus
inside that Banach carrier.  This removes the previous ambient nonsymmetric section-space detour
from the Picard-Lindelöf part of the Ricci-DeTurck proof route. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  letI : CompleteSpace (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :=
    instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover
  exact @exists_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_lipschitzOn
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedAddCommGroupSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    A
    (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    t₀ g₀ K hA
    (isOpen_riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Local metric-locus version of
`exists_open_subset_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_mem_isOpen`.
For an autonomous `C^1` Banach-chart vector field, it produces a smaller open neighborhood inside the
positive-definite finite-cover metric locus, a local Lipschitz bound there, and a unique
state-preserving local solution. -/
theorem exists_open_subset_positiveDefiniteLocus_unique_of_contDiffAt
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∃ localStateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover),
      IsOpen localStateSet ∧ g₀ ∈ localStateSet ∧
      localStateSet ⊆ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover ∧
      ∃ K : ℝ≥0, LipschitzOnWith K A localStateSet ∧
        ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A) localStateSet t₀ g₀,
          ∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A) localStateSet t₀ g₀,
            EqOn sol.curve sol'.curve
              (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact exists_open_subset_unique_autonomous_banachEvolutionLocalSolutionIn_of_contDiffAt_mem_isOpen
    (F := A)
    (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (t₀ := t₀) (u₀ := g₀) hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀

/-- Non-autonomous finite-cover metric-locus bridge. Once a time-dependent Banach-chart vector
field satisfies Picard-Lindelof hypotheses and is locally Lipschitz on the positive-definite metric
locus, the local solution can be shrunk to remain positive-definite, with uniqueness among
state-preserving solutions. -/
theorem exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen
    (F := A) (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) hT hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Non-autonomous symmetric metric-locus bridge. Picard-Lindelöf hypotheses on the closed
symmetric section submodule produce a local solution that remains in the finite-cover
Riemannian-metric locus, unique among solutions preserving that locus. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact @IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedAddCommGroupSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    A
    (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    t₀ T hT g₀ a L Kpic Kstate hA
    (isOpen_riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Non-autonomous finite-cover metric-locus bridge with Lipschitz bounds required only on the
verified Picard time interval. -/
theorem exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc
    (F := A) (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) hT hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Interval-scoped non-autonomous symmetric metric-locus bridge, with Lipschitz bounds required
only on the Picard interval. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact @IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedAddCommGroupSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    A
    (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    t₀ T hT g₀ a L Kpic Kstate hA
    (isOpen_riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Interval-scoped positive-definite state-set bridge retaining the terminal-time bound supplied by
the Picard interval. -/
theorem exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc_terminal_le
    (F := A) (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) hT hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Interval-scoped positive-definite state-set bridge for local estimates supplied on every
prescribed shorter terminal.  The conclusion is open-common-interval uniqueness, matching the
largest interval that can be reconstructed from all shorter closed readouts. -/
theorem exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve (Ico t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc
    (F := A) (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) hT hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Interval-scoped symmetric metric-locus bridge retaining the terminal-time bound supplied by
the Picard interval. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact @IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_Icc_terminal_le
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedAddCommGroupSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    A
    (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    t₀ T hT g₀ a L Kpic Kstate hA
    (isOpen_riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Interval-scoped symmetric metric-locus bridge for local estimates supplied on every prescribed
shorter terminal.  It keeps the constructed solution inside the selected Picard interval and gives
uniqueness on the open common interval. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn A
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve (Ico t₀ (min sol.terminalTime sol'.terminalTime)) := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  exact @IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedAddCommGroupSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instNormedSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (instCompleteSpaceSymmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    A
    (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    t₀ T hT g₀ a L Kpic Kstate hA
    (isOpen_riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Variant of `exists_unique_in_positiveDefiniteLocus_of_contDiffAt_lipschitzOn` that also keeps
track of an abstract continuous-linear symmetry of the finite-cover metric model. If the symmetry
preserves positive definiteness, fixes the initial metric, and commutes with the vector field on the
positive-definite locus, uniqueness forces the produced solution to remain fixed by that symmetry.

The intended later instance is the slot-swap map on bundled bilinear-form sections; its fixed locus
is the symmetric metric locus. -/
theorem exists_unique_in_positiveDefiniteLocus_fixedBy_of_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (L : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (hL_state : MapsTo L
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hL_initial : L g₀ = g₀)
    (hcomm : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      L (A x) = A (L x)) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → L (sol.curve t) = sol.curve t := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  rcases exists_unique_in_positiveDefiniteLocus_of_contDiffAt_lipschitzOn
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA hg₀ hLip with
    ⟨sol, huniq⟩
  exact ⟨sol, huniq,
    BanachEvolutionLocalSolutionIn.fixedBy_continuousLinearMap_of_lipschitzOn
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := fun _ : ℝ ↦ A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀) (K := K)
      (fun _ ↦ hLip) L hL_state hL_initial (fun _ x hx ↦ hcomm x hx) sol⟩

/-- Time-dependent interval-scoped version of
`exists_unique_in_positiveDefiniteLocus_fixedBy_of_contDiffAt_lipschitzOn`. This is the symmetry
form needed when the parabolic estimates only provide Lipschitz control on the verified Picard
interval. -/
theorem exists_unique_in_positiveDefiniteLocus_fixedBy_of_isPicardLindelof_lipschitzOn_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (S : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (hS_state : MapsTo S
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hS_initial : S g₀ = g₀)
    (hcomm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      S (A t x) = A t (S x)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → S (sol.curve t) = sol.curve t := by
  letI : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := hcomplete
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀ hLip with
    ⟨sol, hsolT, huniq⟩
  exact ⟨sol, hsolT, huniq,
    BanachEvolutionLocalSolutionIn.fixedBy_continuousLinearMap_of_lipschitzOn_Icc
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀) (K := Kstate)
      S hS_state hS_initial hcomm sol
      (fun t ht ↦ hLip t ⟨ht.1, le_trans ht.2 hsolT⟩)⟩

/-- If a continuous-linear defect map cuts out the closed symmetric locus and annihilates the
vector field on the positive-definite state set, then the positive-definite local solution produced
by the Banach core actually remains in the full symmetric positive-definite locus. This is a direct
"tangent to the symmetric constraint" alternative to proving commutation with a global slot-swap
operator. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] Y)
    (hker_iff : ∀ x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
      C x = 0 ↔ x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hC_A : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover → C (A x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_of_contDiffAt_lipschitzOn
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA hg₀.2 hLip with
    ⟨sol, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → C (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := fun _ : ℝ ↦ A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      C ((hker_iff g₀).2 hg₀.1) (fun _ x hx ↦ hC_A x hx) sol
  exact ⟨sol, huniq, by
    intro t ht
    exact ⟨(hker_iff (sol.curve t)).1 (hdefect ht), sol.mem_state ht⟩⟩

/-- Concrete finite-cover version of
`exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_contDiffAt_lipschitzOn` using the
coordinatewise antisymmetric-defect continuous linear map from `RiemannianSection`. This is the
closest current analytic bridge to the Ricci-DeTurck symmetry obligation: after the vector field is
constructed in the finite-cover section model, it suffices to prove its coordinatewise
antisymmetric defect vanishes on the positive-definite state set. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_contDiffAt_lipschitzOn
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA hg₀ hLip
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hdefect_A

/-- Interval-scoped direct defect route to the finite-cover symmetric positive-definite locus. This
is the local-in-time version needed when the Banach-chart estimates are only available on the
verified Picard interval. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] Y)
    (hker_iff : ∀ x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
      C x = 0 ↔ x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hC_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover → C (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip with
    ⟨sol, hsolT, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → C (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      C ((hker_iff g₀).2 hg₀.1) hC_A sol
  exact ⟨sol, hsolT, huniq, by
    intro t ht
    exact ⟨(hker_iff (sol.curve t)).1 (hdefect ht), sol.mem_state ht⟩⟩

/-- Concrete coordinatewise-defect version of the interval-scoped direct defect route. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀ hLip
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hdefect_A

/-- Restricted-terminal direct defect route to the finite-cover symmetric positive-definite locus.
The Lipschitz estimate is only required on each prescribed shorter closed terminal, and uniqueness is
therefore recovered on the open common interval. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] Y)
    (hker_iff : ∀ x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
      C x = 0 ↔ x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hC_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover → C (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_restricted_Icc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip with
    ⟨sol, hsolT, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime → C (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      C ((hker_iff g₀).2 hg₀.1) hC_A sol
  exact ⟨sol, hsolT, huniq, by
    intro t ht
    exact ⟨(hker_iff (sol.curve t)).1 (hdefect ht), sol.mem_state ht⟩⟩

/-- Concrete coordinatewise-defect version of the restricted-terminal direct defect route. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀ hLip
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hdefect_A

/-- Non-autonomous finite-cover symmetry bridge. If a time-dependent Banach-chart vector field
satisfies Picard-Lindelof hypotheses, is Lipschitz on the positive-definite locus, and takes
positive-definite inputs to pointwise symmetric sections at every time, then the state-preserving
local solution remains in the symmetric positive-definite metric locus. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip with
    ⟨sol, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
          (F := F) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      ((_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀).2 hg₀.1)
      (fun t x hx =>
        (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
          (M := M) (F := F) (W := W)
          x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))
      sol
  exact ⟨sol, huniq, by
    intro t ht
    exact ⟨(_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover (sol.curve t)).1 (hdefect ht),
      sol.mem_state ht⟩⟩

/-- Non-autonomous finite-cover symmetry bridge with Lipschitz bounds required only on the verified
Picard time interval. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip with
    ⟨sol, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
          (F := F) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      ((_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀).2 hg₀.1)
      (fun t x hx =>
        (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
          (M := M) (F := F) (W := W)
          x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))
      sol
  exact ⟨sol, huniq, by
    intro t ht
    exact ⟨(_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover (sol.curve t)).1 (hdefect ht),
      sol.mem_state ht⟩⟩

/-- Terminal-time retaining version of the interval-scoped non-autonomous finite-cover symmetry
bridge. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip with
    ⟨sol, hsolT, huniq⟩
  have hdefect :
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
          (F := F) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover (sol.curve t) = 0 :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_eq_zero_of_vectorField_eq_zero
      (X := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      (F := A)
      (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := t₀) (u₀ := g₀)
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
      ((_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀).2 hg₀.1)
      (fun t x hx =>
        (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
          (M := M) (F := F) (W := W)
          x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))
      sol
  exact ⟨sol, hsolT, huniq, by
    intro t ht
    exact ⟨(_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover (sol.curve t)).1 (hdefect ht),
      sol.mem_state ht⟩⟩

/-- Restricted-terminal version of the non-autonomous finite-cover symmetry bridge.  Estimates are
provided on every shorter closed terminal, and uniqueness is recovered on the open common interval. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀ hLip
    (by
      intro t x hx
      exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))

/-- Concrete finite-cover version where the vector field is assumed directly to take
positive-definite inputs to symmetric sections. The coordinatewise antisymmetric-defect map then
vanishes automatically, so the local solution stays in the symmetric positive-definite locus.

For a future Ricci-DeTurck specialization this means pointwise tensor symmetry of the operator can be
used directly, without separately restating it as a coordinatewise defect equation. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricVectorField_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_contDiffAt_lipschitzOn
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA hg₀ hLip
    (fun x hx =>
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover (A x)).2 (hA_symm x hx))

/-- Version of
`exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_contDiffAt_lipschitzOn` whose
initial datum is an actual bundled continuous Riemannian metric. This removes the manual
finite-cover metric-locus membership proof from the future Ricci-DeTurck Banach-chart
specialization. -/
theorem exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover))
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_contDiffAt_lipschitzOn
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip hdefect_A

/-- Continuous-Riemannian-metric initial-data version of
`exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricVectorField_contDiffAt_lipschitzOn`.
It reduces the future Ricci-DeTurck metric-locus theorem to the usual analytic hypotheses plus
direct pointwise symmetry of the finite-cover vector field. -/
theorem exists_unique_from_continuousRiemannianMetric_of_symmetricVectorField_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover))
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricVectorField_contDiffAt_lipschitzOn
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip hA_symm

/-- Continuous-Riemannian-metric initial-data version of the interval-scoped coordinatewise-defect
bridge. This is the local-in-time shape needed by parabolic Ricci-DeTurck estimates: once the
Banach vector field is known to be tangent to the symmetric constraint on the Picard interval, the
solution starting from a bundled continuous Riemannian metric stays in the symmetric
positive-definite locus and retains the terminal-time bound. -/
theorem exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip hdefect_A

/-- Continuous-Riemannian-metric initial-data version of the restricted-terminal
coordinatewise-defect bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hdefect_A : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover (A t x) = 0) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip hdefect_A

/-- Continuous-Riemannian-metric initial-data version of the terminal-time interval theorem for
time-dependent vector fields that are already pointwise symmetric on the positive-definite state
set. This packages the common route from geometric Ricci-DeTurck RHS symmetry to the coordinatewise
defect condition used by the interval-scoped Banach bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete g₀ hT hA hLip
    (by
      intro t x hx
      exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))

/-- Continuous-Riemannian-metric initial-data version of the restricted-terminal
non-autonomous symmetric-vector-field bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete g₀ hT hA hLip
    (by
      intro t x hx
      exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))

/-- Continuous-Riemannian-metric initial-data version of the non-autonomous symmetric-vector-field
bridge. This is the time-dependent analogue of
`exists_unique_from_continuousRiemannianMetric_of_symmetricVectorField_contDiffAt_lipschitzOn`. -/
theorem exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_symm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      A t x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip hA_symm

/-- Ricci-DeTurck Banach-chart bridge: if the autonomous finite-cover vector field agrees pointwise,
on the positive-definite locus, with an intrinsic geometric Ricci-DeTurck right-hand side, then the
local Banach solution produced from a continuous Riemannian initial metric stays in the symmetric
positive-definite metric locus.

The remaining analytic specialization is to construct such an `A` from a quasilinear parabolic
Ricci-DeTurck chart and prove its `C^1`/Lipschitz estimates.  The geometric symmetry obligation is
discharged here by `intrinsicRicciDeTurckRHS_symm`. -/
theorem exists_unique_from_continuousRiemannianMetric_of_geometricRicciDeTurckRHS_contDiffAt_lipschitzOn
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover))
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_geometric : ∀ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)) (t : ℝ),
        ∀ (x : M) (u v : TangentSpace I x),
          A s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_symmetricVectorField_contDiffAt_lipschitzOn
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete g₀ hA hLip
    (by
      intro s hs
      rcases hA_geometric s hs with ⟨g, background, t, hAeq⟩
      intro x u v
      calc
        A s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v :=
          hAeq x u v
        _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u :=
          intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background t x u v
        _ = A s x v u := (hAeq x v u).symm)

/-- Time-dependent Ricci-DeTurck Banach-chart bridge. If a time-dependent finite-cover vector field
satisfies Picard-Lindelof/Lipschitz hypotheses and agrees pointwise, on the positive-definite locus,
with an intrinsic geometric Ricci-DeTurck right-hand side at the same time, then the local Banach
solution produced from a continuous Riemannian initial metric stays in the symmetric
positive-definite metric locus.

This is the non-autonomous counterpart of
`exists_unique_from_continuousRiemannianMetric_of_geometricRicciDeTurckRHS_contDiffAt_lipschitzOn`.
The remaining analytic specialization is still the parabolic construction of the chart vector field
and its estimates. -/
theorem exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip
    (by
      intro τ s hs
      rcases hA_geometric τ s hs with ⟨g, background, hAeq⟩
      intro x u v
      calc
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
          hAeq x u v
        _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
          intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
        _ = A τ s x v u := (hAeq x v u).symm)

/-- Time-dependent Ricci-DeTurck Banach-chart bridge with Lipschitz control required only on the
verified Picard interval. This is the estimate shape expected from a local parabolic theorem. -/
theorem exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_Icc
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover g₀)
    hLip
    (by
      intro τ s hs
      rcases hA_geometric τ s hs with ⟨g, background, hAeq⟩
      intro x u v
      calc
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
          hAeq x u v
        _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
          intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
        _ = A τ s x v u := (hAeq x v u).symm)

/-- Terminal-time retaining version of the interval-scoped time-dependent Ricci-DeTurck
Banach-chart bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn_Icc_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_Icc_terminal_le
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete g₀ hT hA hLip
    (by
      intro τ s hs
      rcases hA_geometric τ s hs with ⟨g, background, hAeq⟩
      intro x u v
      calc
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
          hAeq x u v
        _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
          intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
        _ = A τ s x v u := (hAeq x v u).symm)

/-- Restricted-terminal time-dependent Ricci-DeTurck Banach-chart bridge.  The Lipschitz
hypothesis is required only on every shorter closed terminal, and uniqueness is therefore stated on
the open common interval. -/
theorem exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn_restricted_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover))
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate
      (A t) (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hA_geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete g₀ hT hA hLip
    (by
      intro τ s hs
      rcases hA_geometric τ s hs with ⟨g, background, hAeq⟩
      intro x u v
      calc
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
          hAeq x u v
        _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
          intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
        _ = A τ s x v u := (hAeq x v u).symm)

/-- Interval-scoped time-dependent Banach chart whose symmetry preservation obligation is expressed
as the concrete coordinatewise antisymmetric-defect equation. This separates the local parabolic
Picard/Lipschitz estimates from the weaker tangent-to-the-symmetric-locus condition, before any
geometric Ricci-DeTurck RHS identification is available. -/
structure TimeDependentCoordwiseDefectMetricBanachChartOnIcc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0) where
  /-- The time-dependent Banach vector field on finite-cover bilinear-form sections. -/
  A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover
  /-- The Picard-Lindelof interval is genuinely forward. -/
  hT : t₀ < T
  /-- Picard-Lindelof hypotheses for the Banach representative at the initial metric. -/
  picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
    ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
    (⟨g₀.toSection, g₀.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic
  /-- Lipschitz control on the positive-definite locus along the verified Picard interval. -/
  lipschitzOn_Icc : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
    (positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
  /-- The Banach vector field is tangent to the coordinatewise symmetric constraint. -/
  coordwiseDefect : ∀ t s, s ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover →
    _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover (A t s) = 0

/-- Extract the symmetric positive-definite local Banach metric evolution from an interval chart
whose remaining symmetry input is the coordinatewise antisymmetric-defect equation. -/
theorem TimeDependentCoordwiseDefectMetricBanachChartOnIcc.exists_unique_symmetricPositiveDefinite_terminal_le
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF BilW (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F W}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentCoordwiseDefectMetricBanachChartOnIcc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_Icc_terminal_le
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance g₀
    chart.hT chart.picard chart.lipschitzOn_Icc chart.coordwiseDefect

/-- Non-terminal extractor obtained by forgetting the terminal-time bound from the interval
coordinatewise-defect chart. -/
theorem TimeDependentCoordwiseDefectMetricBanachChartOnIcc.exists_unique_symmetricPositiveDefinite
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF BilW (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F W}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentCoordwiseDefectMetricBanachChartOnIcc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, _hsolT, huniq, hsymm⟩
  exact ⟨sol, huniq, hsymm⟩

/-- Restricted-terminal coordinatewise-defect chart.  Its Lipschitz obligation is local on every
shorter closed terminal, exactly matching the estimate shape used to derive open-common uniqueness. -/
structure TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F W)
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0) where
  /-- The time-dependent Banach vector field on finite-cover bilinear-form sections. -/
  A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover
  /-- The Picard-Lindelof interval is genuinely forward. -/
  hT : t₀ < T
  /-- Picard-Lindelof hypotheses for the Banach representative at the initial metric. -/
  picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
    ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
    (⟨g₀.toSection, g₀.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic
  /-- Lipschitz control on each prescribed shorter closed terminal. -/
  lipschitzOn_restricted_Icc :
    ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
  /-- The Banach vector field is tangent to the coordinatewise symmetric constraint. -/
  coordwiseDefect : ∀ t s, s ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover →
    _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover (A t s) = 0

/-- Extract the symmetric positive-definite local Banach metric evolution from a restricted-terminal
coordinatewise-defect chart. -/
theorem TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF BilW (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F W}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc
    (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance g₀
    chart.hT chart.picard chart.lipschitzOn_restricted_Icc chart.coordwiseDefect

/-- An interval-scoped coordinatewise-defect chart also supplies restricted-terminal estimates. -/
def TimeDependentCoordwiseDefectMetricBanachChartOnIcc.toRestrictedIcc
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF BilW (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F W}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentCoordwiseDefectMetricBanachChartOnIcc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := chart.A
  hT := chart.hT
  picard := chart.picard
  lipschitzOn_restricted_Icc := by
    intro S _hS hST t ht
    exact chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hST⟩
  coordwiseDefect := chart.coordwiseDefect

/-- A proof-bearing package for a time-dependent finite-cover Banach representative of the
Ricci-DeTurck right-hand side around a continuous Riemannian initial metric.

The fields are exactly the analytic obligations left for the genuine quasilinear parabolic
specialization: completeness of the chosen finite-cover section model, Picard-Lindelof estimates,
Lipschitz control on the positive-definite metric locus, and pointwise identification with the
intrinsic geometric Ricci-DeTurck RHS. The theorem below extracts the symmetric positive-definite
local Banach metric evolution, so later PDE work can target these fields directly. -/
structure TimeDependentGeometricRicciDeTurckBanachChart
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0) where
  /-- The time-dependent Banach representative of the Ricci-DeTurck operator. -/
  A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
  /-- The Picard-Lindelof interval is genuinely forward. -/
  hT : t₀ < T
  /-- Picard-Lindelof hypotheses for the Banach representative at the initial metric. -/
  picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
    ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
    (⟨g₀.toSection, g₀.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic
  /-- Lipschitz control on the positive-definite metric locus. -/
  lipschitz : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
  /-- Pointwise identification with the intrinsic geometric Ricci-DeTurck RHS. -/
  geometric : ∀ τ s, s ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover →
    ∃ (g : MetricFamily (I := I) (M := M))
      (background : ConnectionFamily (I := I) (M := M)),
      ∀ (x : M) (u v : TangentSpace I x),
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v

/-- The geometric Ricci-DeTurck identification in a global Banach chart forces each chart
right-hand side to be symmetric on the positive-definite locus. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.A_mem_symmetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate)
    (τ : ℝ)
    {sec : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hsec : sec ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) :
    chart.A τ sec ∈ symmetricLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover := by
  rcases chart.geometric τ sec hsec with ⟨g, background, hAeq⟩
  intro x u v
  calc
    chart.A τ sec x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
      hAeq x u v
    _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
      intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
    _ = chart.A τ sec x v u := (hAeq x v u).symm

/-- The global geometric Ricci-DeTurck identification supplies the coordinatewise
antisymmetric-defect equation consumed by the interval defect chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.A_coordwiseSymmetryDefect_eq_zero
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate)
    (τ : ℝ)
    {sec : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hsec : sec ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) :
    _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover (chart.A τ sec) = 0 := by
  exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover (chart.A τ sec)).2
    (chart.A_mem_symmetricLocus τ hsec)

/-- Extract the local symmetric positive-definite Banach metric evolution from a packaged
time-dependent geometric Ricci-DeTurck Banach chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_symmetricPositiveDefinite
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance g₀
    chart.hT chart.picard chart.lipschitz chart.geometric

/-- Interval-scoped Ricci-DeTurck Banach-chart package. Compared to
`TimeDependentGeometricRicciDeTurckBanachChart`, the Lipschitz obligation only lives on `Icc t₀ T`,
matching local parabolic estimates and avoiding an artificial global-in-time bound. -/
structure TimeDependentGeometricRicciDeTurckBanachChartOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0) where
  /-- The time-dependent Banach representative of the Ricci-DeTurck operator. -/
  A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
  /-- The Picard-Lindelof interval is genuinely forward. -/
  hT : t₀ < T
  /-- Picard-Lindelof hypotheses for the Banach representative at the initial metric. -/
  picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
    ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
    (⟨g₀.toSection, g₀.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic
  /-- Lipschitz control on the positive-definite metric locus along the Picard interval. -/
  lipschitzOn_Icc : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
  /-- Pointwise identification with the intrinsic geometric Ricci-DeTurck RHS. -/
  geometric : ∀ τ s, s ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover →
    ∃ (g : MetricFamily (I := I) (M := M))
      (background : ConnectionFamily (I := I) (M := M)),
      ∀ (x : M) (u v : TangentSpace I x),
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v

/-- The geometric Ricci-DeTurck identification in an interval-scoped Banach chart forces each chart
right-hand side to be symmetric on the positive-definite locus. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.A_mem_symmetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate)
    (τ : ℝ)
    {sec : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hsec : sec ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) :
    chart.A τ sec ∈ symmetricLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover := by
  rcases chart.geometric τ sec hsec with ⟨g, background, hAeq⟩
  intro x u v
  calc
    chart.A τ sec x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
      hAeq x u v
    _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
      intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
    _ = chart.A τ sec x v u := (hAeq x v u).symm

/-- The geometric Ricci-DeTurck identification also supplies the concrete coordinatewise
antisymmetric-defect equation consumed by the interval defect chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.A_coordwiseSymmetryDefect_eq_zero
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate)
    (τ : ℝ)
    {sec : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hsec : sec ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) :
    _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
      (F := F) (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover (chart.A τ sec) = 0 := by
  exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover (chart.A τ sec)).2
    (chart.A_mem_symmetricLocus τ hsec)

/-- Forget the geometric Ricci-DeTurck identification down to the interval coordinatewise-defect
chart interface. This exposes a smaller target for the analytic PDE construction: once the
coordinatewise defect is known to vanish, the metric-locus evolution no longer needs the full
geometric RHS identity. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.toCoordwiseDefectMetricChartOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentCoordwiseDefectMetricBanachChartOnIcc
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := chart.A
  hT := chart.hT
  picard := chart.picard
  lipschitzOn_Icc := chart.lipschitzOn_Icc
  coordwiseDefect := by
    intro τ sec hsec
    exact chart.A_coordwiseSymmetryDefect_eq_zero τ hsec

/-- A globally Lipschitz time-dependent chart is, in particular, an interval-scoped chart on its
Picard interval. -/
def TimeDependentGeometricRicciDeTurckBanachChart.toOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := chart.A
  hT := chart.hT
  picard := chart.picard
  lipschitzOn_Icc := by
    intro t _ht
    exact chart.lipschitz t
  geometric := chart.geometric

/-- Forget a globally Lipschitz geometric Ricci-DeTurck chart directly down to the interval
coordinatewise-defect chart interface on its Picard interval. -/
def TimeDependentGeometricRicciDeTurckBanachChart.toCoordwiseDefectMetricChartOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentCoordwiseDefectMetricBanachChartOnIcc
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate :=
  chart.toOnIcc.toCoordwiseDefectMetricChartOnIcc

/-- Extract the symmetric positive-definite Banach metric evolution from an interval-scoped
time-dependent geometric Ricci-DeTurck Banach chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_symmetricPositiveDefinite
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact TimeDependentCoordwiseDefectMetricBanachChartOnIcc.exists_unique_symmetricPositiveDefinite
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    (chart := chart.toCoordwiseDefectMetricChartOnIcc)

/-- Terminal-time retaining extractor for an interval-scoped time-dependent geometric Ricci-DeTurck
Banach chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_symmetricPositiveDefinite_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact TimeDependentCoordwiseDefectMetricBanachChartOnIcc.exists_unique_symmetricPositiveDefinite_terminal_le
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    (chart := chart.toCoordwiseDefectMetricChartOnIcc)

/-- Terminal-time retaining extractor for the globally Lipschitz time-dependent geometric
Ricci-DeTurck Banach chart, routed through the smaller coordinatewise-defect interface. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_symmetricPositiveDefinite_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact TimeDependentCoordwiseDefectMetricBanachChartOnIcc.exists_unique_symmetricPositiveDefinite_terminal_le
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    (chart := chart.toCoordwiseDefectMetricChartOnIcc)

/-- Restricted-terminal Ricci-DeTurck Banach-chart package.  This is the version whose analytic
estimate field supplies Lipschitz control on every shorter closed terminal, yielding open-common
uniqueness for the extracted local metric evolution. -/
structure TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0) where
  /-- The time-dependent Banach representative of the Ricci-DeTurck operator. -/
  A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
  /-- The Picard-Lindelof interval is genuinely forward. -/
  hT : t₀ < T
  /-- Picard-Lindelof hypotheses for the Banach representative at the initial metric. -/
  picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
    ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
    (⟨g₀.toSection, g₀.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic
  /-- Lipschitz control on the positive-definite metric locus for every shorter closed terminal. -/
  lipschitzOn_restricted_Icc :
    ∀ {S : ℝ}, t₀ < S → S ≤ T → ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
  /-- Pointwise identification with the intrinsic geometric Ricci-DeTurck RHS. -/
  geometric : ∀ τ s, s ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover →
    ∃ (g : MetricFamily (I := I) (M := M))
      (background : ConnectionFamily (I := I) (M := M)),
      ∀ (x : M) (u v : TangentSpace I x),
        A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v

/-- Forget a restricted-terminal geometric Ricci-DeTurck chart down to the coordinatewise-defect
interface. -/
def TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc.toCoordwiseDefectMetricChartRestrictedIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := chart.A
  hT := chart.hT
  picard := chart.picard
  lipschitzOn_restricted_Icc := chart.lipschitzOn_restricted_Icc
  coordwiseDefect := by
    intro τ sec hsec
    exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover (chart.A τ sec)).2
      (by
        rcases chart.geometric τ sec hsec with ⟨g, background, hAeq⟩
        intro x u v
        calc
          chart.A τ sec x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v :=
            hAeq x u v
          _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x v u :=
            intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background τ x u v
          _ = chart.A τ sec x v u := (hAeq x v u).symm)

/-- Extract the symmetric positive-definite Banach metric evolution from a restricted-terminal
geometric Ricci-DeTurck Banach chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Ico t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    (chart := chart.toCoordwiseDefectMetricChartRestrictedIcc)

/-- An interval-scoped geometric Ricci-DeTurck chart also supplies restricted-terminal estimates. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.toRestrictedIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := chart.A
  hT := chart.hT
  picard := chart.picard
  lipschitzOn_restricted_Icc := by
    intro S _hS hST t ht
    exact chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hST⟩
  geometric := chart.geometric

/-- A globally Lipschitz geometric Ricci-DeTurck chart also supplies restricted-terminal estimates. -/
def TimeDependentGeometricRicciDeTurckBanachChart.toRestrictedIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate :=
  chart.toOnIcc.toRestrictedIcc

/-- Reify a symmetric positive-definite state of a finite-cover Banach local solution as a bundled
continuous Riemannian metric. -/
def BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    {t : ℝ} (ht : t ∈ Icc t₀ sol.terminalTime) :
    _root_.Bundle.ContinuousRiemannianMetric F W :=
  _root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
    (sol.curve t) (hsymm ht)

/-- Reifying a Banach metric-section state as a continuous Riemannian metric and then forgetting
back to the continuous-section carrier recovers the original Banach state. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    {t : ℝ} (ht : t ∈ Icc t₀ sol.terminalTime) :
    (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
        sol hsymm ht).toSection,
      (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
        sol hsymm ht).continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) = sol.curve t := by
  ext x u v
  rfl

/-- Reifying the initial state of a Banach local solution recovers the original continuous
Riemannian metric. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_initial_eq
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀
      (⟨g.toSection, g.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover))
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm
      sol.toBanachEvolutionLocalSolution.initial_mem = g := by
  ext x u v
  change sol.curve t₀ x u v = g.inner x u v
  have hcurve := congrArg
    (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover => s x u v)
    sol.initial_eq
  simpa [_root_.Bundle.ContinuousRiemannianMetric.toSection] using hcurve

/-- Reify a Banach metric-section local solution as a metric-valued curve, using a fixed default
metric away from the local solution interval. -/
noncomputable def BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W) :
    ℝ → _root_.Bundle.ContinuousRiemannianMetric F W :=
  fun t ↦
    if ht : t ∈ Icc t₀ sol.terminalTime then
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm ht
    else
      defaultMetric

/-- On the local solution interval, the reified metric curve has the same inner products as the
underlying Banach section curve. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_inner_eq_of_mem
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W)
    {t : ℝ} (ht : t ∈ Icc t₀ sol.terminalTime)
    (x : M) (u v : W x) :
    (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
      sol hsymm defaultMetric t).inner x u v = sol.curve t x u v := by
  change ((if h : t ∈ Icc t₀ sol.terminalTime then
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm h
    else defaultMetric).inner x u v) = sol.curve t x u v
  simp [ht, BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt]

/-- The reified continuous-Riemannian-metric curve inherits the finite-cover
coordinate projected ODE as a whole bilinear-form readout on the interior of the
Banach local interval. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo
      (M := M) (F := F) (W := W) sol i x ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
        =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm hτ
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, hτ, hsec]
  exact hproj.congr_of_eventuallyEq hEq

/-- The reified continuous-Riemannian-metric curve inherits the finite-cover coordinate projected
ODE on the interior of the Banach local interval.  This is the concrete-coordinate version of the
Picard-to-metric derivative bridge for the continuous metric curve. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadout_hasDerivAt_of_mem_Ioo
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x u v)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x u v) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivAt_of_mem_Ioo
      (M := M) (F := F) (W := W) sol i x u v ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
        =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm hτ
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, hτ, hsec]
  exact hproj.congr_of_eventuallyEq hEq

/-- One-sided version of
`BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`.
The reified continuous-Riemannian-metric curve has the finite-cover coordinate
projected ODE as a whole bilinear-form readout, as a right derivative on
`Ici t`. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico
      (M := M) (F := F) (W := W) sol i x ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
        =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm hτ
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, hτ, hsec]
  have hEq_t :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
        (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
            (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
            sol hsymm defaultMetric t).toSection,
          (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
            (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
            sol hsymm defaultMetric t).continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover)).1 i x =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
        (sol.curve t)).1 i x := by
    have htIcc : t ∈ Icc t₀ sol.terminalTime := Ico_subset_Icc_self ht
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm htIcc
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, htIcc, hsec]
  exact hproj.congr_of_eventuallyEq hEq hEq_t

/-- One-sided version of
`BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadout_hasDerivAt_of_mem_Ioo`.
The reified continuous-Riemannian-metric curve has the finite-cover coordinate projected ODE as a
right derivative on `Ici t`. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_coordBilinearFormReadout_hasDerivWithinAt_Ici_of_mem_Ico
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric : _root_.Bundle.ContinuousRiemannianMetric F W)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x u v)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x u v) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivWithinAt_Ici_of_mem_Ico
      (M := M) (F := F) (W := W) sol i x u v ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).toSection,
            (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
              sol hsymm defaultMetric τ).continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
        =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm hτ
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, hτ, hsec]
  have hEq_t :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
        (⟨(BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
            (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
            sol hsymm defaultMetric t).toSection,
          (BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
            (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
            sol hsymm defaultMetric t).continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover)).1 i x u v =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
        (sol.curve t)).1 i x u v := by
    have htIcc : t ∈ Icc t₀ sol.terminalTime := Ico_subset_Icc_self ht
    have hsec :=
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_toSection_eq
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm htIcc
    simp [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve, htIcc, hsec]
  exact hproj.congr_of_eventuallyEq hEq hEq_t

/-- If the default metric is the initial metric, the reified metric curve starts at the original
continuous Riemannian metric. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_initial_eq
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀
      (⟨g.toSection, g.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover))
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover) :
    BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover sol hsymm g t₀ = g := by
  unfold BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
  rw [dif_pos sol.toBanachEvolutionLocalSolution.initial_mem]
  exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt_initial_eq
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g sol hsymm

/-- Banach-curve uniqueness reifies to uniqueness of the continuous-Riemannian-metric curves on the
common local interval. The arbitrary default metrics used off the interval do not matter. -/
theorem BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_eq_on_common_interval
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    (sol sol' : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (hEq : EqOn sol.curve sol'.curve (Icc t₀ (min sol.terminalTime sol'.terminalTime)))
    (hsymm : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
      sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hsymm' : ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol'.terminalTime →
      sol'.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (defaultMetric defaultMetric' : _root_.Bundle.ContinuousRiemannianMetric F W)
    {t : ℝ} (ht : t ∈ Icc t₀ (min sol.terminalTime sol'.terminalTime)) :
    BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
        sol hsymm defaultMetric t =
      BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
        sol' hsymm' defaultMetric' t := by
  have ht_sol : t ∈ Icc t₀ sol.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht_sol' : t ∈ Icc t₀ sol'.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  ext x u v
  rw [BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_inner_eq_of_mem
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
      sol hsymm defaultMetric ht_sol x u v,
    BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_inner_eq_of_mem
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
      sol' hsymm' defaultMetric' ht_sol' x u v]
  exact congrArg (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
    et Kc hKc Ko hKo hKoEq hcover => s x u v) (hEq ht)

/-- The finite-cover Banach-section representative of a smooth initial metric. -/
def InitialValueProblem.toContinuousSectionSpace
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover :=
  ⟨ivp.initialMetric.toContinuousRiemannianMetric.toSection,
    ivp.initialMetric.toContinuousRiemannianMetric.continuous_toSection⟩

/-- The finite-cover Banach-section representative of a smooth initial metric, valued in the closed
symmetric section submodule. -/
def InitialValueProblem.toSymmetricSectionSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  ivp.initialMetric.toContinuousRiemannianMetric.toSymmetricSectionSubmodule
    x0 et het Kc hKc Ko hKo hKoEq hcover

@[simp] theorem InitialValueProblem.coe_toSymmetricSectionSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    (InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp).1 =
      InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp :=
  rfl

theorem InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp ∈
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  exact ivp.initialMetric.toContinuousRiemannianMetric.mem_riemannianMetricLocusSubmodule
    x0 et het Kc hKc Ko hKo hKoEq hcover

/-- A Banach solution in the symmetric metric submodule carrier can be viewed as an ambient
positive-definite section-space solution, provided the ambient and submodule vector fields agree
after coercion. This is the bridge from the genuine metric carrier back to the existing smooth
realization APIs. -/
def BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    (sol : BanachEvolutionLocalSolutionIn Asub
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) :
    BanachEvolutionLocalSolutionIn A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp) :=
  let S := symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover
  let Xamb := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
    (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
    et Kc hKc Ko hKo hKoEq hcover
  let L : S →L[ℝ] Xamb := Submodule.subtypeL S
  BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween
    (X := S) (Y := Xamb)
    (F := Asub) (G := A)
    (stateSet := riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (targetStateSet := positiveDefiniteLocus (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ := ivp.initialTime)
    (u₀ := InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
    (v₀ := InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
    L
    (fun x hx ↦ hx)
    (InitialValueProblem.coe_toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
    hcomm sol

/-- The remaining smooth-realization obligations needed to turn a Banach metric-section solution
into an intrinsic Ricci-DeTurck local solution for the original smooth initial-value problem. -/
structure BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    (sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) where
  /-- The smooth metric family realizing the Banach section curve on the local interval. -/
  metric : MetricFamily (I := I) (M := M)
  /-- The tensor time derivative of the smooth metric realization. -/
  metricVelocity : MetricTensorFamily (I := I) (M := M)
  /-- The background connection family used in the intrinsic DeTurck equation. -/
  background : ConnectionFamily (I := I) (M := M)
  /-- The smooth metric realizes the Banach section curve on the local interval. -/
  metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v
  /-- The smooth realization has the declared tensor time derivative on the local interval. -/
  hasTimeDerivative : HasTimeDerivativeOn (I := I) (M := M)
    metric metricVelocity (Icc ivp.initialTime sol.terminalTime)
  /-- The smooth realization satisfies the intrinsic Ricci-DeTurck equation on the local interval. -/
  equation : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      metric metricVelocity background t

/-- Restrict a smooth intrinsic Ricci-DeTurck realization of a Banach metric-section solution to a
shorter forward terminal time.  The smooth metric, velocity, and background are unchanged; only the
interval on which they realize the Banach curve is shortened. -/
def BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.restrictTerminal
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
      (sol.restrictTerminal hT₀ hT) where
  metric := realization.metric
  metricVelocity := realization.metricVelocity
  background := realization.background
  metric_eq_curve := by
    intro t ht x u v
    have htSol : t ∈ Icc ivp.initialTime sol.terminalTime :=
      ⟨ht.1, le_trans ht.2 hT⟩
    simpa [BanachEvolutionLocalSolutionIn.restrictTerminal] using
      realization.metric_eq_curve htSol x u v
  hasTimeDerivative := by
    refine realization.hasTimeDerivative.mono ?_
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hT⟩
  equation := by
    intro t ht
    exact realization.equation ⟨ht.1, le_trans ht.2 hT⟩

/-- On the interior of the local interval, a smooth metric whose tensor coefficients realize the
Banach curve inherits scalar metric-coefficient derivatives from the Banach ODE after applying any
continuous-linear scalar readout of the section model. -/
theorem BanachEvolutionLocalSolutionIn.metric_hasDerivAt_of_metric_eq_curve_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    {x : M} (u v : TangentSpace I x)
    (L : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ)
    (hL : ∀ s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover,
      L s = s x u v)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) metric τ x u v)
      (A t (sol.curve t) x u v) t := by
  have hproj :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ))
        (A t (sol.curve t) x u v) t := by
    simpa [hL] using
      (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
        (F := A) (stateSet := stateSet) L sol ht)
  have hEq :
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) metric τ x u v)
        =ᶠ[𝓝 t] (fun τ : ℝ ↦ L (sol.curve τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [metric_eq_curve hτ x u v, hL]
  exact hproj.congr_of_eventuallyEq hEq

/-- Pointwise version of `metric_hasDerivAt_of_metric_eq_curve_of_mem_Ioo` using the preferred
finite-cover point readout. -/
theorem BanachEvolutionLocalSolutionIn.metric_hasDerivAt_chartRHS_of_metric_eq_curve_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (metric : MetricFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) metric τ x u v)
      (A t (sol.curve t) x u v) t := by
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simp [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
    pointBilinearFormReadoutContinuousLinearMap
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et Kc hKc Ko hKo hKoEq hcover i xK u v
  refine BanachEvolutionLocalSolutionIn.metric_hasDerivAt_of_metric_eq_curve_of_mem_Ioo
    (M := M) (F := F) (I := I) (sol := sol) metric metric_eq_curve u v L ?_ ht
  intro s
  simpa [L, xK] using
    pointBilinearFormReadoutContinuousLinearMap_apply
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover i xK u v s

/-- Build a smooth intrinsic DeTurck realization once the smooth metric has the Banach curve as its
tensor coefficients, its velocity is the Banach chart right-hand side, and that right-hand side is
identified with the intrinsic Ricci-DeTurck expression. This isolates the remaining PDE burden into
scalar velocity/RHS identification rather than requiring the full intrinsic equation as a primitive
field. -/
def BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_metricVelocity_eq_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (metricVelocity : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    (hasTimeDerivative : HasTimeDerivativeOn (I := I) (M := M)
      metric metricVelocity (Icc ivp.initialTime sol.terminalTime))
    (velocity_eq_chartRHS : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricVelocity t x u v = A t (sol.curve t) x u v)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M) metric background t x u v) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol where
  metric := metric
  metricVelocity := metricVelocity
  background := background
  metric_eq_curve := metric_eq_curve
  hasTimeDerivative := hasTimeDerivative
  equation := by
    intro t ht x u v
    exact (velocity_eq_chartRHS ht x u v).trans (chartRHS_eq_intrinsic ht x u v)

/-- Build a smooth intrinsic DeTurck realization using the Banach ODE for all interior tensor
time-derivatives.  The only remaining time-derivative assumptions are boundary obligations, where
the closed-interval Banach ODE supplies only one-sided derivatives. -/
def BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (metric : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ ⦃t : ℝ⦄,
      t ∈ Icc ivp.initialTime sol.terminalTime →
      t ∉ Ioo ivp.initialTime sol.terminalTime →
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M) metric background t x u v) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol where
  metric := metric
  metricVelocity := fun τ x u v ↦ A τ (sol.curve τ) x u v
  background := background
  metric_eq_curve := metric_eq_curve
  hasTimeDerivative := by
    intro t ht
    by_cases htInterior : t ∈ Ioo ivp.initialTime sol.terminalTime
    · intro x u v
      exact BanachEvolutionLocalSolutionIn.metric_hasDerivAt_chartRHS_of_metric_eq_curve_of_mem_Ioo
        (M := M) (F := F) (I := I) (sol := sol) x0 het metric metric_eq_curve htInterior x u v
    · exact boundary_hasTimeDerivative ht htInterior
  equation := by
    intro t ht x u v
    exact chartRHS_eq_intrinsic ht x u v

/-- A point of a closed real interval that is not in the open interval is one of the two endpoints. -/
theorem eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo {a b t : ℝ}
    (ht : t ∈ Icc a b) (hnot : t ∉ Ioo a b) : t = a ∨ t = b := by
  by_cases hleft : a < t
  · right
    have hnotRight : ¬ t < b := by
      intro htb
      exact hnot ⟨hleft, htb⟩
    exact le_antisymm ht.2 (le_of_not_gt hnotRight)
  · left
    exact le_antisymm (le_of_not_gt hleft) ht.1

/-- Endpoint-only version of `of_boundaryTimeDerivative_chartRHS`. Since the local solution interval
is closed, the non-interior boundary derivative obligation reduces to the initial and terminal times. -/
def BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (metric : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M) metric background t x u v) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
  BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover x0 het metric background
    metric_eq_curve
    (by
      intro t ht hboundary
      rcases eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo ht hboundary with rfl | rfl
      · exact initial_hasTimeDerivative
      · exact terminal_hasTimeDerivative)
    chartRHS_eq_intrinsic

/-- On the interior of the local interval, a smooth realization inherits scalar metric-coefficient
derivatives from the Banach ODE after applying any continuous-linear scalar readout of the section
model. This is the bridge used to turn Banach Picard evolution into fibrewise metric time
derivatives once point-evaluation readouts have been supplied. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_hasDerivAt_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {x : M} (u v : TangentSpace I x)
    (L : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ)
    (hL : ∀ s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover,
      L s = s x u v)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ x u v)
      (A t (sol.curve t) x u v) t := by
  exact BanachEvolutionLocalSolutionIn.metric_hasDerivAt_of_metric_eq_curve_of_mem_Ioo
    (M := M) (F := F) (I := I) (sol := sol)
    realization.metric realization.metric_eq_curve u v L hL ht

/-- At every time in its local interval, the smooth metric realization packages back to the same
finite-cover continuous-section state as the Banach solution curve. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_toContinuousSection_eq_curve
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime sol.terminalTime) :
    (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
      (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) = sol.curve t := by
  ext x u v
  exact realization.metric_eq_curve ht x u v

/-- Coordinate components of the smooth metric realization inherit the Banach
chart right-hand side as whole bilinear-form readouts on the interior of the
local interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i x ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
        =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ]
  exact hproj.congr_of_eventuallyEq hEq

/-- One-sided version of
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) (x : Kc i)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivWithinAt_Ici_of_mem_Ico
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i x ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x)
        =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ]
  have hEq_t :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
        (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover)).1 i x =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
        (sol.curve t)).1 i x := by
    rw [realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  exact hproj.congr_of_eventuallyEq hEq hEq_t

/-- Moving-point time-difference version of
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`.
The Banach curve supplies the derivative in the compact coordinate norm, and
the smooth realization equality transfers the time-difference to the realized
metric section near the base time. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ))
        =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ioo_subset_Icc_self ht)]
  exact hproj.congr_of_eventuallyEq hEq

/-- One-sided moving-point version of
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ))
        =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  exact hproj.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- Coordinate components of the smooth metric realization inherit the projected Banach ODE on the
interior of the local interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadout_hasDerivAt_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x u v)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x u v) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivAt_of_mem_Ioo
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i x u v ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
        =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ]
  exact hproj.congr_of_eventuallyEq hEq

/-- Interior pointwise metric coefficients of a smooth realization inherit the Banach chart
right-hand side.  The finite cover is used only to choose a preferred trivialization containing the
point, whose coordinate readout is a concrete continuous-linear scalar functional on the Banach
section space. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_hasDerivAt_chartRHS_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ x u v)
      (A t (sol.curve t) x u v) t := by
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simp [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
    pointBilinearFormReadoutContinuousLinearMap
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et Kc hKc Ko hKo hKoEq hcover i xK u v
  refine realization.metric_hasDerivAt_of_mem_Ioo (x := x) u v L ?_ ht
  intro s
  simpa [L, xK] using
    pointBilinearFormReadoutContinuousLinearMap_apply
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover i xK u v s

/-- Interior `HasTimeDerivativeAt` form of
`metric_hasDerivAt_chartRHS_of_mem_Ioo`: the velocity tensor can be read directly from the Banach
chart right-hand side on the open local interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime) :
    HasTimeDerivativeAt (I := I) (M := M) realization.metric
      (fun τ x u v ↦ A τ (sol.curve τ) x u v) t := by
  intro x u v
  exact realization.metric_hasDerivAt_chartRHS_of_mem_Ioo
    (M := M) (F := F) (I := I) x0 het ht x u v

/-- The smooth realization has the Banach chart right-hand side as its pointwise tensor time
derivative throughout the open local interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_Ioo_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    HasTimeDerivativeOn (I := I) (M := M) realization.metric
      (fun τ x u v ↦ A τ (sol.curve τ) x u v) (Ioo ivp.initialTime sol.terminalTime) := by
  intro t ht
  exact realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
    (M := M) (F := F) (I := I) x0 het ht

/-- One-sided pointwise metric-coefficient version of the Banach chart right-hand-side derivative
bridge.  This reaches the initial endpoint as a right derivative on `Ici t`, matching the
closed-interval Banach ODE statement. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (x : M) (u v : TangentSpace I x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ x u v)
      (A t (sol.curve t) x u v) (Ici t) t := by
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simp [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
    pointBilinearFormReadoutContinuousLinearMap
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et Kc hKc Ko hKo hKoEq hcover i xK u v
  have hL : ∀ s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover, L s = s x u v := by
    intro s
    simpa [L, xK] using
      pointBilinearFormReadoutContinuousLinearMap_apply
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        x0 et het Kc hKc Ko hKo hKoEq hcover i xK u v s
  have hproj :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ))
        (A t (sol.curve t) x u v) (Ici t) t := by
    simpa [hL] using
      (BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
        (F := A) (stateSet := stateSet) L sol ht)
  have hEq :
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ x u v)
        =ᶠ[𝓝[Ici t] t] (fun τ : ℝ ↦ L (sol.curve τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_eq_curve hτ x u v, hL]
  have hEq_t :
      metricTensor (I := I) (M := M) realization.metric t x u v =
        L (sol.curve t) := by
    rw [realization.metric_eq_curve (Ico_subset_Icc_self ht) x u v, hL]
  exact hproj.congr_of_eventuallyEq hEq hEq_t

/-- One-sided version of
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadout_hasDerivAt_of_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadout_hasDerivWithinAt_Ici_of_mem_Ico
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) (x : Kc i) (u v : F)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i x u v) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i x u v)
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i x u v) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.coordBilinearFormReadout_hasDerivWithinAt_Ici_of_mem_Ico
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i x u v ht
  have hEq :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i x u v)
        =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i x u v) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ]
  have hEq_t :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
        (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover)).1 i x u v =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover
        (sol.curve t)).1 i x u v := by
    rw [realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  exact hproj.congr_of_eventuallyEq hEq hEq_t

/-- A smooth realization of a Banach metric-section solution is an intrinsic Ricci-DeTurck local
solution for the original smooth initial-value problem. -/
def BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicDeTurckSolution :=
    { timeSet := Icc ivp.initialTime sol.terminalTime
      metric := realization.metric
      metricVelocity := realization.metricVelocity
      background := realization.background
      isRicciDeTurck := ⟨realization.hasTimeDerivative, by
        intro t ht
        exact realization.equation ht⟩ }
  interval_subset := by
    intro t ht
    exact ht
  matchesInitialMetric := by
    intro x u v
    have hmetric :=
      realization.metric_eq_curve sol.toBanachEvolutionLocalSolution.initial_mem x u v
    have hcurve := congrArg
      (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover => s x u v)
      sol.initial_eq
    calc
      metricTensor (I := I) (M := M) realization.metric ivp.initialTime x u v =
          sol.curve ivp.initialTime x u v := hmetric
      _ = ivp.initialMetric.inner x u v := by
        simpa [InitialValueProblem.toContinuousSectionSpace,
          _root_.Bundle.ContinuousRiemannianMetric.toSection,
          _root_.Bundle.ContMDiffRiemannianMetric.toContinuousRiemannianMetric] using hcurve

/-- The packaged time-dependent Ricci-DeTurck Banach chart produces a local Banach solution whose
values can be reified at every time as bundled continuous Riemannian metrics. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_with_continuousRiemannianMetrics
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
        ∃ g_t : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
          ∀ (x : M) (u v : TangentSpace I x), g_t.inner x u v = sol.curve t x u v := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, _hterminal, huniq, hsymm⟩
  refine ⟨sol, huniq, hsymm, ?_⟩
  intro t ht
  refine ⟨BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol hsymm ht, ?_⟩
  intro x u v
  rfl

/-- The packaged time-dependent Ricci-DeTurck Banach chart also produces a single
continuous-Riemannian-metric-valued curve, initialized at the prescribed metric and agreeing with the
Banach section solution on the whole local interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_with_continuousRiemannianMetricCurve
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G t₀ = g₀ := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, _hterminal, huniq, hsymm⟩
  refine ⟨sol, huniq, hsymm, ?_⟩
  refine ⟨BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol hsymm g₀, ?_, ?_⟩
  · intro t ht x u v
    exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_inner_eq_of_mem
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover sol hsymm g₀ ht x u v
  · exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_initial_eq
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover g₀ sol hsymm

/-- The interval-scoped time-dependent Ricci-DeTurck Banach chart produces a local Banach
solution whose values can be reified as continuous Riemannian metrics, while retaining the
verified `terminalTime ≤ T` Picard interval bound. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_with_continuousRiemannianMetrics_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
        ∃ g_t : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
          ∀ (x : M) (u v : TangentSpace I x), g_t.inner x u v = sol.curve t x u v := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, hterminal, huniq, hsymm⟩
  refine ⟨sol, hterminal, huniq, hsymm, ?_⟩
  intro t ht
  refine ⟨BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricAt
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol hsymm ht, ?_⟩
  intro x u v
  rfl

/-- The globally Lipschitz time-dependent Ricci-DeTurck Banach chart produces local Banach metrics
with the same terminal-time bound as its Picard interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_with_continuousRiemannianMetrics_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
        ∃ g_t : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
          ∀ (x : M) (u v : TangentSpace I x), g_t.inner x u v = sol.curve t x u v := by
  exact TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_with_continuousRiemannianMetrics_terminal_le
    (M := M) (F := F) (I := I) (chart := chart.toOnIcc)

/-- The interval-scoped time-dependent Ricci-DeTurck Banach chart also produces a single
continuous-Riemannian-metric-valued curve, initialized at the prescribed metric, agreeing with the
Banach section solution on the local interval, and retaining `terminalTime ≤ T`. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G t₀ = g₀ := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, hterminal, huniq, hsymm⟩
  refine ⟨sol, hterminal, huniq, hsymm, ?_⟩
  refine ⟨BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol hsymm g₀, ?_, ?_⟩
  · intro t ht x u v
    exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_inner_eq_of_mem
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover sol hsymm g₀ ht x u v
  · exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_initial_eq
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover g₀ sol hsymm

/-- The globally Lipschitz time-dependent Ricci-DeTurck Banach chart produces a single
continuous-Riemannian-metric-valued curve while retaining the Picard terminal-time bound. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _)}
    {t₀ T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) t₀
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) t₀
          (⟨g₀.toSection, g₀.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc t₀ sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G t₀ = g₀ := by
  exact TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
    (M := M) (F := F) (I := I) (chart := chart.toOnIcc)

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart produces an intrinsic Ricci-DeTurck local
solution as soon as each Banach solution has the packaged smooth realization. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.nonempty_intrinsicDeTurckLocalSolution_of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, _hterminal, _huniq, _hsymm⟩
  exact ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
    (M := M) (F := F) (I := I) (realize sol)⟩

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart produces an intrinsic Ricci-DeTurck local
solution from raw smooth metric realization data. Interior metric time derivatives are supplied by
the Banach ODE; only the closed-interval boundary derivative obligations remain explicit. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.nonempty_intrinsicDeTurckLocalSolution_of_boundaryTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric sol)
          (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) :=
  chart.nonempty_intrinsicDeTurckLocalSolution_of_smoothRealization
    (M := M) (F := F) (I := I)
    (fun sol =>
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol) (boundary_hasTimeDerivative sol) (chartRHS_eq_intrinsic sol))

/-- Endpoint-only smooth-realization route to a nonempty intrinsic Ricci-DeTurck solution. Interior
metric time derivatives are supplied by the Banach ODE, so the remaining closed-interval derivative
work is reduced to the initial and terminal endpoint statements for each Banach solution. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.nonempty_intrinsicDeTurckLocalSolution_of_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) :=
  chart.nonempty_intrinsicDeTurckLocalSolution_of_smoothRealization
    (M := M) (F := F) (I := I)
    (fun sol =>
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_endpointTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol) (initial_hasTimeDerivative sol) (terminal_hasTimeDerivative sol)
        (chartRHS_eq_intrinsic sol))

/-- Smooth realizations of two Banach solutions from the same Ricci-DeTurck chart have identical
metric tensors on their common local interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.smoothRealization_metric_eq_on_common_interval
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {sol sol' : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (realization' : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol')
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) realization.metric t x u v =
      metricTensor (I := I) (M := M) realization'.metric t x u v := by
  have hEq := BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn
    (K := Kstate) chart.lipschitz sol sol'
  have ht_sol : t ∈ Icc ivp.initialTime sol.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht_sol' : t ∈ Icc ivp.initialTime sol'.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  calc
    metricTensor (I := I) (M := M) realization.metric t x u v = sol.curve t x u v :=
      realization.metric_eq_curve ht_sol x u v
    _ = sol'.curve t x u v := by
      exact congrArg (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover => s x u v) (hEq ht)
    _ = metricTensor (I := I) (M := M) realization'.metric t x u v :=
      (realization'.metric_eq_curve ht_sol' x u v).symm

/-- Smooth realizations of two Banach solutions from an interval-scoped Ricci-DeTurck chart have
identical metric tensors on their common local interval, provided both candidate intervals remain
inside the chart's Picard interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.smoothRealization_metric_eq_on_common_interval_of_terminal_le
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {sol sol' : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (hsolT : sol.terminalTime ≤ T) (_hsol'T : sol'.terminalTime ≤ T)
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (realization' : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol')
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) realization.metric t x u v =
      metricTensor (I := I) (M := M) realization'.metric t x u v := by
  have hEq := BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc
    (K := Kstate) sol sol' (by
      intro τ hτ
      have hmin_le_T : min sol.terminalTime sol'.terminalTime ≤ T :=
        le_trans (min_le_left _ _) hsolT
      exact chart.lipschitzOn_Icc τ ⟨hτ.1, le_trans hτ.2 hmin_le_T⟩)
  have ht_sol : t ∈ Icc ivp.initialTime sol.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht_sol' : t ∈ Icc ivp.initialTime sol'.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  calc
    metricTensor (I := I) (M := M) realization.metric t x u v = sol.curve t x u v :=
      realization.metric_eq_curve ht_sol x u v
    _ = sol'.curve t x u v := by
      exact congrArg (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover => s x u v) (hEq ht)
    _ = metricTensor (I := I) (M := M) realization'.metric t x u v :=
      (realization'.metric_eq_curve ht_sol' x u v).symm

/-- Encoding of an arbitrary intrinsic Ricci-DeTurck candidate into the Banach chart used to prove
metric uniqueness. This is the precise reverse-chart obligation: every candidate solution must be
represented by a Banach solution with a smooth realization on the same terminal interval. -/
structure TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) where
  /-- The Banach solution representing the candidate. -/
  sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
  /-- The smooth realization of that Banach solution. -/
  realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol
  /-- The Banach and candidate intervals have the same terminal time. -/
  terminal_eq : sol.terminalTime = candidate.terminalTime
  /-- The candidate's metric tensor is realized by the smooth chart realization on the interval. -/
  metric_eq : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime candidate.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) candidate.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) realization.metric t x u v

/-- The intrinsic DeTurck solution obtained from a smooth realization is encoded by the same Banach
solution and realization. -/
def TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization) where
  sol := sol
  realization := realization
  terminal_eq := rfl
  metric_eq := by
    intro t ht x u v
    rfl

/-- Chosen-background version of `CandidateEncoding.of_smoothRealization`: once the produced smooth
realization is known to use the chosen background, the corresponding chosen DeTurck candidate encodes
back into the same Banach chart without any extra reverse-chart work. -/
def TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_chosenSmoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : UsesChosenBackground (I := I) (M := M)
      (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization)) :
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization, hchosen⟩ :
        ChosenIntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp).1 :=
  TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_smoothRealization
    (M := M) (F := F) (I := I) realization

/-- Two intrinsic DeTurck candidates encoded in the same global Banach chart have equal metric
tensors on their common time interval. This isolates the reverse-chart uniqueness consequence used by
the theorem-package constructors. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.metric_eq_on_common_interval
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate₁ candidate₂ :
      IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc₁ : TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate₁)
    (enc₂ : TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate₂)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime (min candidate₁.terminalTime candidate₂.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) candidate₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) candidate₂.toIntrinsicDeTurckSolution.metric t x u v := by
  have ht₁ : t ∈ Icc ivp.initialTime candidate₁.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Icc ivp.initialTime candidate₂.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
    refine ⟨ht.1, ?_⟩
    simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
  calc
    metricTensor (I := I) (M := M) candidate₁.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
      enc₁.metric_eq ht₁ x u v
    _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
      TimeDependentGeometricRicciDeTurckBanachChart.smoothRealization_metric_eq_on_common_interval
        (M := M) (F := F) (I := I) chart enc₁.realization enc₂.realization htBanach x u v
    _ = metricTensor (I := I) (M := M) candidate₂.toIntrinsicDeTurckSolution.metric t x u v :=
      (enc₂.metric_eq ht₂ x u v).symm

/-- The Picard-produced smooth realization gives a chosen-background DeTurck candidate already
encoded in the same global Banach chart. Thus the existence half of the chosen-background chart route
does not require a separate reverse-chart candidate-encoding argument. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_chosenCandidateEncoding_of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol))) :
    Nonempty (Σ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, _hterminal, _huniq, _hsymm⟩
  refine ⟨⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
    (M := M) (F := F) (I := I) (realize sol), hchosen sol⟩, ?_⟩
  exact TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_chosenSmoothRealization
    (M := M) (F := F) (I := I) (realize sol) (hchosen sol)

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart yields the full intrinsic DeTurck
local-existence/uniqueness package once all candidate solutions can be encoded back into the same
chart. This isolates the remaining reverse-chart uniqueness obligation needed for point 4. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_candidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode : ∀ candidate : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate) :
    IntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · exact chart.nonempty_intrinsicDeTurckLocalSolution_of_smoothRealization realize
  · intro sol₁ sol₂ t ht x u v
    let enc₁ := encode sol₁
    let enc₂ := encode sol₂
    have ht₁ : t ∈ Icc ivp.initialTime sol₁.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Icc ivp.initialTime sol₂.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
    have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
      refine ⟨ht.1, ?_⟩
      simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
    calc
      metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
        enc₁.metric_eq ht₁ x u v
      _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
        TimeDependentGeometricRicciDeTurckBanachChart.smoothRealization_metric_eq_on_common_interval
          (M := M) (F := F) (I := I) chart enc₁.realization enc₂.realization htBanach x u v
      _ = metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v :=
        (enc₂.metric_eq ht₂ x u v).symm

/-- Candidate encoding for an interval-scoped Ricci-DeTurck Banach chart. In addition to the usual
reverse-chart realization, the encoded Banach candidate is required to stay within the chart's Picard
interval; this is the exact extra obligation needed to replace global-in-time Lipschitz control by an
`Icc`-restricted estimate. -/
structure TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) where
  /-- The Banach solution representing the candidate. -/
  sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
  /-- The encoded candidate interval stays inside the Picard interval of the chart. -/
  terminal_le_chart : sol.terminalTime ≤ T
  /-- The smooth realization of that Banach solution. -/
  realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol
  /-- The Banach and candidate intervals have the same terminal time. -/
  terminal_eq : sol.terminalTime = candidate.terminalTime
  /-- The candidate's metric tensor is realized by the smooth chart realization on the interval. -/
  metric_eq : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime candidate.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) candidate.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) realization.metric t x u v

/-- The intrinsic DeTurck solution obtained from a smooth realization of an interval chart is encoded
by the same Banach solution and realization, provided the solution interval stays inside the chart. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (hterminal : sol.terminalTime ≤ T)
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization) where
  sol := sol
  terminal_le_chart := hterminal
  realization := realization
  terminal_eq := rfl
  metric_eq := by
    intro t ht x u v
    rfl

/-- Chosen-background version of the interval self-encoding constructor. The only extra datum is the
known terminal-time containment in the chart's Picard interval. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.of_chosenSmoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (hterminal : sol.terminalTime ≤ T)
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : UsesChosenBackground (I := I) (M := M)
      (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization)) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) realization, hchosen⟩ :
        ChosenIntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp).1 :=
  TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.of_smoothRealization
    (M := M) (F := F) (I := I) hterminal realization

/-- Restrict an interval candidate encoding to a shorter candidate terminal time.  The encoded
Banach solution and smooth realization are restricted to the same shorter interval, and the
candidate metric is unchanged as a geometric object. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.restrictTerminal
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {T' : ℝ} (hT'₀ : ivp.initialTime < T') (hT' : T' ≤ candidate.terminalTime) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (candidate.restrictTerminal hT'₀ hT') := by
  have hT'sol : T' ≤ enc.sol.terminalTime := by
    simpa [enc.terminal_eq] using hT'
  refine
    { sol := enc.sol.restrictTerminal hT'₀ hT'sol
      terminal_le_chart := ?_
      realization := enc.realization.restrictTerminal hT'₀ hT'sol
      terminal_eq := ?_
      metric_eq := ?_ }
  · exact le_trans hT'sol enc.terminal_le_chart
  · rfl
  · intro t ht x u v
    have htCandidate : t ∈ Icc ivp.initialTime candidate.terminalTime :=
      ⟨ht.1, le_trans (by simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using ht.2) hT'⟩
    simpa [IntrinsicDeTurckLocalSolution.restrictTerminal,
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.restrictTerminal] using
      enc.metric_eq htCandidate x u v

/-- Two intrinsic DeTurck candidates encoded in the same interval-scoped Banach chart have equal
metric tensors on their common time interval. The terminal-containment fields are exactly the extra
data needed to use the `Icc`-restricted chart uniqueness theorem. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.metric_eq_on_common_interval
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate₁ candidate₂ :
      IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc₁ : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate₁)
    (enc₂ : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate₂)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime (min candidate₁.terminalTime candidate₂.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) candidate₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) candidate₂.toIntrinsicDeTurckSolution.metric t x u v := by
  have ht₁ : t ∈ Icc ivp.initialTime candidate₁.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Icc ivp.initialTime candidate₂.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
    refine ⟨ht.1, ?_⟩
    simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
  calc
    metricTensor (I := I) (M := M) candidate₁.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
      enc₁.metric_eq ht₁ x u v
    _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.smoothRealization_metric_eq_on_common_interval_of_terminal_le
        (M := M) (F := F) (I := I) chart enc₁.terminal_le_chart enc₂.terminal_le_chart
        enc₁.realization enc₂.realization htBanach x u v
    _ = metricTensor (I := I) (M := M) candidate₂.toIntrinsicDeTurckSolution.metric t x u v :=
      (enc₂.metric_eq ht₂ x u v).symm

/-- The Picard-produced smooth realization gives a chosen-background DeTurck candidate already
encoded in the same interval-scoped Banach chart. The terminal containment is supplied by the
interval chart's Picard theorem. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_chosenCandidateEncoding_of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol))) :
    Nonempty (Σ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, hterminal, _huniq, _hsymm⟩
  refine ⟨⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
    (M := M) (F := F) (I := I) (realize sol), hchosen sol⟩, ?_⟩
  exact TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.of_chosenSmoothRealization
    (M := M) (F := F) (I := I) (chart := chart) (sol := sol)
    hterminal (realize sol) (hchosen sol)

/-- A global-chart candidate encoding becomes an interval-chart candidate encoding once its Banach
representative is known to stay inside the chart's Picard interval. -/
def TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.toOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    (hterminal : enc.sol.terminalTime ≤ T) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart.toOnIcc candidate where
  sol := enc.sol
  terminal_le_chart := hterminal
  realization := enc.realization
  terminal_eq := enc.terminal_eq
  metric_eq := enc.metric_eq

/-- The global Picard-produced smooth realization also gives a chosen-background DeTurck candidate
encoded in the interval-scoped chart obtained by restriction to `Icc`. This exposes the bounded
candidate-encoding witness directly for downstream interval routes. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.exists_chosenCandidateEncodingOnIcc_of_smoothRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol))) :
    Nonempty (Σ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1) := by
  rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
    ⟨sol, hterminal, _huniq, _hsymm⟩
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) (realize sol), hchosen sol⟩
  refine ⟨candidate, ?_⟩
  let enc : TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1 :=
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_chosenSmoothRealization
      (M := M) (F := F) (I := I) (chart := chart) (sol := sol)
      (realize sol) (hchosen sol)
  exact enc.toOnIcc hterminal

/-- Interval-scoped Ricci-DeTurck Banach charts yield the full intrinsic DeTurck
local-existence/uniqueness package once smooth realizations and bounded candidate encodings are
supplied. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_candidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode : ∀ candidate : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate) :
    IntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with ⟨sol, _hsolT, _huniq, _hsymm⟩
    exact ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) (realize sol)⟩
  · intro sol₁ sol₂ t ht x u v
    let enc₁ := encode sol₁
    let enc₂ := encode sol₂
    have ht₁ : t ∈ Icc ivp.initialTime sol₁.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Icc ivp.initialTime sol₂.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
    have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
      refine ⟨ht.1, ?_⟩
      simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
    calc
      metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
        enc₁.metric_eq ht₁ x u v
      _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.smoothRealization_metric_eq_on_common_interval_of_terminal_le
          (M := M) (F := F) (I := I) chart enc₁.terminal_le_chart enc₂.terminal_le_chart
          enc₁.realization enc₂.realization htBanach x u v
      _ = metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v :=
        (enc₂.metric_eq ht₂ x u v).symm

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart yields the intrinsic Ricci-flow point-4 package
once candidate solutions encode into the chart and DeTurck backgrounds in the resulting class are
Levi-Civita for their evolving metrics. This is the identity-gauge closure route; the non-identity
gauge route replaces the final Levi-Civita-background condition by gauge-reduction obligations. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_candidateEncoding_and_allBackgroundsLeviCivita
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode : ∀ candidate : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate)
    (hbackground : ∀ sol : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_all_backgrounds_isLeviCivita
      (TimeDependentGeometricRicciDeTurckBanachChart.intrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_candidateEncoding
          (M := M) (F := F) (I := I) chart realize encode)
      hbackground

/-- Interval-scoped identity-gauge closure route: an `Icc`-Lipschitz Ricci-DeTurck Banach chart
promotes to the intrinsic Ricci-flow point-4 package once smooth realizations, bounded candidate
encodings, and Levi-Civita backgrounds are supplied. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_candidateEncoding_and_allBackgroundsLeviCivita
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode : ∀ candidate : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate)
    (hbackground : ∀ sol : IntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_all_backgrounds_isLeviCivita
      (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_candidateEncoding
          (M := M) (F := F) (I := I) chart realize encode)
      hbackground

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart yields the chosen-background DeTurck package
once its produced smooth realizations use the chosen Levi-Civita background and all chosen-background
candidates encode back into the same Banach chart. This is the DeTurck theorem package expected by
the non-identity gauge-reduction layer. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with
      ⟨sol, _hterminal, _huniq, _hsymm⟩
    exact ⟨⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) (realize sol), hchosen sol⟩⟩
  · intro sol₁ sol₂ t ht x u v
    let enc₁ := encode sol₁
    let enc₂ := encode sol₂
    have ht₁ : t ∈ Icc ivp.initialTime sol₁.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Icc ivp.initialTime sol₂.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
    have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
      refine ⟨ht.1, ?_⟩
      simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
    calc
      metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
        enc₁.metric_eq ht₁ x u v
      _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
        TimeDependentGeometricRicciDeTurckBanachChart.smoothRealization_metric_eq_on_common_interval
          (M := M) (F := F) (I := I) chart enc₁.realization enc₂.realization htBanach x u v
      _ = metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v :=
        (enc₂.metric_eq ht₂ x u v).symm

/-- Chosen-background DeTurck package from raw smooth metric realization data.  This removes the
primitive packaged-realization hypothesis from the chosen chart route: the Banach ODE supplies
interior time derivatives, while only boundary derivatives and the chart/intrinsic RHS comparison
remain as analytic inputs. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric sol)
          (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  let realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
    fun sol ↦
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol) (boundary_hasTimeDerivative sol) (chartRHS_eq_intrinsic sol)
  refine
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize ?_ encode
  intro sol
  dsimp [realize, UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution]
  exact hbackground sol

/-- Endpoint derivative data supplies the boundary time-derivative hypothesis for a single global
Ricci-DeTurck Banach-chart solution. This is the reusable one-solution form of the closed-interval
endpoint reduction used by the endpoint-only smooth-realization routes. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.boundaryTimeDerivative_of_endpointTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      t ∉ Ioo ivp.initialTime sol.terminalTime →
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t := by
  intro t ht hboundary
  rcases eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo ht hboundary with rfl | rfl
  · exact initial_hasTimeDerivative
  · exact terminal_hasTimeDerivative

/-- Chosen-background DeTurck package from raw smooth metric realization data with endpoint-only
time-derivative obligations. The Banach ODE supplies interior derivatives, and the closed-interval
boundary is reduced to the initial and terminal endpoint statements. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  let realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
    fun sol ↦
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol)
        (TimeDependentGeometricRicciDeTurckBanachChart.boundaryTimeDerivative_of_endpointTimeDerivative
          (M := M) (F := F) (I := I) chart (metric sol)
          (initial_hasTimeDerivative sol) (terminal_hasTimeDerivative sol))
        (chartRHS_eq_intrinsic sol)
  refine
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize ?_ encode
  intro sol
  dsimp [realize, UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution]
  exact hbackground sol

/-- Boundary-reduced single-IVP route from a global Ricci-DeTurck Banach chart, prepackaged `C³`
gauges, and pulled-back metric time derivatives to the intrinsic Ricci-flow theorem package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric sol)
          (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3Gauge
    (TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart metric background metric_eq_curve
      boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsic

/-- Endpoint-reduced single-IVP route from a global Ricci-DeTurck Banach chart, prepackaged `C³`
gauges, and pulled-back metric time derivatives to the intrinsic Ricci-flow theorem package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3Gauge
    (TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart metric background metric_eq_curve
      initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsic

/-- Interval-scoped chosen-background DeTurck package. This is the chosen-candidate version of the
bounded interval chart theorem and is the DeTurck package expected by the non-identity gauge layer. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases chart.exists_unique_symmetricPositiveDefinite_terminal_le with ⟨sol, _hsolT, _huniq, _hsymm⟩
    exact ⟨⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) (realize sol), hchosen sol⟩⟩
  · intro sol₁ sol₂ t ht x u v
    let enc₁ := encode sol₁
    let enc₂ := encode sol₂
    have ht₁ : t ∈ Icc ivp.initialTime sol₁.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Icc ivp.initialTime sol₂.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
    have htBanach : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
      refine ⟨ht.1, ?_⟩
      simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
    calc
      metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
        enc₁.metric_eq ht₁ x u v
      _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v :=
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.smoothRealization_metric_eq_on_common_interval_of_terminal_le
          (M := M) (F := F) (I := I) chart enc₁.terminal_le_chart enc₂.terminal_le_chart
          enc₁.realization enc₂.realization htBanach x u v
      _ = metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v :=
        (enc₂.metric_eq ht₂ x u v).symm

/-- Global chart chosen-background DeTurck package using bounded interval candidate encodings. This
lets global chart callers discharge the uniqueness side through the interval-scoped encoding surface
without first manufacturing global candidate encodings. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart.toOnIcc realize hchosen encode

/-- Interval-scoped chosen-background package from raw smooth metric realization data.  As in the
global chart route, the Banach ODE supplies all interior tensor derivatives; boundary derivatives
and the chart/intrinsic RHS comparison remain the explicit analytic obligations. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric sol)
          (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  let realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
    fun sol ↦
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol) (boundary_hasTimeDerivative sol) (chartRHS_eq_intrinsic sol)
  refine
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize ?_ encode
  intro sol
  dsimp [realize, UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution]
  exact hbackground sol

/-- Endpoint derivative data supplies the boundary time-derivative hypothesis for a single
interval-scoped Ricci-DeTurck Banach-chart solution. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.boundaryTimeDerivative_of_endpointTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime) :
    ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      t ∉ Ioo ivp.initialTime sol.terminalTime →
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t := by
  intro t ht hboundary
  rcases eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo ht hboundary with rfl | rfl
  · exact initial_hasTimeDerivative
  · exact terminal_hasTimeDerivative

/-- Interval-scoped chosen-background DeTurck package from raw smooth metric realization data with
endpoint-only time-derivative obligations. This is the `Icc`-Lipschitz analogue of the global
endpoint route. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  let realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
    fun sol ↦
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
        (M := M) (F := F) (I := I)
        et Kc hKc Ko hKo hKoEq hcover x0 het
        (metric sol) (background sol)
        (metric_eq_curve sol)
        (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.boundaryTimeDerivative_of_endpointTimeDerivative
          (M := M) (F := F) (I := I) chart (metric sol)
          (initial_hasTimeDerivative sol) (terminal_hasTimeDerivative sol))
        (chartRHS_eq_intrinsic sol)
  refine
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize ?_ encode
  intro sol
  dsimp [realize, UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution]
  exact hbackground sol

/-- Boundary-reduced single-IVP route from an interval-scoped Ricci-DeTurck Banach chart,
prepackaged `C³` gauges, and pulled-back metric time derivatives to the intrinsic Ricci-flow
theorem package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric sol)
          (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3Gauge
    (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart metric background metric_eq_curve
      boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsic

/-- Endpoint-reduced single-IVP route from an interval-scoped Ricci-DeTurck Banach chart,
prepackaged `C³` gauges, and pulled-back metric time derivatives to the intrinsic Ricci-flow theorem
package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M))
    (background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M))
    (metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v)
    (hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3Gauge
    (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart metric background metric_eq_curve
      initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsic

/-- Direct chosen-background route from a smooth-IVP-seeded Ricci-DeTurck Banach chart to the
intrinsic Ricci-flow local-existence/uniqueness package. Compared with the arbitrary-background route,
this requires only chosen-background candidate encodings, because intrinsic Ricci-flow candidates are
converted to chosen-background DeTurck candidates. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    (M := M) (F := F) (I := I) chart realize hchosen encode).toIntrinsic

/-- Direct chosen-background route from a global smooth-IVP-seeded Ricci-DeTurck Banach chart to the
intrinsic Ricci-flow package using only bounded interval candidate encodings. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
    (M := M) (F := F) (I := I) chart realize hchosen encode).toIntrinsic

/-- Interval-scoped direct chosen-background route from a smooth-IVP-seeded Ricci-DeTurck Banach
chart to the intrinsic Ricci-flow local-existence/uniqueness package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    (M := M) (F := F) (I := I) chart realize hchosen encode).toIntrinsic

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart feeds the non-identity gauge-reduction boundary
once the chosen-background chart package is available and at least one chosen-background solution has
the required gauge-reducibility data. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_gaugeReducible

/-- Global chart route to the non-identity gauge-reduction package using bounded interval
candidate encodings for the underlying chosen-background DeTurck uniqueness proof. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_gaugeReducible

/-- A smooth-IVP-seeded Ricci-DeTurck Banach chart feeds the scalar-inner-derivative
gauge-reduction boundary. This global-chart version matches the interval-scoped theorem but keeps
the older global-in-time Lipschitz chart package as input. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_innerDerivativeGaugeReducible

/-- Global chart route to the scalar-inner-derivative gauge package using bounded interval
candidate encodings for the underlying chosen-background DeTurck uniqueness proof. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_innerDerivativeGaugeReducible

/-- Interval-scoped Ricci-DeTurck Banach chart feeds the non-identity gauge-reduction boundary once
the bounded chosen-background chart package and one gauge-reducible chosen solution are supplied. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_gaugeReducible

/-- Interval-scoped Ricci-DeTurck Banach chart feeds the scalar-inner-derivative gauge-reduction
boundary. This is the more explicit analytic gauge target: instead of supplying a fully bundled
`GaugeReducible` solution, it suffices to supply scalar derivatives of the gauge-pulled metric
inner products. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp where
  chosen_package :=
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) chart realize hchosen encode
  exists_gaugeReducible := exists_innerDerivativeGaugeReducible

/-- Direct non-identity gauge-reduction route from a smooth-IVP-seeded Ricci-DeTurck Banach chart to
the intrinsic Ricci-flow local-existence/uniqueness package. The remaining gauge obligation is now
exactly a `GaugeReducibleChosenIntrinsicDeTurckLocalSolution`, rather than an all-backgrounds
Levi-Civita assumption. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode exists_gaugeReducible).toIntrinsic

/-- Direct non-identity gauge-reduction route from a global smooth-IVP-seeded Ricci-DeTurck Banach
chart to the intrinsic Ricci-flow package using bounded interval candidate encodings. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode exists_gaugeReducible).toIntrinsic

/-- Scalar-inner-derivative gauge route from a smooth-IVP-seeded Ricci-DeTurck Banach chart to the
intrinsic Ricci-flow local-existence/uniqueness package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode
    exists_innerDerivativeGaugeReducible).toGaugeReducible.toIntrinsic

/-- Scalar-inner-derivative gauge route from a global smooth-IVP-seeded Ricci-DeTurck Banach chart
to the intrinsic Ricci-flow package using bounded interval candidate encodings. -/
theorem TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart.toOnIcc candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode
    exists_innerDerivativeGaugeReducible).toGaugeReducible.toIntrinsic

/-- Interval-scoped non-identity gauge-reduction route from a smooth-IVP-seeded Ricci-DeTurck Banach
chart to the intrinsic Ricci-flow local-existence/uniqueness package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_gaugeReducible :
      Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode exists_gaugeReducible).toIntrinsic

/-- Interval-scoped scalar-inner-derivative gauge route from a smooth-IVP-seeded Ricci-DeTurck
Banach chart to the intrinsic Ricci-flow local-existence/uniqueness package. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1)
    (exists_innerDerivativeGaugeReducible :
      Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    (M := M) (F := F) (I := I) chart realize hchosen encode
    exists_innerDerivativeGaugeReducible).toGaugeReducible.toIntrinsic

/-- Family-level chosen-background DeTurck package from global Ricci-DeTurck Banach charts. This
preserves the chosen DeTurck theorem family before any identity-gauge or non-identity-gauge
conversion to Ricci flow. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)

/-- Family-level chosen-background DeTurck package from global Ricci-DeTurck Banach charts using
bounded interval candidate encodings. This keeps the global chart input while letting callers prove
only the interval-scoped encoding obligations needed for uniqueness. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp).toOnIcc candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncodingOnIcc
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)

/-- Family-level chosen-background DeTurck package from global Ricci-DeTurck Banach charts and raw
smooth metric realization data. This is the boundary-reduced replacement for the packaged
`SmoothIntrinsicDeTurckRealization` assumption in the global chart route. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (metric ivp) (background ivp)
      (metric_eq_curve ivp) (boundary_hasTimeDerivative ivp) (chartRHS_eq_intrinsic ivp)
      (hbackground ivp) (encode ivp)

/-- Family-level endpoint-to-boundary adapter for global Ricci-DeTurck Banach charts. It packages
the single-solution endpoint reduction for every IVP in a theorem family. -/
theorem boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime) :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t := by
  intro ivp sol t ht hboundary
  exact TimeDependentGeometricRicciDeTurckBanachChart.boundaryTimeDerivative_of_endpointTimeDerivative
    (M := M) (F := F) (I := I) (chart ivp) (metric ivp sol)
    (initial_hasTimeDerivative ivp sol) (terminal_hasTimeDerivative ivp sol) ht hboundary

/-- Family-level chosen-background DeTurck package from global Ricci-DeTurck Banach charts and raw
smooth metric realization data with endpoint-only time-derivative obligations. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (metric ivp) (background ivp)
      (metric_eq_curve ivp) (initial_hasTimeDerivative ivp) (terminal_hasTimeDerivative ivp)
      (chartRHS_eq_intrinsic ivp) (hbackground ivp) (encode ivp)

/-- Global chart route with primitive non-identity gauge data: chosen DeTurck packages extracted
from global Banach charts become scalar-derivative gauge theorem families when each chosen solution
has a `C³` diffeomorphism gauge and the corresponding scalar inner-product derivative identity. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    gauge3 hderiv

/-- Global chart route with primitive non-identity gauge data and pulled-back metric
time-derivative data. This keeps the scalar-derivative gauge package as the endpoint while allowing
callers to provide the preferred `HasTimeDerivativeOn` statement instead of pointwise scalar
inner-product derivatives. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    gauge3 hpullDerivative

/-- Global chart route with raw non-identity gauge-flow data: after extracting the
chosen-background DeTurck theorem family from global Banach charts, raw `C³` diffeomorphism
families with anchoring, the gauge-flow equation, and scalar inner-product derivative identities
produce the scalar-derivative gauge theorem family. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hderiv

/-- Global chart route with raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge package endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hpullDerivative

/-- Boundary-reduced global chart route with raw non-identity gauge-flow data. This is the same
scalar-derivative gauge-reduction endpoint as the packaged-realization route, but it builds each
smooth DeTurck realization from metric realization, boundary time derivatives, and the
chart/intrinsic RHS bridge. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hderiv

/-- Boundary-reduced global chart route with raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge theorem family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hpullDerivative

/-- Endpoint-only global chart route with raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background metric_eq_curve
    (boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric
      initial_hasTimeDerivative terminal_hasTimeDerivative)
    chartRHS_eq_intrinsic hbackground encode maps3 anchored hflow hpullDerivative

/-- Boundary-reduced global chart route with raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the preferred `HasTimeDerivativeOn` gauge-reducible theorem-family
endpoint. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hpullDerivative

/-- Boundary-reduced global chart route from primitive pointwise `C³` gauge-flow ODE
derivative data and scalar inner-product derivative data, retaining the scalar-derivative
gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflowDeriv hderiv

/-- Intrinsic boundary-reduced global chart route from primitive pointwise `C³`
gauge-flow ODE derivative data and scalar inner-product derivative data. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hderiv).toIntrinsicFamily

/-- Ordinary boundary-reduced global chart route from primitive pointwise `C³` gauge-flow ODE
derivative data and scalar inner-product derivative data. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hderiv).toOrdinaryFamily

/-- Boundary-reduced global chart route with raw pointwise `C³` gauge-flow ODE derivative data and
pulled-back metric time-derivative data, retaining the preferred `HasTimeDerivativeOn`
gauge-reducible theorem-family endpoint. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflowDeriv hpullDerivative

/-- Ordinary boundary-reduced global chart route with primitive pointwise `C³` gauge-flow ODE
derivative data and pulled-back metric time-derivative data. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hpullDerivative).toOrdinaryFamily

/-- Global chart route from raw non-identity gauge-flow data all the way to the compact
Ricci-flow local-existence/uniqueness theorem family. This composes the raw scalar-derivative
gauge theorem family with the final gauge-reduction-to-Ricci-flow packaging step. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hderiv

/-- Boundary-reduced global chart route from raw non-identity gauge-flow data all the way to the
compact Ricci-flow local-existence/uniqueness theorem family. Compared with the packaged route, the
smooth DeTurck local solution is constructed from raw metric realization data plus endpoint
derivative and RHS-identification obligations. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hderiv

/-- Boundary-reduced global chart route from raw non-identity gauge-flow data and a genuine
time-derivative statement for the pulled-back metric.  This derives the scalar inner-product
derivative hypothesis used by the lower-level gauge-reduction wrapper, so the final chart route no
longer has to assume those scalar derivatives separately. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflow
    (fun ivp sol {t} ht x u v ↦ by
      simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
        hpullDerivative ivp sol ht x u v)

/-- Boundary-reduced global chart route from prepackaged non-identity `C³` gauges and a genuine
time-derivative statement for each pulled-back metric.  This is the final compact Ricci-flow theorem
family surface when gauge-flow existence has already been packaged as
`AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn`. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3Gauge
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsicFamily

/-- Endpoint-reduced global chart route from prepackaged non-identity `C³` gauges and a genuine
time-derivative statement for each pulled-back metric to the compact Ricci-flow theorem family. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3Gauge
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic
      hbackground encode)
    gauge3 hpullDerivative).toIntrinsicFamily

/-- Family-level non-identity gauge-reduction route from Ricci-DeTurck Banach charts to the compact
Ricci-flow local-existence/uniqueness theorem family. This is the point-4 family package once the
quasilinear parabolic chart estimates, smooth realizations, chosen-candidate encodings, and gauge
reducibility data are supplied for every smooth initial value problem. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_gaugeReducible ivp)

/-- Stronger family-level non-identity gauge-reduction package from global Ricci-DeTurck Banach
charts. This keeps the gauge-reducible theorem-family wrapper available instead of immediately
forgetting it to the intrinsic Ricci-flow family. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_gaugeReducible ivp)

/-- Stronger family-level non-identity gauge-reduction package from global Ricci-DeTurck Banach
charts using only bounded interval candidate encodings for each chosen-background DeTurck package. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp).toOnIcc candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_gaugeReducible ivp)

/-- Family-level non-identity gauge-reduction route from global Ricci-DeTurck Banach charts to the
compact Ricci-flow theorem family using bounded interval candidate encodings. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp).toOnIcc candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_gaugeReducible
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode
    exists_gaugeReducible).toIntrinsicFamily

/-- Family-level scalar-inner-derivative gauge route from global Ricci-DeTurck Banach charts to the
compact Ricci-flow local-existence/uniqueness theorem family. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_innerDerivativeGaugeReducible ivp)

/-- Stronger family-level scalar-inner-derivative gauge package from global Ricci-DeTurck Banach
charts. Downstream work can use this when it needs to retain the explicit scalar-derivative
gauge-reduction witness instead of only the intrinsic Ricci-flow consequence. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_innerDerivativeGaugeReducible ivp)

/-- Stronger family-level scalar-inner-derivative gauge package from global Ricci-DeTurck Banach
charts using only bounded interval candidate encodings for each chosen-background DeTurck package. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp).toOnIcc candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChart.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_innerDerivativeGaugeReducible ivp)

/-- Family-level scalar-inner-derivative gauge route from global Ricci-DeTurck Banach charts to the
compact Ricci-flow theorem family using bounded interval candidate encodings. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp).toOnIcc candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_smoothRealization_chosenCandidateEncodingOnIcc_and_innerDerivativeGaugeReducible
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode
    exists_innerDerivativeGaugeReducible).toIntrinsicFamily

/-- Family-level non-identity gauge-reduction route from interval-scoped Ricci-DeTurck Banach charts
to the compact Ricci-flow local-existence/uniqueness theorem family. This is the family package whose
analytic chart estimates only need to be proved on the local Picard interval for each IVP. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_gaugeReducible ivp)

/-- Stronger family-level non-identity gauge-reduction package from interval-scoped Ricci-DeTurck
Banach charts. This preserves the gauge-reducible theorem-family wrapper while only requiring
`Icc`-restricted chart estimates. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_gaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_gaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_gaugeReducible ivp)

/-- Family-level scalar-inner-derivative gauge route from interval-scoped Ricci-DeTurck Banach
charts to the compact Ricci-flow local-existence/uniqueness theorem family. This sharpens the
non-identity gauge obligation to the concrete scalar derivative identities needed by
`GaugeReduction`. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_innerDerivativeGaugeReducible ivp)

/-- Stronger family-level scalar-inner-derivative gauge package from interval-scoped Ricci-DeTurck
Banach charts. This is the sharpest current interval chart-to-gauge family boundary: local
`Icc`-restricted estimates plus scalar inner-product derivative data. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (exists_innerDerivativeGaugeReducible :
      ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
        Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_chosenCandidateEncoding_and_innerDerivativeGaugeReducible
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)
      (exists_innerDerivativeGaugeReducible ivp)

/-- Family-level arbitrary-background DeTurck package from interval-scoped Ricci-DeTurck Banach
charts. This preserves the strongest DeTurck uniqueness package before any Levi-Civita-background
or gauge-reduction conversion to Ricci flow. -/
theorem intrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_candidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : IntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate) :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_candidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (encode ivp)

/-- Family-level identity-gauge route from interval-scoped Ricci-DeTurck Banach charts to the compact
Ricci-flow local-existence/uniqueness theorem family. This route uses arbitrary DeTurck candidate
encodings plus a Levi-Civita-background condition, while still requiring Lipschitz estimates only on
each local Picard interval. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_candidateEncoding_and_allBackgroundsLeviCivita
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : IntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp),
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_candidateEncoding_and_allBackgroundsLeviCivita
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (encode ivp) (hbackground ivp)

/-- Family-level chosen-background DeTurck package from interval-scoped Ricci-DeTurck Banach charts.
This is the direct interval DeTurck theorem family expected by the identity and non-identity gauge
routes, before forgetting to the intrinsic Ricci-flow theorem family. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)

/-- Family-level interval-scoped chosen-background DeTurck package from raw smooth metric
realization data. This is the `Icc` counterpart of the global boundary-reduced chart route. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (metric ivp) (background ivp)
      (metric_eq_curve ivp) (boundary_hasTimeDerivative ivp) (chartRHS_eq_intrinsic ivp)
      (hbackground ivp) (encode ivp)

/-- Family-level endpoint-to-boundary adapter for interval-scoped Ricci-DeTurck Banach charts. It
lets downstream interval theorem families consume only initial and terminal time-derivative data. -/
theorem boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime) :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        t ∉ Ioo ivp.initialTime sol.terminalTime →
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t := by
  intro ivp sol t ht hboundary
  exact TimeDependentGeometricRicciDeTurckBanachChartOnIcc.boundaryTimeDerivative_of_endpointTimeDerivative
    (M := M) (F := F) (I := I) (chart ivp) (metric ivp sol)
    (initial_hasTimeDerivative ivp sol) (terminal_hasTimeDerivative ivp sol) ht hboundary

/-- Family-level interval-scoped chosen-background DeTurck package from raw smooth metric realization
data with endpoint-only time-derivative obligations. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (metric ivp) (background ivp)
      (metric_eq_curve ivp) (initial_hasTimeDerivative ivp) (terminal_hasTimeDerivative ivp)
      (chartRHS_eq_intrinsic ivp) (hbackground ivp) (encode ivp)

/-- Interval-scoped boundary-reduced route from raw non-identity gauge-flow data and pulled-back
metric time-derivative data, retaining the scalar-derivative gauge theorem family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hpullDerivative

/-- Interval-scoped endpoint-only route from raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background metric_eq_curve
    (boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric
      initial_hasTimeDerivative terminal_hasTimeDerivative)
    chartRHS_eq_intrinsic hbackground encode maps3 anchored hflow hpullDerivative

/-- Interval-scoped boundary-reduced route from primitive pointwise `C³` gauge-flow ODE
derivative data and scalar inner-product derivative data, retaining the scalar-derivative
gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflowDeriv hderiv

/-- Intrinsic boundary-reduced interval-scoped chart route from primitive pointwise `C³`
gauge-flow ODE derivative data and scalar inner-product derivative data. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hderiv).toIntrinsicFamily

/-- Ordinary boundary-reduced interval-scoped chart route from primitive pointwise `C³`
gauge-flow ODE derivative data and scalar inner-product derivative data. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hderiv).toOrdinaryFamily

/-- Interval-scoped boundary-reduced route from raw non-identity gauge-flow data and pulled-back
metric time-derivative data, retaining the preferred `HasTimeDerivativeOn` gauge-reducible
theorem-family endpoint. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow hpullDerivative

/-- Interval-scoped boundary-reduced route with raw pointwise `C³` gauge-flow ODE derivative data and
pulled-back metric time-derivative data, retaining the preferred `HasTimeDerivativeOn`
gauge-reducible theorem-family endpoint. -/
theorem gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflowDeriv hpullDerivative

/-- Ordinary interval-scoped boundary-reduced route with raw pointwise `C³` gauge-flow ODE
derivative data and pulled-back metric time-derivative data. This exposes the final ordinary
theorem-family endpoint directly from the primitive derivative-level gauge-flow boundary. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (gaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeTimeDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
    metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode
    maps3 anchored hflowDeriv hpullDerivative).toOrdinaryFamily

/-- Interval-scoped boundary-reduced route from raw non-identity gauge-flow data and a
time-derivative statement for the pulled-back metric to the compact Ricci-flow local theorem
family. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    maps3 anchored hflow
    (fun ivp sol {t} ht x u v ↦ by
      simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
        hpullDerivative ivp sol ht x u v)

/-- Interval-scoped boundary-reduced route from prepackaged non-identity `C³` gauges and a
time-derivative statement for each pulled-back metric to the compact Ricci-flow local theorem
family. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (boundary_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          t ∉ Ioo ivp.initialTime sol.terminalTime →
          HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
            (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) t)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3Gauge
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve boundary_hasTimeDerivative chartRHS_eq_intrinsic hbackground encode)
    gauge3 hpullDerivative).toIntrinsicFamily

/-- Interval-scoped endpoint-reduced route from prepackaged non-identity `C³` gauges and a
time-derivative statement for each pulled-back metric to the compact Ricci-flow local theorem family. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3Gauge
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background
      metric_eq_curve initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic
      hbackground encode)
    gauge3 hpullDerivative).toIntrinsicFamily

/-- Interval chart route that keeps the non-identity gauge obligation primitive: after the chosen
Ricci-DeTurck theorem family has been extracted from the `Icc` chart estimates, per-solution `C³`
diffeomorphism gauges and scalar inner-product derivative identities produce the scalar-derivative
gauge theorem family directly. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    gauge3 hderiv

/-- Interval chart route with primitive non-identity gauge data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge theorem family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (gauge3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    gauge3 hpullDerivative

/-- Interval chart route with raw non-identity gauge-flow data. This is the sharpest current
`Icc`-chart-to-gauge-family boundary: interval Ricci-DeTurck chart estimates plus raw `C³`
diffeomorphism-family gauge-flow data and scalar derivative identities. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hderiv

/-- Interval chart route with raw non-identity gauge-flow data and pulled-back metric
time-derivative data, retaining the scalar-derivative gauge theorem family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hpullDerivative

/-- Interval chart route from raw non-identity gauge-flow data all the way to the compact
Ricci-flow local-existence/uniqueness theorem family. This is the direct `Icc`-local analytic
boundary once the parabolic chart estimates, smooth realizations, candidate encodings, and raw
gauge-flow identities are available. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode)
    maps3 anchored hflow hderiv

/-- Interval chart route from raw non-identity gauge-flow data and a time-derivative statement for
the pulled-back metric.  This derives the scalar inner-product derivative hypothesis needed by the
lower-level `Icc` gauge-flow route. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode
    maps3 anchored hflow
    (fun ivp sol {t} ht x u v ↦ by
      simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
        hpullDerivative ivp sol ht x u v)

/-- Ordinary interval chart route from raw non-identity gauge-flow data to the compact Ricci-flow
local-existence/uniqueness theorem family. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode
    maps3 anchored hflow hderiv).toOrdinary

/-- Ordinary interval chart route from raw non-identity gauge-flow data and a pulled-back metric
time-derivative statement. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_chosenCandidateEncoding_and_diffeomorph3GaugeFlowTimeDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode
    maps3 anchored hflow hpullDerivative).toOrdinary

/-- Family-level chosen-background route from interval-scoped Ricci-DeTurck Banach charts to the
compact Ricci-flow local-existence/uniqueness theorem family. This is the interval counterpart of
the direct chosen-background identity route and requires no separate gauge-reducibility witness. -/
theorem intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.intrinsicLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) (chart ivp) (realize ivp) (hchosen ivp) (encode ivp)

/-- Ordinary connection-parametrized interval chart route from Ricci-DeTurck Banach charts to the
compact Ricci-flow local-existence/uniqueness theorem family. This is the standard point-4 package
obtained from the direct chosen-background intrinsic route. -/
theorem localExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (realize :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (hchosen :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        UsesChosenBackground (I := I) (M := M)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) (realize ivp sol)))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_smoothRealization_and_chosenCandidateEncoding
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart realize hchosen encode).toOrdinary

/-- If the continuous-linear symmetry in
`exists_unique_in_positiveDefiniteLocus_fixedBy_of_contDiffAt_lipschitzOn` has the closed symmetric
section locus as its fixed-point set, then the produced solution stays in the full finite-cover
symmetric positive-definite locus. This remains available as an abstract fixed-locus route; the
concrete Ricci-DeTurck route now uses the pointwise-symmetric-vector-field variant, with the remaining
Banach-chart task being to identify the chart representative with the symmetric geometric RHS and
prove the needed parabolic estimates. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_fixedSymmetry_contDiffAt_lipschitzOn
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {K : ℝ≥0}
    (hA : ContDiffAt ℝ 1 A g₀)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : LipschitzOnWith K A
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (L : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (hL_state : MapsTo L
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hfixed_iff : ∀ x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
      L x = x ↔ x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      L (A x) = A (L x)) :
    ∃ sol : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      (∀ sol' : BanachEvolutionLocalSolutionIn (fun _ : ℝ ↦ A)
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_fixedBy_of_contDiffAt_lipschitzOn
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hA hg₀.2 hLip
      L hL_state ((hfixed_iff g₀).2 hg₀.1) hcomm with
    ⟨sol, huniq, hfixed⟩
  exact ⟨sol, huniq, by
    intro t ht
    exact ⟨(hfixed_iff (sol.curve t)).1 (hfixed ht), sol.mem_state ht⟩⟩

/-- Interval-scoped fixed-symmetry route to the finite-cover symmetric positive-definite locus.
This is the time-dependent counterpart of
`exists_unique_in_symmetricPositiveDefiniteLocus_of_fixedSymmetry_contDiffAt_lipschitzOn`. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_fixedSymmetry_isPicardLindelof_lipschitzOn_Icc
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hcomplete : CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover))
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {a L Kpic Kstate : ℝ≥0}
    (hA : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ g₀ a 0 L Kpic)
    (hg₀ : g₀ ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (S : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover)
    (hS_state : MapsTo S
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
      (positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover))
    (hfixed_iff : ∀ x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
      S x = x ↔ x ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x, x ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover →
      S (A t x) = A t (S x)) :
    ∃ sol : BanachEvolutionLocalSolutionIn A
        (positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn A
          (positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover) t₀ g₀,
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_fixedBy_of_isPicardLindelof_lipschitzOn_Icc
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hcomplete hT hA hg₀.2 hLip
      S hS_state ((hfixed_iff g₀).2 hg₀.1) hcomm with
    ⟨sol, hsolT, huniq, hfixed⟩
  exact ⟨sol, hsolT, huniq, by
    intro t ht
    exact ⟨(hfixed_iff (sol.curve t)).1 (hfixed ht), sol.mem_state ht⟩⟩

end MetricLocusEvolution

end AnalyticPDE
end RicciFlow
