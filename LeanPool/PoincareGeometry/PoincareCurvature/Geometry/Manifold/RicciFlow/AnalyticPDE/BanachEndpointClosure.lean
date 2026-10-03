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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE
/-!
# Endpoint closure for Banach evolution uniqueness

This leaf module closes the restricted-terminal Banach uniqueness bridge at the
common endpoint.  The core analytic layer already supplies equality on every
shorter closed interval and therefore on the open common interval; the lemmas
below add the endpoint using within-interval continuity of the ODE curves.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Endpoint closure for functions that agree on the left-open interval and
are continuous within the corresponding closed interval at the endpoint. -/
theorem eq_of_continuousWithinAt_Icc_of_eqOn_Ico {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ℝ → Y} {a b : ℝ} (hab : a < b)
    (hf : ContinuousWithinAt f (Icc a b) b)
    (hg : ContinuousWithinAt g (Icc a b) b)
    (hEq : EqOn f g (Ico a b)) : f b = g b := by
  have hleft_le : 𝓝[<] b ≤ 𝓝[Icc a b] b := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact nhdsWithin_mono b (by
      intro t ht
      exact ⟨ht.1, le_of_lt ht.2⟩)
  have hfg : f =ᶠ[𝓝[<] b] g := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact eventuallyEq_nhdsWithin_of_eqOn hEq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left hleft_le) (hg.mono_left hleft_le) hfg

namespace BanachEvolutionLocalSolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {t₀ : ℝ} {u₀ : X}

/-- Closed-interval continuation bridge from an already-established open common
interval equality. -/
theorem eqOn_Icc_of_eqOn_Ico
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀)
    (hEq : EqOn sol₁.curve sol₂.curve
      (Ico t₀ (min sol₁.terminalTime sol₂.terminalTime))) :
    EqOn sol₁.curve sol₂.curve
      (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let Tcommon := min sol₁.terminalTime sol₂.terminalTime
  intro t ht
  by_cases htlt : t < Tcommon
  · exact hEq ⟨ht.1, htlt⟩
  · have ht_eq : t = Tcommon :=
      le_antisymm (by simpa [Tcommon] using ht.2) (le_of_not_gt htlt)
    subst t
    have hT₀ : t₀ < Tcommon := by
      exact lt_min sol₁.initial_lt_terminal sol₂.initial_lt_terminal
    have hcont₁ : ContinuousWithinAt sol₁.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₁.continuousOn_Icc_of_le_terminal (min_le_left _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    have hcont₂ : ContinuousWithinAt sol₂.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₂.continuousOn_Icc_of_le_terminal (min_le_right _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    exact eq_of_continuousWithinAt_Icc_of_eqOn_Ico hT₀ hcont₁ hcont₂ hEq

/-- Closed-interval continuation bridge: if equality is available on every
prescribed shorter common terminal, continuity of the Banach ODE curves closes
the equality at the common terminal. -/
theorem eqOn_Icc_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let Tcommon := min sol₁.terminalTime sol₂.terminalTime
  intro t ht
  by_cases htlt : t < Tcommon
  · exact eqOn_Ico_of_eqOn_Icc_of_le_terminal sol₁ sol₂ hEq ⟨ht.1, htlt⟩
  · have ht_eq : t = Tcommon :=
      le_antisymm (by simpa [Tcommon] using ht.2) (le_of_not_gt htlt)
    subst t
    have hT₀ : t₀ < Tcommon := by
      exact lt_min sol₁.initial_lt_terminal sol₂.initial_lt_terminal
    have hcont₁ : ContinuousWithinAt sol₁.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₁.continuousOn_Icc_of_le_terminal (min_le_left _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    have hcont₂ : ContinuousWithinAt sol₂.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₂.continuousOn_Icc_of_le_terminal (min_le_right _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    exact eq_of_continuousWithinAt_Icc_of_eqOn_Ico hT₀ hcont₁ hcont₂
      (eqOn_Ico_of_eqOn_Icc_of_le_terminal sol₁ sol₂ hEq)

end BanachEvolutionLocalSolution

namespace BanachEvolutionLocalSolutionIn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X}

/-- Closed-interval continuation bridge for state-preserving solutions from an
already-established open common interval equality. -/
theorem eqOn_Icc_of_eqOn_Ico
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hEq : EqOn sol₁.curve sol₂.curve
      (Ico t₀ (min sol₁.terminalTime sol₂.terminalTime))) :
    EqOn sol₁.curve sol₂.curve
      (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact BanachEvolutionLocalSolution.eqOn_Icc_of_eqOn_Ico
    sol₁.toBanachEvolutionLocalSolution sol₂.toBanachEvolutionLocalSolution hEq

/-- Closed-interval continuation bridge for state-preserving solutions. -/
theorem eqOn_Icc_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact BanachEvolutionLocalSolution.eqOn_Icc_of_eqOn_Icc_of_le_terminal
    sol₁.toBanachEvolutionLocalSolution sol₂.toBanachEvolutionLocalSolution hEq

/-- State-set uniqueness on the closed common interval when the Lipschitz bound
is available on every prescribed shorter common terminal interval. -/
theorem eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal_common
    {K : ℝ≥0}
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hF : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      ∀ t ∈ Icc t₀ T, LipschitzOnWith K (F t) stateSet) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact eqOn_Icc_of_eqOn_Icc_of_le_terminal sol₁ sol₂ (fun hT₀ hT₁ hT₂ ↦
    eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal (F := F) (stateSet := stateSet)
      (t₀ := t₀) (u₀ := u₀) (K := K) sol₁ sol₂ hT₀ hT₁ hT₂
      (hF hT₀ hT₁ hT₂))

end BanachEvolutionLocalSolutionIn

/-- Picard-Lindelof plus an open state set and Lipschitz bounds on every
prescribed shorter terminal gives local existence and closed-common-interval
uniqueness.  This is the endpoint-closed form of
`IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc`. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc_closed
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
        EqOn sol.curve sol'.curve (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
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
  exact BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal_common
    (F := F) (stateSet := stateSet) (t₀ := t₀) (u₀ := u₀) (K := Kstate) sol sol'
    (fun hS₀ hS₁ _hS₂ t ht ↦ hLip hS₀ (le_trans hS₁ hsolT) t ht)

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

local instance banachEndpointClosureBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance banachEndpointClosureBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))

/-- Endpoint-closed finite-cover positive-definite state-set bridge for local
estimates supplied on every prescribed shorter terminal. -/
theorem exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  exact IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc_closed
    (F := A) (stateSet := positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) hT hA
    (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    hg₀ hLip

/-- Endpoint-closed restricted-terminal direct defect route to the finite-cover
symmetric positive-definite locus. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  rcases exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hT hA hg₀.2 hLip with
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

/-- Concrete coordinatewise-defect version of the endpoint-closed
restricted-terminal direct defect route. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  letI : Fintype κ := Fintype.ofFinite κ
  exact
    exists_unique_in_symmetricPositiveDefiniteLocus_of_linearDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hT hA hg₀ hLip
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover)
      (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
        (M := M) (F := F) (W := W)
        x0 et het Kc hKc Ko hKo hKoEq hcover)
      hdefect_A

/-- Endpoint-closed restricted-terminal non-autonomous symmetric-vector-field
bridge with arbitrary symmetric positive-definite initial section. -/
theorem exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact
    exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hT hA hg₀ hLip
      (by
        intro t x hx
        exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
          (M := M) (F := F) (W := W)
          x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))

/-- Continuous-Riemannian-metric initial-data version of the endpoint-closed
restricted-terminal coordinatewise-defect bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact
    exists_unique_in_symmetricPositiveDefiniteLocus_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover hT hA
      (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g₀)
      hLip hdefect_A

/-- Continuous-Riemannian-metric initial-data version of the endpoint-closed
restricted-terminal non-autonomous symmetric-vector-field bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact
    exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT hA hLip
      (by
        intro t x hx
        exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
          (M := M) (F := F) (W := W)
          x0 et het Kc hKc Ko hKo hKoEq hcover (A t x)).2 (hA_symm t x hx))

/-- Endpoint-closed restricted-terminal time-dependent Ricci-DeTurck Banach-chart bridge. -/
theorem exists_unique_from_continuousRiemannianMetric_of_timeDependent_geometricRicciDeTurckRHS_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact
    exists_unique_from_continuousRiemannianMetric_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT hA hLip
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

/-- Endpoint-closed extractor from a restricted-terminal coordinatewise-defect chart. -/
theorem TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  exact
    exists_unique_from_continuousRiemannianMetric_of_coordwiseDefect_isPicardLindelof_lipschitzOn_restricted_Icc_closed
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀
      chart.hT chart.picard chart.lipschitzOn_restricted_Icc chart.coordwiseDefect

/-- Endpoint-closed extractor from a restricted-terminal geometric Ricci-DeTurck Banach chart. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite_closed
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
          (Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc t₀ sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  exact TimeDependentCoordwiseDefectMetricBanachChartRestrictedIcc.exists_unique_symmetricPositiveDefinite_closed
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    (chart := chart.toCoordwiseDefectMetricChartRestrictedIcc)

/-- Endpoint-closed symmetric metric-locus bridge for local estimates supplied
on every prescribed shorter terminal. -/
theorem exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_restricted_Icc_closed
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
        EqOn sol.curve sol'.curve
          (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  exact @IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc_closed
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

end MetricLocusEvolution

end AnalyticPDE
end RicciFlow
