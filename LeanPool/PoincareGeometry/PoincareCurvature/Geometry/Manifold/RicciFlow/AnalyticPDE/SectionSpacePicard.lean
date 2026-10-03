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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE

/-!
# Section-space Picard–Lindelöf constructor (route (ii))

The `picard` field of a `TimeDependentGeometricRicciDeTurckBanachChart` asks for
`IsPicardLindelof A` for the time-dependent Banach representative `A` on the
`ContinuousSectionSpace`.  Roadmap point 4 route (ii) supplies this through the
Banach-space Picard–Lindelöf foundation
`RicciFlow.AnalyticPDE.isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`, whose
hypotheses are boundedness, uniform Lipschitzness and time-continuity of `A`.

This module assembles the three coordinate→section handoffs proved in `ContinuousSection.lean`
(`norm_le_of_forall_coord_norm_le`, `lipschitzWith_of_forall_coord_dist_le`,
`continuousOn_of_forall_coord_continuousOn`) with that foundation into a single constructor
`isPicardLindelof_continuousSectionSpace_of_forall_coord`: from *coordinatewise* (local
trivialization readout) boundedness, Lipschitz and continuity data it produces
`IsPicardLindelof A` in exactly the interval/anchor/constant shape consumed by the chart's
`picard` field.  This is the section-space `picard`-field constructor for the mild/regularised
Ricci–DeTurck chart.
-/

@[expose] public noncomputable section

open scoped NNReal Topology
open RicciFlow.AnalyticPDE

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

/-- **Section-space Picard–Lindelöf constructor (route (ii)).**  A time-dependent operator `A` on
the `ContinuousSectionSpace` whose local trivialization readouts are, uniformly over sections,
bounded by `L`, `K`-Lipschitz in the section, and time-continuous on `[t₀, T]`, is
`IsPicardLindelof` with anchor `t₀`, initial datum `x0`, radius `L·(T−t₀)₊ + 1`, and Lipschitz
constant `K` — exactly the shape demanded by the
`TimeDependentGeometricRicciDeTurckBanachChart.picard` field.  Assembles the coordinate→section
boundedness / Lipschitz / continuity handoffs with the Banach ODE foundation
`isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (L K : ℝ≥0)
    (hbound : ∀ (t : ℝ)
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x‖ ≤ (L : ℝ))
    (hlip : ∀ (t : ℝ)
        (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 (L * (T - t₀).toNNReal + 1) 0 L K := by
  refine isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc A x0 t₀ T hT L K ?_ ?_ ?_
  · intro t s
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L) (fun i x => hbound t s i x)
  · intro t
    exact lipschitzWith_of_forall_coord_dist_le (fun s s' i x => hlip t s s' i x)
  · intro s
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s i)

/-- **Section-space bounded–Lipschitz evolution existence & uniqueness (transport step (a)).**
From coordinatewise (local trivialization readout) boundedness ≤ `L`, `K`-Lipschitz-in-section and
time-continuity on `[t₀, T]`, the time-dependent operator `A` on the (complete) section space admits
a unique `[t₀, T]`-evolution `α` with `α t₀ = x0` solving `α'(t) = A t (α t)`.  This lifts the model
`ℝⁿ` mild-solution existence–uniqueness to the manifold-bundle section space (`CompleteSpace` from
`CompleteSpace F`), the state space of the chart's `A`, by assembling the coordinate→section handoffs
with the Banach evolution foundation `bounded_lipschitz_evolution_exists_unique_timeDependent_Icc`. -/
theorem sectionSpace_evolution_exists_unique_of_forall_coord
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (L K : ℝ≥0)
    (hbound : ∀ (t : ℝ)
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x‖ ≤ (L : ℝ))
    (hlip : ∀ (t : ℝ)
        (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T)) :
    (∃ α : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = x0 ∧
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t)) ∧
    (∀ α β : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = β t₀ →
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t) →
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt β (A t (β t)) (Set.Icc t₀ T) t) →
      ∀ t ∈ Set.Icc t₀ T, α t = β t) := by
  refine bounded_lipschitz_evolution_exists_unique_timeDependent_Icc
    A x0 hT (L := L) (K := K) ?_ ?_ ?_
  · intro t s
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L) (fun i x => hbound t s i x)
  · intro t
    exact lipschitzWith_of_forall_coord_dist_le (fun s s' i x => hlip t s s' i x)
  · intro s
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s i)

/-- **Section-space ball-local (superset) Picard–Lindelöf constructor (route (ii), honest form).**
The globally-`C⁰`-unbounded second-order Ricci–DeTurck operator cannot satisfy the *global* bound of
`isPicardLindelof_continuousSectionSpace_of_forall_coord`; the honest `picard` datum is only
ball-local.  From coordinatewise (local trivialization readout) boundedness ≤ `L` and
`K`-Lipschitz-in-section control over a set `S ⊇ closedBall x0 a` (e.g. the positive-definite locus),
together with time-continuity on `[t₀, T]` at each point of the ball and the compatibility
`L·(T − t₀) ≤ a`, the time-dependent operator `A` is `IsPicardLindelof` with anchor `t₀`, initial
datum `x0`, radius **`a`** (the chart's own radius, not the global `L·(T−t₀)₊+1`) and Lipschitz
constant `K` — exactly the shape `IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 L K` demanded by the
`TimeDependentGeometricRicciDeTurckBanachChart.picard` field.  Assembles the coordinate→section
boundedness / Lipschitz / continuity handoffs with the ball-local Banach ODE foundation
`isPicardLindelof_of_boundedOn_lipschitzOn_superset_timeDependent_Icc`. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord_superset
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a L K : ℝ≥0)
    (S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (hball : Metric.closedBall x0 (a : ℝ) ⊆ S)
    (hbound : ∀ t ∈ Set.Icc t₀ T, ∀ s ∈ S, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x‖ ≤ (L : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ S → ∀ ⦃s'⦄, s' ∈ S → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hLa : (L : ℝ) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 L K := by
  refine isPicardLindelof_of_boundedOn_lipschitzOn_superset_timeDependent_Icc
    A x0 t₀ T hT a L K hball ?_ ?_ ?_ hLa
  · intro t ht
    exact lipschitzOnWith_of_forall_coord_dist_le
      (fun s hs s' hs' i x => hlip t ht hs hs' i x)
  · intro s hs
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s hs i)
  · intro t ht s hs
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L)
      (fun i x => hbound t ht s hs i x)

/-- **Section-space centre-bound ball-local Picard–Lindelöf constructor (route (ii), sharpest
honest form).**  The most economical `picard` datum: the only norm information required about the
`C⁰`-unbounded operator is its coordinatewise readout size at the **fixed centre** `x0` (the initial
metric `g₀`), not a bound over a whole ball — the ball bound `Mc + K·a` is *derived* from the
`K`-Lipschitz control on `closedBall x0 a`.  From coordinatewise `K`-Lipschitz-in-section control on
the ball, time-continuity on `[t₀, T]` at each ball point, the centre readout bound
`‖(A t x0)ᵢ x‖ ≤ Mc`, and the compatibility `(Mc + K·a)·(T − t₀) ≤ a`, the time-dependent operator
`A` is `IsPicardLindelof` with anchor `t₀`, initial datum `x0`, radius `a`, bound `Mc + K·a` and
Lipschitz constant `K` — the exact shape of `TimeDependentGeometricRicciDeTurckBanachChart.picard`.
Assembles the coordinate→section handoffs with the centre-bound Banach ODE foundation
`isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc`; this is the form where the
only genuinely analytic input is the size of the Ricci–DeTurck operator applied to the initial
metric. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc
    A x0 t₀ T hT a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact lipschitzOnWith_of_forall_coord_dist_le
      (fun s hs s' hs' i x => hlip t ht hs hs' i x)
  · intro s hs
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s hs i)
  · intro t ht
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg Mc)
      (fun i x => hcenter t ht i x)

/-- **Section-space centre-bound Picard endpoint chooser (route (ii) capstone).**  The
`TimeDependentGeometricRicciDeTurckBanachChart`'s only `T`-dependent data are `hT : t₀ < T` and the
`picard` field (its `lipschitz`/`geometric` fields quantify over *all* times).  This lemma supplies
both at once: from *forward*-time-uniform (on `Set.Ici t₀`) coordinatewise `K`-Lipschitz-in-section
control on `closedBall x0 a`, continuity there, and the centre readout bound `‖(A t x0)ᵢ x‖ ≤ Mc`
(for a genuinely positive radius `a`), there **exists** a forward endpoint `T > t₀` for which `A` is
`IsPicardLindelof` with radius `a`, bound `Mc + K·a`, Lipschitz `K` — the chart's exact `picard`
shape.  The endpoint is produced by `exists_forwardTime_mul_sub_le` (satisfying the time-radius
compatibility `(Mc + K·a)·(T − t₀) ≤ a` automatically), letting the chart *choose* its per-IVP Picard
window from the analytic size constants `Mc` (centre bound) and `K` (Lipschitz constant) alone. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ) (a K Mc : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Ici t₀, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Ici t₀))
    (hcenter : ∀ t ∈ Set.Ici t₀, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  obtain ⟨T, hT, hLa⟩ := RicciFlow.AnalyticPDE.exists_forwardTime_mul_sub_le t₀ a K Mc ha
  refine ⟨T, hT, ?_⟩
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ T hT a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact hlip t (Set.Icc_subset_Ici_self ht)
  · intro s hs i
    exact (hcont s hs i).mono Set.Icc_subset_Ici_self
  · intro t ht
    exact hcenter t (Set.Icc_subset_Ici_self ht)

/-- **Section-space evolution existence from centre-bound ball-local data (honest form).**  The
ball-local companion of `sectionSpace_evolution_exists_unique_of_forall_coord` (which assumes the
unattainable *global* bound): from the honest centre-bound ball-local coordinatewise data — `K`-
Lipschitz-in-section on `closedBall x0 a`, time-continuity there, centre readout bound
`‖(A t x0)ᵢ x‖ ≤ Mc`, and `(Mc + K·a)·(T − t₀) ≤ a` — the time-dependent operator `A` on the complete
section space admits a `[t₀, T]`-evolution `α` with `α t₀ = x0` solving `α'(t) = A t (α t)`.  Combines
the centre-bound section-space Picard constructor with the Mathlib differential Picard–Lindelöf
theorem `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.  This is the raw evolution
curve a downstream `realization` decode into a genuine intrinsic De Turck local solution consumes,
now available from the honest (not globally bounded) analytic input. -/
theorem sectionSpace_evolution_exists_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    ∃ α : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = x0 ∧
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t) :=
  (isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ T hT a K Mc hlip hcont hcenter hLa).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Single-solution Picard–Lindelöf with closed-ball state membership.**  Mathlib's differential
Picard–Lindelöf theorem `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` produces the
local integral curve `α` but discards the a-priori bound that `α` stays inside the closed ball
`closedBall x₀ a`, on which the vector-field hypotheses hold — a bound its own proof establishes
(`ODE.FunSpace.compProj_mem_closedBall`).  This variant *retains* that state-membership readout on
the whole interval, which is exactly what upgrades a raw evolution curve to a state-constrained
`BanachEvolutionLocalSolutionIn` without shrinking the interval or assuming the state set is open. -/
theorem _root_.IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) :
    ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Set.Icc tmin tmax, α t ∈ Metric.closedBall x₀ (a : ℝ)) ∧
      ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Set.Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj,
    by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t _ => α.compProj_mem_closedBall hf.mul_max_le, fun t ht => ?_⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn
    (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- **Closed-ball Picard–Lindelöf gives a state-constrained forward local solution.**  When the
Picard state ball `closedBall u₀ a` is contained in the prescribed state set `stateSet`, the forward
Picard–Lindelöf solution — which provably stays in that ball on the *whole* interval `[t₀, T]` — is a
genuine `BanachEvolutionLocalSolutionIn` on the full window, with **no** interval shrinking and **no**
openness hypothesis on `stateSet` (contrast `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_mem_isOpen`,
which shrinks the terminal time to keep the curve inside an open set).  This is the a-posteriori
ball-membership route that the honest ball-local section-space Picard data feeds directly into a
`realization` decode. -/
theorem _root_.IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hsub : Metric.closedBall u₀ (a : ℝ) ⊆ stateSet) :
    Nonempty (BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) := by
  obtain ⟨α, hα0, hmem, hderiv⟩ :=
    hF.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall (x := u₀) (by simp)
  exact ⟨{
    terminalTime := T
    initial_lt_terminal := hT
    curve := α
    initial_eq := hα0
    equation := by intro t ht; exact hderiv t ht
    mem_state := by intro t ht; exact hsub (hmem t ht) }⟩

/-- **Section-space state-constrained local solution from centre-bound ball-local data.**  The
capstone of the honest route (ii): from the same centre-bound coordinatewise analytic control that
supplies the chart's `picard` field (`K`-Lipschitz-in-section on `closedBall x0 a`, time-continuity
there, centre readout bound `‖(A t x0)ᵢ x‖ ≤ Mc`, and the time-radius compatibility
`(Mc + K·a)·(T − t₀) ≤ a`), together with the a-priori containment `closedBall x0 a ⊆ locus` of the
Picard ball in the prescribed state locus (e.g. the positive-definite / Riemannian metric cone), the
time-dependent operator `A` on the complete section space admits a genuine
`BanachEvolutionLocalSolutionIn A locus t₀ x0` on the full window `[t₀, T]`.  Combines the centre-bound
section-space Picard constructor `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`
with the closed-ball a-posteriori bridge
`IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`.  This is precisely the
state-constrained Banach solution a downstream `realization` decode into a genuine intrinsic De Turck
local solution consumes, now available from the honest (not globally bounded) analytic input. -/
theorem sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn A locus t₀ x0) :=
  IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT
    (isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
      A x0 t₀ T hT a K Mc hlip hcont hcenter hLa) hsub

/-- **Section-space Picard endpoint chooser from Lipschitz + time-continuity alone (no hand-supplied
centre bound).**  A convenience strengthening of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`: the centre
readout size `Mc` need not be supplied by hand.  On a reference window `Icc t₀ T₀`, from
coordinatewise `K`-Lipschitz-in-section control on `closedBall x0 a` and mere *time-continuity* of the
compact coordinate readouts there, the uniform centre bound is *derived*
(`exists_forall_mem_Icc_coord_norm_le_of_continuousOn`, using compactness of `Icc t₀ T₀` and of the
base pieces), and a forward Picard endpoint `T ∈ (t₀, T₀]` is chosen (`exists_forwardTime_mul_sub_le`
intersected with the window `min T' T₀`) for which `A` is `IsPicardLindelof` with radius `a`,
Lipschitz `K`, and the internally produced bound `Mc + K·a`.  This is the honest section-space
`picard`-field shape whose only analytic inputs are the operator's ball-local Lipschitz constant and
the continuity of its coordinate readout — no separately quantified size constant, the centre bound
`Mc` coming for free from continuity of the readout at the initial metric on a compact window. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T₀, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_forall_mem_Icc_coord_norm_le_of_continuousOn
      (f := fun t => A t x0) (t₀ := t₀) (T := T₀)
      (hcont x0 (Metric.mem_closedBall_self ha.le))
  set Mc : ℝ≥0 := C.toNNReal with hMc
  have hCMc : C ≤ (Mc : ℝ) := by
    rw [hMc]; exact (Real.coe_toNNReal C hC0).ge
  obtain ⟨T', hT', hLa'⟩ :=
    RicciFlow.AnalyticPDE.exists_forwardTime_mul_sub_le t₀ a K Mc ha
  have hTle : min T' T₀ ≤ T₀ := min_le_right T' T₀
  have hstep : (min T' T₀ - t₀) ≤ (T' - t₀) := by
    have := min_le_left T' T₀; linarith
  refine ⟨min T' T₀, lt_min hT' hT₀, Mc, ?_⟩
  have hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀) ≤ (a : ℝ) := by
    calc ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀)
        ≤ ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T' - t₀) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (a : ℝ) := hLa'
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ (min T' T₀) (lt_min hT' hT₀) a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact hlip t ⟨ht.1, le_trans ht.2 hTle⟩
  · intro s hs i
    exact (hcont s hs i).mono (Set.Icc_subset_Icc le_rfl hTle)
  · intro t ht i x
    exact le_trans (hCbound t ⟨ht.1, le_trans ht.2 hTle⟩ i x) hCMc

/-- **Section-space Picard endpoint chooser from Banach-norm Lipschitz + time-continuity alone.**
The cleanest honest form of the chart's `picard` field: its only analytic inputs are stated purely
at the *section-space (finite-cover Banach norm)* level, with no reference to the compact coordinate
readouts.  On a reference window `Icc t₀ T₀`, from
* `hlip` — for each `t ∈ Icc t₀ T₀` the time-slice operator `A t` is `K`-`LipschitzOnWith` on the
  section-space ball `closedBall x0 a`, and
* `hcont` — for each section `s ∈ closedBall x0 a` the time-curve `t ↦ A t s` is `ContinuousOn`
  `(Icc t₀ T₀)` in the section-space norm,

a forward Picard endpoint `T ∈ (t₀, T₀]` and centre size `Mc` are produced for which `A` is
`IsPicardLindelof` with radius `a`, Lipschitz `K`, and bound `Mc + K·a`.  The coordinatewise
hypotheses of `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn`
are discharged from these section-space ones by the `1`-Lipschitz coordinate readout:
`coord_dist_le_dist` turns the ball-local `LipschitzOnWith` estimate into the pointwise coordinate
`hlip`, and `continuousOn_coord_of_continuousOn` turns section-space time-continuity into the
coordinate `hcont`.  This is the interface a genuine (mild/regularised) Ricci–DeTurck section-space
operator is meant to verify — a Banach-norm Lipschitz-in-state bound and a Banach-norm time-continuity
of the operator — with all trivialization/coordinate bookkeeping absorbed here. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T₀, LipschitzOnWith K (A t) (Metric.closedBall x0 (a : ℝ)))
    (hcont : ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ContinuousOn (fun t => A t s) (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn
    A x0 t₀ T₀ hT₀ a K ha ?_ ?_
  · intro t ht s hs s' hs' i x
    calc
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ dist (A t s) (A t s') := coord_dist_le_dist (A t s) (A t s') i x
      _ ≤ (K : ℝ) * dist s s' := (hlip t ht).dist_le_mul s hs s' hs'
  · intro s hs i
    exact continuousOn_coord_of_continuousOn (hcont hs) i

/-- **Section-space Picard–Lindelöf endpoint chooser from purely fiber-pointwise operator
estimates.**  This is the interface a (regularised) geometric section-space operator naturally
verifies.  From
* a uniform operator-norm bound `Lop` on the finite family of fiber trivialization maps,
* a *fiber-pointwise* Lipschitz-in-state estimate
  `dist ((A t s) x) ((A t s') x) ≤ C · dist s s'` at every base point `x`, uniformly over the ball
  and over `t ∈ [t₀, T₀]`, and
* *coordinatewise joint (time–base) continuity* of each trivialization readout of `A · s` on
  `[t₀, T₀] ×ˢ Kc i`,

this chooses a forward endpoint `T` and produces `IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 (Mc + Lop·C·a)
(Lop·C)` — the chart's exact `picard` shape with Lipschitz constant `Lop · C`.  The fiber-pointwise
Lipschitz bound is lifted to the section-space `LipschitzOnWith` via
`lipschitzOnWith_of_forall_fiber_dist_le`, and the joint-continuity data to section-space
time-continuity via `continuousOn_of_forall_coord_uncurry_continuousOn`, before invoking the
section-level capstone
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn`. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_fiber_dist_le_continuousOn
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a Lop C : ℝ≥0) (ha : 0 < (a : ℝ))
    (hL : ∀ i (x : Kc i), ‖(et i).continuousLinearMapAt ℝ x.1‖ ≤ (Lop : ℝ))
    (hfiber : ∀ t ∈ Set.Icc t₀ T₀,
      ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
      ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ x : M, dist ((A t s) x) ((A t s') x) ≤ (C : ℝ) * dist s s')
    (hcont : ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) → ∀ i,
      ContinuousOn
        (fun p : ℝ × M => (et i).continuousLinearMapAt ℝ p.2 ((A p.1 s) p.2))
        (Set.Icc t₀ T₀ ×ˢ (Kc i : Set M))) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + (Lop * C) * a) (Lop * C) := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn
    A x0 t₀ T₀ hT₀ a (Lop * C) ha ?_ ?_
  · intro t ht
    exact lipschitzOnWith_of_forall_fiber_dist_le (A := A t) (L := Lop) (C := C) hL
      (fun s hs s' hs' x => hfiber t ht hs hs' x)
  · intro s hs
    exact continuousOn_of_forall_coord_uncurry_continuousOn
      (f := fun t => A t s) (hcont hs)

/-- **Section-space Picard–Lindelöf endpoint chooser for a bounded-linear generator family with a
continuous source** — the honest *mild-operator* interface for the chart's `picard` field.

If the time-dependent operator has the affine "generator + source" shape `A t s = L t s + b t`,
where `L t : CSS →L[ℝ] CSS` is a *bounded* linear operator on the continuous-section Banach space
with a uniform operator-norm bound `‖L t‖ ≤ K` on `[t₀, T₀]`, the family is *strongly continuous* in
time (`t ↦ L t s` continuous on `[t₀, T₀]` for each `s`), and the source `b` is continuous on
`[t₀, T₀]`, then a forward endpoint `T > t₀` can be chosen so that

`IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 (Mc + K·a) K`

holds — the chart's exact `picard` shape, with Lipschitz constant `K`.

This is precisely the structure a *regularised* (mild) geometric Ricci–DeTurck operator has: a bounded
generator on the section space plus a `g₀`-dependent inhomogeneity.  It therefore reduces the chart's
`picard` field to *exhibiting the bounded linear generator family `L`, its operator-norm bound, its
strong continuity, and the continuous source `b`* — no bundle-distortion or coordinate bookkeeping
survives, because `A t` is affine and the Lipschitz constant is read directly off the operator norm.

The `LipschitzOnWith` hypothesis of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn` is
discharged by the affine identity `dist (L t s + b t) (L t s' + b t) = dist (L t s) (L t s') =
‖L t (s − s')‖ ≤ ‖L t‖ · ‖s − s'‖ ≤ K · dist s s'`; the time-continuity hypothesis is the strong
continuity of `L` plus the continuity of `b`. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (L : ℝ →
      (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hK : ∀ t ∈ Set.Icc t₀ T₀, ‖L t‖ ≤ (K : ℝ))
    (hLc : ∀ s, ContinuousOn (fun t => (L t) s) (Set.Icc t₀ T₀))
    (hb : ContinuousOn b (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof (fun t s => (L t) s + b t) (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn
    (fun t s => (L t) s + b t) x0 t₀ T₀ hT₀ a K ha ?_ ?_
  · intro t ht
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s _ s' _
    calc
      dist ((L t) s + b t) ((L t) s' + b t)
          = dist ((L t) s) ((L t) s') := dist_add_right _ _ _
      _ = ‖(L t) s - (L t) s'‖ := dist_eq_norm _ _
      _ = ‖(L t) (s - s')‖ := by rw [← map_sub]
      _ ≤ ‖L t‖ * ‖s - s'‖ := (L t).le_opNorm _
      _ ≤ (K : ℝ) * ‖s - s'‖ := mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
      _ = (K : ℝ) * dist s s' := by rw [dist_eq_norm]
  · intro s _
    exact (hLc s).add hb

/-- **State-constrained section-space local solution from the mild bounded-linear generator + source
interface.**  Runs the mild-operator `picard` field
(`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source`) all
the way through the a-posteriori closed-ball bridge
(`IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`) to a genuine
`BanachEvolutionLocalSolutionIn (fun t s => L t s + b t) locus t₀ x0` — precisely the state-constrained
Banach evolution object a downstream `realization` decode into an intrinsic De Turck local solution
consumes.

The analytic inputs are exactly the mild (regularised) generator data: `L t : CSS →L[ℝ] CSS` a
bounded linear operator with uniform operator-norm bound `‖L t‖ ≤ K` on `[t₀, T₀]`, strong time
continuity of `L`, a continuous source `b`, and the a-priori containment `closedBall x0 a ⊆ locus` of
the Picard ball in the prescribed state locus (e.g. the Riemannian metric cone).  With `F` complete
the section space is a Banach space, so the Picard–Lindelöf solution — which stays in `closedBall x0 a`
on the whole window — is a `locus`-valued local solution with no interval shrinking.  This is the
picard→solution half of the chart, reduced to *exhibiting the regularised generator family*. -/
theorem exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_boundedLinear_generator_source
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (L : ℝ →
      (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hK : ∀ t ∈ Set.Icc t₀ T₀, ‖L t‖ ≤ (K : ℝ))
    (hLc : ∀ s, ContinuousOn (fun t => (L t) s) (Set.Icc t₀ T₀))
    (hb : ContinuousOn b (Set.Icc t₀ T₀))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn (fun t s => (L t) s + b t) locus t₀ x0) := by
  obtain ⟨T, hT, Mc, hPL⟩ :=
    exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source
      L b x0 t₀ T₀ hT₀ a K ha hK hLc hb
  exact IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT hPL hsub

/-- **Fixed-window section-space Picard–Lindelöf from section-norm Lipschitz + time-continuity +
centre bound.**  The prescribed-endpoint analogue of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn`: the
window `[t₀, T]` is *supplied by the caller* (not chosen internally), which is exactly what the
`TimeDependentGeometricRicciDeTurckBanachChart.picard` field needs — the chart fixes `t₀` and `T`.
From

* `hlip` — for each `t ∈ [t₀, T]`, the time-slice operator `A t` is `K`-`LipschitzOnWith` on the
  section-space ball `closedBall x0 a`,
* `hcont` — for each section `s ∈ closedBall x0 a`, the time-curve `t ↦ A t s` is
  `ContinuousOn [t₀, T]` in the section-space norm,
* `hcenter` — the centre readout is bounded, `‖(A t x0)ᵢ x‖ ≤ Mc` on the window, and
* `hLa` — the time-radius compatibility `(Mc + K·a)·(T − t₀) ≤ a`,

`A` is `IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 (Mc + K·a) K` on `[t₀, T]` — the chart's exact `picard`
shape.  The section-norm `hlip`/`hcont` are pushed to the coordinatewise hypotheses of
`isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` by the `1`-Lipschitz coordinate
readout (`coord_dist_le_dist`) and `continuousOn_coord_of_continuousOn`; only the coordinate centre
bound `hcenter` and the compatibility `hLa` remain, both stated at the level the chart provides. -/
theorem isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, LipschitzOnWith K (A t) (Metric.closedBall x0 (a : ℝ)))
    (hcont : ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ContinuousOn (fun t => A t s) (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ T hT a K Mc ?_ ?_ hcenter hLa
  · intro t ht s hs s' hs' i x
    exact le_trans (coord_dist_le_dist (A t s) (A t s') i x)
      ((hlip t ht).dist_le_mul s hs s' hs')
  · intro s hs i
    exact continuousOn_coord_of_continuousOn (hcont hs) i

/-- **Fixed-window chart `picard` field from the mild bounded-linear generator + source interface.**
The prescribed-endpoint form of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source`,
producing `IsPicardLindelof (fun t s => L t s + b t) ⟨t₀,_⟩ x0 a 0 (Mc + K·a) K` on a caller-supplied
window `[t₀, T]` — i.e. the `TimeDependentGeometricRicciDeTurckBanachChart.picard` field verbatim, with
`L := Mc + K·a` (the bound) and `Kpic := K` (the Lipschitz constant).

The mild (regularised) generator data are: `L t : CSS →L[ℝ] CSS` a bounded linear operator with
uniform operator-norm bound `‖L t‖ ≤ K` on `[t₀, T]`, strong time continuity of `L`, a continuous
source `b`, a coordinate centre bound `‖(L t x0 + b t)ᵢ x‖ ≤ Mc` on the window, and the time-radius
compatibility `(Mc + K·a)·(T − t₀) ≤ a`.  The affine identity discharges the section-norm
`LipschitzOnWith K` hypothesis (`dist (L t s + b t) (L t s' + b t) = ‖L t (s − s')‖ ≤ ‖L t‖·‖s − s'‖ ≤
K·dist s s'`); strong continuity of `L` plus continuity of `b` discharge the time-continuity; the
remaining centre bound and compatibility are supplied at the level the chart provides. -/
theorem isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source_fixedWindow
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (L : ℝ →
      (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hK : ∀ t ∈ Set.Icc t₀ T, ‖L t‖ ≤ (K : ℝ))
    (hLc : ∀ s, ContinuousOn (fun t => (L t) s) (Set.Icc t₀ T))
    (hb : ContinuousOn b (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
            ((L t) x0 + b t)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof (fun t s => (L t) s + b t) (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn_centerBound
    (fun t s => (L t) s + b t) x0 t₀ T hT a K Mc ?_ ?_ hcenter hLa
  · intro t ht
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s _ s' _
    calc
      dist ((L t) s + b t) ((L t) s' + b t)
          = dist ((L t) s) ((L t) s') := dist_add_right _ _ _
      _ = ‖(L t) s - (L t) s'‖ := dist_eq_norm _ _
      _ = ‖(L t) (s - s')‖ := by rw [← map_sub]
      _ ≤ ‖L t‖ * ‖s - s'‖ := (L t).le_opNorm _
      _ ≤ (K : ℝ) * ‖s - s'‖ := mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
      _ = (K : ℝ) * dist s s' := by rw [dist_eq_norm]
  · intro s _
    exact (hLc s).add hb

/-- **Time-dependent fiberwise bundle-endomorphism generator.**  The time-slice
`endoFieldFamily et … hΦ C hC hbound t = endoField (Φ t)` packages a family of endomorphism-bundle
sections `Φ : ℝ → Π x, V x →L[ℝ] V x`, each continuous into the endomorphism (hom) bundle and each
with the uniform trivialization-distorted fiber bound `C`, as a time-dependent bounded section-space
generator `ℝ → (CSS →L[ℝ] CSS)` — the honest zeroth-order `L t` shape the affine section-space
Picard–Lindelöf capstone consumes. -/
noncomputable def endoFieldFamily
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ C) :
    ℝ →
      (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
  fun t => endoField (V := V) et Kc hKc Ko hKo hKoEq hcover (hΦ t) C hC (fun i x => hbound t i x)

@[simp]
theorem endoFieldFamily_apply
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ C)
    (t : ℝ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ C hC hbound t s) x = Φ t x (s x) :=
  rfl

/-- The time-slice of `endoFieldFamily` has operator norm at most the uniform fiber bound `C`. -/
theorem endoFieldFamily_norm_le
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ C)
    (t : ℝ) :
    ‖endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ C hC hbound t‖ ≤ C :=
  endoField_norm_le (V := V) et Kc hKc Ko hKo hKoEq hcover (hΦ t) C hC (fun i x => hbound t i x)

/-- **Strong time-continuity of the time-dependent endomorphism generator.**  From joint continuity
of `Φ : ℝ → Π x, V x →L[ℝ] V x` into the endomorphism (hom) bundle, each section curve
`t ↦ endoFieldFamily … t s` is `ContinuousOn timeSet` in the finite-cover Banach norm — the affine
Picard `hLc` hypothesis for the generator `L t = endoFieldFamily … t`. -/
theorem endoFieldFamily_continuousOn
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ C)
    (hΦjoint : Continuous
      (fun p : ℝ × M =>
        Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) p.2 (Φ p.1 p.2)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (timeSet : Set ℝ) :
    ContinuousOn
      (fun t => endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ C hC hbound t s) timeSet :=
  endoFieldLinearMap_continuousOn (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ hΦjoint s timeSet

/-- **Endpoint-choosing chart `picard` field from a time-dependent bundle-endomorphism generator +
source.**  The fiberwise-endomorphism specialization of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source`: the
bounded linear generator is `L t = endoFieldFamily … t` (`s ↦ (x ↦ Φ t x (s x))`) for a family of
endomorphism-bundle sections `Φ : ℝ → Π x, V x →L[ℝ] V x` that is jointly continuous into the
endomorphism (hom) bundle, and the affine operator is `A t s = (x ↦ Φ t x (s x)) + b t`.

The analytic inputs collapse to *exhibiting a jointly continuous endomorphism family with a uniform
trivialization-distorted fiber bound `‖clmAt‖·‖Φ t x‖·‖symmL‖ ≤ K` together with a continuous source
`b`*: the fiber bound both constructs the generator and supplies the uniform operator-norm bound
`‖L t‖ ≤ K` (`endoFieldFamily_norm_le`); joint continuity supplies the strong time-continuity
(`endoFieldFamily_continuousOn`); and the centre readout size `Mc` and a forward window `T ∈ (t₀, T₀]`
are chosen internally.  The result is the chart's exact `IsPicardLindelof … x0 a 0 (Mc + K·a) K`
shape, reducing the `picard` field for a zeroth-order (curvature/reaction) operator to a single joint
continuity plus fiber-norm estimate. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_endoField_source
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (hΦjoint : Continuous
      (fun p : ℝ × M =>
        Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) p.2 (Φ p.1 p.2)))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ (K : ℝ))
    (hb : ContinuousOn b (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun t s =>
          (endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound t) s + b t)
        (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K :=
  exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source
    (endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound)
    b x0 t₀ T₀ hT₀ a K ha
    (fun t _ =>
      endoFieldFamily_norm_le et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound t)
    (fun s =>
      endoFieldFamily_continuousOn et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound
        hΦjoint s (Set.Icc t₀ T₀))
    hb

/-- **State-constrained section-space local solution from a time-dependent bundle-endomorphism
generator + source.**  Runs the endomorphism-generator affine `picard` field all the way through the
a-posteriori closed-ball bridge to a genuine
`BanachEvolutionLocalSolutionIn (fun t s => (x ↦ Φ t x (s x)) + b t) locus t₀ x0` — precisely the
state-constrained Banach evolution object a downstream `realization` decode into an intrinsic De Turck
local solution consumes.

Compared with
`exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_boundedLinear_generator_source`, the
bounded linear generator is exhibited concretely as `endoFieldFamily … t = endoField (Φ t)` for a
jointly continuous endomorphism-bundle family `Φ : ℝ → Π x, V x →L[ℝ] V x` with the uniform
trivialization-distorted fiber bound `K`.  With `F` complete the section space is Banach, so the
Picard–Lindelöf solution — staying in `closedBall x0 a` on the whole window — is a `locus`-valued local
solution with no interval shrinking, provided the a-priori containment `closedBall x0 a ⊆ locus`.  This
is the picard→solution half of the chart for the zeroth-order (curvature/reaction) part, reduced to
*exhibiting a jointly continuous endomorphism family, a continuous source, and the ball containment*. -/
theorem exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_endoField_source
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {Φ : ℝ → ∀ x : M, V x →L[ℝ] V x}
    (hΦ : ∀ t, Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ t x)))
    (hΦjoint : Continuous
      (fun p : ℝ × M =>
        Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) p.2 (Φ p.1 p.2)))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hbound : ∀ (t : ℝ) (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ t x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ (K : ℝ))
    (hb : ContinuousOn b (Set.Icc t₀ T₀))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (fun t s =>
        (endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound t) s + b t)
      locus t₀ x0) :=
  exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_boundedLinear_generator_source
    (endoFieldFamily et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound)
    b x0 locus t₀ T₀ hT₀ a K ha
    (fun t _ =>
      endoFieldFamily_norm_le et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound t)
    (fun s =>
      endoFieldFamily_continuousOn et Kc hKc Ko hKo hKoEq hcover hΦ (K : ℝ) K.coe_nonneg hbound
        hΦjoint s (Set.Icc t₀ T₀))
    hb hsub

/-- **Autonomous (frozen-coefficient) specialization.**  When the reaction endomorphism is
*time-independent* — a single continuous endomorphism-bundle section `Φ₀ : Π x, V x →L[ℝ] V x` — the
joint `(t, x)`-continuity hypothesis is free (`Φ₀ ∘ snd`), so the whole endomorphism-generator route
collapses to a single spatial continuity input.  From `Φ₀` continuous into the endomorphism (hom)
bundle with uniform trivialization-distorted fiber bound `K`, a continuous source `b`, and the
containment `closedBall x0 a ⊆ locus`, this produces the state-constrained Banach local solution of the
autonomous affine operator `A t s = (x ↦ Φ₀ x (s x)) + b t` — precisely the shape the first geometric
instantiation (a frozen background metric `g₀`, whose zeroth-order reaction coefficient does not depend
on time) supplies. -/
theorem exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_endoField_source_const
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {Φ₀ : ∀ x : M, V x →L[ℝ] V x}
    (hΦ₀ : Continuous
      (fun x => Bundle.TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) x (Φ₀ x)))
    (b : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖Φ₀ x.1‖ * ‖(et i).symmL ℝ x.1‖ ≤ (K : ℝ))
    (hb : ContinuousOn b (Set.Icc t₀ T₀))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (fun t s =>
        (endoField (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ₀ (K : ℝ) K.coe_nonneg hbound) s + b t)
      locus t₀ x0) :=
  exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_endoField_source
    (Φ := fun _ => Φ₀) (fun _ => hΦ₀) (hΦ₀.comp continuous_snd)
    b x0 locus t₀ T₀ hT₀ a K ha (fun _ i x => hbound i x) hb hsub

/-! ### Topological-fibre section-space Picard bridges (Path-B compatible)

The centre-bound section-space Picard bridges above carry a fibre
`[∀ x, SeminormedAddCommGroup (V x)]`, whose *induced* fibre topology (Path A) is baked into their
`ContinuousSectionSpace` type — while the concrete `BilinearFormBundle` continuous section space (with
fibre `V x = W x →L[ℝ] W x →L[ℝ] ℝ`) carries the *defeq-but-differently-spelled*
`ContinuousLinearMap.topologicalSpace` (Path B), the topology `FiberBundle`/`VectorBundle` and the
concrete coordinate readout lemmas use.  Since none of the bridge machinery ever touches a fibre norm
(all estimates are at the Banach `F`-norm / coordinate level), the two lemmas below restate the
centre-bound bridge with the fibre topology taken as an *explicit* `[∀ x, TopologicalSpace (V x)]`
binder (plus the bare `AddCommGroup`/`Module` structure the vector bundle provides), routing the
time-continuity / centre-norm handoffs through the topological-fibre helpers
`continuousOn_of_forall_coord_continuousOn_topFibre` / `norm_le_of_forall_coord_norm_le_topFibre`.
This lets the section-space Picard bridge apply verbatim to the concrete `BilinearFormBundle`
continuous section space (Path B), so the geometric Ricci–De Turck reaction operator's already-proved
coordinate `hlip`/`hcenter` bounds are consumed directly. -/

/-- **Topological-fibre version of `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`.**
Identical statement and proof, with the fibre topology taken as an explicit
`[∀ x, TopologicalSpace (V x)]` binder (instead of derived from a `SeminormedAddCommGroup (V x)`), so
the section space is built with the caller's fibre topology.  The time-continuity and centre-norm
handoffs go through the topological-fibre helpers. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound_topFibre
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc
    A x0 t₀ T hT a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact lipschitzOnWith_of_forall_coord_dist_le
      (fun s hs s' hs' i x => hlip t ht hs hs' i x)
  · intro s hs
    exact continuousOn_of_forall_coord_continuousOn_topFibre (fun i => hcont s hs i)
  · intro t ht
    exact norm_le_of_forall_coord_norm_le_topFibre (NNReal.coe_nonneg Mc)
      (fun i x => hcenter t ht i x)

/-- **Topological-fibre version of
`sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound`.**  Identical
statement and proof, with the fibre topology taken as an explicit `[∀ x, TopologicalSpace (V x)]`
binder.  Combines the topological-fibre centre-bound section-space Picard constructor with the
closed-ball a-posteriori bridge `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`
(a Banach-space fact with no fibre instances).  This is the form the geometric Ricci–De Turck chart's
`realization` decode consumes for the concrete `BilinearFormBundle` (Path-B) continuous section
space. -/
theorem sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound_topFibre
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn A locus t₀ x0) :=
  IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT
    (isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound_topFibre
      A x0 t₀ T hT a K Mc hlip hcont hcenter hLa) hsub

/-- **Topological-fibre version of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn`.**
Identical statement and proof, with the fibre topology taken as an explicit
`[∀ x, TopologicalSpace (V x)]` binder.  From coordinatewise Lipschitz-in-section and
time-continuity data on a reference window `Icc t₀ T₀`, a forward Picard endpoint `T ∈ (t₀, T₀]` and
centre size `Mc` are produced for which `A` is `IsPicardLindelof` with radius `a`, Lipschitz `K`, and
bound `Mc + K·a` — the chart's `picard` field shape, obtained for a section space whose fibre carries
a non-seminormed-derived (Path-B) topology.  The centre-readout size constant and the centre-bound
Picard constructor go through the topological-fibre helpers. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T₀, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_forall_mem_Icc_coord_norm_le_of_continuousOn_topFibre
      (f := fun t => A t x0) (t₀ := t₀) (T := T₀)
      (hcont x0 (Metric.mem_closedBall_self ha.le))
  set Mc : ℝ≥0 := C.toNNReal with hMc
  have hCMc : C ≤ (Mc : ℝ) := by
    rw [hMc]; exact (Real.coe_toNNReal C hC0).ge
  obtain ⟨T', hT', hLa'⟩ :=
    RicciFlow.AnalyticPDE.exists_forwardTime_mul_sub_le t₀ a K Mc ha
  have hTle : min T' T₀ ≤ T₀ := min_le_right T' T₀
  have hstep : (min T' T₀ - t₀) ≤ (T' - t₀) := by
    have := min_le_left T' T₀; linarith
  refine ⟨min T' T₀, lt_min hT' hT₀, Mc, ?_⟩
  have hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀) ≤ (a : ℝ) := by
    calc ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀)
        ≤ ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T' - t₀) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (a : ℝ) := hLa'
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound_topFibre
    A x0 t₀ (min T' T₀) (lt_min hT' hT₀) a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact hlip t ⟨ht.1, le_trans ht.2 hTle⟩
  · intro s hs i
    exact (hcont s hs i).mono (Set.Icc_subset_Icc le_rfl hTle)
  · intro t ht i x
    exact le_trans (hCbound t ⟨ht.1, le_trans ht.2 hTle⟩ i x) hCMc

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
