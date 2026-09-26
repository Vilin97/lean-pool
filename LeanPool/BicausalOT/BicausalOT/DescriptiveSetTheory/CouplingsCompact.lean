/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Compactness of coupling sets in the topology of weak convergence

  Blueprint: BLUEPRINT.md §7, wave 3, front F3. For Borel Polish spaces
  `A`, `B` and probability measures `mu` on `A`, `nu` on `B`, the set of
  couplings `{γ | fst_* γ = mu ∧ snd_* γ = nu}` is compact in
  `ProbabilityMeasure (A × B)` with the topology of weak convergence.

  Route: (i) the coupling set is uniformly TIGHT — `mu` and `nu` are
  individually tight (`isTightMeasureSet_singleton`, Polish ⇒ completely
  metrizable + second countable), and for any coupling `γ`,
  `γ ((K₁ ×ˢ K₂)ᶜ) ≤ γ (K₁ᶜ ×ˢ univ) + γ (univ ×ˢ K₂ᶜ) = mu K₁ᶜ + nu K₂ᶜ`
  via the marginal equations (`Set.compl_prod_eq_union`,
  `Measure.map_apply measurable_fst`); (ii) Prokhorov
  (`isCompact_closure_of_isTightMeasureSet`) gives compactness of the
  closure; (iii) the set is CLOSED
  (`isClosed_probabilityMeasure_couplings` below), so it equals
  its closure.

  The `Measure.map`-level reformulations matching the shape of
  the repository's marginal constraints (`CouplingSet₀` in Defs.lean,
  `MultiPeriod.Feas`) are provided, including the unconditional plain-
  `Measure`-target version (empty when a target is not a probability
  measure — and the empty set is compact).

  Nonemptiness follows from the product coupling
  (`ProbabilityMeasure.prod`, `ProbabilityMeasure.map_fst_prod`).
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic


/-! ## Translation between `ProbabilityMeasure.map` and `Measure.map` constraints -/

@[expose] public section

open MeasureTheory Topology

noncomputable section



section Translation

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- A marginal-type constraint on a `ProbabilityMeasure` can be stated equivalently via
`ProbabilityMeasure.map` or via `Measure.map` on the underlying measures. -/
theorem probabilityMeasure_map_eq_iff (γ : ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω')
    (f : Ω → Ω') :
    γ.map f = μ ↔ (γ : Measure Ω).map f = (μ : Measure Ω') := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact h

end Translation

/-! ## Closedness of coupling sets -/

section Couplings

variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

/-- On Borel Polish spaces, the set of couplings of `mu` and `nu` is closed in the topology of weak
convergence. -/
theorem isClosed_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.fst = mu ∧ γ.map Prod.snd = nu} := by
  have hfst : IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.fst = mu} :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)
  have hsnd : IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.snd = nu} :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd)
  exact hfst.inter hsnd

omit [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [BorelSpace B] in
/-- The coupling set stated with `Measure.map` constraints on the underlying measures
(the shape used by `CouplingSet₀` and `MultiPeriod.Feas`) coincides with the coupling
set stated via `ProbabilityMeasure.map`. -/
theorem probabilityMeasure_couplings_toMeasure_eq
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    {γ : ProbabilityMeasure (A × B) |
        (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)}
      = {γ : ProbabilityMeasure (A × B) |
          γ.map Prod.fst = mu ∧
          γ.map Prod.snd = nu} := by
  ext γ
  exact and_congr (probabilityMeasure_map_eq_iff γ mu Prod.fst).symm
    (probabilityMeasure_map_eq_iff γ nu Prod.snd).symm

/-! ## Tightness of coupling sets (front F3, new) -/

/-- **F3, tightness, `Measure` level.** On Borel Polish spaces, the set of measures on
`A × B` with marginals `mu` and `nu` is uniformly tight: `mu` and `nu` are individually
tight, and if `K₁`, `K₂` capture all but `ε / 2` of the mass of `mu`, `nu` respectively,
then `K₁ ×ˢ K₂` captures all but `ε` of the mass of every coupling, by the marginal
equations. -/
theorem isTightMeasureSet_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {γm : Measure (A × B) |
      γm.map Prod.fst = (mu : Measure A) ∧ γm.map Prod.snd = (nu : Measure B)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K₁, hK₁, hK₁le⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := (mu : Measure A))) (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂, hK₂le⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := (nu : Measure B))) (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, ?_⟩
  rintro γm ⟨hfst, hsnd⟩
  calc γm ((K₁ ×ˢ K₂)ᶜ)
      = γm ((K₁ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ K₂ᶜ)) := by rw [Set.compl_prod_eq_union]
    _ ≤ γm (K₁ᶜ ×ˢ Set.univ) + γm (Set.univ ×ˢ K₂ᶜ) := measure_union_le _ _
    _ = (mu : Measure A) K₁ᶜ + (nu : Measure B) K₂ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
          ← Measure.map_apply measurable_fst hK₁.isClosed.measurableSet.compl,
          ← Measure.map_apply measurable_snd hK₂.isClosed.measurableSet.compl, hfst, hsnd]
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hK₁le _ (Set.mem_singleton _)) (hK₂le _ (Set.mem_singleton _))
    _ = ε := ENNReal.add_halves ε

/-- **F3, tightness, image form.** The underlying measures of the coupling set of `mu`
and `nu` form a tight set of measures — the exact hypothesis shape of Prokhorov's
theorem `isCompact_closure_of_isTightMeasureSet`. -/
theorem isTightMeasureSet_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {((γ : ProbabilityMeasure (A × B)) : Measure (A × B)) |
      γ ∈ {γ' : ProbabilityMeasure (A × B) |
        γ'.map Prod.fst = mu ∧
        γ'.map Prod.snd = nu}} := by
  refine (isTightMeasureSet_couplings mu nu).subset ?_
  rintro x ⟨γ, ⟨h₁, h₂⟩, rfl⟩
  exact ⟨(probabilityMeasure_map_eq_iff γ mu Prod.fst).1 h₁,
    (probabilityMeasure_map_eq_iff γ nu Prod.snd).1 h₂⟩

/-! ## Compactness of coupling sets (front F3, main results) -/

/-- **F3, MAIN TARGET.** On Borel Polish spaces, the set of couplings of `mu` and `nu`
is compact in the topology of weak convergence: it is tight
(`isTightMeasureSet_probabilityMeasure_couplings`), so its closure is compact by
Prokhorov's theorem, and it is closed (`isClosed_probabilityMeasure_couplings`), so it
equals its closure. -/
theorem isCompact_probabilityMeasure_couplings
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.fst = mu ∧ γ.map Prod.snd = nu} := by
  have hcompact : IsCompact (closure {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.fst = mu ∧ γ.map Prod.snd = nu}) :=
    isCompact_closure_of_isTightMeasureSet
      (isTightMeasureSet_probabilityMeasure_couplings mu nu)
  rwa [(isClosed_probabilityMeasure_couplings mu nu).closure_eq] at hcompact

/-- **F3, `Measure` level, `ProbabilityMeasure` targets.** The set of probability
measures on `A × B` whose underlying measure has marginals `mu` and `nu` is compact in
the topology of weak convergence. -/
theorem isCompact_probabilityMeasure_couplings_toMeasure
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)} := by
  rw [probabilityMeasure_couplings_toMeasure_eq]
  exact isCompact_probabilityMeasure_couplings mu nu

/-- **F3, `Measure` level, plain `Measure` targets, unconditional.** For arbitrary
target measures `m`, `n` (the exact shape of `MultiPeriod.Feas` and `CouplingSet₀`,
reindexed over probability measures on the product), the constraint set is compact in
the topology of weak convergence: if either target fails to be a probability measure
the set is empty, and the empty set is compact. -/
theorem isCompact_probabilityMeasure_marginals (m : Measure A) (n : Measure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = m ∧ (γ : Measure (A × B)).map Prod.snd = n} := by
  by_cases hm : IsProbabilityMeasure m
  · by_cases hn : IsProbabilityMeasure n
    · exact isCompact_probabilityMeasure_couplings_toMeasure ⟨m, hm⟩ ⟨n, hn⟩
    · have hempty : {γ : ProbabilityMeasure (A × B) |
          (γ : Measure (A × B)).map Prod.fst = m ∧
          (γ : Measure (A × B)).map Prod.snd = n} = ∅ := by
        ext γ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h2
        exact hn (h2 ▸ (inferInstance : IsProbabilityMeasure ((γ : Measure (A × B)).map Prod.snd)))
      rw [hempty]
      exact isCompact_empty
  · have hempty : {γ : ProbabilityMeasure (A × B) |
        (γ : Measure (A × B)).map Prod.fst = m ∧
        (γ : Measure (A × B)).map Prod.snd = n} = ∅ := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 _
      exact hm (h1 ▸ (inferInstance : IsProbabilityMeasure ((γ : Measure (A × B)).map Prod.fst)))
    rw [hempty]
    exact isCompact_empty

/-! ## Nonemptiness via the product coupling -/

omit [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [BorelSpace B] in
/-- The coupling set is nonempty: the product measure `mu ⊗ nu` is a coupling.
Together with `isCompact_probabilityMeasure_couplings` this yields a NONEMPTY COMPACT
coupling set — the Existence-upgrade prize. -/
theorem probabilityMeasure_couplings_nonempty
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    {γ : ProbabilityMeasure (A × B) |
      γ.map Prod.fst = mu ∧
      γ.map Prod.snd = nu}.Nonempty :=
  ⟨mu.prod nu, ProbabilityMeasure.map_fst_prod mu nu, ProbabilityMeasure.map_snd_prod mu nu⟩

end Couplings

end
