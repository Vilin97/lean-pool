/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Measurable feasible strategies in the Borel model (front E3-D)

  Blueprint: BLUEPRINT.md §4F File 4; design_krn.md §4.2. Without any
  continuity (Feller) or cost hypotheses, plain-Borel-measurable
  bicausal Markov strategies exist: the feasibility correspondence has
  compact (closed) nonempty values, and its hit-sets against open sets
  are Borel — the open set decomposes into countably many closed sets
  (Fσ), each closed hit-set of the couplings correspondence is closed
  in the weak topology (U4), and it pulls back along the marginal-pair
  map, which is measurable under the honest hypothesis that the kernels
  are weak-Borel measurable (`WeakP`-valued measurability; Giry
  measurability would NOT suffice — that is the open PR3 direction).
  Kuratowski–Ryll-Nardzewski then selects measurably.
-/
import LeanPool.BicausalOT.BicausalOT.LscBellman

/-!
# MeasurableFeasibleStrategy

Supporting results for bicausal optimal transport and measurable selection.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace MultiPeriod

variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]

variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))

/-- Hit-sets of the feasibility fibers against open sets are Borel, for
    weak-Borel measurable kernels: Fσ decomposition of the open set and
    transport of the closed couplings hit-sets (U4) along the measurable
    marginal-pair map. -/
theorem measurableSet_feasGraph_fiber_hit_of_measurable
    (hκμ_measW : ∀ t, @Measurable (XHist X t) (WeakP (X (t + 1)))
      _ _ (κμP t))
    (hκν_measW : ∀ t, @Measurable (YHist Y t) (WeakP (Y (t + 1)))
      _ _ (κνP t)) (t : ℕ)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ U).Nonempty} := by
  obtain ⟨C, hCclosed, hUeq⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ U).Nonempty}
      = ⋃ n, {h : PairHist X Y t |
        ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C n).Nonempty} := by
    rw [hUeq]
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, hγfib, hγU⟩
      obtain ⟨n, hγn⟩ := Set.mem_iUnion.mp hγU
      exact ⟨n, γ, hγfib, hγn⟩
    · rintro ⟨n, γ, hγfib, hγn⟩
      exact ⟨γ, hγfib, Set.mem_iUnion.mpr ⟨n, hγn⟩⟩
  rw [hsplit]
  refine MeasurableSet.iUnion fun n => ?_
  -- the marginal-pair map is measurable into the WeakP product
  have hm : @Measurable (PairHist X Y t)
      (WeakP (X (t + 1)) × WeakP (Y (t + 1))) _ _
      (fun h => (κμP t (projX t h), κνP t (projY t h))) :=
    ((hκμ_measW t).comp (measurable_projX t)).prodMk
      ((hκν_measW t).comp (measurable_projY t))
  -- the closed couplings hit-set is Borel in the WeakP product
  have hhit : IsClosed {p : ProbabilityMeasure (X (t + 1))
      × ProbabilityMeasure (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = (p.1 : Measure (X (t + 1))) ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = (p.2 : Measure (Y (t + 1)))} :=
    isClosed_couplings_hit (hCclosed n)
  have hhitW : IsClosed {p : WeakP (X (t + 1)) × WeakP (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = p.1.toMeasure ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = p.2.toMeasure} := hhit
  have hhitmeas := hhitW.measurableSet
  have hset : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C n).Nonempty}
      = (fun h : PairHist X Y t =>
          ((κμP t (projX t h), κνP t (projY t h))
            : WeakP (X (t + 1)) × WeakP (Y (t + 1)))) ⁻¹'
        {p : WeakP (X (t + 1)) × WeakP (Y (t + 1)) |
          ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
              = p.1.toMeasure ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
              = p.2.toMeasure} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨γ, hγfib, hγC⟩
      exact ⟨γ, hγC, hγfib.1, hγfib.2⟩
    · rintro ⟨γ, hγC, hfst, hsnd⟩
      exact ⟨γ, ⟨hfst, hsnd⟩, hγC⟩
  rw [hset]
  exact hm hhitmeas

/-- **Measurable feasible strategies exist (E3-D).** In the Borel model —
    weak-Borel measurable probability kernels, no continuity and no cost
    hypotheses — there is a strategy that is pointwise feasible and
    plain-Borel measurable at every stage: measurable bicausal Markov
    strategies exist. -/
theorem exists_measurable_feasible_strategy
    (hκμ_measW : ∀ t, @Measurable (XHist X t) (WeakP (X (t + 1)))
      _ _ (κμP t))
    (hκν_measW : ∀ t, @Measurable (YHist Y t) (WeakP (Y (t + 1)))
      _ _ (κνP t)) :
    ∃ γfeas : Strat X Y,
      (∀ t h, γfeas t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γfeas t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      Measurable φ ∧ ∀ h, (h, φ h) ∈ FeasGraph
        (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t := by
    intro t
    exact WeakP.exists_measurable_selection
      (fun h => feasGraph_fiber_nonempty' κμP κνP t h)
      (fun h => (isCompact_feasGraph_fiber κμP κνP t h).isClosed)
      (fun U hU => measurableSet_feasGraph_fiber_hit_of_measurable
        κμP κνP hκμ_measW hκν_measW t hU)
  choose φ hφmeas hφmem using key
  exact ⟨fun t h => (φ t h).toMeasure,
    fun t h => hφmem t h,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩

end MultiPeriod

end
