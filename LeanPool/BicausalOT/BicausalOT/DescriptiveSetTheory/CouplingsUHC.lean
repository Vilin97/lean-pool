/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Sequential Upper Hemicontinuity of the Couplings Correspondence

  Phase 5, File 1 (BLUEPRINT §4F). The couplings correspondence
  Π : P(A) × P(B) → Set P(A × B) is sequentially upper hemicontinuous:
  along convergent marginal sequences, couplings admit convergent
  subsequences whose limits couple the limit marginals (U3). Hit-sets of
  closed targets are closed (U4), and hit-sets of open targets are Borel
  via the Fσ decomposition of opens in metrizable spaces (U5).

  Route: convergent sequences of probability measures are tight (U1,
  via compactness of the closure of the range and Mathlib's converse
  Prokhorov `isTightMeasureSet_of_isCompact_closure`); couplings of
  tight families are tight (U2, slab bound); Prokhorov + metrizability
  extract convergent subsequences whose marginals are identified by
  continuity of the pushforward (U3).
-/
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.CouplingsCompact
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.ProbabilityMeasurePolish

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## U1: convergent sequences of probability measures are tight -/

/-- A convergent sequence of probability measures on a Polish space is a
    tight family (converse Prokhorov on the compact closure of its range). -/
theorem isTightMeasureSet_range_of_tendsto {Ω : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {γs : ℕ → ProbabilityMeasure Ω} {γ : ProbabilityMeasure Ω}
    (hγ : Tendsto γs atTop (𝓝 γ)) :
    IsTightMeasureSet {((γs n : ProbabilityMeasure Ω) : Measure Ω) | n : ℕ} := by
  have hins : IsCompact (insert γ (Set.range γs)) := hγ.isCompact_insert_range
  have hclos : IsCompact (closure (Set.range γs)) :=
    hins.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert γ (Set.range γs)) hins.isClosed)
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Ω
  have htight := isTightMeasureSet_of_isCompact_closure hclos
  have hset : {((μ : ProbabilityMeasure Ω) : Measure Ω) | μ ∈ Set.range γs}
      = {((γs n : ProbabilityMeasure Ω) : Measure Ω) | n : ℕ} := by
    ext m
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨γs n, ⟨n, rfl⟩, rfl⟩
  rwa [hset] at htight

/-! ## U2: couplings of tight families are tight -/

variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

/-- Couplings whose marginals range over tight families form a tight
    family: the slab bound `γ ((K₁ ×ˢ K₂)ᶜ) ≤ μ K₁ᶜ + ν K₂ᶜ`. -/
theorem isTightMeasureSet_couplings_of_isTightMeasureSet
    {S : Set (Measure A)} {T : Set (Measure B)}
    (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet
      {γm : Measure (A × B) | γm.map Prod.fst ∈ S ∧ γm.map Prod.snd ∈ T} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS hT ⊢
  intro ε hε
  obtain ⟨K₁, hK₁c, hK₁⟩ := hS (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂c, hK₂⟩ := hT (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ ×ˢ K₂, hK₁c.prod hK₂c, fun γm hγm => ?_⟩
  calc γm ((K₁ ×ˢ K₂)ᶜ)
      = γm ((K₁ᶜ ×ˢ univ) ∪ (univ ×ˢ K₂ᶜ)) := by rw [Set.compl_prod_eq_union]
    _ ≤ γm (K₁ᶜ ×ˢ univ) + γm (univ ×ˢ K₂ᶜ) := measure_union_le _ _
    _ = (γm.map Prod.fst) K₁ᶜ + (γm.map Prod.snd) K₂ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
          Measure.map_apply measurable_fst hK₁c.isClosed.measurableSet.compl,
          Measure.map_apply measurable_snd hK₂c.isClosed.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 := add_le_add (hK₁ _ hγm.1) (hK₂ _ hγm.2)
    _ = ε := ENNReal.add_halves ε

/-! ## U3: sequential upper hemicontinuity of the couplings correspondence -/

/-- **Sequential upper hemicontinuity.** Along convergent marginal
    sequences, any sequence of couplings admits a subsequence converging
    to a coupling of the limit marginals (tightness + Prokhorov +
    continuity of the marginal maps). -/
theorem exists_tendsto_subseq_couplings
    {μs : ℕ → ProbabilityMeasure A} {μ : ProbabilityMeasure A}
    {νs : ℕ → ProbabilityMeasure B} {ν : ProbabilityMeasure B}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    {γs : ℕ → ProbabilityMeasure (A × B)}
    (hfst : ∀ n, (γs n : Measure (A × B)).map Prod.fst = (μs n : Measure A))
    (hsnd : ∀ n, (γs n : Measure (A × B)).map Prod.snd = (νs n : Measure B)) :
    ∃ γ : ProbabilityMeasure (A × B),
      (γ : Measure (A × B)).map Prod.fst = (μ : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (ν : Measure B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (γs ∘ φ) atTop (𝓝 γ) := by
  -- the couplings are a tight family
  have htight : IsTightMeasureSet
      {((γs n : ProbabilityMeasure (A × B)) : Measure (A × B)) | n : ℕ} := by
    have h12 := isTightMeasureSet_couplings_of_isTightMeasureSet
      (isTightMeasureSet_range_of_tendsto hμ)
      (isTightMeasureSet_range_of_tendsto hν)
    refine h12.subset ?_
    rintro m ⟨n, rfl⟩
    exact ⟨⟨n, (hfst n).symm⟩, ⟨n, (hsnd n).symm⟩⟩
  -- Prokhorov: the closure of the range is compact
  have hcomp : IsCompact (closure (Set.range γs)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have hset : {((γ' : ProbabilityMeasure (A × B)) : Measure (A × B)) |
        γ' ∈ Set.range γs}
        = {((γs n : ProbabilityMeasure (A × B)) : Measure (A × B)) | n : ℕ} := by
      ext m
      constructor
      · rintro ⟨γ', ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨γs n, ⟨n, rfl⟩, rfl⟩
    rwa [hset]
  -- extract a convergent subsequence
  obtain ⟨γ, -, φ, hφmono, hφt⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  -- identify the marginals of the limit by continuity of the pushforward
  have hfst' : (γ : Measure (A × B)).map Prod.fst = (μ : Measure A) := by
    refine (probabilityMeasure_map_eq_iff γ μ measurable_fst).mp ?_
    refine tendsto_nhds_unique ?_ (hμ.comp hφmono.tendsto_atTop)
    have hc := MeasureTheory.ProbabilityMeasure.continuous_map
      (Ω := A × B) (Ω' := A) continuous_fst
    have := (hc.tendsto γ).comp hφt
    refine (tendsto_congr fun k => ?_).mp this
    exact (probabilityMeasure_map_eq_iff _ _ measurable_fst).mpr (hfst (φ k))
  have hsnd' : (γ : Measure (A × B)).map Prod.snd = (ν : Measure B) := by
    refine (probabilityMeasure_map_eq_iff γ ν measurable_snd).mp ?_
    refine tendsto_nhds_unique ?_ (hν.comp hφmono.tendsto_atTop)
    have hc := MeasureTheory.ProbabilityMeasure.continuous_map
      (Ω := A × B) (Ω' := B) continuous_snd
    have := (hc.tendsto γ).comp hφt
    refine (tendsto_congr fun k => ?_).mp this
    exact (probabilityMeasure_map_eq_iff _ _ measurable_snd).mpr (hsnd (φ k))
  exact ⟨γ, hfst', hsnd', φ, hφmono, hφt⟩

/-! ## U4: hit-sets of closed targets are closed -/

/-- **Closed hit-sets (E3-B).** For a closed set `C` of joint laws, the
    set of marginal pairs whose couplings meet `C` is closed. -/
theorem isClosed_couplings_hit
    {C : Set (ProbabilityMeasure (A × B))} (hC : IsClosed C) :
    IsClosed {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ C, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
  refine isClosed_of_closure_subset fun p hp => ?_
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨ps, hmem, hlim⟩ := hp
  choose γs hγC hγfst hγsnd using hmem
  have hμ : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
    ((continuous_fst.tendsto p).comp hlim)
  have hν : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
    ((continuous_snd.tendsto p).comp hlim)
  obtain ⟨γ, hf, hs, φ, -, hφt⟩ :=
    exists_tendsto_subseq_couplings hμ hν hγfst hγsnd
  exact ⟨γ, hC.mem_of_tendsto hφt (Eventually.of_forall fun k => hγC (φ k)),
    hf, hs⟩

/-! ## U5: opens are Fσ in metrizable spaces; open hit-sets are Borel -/

/-- In a (pseudo)metrizable space every open set is a countable union of
    closed sets (complement of the Gδ representation of its complement;
    Mathlib's `IsOpen.exists_iUnion_isClosed` is the pseudo-emetric
    version — this one works directly at the topology level). -/
theorem IsOpen.exists_iUnion_isClosed_of_pseudoMetrizable
    {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n := by
  obtain ⟨T, hTopen, hTcount, hTeq⟩ := hU.isClosed_compl.isGδ
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- Uᶜ = ⋂₀ ∅ = univ, so U = ∅
    refine ⟨fun _ => ∅, fun _ => isClosed_empty, ?_⟩
    have : U = ∅ := by
      have h1 : Uᶜ = univ := by rw [hTeq, Set.sInter_empty]
      simpa [Set.compl_univ] using congrArg compl h1
    simp [this]
  · obtain ⟨f, rfl⟩ := hTcount.exists_eq_range hTne
    refine ⟨fun n => (f n)ᶜ, fun n =>
      (hTopen (f n) (Set.mem_range_self n)).isClosed_compl, ?_⟩
    have h1 : Uᶜ = ⋂ n, f n := by rw [hTeq, Set.sInter_range]
    calc U = Uᶜᶜ := (compl_compl U).symm
      _ = (⋂ n, f n)ᶜ := by rw [h1]
      _ = ⋃ n, (f n)ᶜ := by rw [Set.compl_iInter]

/-- **Borel hit-sets (E3-C).** For an open set `U` of joint laws, the set
    of marginal pairs whose couplings meet `U` is Borel — with respect to
    Borel σ-algebras of the weak topology on the factors (σ-algebra
    polymorphic via the `BorelSpace` constraints; NOT Mathlib's
    Giry-subtype σ-algebra). Decompose `U` into countably many closed
    sets and take the union of the closed hit-sets. -/
theorem measurableSet_couplings_hit
    {mPA : MeasurableSpace (ProbabilityMeasure A)}
    [BorelSpace (ProbabilityMeasure A)]
    {mPB : MeasurableSpace (ProbabilityMeasure B)}
    [BorelSpace (ProbabilityMeasure B)]
    {U : Set (ProbabilityMeasure (A × B))} (hU : IsOpen U) :
    MeasurableSet {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ U, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
  obtain ⟨C, hCclosed, rfl⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ ⋃ n, C n, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)}
      = ⋃ n, {p : ProbabilityMeasure A × ProbabilityMeasure B |
        ∃ γ ∈ C n, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
          (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, ⟨n, hγn⟩, hmarg⟩
      exact ⟨n, γ, hγn, hmarg⟩
    · rintro ⟨n, γ, hγn, hmarg⟩
      exact ⟨γ, ⟨n, hγn⟩, hmarg⟩
  rw [hsplit]
  exact MeasurableSet.iUnion fun n =>
    (isClosed_couplings_hit (hCclosed n)).measurableSet

end
