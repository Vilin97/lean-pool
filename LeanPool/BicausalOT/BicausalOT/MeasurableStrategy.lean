/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Phase 4: ε-optimal analytically measurable strategies
  (Bertsekas–Shreve Proposition 7.50 analogue, multi-period bicausal OT)

  Blueprint: BLUEPRINT.md §4 + docs/design_phase4.md. Architecture: for
  each stage `t`, the abstract selection theorem
  `exists_eps_optimal_selector` (EpsOptimalSelection.lean) is applied to
  the feasibility graph `FeasGraph` (Borel, hence analytic, by the Giry
  equalizer — Phase 3) and the integrated tail value
  `(h, γ) ↦ ∫⁻ z, VGo (T−t−1) (t+1) (h,z) ∂γ` (lower semianalytic by
  BS 7.48 applied to the evaluation kernel, with the integrand lower
  semianalytic by Phase 3). This upgrades the pointwise-choice strategy
  of `exists_eps_strategy` (L3) to one that is σ(Σ¹₁)-measurable at
  every stage, and the Bellman value representation restricts to such
  strategies without changing its value.
-/
import LeanPool.BicausalOT.BicausalOT.SemianalyticValue
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.EpsOptimalSelection

open MeasureTheory Set ENNReal

noncomputable section

namespace MultiPeriod

variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]

variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

/-! ## Fibers of the feasibility graph -/

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- Fibers of the feasibility graph are nonempty when the one-step
    feasible sets are: feasible plans of probability marginals are
    probability measures (L0). -/
theorem feasGraph_fiber_nonempty
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)), (h, γ) ∈ FeasGraph κμ κν t := by
  obtain ⟨γm, hγm⟩ := hne t h
  haveI hpm : IsProbabilityMeasure γm :=
    ⟨Feas.measure_univ κμ κν hκμ_prob hγm⟩
  exact ⟨show WeakP (X (t + 1) × Y (t + 1)) from
    (⟨γm, hpm⟩ : ProbabilityMeasure (X (t + 1) × Y (t + 1))), hγm⟩

/-! ## The stage objective is lower semianalytic (BS 7.48) -/

/-- The integrated tail value is lower semianalytic on the product of the
    history space with the space of probability measures: BS 7.48 applied
    to the evaluation kernel `(h, γ) ↦ γ`
    (`lintegral_weakP_lowerSemianalytic`), with the integrand lower
    semianalytic by Phase 3. -/
theorem stageF_lowerSemianalytic
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) (k t : ℕ) :
    IsLowerSemianalytic
      (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
        ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z) ∂p.2.toMeasure) :=
  lintegral_weakP_lowerSemianalytic t
    (VGo_isLowerSemianalytic κμ κν c hκμ_meas hκν_meas hκμ_prob
      hκν_prob hc k (t + 1))

/-! ## Main theorem: measurable ε-optimal strategies -/

/-- **Phase 4 (BS Proposition 7.50 analogue).** For Borel Markov kernels
    and lower semianalytic stage costs, the ε-optimal strategy of
    `exists_eps_strategy` can be chosen σ(Σ¹₁)-measurable at every stage:
    each `γε t` factors through an `AnalyticallyMeasurable` map into the
    Polish space of probability measures. -/
theorem exists_eps_strategy_analyticallyMeasurable (T : ℕ)
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γε t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ,
      ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      AnalyticallyMeasurable φ ∧
      (∀ h, (h, φ h) ∈ FeasGraph κμ κν t) ∧
      ∀ h, (∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(φ h).toMeasure)
        ≤ (⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γ.toMeasure)
          + ε :=
    fun t => exists_eps_optimal_selector
      ((measurableSet_feasGraph κμ κν hκμ_meas hκν_meas hκμ_prob
        hκν_prob t).analyticSet)
      (stageF_lowerSemianalytic κμ κν c hκμ_meas hκν_meas hκμ_prob
        hκν_prob hc (T - t - 1) t)
      (feasGraph_fiber_nonempty κμ κν hκμ_prob hne t) hε
  choose φ hφmeas hφmem hφopt using key
  refine ⟨fun t h => (φ t h).toMeasure,
    fun t h => hφmem t h,
    fun t h => ?_,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩
  rw [iInf_feas_eq_iInf_feasGraph κμ κν hκμ_prob t h]
  exact hφopt t h

/-! ## Corollary: measurability is free in the Bellman value -/

/-- **Corollary (Phase 4).** The multi-period Bellman value
    representation holds with the strategy infimum restricted to
    strategies that are σ(Σ¹₁)-measurable at every stage — measurability
    costs nothing in the value. Upper bound via the measurable ε-optimal
    strategy and L4; lower bound inherited from `bellman_value_eq_multi`. -/
theorem bellman_value_eq_multi_measurable (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h)
      (_ : ∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γ t h = (φ h).toMeasure),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by
  refine le_antisymm ?_ ?_
  · -- upper bound via measurable ε-optimal strategies
    refine le_iInf fun γ₀ => le_iInf fun h₀mem => ?_
    have hγ₀mass : γ₀ Set.univ = 1 := by
      have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
        rw [h₀mem.1]; exact measure_univ
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ] at h1
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · -- T = 0: cost and value both reduce to the stage-0 cost
      obtain ⟨γ1, hmem1, -, hφ1⟩ :=
        exists_eps_strategy_analyticallyMeasurable κμ κν c 0 hκμ_meas
          hκν_meas hκμ_prob hκν_prob hc hne (ε := 1) zero_lt_one
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γ1
        (iInf_le_of_le h₀mem (iInf_le_of_le hmem1 (iInf_le _ hφ1))))) ?_
      exact le_of_eq rfl
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / T with hδ
      have hδpos : 0 < δ :=
        ENNReal.div_pos (by exact_mod_cast hε.ne') (by finiteness)
      obtain ⟨γε, hmem, hopt, hφ⟩ :=
        exists_eps_strategy_analyticallyMeasurable κμ κν c T hκμ_meas
          hκν_meas hκμ_prob hκν_prob hc hne hδpos
      have hbound : ∀ h₀ : PairHist X Y 0,
          costGo c γε T 0 h₀ ≤ VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ :=
        fun h₀ => costGo_le_VGo_add κμ κν c T hκμ_prob γε hmem hopt T 0
          (by omega) h₀
      have hTδ : (T : ℝ≥0∞) * δ = (ε : ℝ≥0∞) := by
        rw [hδ]
        exact ENNReal.mul_div_cancel (by exact_mod_cast hT.ne')
          (by finiteness)
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γε
        (iInf_le_of_le h₀mem (iInf_le_of_le hmem (iInf_le _ hφ))))) ?_
      calc ∫⁻ h₀, costGo c γε T 0 h₀ ∂γ₀
          ≤ ∫⁻ h₀, (VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ) ∂γ₀ :=
            lintegral_mono hbound
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (T : ℝ≥0∞) * δ := by
            have hsplit := lintegral_add_right (μ := γ₀)
              (fun h₀ : X 0 × Y 0 => VGo c κμ κν T 0 h₀)
              (g := fun _ : X 0 × Y 0 => (T : ℝ≥0∞) * δ) measurable_const
            rw [hsplit, lintegral_const, hγ₀mass, mul_one]
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (ε : ℝ≥0∞) := by rw [hTδ]
  · -- lower bound: restricting the infimum can only increase it
    rw [← bellman_value_eq_multi κμ κν c T μ₀ ν₀ hκμ_prob hne]
    refine le_iInf fun γ₀ => le_iInf fun γ => le_iInf fun h₀mem =>
      le_iInf fun hfeas => le_iInf fun _ => ?_
    exact iInf_le_of_le γ₀ (iInf_le_of_le γ (iInf_le_of_le h₀mem
      (iInf_le _ hfeas)))

end MultiPeriod

end
