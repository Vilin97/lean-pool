/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Phase 3: lower semianalyticity of the Bellman value functions
  (Bertsekas–Shreve Proposition 8.2 analogue, multi-period bicausal OT)

  Blueprint: BLUEPRINT.md §3 + battle log 2026-07-04. Architecture:
  the one-step infimum in `VGo` is reindexed over the Polish space
  `WeakP W` of probability measures (W1); the feasibility correspondence
  is Borel via the Giry-valued equalizer (`measurableSet_eq_measure`) and
  W2 (`probabilityMeasure_borel_measurable_toMeasure`); the integrand is
  lower semianalytic by BS 7.48 (`lintegral_lowerSemianalytic`) applied
  to the evaluation kernel `(h, γ) ↦ γ`; the fiber infimum is lower
  semianalytic by BS 7.47 (`IsLowerSemianalytic.iInf_fiber`); the stage
  cost is added back via `IsLowerSemianalytic.add`. Induction on the
  time to go.
-/
import LeanPool.BicausalOT.BicausalOT.MultiPeriodTopology
import LeanPool.BicausalOT.BicausalOT.FeasNonempty
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.LsaAlgebra
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.KernelIntegral
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.ProbabilityMeasurePolish

open MeasureTheory Set ENNReal

noncomputable section

/-! ## The Polish space of probability measures with its Borel σ-algebra

`ProbabilityMeasure W` carries Mathlib's Giry-subtype σ-algebra, which is
not the Borel σ-algebra of the weak topology; the type synonym `WeakP`
installs the Borel structure (Polish by W1). -/

/-- Probability measures on `W`, considered with the topology of weak
    convergence and its Borel σ-algebra. -/
def WeakP (W : Type*) [MeasurableSpace W] : Type _ := ProbabilityMeasure W

namespace WeakP

variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W]
  [OpensMeasurableSpace W]

instance : TopologicalSpace (WeakP W) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure W))

instance : MeasurableSpace (WeakP W) := borel (WeakP W)

instance : BorelSpace (WeakP W) := ⟨rfl⟩

instance [PolishSpace W] [BorelSpace W] : PolishSpace (WeakP W) :=
  ProbabilityMeasure.instPolishSpace (X := W)

/-- The underlying measure. -/
def toMeasure (γ : WeakP W) : Measure W :=
  ProbabilityMeasure.toMeasure γ

instance (γ : WeakP W) : IsProbabilityMeasure γ.toMeasure :=
  (γ : ProbabilityMeasure W).prop

/-- **W2, packaged**: the underlying-measure map is measurable from the
    Borel σ-algebra of the weak topology to the Giry σ-algebra. -/
theorem measurable_toMeasure [PolishSpace W] [BorelSpace W] :
    Measurable (toMeasure : WeakP W → Measure W) := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable W
  exact probabilityMeasure_borel_measurable_toMeasure (Ω := W)

end WeakP

namespace MultiPeriod

variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]

variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

/-- The feasibility correspondence, as a subset of the product of the
    history space with the Polish space of probability measures. -/
def FeasGraph (t : ℕ) :
    Set (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1))) :=
  {p | p.2.toMeasure ∈ Feas κμ κν t p.1}

/-- The feasibility correspondence is Borel: each marginal constraint is
    the equalizer of two measurable `Measure`-valued maps. -/
theorem measurableSet_feasGraph
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y)) (t : ℕ) :
    MeasurableSet (FeasGraph κμ κν t) := by
  have h1 : MeasurableSet {p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) |
      p.2.toMeasure.map Prod.fst = κμ t (projX t p.1)} := by
    refine measurableSet_eq_measure ?_ ?_ ?_ ?_
    · exact (Measure.measurable_map _ measurable_fst).comp
        (WeakP.measurable_toMeasure.comp measurable_snd)
    · exact (hκμ_meas t).comp ((measurable_projX t).comp measurable_fst)
    · intro p
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    · intro p
      exact hκμ_prob t _
  have h2 : MeasurableSet {p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) |
      p.2.toMeasure.map Prod.snd = κν t (projY t p.1)} := by
    refine measurableSet_eq_measure ?_ ?_ ?_ ?_
    · exact (Measure.measurable_map _ measurable_snd).comp
        (WeakP.measurable_toMeasure.comp measurable_snd)
    · exact (hκν_meas t).comp ((measurable_projY t).comp measurable_fst)
    · intro p
      exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    · intro p
      exact hκν_prob t _
  exact h1.inter h2

/-- BS 7.48 for the evaluation kernel `(h, γ) ↦ γ`: integrating a lower
    semianalytic function of the extended history against the second
    coordinate is lower semianalytic on the product of the history space
    with the space of probability measures. -/
theorem lintegral_weakP_lowerSemianalytic (t : ℕ)
    {f : PairHist X Y (t + 1) → ℝ≥0∞} (hf : IsLowerSemianalytic f) :
    IsLowerSemianalytic
      (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
        ∫⁻ z, f (p.1, z) ∂p.2.toMeasure) := by
  have hf' : IsLowerSemianalytic
      (fun q : (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)))
          × (X (t + 1) × Y (t + 1)) => f (q.1.1, q.2)) := by
    have hcomp : (fun q : (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)))
          × (X (t + 1) × Y (t + 1)) => f (q.1.1, q.2))
        = f ∘ (fun q => (q.1.1, q.2)) := rfl
    rw [hcomp]
    exact hf.comp_continuous
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact lintegral_lowerSemianalytic hf'
    (WeakP.measurable_toMeasure.comp measurable_snd)
    (fun p => inferInstance)

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- The one-step feasible infimum reindexed over the fibers of the
    feasibility graph (any integrand): legitimate because feasible
    one-step plans are probability measures. -/
theorem iInf_feas_eq_iInf_feasGraph
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (t : ℕ) (h : PairHist X Y t) (f : X (t + 1) × Y (t + 1) → ℝ≥0∞) :
    (⨅ (γm : Measure (X (t + 1) × Y (t + 1))) (_ : γm ∈ Feas κμ κν t h),
        ∫⁻ z, f z ∂γm)
      = ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, f z ∂γ.toMeasure := by
  apply le_antisymm
  · exact le_iInf₂ fun γ hγ => iInf₂_le γ.toMeasure hγ
  · refine le_iInf₂ fun γm hγm => ?_
    haveI hpm : IsProbabilityMeasure γm :=
      ⟨Feas.measure_univ κμ κν hκμ_prob hγm⟩
    exact iInf₂_le
      (show WeakP (X (t + 1) × Y (t + 1)) from
        (⟨γm, hpm⟩ : ProbabilityMeasure (X (t + 1) × Y (t + 1)))) hγm

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- The one-step infimum of `VGo` reindexed over the Polish space of
    probability measures: legitimate because feasible one-step plans are
    probability measures (Markov kernels). -/
theorem VGo_succ_eq_weakP
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x)) (k t : ℕ)
    (h : PairHist X Y t) :
    VGo c κμ κν (k + 1) t h
      = c t h + ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure := by
  show c t h + _ = c t h + _
  congr 1
  exact iInf_feas_eq_iInf_feasGraph κμ κν hκμ_prob t h _

/-- **Phase 3 (BS Proposition 8.2 analogue).** For Borel Markov kernels
    and lower semianalytic stage costs, every Bellman value function
    `VGo k t` is lower semianalytic on the history space. -/
theorem VGo_isLowerSemianalytic
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) :
    ∀ k t : ℕ, IsLowerSemianalytic (VGo c κμ κν k t) := by
  intro k
  induction k with
  | zero => exact fun t => hc t
  | succ k ih =>
    intro t
    -- the integrand on the product with the measure space
    have hintegrand : IsLowerSemianalytic
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z) ∂p.2.toMeasure) :=
      lintegral_weakP_lowerSemianalytic t (ih (t + 1))
    -- fiber infimum over the Borel (hence analytic) feasibility graph
    have hfiber : IsLowerSemianalytic
        (fun h : PairHist X Y t =>
          ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure) :=
      IsLowerSemianalytic.iInf_fiber
        ((measurableSet_feasGraph κμ κν hκμ_meas hκν_meas
          hκμ_prob hκν_prob t).analyticSet)
        hintegrand
    -- reassemble VGo (k+1)
    have heq : VGo c κμ κν (k + 1) t
        = fun h => c t h + ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure :=
      funext fun h => VGo_succ_eq_weakP κμ κν c hκμ_prob k t h
    rw [heq]
    exact (hc t).add hfiber

end MultiPeriod

end
