/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  FRONT F1 — nonemptiness of feasible sets via product couplings.

  Draft for integration into BicausalOT.  The independent (product)
  coupling witnesses nonemptiness of `CouplingSet₀`, `FeasibleSet₀` and
  `MultiPeriod.Feas` whenever the marginals / conditional marginals are
  probability measures.  This makes the hypotheses `h_Gamma_ne`
  (T=1, `bellman_value_eq`) and `hne` (`bellman_value_eq_multi`)
  redundant; `CouplingSet₀.measure_univ` additionally kills `h_prob`.

  Integration targets: general lemmas → Defs.lean (or a small new file),
  `Feas.nonempty` + `bellman_value_eq_multi'` → MultiPeriod.lean,
  `bellman_value_eq'` → ValueRepresentation.lean.
  See note_FeasNonempty.md for the recommendation.
-/
import LeanPool.BicausalOT.BicausalOT.MultiPeriod
import LeanPool.BicausalOT.BicausalOT.ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod

/-! ### General marginal lemmas for product measures

Mathlib's `Measure.map_fst_prod : (μ.prod ν).map Prod.fst = (ν univ) • μ`
(and symmetrically `Measure.map_snd_prod`) carry a total-mass scalar; for
probability factors the scalar is `1` and disappears. -/

open MeasureTheory Set ENNReal

noncomputable section



/-- The first marginal of a product measure is the first factor, when the
    second factor is a probability measure. -/
theorem MeasureTheory.Measure.map_fst_prod_of_isProbabilityMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.fst = μ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The second marginal of a product measure is the second factor, when
    the first factor is a probability measure. -/
theorem MeasureTheory.Measure.map_snd_prod_of_isProbabilityMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν] :
    (μ.prod ν).map Prod.snd = ν := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-! ### T=1: `CouplingSet₀` and `FeasibleSet₀` are nonempty -/

section OneStep

variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

/-- The independent coupling `μ₀.prod ν₀` witnesses nonemptiness of the
    coupling set of two probability measures. -/
theorem CouplingSet₀.nonempty (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀] :
    (CouplingSet₀ μ₀ ν₀).Nonempty :=
  ⟨μ₀.prod ν₀,
    Measure.map_fst_prod_of_isProbabilityMeasure μ₀ ν₀,
    Measure.map_snd_prod_of_isProbabilityMeasure μ₀ ν₀⟩

omit [MeasurableSpace X₀] [MeasurableSpace Y₀] in
/-- The product of the conditional marginals witnesses nonemptiness of
    the one-step feasible set, for probability kernels. -/
theorem FeasibleSet₀.nonempty
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y))
    (z₀ : X₀ × Y₀) :
    (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty := by
  have := hκμ z₀.1
  have := hκν z₀.2
  exact ⟨(κ_μ z₀.1).prod (κ_ν z₀.2),
    Measure.map_fst_prod_of_isProbabilityMeasure _ _,
    Measure.map_snd_prod_of_isProbabilityMeasure _ _⟩

/-- Any coupling of probability marginals has total mass one.  Makes the
    hypothesis `h_prob` of `bellman_value_leq` / `bellman_value_eq`
    redundant. -/
theorem CouplingSet₀.measure_univ
    {μ₀ : Measure X₀} {ν₀ : Measure Y₀} [hμ₀ : IsProbabilityMeasure μ₀]
    {γ₀ : Measure (X₀ × Y₀)} (hγ₀ : γ₀ ∈ CouplingSet₀ μ₀ ν₀) :
    γ₀ Set.univ = 1 := by
  have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
    rw [hγ₀.1]; exact hμ₀.measure_univ
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] at h1

variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

/-- **T=1 Bellman value representation, probability-kernel form.**
    `bellman_value_eq` with both side conditions discharged: the
    nonemptiness hypothesis `h_Gamma_ne` follows from the kernels being
    probability-valued (`FeasibleSet₀.nonempty`), and the mass bound
    `h_prob` from the probability marginals (`CouplingSet₀.measure_univ`). -/
theorem bellman_value_eq'
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y)) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    = ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ :=
  bellman_value_eq c₀ c₁ μ₀ ν₀ κ_μ κ_ν
    (FeasibleSet₀.nonempty κ_μ κ_ν hκμ hκν)
    (fun _ hγ₀ => le_of_eq (CouplingSet₀.measure_univ hγ₀))

end OneStep

/-! ### Multi-period: `Feas` is nonempty -/

namespace MultiPeriod

variable {X Y : ℕ → Type*}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))

/-- F1 main lemma: every one-step feasible set is nonempty when the
    conditional marginals are probability measures.  The witness is the
    conditionally independent (product) coupling. -/
theorem Feas.nonempty
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y))
    (t : ℕ) (h : PairHist X Y t) :
    (Feas κμ κν t h).Nonempty := by
  have := hκμ t (projX t h)
  have := hκν t (projY t h)
  exact ⟨(κμ t (projX t h)).prod (κν t (projY t h)),
    Measure.map_fst_prod_of_isProbabilityMeasure _ _,
    Measure.map_snd_prod_of_isProbabilityMeasure _ _⟩

variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

/-- **Multi-period Bellman value representation, probability-kernel
    form.**  `bellman_value_eq_multi` with the nonemptiness hypothesis
    `hne` replaced by the probability hypothesis on the `Y`-side kernel
    (the `X`-side one was already assumed): nonemptiness of every `Feas`
    fiber follows via `Feas.nonempty`. -/
theorem bellman_value_eq_multi' (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0))
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y)) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ :=
  bellman_value_eq_multi κμ κν c T μ₀ ν₀ hκμ (Feas.nonempty κμ κν hκμ hκν)

end MultiPeriod

end
