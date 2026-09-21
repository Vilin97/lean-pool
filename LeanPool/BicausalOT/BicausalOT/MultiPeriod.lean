/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Multi-period Bicausal OT — general finite horizon T

  Blueprint: BLUEPRINT.md §2 (Phase 1–2). Design: nested-product
  histories, time-to-go recursion, arbitrary function strategies.
  Target theorem: `bellman_value_eq_multi`.
-/
import LeanPool.BicausalOT.BicausalOT.Defs
import LeanPool.BicausalOT.BicausalOT.UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# MultiPeriod

Supporting results for bicausal optimal transport and measurable selection.
-/

open MeasureTheory Set ENNReal

noncomputable section

namespace MultiPeriod

variable (X Y : ℕ → Type*)

/-- D1: pair-history up to time `t`, as nested products. Appending one
    step is literally pairing `(h, z)`. -/
def PairHist : ℕ → Type _
  | 0 => X 0 × Y 0
  | t + 1 => PairHist t × (X (t + 1) × Y (t + 1))

/-- D2: X-side history. -/
def XHist : ℕ → Type _
  | 0 => X 0
  | t + 1 => XHist t × X (t + 1)

/-- D2: Y-side history. -/
def YHist : ℕ → Type _
  | 0 => Y 0
  | t + 1 => YHist t × Y (t + 1)

variable {X Y}

/-- D3: X-side projection of a pair-history. -/
def projX : (t : ℕ) → PairHist X Y t → XHist X t
  | 0, h => h.1
  | t + 1, hz => (projX t hz.1, hz.2.1)

/-- D3: Y-side projection of a pair-history. -/
def projY : (t : ℕ) → PairHist X Y t → YHist Y t
  | 0, h => h.2
  | t + 1, hz => (projY t hz.1, hz.2.2)

variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]

variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

/-- D5: one-step feasible couplings after history `h`: couplings of the
    conditional marginals. -/
def Feas (t : ℕ) (h : PairHist X Y t) :
    Set (Measure (X (t + 1) × Y (t + 1))) :=
  {γ | γ.map Prod.fst = κμ t (projX t h) ∧ γ.map Prod.snd = κν t (projY t h)}

/-- D6: a strategy is an arbitrary family of one-step transition plans
    (no measurability imposed; mirrors the T=1 design). -/
def Strat (X Y : ℕ → Type*)
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)] : Type _ :=
  (t : ℕ) → PairHist X Y t → Measure (X (t + 1) × Y (t + 1))

variable {κμ κν}

/-- D7: cost-to-go with `k` remaining periods, starting at time `t`. -/
def costGo (γ : Strat X Y) : (k : ℕ) → (t : ℕ) → PairHist X Y t → ℝ≥0∞
  | 0, t, h => c t h
  | k + 1, t, h => c t h + ∫⁻ z, costGo γ k (t + 1) (h, z) ∂(γ t h)

/-- D8: Bellman value with `k` remaining periods. -/
def VGo (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
    (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))) :
    (k : ℕ) → (t : ℕ) → PairHist X Y t → ℝ≥0∞
  | 0, t, h => c t h
  | k + 1, t, h => c t h +
      ⨅ (γm : Measure (X (t + 1) × Y (t + 1))) (_ : γm ∈ Feas κμ κν t h),
        ∫⁻ z, VGo κμ κν k (t + 1) (h, z) ∂γm

variable (κμ κν)

/-- L0: feasible one-step plans are probability measures when the
    conditional marginals are. -/
theorem Feas.measure_univ
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    {t : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    γm Set.univ = 1 := by
  have h1 : (γm.map Prod.fst) Set.univ = 1 := by
    rw [hγ.1]
    exact (hκμ t (projX t h)).measure_univ
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] at h1

/-- L1: pointwise Bellman bound at any feasible one-step plan. -/
theorem VGo_le_pointwise {t k : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    VGo c κμ κν (k + 1) t h
      ≤ c t h + ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γm := by
  change c t h + _ ≤ _
  gcongr
  exact iInf₂_le γm hγ

/-- L2: the Bellman value bounds the cost of every feasible strategy,
    pointwise in the history. Backward induction on the time to go. -/
theorem VGo_le_costGo (γ : Strat X Y)
    (hfeas : ∀ t h, γ t h ∈ Feas κμ κν t h) :
    ∀ (k t : ℕ) (h : PairHist X Y t),
      VGo c κμ κν k t h ≤ costGo c γ k t h
  | 0, _, _ => le_of_eq rfl
  | k + 1, t, h => by
    refine le_trans (VGo_le_pointwise κμ κν c (hfeas t h)) ?_
    change c t h + _ ≤ c t h + _
    gcongr with z
    exact VGo_le_costGo γ hfeas k (t + 1) (h, z)

/-- L3: an ε-optimal strategy for a fixed horizon `T`: at each stage the
    chosen plan is ε-optimal for the time-consistent depth `T - t - 1`
    (the only depth at which `costGo _ T 0` ever evaluates it). -/
theorem exists_eps_strategy (T : ℕ)
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      ∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε := by
  have key : ∀ t (h : PairHist X Y t),
      ∃ γm ∈ Feas κμ κν t h,
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm
          ≤ (⨅ (γm' : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm' ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm') + ε :=
    fun t h => eps_optimal_element (Feas κμ κν t h) (hne t h)
      (fun γm => ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) ε hε
  choose γε hmem hopt using key
  exact ⟨γε, hmem, hopt⟩

/-- L4: over `k` remaining periods (with `t + k = T`), the ε-optimal
    strategy overshoots the Bellman value by at most `k·ε`. -/
theorem costGo_le_VGo_add (T : ℕ)
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γε : Strat X Y) (hmem : ∀ t h, γε t h ∈ Feas κμ κν t h)
    {ε : ℝ≥0∞}
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
        ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γε k t h ≤ VGo c κμ κν k t h + (k : ℝ≥0∞) * ε
  | 0, t, _, h => by simp [costGo, VGo]
  | k + 1, t, htk, h => by
    have hdepth : T - t - 1 = k := by omega
    have hmass : (γε t h) Set.univ = 1 :=
      Feas.measure_univ κμ κν hκμ (hmem t h)
    calc costGo c γε (k + 1) t h
        = c t h + ∫⁻ z, costGo c γε k (t + 1) (h, z) ∂(γε t h) := rfl
      _ ≤ c t h + ∫⁻ z, (VGo c κμ κν k (t + 1) (h, z) + (k : ℝ≥0∞) * ε)
            ∂(γε t h) := by
          gcongr with z
          exact costGo_le_VGo_add T hκμ γε hmem hopt k (t + 1) (by omega) (h, z)
      _ = c t h + (∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂(γε t h)
            + (k : ℝ≥0∞) * ε) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const,
            hmass, mul_one]
      _ ≤ c t h + (((⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γm) + ε)
            + (k : ℝ≥0∞) * ε) := by
          gcongr
          have hstep := hopt t h
          rw [hdepth] at hstep
          exact hstep
      _ = VGo c κμ κν (k + 1) t h + ((k : ℕ) + 1 : ℝ≥0∞) * ε := by
          change c t h + _ = (c t h + _) + _
          ring
      _ = VGo c κμ κν (k + 1) t h + ((k + 1 : ℕ) : ℝ≥0∞) * ε := by
          push_cast
          ring

/-- Main theorem (Phase 2): multi-period Bellman value representation.
    The infimum of the total cost over initial couplings and pointwise
    feasible strategies equals the infimum over initial couplings of the
    integrated Bellman value. -/
theorem bellman_value_eq_multi (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0))
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by
  refine le_antisymm ?_ ?_
  · -- upper bound via ε-optimal strategies
    refine le_iInf fun γ₀ => le_iInf fun h₀mem => ?_
    have hγ₀mass : γ₀ Set.univ = 1 := by
      have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
        rw [h₀mem.1]; exact measure_univ
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ] at h1
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · -- T = 0: cost and value both reduce to the stage-0 cost
      refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le
        (fun t h => (hne t h).choose) (iInf_le_of_le h₀mem
          (iInf_le _ fun t h => (hne t h).choose_spec)))) ?_
      exact le_of_eq rfl
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / T with hδ
      have hδpos : 0 < δ :=
        ENNReal.div_pos (by exact_mod_cast hε.ne') (by finiteness)
      obtain ⟨γε, hmem, hopt⟩ := exists_eps_strategy κμ κν c T hne hδpos
      have hbound : ∀ h₀ : PairHist X Y 0,
          costGo c γε T 0 h₀ ≤ VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ :=
        fun h₀ => costGo_le_VGo_add κμ κν c T hκμ γε hmem hopt T 0
          (by omega) h₀
      have hTδ : (T : ℝ≥0∞) * δ = (ε : ℝ≥0∞) := by
        rw [hδ]
        exact ENNReal.mul_div_cancel (by exact_mod_cast hT.ne')
          (by finiteness)
      calc ⨅ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y)
            (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
            (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
            ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀'
          ≤ ∫⁻ h₀, costGo c γε T 0 h₀ ∂γ₀ := by
            refine le_trans (iInf_le_of_le γ₀ (iInf_le_of_le γε
              (iInf_le_of_le h₀mem (iInf_le _ hmem)))) ?_
            exact le_refl _
        _ ≤ ∫⁻ h₀, (VGo c κμ κν T 0 h₀ + (T : ℝ≥0∞) * δ) ∂γ₀ :=
            lintegral_mono hbound
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (T : ℝ≥0∞) * δ := by
            have hsplit := lintegral_add_right (μ := γ₀)
              (fun h₀ : X 0 × Y 0 => VGo c κμ κν T 0 h₀)
              (g := fun _ : X 0 × Y 0 => (T : ℝ≥0∞) * δ) measurable_const
            rw [hsplit, lintegral_const, hγ₀mass, mul_one]
        _ = ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ + (ε : ℝ≥0∞) := by rw [hTδ]
  · -- lower bound: integrate L2
    refine le_iInf fun γ₀ => le_iInf fun γ => le_iInf fun h₀mem =>
      le_iInf fun hfeas => ?_
    calc ⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀'
        ≤ ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := iInf₂_le γ₀ h₀mem
      _ ≤ ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀ :=
          lintegral_mono fun h₀ => VGo_le_costGo κμ κν c γ hfeas T 0 h₀

end MultiPeriod

end
