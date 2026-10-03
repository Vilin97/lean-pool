/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Induction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2JointInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.Recursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2Smoothness

/-! Proofs of the Section 2 stream-function stream estimates.

The stream-function estimates statement is constructed from App. B.2. The Section 2 bridge
derives the flow/material displays from the same recursive induction. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

/-- Conditional form of the stream-function estimates statement from its first display. The
conclusion has the quantifiers and all three estimates; the
hypothesis is exactly the increment bound copied from that statement file. -/
theorem stream_regularity_of_increment_bounds (β : ℝ)
    (hIncrement : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ),
      IsStreamSeq I Φ → Infra.Construction.StreamIncrementBounds I Φ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
          (∀ n : ℕ,
            barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
              ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)) ∧
          (∀ n : ℕ, 2 ≤ n →
            barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
                (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
          (∀ n : ℕ, n ≤ 1 →
            barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (C * epsilon β I.Λ m ^ n)) := by
  classical
  by_cases hI : Nonempty (Ingredients β)
  · obtain ⟨I₀⟩ := hI
    let C : ℝ := 11 + 768 / (β - 1)
    have hβ : 0 < β - 1 := by linarith [I₀.one_lt_beta]
    have hC : 1 ≤ C := by
      dsimp [C]
      have hnonneg : 0 ≤ 768 / (β - 1) := div_nonneg (by norm_num) hβ.le
      linarith
    refine ⟨C, hC, ?_⟩
    intro I Φ hseq m hm t
    have hreg := Infra.Construction.stream_regularity_bounds_of_increment_bounds
      hseq (hIncrement I Φ hseq)
    simpa [C] using hreg m hm t
  · refine ⟨1, le_rfl, ?_⟩
    intro I Φ hseq m hm t
    exact (hI ⟨I⟩).elim

/-- The explicit source recurrence for `R_m` and `M_m`, together with the
App. B.2 inverse-flow estimate, proves the increment display and hence all
three stream-function estimates spatial bounds. The only analytic input left at this boundary
is `AppB2InverseFlowData`; it is not replaced by an assumed increment bound. -/
theorem stream_regularity_of_appB2 (β : ℝ)
    (hAppB2 : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ),
      ∀ hseq : IsStreamSeq I Φ,
        Infra.Construction.AppB2InverseFlowData I Φ hseq
          (Infra.Construction.section2Radius I)
          (Infra.Construction.section2Amplitude I)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
          (∀ n : ℕ,
            barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
              ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)) ∧
          (∀ n : ℕ, 2 ≤ n →
            barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
                (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
          (∀ n : ℕ, n ≤ 1 →
            barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (C * epsilon β I.Λ m ^ n)) := by
  apply stream_regularity_of_increment_bounds β
  intro I Φ hseq
  let R := Infra.Construction.section2Radius I
  let M := Infra.Construction.section2Amplitude I
  have hscales : Infra.Construction.Section2Scales I R M := by
    simpa [R, M] using Infra.Construction.section2Scales_canonical I
  have happB2 : Infra.Construction.AppB2InverseFlowData I Φ hseq R M := by
    simpa [R, M] using hAppB2 I Φ hseq
  have hind := Infra.Construction.section2_stream_induction hscales happB2
  intro m hm t n
  exact Infra.Construction.stream_increment_bound_at_scale hscales happB2 m hm
    (hind (m - 1)) t n

/-- Stream-function estimates proof. The canonical Section 2 scales and the smooth-periodic
flow theorem construct the consumed App. B.2 data, which yields the exact
three displays and quantifiers of the statement. -/
theorem stream_regularity (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
          (∀ n : ℕ,
            barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
              ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)) ∧
          (∀ n : ℕ, 2 ≤ n →
            barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
                (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
          (∀ n : ℕ, n ≤ 1 →
            barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (C * epsilon β I.Λ m ^ n)) := by
  apply stream_regularity_of_appB2 β
  intro I Φ hseq
  exact Infra.Construction.appB2InverseFlowData_of_smoothPeriodicFlow hseq
    (Infra.Construction.section2Scales_canonical I)

/-- The recursive proof of the first stream-function estimates display also derives every per-scale
flow/material field, then assembles the global source-form package. -/
theorem section2_induction_outputs_from_source_data {β : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Infra.Construction.Section2Scales I R M)
    (happB2 : Infra.Construction.AppB2InverseFlowData I Φ hseq R M)
    :
    StreamRegularityBounds (11 + 768 / (β - 1)) I Φ ∧
      (∃ Cmat : ℝ, 1 ≤ Cmat ∧ FlowBoundsData I Φ hseq Cmat) := by
  obtain ⟨_hind, hincrement, hflow⟩ :=
    Infra.Construction.section2_joint_induction_with_derived_flow hscales happB2
  have hreg : StreamRegularityBounds (11 + 768 / (β - 1)) I Φ :=
    Infra.Construction.stream_regularity_bounds_of_increment_bounds hseq hincrement
  rcases hflow with ⟨Cmat, hCmat, hflow, _⟩
  exact ⟨hreg, ⟨Cmat, hCmat, hflow⟩⟩

/-- Stream-function estimates limit-field package following the same §2 induction that proves the
first stream-function estimates increment estimate and derives the per-scale flow bounds. -/
theorem limit_field_regular_of_section2_induction {β α : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ)
    (hα : 0 < α) (hαβ : α < β - 1) :
    ∃ φ : ℝ → Vec 2 → ℝ,
      (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
      (∀ M t x, |φ t x - Φ M t x| ≤ 11 * epsilon β I.Λ (M + 1) ^ β) ∧
      (∀ t, Differentiable ℝ (φ t)) ∧
      TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
        (fun p => streamVel φ p.1 p.2) atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
      IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ) := by
  let R := Infra.Construction.section2Radius I
  let M := Infra.Construction.section2Amplitude I
  have hscales : Infra.Construction.Section2Scales I R M := by
    simpa [R, M] using Infra.Construction.section2Scales_canonical I
  have happB2 : Infra.Construction.AppB2InverseFlowData I Φ hseq R M := by
    simpa [R, M] using Infra.Construction.appB2InverseFlowData_of_smoothPeriodicFlow hseq
      (Infra.Construction.section2Scales_canonical I)
  obtain ⟨hreg, ⟨_, _, hflow⟩⟩ :=
    section2_induction_outputs_from_source_data hscales happB2
  exact AVenhance.limit_field_regular_of_stream_regularity
    hseq hreg hflow hα hαβ

end AVenhance.Proofs
