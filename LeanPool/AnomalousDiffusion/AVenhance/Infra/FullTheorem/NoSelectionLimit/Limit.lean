/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Sup

/-! # The limit field of a stream sequence, packaged

All regularity facts about `φ = lim Φ_M` needed for `tail_sup` and the transport limit. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem Limit.limit_periodic {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) (t : ℝ) :
    IsZ2Periodic (φ t) := by
  intro n x
  refine tendsto_nhds_unique (htend t (x + latticeShift n)) ?_
  have h := htend t x
  refine h.congr fun M => ?_
  have := (hΦ M).2 0 n t x
  simpa using this.symm

theorem Limit.limit_meas {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (μ : Measure (ℝ × Vec 2)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2) μ := by
  have hm : Measurable (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    measurable_of_tendsto_metrizable (f := fun M (p : ℝ × Vec 2) => Φ M p.1 p.2)
      (fun M => (hΦ M).1.continuous.measurable)
      (tendsto_pi_nhds.2 fun p => htend p.1 p.2)
  exact hm.aestronglyMeasurable

/-- Regularity package for the limit field. -/
theorem limit_package {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {φ : ℝ → Vec 2 → ℝ}
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) :
    ∃ Ct Bφ : ℝ, 0 ≤ Ct ∧ 0 ≤ Bφ ∧
      (∀ (M : ℕ) (t : ℝ) (x : Vec 2), |φ t x - Φ M t x| ≤ Ct * epsilon β I.Λ (M + 1) ^ β) ∧
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t)) ∧
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t)) ∧
      IsDivFree (streamVel φ) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ Bφ) := by
  obtain ⟨Ct, hCt1, hlim⟩ := AVenhance.limit_field_regular β
  have hadm : ∀ M, IsAdmissibleStream (Φ M) := streamSeq_isAdmissible hΦ
  obtain ⟨φ', htend', htail', hdiff', -, hhol'⟩ := hlim I Φ hΦ
  have hφφ : φ' = φ := by
    funext t x
    exact tendsto_nhds_unique (htend' t x) (htend t x)
  subst hφφ
  have hβ := I.one_lt_beta
  obtain ⟨hHolder, hdiv⟩ := hhol' _ (by linarith : 0 < (β - 1) / 2) (by linarith)
  obtain ⟨Cb, hCb⟩ := hHolder.2.2.1
  refine ⟨Ct, max Cb 0, by linarith, le_max_right _ _, htail',
    Limit.limit_meas hadm htend _, fun t _ => Limit.limit_periodic hadm htend t, fun t _ => hdiff'
        t,
    hHolder.2.1.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ),
    hHolder.1, hdiv, fun t ht x => (hCb t ht x).trans (le_max_left _ _)⟩

end AVenhance.Infra.FullTheorem
