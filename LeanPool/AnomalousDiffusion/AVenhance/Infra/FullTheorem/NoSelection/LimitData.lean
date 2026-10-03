/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.TailHolder
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular

/-! # Regularity data of the limit field

`limit_data β`: a constant `C_t ≥ 1` such that for every stream sequence and every pointwise limit
`φ` of it, `φ` satisfies the tail estimate and the measurability/periodicity/boundedness
hypotheses of `tail_sup`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance AVenhance.Infra.FullTheorem

theorem limit_data (β : ℝ) :
    ∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ Bφ : ℝ,
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
  refine ⟨Ct, hCt1, ?_⟩
  intro I Φ hΦ φ htend
  have hadm : ∀ M, IsAdmissibleStream (Φ M) := streamSeq_isAdmissible hΦ
  obtain ⟨φ', htend', htail', hdiff', -, hhol'⟩ := hlim I Φ hΦ
  have hφφ : φ' = φ := by
    funext t x
    exact tendsto_nhds_unique (htend' t x) (htend t x)
  subst hφφ
  have hα0 : 0 < (β - 1) / 2 := by linarith [I.one_lt_beta]
  have hα1 : (β - 1) / 2 < β - 1 := by linarith [I.one_lt_beta]
  obtain ⟨hHolder, hdiv⟩ := hhol' _ hα0 hα1
  obtain ⟨Cb, hCb⟩ := hHolder.2.2.1
  refine ⟨max Cb 0, htail', ?_, ?_, fun t _ => hdiff' t, ?_, fun t ht => hHolder.1 t ht, hdiv,
    fun t ht x => (hCb t ht x).trans (le_max_left _ _)⟩
  · have hm : Measurable (fun p : ℝ × Vec 2 => φ' p.1 p.2) :=
      measurable_of_tendsto_metrizable (f := fun M (p : ℝ × Vec 2) => Φ M p.1 p.2)
        (fun M => (hadm M).1.continuous.measurable)
        (tendsto_pi_nhds.2 fun p => htend p.1 p.2)
    exact hm.aestronglyMeasurable
  · intro t _ n x
    refine tendsto_nhds_unique (htend t (x + latticeShift n)) ?_
    have h := htend t x
    refine h.congr fun M => ?_
    have := (hadm M).2 0 n t x
    simpa using this.symm
  · exact hHolder.2.1.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)

end AVenhance.Infra.FullTheorem.NoSel
