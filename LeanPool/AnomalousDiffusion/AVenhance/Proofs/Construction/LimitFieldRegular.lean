/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Construction.StreamRegularity

/-! Proof of stream-function estimates. The exponent-specific construction
below uses one admissible exponent to choose the limit field; uniqueness of
pointwise limits identifies every other exponent's witness with that field. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

/-- Stream-function estimates proof. Its statement is identical to
`AVenhance.limit_field_regular`; the statement file is not imported. -/
theorem limit_field_regular (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∃ φ : ℝ → Vec 2 → ℝ,
          (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
          (∀ (M : ℕ) (t : ℝ) (x : Vec 2),
            |φ t x - Φ M t x| ≤ C * epsilon β I.Λ (M + 1) ^ β) ∧
          (∀ t, Differentiable ℝ (φ t)) ∧
          TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
            (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) atTop
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
          ∀ α : ℝ, 0 < α → α < β - 1 → IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ) := by
  refine ⟨11, by norm_num, ?_⟩
  intro I Φ hseq
  have hβ : 0 < β - 1 := by linarith [I.one_lt_beta]
  let α₀ : ℝ := (β - 1) / 2
  have hα₀ : 0 < α₀ := by
    dsimp [α₀]
    exact div_pos hβ (by norm_num)
  have hα₀β : α₀ < β - 1 := by
    dsimp [α₀]
    nlinarith [hβ]
  obtain ⟨φ, hlim, htail, hdiff, hvel, _hregular⟩ :=
    limit_field_regular_of_section2_induction hseq hα₀ hα₀β
  refine ⟨φ, hlim, ?_, hdiff, hvel, ?_⟩
  · intro M t x
    simpa using htail M t x
  · intro α hα hαβ
    obtain ⟨ψ, hψlim, _hψtail, _hψdiff, _hψvel, hψregular⟩ :=
      limit_field_regular_of_section2_induction hseq hα hαβ
    have hψeq : ψ = φ := by
      funext t x
      exact tendsto_nhds_unique (hψlim t x) (hlim t x)
    simpa [hψeq] using hψregular

end AVenhance.Proofs

end
