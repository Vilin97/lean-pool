/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Lemma43Complete
import LeanPool.Feige.Lemma43Endpoints

/-!
# Local transfer identity for an arbitrary base law
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige
namespace Lemma43ArbitraryBase

open ProbabilityTheory TransferStein TransferTestFunctions

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The factorized transfer identity and denominator positivity require no
density or TP2 assumption: they hold for the two exponential shifts of
every probability base law. -/
theorem identity_and_w_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    let νP := zPlusLaw μ a
    let νM := zMinusLaw μ b
    ((1 - Lemma43.theta νM c d) *
          (Lemma43.A νP d - Lemma43.A νM d) -
          (c / (c + d)) * (Lemma43.F νP - Lemma43.F νM) =
        ((a - c) / (c + d)) * Lemma43.w νP c d *
          (Lemma43.theta νP c d - Lemma43.theta νM c d)) ∧
      0 < Lemma43.w νP c d ∧ 0 < Lemma43.w νM c d := by
  dsimp only
  let : IsProbabilityMeasure (zPlusLaw μ a) := by
    constructor
    rw [zPlusLaw, Measure.map_apply (measurable_zPlusMap a)
      MeasurableSet.univ]
    simp
  let : IsProbabilityMeasure (zMinusLaw μ b) := by
    constructor
    rw [zMinusLaw, Measure.map_apply (measurable_zMinusMap b)
      MeasurableSet.univ]
    simp
  refine ⟨Lemma43.transfer_identity _ _ (a := a) (b := b) hc hd
      (Lemma43.probabilityRelations _ _ hc hd) ?_ ?_,
    Lemma43.w_pos _ hc hd, Lemma43.w_pos _ hc hd⟩
  · simpa only [Lemma43.A, Lemma43.u] using
      Lemma43Complete.equation23_A_probability_auto μ ha hb hd
  · simpa only [Lemma43.B, Lemma43.v] using
      Lemma43Complete.equation23_B_probability_auto μ ha hb hc

/-- At a terminal base law supported on the nonpositive half-line, the
negative endpoint has zero nonnegative tail and hence zero transfer
parameter. -/
theorem terminal_zMinus
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Ioi 0) = 0) {b c d : ℝ}
    (hb : 0 < b) :
    let νM := zMinusLaw μ b
    Lemma43.F νM = 0 ∧ Lemma43.theta νM c d = 0 := by
  dsimp only
  let : IsProbabilityMeasure (zMinusLaw μ b) := by
    constructor
    rw [zMinusLaw, Measure.map_apply (measurable_zMinusMap b)
      MeasurableSet.univ]
    simp
  have hae : ∀ᵐ y ∂μ, y ≤ 0 := by
    rw [ae_iff]
    have hs : {y : ℝ | ¬y ≤ 0} = Ioi 0 := by
      ext y
      simp
    rw [hs]
    exact hpos
  have hF : Lemma43.F (zMinusLaw μ b) = 0 := by
    rw [Lemma43Endpoints.F_zMinusLaw_eq_A μ hb, Lemma43.A]
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with y hy
    exact transferPhi_of_nonpos hb hy
  refine ⟨hF, ?_⟩
  have hIci : zMinusLaw μ b (Ici 0) = 0 := by
    have htr : ENNReal.toReal (zMinusLaw μ b (Ici 0)) = 0 := by
      simpa only [Lemma43.F] using hF
    rcases (ENNReal.toReal_eq_zero_iff _).mp htr with hzero | htop
    · exact hzero
    · exact (measure_ne_top (zMinusLaw μ b) (Ici 0) htop).elim
  have hu : Lemma43.u (zMinusLaw μ b) d = 0 := by
    unfold Lemma43.u uProbability
    have hsub :
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < d * p.2} ⊆
          Ici 0 ×ˢ Set.univ := by
      intro p hp
      exact ⟨hp.1, Set.mem_univ _⟩
    have hzero :
        (zMinusLaw μ b).prod (expMeasure 1)
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < d * p.2} = 0 := by
      apply nonpos_iff_eq_zero.mp
      calc
        _ ≤ (zMinusLaw μ b).prod (expMeasure 1)
            (Ici 0 ×ˢ Set.univ) := measure_mono hsub
        _ = 0 := by rw [Measure.prod_prod, hIci, zero_mul]
    rw [hzero]
    simp
  rw [Lemma43.theta, hu, zero_div]

end Lemma43ArbitraryBase
end Feige
