/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Separable Hilbert Measurability -/

namespace Homogenization

/-!
# Separable Hilbert measurability helpers

This file isolates the abstract measurable-space facts needed by the
fixed-competitor measurability cleanup.  The first lemma is metric rather than
Hilbert-specific: a map into a second-countable metric Borel space is
measurable once its distances to a fixed countable dense sequence are
measurable.
-/

theorem measurable_of_measurable_dist_denseRange
    {Ω β : Type*} [MeasurableSpace Ω] [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (c : ℕ → β) (hc : DenseRange c) {F : Ω → β}
    (hFdist : ∀ n : ℕ, Measurable fun ω => dist (F ω) (c n)) :
    Measurable F := by
  classical
  let r : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  apply measurable_of_isOpen
  intro s hs
  let ballSet : ℕ × ℕ → Set Ω := fun p =>
    if Metric.ball (c p.1) (r p.2) ⊆ s then
      {ω | dist (F ω) (c p.1) < r p.2}
    else
      ∅
  have hballSet_meas : ∀ p : ℕ × ℕ, MeasurableSet (ballSet p) := by
    intro p
    by_cases hp : Metric.ball (c p.1) (r p.2) ⊆ s
    · have hdist : Measurable fun ω => dist (F ω) (c p.1) := hFdist p.1
      simpa [ballSet, hp] using measurableSet_lt hdist measurable_const
    · simp [ballSet, hp]
  have hpre :
      F ⁻¹' s = ⋃ p : ℕ × ℕ, ballSet p := by
    ext ω
    constructor
    · intro hω
      rw [Metric.isOpen_iff] at hs
      obtain ⟨ε, hε_pos, hε_sub⟩ := hs (F ω) hω
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
      have hr_pos : 0 < r m := by
        dsimp [r]
        positivity
      have htwo_r_lt : 2 * r m < ε := by
        dsimp [r] at hm ⊢
        nlinarith
      obtain ⟨n, hn⟩ :=
        (Metric.denseRange_iff.mp hc) (F ω) (r m) hr_pos
      refine Set.mem_iUnion.2 ⟨(n, m), ?_⟩
      have hsub : Metric.ball (c n) (r m) ⊆ s := by
        intro y hy
        rw [Metric.mem_ball] at hy
        apply hε_sub
        rw [Metric.mem_ball]
        have htriangle : dist y (F ω) ≤ dist y (c n) + dist (c n) (F ω) :=
          dist_triangle y (c n) (F ω)
        have hn' : dist (c n) (F ω) < r m := by
          simpa [dist_comm] using hn
        nlinarith [hy, hn', htriangle, htwo_r_lt]
      simpa [ballSet, hsub] using hn
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨p, hp⟩
      by_cases hsub : Metric.ball (c p.1) (r p.2) ⊆ s
      · have hdist : dist (F ω) (c p.1) < r p.2 := by
          simpa [ballSet, hsub] using hp
        exact hsub hdist
      · simp [ballSet, hsub] at hp
  rw [hpre]
  exact MeasurableSet.iUnion hballSet_meas

theorem measurable_of_measurable_dist_denseSeq
    {Ω β : Type*} [MeasurableSpace Ω] [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β] [Nonempty β]
    {F : Ω → β}
    (hFdist : ∀ n : ℕ, Measurable fun ω => dist (F ω) (TopologicalSpace.denseSeq β n)) :
    Measurable F :=
  measurable_of_measurable_dist_denseRange
    (TopologicalSpace.denseSeq β) (TopologicalSpace.denseRange_denseSeq β) hFdist

theorem measurable_of_measurable_norm_inner_denseRange
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (u : ℕ → H) (hu : DenseRange u) {F : Ω → H}
    (hNorm : Measurable fun ω => ‖F ω‖)
    (hInner : ∀ n : ℕ, Measurable fun ω => inner ℝ (u n) (F ω)) :
    Measurable F := by
  refine measurable_of_measurable_dist_denseRange u hu ?_
  intro n
  let c : H := u n
  have hInner' : Measurable fun ω => inner ℝ (F ω) c := by
    simpa [c, real_inner_comm] using hInner n
  have hNormSq : Measurable fun ω => ‖F ω‖ ^ 2 := by
    simpa [pow_two, Pi.mul_def] using hNorm.mul hNorm
  have hExpr :
      Measurable fun ω =>
        ‖F ω‖ ^ 2 - 2 * inner ℝ (F ω) c + ‖c‖ ^ 2 :=
    (hNormSq.sub (measurable_const.mul hInner')).add measurable_const
  have hSqrt :
      Measurable fun ω =>
        √(‖F ω‖ ^ 2 - 2 * inner ℝ (F ω) c + ‖c‖ ^ 2) :=
    hExpr.sqrt
  convert hSqrt using 1
  funext ω
  rw [dist_eq_norm]
  have hsq :
      ‖F ω - c‖ ^ 2 = ‖F ω‖ ^ 2 - 2 * inner ℝ (F ω) c + ‖c‖ ^ 2 :=
    norm_sub_sq_real (F ω) c
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem measurable_norm_of_norm_eq_iSup_abs_inner
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) {F : Ω → H}
    (hNormEq : ∀ x : H, ‖x‖ = ⨆ n : ℕ, |inner ℝ (u n) x|)
    (hInner : ∀ n : ℕ, Measurable fun ω => inner ℝ (u n) (F ω)) :
    Measurable fun ω => ‖F ω‖ := by
  have hSup : Measurable fun ω => ⨆ n : ℕ, |inner ℝ (u n) (F ω)| :=
    Measurable.iSup fun n => by
      simpa [Real.norm_eq_abs] using (hInner n).norm
  convert hSup using 1
  funext ω
  exact hNormEq (F ω)

theorem measurable_of_measurable_inner_denseRange_of_norm_eq_iSup_abs_inner
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (u : ℕ → H) (hu : DenseRange u) {F : Ω → H}
    (hNormEq : ∀ x : H, ‖x‖ = ⨆ n : ℕ, |inner ℝ (u n) x|)
    (hInner : ∀ n : ℕ, Measurable fun ω => inner ℝ (u n) (F ω)) :
    Measurable F :=
  measurable_of_measurable_norm_inner_denseRange u hu
    (measurable_norm_of_norm_eq_iSup_abs_inner u hNormEq hInner) hInner

theorem measurable_of_measurable_inner_denseRange_polish
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [PolishSpace H]
    (u : ℕ → H) (hu : DenseRange u) {F : Ω → H}
    (hInner : ∀ n : ℕ, Measurable fun ω => inner ℝ (u n) (F ω)) :
    Measurable F := by
  let Φ : H → (ℕ → ℝ) := fun x n => inner ℝ (u n) x
  have hΦ_meas : Measurable Φ := by
    refine measurable_pi_lambda ?_
    intro n
    simpa [Φ, innerSL_apply_apply] using (innerSL ℝ (u n)).measurable
  have hΦ_inj : Function.Injective Φ := by
    intro x y hxy
    apply (innerSL_inj (𝕜 := ℝ)).mp
    ext z
    have h_on :
        Set.EqOn (fun z => inner ℝ x z) (fun z => inner ℝ y z) (Set.range u) := by
      rintro z ⟨n, rfl⟩
      have hn := congr_fun hxy n
      simpa [Φ, real_inner_comm] using hn
    have hfun : (fun z => inner ℝ x z) = fun z => inner ℝ y z :=
      Continuous.ext_on hu (innerSL ℝ x).continuous (innerSL ℝ y).continuous h_on
    exact congr_fun hfun z
  exact (hΦ_meas.measurableEmbedding hΦ_inj).measurable_comp_iff.mp
    (measurable_pi_lambda hInner)

theorem measurable_of_measurable_norm_inner_denseSeq
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {F : Ω → H}
    (hNorm : Measurable fun ω => ‖F ω‖)
    (hInner : ∀ n : ℕ, Measurable fun ω => inner ℝ (TopologicalSpace.denseSeq H n) (F ω)) :
    Measurable F :=
  measurable_of_measurable_norm_inner_denseRange
    (TopologicalSpace.denseSeq H) (TopologicalSpace.denseRange_denseSeq H) hNorm hInner

end Homogenization
