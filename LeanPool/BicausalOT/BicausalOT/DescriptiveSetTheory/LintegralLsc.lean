/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lower semicontinuity of `γ ↦ ∫⁻ f dγ` on `ProbabilityMeasure W`

For a lower semicontinuous `f : W → ℝ≥0∞` on a Polish Borel space `W`, the
map `γ ↦ ∫⁻ x, f x ∂γ` is lower semicontinuous on `ProbabilityMeasure W`
with the topology of weak convergence.

## Proof route

Mathlib has the portmanteau open-set inequality for arbitrary filters
(`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) and the
real-valued layer-cake formula (`MeasureTheory.lintegral_eq_lintegral_meas_lt`),
but only a `Continuous`/`ℝ`-valued version of the liminf inequality for
integrals (`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`).
We upgrade it to lower semicontinuous `ℝ≥0∞`-valued integrands in three steps:

1. `LowerSemicontinuous.lintegral_le_liminf_of_ne_top`: for `f` lsc with finite
   values, rewrite `∫⁻ f ∂ν = ∫⁻ t in Ioi 0, ν {a | t < (f a).toReal}` by the
   layer-cake formula; superlevel sets of an lsc function are open, so the
   open-set liminf hypothesis applies pointwise in `t`, and Fatou's lemma
   (`lintegral_liminf_le`) swaps `liminf` with the `t`-integral.
2. `LowerSemicontinuous.lintegral_le_liminf`: reduce a general lsc `f` to the
   truncations `min f n` (again lsc, with finite values) via monotone
   convergence.
3. `lowerSemicontinuous_lintegral_probabilityMeasure`: lower semicontinuity at
   `γ` follows from the sequential bound: `ProbabilityMeasure W` is metrizable
   (Lévy–Prokhorov, `instMetrizableSpaceProbabilityMeasure`), hence first
   countable, so a failure of lower semicontinuity yields a sequence
   `γs → γ` with `∫⁻ f ∂(γs n) ≤ y < ∫⁻ f ∂γ`, contradicting step 2 combined
   with the portmanteau inequality along `γs`.
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.ENNRealTruncation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic


/-!
# LintegralLsc

Supporting results for BicausalOT.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

section SequentialBound

variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]

/-- Portmanteau-type liminf inequality for the lower Lebesgue integral of a lower
semicontinuous function with finite values: if `μ G ≤ liminf (μs · G)` for every open `G`,
then `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂(μs ·))`.

This is the `ℝ≥0∞`-valued analogue of
`MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`:
layer-cake formula + openness of superlevel sets + Fatou's lemma. -/
theorem LowerSemicontinuous.lintegral_le_liminf_of_ne_top
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f) (hf_ne : ∀ x, f x ≠ ∞)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by
  have g_nn : ∀ x, (0 : ℝ) ≤ (f x).toReal := fun x => ENNReal.toReal_nonneg
  have g_mble : Measurable fun x => (f x).toReal := hf.measurable.ennreal_toReal
  -- superlevel sets of `x ↦ (f x).toReal` are open
  have levels_open : ∀ t : ℝ, IsOpen {a : W | t < (f a).toReal} := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · have huniv : {a : W | t < (f a).toReal} = univ :=
        eq_univ_of_forall fun a => lt_of_lt_of_le ht (g_nn a)
      rw [huniv]
      exact isOpen_univ
    · have hpre : {a : W | t < (f a).toReal} = f ⁻¹' Ioi (ENNReal.ofReal t) := by
        ext a
        simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
        exact (ENNReal.ofReal_lt_iff_lt_toReal ht (hf_ne a)).symm
      rw [hpre]
      exact hf.isOpen_preimage _
  -- layer-cake formula for each measure
  have key : ∀ ν : Measure W,
      ∫⁻ x, f x ∂ν = ∫⁻ t in Ioi (0 : ℝ), ν {a : W | t < (f a).toReal} := fun ν =>
    (lintegral_congr fun x => (ENNReal.ofReal_toReal (hf_ne x)).symm).trans
      (lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall g_nn) g_mble.aemeasurable)
  calc ∫⁻ x, f x ∂μ
      = ∫⁻ t in Ioi (0 : ℝ), μ {a : W | t < (f a).toReal} := key μ
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), atTop.liminf fun i => μs i {a : W | t < (f a).toReal} :=
        lintegral_mono fun t => h_opens _ (levels_open t)
    _ ≤ atTop.liminf fun i => ∫⁻ t in Ioi (0 : ℝ), μs i {a : W | t < (f a).toReal} :=
        lintegral_liminf_le fun i => Antitone.measurable fun s t hst =>
          measure_mono fun ω hω => lt_of_le_of_lt hst hω
    _ = atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) :=
        liminf_congr (Eventually.of_forall fun i => (key (μs i)).symm)

/-- Portmanteau-type liminf inequality for the lower Lebesgue integral of a lower
semicontinuous `ℝ≥0∞`-valued function: if `μ G ≤ liminf (μs · G)` for every open `G`,
then `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂(μs ·))`.

Reduces to `LowerSemicontinuous.lintegral_le_liminf_of_ne_top` via the truncations
`min f n` and monotone convergence. -/
theorem LowerSemicontinuous.lintegral_le_liminf
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by
  -- the truncations are again lower semicontinuous
  have h_trunc_lsc : ∀ n : ℕ, LowerSemicontinuous fun x => min (f x) (n : ℝ≥0∞) := by
    intro n x y hy
    filter_upwards [hf x y (hy.trans_le (min_le_left _ _))] with z hz
    exact lt_min hz (hy.trans_le (min_le_right _ _))
  -- each truncation satisfies the liminf bound for the untruncated integrals
  have h_bound : ∀ n : ℕ,
      ∫⁻ x, min (f x) (n : ℝ≥0∞) ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := fun n =>
    ((h_trunc_lsc n).lintegral_le_liminf_of_ne_top
        (fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))
        h_opens).trans
      (liminf_le_liminf
        (Eventually.of_forall fun i => lintegral_mono fun x => min_le_left _ _))
  -- monotone convergence for the truncations
  calc ∫⁻ x, f x ∂μ
      = ⨆ n : ℕ, ∫⁻ x, min (f x) (n : ℝ≥0∞) ∂μ := by
        rw [← lintegral_iSup (fun n => hf.measurable.min measurable_const)
            (fun n m hnm x => min_le_min le_rfl (by exact_mod_cast hnm))]
        exact lintegral_congr fun x => (ennreal_iSup_min_natCast (f x)).symm
    _ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := iSup_le h_bound

end SequentialBound

/-- **Lower semicontinuity of integration on `P(W)`.** For a Polish Borel space `W` and a
lower semicontinuous `f : W → ℝ≥0∞`, the map `γ ↦ ∫⁻ x, f x ∂γ` is lower semicontinuous
on `ProbabilityMeasure W` with the topology of weak convergence. -/
theorem lowerSemicontinuous_lintegral_probabilityMeasure
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W] [BorelSpace W]
    {f : W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun γ : ProbabilityMeasure W => ∫⁻ x, f x ∂(γ : Measure W) := by
  intro γ y hy
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- extract a sequence `γs → γ` along which the integrals stay `≤ y`;
  -- `ProbabilityMeasure W` is metrizable, hence `𝓝 γ` is countably generated
  have h_freq : ∃ᶠ ν : ProbabilityMeasure W in 𝓝 γ, ∫⁻ x, f x ∂(ν : Measure W) ≤ y :=
    hcon.mono fun ν hν => not_lt.mp hν
  obtain ⟨γs, hγs_tendsto, hγs_le⟩ := exists_seq_forall_of_frequently h_freq
  -- portmanteau: the open-set liminf condition holds along `γs`
  have h_opens : ∀ G, IsOpen G →
      (γ : Measure W) G ≤ atTop.liminf fun i => (γs i : Measure W) G := fun _ hG =>
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hγs_tendsto hG
  have h_le : ∫⁻ x, f x ∂(γ : Measure W) ≤
      atTop.liminf fun i => ∫⁻ x, f x ∂(γs i : Measure W) :=
    hf.lintegral_le_liminf h_opens
  have h_lim_le : (atTop.liminf fun i => ∫⁻ x, f x ∂(γs i : Measure W)) ≤ y :=
    liminf_le_of_frequently_le' (Frequently.of_forall hγs_le)
  exact absurd (hy.trans_le (h_le.trans h_lim_le)) (lt_irrefl y)
