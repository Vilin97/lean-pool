/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Ols.HCSandwichConsistency

/-!
# Conservative HC t-tests and their p-values

This file establishes that the heteroscedasticity-consistent t-tests, in
their p-value formulation, are asymptotically conservative under the
assumption bundle: at every level `α ∈ (0, 1)`, the probability of rejection
`P{p(t̂ₙ) ≤ α}` is asymptotically at most `α`.

To formalize p-values, we first create a reference distribution for two-sided tests
known as a `ConservativeTail`: a finite measure `ν` on `ℝ` that is non-zero on
nonempty open subintervals of `(0, ∞)` and has no atoms at `±z` for any `z`.  Its
two-sided tail `T(z) = ν{z < |x|}` is then provably finite, antitone, strictly antitone
on `[0, ∞)`, continuous on `(0, ∞)`, and vanishing at infinity, and the p-value of a
statistic `t` is `p(t) = T(|t|)`.

For a direction `a ≠ 0` we use the studentised statistic `t̂ₙ = √(Nbarₙ / D̂ₙ(ω)) · Zₙ(ω)`,
where `Zₙ = aᵀ(β̂ₙ−β*ₙ)/sₙ` is the projection-CLT statistic, `Nbarₙ = aᵀSₙ⁻¹MₙSₙ⁻¹a`
and `D̂ₙ = aᵀSₙ⁻¹M̂ₙSₙ⁻¹a` is its HC estimate; equivalently
`t̂ₙ = aᵀ(β̂ₙ−β*ₙ)/sHatₙ` with `sHatₙ² = D̂ₙ/n`.
Using this, we derive conservativeness results for the each of the HC estimators,
namely that `(limsup P{p(t̂ₙ) ≤ α}) ≤ α` for any `α ∈ (0,1)`.

The main results are:

· `hcGram_pvalue_conservative_of_level` — p-value conservativeness for
  any admissible multiplier family: at every level `α ∈ (0, 1)`,
  `(limsup P{p(t̂ₙ) ≤ α}) ≤ α`.
· `hc0/…/hc3_pvalue_conservative` — the same statement instantiated at the
  HC0–HC3 multipliers.
-/

open MeasureTheory ProbabilityTheory Matrix Finset BigOperators Filter
open scoped Topology ENNReal

namespace LeanPool.LinearModel

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Abstract tail functions and p-values

The p-value reductions below use only order and continuity facts about the
reference tail `z ↦ ν{z < |x|}`, and no Gaussian-specific facts.  `ConservativeTail`
carries the reference measure `ν` itself, together with the only two facts
that must be supplied: `ν` charges nonempty open subintervals of `(0, ∞)`,
and puts no atoms at `±z`.  Every property the reductions use (finiteness,
antitonicity, strict antitonicity on `[0, ∞)`, left-continuity of the tail)
is then a theorem, so a further instance (χ², F-ratio) requires establishing
only these two properties of a named distribution.  Internally everything stays
in `ℝ≥0∞`; `.toReal` appears only in the final statistical statements
(`pValue`, `gaussTailProb`). -/

section TailFunctions

/-- A reference distribution for two-sided tests: a finite measure `ν` that
has non-zero measure on nonempty open subintervals of `(0, ∞)` and has no
atoms at `±z` for `z > 0`.  The induced two-sided tail is `ConservativeTail.tail`. -/
structure ConservativeTail where
  /-- The finite reference measure whose two-sided tails define test levels. -/
  ν : Measure ℝ
  finite : IsFiniteMeasure ν
  open_pos : ∀ w z : ℝ, 0 ≤ w → w < z → 0 < ν (Set.Ioo w z)
  pair_null : ∀ z : ℝ, 0 < z → ν ({-z, z} : Set ℝ) = 0

namespace ConservativeTail

variable (Θ : ConservativeTail)

/-- The two-sided reference tail `tail z = ν {x | z < |x|}`. -/
def tail (z : ℝ) : ℝ≥0∞ := Θ.ν {x : ℝ | z < |x|}

/-- `tail z ≠ ∞` for any `z`. -/
lemma tail_ne_top (z : ℝ) : Θ.tail z ≠ ⊤ :=
  have := Θ.finite
  measure_ne_top _ _

/-- The tail is antitone. -/
lemma antitone_tail : Antitone Θ.tail := fun _ _ hwz =>
  measure_mono fun _ hx => lt_of_le_of_lt hwz hx

/-- The tail is strictly antitone on `[0, ∞)`. -/
lemma strictAntiOn_tail : StrictAntiOn Θ.tail (Set.Ici 0) := by
  intro w hw z _ hwz
  rw [Set.mem_Ici] at hw
  have hsub : {x : ℝ | z < |x|} ∪ Set.Ioo w z ⊆ {x : ℝ | w < |x|} := by
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_ofPred_eq] at hx ⊢
      linarith
    · rw [Set.mem_ofPred_eq]
      rw [Set.mem_Ioo] at hx
      have hx0 : 0 < x := lt_of_le_of_lt hw hx.1
      rw [abs_of_pos hx0]
      exact hx.1
  have hdisj : Disjoint {x : ℝ | z < |x|} (Set.Ioo w z) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_ofPred_eq] at hx
    rw [Set.mem_Ioo] at hx'
    have h0 : 0 < x := lt_of_le_of_lt hw hx'.1
    rw [abs_of_pos h0] at hx
    linarith [hx'.2]
  have hunion : Θ.ν ({x : ℝ | z < |x|} ∪ Set.Ioo w z)
      = Θ.ν {x : ℝ | z < |x|} + Θ.ν (Set.Ioo w z) :=
    measure_union hdisj measurableSet_Ioo
  simp only [tail]
  calc Θ.ν {x : ℝ | z < |x|}
      < Θ.ν {x : ℝ | z < |x|} + Θ.ν (Set.Ioo w z) :=
        ENNReal.lt_add_right (Θ.tail_ne_top z) (Θ.open_pos w z hw hwz).ne'
    _ = Θ.ν ({x : ℝ | z < |x|} ∪ Set.Ioo w z) := hunion.symm
    _ ≤ Θ.ν {x : ℝ | w < |x|} := measure_mono hsub

/-- No mass on `{|x| = z}`: the closed tail agrees with the open tail. -/
lemma measure_le_abs_eq_tail {z : ℝ} (hz : 0 < z) :
    Θ.ν {x : ℝ | z ≤ |x|} = Θ.tail z := by
  have hsub_pair : {x : ℝ | |x| = z} ⊆ ({-z, z} : Set ℝ) := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
    · right
      rw [he] at hx
      exact hx
    · left
      rw [he] at hx
      linarith
  have heq0 : Θ.ν {x : ℝ | |x| = z} = 0 :=
    measure_mono_null hsub_pair (Θ.pair_null z hz)
  have hunion : {x : ℝ | z ≤ |x|} = {x : ℝ | z < |x|} ∪ {x : ℝ | |x| = z} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  rw [tail, hunion]
  refine le_antisymm (le_trans (measure_union_le _ _) ?_)
    (measure_mono Set.subset_union_left)
  rw [heq0, add_zero]

/-- Left-continuity of the tail at every `z > 0`. -/
theorem tendsto_tail_nhdsLT {z : ℝ} (hz : 0 < z) :
    Tendsto Θ.tail (𝓝[<] z) (𝓝 (Θ.tail z)) := by
  have := Θ.finite
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact lt_of_lt_of_le hc (Θ.antitone_tail hw.le)
  · set s : ℕ → Set ℝ := fun n => {x : ℝ | z - 1 / (n + 1) < |x|} with hs_def
    have hmono : Antitone s := by
      intro i j hij x hx
      rw [hs_def, Set.mem_ofPred_eq] at hx ⊢
      have h1 : (1 : ℝ) / (j + 1) ≤ 1 / (i + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.succ_le_succ hij)
      linarith
    have hiInter : ⋂ n, s n = {x : ℝ | z ≤ |x|} := by
      ext x
      simp only [hs_def, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h
        have hlim : Tendsto (fun n : ℕ => z - 1 / ((n : ℝ) + 1)) atTop (𝓝 z) := by
          simpa using tendsto_const_nhds.sub
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact le_of_tendsto hlim (Eventually.of_forall fun n => (h n).le)
      · intro hx n
        have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hcont := tendsto_measure_iInter_atTop (μ := Θ.ν) (s := s)
      (fun n =>
        (measurableSet_lt measurable_const measurable_id.norm).nullMeasurableSet)
      hmono ⟨0, measure_ne_top _ _⟩
    rw [hiInter, Θ.measure_le_abs_eq_tail hz] at hcont
    obtain ⟨n, hn⟩ := (hcont.eventually_lt_const hc).exists
    have hlt : z - 1 / ((n : ℝ) + 1) < z := by
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    filter_upwards [Ioo_mem_nhdsLT hlt] with w hw
    calc Θ.tail w ≤ Θ.tail (z - 1 / ((n : ℝ) + 1)) := Θ.antitone_tail hw.1.le
      _ = Θ.ν (s n) := rfl
      _ < c := hn

/-- `z/(1+r)` approaches `z` strictly from the left as `r → 0⁺`. -/
lemma tendsto_div_one_add_nhdsLT {z : ℝ} (hz : 0 < z) :
    Tendsto (fun r : ℝ => z / (1 + r)) (𝓝[>] (0 : ℝ)) (𝓝[<] z) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Tendsto (fun r : ℝ => z / (1 + r)) (𝓝 0) (𝓝 (z / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by norm_num)
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Set.mem_Iio, div_lt_iff₀ (by linarith [Set.mem_Ioi.mp hr] : (0 : ℝ) < 1 + r)]
    nlinarith [hz, Set.mem_Ioi.mp hr]

/-- As `r → 0⁺`, `tail (z/(1+r)) → tail z`. -/
theorem tendsto_div_one_add {z : ℝ} (hz : 0 < z) :
    Tendsto (fun r : ℝ => Θ.tail (z / (1 + r))) (𝓝[>] (0 : ℝ))
      (𝓝 (Θ.tail z)) :=
  (Θ.tendsto_tail_nhdsLT hz).comp (tendsto_div_one_add_nhdsLT hz)

/-- Right-continuity of the tail at every `z`. -/
theorem tendsto_tail_nhdsGT (z : ℝ) :
    Tendsto Θ.tail (𝓝[>] z) (𝓝 (Θ.tail z)) := by
  have := Θ.finite
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · set s : ℕ → Set ℝ := fun n => {x : ℝ | z + 1 / (n + 1) < |x|} with hs_def
    have hmono : Monotone s := by
      intro i j hij x hx
      rw [hs_def, Set.mem_ofPred_eq] at hx ⊢
      have h1 : (1 : ℝ) / (j + 1) ≤ 1 / (i + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.succ_le_succ hij)
      linarith
    have hiUnion : ⋃ n, s n = {x : ℝ | z < |x|} := by
      ext x
      simp only [hs_def, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩
        have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨n, hn⟩ :=
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const
            (show (0 : ℝ) < |x| - z by linarith)).exists
        exact ⟨n, by linarith⟩
    have hcont := tendsto_measure_iUnion_atTop (μ := Θ.ν) (s := s) hmono
    rw [hiUnion] at hcont
    obtain ⟨n, hn⟩ := (hcont.eventually_const_lt hc).exists
    have hlt : z < z + 1 / ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    filter_upwards [Ioo_mem_nhdsGT hlt] with w hw
    calc c < Θ.ν (s n) := hn
      _ = Θ.tail (z + 1 / ((n : ℝ) + 1)) := rfl
      _ ≤ Θ.tail w := Θ.antitone_tail hw.2.le
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact lt_of_le_of_lt (Θ.antitone_tail hw.le) hc

/-- The tail is continuous at every `z > 0`. -/
theorem continuousAt_tail {z : ℝ} (hz : 0 < z) : ContinuousAt Θ.tail z := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rw [← continuousWithinAt_Iio_iff_Iic]
    exact Θ.tendsto_tail_nhdsLT hz
  · rw [← continuousWithinAt_Ioi_iff_Ici]
    exact Θ.tendsto_tail_nhdsGT z

/-- The tail vanishes at infinity. -/
theorem tendsto_tail_atTop : Tendsto Θ.tail atTop (𝓝 0) := by
  have := Θ.finite
  refine tendsto_order.2 ⟨fun c hc => absurd hc (by simp), fun c hc => ?_⟩
  set s : ℕ → Set ℝ := fun n => {x : ℝ | (n : ℝ) < |x|} with hs_def
  have hmono : Antitone s := by
    intro i j hij x hx
    rw [hs_def, Set.mem_ofPred_eq] at hx ⊢
    have h1 : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hiInter : ⋂ n, s n = ∅ := by
    ext x
    simp only [hs_def, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, hn.le⟩
  have hcont := tendsto_measure_iInter_atTop (μ := Θ.ν) (s := s)
    (fun n =>
      (measurableSet_lt measurable_const measurable_id.norm).nullMeasurableSet)
    hmono ⟨0, measure_ne_top _ _⟩
  rw [hiInter, measure_empty] at hcont
  obtain ⟨n, hn⟩ := (hcont.eventually_lt_const hc).exists
  filter_upwards [eventually_ge_atTop (n : ℝ)] with w hw
  calc Θ.tail w ≤ Θ.tail (n : ℝ) := Θ.antitone_tail hw
    _ = Θ.ν (s n) := rfl
    _ < c := hn

/-- The p-value of a test statistic: `p(t) = tail |t|`. -/
def pValue (t : ℝ) : ℝ := (Θ.tail |t|).toReal

/-- The `ℝ`-valued tail is antitone. -/
lemma toReal_tail_antitone : Antitone fun z => (Θ.tail z).toReal :=
  fun a _ hab => ENNReal.toReal_mono (Θ.tail_ne_top a) (Θ.antitone_tail hab)

/-- The `ℝ`-valued tail is strictly antitone on `[0, ∞)`. -/
lemma toReal_tail_strictAntiOn :
    StrictAntiOn (fun z => (Θ.tail z).toReal) (Set.Ici 0) :=
  fun w hw z hz hwz => (ENNReal.toReal_lt_toReal (Θ.tail_ne_top z)
    (Θ.tail_ne_top w)).mpr (Θ.strictAntiOn_tail hw hz hwz)

/-- p-values are measurable. -/
lemma measurable_pValue : Measurable Θ.pValue :=
  Θ.toReal_tail_antitone.measurable.comp continuous_abs.measurable

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}

/-- p-value conservativeness: rejecting when `p(Tₙ) ≤ α`, at any attainable
level `α = (tail z).toReal`, has asymptotic size at most `tail z`. -/
theorem pvalue_conservative {P : Measure Ω'} {T : ℕ → Ω' → ℝ}
    (hT : ∀ z, 0 < z →
      Filter.limsup (fun n => P {ω | z < |T n ω|}) atTop ≤ Θ.tail z)
    {z : ℝ} (hz : 0 < z) :
    Filter.limsup (fun n => P {ω | Θ.pValue (T n ω) ≤ (Θ.tail z).toReal})
      atTop ≤ Θ.tail z := by
  have hbound : ∀ r > (0 : ℝ),
      Filter.limsup (fun n => P {ω | Θ.pValue (T n ω) ≤ (Θ.tail z).toReal})
        atTop ≤ Θ.tail (z / (1 + r)) := by
    intro r hr
    have hz' : (0 : ℝ) < z / (1 + r) := div_pos hz (by linarith)
    refine le_trans (Filter.limsup_le_limsup
      (Filter.Eventually.of_forall fun n => measure_mono ?_)) (hT _ hz')
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω
    rw [Set.mem_ofPred_eq]
    -- `p(Tₙ) ≤ (tail z).toReal` forces `z ≤ |Tₙ|` by strict antitonicity,
    have hz_le : z ≤ |T n ω| := by
      by_contra hcon
      rw [not_le] at hcon
      have h := Θ.toReal_tail_strictAntiOn (Set.mem_Ici.mpr (abs_nonneg _))
        (Set.mem_Ici.mpr hz.le) hcon
      rw [pValue] at hω
      linarith
    -- and `z/(1+r) < z`.
    have hlt : z / (1 + r) < z := by
      rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + r)]
      nlinarith [hz, hr]
    linarith
  refine ge_of_tendsto (Θ.tendsto_div_one_add hz) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound r hr

end ConservativeTail

end TailFunctions


section GaussianTailInstance

/-- The standard Gaussian has non-zero measure on every nonempty open interval. -/
lemma gaussianReal_Ioo_pos {w z : ℝ} (hwz : w < z) :
    0 < gaussianReal 0 1 (Set.Ioo w z) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ measurableSet_Ioo]
  rw [show ∫⁻ x in Set.Ioo w z, gaussianPDF 0 1 x
      = ∫⁻ x, gaussianPDF 0 1 x ∂(volume.restrict (Set.Ioo w z)) from rfl]
  rw [lintegral_pos_iff_support (measurable_gaussianPDF 0 1)]
  rw [support_gaussianPDF one_ne_zero, Measure.restrict_apply_univ,
    Real.volume_Ioo]
  simp only [ENNReal.ofReal_pos]
  linarith

/-- The standard Gaussian puts no mass on `{|x| = z}`. -/
lemma gaussianReal_pair_eq_zero (z : ℝ) :
    (gaussianReal 0 1) ({-z, z} : Set ℝ) = 0 := by
  have : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  rw [Set.insert_eq]
  exact measure_union_null (measure_singleton _) (measure_singleton _)

/-- The standard Gaussian as a `ConservativeTail`. -/
def gaussianTail : ConservativeTail where
  ν := gaussianReal 0 1
  finite := inferInstance
  open_pos := fun _ _ _ hwz => gaussianReal_Ioo_pos hwz
  pair_null := fun z _ => gaussianReal_pair_eq_zero z

/-- The two-sided Gaussian tail probability `T(z) = N(0,1){z < |x|}`. -/
def gaussTailProb (z : ℝ) : ℝ := (gaussianTail.tail z).toReal

/-- The two-sided Gaussian p-value of a test statistic: `p(t) = T(|t|)`. -/
def twoSidedPValue (t : ℝ) : ℝ := gaussianTail.pValue t

/-- The Gaussian tail is antitone. -/
lemma gaussTailProb_antitone : Antitone gaussTailProb :=
  gaussianTail.toReal_tail_antitone

/-- The Gaussian tail is strictly antitone on `[0, ∞)`. -/
lemma gaussTailProb_strictAntiOn : StrictAntiOn gaussTailProb (Set.Ici 0) :=
  gaussianTail.toReal_tail_strictAntiOn

/-- Test levels are probabilities: `T(z) ≤ 1`. -/
lemma gaussTailProb_le_one (z : ℝ) : gaussTailProb z ≤ 1 := by
  rw [gaussTailProb]
  calc (gaussianTail.tail z).toReal
      ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp)
          (show (gaussianReal 0 1) {x : ℝ | z < |x|} ≤ 1 from prob_le_one)
    _ = 1 := by simp

/-- The two-sided Gaussian p-value is measurable. -/
lemma measurable_twoSidedPValue : Measurable twoSidedPValue :=
  gaussianTail.measurable_pValue

/-- The full two-sided mass: `gaussianTail.tail 0 = 1`. -/
lemma gaussianTail_tail_zero : gaussianTail.tail 0 = 1 := by
  change (gaussianReal 0 1) {x : ℝ | 0 < |x|} = 1
  have : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hset : {x : ℝ | 0 < |x|} = ({0}ᶜ : Set ℝ) := by
    ext x
    simp [abs_pos]
  rw [hset, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _),
    measure_singleton]
  simp

/-- `gaussTailProb` is continuous on `(0, ∞)`. -/
lemma continuousOn_gaussTailProb : ContinuousOn gaussTailProb (Set.Ioi 0) :=
  fun z hz => ContinuousAt.continuousWithinAt
    ((ENNReal.tendsto_toReal (gaussianTail.tail_ne_top z)).comp
      (gaussianTail.continuousAt_tail hz))

/-- Test levels vanish as the critical value grows. -/
lemma tendsto_gaussTailProb_atTop : Tendsto gaussTailProb atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp)).comp
    gaussianTail.tendsto_tail_atTop
  have hfun : ENNReal.toReal ∘ gaussianTail.tail =
      fun z => (gaussianTail.tail z).toReal := rfl
  rw [hfun] at h
  change Tendsto (fun z => (gaussianTail.tail z).toReal) atTop (𝓝 0)
  simpa using h

/-- Test levels approach `1` as the critical value shrinks to `0`. -/
lemma tendsto_gaussTailProb_nhdsGT_zero :
    Tendsto gaussTailProb (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (ENNReal.tendsto_toReal (gaussianTail.tail_ne_top 0)).comp
    (gaussianTail.tendsto_tail_nhdsGT 0)
  have hfun : ENNReal.toReal ∘ gaussianTail.tail =
      fun z => (gaussianTail.tail z).toReal := rfl
  rw [hfun] at h
  change Tendsto (fun z => (gaussianTail.tail z).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1)
  simpa [gaussianTail_tail_zero] using h

/-- Every `α ∈ (0, 1)` is an attained test level, `α = gaussTailProb z`
for some critical value `z > 0`. -/
lemma exists_gaussTailProb_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ z > (0 : ℝ), gaussTailProb z = α := by
  obtain ⟨zlo, hzlo_gt, hzlo_mem⟩ :=
    ((tendsto_gaussTailProb_nhdsGT_zero.eventually_const_lt hα1).and
      self_mem_nhdsWithin).exists
  obtain ⟨zhi, hzhi_lt⟩ :=
    (tendsto_gaussTailProb_atTop.eventually_lt_const hα0).exists
  have hlolt : zlo < zhi := by
    by_contra hcon
    rw [not_lt] at hcon
    have h := gaussTailProb_antitone hcon
    linarith
  have hsub : Set.Icc zlo zhi ⊆ Set.Ioi (0 : ℝ) := fun w hw =>
    Set.mem_Ioi.mpr (lt_of_lt_of_le hzlo_mem hw.1)
  obtain ⟨z, hz_mem, hz_eq⟩ := intermediate_value_Icc' hlolt.le
    (continuousOn_gaussTailProb.mono hsub) ⟨hzhi_lt.le, hzlo_gt.le⟩
  exact ⟨z, lt_of_lt_of_le hzlo_mem hz_mem.1, hz_eq⟩

end GaussianTailInstance


section ScalarSandwich

variable {p : ℕ}

/-- The sandwich quadratic form `aᵀ S⁻¹ M S⁻¹ a`. -/
def scalarSandwich (S M : Matrix (Fin p) (Fin p) ℝ) (a : Fin p → ℝ) : ℝ :=
  normSq' (S⁻¹ * M * S⁻¹) a

variable {P : Measure Ω}

variable [IsProbabilityMeasure P] {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ}
  {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- `D̂ₙ − Dbarₙ →ᵖ 0`, where `D̂ₙ = aᵀSₙ⁻¹M̂ₙSₙ⁻¹a` and
`Dbarₙ = aᵀSₙ⁻¹(Mₙ+Rₙ)Sₙ⁻¹a`. -/
theorem hcGram_scalarSandwich_consistent (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd : Tendsto (fun n => ⨆ i : Fin n, |d n i - 1|) atTop (𝓝 0))
    (a : Fin p → ℝ) :
    TendstoInProbability P
      (fun n ω => scalarSandwich (sampleGram (X n))
        (hcGram (X n) (d n) (fun i => y n i ω)) a)
      (fun n => scalarSandwich (sampleGram (X n)) (hcTarget P (X n) (y n)) a) :=
  TendstoInProbability.normSq'_of_entry a fun k ℓ =>
    hcGram_sandwich_consistent A1 d hd k ℓ

end ScalarSandwich


section OrderingAndLowerBounds

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- Misspecification only inflates the target:
 `Nbar = aᵀS⁻¹MS⁻¹a ≤ aᵀS⁻¹(M+R)S⁻¹a = Dbar`. -/
lemma scalarSandwich_ordering {n p : ℕ} (P : Measure Ω)
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ) (a : Fin p → ℝ) :
    scalarSandwich (sampleGram X) (varGram P X y) a
      ≤ scalarSandwich (sampleGram X) (hcTarget P X y) a := by
  set S : Matrix (Fin p) (Fin p) ℝ := sampleGram X with hS_def
  have hsplit : S⁻¹ * hcTarget P X y * S⁻¹
      = S⁻¹ * varGram P X y * S⁻¹
        + S⁻¹ * misspecGram P X y * S⁻¹ := by
    rw [hcTarget, Matrix.mul_add, Matrix.add_mul]
  have hadd : normSq' (S⁻¹ * varGram P X y * S⁻¹
        + S⁻¹ * misspecGram P X y * S⁻¹) a
      = normSq' (S⁻¹ * varGram P X y * S⁻¹) a
        + normSq' (S⁻¹ * misspecGram P X y * S⁻¹) a := by
    simp only [normSq', toBilin'_apply', Matrix.add_mulVec, dotProduct_add]
  rw [scalarSandwich, scalarSandwich, hsplit, hadd]
  have hpsd : 0 ≤ toBilin'
      (S⁻¹ * misspecGram P X y * S⁻¹) a a := by
    have hconj := normSq'_conj S⁻¹ (misspecGram P X y)
      (sampleGram_inv_transpose X) a
    rw [show toBilin' (S⁻¹ * misspecGram P X y * S⁻¹) a a
        = normSq' (S⁻¹ * misspecGram P X y * S⁻¹) a from rfl, hconj]
    exact weightedGram_psd_of_pos X _
      (fun i => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) _
  linarith

omit [IsProbabilityMeasure P] in
/-- For `n ≥ 1`, `α·‖a‖²/C ≤ Nbarₙ`, where `α` is a lower bound on the variances (from
the assumption bundle). -/
lemma AssumptionBundle.scalarSandwich_trueVar_lb (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) {n : ℕ} (hn : 0 < n) :
    A1.α / A1.C * (a ⬝ᵥ a)
      ≤ scalarSandwich (sampleGram (X n)) (varGram P (X n) (y n)) a := by
  set S : Matrix (Fin p) (Fin p) ℝ := sampleGram (X n) with hS_def
  set v : Fin p → ℝ := S⁻¹ *ᵥ a with hv_def
  have hdet : IsUnit S.det :=
    isUnit_sampleGram (X n) hn (A1.isUnit_gram_det hn)
  -- the sandwich as a quadratic form at `v = S⁻¹a`
  have h1 : scalarSandwich S (varGram P (X n) (y n)) a
      = normSq' (varGram P (X n) (y n)) v := by
    rw [scalarSandwich]
    exact normSq'_conj S⁻¹ _ (sampleGram_inv_transpose (X n)) a
  -- lower bound on variance: `Mₙ >= α·Sₙ` on quadratic forms
  have h2 : A1.α * normSq' S v
      ≤ normSq' (varGram P (X n) (y n)) v := by
    rw [hS_def, sampleGram_eq_weightedGram, varGram,
      weightedGram_normSq'_eq, weightedGram_normSq'_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hlb := A1.hvar_lb n i
    have hnn : (0 : ℝ) ≤ (X n i ⬝ᵥ v) ^ 2 := sq_nonneg _
    have hn_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    calc A1.α * (1 / (n : ℝ) * (X n i ⬝ᵥ v) ^ 2)
        = A1.α * (1 / (n : ℝ)) * (X n i ⬝ᵥ v) ^ 2 := by ring
      _ ≤ centralMoment (y n i) 2 P * (1 / (n : ℝ)) * (X n i ⬝ᵥ v) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          exact mul_le_mul_of_nonneg_right hlb hn_nn
      _ = centralMoment (y n i) 2 P / (n : ℝ) * (X n i ⬝ᵥ v) ^ 2 := by ring
  -- `vᵀSₙv = aᵀSₙ⁻¹a` and the spectral lower bound for `Sₙ⁻¹`
  have h3 : normSq' S v = normSq' S⁻¹ a := (normSq'_inv S hdet a).symm
  have h4 : 1 / A1.C * normSq a ≤ normSq' S⁻¹ a :=
    inv_spectral_lb S (sampleGram_transpose _) hdet (sampleGram_is_psd _)
      A1.C A1.hC_pos (A1.hGram_spectral_ub n hn) a
  have hσ_nn : (0 : ℝ) ≤ A1.α := A1.hvar_pos.le
  calc A1.α / A1.C * (a ⬝ᵥ a)
      = A1.α * (1 / A1.C * normSq a) := by
        rw [normSq]
        ring
    _ ≤ A1.α * normSq' S⁻¹ a := mul_le_mul_of_nonneg_left h4 hσ_nn
    _ = A1.α * normSq' S v := by rw [h3]
    _ ≤ normSq' (varGram P (X n) (y n)) v := h2
    _ = scalarSandwich S (varGram P (X n) (y n)) a := h1.symm

end OrderingAndLowerBounds


section OneSidedSlutsky

variable {P : Measure Ω}

/-- Per-`n` one-sided Slutsky bound. -/
lemma slutsky_per_n_bound_oneSided
    {Z : Ω → ℝ} {c_ω : Ω → ℝ} {c : ℝ}
    (hcω_nn : ∀ ω, 0 ≤ c_ω ω)
    {z : ℝ} (hz : 0 < z) {ε : ℝ} (hε : 0 < ε) (hc_nn : 0 ≤ c) :
    P {ω | z < |c_ω ω * Z ω|} ≤
      P {ω | z / (c + ε) < |Z ω|} + P {ω | c + ε < c_ω ω} := by
  have h_pos : 0 < c + ε := by linarith
  have h_incl : {ω | z < |c_ω ω * Z ω|} ⊆
      {ω | z / (c + ε) < |Z ω|} ∪ {ω | c + ε < c_ω ω} := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    by_contra h_not
    rw [not_or] at h_not
    obtain ⟨h_Z_le, h_c_close⟩ := h_not
    rw [not_lt] at h_Z_le h_c_close
    have h_cω_bd : |c_ω ω| ≤ c + ε := by
      rw [abs_of_nonneg (hcω_nn ω)]
      exact h_c_close
    have h_bd : |c_ω ω * Z ω| ≤ z := by
      rw [abs_mul]
      calc |c_ω ω| * |Z ω|
          ≤ (c + ε) * (z / (c + ε)) :=
            mul_le_mul h_cω_bd h_Z_le (abs_nonneg _) h_pos.le
        _ = z := by field_simp
    linarith
  exact le_trans (measure_mono h_incl) (measure_union_le _ _)

/-- One-sided Slutsky `limsup` tail bound. -/
theorem slutsky_limsup_tail_bound_oneSided
    {Z : ℕ → Ω → ℝ} {ν : Measure ℝ}
    (h_Z_dist : ∀ z' > (0 : ℝ),
        Tendsto (fun n => P {ω | z' < |Z n ω|}) atTop
          (𝓝 (ν {x : ℝ | z' < |x|})))
    {c_ω : ℕ → Ω → ℝ} {c : ℝ} (hc_nn : 0 ≤ c)
    (hcω_nn : ∀ n ω, 0 ≤ c_ω n ω)
    {ε : ℝ} (hε : 0 < ε)
    (h_c_prob : Tendsto (fun n => P {ω | c + ε < c_ω n ω}) atTop (𝓝 0))
    {z : ℝ} (hz : 0 < z) :
    Filter.limsup (fun n => P {ω | z < |c_ω n ω * Z n ω|}) atTop ≤
      ν {x : ℝ | z / (c + ε) < |x|} := by
  have h_per_n : ∀ n, P {ω | z < |c_ω n ω * Z n ω|} ≤
      P {ω | z / (c + ε) < |Z n ω|} + P {ω | c + ε < c_ω n ω} :=
    fun n => slutsky_per_n_bound_oneSided (hcω_nn n) hz hε hc_nn
  have h_Ztail_pos : (0 : ℝ) < z / (c + ε) := div_pos hz (by linarith)
  have h_sum_lim : Tendsto (fun n =>
      P {ω | z / (c + ε) < |Z n ω|} + P {ω | c + ε < c_ω n ω}) atTop
      (𝓝 (ν {x : ℝ | z / (c + ε) < |x|})) := by
    have h := (h_Z_dist _ h_Ztail_pos).add h_c_prob
    simpa using h
  calc Filter.limsup (fun n => P {ω | z < |c_ω n ω * Z n ω|}) atTop
      ≤ Filter.limsup (fun n =>
          P {ω | z / (c + ε) < |Z n ω|} + P {ω | c + ε < c_ω n ω}) atTop :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall h_per_n)
    _ = ν {x : ℝ | z / (c + ε) < |x|} := h_sum_lim.limsup_eq

/-- If `cₙ = √(Nbarₙ/D̂ₙ)`, `Nbarₙ ≤ Dbarₙ`, `m ≤ Nbarₙ` eventually for some `m > 0`
and `D̂ₙ − Dbarₙ →ᵖ 0`,
the event `{1 + ε < cₙ}` has vanishing probability. -/
lemma ratio_sqrt_oneSided_to_zero
    {Nbar Dbar : ℕ → ℝ} {Dhat : ℕ → Ω → ℝ}
    {m : ℝ} (hm : 0 < m)
    (hN_lb : ∀ᶠ n in atTop, m ≤ Nbar n)
    (hND : ∀ n, Nbar n ≤ Dbar n)
    (hDhat_conc : TendstoInProbability P Dhat Dbar)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | 1 + ε < Real.sqrt (Nbar n / Dhat n ω)}) atTop
      (𝓝 0) := by
  set β : ℝ := (1 + ε) ^ 2 with hβ_def
  have hβ_pos : 0 < β := by positivity
  have hβ_gt_one : 1 < β := by nlinarith [hε]
  set δ₀ : ℝ := (β - 1) * m / β with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := div_pos (mul_pos (by linarith) hm) hβ_pos
  have hδ₀_clear : δ₀ * β = (β - 1) * m := by
    rw [hδ₀_def]
    field_simp
  have h_incl : ∀ n, m ≤ Nbar n →
      {ω | 1 + ε < Real.sqrt (Nbar n / Dhat n ω)} ⊆
        {ω | δ₀ < |Dhat n ω - Dbar n|} := by
    intro n hNn ω hω
    rw [Set.mem_ofPred_eq] at hω
    rw [Set.mem_ofPred_eq]
    set r := Nbar n / Dhat n ω with hr_def
    have h_sqrt_pos : 0 < Real.sqrt r := by linarith
    have hr_pos : 0 < r := Real.sqrt_pos.mp h_sqrt_pos
    have hN_pos : 0 < Nbar n := lt_of_lt_of_le hm hNn
    have hDhat_pos : 0 < Dhat n ω := by
      rcases div_pos_iff.mp hr_pos with ⟨_, hd⟩ | ⟨hn_neg, _⟩
      · exact hd
      · exact absurd hN_pos (not_lt.mpr hn_neg.le)
    have hr_eq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr_pos.le
    have hβ_lt_r : β < r := by
      nlinarith [hω, hr_eq, Real.sqrt_nonneg r]
    have hβDhat_lt_N : β * Dhat n ω < Nbar n := by
      rw [hr_def, lt_div_iff₀ hDhat_pos] at hβ_lt_r
      linarith
    have hβDhat_lt_D : β * Dhat n ω < Dbar n :=
      lt_of_lt_of_le hβDhat_lt_N (hND n)
    have hDbar_lb : m ≤ Dbar n := le_trans hNn (hND n)
    have h_diff_lt : Dhat n ω - Dbar n < -δ₀ := by
      have hpos : 0 < β - 1 := by linarith
      nlinarith [hβDhat_lt_D, hDbar_lb, hδ₀_clear, hβ_pos, hpos,
        mul_le_mul_of_nonneg_left hDbar_lb hpos.le]
    rw [lt_abs]
    right
    linarith
  have hconc' := hDhat_conc δ₀ hδ₀_pos
  rw [ENNReal.tendsto_nhds_zero] at hconc' ⊢
  intro q hq
  filter_upwards [hconc' q hq, hN_lb] with n hn hNn
  exact le_trans (measure_mono (h_incl n hNn)) hn

end OneSidedSlutsky


section ConservativeSizeBound

/-- For every critical value z > 0, limsup_{n→∞} P(|t̂ₙ| > z) ≤ T(z). -/
theorem conservative_size_bound_of_oneSided (Θ : ConservativeTail)
    {P : Measure Ω}
    {Nbar Dbar : ℕ → ℝ} {Dhat Z : ℕ → Ω → ℝ}
    {m : ℝ} (hm : 0 < m)
    (hN_lb : ∀ᶠ n in atTop, m ≤ Nbar n)
    (hND : ∀ n, Nbar n ≤ Dbar n)
    (hDhat_conc : TendstoInProbability P Dhat Dbar)
    (h_Z_dist : ∀ z' > (0 : ℝ),
        Tendsto (fun n => P {ω | z' < |Z n ω|}) atTop (𝓝 (Θ.tail z')))
    {z : ℝ} (hz : 0 < z) :
    Filter.limsup (fun n => P {ω |
        z < |Real.sqrt (Nbar n / Dhat n ω) * Z n ω|}) atTop ≤ Θ.tail z := by
  have hbound : ∀ ε > (0 : ℝ),
      Filter.limsup (fun n => P {ω |
          z < |Real.sqrt (Nbar n / Dhat n ω) * Z n ω|}) atTop ≤
        Θ.tail (z / (1 + ε)) := by
    intro ε hε
    have hratio := ratio_sqrt_oneSided_to_zero (P := P) hm hN_lb hND
      hDhat_conc hε
    have hslutsky := slutsky_limsup_tail_bound_oneSided (P := P)
      (ν := Θ.ν)
      (c_ω := fun n ω => Real.sqrt (Nbar n / Dhat n ω)) (c := 1)
      h_Z_dist (by norm_num) (fun n ω => Real.sqrt_nonneg _) hε hratio hz
    simpa only [ConservativeTail.tail] using hslutsky
  refine ge_of_tendsto (Θ.tendsto_div_one_add hz) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

end ConservativeSizeBound


section TailPortmanteauTheorem

/-- For `z > 0`, `frontier {x : ℝ | z < |x|} = {-z, z}`. -/
private lemma frontier_abs_gt_eq {z : ℝ} (hz : 0 < z) :
    frontier {x : ℝ | z < |x|} = ({-z, z} : Set ℝ) := by
  have h_compl : {x : ℝ | z < |x|}ᶜ = Set.Icc (-z) z := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_Icc, not_lt]
    exact abs_le
  rw [← frontier_compl, h_compl, frontier_Icc (by linarith : -z ≤ z)]

/-- The standard Gaussian gives no mass to the two-point set `{-z, z}`. -/
private lemma stdGaussian_pair_eq_zero (z : ℝ) :
    ((stdGaussian : ProbabilityMeasure ℝ) : Measure ℝ) ({-z, z} : Set ℝ) = 0 :=
  gaussianReal_pair_eq_zero z

/-- The Portmanteau theorem applied to two-sided tails: if `μₙ → stdGaussian`
in distribution then the two-sided tail probabilities converge, for every `z > 0`. -/
lemma tendsto_measure_abs_gt_of_tendsto_stdGaussian
    {μs : ℕ → ProbabilityMeasure ℝ}
    (h_lim : Tendsto μs atTop (𝓝 stdGaussian))
    {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n => (μs n : Measure ℝ) {x : ℝ | z < |x|}) atTop
      (𝓝 ((gaussianReal 0 1) {x : ℝ | z < |x|})) := by
  have h_null : ((stdGaussian : ProbabilityMeasure ℝ) : Measure ℝ)
      (frontier {x : ℝ | z < |x|}) = 0 := by
    rw [frontier_abs_gt_eq hz]
    exact stdGaussian_pair_eq_zero z
  have h_tendsto :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h_lim h_null
  have h_std_eq : ((stdGaussian : ProbabilityMeasure ℝ) : Measure ℝ)
      = gaussianReal 0 1 := rfl
  rw [← h_std_eq]
  exact h_tendsto

end TailPortmanteauTheorem


section TailTendsto

variable {p : ℕ} {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ}
  {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- For every `z > 0`, `P{z < |aᵀ(β̂ₙ−β*ₙ)/sₙ|} → N(0,1){z < |x|}`. -/
theorem AssumptionBundle.olsArray_tail_tendsto {P : Measure Ω}
    [IsProbabilityMeasure P] (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) :
    ∀ z > (0 : ℝ), Tendsto
      (fun n => P {ω | z < |LindebergSumTriangular (olsArray P X y a) P n ω|}) atTop
      (𝓝 ((gaussianReal 0 1) {x : ℝ | z < |x|})) := by
  intro z hz
  set Pprob : ProbabilityMeasure Ω := ⟨P, ‹IsProbabilityMeasure P›⟩
    with hPprob_def
  have hclt : Tendsto
      (fun n : ℕ => Pprob.map (aemeasurable_olsArray X y a A1.hy_meas n))
      atTop (𝓝 stdGaussian) :=
    AssumptionBundle.central_limit_OLS_projection' (P := Pprob) A1 a ha_nz.symm
  have htail := tendsto_measure_abs_gt_of_tendsto_stdGaussian hclt hz
  refine htail.congr fun n => ?_
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_LindebergSumTriangular n (olsArray_measurable X y a A1.hy_meas))
      (measurableSet_lt measurable_const continuous_abs.measurable)]
  rfl

end TailTendsto


section ConservativeTests

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- The HC-studentised statistic `t̂ₙ = √(Nbarₙ/D̂ₙ(ω)) · Zₙ(ω)`, with
`Zₙ = aᵀ(β̂ₙ−β*ₙ)/sₙ` the projection-CLT statistic. -/
def hcStudentized (P : Measure Ω) (X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ)
    (y : (n : ℕ) → Fin n → Ω → ℝ) (d : (n : ℕ) → Fin n → ℝ)
    (a : Fin p → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (scalarSandwich (sampleGram (X n)) (varGram P (X n) (y n)) a
      / scalarSandwich (sampleGram (X n))
        (hcGram (X n) (d n) (fun i => y n i ω)) a)
    * LindebergSumTriangular (olsArray P X y a) P n ω

/-- Generic conservative t-test result: for any multiplier family with
`⨆ᵢ|dₙᵢ − 1| → 0` and any `a ≠ 0`, the HC-studentised test is asymptotically
conservative: `limsup P{z < |t̂ₙ|} ≤ N(0,1){z < |x|}`. -/
theorem hcGram_conservative_test (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd : Tendsto (fun n => ⨆ i : Fin n, |d n i - 1|) atTop (𝓝 0))
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {z : ℝ} (hz : 0 < z) :
    Filter.limsup
      (fun n => P {ω | z < |hcStudentized P X y d a n ω|}) atTop ≤
      (gaussianReal 0 1) {x : ℝ | z < |x|} := by
  have ha : 0 < a ⬝ᵥ a :=
    (Finset.sum_nonneg fun i _ => mul_self_nonneg _).lt_of_ne fun h =>
      ha_nz (dotProduct_self_eq_zero.mp h.symm)
  have hm_pos : 0 < A1.α / A1.C * (a ⬝ᵥ a) :=
    mul_pos (div_pos A1.hvar_pos A1.hC_pos) ha
  have hN_lb : ∀ᶠ n in atTop, A1.α / A1.C * (a ⬝ᵥ a)
      ≤ scalarSandwich (sampleGram (X n)) (varGram P (X n) (y n)) a := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact A1.scalarSandwich_trueVar_lb a hn
  have hND : ∀ n,
      scalarSandwich (sampleGram (X n)) (varGram P (X n) (y n)) a
        ≤ scalarSandwich (sampleGram (X n)) (hcTarget P (X n) (y n)) a :=
    fun n => scalarSandwich_ordering P (X n) (y n) a
  have hDhat_conc := hcGram_scalarSandwich_consistent A1 d hd a
  have hZ := A1.olsArray_tail_tendsto a ha_nz
  exact conservative_size_bound_of_oneSided gaussianTail hm_pos hN_lb hND
    hDhat_conc hZ hz

end ConservativeTests


section PValueTests

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

/-- p-value conservativeness at every level `α ∈ (0, 1)`:
`(limsup P{p(t̂ₙ) ≤ α}) ≤ α`. -/
theorem hcGram_pvalue_conservative_of_level (A1 : AssumptionBundle P X y)
    (d : (n : ℕ) → Fin n → ℝ)
    (hd : Tendsto (fun n => ⨆ i : Fin n, |d n i - 1|) atTop (𝓝 0))
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Filter.limsup (fun n => P {ω |
        twoSidedPValue (hcStudentized P X y d a n ω) ≤ α}) atTop).toReal
      ≤ α := by
  obtain ⟨z, hz, hzα⟩ := exists_gaussTailProb_eq hα0 hα1
  rw [← hzα]
  exact ENNReal.toReal_mono (gaussianTail.tail_ne_top z)
    (gaussianTail.pvalue_conservative
      (fun _ hz' => hcGram_conservative_test A1 d hd a ha_nz hz') hz)

/-- HC0 p-value conservativeness. -/
theorem hc0_pvalue_conservative (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Filter.limsup (fun n => P {ω | twoSidedPValue
        (hcStudentized P X y (fun _ _ => 1) a n ω) ≤ α}) atTop).toReal
      ≤ α :=
  hcGram_pvalue_conservative_of_level A1 (fun _ _ => 1)
    hc0_multiplier_tendsto a ha_nz hα0 hα1

/-- HC1 p-value conservativeness. -/
theorem hc1_pvalue_conservative (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Filter.limsup (fun n => P {ω | twoSidedPValue
        (hcStudentized P X y (fun n _ => hc1Correction n p) a n ω) ≤ α})
      atTop).toReal ≤ α :=
  hcGram_pvalue_conservative_of_level A1 (fun n _ => hc1Correction n p)
    (hc1_multiplier_tendsto p) a ha_nz hα0 hα1

/-- HC2 p-value conservativeness. -/
theorem hc2_pvalue_conservative (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Filter.limsup (fun n => P {ω | twoSidedPValue
        (hcStudentized P X y (fun n => hc2Correction (X n)) a n ω) ≤ α})
      atTop).toReal ≤ α :=
  hcGram_pvalue_conservative_of_level A1 (fun n => hc2Correction (X n))
    A1.hc2_multiplier_tendsto a ha_nz hα0 hα1

/-- HC3 p-value conservativeness. -/
theorem hc3_pvalue_conservative (A1 : AssumptionBundle P X y)
    (a : Fin p → ℝ) (ha_nz : a ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (Filter.limsup (fun n => P {ω | twoSidedPValue
        (hcStudentized P X y (fun n => hc3Correction (X n)) a n ω) ≤ α})
      atTop).toReal ≤ α :=
  hcGram_pvalue_conservative_of_level A1 (fun n => hc3Correction (X n))
    A1.hc3_multiplier_tendsto a ha_nz hα0 hα1

end PValueTests


end

end LinearModel
end LeanPool
