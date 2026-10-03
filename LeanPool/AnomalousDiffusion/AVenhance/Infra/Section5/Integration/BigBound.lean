/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound.Grouped
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Cutoff1Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie1Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie2Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.TinyScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Twistie1Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Twistie3Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Matrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts

/-! # Big-bound estimate wiring: `BigBoundStatement` from the explicit §5.2 inputs

`bigbound_of_inputs` turns the conditional §5.2 term estimates (`Terms/*Scale.lean`) and the
conditional ten-term assembly into the literal big-bound estimate proposition `BigBoundStatement β
    C₀`.
The inputs proved in other modules are collected, for one instance, in the `Prop`-valued
structure `BigBoundInputs`; no field is (or contains) the big-bound estimate conclusion.

Hypotheses of the existing conditional lemmas that are *derived here* and therefore not fields:
* `MemL2On` of every slice of every term and the time measurability of the `HDot⁻¹` norms of the
  terms and of all partial sums (from joint continuity `term_continuous`, via
  `HMinusMeasurable.lean`);
* the residual identity at *closed* times / all `x` (only open times `Ioo 0 1` are used,
  `timeHMinusOneNorm_residual_le_sum_sourceScale_Ioo`);

Grouped mean zero: the assembly uses that the sum of `twistie4`, `twistie5` and `normie3` is mean
zero (`group_meanZero`).  It runs on the *centered*
ten-term family `section5CenteredTerm` (slots `3`, `4`, `8` replaced by `centerCell`, see
`BigBound/Grouped.lean`), whose pointwise sum equals the original ten-term sum on `(0,1)` by
`group_meanZero`.  The three centered slots are bounded directly by the fields
`twistie4_centered_source`, `twistie5_centered_source`, `normie3_centered_source`; the other seven
slots by the existing conditional `*_sourceScale` theorems.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ### Small analytic and ENNReal helpers -/

/-- `ofReal (κ ^ (-1/2))` times the sum of ten copies of `ofReal (c √κ)` is `ofReal (10 c)`. -/
theorem ofReal_rpow_neg_half_mul_sum_ten {κ : ℝ} (hκ : 0 < κ) (c : ℝ) :
    ENNReal.ofReal (κ ^ (-(1 / 2 : ℝ))) *
        ∑ _i ∈ Finset.range 10, ENNReal.ofReal (c * Real.sqrt κ) =
      ENNReal.ofReal (10 * c) := by
  have hsq : κ ^ (-(1 / 2 : ℝ)) * Real.sqrt κ = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hκ]
    norm_num
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h10 : ((10 : ℕ) : ENNReal) = ENNReal.ofReal 10 := by
    rw [ENNReal.ofReal_ofNat]
    norm_num
  rw [h10, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hκ.le _)]
  congr 1
  calc κ ^ (-(1 / 2 : ℝ)) * (10 * (c * Real.sqrt κ))
      = 10 * c * (κ ^ (-(1 / 2 : ℝ)) * Real.sqrt κ) := by ring
    _ = 10 * c := by rw [hsq, mul_one]

/-- Conversion of the normalised (`κ_m ^ (-1/2)`) bound to the plain time-norm bound used in the
`κ_m^{1/2}`-scaled form (step-down part (i)). -/
theorem timeHMinusOneNorm_le_of_bigbound_conclusion {κm X : ℝ} {N : ENNReal}
    (h : ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) * N ≤ ENNReal.ofReal X)
    (hκ : 0 < κm) :
    N ≤ ENNReal.ofReal (X * Real.sqrt κm) := by
  have hsq : Real.sqrt κm * κm ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hκ]
    norm_num
  have hone : ENNReal.ofReal (Real.sqrt κm) * ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsq, ENNReal.ofReal_one]
  calc N = ENNReal.ofReal (Real.sqrt κm) *
          (ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) * N) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (Real.sqrt κm) * ENNReal.ofReal X := by gcongr
    _ = ENNReal.ofReal (X * Real.sqrt κm) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]

/-! ### The ten-term assembly with the residual identity on open times only -/

section Assembly

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `timeHMinusOneNorm_residual_le_sum_sourceScale`, with the residual identity assumed only for
`t ∈ (0,1)` (the only times seen by the time norm). -/
theorem timeHMinusOneNorm_residual_le_sum_sourceScale_Ioo
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e b : ℝ → Vec 2 → Vec 2)
    (hResidual : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x, residualIdentity I hΦ m κm T d e b t x)
    (htermL2 : ∀ i, i < 10 → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MemL2On unitCube (section5Term I hΦ m κm T d e i t))
    (htermMeas : ∀ i, i < 10 →
      AEMeasurable
        (fun t => hMinusOneNorm (section5Term I hΦ m κm T d e i t))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hprefixMeas : ∀ n, 1 ≤ n → n < 10 →
      AEMeasurable
        (fun t => hMinusOneNorm (section5Prefix I hΦ m κm T d e n t))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    {S : ℝ}
    (htermScale : ∀ i, i < 10 →
      timeHMinusOneNorm (section5Term I hΦ m κm T d e i) ≤ ENNReal.ofReal S) :
    timeHMinusOneNorm
      (fun t x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) ≤
      ∑ _i ∈ Finset.range 10, ENNReal.ofReal S := by
  have hprefixBound := timeHMinusOneNorm_section5Prefix_le_sum I hΦ m κm T d e
    htermL2 htermMeas hprefixMeas 10 (by norm_num) (by norm_num)
  have hEq : timeHMinusOneNorm
      (fun t x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) =
        timeHMinusOneNorm (section5Prefix I hΦ m κm T d e 10) := by
    unfold timeHMinusOneNorm
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hfun : (fun x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) =
        section5Prefix I hΦ m κm T d e 10 t := by
      funext x
      rw [hResidual t ht x]
      exact (congrFun (congrFun
        (section5Prefix_ten_eq_terms I hΦ m κm T d e) t) x).symm
    change hMinusOneNorm (fun x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) ^ 2 = _
    rw [hfun]
  rw [hEq]
  exact hprefixBound.trans
    (Finset.sum_le_sum fun i hi => htermScale i (Finset.mem_range.mp hi))

end Assembly

/-! ### The input structure -/

section Inputs

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The remaining upstream statements needed to obtain the big-bound estimate bound `e.bigbound`
    for ONE
instance `(I, Φ, m, κ_m, κ_{m-1}, T, θ₀)` with common constant `C`.

Notation: `N := T (Nstar β)` is the final T-iterate, `d := sourceErrorD I hΦ m κm N`,
`e := iterateError I hΦ m κm κprev T`, `S := section5SourceScale β I.Λ m κm C θ₀
= C ε_{m-1}^δ √κ_m ‖θ₀‖`.  The `hsource` fields are the `S`-sized space-time `L²` bounds on the
spatial `L²` norm (or flux gradient norm) of each term (the "monster" display
`e.monster.cutoff1`–`e.monster.normie3`, `enhance.tex` 6886–6990; estimates 7300–8010).

Grouped mean zero: `twistie4`, `twistie5`, `normie3` carry no individual mean-zero or source field;
instead `group_meanZero` (their sum is mean zero) and the three centered negative-norm bounds
`twistie4_centered_source`, `twistie5_centered_source`, `normie3_centered_source`.

Fields dropped relative to the underlying conditional lemmas (proved in this file, from the single
field `term_continuous`): `MemL2On` of every slice of every term (`memL2On_of_continuousOn_slice`),
the time measurability of the `HDot⁻¹` norm of every term and every partial sum
(`aemeasurable_hMinusOneNorm_of_continuousOn`; a partial sum of continuous terms is continuous),
the residual identity at `t ∉ (0,1)`. -/
structure BigBoundInputs (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (C : ℝ) : Prop where
  /-- The exact `ε`-residual identity `e.monster` for the ansatz built from
  `N = T (Nstar β)` with the source errors `d_m` (`e.dm`) and `e_{m-1}`
  (`enhance.tex` 6886–6990). -/
  residual : ResidualContract I hΦ m κm κprev T
  /-- Mean zero of `cutoff1(t)` on the cube, `t ∈ (0,1)`. -/
  cutoff1_meanZero : Cutoff1MeanZeroContract I hΦ m κm T
  /-- Source-scale space-time `L²` bound for `cutoff1` (`e.monster.est.*`, 7300–7500; a §3/§4
  bound). -/
  cutoff1_source : Cutoff1SourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Negative-norm source bound for `twistie1` (`e.monster.est.5`, ergodic lemma). -/
  twistie1_hminus_source : Twistie1HMinusSourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Smoothness of the divergence flux of `twistie3` (`e.monster.twistie3`, 6912), `t ∈ (0,1)`. -/
  twistie3_flux_smooth : Twistie3FluxSmoothContract I hΦ m κm T
  /-- `ℤ²`-periodicity of the `twistie3` flux. -/
  twistie3_flux_periodic : Twistie3FluxPeriodicContract I hΦ m κm T
  /-- Source-scale space-time `L²` bound on `∇ (twistie3 flux)`-norm (§3/§4 bound). -/
  twistie3_source : Twistie3SourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Grouped mean zero: the sum of `twistie4`, `twistie5` and `normie3` is mean zero on
  the cube for `t ∈ (0,1)`; the centered estimates below use this grouped form. -/
  group_meanZero : GroupMeanZeroContract I hΦ m κm T
  /-- Centered negative-norm bound for `twistie4`: the time `HDot⁻¹` norm
  of its unit-cube centering is at most the common source scale. -/
  twistie4_centered_source : Twistie4CenteredSourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Centered negative-norm bound for `twistie5`. -/
  twistie5_centered_source : Twistie5CenteredSourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Centered negative-norm bound for `normie3`. -/
  normie3_centered_source : Normie3CenteredSourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Smoothness of the divergence flux of `normie1` (`e.monster.normie1`, 6950). -/
  normie1_flux_smooth : Normie1FluxSmoothContract I hΦ m κm T
  /-- `ℤ²`-periodicity of the `normie1` flux. -/
  normie1_flux_periodic : Normie1FluxPeriodicContract I hΦ m κm T
  /-- Source-scale space-time `L²` bound on the `normie1` flux gradient (§3/§4 bound). -/
  normie1_source : Normie1SourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Smoothness of the divergence flux of `normie2` (`e.monster.normie2`, 6959). -/
  normie2_flux_smooth : Normie2FluxSmoothContract I hΦ m κm T
  /-- `ℤ²`-periodicity of the `normie2` flux. -/
  normie2_flux_periodic : Normie2FluxPeriodicContract I hΦ m κm T
  /-- Source-scale space-time `L²` bound on the `normie2` flux gradient (§3/§4 bound; `H_m`
  estimates). -/
  normie2_source : Normie2SourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Negative-norm source bound for `tiny` (`e.monster.est.tiny`, divergence form). -/
  tiny_hminus_source : TinyHMinusSourceContract I hΦ m κm κprev T C (Real.sqrt (l2NormSq θ₀))
  /-- Smoothness of the transition-window flux of `R46` (the transition remainder). -/
  R46_flux_smooth : R46FluxSmoothContract I hΦ m κm T
  /-- `ℤ²`-periodicity of the `R46` flux. -/
  R46_flux_periodic : R46FluxPeriodicContract I hΦ m κm T
  /-- Source-scale `L²` bound on the `R46` flux gradient (the transition-window estimate that
  the source does not state; §3/§4 bound). -/
  R46_source : R46SourceContract I hΦ m κm T C (Real.sqrt (l2NormSq θ₀))
  /-- Joint continuity of every named term on `(0,1) × ℝ²` (source: all pieces are smooth for
  `t > 0`).  From it are derived the `L²` regularity of every slice `t ∈ (0,1)` and the time
  measurability of the `HDot⁻¹` norms of the terms and of their partial sums. -/
  term_continuous : TermContinuousContract I hΦ m κm κprev T

variable {I} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κm κprev : ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
  {θ₀ : Vec 2 → ℝ} {C : ℝ}

/-- Every slice `t ∈ (0,1)` of every term is `L²` on the cube (continuity of the term). -/
theorem BigBoundInputs.termL2 (h : BigBoundInputs I hΦ m κm κprev T θ₀ C) :
    ∀ i, i < 10 → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MemL2On unitCube (section5Term I hΦ m κm (T (Nstar β))
        (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i t) :=
  fun i hi _ ht => memL2On_of_continuousOn_slice (h.term_continuous i hi) ht

/-- Every slot of the centered ten-term family is jointly continuous on `(0,1) × ℝ²`
(centering preserves joint continuity). -/
theorem BigBoundInputs.centeredTerm_continuous (h : BigBoundInputs I hΦ m κm κprev T θ₀ C) :
    ∀ i, i < 10 → ContinuousOn
      (fun p : ℝ × Vec 2 => section5CenteredTerm I hΦ m κm (T (Nstar β))
        (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
  intro i hi
  interval_cases i
  · exact h.term_continuous 0 (by norm_num)
  · exact h.term_continuous 1 (by norm_num)
  · exact h.term_continuous 2 (by norm_num)
  · exact continuousOn_centerCell (h.term_continuous 3 (by norm_num))
  · exact continuousOn_centerCell (h.term_continuous 4 (by norm_num))
  · exact h.term_continuous 5 (by norm_num)
  · exact h.term_continuous 6 (by norm_num)
  · exact h.term_continuous 7 (by norm_num)
  · exact continuousOn_centerCell (h.term_continuous 8 (by norm_num))
  · exact h.term_continuous 9 (by norm_num)

/-- The ten source-scale bounds for the *centered* family: the seven ungrouped slots by the
existing conditional `*_sourceScale` theorems, the three grouped slots directly by the
`*_centered_source` fields. -/
theorem BigBoundInputs.centeredTermScale (h : BigBoundInputs I hΦ m κm κprev T θ₀ C) :
    ∀ i, i < 10 →
      timeHMinusOneNorm (section5CenteredTerm I hΦ m κm (T (Nstar β))
        (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i) ≤
      ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀) := by
  intro i hi
  interval_cases i
  · exact timeHMinusOneNorm_cutoff1_sourceScale I hΦ m κm C (T (Nstar β)) θ₀
      (h.termL2 0 (by norm_num)) h.cutoff1_meanZero h.cutoff1_source
  · exact h.twistie1_hminus_source
  · exact timeHMinusOneNorm_twistie3_sourceScale I hΦ m κm C (T (Nstar β)) θ₀
      h.twistie3_flux_smooth h.twistie3_flux_periodic h.twistie3_source
  · exact h.twistie4_centered_source
  · exact h.twistie5_centered_source
  · exact timeHMinusOneNorm_normie1_sourceScale I hΦ m κm C (T (Nstar β)) θ₀
      h.normie1_flux_smooth h.normie1_flux_periodic h.normie1_source
  · exact timeHMinusOneNorm_normie2_sourceScale I hΦ m κm C (T (Nstar β)) θ₀
      h.normie2_flux_smooth h.normie2_flux_periodic h.normie2_source
  · exact h.tiny_hminus_source
  · exact h.normie3_centered_source
  · exact timeHMinusOneNorm_R46_sourceScale I hΦ m κm C (T (Nstar β)) θ₀
      h.R46_flux_smooth h.R46_flux_periodic h.R46_source

/-- The residual time norm is at most ten times the common source scale.  The residual
equals the ten-term sum, which on `(0,1)` equals the centered ten-term sum (`group_meanZero`);
triangle inequality over the centered slots. -/
theorem BigBoundInputs.residual_le (h : BigBoundInputs I hΦ m κm κprev T θ₀ C) :
    timeHMinusOneNorm
        (fun t x => advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x) ≤
      ∑ _i ∈ Finset.range 10, ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀) := by
  have hEq : timeHMinusOneNorm
      (fun t x => advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x) =
        timeHMinusOneNorm (fun t x => ∑ i ∈ Finset.range 10,
          section5CenteredTerm I hΦ m κm (T (Nstar β))
            (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i t x) := by
    unfold timeHMinusOneNorm
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hfun : (fun x => advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x) =
        fun x => ∑ i ∈ Finset.range 10, section5CenteredTerm I hΦ m κm (T (Nstar β))
          (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i t x := by
      funext x
      rw [h.residual t ht x, sum_section5CenteredTerm_eq I hΦ m κm (T (Nstar β))
        (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) t
        (fun i hi => h.termL2 i hi t ht) (h.group_meanZero t ht) x]
      exact (congrFun (congrFun (section5Prefix_ten_eq_terms I hΦ m κm (T (Nstar β))
        (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T)) t) x).symm
    change hMinusOneNorm (fun x => advDiffOp (streamVel (Φ m)) κm
        (I.ansatz hΦ m κm (T (Nstar β))) t x) ^ 2 = _
    rw [hfun]
  rw [hEq]
  exact (timeHMinusOneNorm_sum_range_le (by norm_num) h.centeredTerm_continuous).trans
    (Finset.sum_le_sum fun i hi => h.centeredTermScale i (Finset.mem_range.mp hi))

end Inputs

/-! ### The big-bound estimate wiring theorem -/

/-- **Family contract for big-bound estimate** (`IndyStepDownV2Inputs.bigbound`): constants `C₁`
    (Λ-threshold) and
`C₂` (common source constant) chosen before `I`, then `BigBoundInputs` on the big-bound premise
    block
`OnA7Instances`.  Each field of `BigBoundInputs` is produced separately as its `*Contract`. -/
def BigBoundFamilyContract (β C₀ : ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
    BigBoundInputs I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T θ₀ C₂)

/-- **Big-bound estimate wiring.**  If, for every admissible instance with `C₁ ≤ Λ`, the explicit
`BigBoundInputs` (the remaining §3/§4/§5 statements) hold with a constant `C₂`, then the
Big-bound estimate proposition `BigBoundStatement β C₀` holds with `C = max C₁ (10 C₂)`. -/
theorem bigbound_of_inputs (β C₀ : ℝ)
    (hin : BigBoundFamilyContract β C₀) :
    BigBoundStatement β C₀ := by
  obtain ⟨C₁, C₂, h⟩ := hin
  refine ⟨max C₁ (10 * C₂), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hcl hT
  have hinp := h I hz hx hh (le_trans (le_max_left _ _) hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hθ
    hper hmean hana m hm hmM θprev T hcl hT
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hepos : ∀ n : ℕ, 0 < epsilon β I.Λ n := fun n =>
    Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos (hepos M) _))
      (Set.mem_Icc.mp hperm).1
  have hκm : 0 < I.kappaSeq κ M m := LeftToShow.kappaSeq_pos I hκpos M m
  have hres := hinp.residual_le
  set κm := I.kappaSeq κ M m with hκm_def
  set c : ℝ := epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (hepos _).le _) (Real.sqrt_nonneg _)
  have hscale : section5SourceScale β I.Λ m κm C₂ θ₀ = (C₂ * c) * Real.sqrt κm := by
    unfold section5SourceScale
    rw [hc]
    ring
  change ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) *
      timeHMinusOneNorm
        (fun t x => advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x) ≤ _
  calc ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) *
        timeHMinusOneNorm
          (fun t x => advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x)
      ≤ ENNReal.ofReal (κm ^ (-(1 / 2 : ℝ))) *
          ∑ _i ∈ Finset.range 10, ENNReal.ofReal (section5SourceScale β I.Λ m κm C₂ θ₀) := by
        gcongr
    _ = ENNReal.ofReal (10 * (C₂ * c)) := by
        rw [hscale]
        exact ofReal_rpow_neg_half_mul_sum_ten hκm _
    _ ≤ ENNReal.ofReal (max C₁ (10 * C₂) * c) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hc0
    _ = _ := by rw [hc, mul_assoc]

end AVenhance.Infra.Section5.Integration
end
