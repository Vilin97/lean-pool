/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.CenteredTruncation

/-! # Symmetric -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- A symmetric variable keeps zero mean after absolute truncation. -/
theorem integral_absTruncation_eq_zero_of_identDistrib_neg
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {r : ℝ}
    (hX_symm : IdentDistrib X (fun ω => -X ω) μ μ) :
    μ[absTruncation X r] = 0 := by
  let φ : ℝ → ℝ := absTruncation (fun t : ℝ => t) r
  have hφ : Measurable φ :=
    absTruncation_measurable (X := fun t : ℝ => t) (r := r) measurable_id
  have htr : IdentDistrib (φ ∘ X) (φ ∘ fun ω => -X ω) μ μ :=
    hX_symm.comp hφ
  have hodd : ∀ x : ℝ, φ (-x) = -φ x := by
    intro x
    by_cases hx : r < |x|
    · simp [φ, hx, abs_neg]
    · simp [φ, hx, abs_neg]
  have hEq : ∫ ω, φ (X ω) ∂μ = -∫ ω, φ (X ω) ∂μ := by
    simpa [hodd, integral_neg, Function.comp] using htr.integral_eq
  have hzero : ∫ ω, φ (X ω) ∂μ = 0 :=
    CharZero.eq_neg_self_iff.mp hEq
  simpa [φ] using hzero

section

omit [MeasurableSpace Ω]

/-- If the absolute maximum of a finite family is below the truncation scale,
each truncated variable agrees with the original one. -/
theorem absTruncation_eq_self_of_sup'_abs_le
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {r : ℝ} {ω : Ω}
    (hω : s.sup' hs (fun i => |X i ω|) ≤ r) :
    ∀ i ∈ s, absTruncation (X i) r ω = X i ω := by
  intro i hi
  exact absTruncation_of_abs_le ((Finset.sup'_le_iff hs _).mp hω i hi)

/-- In the symmetric Rosenthal proof, the tail of the finite sum splits into the
tail of the finite maximum and the tail of the bounded truncation sum. -/
theorem absTailEvent_finsetSum_subset_sup'_abs_union_absTruncation
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {r t : ℝ} :
    absTailEvent (fun ω => ∑ i ∈ s, X i ω) t ⊆
      upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r ∪
        absTailEvent (fun ω => ∑ i ∈ s, absTruncation (X i) r ω) t := by
  intro ω hω
  by_cases hsup : r < s.sup' hs (fun i => |X i ω|)
  · exact Or.inl hsup
  · have hsup_le : s.sup' hs (fun i => |X i ω|) ≤ r := le_of_not_gt hsup
    have hω' : ω ∈ absTailEvent (fun ω => ∑ i ∈ s, absTruncation (X i) r ω) t := by
      have hω'' : t < |∑ i ∈ s, X i ω| := by
        simpa [absTailEvent] using hω
      have hsmall : ∀ i ∈ s, ¬ r < |X i ω| := by
        intro i hi
        exact not_lt_of_ge ((Finset.sup'_le_iff hs _).mp hsup_le i hi)
      have htail_zero : ∑ i ∈ s, (if r < |X i ω| then X i ω else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [hsmall i hi]
      rw [absTailEvent, upperTailEvent]
      simpa [absTruncation, absTailIndicator, Finset.sum_sub_distrib, htail_zero] using hω''
    exact Or.inr hω'

theorem abs_absTruncation_le_abs
    {X : Ω → ℝ} {r : ℝ} (ω : Ω) :
    |absTruncation X r ω| ≤ |X ω| := by
  by_cases hω : r < |X ω|
  · simp [absTruncation, absTailIndicator, hω]
  · simp [absTruncation, absTailIndicator, hω]

end

/-- Truncating a variable can only decrease its second moment. -/
theorem moment_absTruncation_two_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {r : ℝ}
    (hX_meas : Measurable X)
    (hX_sq_int : Integrable (fun ω => X ω ^ (2 : ℕ)) μ) :
    ProbabilityTheory.moment (absTruncation X r) 2 μ ≤ ProbabilityTheory.moment X 2 μ := by
  have htrunc_sq_meas : Measurable (fun ω => absTruncation X r ω ^ (2 : ℕ)) :=
    (absTruncation_measurable (X := X) (r := r) hX_meas).pow_const 2
  have htrunc_sq_int : Integrable (fun ω => absTruncation X r ω ^ (2 : ℕ)) μ := by
    refine Integrable.mono' hX_sq_int htrunc_sq_meas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with ω
    have hpow :
        |absTruncation X r ω| ^ (2 : ℕ) ≤ |X ω| ^ (2 : ℕ) :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_absTruncation_le_abs (X := X) (r := r) ω) 2
    simpa [Real.norm_eq_abs, sq_abs,
      abs_of_nonneg (show 0 ≤ absTruncation X r ω ^ (2 : ℕ) by positivity),
      abs_of_nonneg (show 0 ≤ X ω ^ (2 : ℕ) by positivity)] using hpow
  refine integral_mono_ae htrunc_sq_int hX_sq_int ?_
  filter_upwards with ω
  have hpow :
      |absTruncation X r ω| ^ (2 : ℕ) ≤ |X ω| ^ (2 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_absTruncation_le_abs (X := X) (r := r) ω) 2
  simpa [ProbabilityTheory.moment, sq_abs] using hpow

/-- Symmetric truncation tail bound: split off the event where the finite
maximum exceeds the truncation scale, and apply Bennett to the bounded
truncation sum. -/
theorem measureReal_absTailEvent_finsetSum_le_sup'_abs_add_bennett
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {r t : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_symm : ∀ i ∈ s, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hv_pos : 0 < ∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) t) ≤
      μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r) +
        2 * Real.exp
          (-
            (((∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ) /
                r ^ (2 : ℕ)) *
              bennettH
                (t * r /
                  (∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ)))) := by
  let Y : ι → Ω → ℝ := fun i => absTruncation (X i) r
  have hsubset :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) t ⊆
        upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r ∪
          absTailEvent (fun ω => ∑ i ∈ s, Y i ω) t := by
    simpa [Y] using
      (absTailEvent_finsetSum_subset_sup'_abs_union_absTruncation
        (X := X) (s := s) hs (r := r) (t := t))
  have h_indepY : iIndepFun Y μ := by
    let g : ι → ℝ → ℝ := fun _ x => absTruncation (fun t : ℝ => t) r x
    have hg : ∀ i, Measurable (g i) := by
      intro i
      exact absTruncation_measurable (X := fun t : ℝ => t) (r := r) measurable_id
    simpa [Y, g, Function.comp] using! h_indep.comp g hg
  have h_measY : ∀ i, Measurable (Y i) := by
    intro i
    exact absTruncation_measurable (X := X i) (r := r) (h_meas i)
  have h_meanY : ∀ i ∈ s, μ[Y i] = 0 := by
    intro i hi
    exact integral_absTruncation_eq_zero_of_identDistrib_neg
      (μ := μ) (X := X i) (r := r) (h_symm i hi)
  have h_bddY : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Y i ω| ≤ r := by
    intro i hi
    exact Filter.Eventually.of_forall fun ω =>
      abs_absTruncation_le (X := X i) (r := r) hr.le ω
  have htailY :=
    measureReal_absTailEvent_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) (y := r) (a := t)
      h_indepY h_measY hr hv_pos ht h_bddY h_meanY
  have htailY' :
      μ.real (absTailEvent (fun ω => ∑ i ∈ s, Y i ω) t) ≤
        2 * Real.exp
          (-
            (((∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ) /
                r ^ (2 : ℕ)) *
              bennettH
                (t * r /
                  (∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ)))) := by
    simpa [Y] using! htailY
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) t)
        ≤ μ.real
            (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r ∪
              absTailEvent (fun ω => ∑ i ∈ s, Y i ω) t) := by
              exact measureReal_mono hsubset
    _ ≤ μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r) +
          μ.real (absTailEvent (fun ω => ∑ i ∈ s, Y i ω) t) := by
            exact measureReal_union_le _ _
    _ ≤ μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r) +
          2 * Real.exp
            (-
              (((∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ) /
                  r ^ (2 : ℕ)) *
                bennettH
                  (t * r /
                    (∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ)))) := by
            exact add_le_add_right htailY' _
    _ = μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) r) +
          2 * Real.exp
            (-
              (((∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ) /
                  r ^ (2 : ℕ)) *
                bennettH
                  (t * r /
                    (∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ)))) := by
            rfl

theorem bennett_truncation_exponent_eq_beta
    {v r t : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) :
    ((v / r ^ (2 : ℕ)) * bennettH (t * r / v)) = (t / r) * bennettBeta (t * r / v) := by
  by_cases ht : t = 0
  · simp [ht, bennettH_zero, bennettBeta]
  · have hcoeff : v / r ^ (2 : ℕ) = (t / r) / (t * r / v) := by
      field_simp [hr, hv, ht]
    calc
      (v / r ^ (2 : ℕ)) * bennettH (t * r / v)
          = (((t / r) / (t * r / v)) * bennettH (t * r / v)) := by rw [hcoeff]
      _ = (t / r) * (bennettH (t * r / v) / (t * r / v)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ = (t / r) * bennettBeta (t * r / v) := by rw [bennettBeta]

/-- Moment-adapted truncation choice in the symmetric Rosenthal proof:
specializing the truncation scale to `r = t / p` converts the Bennett term to
the exact note-facing `p β(t² / (p σ²))` form. -/
theorem measureReal_absTailEvent_finsetSum_le_sup'_abs_add_bennettBeta_of_scale
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p t : ℝ}
    (hp : 1 ≤ p) (ht : 0 < t)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (h_symm : ∀ i ∈ s, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hv_pos :
      0 < ∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) (t / p) ω) 2 μ)
    (hSigma_pos : 0 < ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) t) ≤
      μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) (t / p)) +
        2 * Real.exp
          (-(p * bennettBeta
            (t ^ (2 : ℕ) / (p * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)))) := by
  let r : ℝ := t / p
  let v : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) r ω) 2 μ
  let sigmaSq : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr_pos : 0 < r := div_pos ht hp_pos
  have hv_le : v ≤ sigmaSq := by
    dsimp [v, sigmaSq]
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa [r] using! moment_absTruncation_two_le
      (μ := μ) (X := X i) (r := t / p) (h_meas i) (h_sq_int i hi)
  have hmaster :=
    measureReal_absTailEvent_finsetSum_le_sup'_abs_add_bennett
      (μ := μ) (X := X) (s := s) hs hr_pos (le_of_lt ht)
      h_indep h_meas h_symm (by simpa [v, r] using hv_pos)
  have harg_le : t * r / sigmaSq ≤ t * r / v := by
    have htr_nonneg : 0 ≤ t * r := mul_nonneg ht.le hr_pos.le
    have hinv : sigmaSq⁻¹ ≤ v⁻¹ := by
      simpa [one_div] using! one_div_le_one_div_of_le hv_pos hv_le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv htr_nonneg
  have hleft_pos : 0 < t * r / sigmaSq := by
    exact div_pos (mul_pos ht hr_pos) hSigma_pos
  have hright_pos : 0 < t * r / v := by
    exact div_pos (mul_pos ht hr_pos) hv_pos
  have hbeta_mono : bennettBeta (t * r / sigmaSq) ≤ bennettBeta (t * r / v) :=
    monotoneOn_bennettBeta hleft_pos hright_pos harg_le
  have hscale_mul : p * r = t := by
    dsimp [r]
    field_simp [hp_pos.ne']
  have hscale : t / r = p := by
    rw [div_eq_iff hr_pos.ne']
    simpa [mul_comm] using hscale_mul.symm
  have harg_eq : t * r / sigmaSq = t ^ (2 : ℕ) / (p * sigmaSq) := by
    dsimp [r]
    field_simp [hp_pos.ne', hSigma_pos.ne']
  have hbeta_mono' :
      bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)) ≤ bennettBeta (t * r / v) := by
    calc
      bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))
          = bennettBeta (t * r / sigmaSq) := by rw [harg_eq]
      _ ≤ bennettBeta (t * r / v) := hbeta_mono
  have hexponent :
      -(((v / r ^ (2 : ℕ)) * bennettH (t * r / v))) ≤
        -(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))) := by
    rw [bennett_truncation_exponent_eq_beta (hr := hr_pos.ne') (hv := (by simpa [v] using hv_pos.ne'))]
    rw [hscale]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hbeta_mono' hp_pos.le)
  refine hmaster.trans ?_
  gcongr

/-- Vanishing second moment forces a real random variable to vanish almost
everywhere. This is the degenerate case used in the Rosenthal proof when the
variance proxy is zero. -/
theorem ae_eq_zero_of_moment_two_eq_zero
    {X : Ω → ℝ}
    (hX_sq_int : Integrable (fun ω => X ω ^ (2 : ℕ)) μ)
    (hX_moment_zero : ProbabilityTheory.moment X 2 μ = 0) :
    X =ᵐ[μ] 0 := by
  have hsq_nonneg : 0 ≤ᵐ[μ] fun ω => X ω ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have hsq_zero : (fun ω => X ω ^ (2 : ℕ)) =ᵐ[μ] 0 := by
    refine (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hsq_nonneg hX_sq_int).1 ?_
    simpa [ProbabilityTheory.moment] using hX_moment_zero
  filter_upwards [hsq_zero] with ω hω
  rw [pow_two] at hω
  exact mul_self_eq_zero.mp hω

/-- A finite sum of almost-everywhere vanishing functions vanishes almost
everywhere. -/
theorem ae_eq_zero_finsetSum_of_forall
    {Y : ι → Ω → ℝ} {s : Finset ι}
    (hY_zero : ∀ i ∈ s, Y i =ᵐ[μ] 0) :
    (fun ω => ∑ i ∈ s, Y i ω) =ᵐ[μ] 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall (fun _ => by simp)
  | @insert a s ha ih =>
      have hae : Y a =ᵐ[μ] 0 := hY_zero a (by simp)
      have hrest : (fun ω => ∑ i ∈ s, Y i ω) =ᵐ[μ] 0 := by
        apply ih
        intro i hi
        exact hY_zero i (by simp [hi])
      simpa [Finset.sum_insert, ha] using! hae.add hrest

/-- Symmetric Rosenthal bound in `lintegral` form. This is the exact
tail-integration endpoint coming from the Chapter 4 Bennett-plus-maximum split. -/
theorem lintegral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (h_symm : ∀ i ∈ s, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ p) ∂μ ≤
      ENNReal.ofReal (p ^ p) *
        ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ +
      ENNReal.ofReal
        (2 * (rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p) := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let sigmaSq : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hSigma_nonneg : 0 ≤ sigmaSq := by
    dsimp [sigmaSq]
    refine Finset.sum_nonneg ?_
    intro i hi
    simp [ProbabilityTheory.moment]
    positivity
  have hS_meas : Measurable S := by
    dsimp [S]
    refine Finset.measurable_sum s ?_
    intro i hi
    exact h_meas i
  have hLayerS :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := μ) (f := fun ω => |S ω|)
      (Filter.Eventually.of_forall fun ω => abs_nonneg (S ω))
      (continuous_abs.measurable.comp_aemeasurable hS_meas.aemeasurable) hp_pos
  by_cases hSigma_pos : 0 < sigmaSq
  · let kernel : ℝ → ℝ := fun t =>
      t ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))
    let A : ℝ → ENNReal := fun t =>
      μ {ω | t / p < M ω} * ENNReal.ofReal (t ^ (p - 1))
    let B : ℝ → ENNReal := fun t =>
      ENNReal.ofReal (2 * kernel t)
    have hB_aemeas :
        AEMeasurable B (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hB_int :
          Integrable (fun t => 2 * kernel t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
        simpa [kernel, IntegrableOn] using
          ((integrableOn_rosenthal_bennett_scaled_kernel (p := p) (sigmaSq := sigmaSq) hp hSigma_pos)).const_mul
            (2 : ℝ)
      exact measurable_id.ennreal_ofReal.comp_aemeasurable hB_int.aestronglyMeasurable.aemeasurable
    have hdom :
        ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          μ {ω | t < |S ω|} * ENNReal.ofReal (t ^ (p - 1)) ≤ A t + B t := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      let truncVar : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (fun ω => absTruncation (X i) (t / p) ω) 2 μ
      have htail_real :
          μ.real (absTailEvent S t) ≤
            μ.real (upperTailEvent M (t / p)) +
              2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) := by
        by_cases hTrunc_pos : 0 < truncVar
        · simpa [S, M, sigmaSq, truncVar] using
            measureReal_absTailEvent_finsetSum_le_sup'_abs_add_bennettBeta_of_scale
              (μ := μ) (X := X) (s := s) hs hp_one ht
              h_indep h_meas h_sq_int h_symm hTrunc_pos hSigma_pos
        · let T : Ω → ℝ := fun ω => ∑ i ∈ s, absTruncation (X i) (t / p) ω
          have htrunc_nonneg : 0 ≤ truncVar := by
            dsimp [truncVar]
            refine Finset.sum_nonneg ?_
            intro i hi
            simp [ProbabilityTheory.moment]
            positivity
          have htrunc_zero : truncVar = 0 := le_antisymm (le_of_not_gt hTrunc_pos) htrunc_nonneg
          have htrunc_term_zero :
              ∀ i ∈ s,
                ProbabilityTheory.moment (fun ω => absTruncation (X i) (t / p) ω) 2 μ = 0 := by
            intro i hi
            have hnonneg_terms :
                ∀ j ∈ s, 0 ≤ ProbabilityTheory.moment (fun ω => absTruncation (X j) (t / p) ω) 2 μ := by
              intro j hj
              simp [ProbabilityTheory.moment]
              positivity
            exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg_terms).1
              (by simpa [truncVar] using htrunc_zero) i hi
          have htrunc_sq_int :
              ∀ i ∈ s, Integrable (fun ω => absTruncation (X i) (t / p) ω ^ (2 : ℕ)) μ := by
            intro i hi
            refine Integrable.mono' (h_sq_int i hi)
              ((absTruncation_measurable (X := X i) (r := t / p) (h_meas i)).pow_const 2).aemeasurable.aestronglyMeasurable ?_
            filter_upwards with ω
            have hpow :
                |absTruncation (X i) (t / p) ω| ^ (2 : ℕ) ≤ |X i ω| ^ (2 : ℕ) :=
              pow_le_pow_left₀ (abs_nonneg _)
                (abs_absTruncation_le_abs (X := X i) (r := t / p) ω) 2
            simpa [Real.norm_eq_abs, sq_abs,
              abs_of_nonneg (show 0 ≤ absTruncation (X i) (t / p) ω ^ (2 : ℕ) by positivity),
              abs_of_nonneg (show 0 ≤ X i ω ^ (2 : ℕ) by positivity)] using hpow
          have hT_zero_ae : T =ᵐ[μ] 0 := by
            dsimp [T]
            apply ae_eq_zero_finsetSum_of_forall
            intro i hi
            exact ae_eq_zero_of_moment_two_eq_zero (μ := μ)
              (htrunc_sq_int i hi) (htrunc_term_zero i hi)
          have hT_meas : Measurable T := by
            dsimp [T]
            refine Finset.measurable_sum s ?_
            intro i hi
            exact absTruncation_measurable (X := X i) (r := t / p) (h_meas i)
          have htail_T_zero : μ.real (absTailEvent T t) = 0 := by
            have hsubset_nonzero : absTailEvent T t ⊆ {ω | T ω ≠ 0} := by
              intro ω hω hzero
              have : ¬ t < |T ω| := by simpa [hzero] using not_lt.mpr ht.le
              exact this hω
            have hnonzero_null : μ {ω | T ω ≠ 0} = 0 := by
              simpa [ae_iff] using (ae_iff.mp hT_zero_ae)
            have hnonzero_real : μ.real {ω | T ω ≠ 0} = 0 := by
              exact (measureReal_eq_zero_iff).2 hnonzero_null
            exact measureReal_mono_null hsubset_nonzero hnonzero_real
          have hsubset :
              absTailEvent S t ⊆
                upperTailEvent M (t / p) ∪ absTailEvent T t := by
            simpa [S, M, T] using
              (absTailEvent_finsetSum_subset_sup'_abs_union_absTruncation
                (X := X) (s := s) hs (r := t / p) (t := t))
          calc
            μ.real (absTailEvent S t)
                ≤ μ.real (upperTailEvent M (t / p) ∪ absTailEvent T t) := by
                    exact measureReal_mono hsubset
            _ ≤ μ.real (upperTailEvent M (t / p)) + μ.real (absTailEvent T t) := by
                  exact measureReal_union_le _ _
            _ = μ.real (upperTailEvent M (t / p)) := by rw [htail_T_zero, add_zero]
            _ ≤ μ.real (upperTailEvent M (t / p)) +
                  2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) := by
                  have hconst_nonneg :
                      0 ≤ 2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) := by
                    positivity
                  linarith
      have hset_abs : {ω | t < |S ω|} = absTailEvent S t := by
        ext ω
        simp [S, absTailEvent]
      have hset_max : {ω | t / p < M ω} = upperTailEvent M (t / p) := by
        ext ω
        simp [M, upperTailEvent]
      have htail :
          μ {ω | t < |S ω|} ≤
            μ {ω | t / p < M ω} +
              ENNReal.ofReal (2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))) := by
        calc
          μ {ω | t < |S ω|}
              = ENNReal.ofReal (μ.real (absTailEvent S t)) := by
                  rw [hset_abs]
                  simp [Measure.real, (measure_lt_top μ (absTailEvent S t)).ne]
          _ ≤ ENNReal.ofReal
                (μ.real (upperTailEvent M (t / p)) +
                  2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))) := by
                  exact ENNReal.ofReal_le_ofReal (by simpa [sigmaSq] using htail_real)
          _ = ENNReal.ofReal (μ.real (upperTailEvent M (t / p))) +
                ENNReal.ofReal (2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))) := by
                  rw [ENNReal.ofReal_add]
                  · exact MeasureTheory.measureReal_nonneg
                  · positivity
          _ = μ {ω | t / p < M ω} +
                ENNReal.ofReal (2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))) := by
                  rw [hset_max]
                  simp [Measure.real, (measure_lt_top μ (upperTailEvent M (t / p))).ne]
      have hexp_nonneg :
          0 ≤ 2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) := by
        positivity
      have htpow_nonneg : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht.le _
      calc
        μ {ω | t < |S ω|} * ENNReal.ofReal (t ^ (p - 1))
            ≤ (μ {ω | t / p < M ω} +
                  ENNReal.ofReal
                    (2 * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))))) *
                ENNReal.ofReal (t ^ (p - 1)) := by
                  exact mul_le_mul_of_nonneg_right htail (by positivity)
        _ = A t + B t := by
              dsimp [A, B]
              rw [add_mul, ← ENNReal.ofReal_mul hexp_nonneg]
              congr 1
              dsimp [kernel]
              ring_nf
    have hmono :
        ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < |S ω|} * ENNReal.ofReal (t ^ (p - 1)) ≤
          ∫⁻ t in Set.Ioi (0 : ℝ), A t + B t := by
      exact lintegral_mono_ae hdom
    have hB_bound :
        ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), B t ≤
          ENNReal.ofReal
            (2 * (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p) := by
      have hB_int :
          Integrable (fun t => 2 * kernel t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
        simpa [kernel, IntegrableOn] using
          ((integrableOn_rosenthal_bennett_scaled_kernel (p := p) (sigmaSq := sigmaSq) hp hSigma_pos)).const_mul
            (2 : ℝ)
      have hB_nonneg :
          0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t => 2 * kernel t := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have hpow_nonneg : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht.le _
        have hexp_nonneg :
            0 ≤ Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) := by
          positivity
        dsimp [kernel]
        nlinarith
      have hB_lintegral :
          ∫⁻ t in Set.Ioi (0 : ℝ), B t =
            ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), 2 * kernel t) := by
        dsimp [B]
        symm
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := volume.restrict (Set.Ioi (0 : ℝ))) hB_int hB_nonneg)
      have hB_integral_nonneg : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), 2 * kernel t := by
        exact integral_nonneg_of_ae hB_nonneg
      calc
        ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), B t
            = ENNReal.ofReal p * ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), 2 * kernel t) := by
                rw [hB_lintegral]
        _ = ENNReal.ofReal (p * ∫ t in Set.Ioi (0 : ℝ), 2 * kernel t) := by
              rw [← ENNReal.ofReal_mul (show 0 ≤ p by linarith)]
        _ = ENNReal.ofReal (2 * (p * ∫ t in Set.Ioi (0 : ℝ), kernel t)) := by
              congr 1
              rw [integral_const_mul]
              ring
        _ ≤ ENNReal.ofReal
              (2 * (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hscaled :=
                rosenthal_bennett_scaled_integral_le (p := p) (sigmaSq := sigmaSq) hp hSigma_pos
              linarith
    calc
      ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ p) ∂μ
          = ENNReal.ofReal p *
              ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < |S ω|} * ENNReal.ofReal (t ^ (p - 1)) := by
                simpa [S] using hLayerS
      _ ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0 : ℝ), A t + B t) := by
            exact mul_le_mul_right hmono _
      _ = (ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), A t) +
            (ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), B t) := by
            rw [lintegral_add_right' (f := A) hB_aemeas, mul_add]
      _ = ENNReal.ofReal (p ^ p) *
            ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ +
            (ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), B t) := by
            have hA :
                ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), A t =
                  ENNReal.ofReal (p ^ p) *
                    ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ := by
              dsimp [A, M]
              simpa using
                (lintegral_rpow_sup'_abs_eq_scaled_tail
                  (μ := μ) (X := X) (s := s) hs hp_pos h_meas)
            simp [hA]
      _ ≤ ENNReal.ofReal (p ^ p) *
            ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ +
            ENNReal.ofReal
              (2 * (rosenthalBennettIntegralConst *
                (Real.sqrt p * Real.sqrt sigmaSq)) ^ p) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hB_bound
                (ENNReal.ofReal (p ^ p) *
                  ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ)
  · have hSigma_zero : sigmaSq = 0 := by
      exact le_antisymm (le_of_not_gt hSigma_pos) hSigma_nonneg
    have hmom_zero : ∀ i ∈ s, ProbabilityTheory.moment (X i) 2 μ = 0 := by
      intro i hi
      have hnonneg_terms : ∀ j ∈ s, 0 ≤ ProbabilityTheory.moment (X j) 2 μ := by
        intro j hj
        simp [ProbabilityTheory.moment]
        positivity
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg_terms).1 (by simpa [sigmaSq] using hSigma_zero) i hi
    have hsum_zero_ae : S =ᵐ[μ] 0 := by
      dsimp [S]
      apply ae_eq_zero_finsetSum_of_forall
      intro i hi
      exact ae_eq_zero_of_moment_two_eq_zero (μ := μ) (h_sq_int i hi) (hmom_zero i hi)
    calc
      ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ p) ∂μ
          = 0 := by
              calc
                ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ p) ∂μ
                    = ∫⁻ ω, (0 : ENNReal) ∂μ := by
                        refine lintegral_congr_ae ?_
                        filter_upwards [hsum_zero_ae] with ω hω
                        have hsum : ∑ i ∈ s, X i ω = 0 := by
                          simpa [S] using hω
                        rw [hsum]
                        simp [hp_pos.ne']
                _ = 0 := by simp
      _ ≤ ENNReal.ofReal (p ^ p) *
            ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ +
          ENNReal.ofReal
            (2 * (rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt sigmaSq)) ^ p) := by
            positivity

/-- Integrability consequence of the symmetric Rosenthal `lintegral` bound. -/
theorem integrable_abs_finsetSum_rpow_of_identDistrib_neg
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (h_symm : ∀ i ∈ s, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hmax_int :
      Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  have hlin :=
    lintegral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int h_symm
  have hS_meas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum s fun i _ => h_meas i
  have hSpow_nonneg : 0 ≤ᵐ[μ] fun ω => |S ω| ^ p := by
    exact Filter.Eventually.of_forall fun ω => by positivity
  have hSpow_aesm : AEStronglyMeasurable (fun ω => |S ω| ^ p) μ := by
    exact
      ((Real.continuous_rpow_const (show 0 ≤ p by linarith)).measurable.comp
        (continuous_abs.measurable.comp hS_meas)).aemeasurable.aestronglyMeasurable
  have hM_meas : Measurable M := by
    dsimp [M]
    convert
      (Finset.measurable_sup' (hs := hs) (f := fun i ω => |X i ω|) fun i _ =>
        continuous_abs.measurable.comp (h_meas i)) using 1
    ext ω
    simp
  have hM_nonneg : ∀ ω, 0 ≤ M ω := by
    intro ω
    have hnonneg : 0 ≤ |X hs.choose ω| := abs_nonneg _
    have hle : |X hs.choose ω| ≤ M ω := by
      show |X hs.choose ω| ≤ s.sup' hs (fun i => |X i ω|)
      exact Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec
    exact le_trans hnonneg hle
  have hMpow_nonneg : 0 ≤ᵐ[μ] fun ω => M ω ^ p := by
    exact Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hM_nonneg ω) _
  have hMpow_aesm : AEStronglyMeasurable (fun ω => M ω ^ p) μ := by
    exact
      ((Real.continuous_rpow_const (show 0 ≤ p by linarith)).measurable.comp
        hM_meas).aemeasurable.aestronglyMeasurable
  have hMpow_ne_top :
      (∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ) ≠ ⊤ := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (μ := μ) hMpow_aesm hMpow_nonneg).2 ?_
    simpa [M] using hmax_int
  have hbound_lt_top :
      ENNReal.ofReal (p ^ p) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ +
        ENNReal.ofReal
          (2 * (rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p) < ⊤ := by
    refine ENNReal.add_lt_top.mpr ?_
    constructor
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_ne le_top hMpow_ne_top)
    · exact ENNReal.ofReal_lt_top
  refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (μ := μ) hSpow_aesm hSpow_nonneg).1 ?_
  refine ne_of_lt (lt_of_le_of_lt ?_ hbound_lt_top)
  simpa [S, M] using hlin

/-- Real-integral version of the symmetric Rosenthal bound. -/
theorem integral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (h_symm : ∀ i ∈ s, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hmax_int :
      Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ ≤
      p ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
        2 * (rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let C : ℝ :=
    2 * (rosenthalBennettIntegralConst *
      (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p
  have hlin :=
    lintegral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int h_symm
  have hsum_int :
      Integrable (fun ω => |S ω| ^ p) μ := by
    simpa [S] using
      (integrable_abs_finsetSum_rpow_of_identDistrib_neg
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int h_symm hmax_int)
  have hS_meas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum s fun i _ => h_meas i
  have hSpow_nonneg : 0 ≤ᵐ[μ] fun ω => |S ω| ^ p := by
    exact Filter.Eventually.of_forall fun ω => by positivity
  have hSpow_aesm : AEStronglyMeasurable (fun ω => |S ω| ^ p) μ := by
    exact
      ((Real.continuous_rpow_const (show 0 ≤ p by linarith)).measurable.comp
        (continuous_abs.measurable.comp hS_meas)).aemeasurable.aestronglyMeasurable
  have hM_meas : Measurable M := by
    dsimp [M]
    convert
      (Finset.measurable_sup' (hs := hs) (f := fun i ω => |X i ω|) fun i _ =>
        continuous_abs.measurable.comp (h_meas i)) using 1
    ext ω
    simp
  have hM_nonneg : ∀ ω, 0 ≤ M ω := by
    intro ω
    have hnonneg : 0 ≤ |X hs.choose ω| := abs_nonneg _
    have hle : |X hs.choose ω| ≤ M ω := by
      show |X hs.choose ω| ≤ s.sup' hs (fun i => |X i ω|)
      exact Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec
    exact le_trans hnonneg hle
  have hMpow_nonneg : 0 ≤ᵐ[μ] fun ω => M ω ^ p := by
    exact Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hM_nonneg ω) _
  have hM_integral_nonneg : 0 ≤ ∫ ω, M ω ^ p ∂μ := by
    exact integral_nonneg_of_ae hMpow_nonneg
  have hM_lintegral :
      ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ = ENNReal.ofReal (∫ ω, M ω ^ p ∂μ) := by
    symm
    exact
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (by simpa [M] using hmax_int) hMpow_nonneg
  have hSigma_nonneg : 0 ≤ ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    simp [ProbabilityTheory.moment]
    positivity
  have hC_nonneg : 0 ≤ C := by
    have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst]
      positivity
    dsimp [C]
    refine mul_nonneg (by positivity : 0 ≤ (2 : ℝ))
      (Real.rpow_nonneg
        (mul_nonneg hRB_nonneg
          (mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg _))) _)
  have hlin' :
      ∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ ≤
        ENNReal.ofReal (p ^ p * ∫ ω, M ω ^ p ∂μ + C) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ
          ≤ ENNReal.ofReal (p ^ p) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ +
              ENNReal.ofReal C := by
                simpa [S, M, C] using hlin
      _ = ENNReal.ofReal (p ^ p * ∫ ω, M ω ^ p ∂μ) + ENNReal.ofReal C := by
            rw [hM_lintegral, ← ENNReal.ofReal_mul (Real.rpow_nonneg (show 0 ≤ p by linarith) _)]
      _ = ENNReal.ofReal (p ^ p * ∫ ω, M ω ^ p ∂μ + C) := by
            rw [← ENNReal.ofReal_add]
            · exact mul_nonneg (Real.rpow_nonneg (show 0 ≤ p by linarith) _) hM_integral_nonneg
            · exact hC_nonneg
  have hfin : (∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ) < ⊤ := by
    exact lt_of_le_of_lt hlin' ENNReal.ofReal_lt_top
  have hleft :
      ∫ ω, |S ω| ^ p ∂μ =
        (∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ).toReal := by
    rw [← ENNReal.toReal_ofReal (integral_nonneg_of_ae hSpow_nonneg)]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := μ) hsum_int hSpow_nonneg]
  have htoReal :
      (∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ).toReal ≤
        (ENNReal.ofReal (p ^ p * ∫ ω, M ω ^ p ∂μ + C)).toReal :=
    (ENNReal.toReal_le_toReal hfin.ne ENNReal.ofReal_ne_top).2 hlin'
  have hrhs_nonneg : 0 ≤ p ^ p * ∫ ω, M ω ^ p ∂μ + C := by
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg (show 0 ≤ p by linarith) _) hM_integral_nonneg)
      hC_nonneg
  calc
    ∫ ω, |S ω| ^ p ∂μ = (∫⁻ ω, ENNReal.ofReal (|S ω| ^ p) ∂μ).toReal := hleft
    _ ≤ (ENNReal.ofReal (p ^ p * ∫ ω, M ω ^ p ∂μ + C)).toReal := htoReal
    _ = p ^ p * ∫ ω, M ω ^ p ∂μ + C := by
          rw [ENNReal.toReal_ofReal hrhs_nonneg]


end
end IndependentSums
end Homogenization
