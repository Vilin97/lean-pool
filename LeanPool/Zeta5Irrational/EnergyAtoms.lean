/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Constants
public import LeanPool.Zeta5Irrational.ArcsineAtoms
public import LeanPool.Zeta5Irrational.EnergyLimit
public import LeanPool.Zeta5Irrational.Measure
import LeanPool.Zeta5Irrational.CircleAtoms
import LeanPool.Zeta5Irrational.Potential
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The atoms of the configuration energy

For a configuration `t : Fin h → ℝ` and a radius `ε > 0`, the atoms are the circles of radius
`ε` around the `t i` (weights `1/K`) and the sixteen arcsine curves (weights `-c_j`).
This file verifies the hypotheses of `energy_log_nonpos` for these atoms.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

/-- Reindexing `∑_{j ∈ Icc 1 m} f j = ∑_{j < m} f (j + 1)`. -/
lemma sum_Icc_eq_sum_range' (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ j ∈ Finset.range m, f (j + 1) := by
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x;
    simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

/-- Midpoints and half-lengths of the intervals of Table 1. -/
@[expose] noncomputable def mρ (j : ℕ) : ℝ :=
  (aρ j + bρ j) / 2

/-- Half-width of the support of the `j`th arcsine component. -/
@[expose] noncomputable def rρ (j : ℕ) : ℝ :=
  (bρ j - aρ j) / 2

lemma rρ_pos (j : Fin 16) : 0 < rρ (j + 1) := by
  have := aρ_lt_bρ (j + 1) (by simp only [Finset.mem_Icc]; omega)
  unfold rρ; linarith

lemma rρ_ge (j : Fin 16) : 1 / 450 ≤ rρ (j + 1) := by
  unfold rρ;
  fin_cases j <;> norm_num [aρ, bρ, table1]

lemma mρ_bounds (j : Fin 16) : 0 < mρ (j + 1) ∧ mρ (j + 1) < 2 := by
  unfold mρ;
  fin_cases j <;> norm_num [aρ, bρ, table1]

lemma rρ_le (j : Fin 16) : rρ (j + 1) ≤ 1 := by
  unfold rρ;
  fin_cases j <;> norm_num [aρ, bρ, table1]

/-- The index type of the atoms. -/
abbrev Idx (h : ℕ) :=
  Fin h ⊕ Fin 16

/-- The weights. -/
@[expose] noncomputable def atomS (h : ℕ) (K : ℝ) : Idx h → ℝ
  | Sum.inl _ => 1 / K
  | Sum.inr j => -cρ (j + 1)

/-- The curves. -/
@[expose] noncomputable def atomγ {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) : Idx h → ℝ → ℂ
  | Sum.inl i => circleMap (t i) ε
  | Sum.inr j => arcCurve (mρ (j + 1)) (rρ (j + 1))

lemma continuous_atomγ {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k : Idx h) : Continuous (atomγ t ε k) := by
  cases k with
  | inl i => exact continuous_circleMap _ _
  | inr j => exact continuous_arcCurve _ _

lemma norm_atomγ_le {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k : Idx h) (θ : ℝ) :
    ‖atomγ t ε k θ‖ ≤ (∑ i, |t i|) + |ε| + 3 := by
  cases k with
  | inl i =>
    simp only [atomγ, circleMap]
    calc
      ‖(t i : ℂ) + ε * Complex.exp (θ * Complex.I)‖ ≤
          ‖(t i : ℂ)‖ + ‖(ε : ℂ) * Complex.exp (θ * Complex.I)‖ :=
        norm_add_le _ _
      _ = |t i| + |ε| := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (∑ i, |t i|) + |ε| + 3 := by
        have : |t i| ≤ ∑ i, |t i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (t i)) (Finset.mem_univ i)
        linarith
  | inr j =>
    simp only [atomγ]
    refine (norm_arcCurve_le _ _ _).trans ?_
    have h1 := mρ_bounds j
    have h2 := rρ_pos j
    have h3 := rρ_le j
    rw [abs_of_pos h1.1, abs_of_pos h2]
    have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [abs_nonneg ε]

/-- Zero total mass when `h = 37 n` and `K = 40 n`. -/
lemma atomS_mass (n : ℕ) (hn : 0 < n) : ∑ k, atomS (37 * n) (Kr n) k = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [atomS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_neg_distrib]
  have h1 : ∑ j : Fin 16, cρ (j + 1) = lam := by
    rw [← Sρ_sixteen, Sρ, sum_Icc_eq_sum_range', Fin.sum_univ_eq_sum_range (fun j => cρ (j + 1))]
  rw [h1]
  simp only [Kr, lam]
  push_cast
  field_simp
  ring

/-! ### Pointwise integrability and bounds for the atoms -/

/-- `∫₀^{2π} |log ‖z - circleMap c ε φ‖| ≤ 2π |log ε| + 4π log (1 + ‖(z - c)/ε‖)`. -/
lemma circle_point_abs_log_le (z c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ φ in (0 : ℝ)..2 * π, |Real.log ‖z - circleMap c ε φ‖| ≤
      2 * π * |Real.log ε| + 4 * π * Real.log (1 + ‖(z - c) / ε‖) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hfac : ∀ φ, ‖z - circleMap c ε φ‖ = ε * ‖circleMap 0 1 φ - (z - c) / ε‖ := by
    intro φ
    have e : z - circleMap c ε φ = -((ε : ℂ) * (circleMap 0 1 φ - (z - c) / ε)) := by
      simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]; field_simp; ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hpt :
    ∀ φ,
      |Real.log ‖z - circleMap c ε φ‖| ≤
        |Real.log ε| + |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖| := by
    intro φ
    rw [hfac]
    by_cases h0 : ‖circleMap 0 1 φ - (z - c) / ε‖ = 0
    · rw [h0, mul_zero, Real.log_zero, abs_zero]; positivity
    · rw [Real.log_mul hε.ne' h0]; exact abs_add_le _ _
  have hi : IntervalIntegrable (fun φ => |Real.log ‖z - circleMap c ε φ‖|) volume 0 (2 * π) := by
    have := (circle_log_integrable c z ε).abs
    refine this.congr ?_
    intro φ _; simp only [norm_sub_rev]
  calc
    ∫ φ in (0 : ℝ)..2 * π, |Real.log ‖z - circleMap c ε φ‖| ≤
        ∫ φ in (0 : ℝ)..2 * π, (|Real.log ε| + |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖|) :=
      integral_mono_on (by positivity) hi
        (intervalIntegrable_const.add (circle_log_integrable 0 _ 1).abs) (fun φ _ => hpt φ)
    _ =
        2 * π * |Real.log ε| +
          ∫ φ in (0 : ℝ)..2 * π, |Real.log ‖circleMap 0 1 φ - (z - c) / ε‖| := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
          (circle_log_integrable 0 _ 1).abs,
        intervalIntegral.integral_const]
      simp
    _ ≤ _ := by linarith [abs_log_circle_integral_le ((z - c) / ε)]

/-- Integrability of `φ ↦ log ‖z - atomγ k φ‖`. -/
lemma atom_point_integrable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (_hε : 0 < ε) (k : Idx h) (z : ℂ) :
    IntervalIntegrable (fun φ => Real.log ‖z - atomγ t ε k φ‖) volume 0 (2 * π) := by
  cases k with
  | inl i =>
    have := circle_log_integrable (t i) z ε
    refine this.congr ?_
    intro φ _; simp only [atomγ, norm_sub_rev]
  | inr j => exact arc_log_integrable (rρ_pos j)

lemma norm_root_le {ζ sq : ℂ} (hsq : sq ^ 2 = ζ ^ 2 - 1) : ‖sq‖ ≤ ‖ζ‖ + 1 := by
  have h1 : ‖sq‖ ^ 2 = ‖ζ ^ 2 - 1‖ := by rw [← norm_pow, hsq]
  have h2 : ‖ζ ^ 2 - 1‖ ≤ ‖ζ‖ ^ 2 + 1 := by
    calc
      ‖ζ ^ 2 - 1‖ ≤ ‖ζ ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖ζ‖ ^ 2 + 1 := by rw [norm_pow, norm_one]
  nlinarith [norm_nonneg sq, norm_nonneg ζ]

/-- A uniform bound for `∫₀^{2π} |log ‖z - atomγ k φ‖| dφ` over `‖z‖ ≤ R`. -/
lemma atom_point_abs_log_le {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k : Idx h) {R : ℝ}
    (_hR : 0 ≤ R) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ R → ∫ φ in (0 : ℝ)..2 * π, |Real.log ‖z - atomγ t ε k φ‖| ≤ C := by
  cases k with
  | inl i =>
    refine ⟨2 * π * |Real.log ε| + 4 * π * ((R + |t i|) / ε), fun z hz => ?_⟩
    refine (circle_point_abs_log_le z (t i) hε).trans ?_
    have h1 : Real.log (1 + ‖(z - t i) / ε‖) ≤ ‖(z - t i) / ε‖ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - t i) / ε‖ by positivity)
      linarith
    have h2 : ‖(z - t i) / ε‖ ≤ (R + |t i|) / ε := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      apply div_le_div_of_nonneg_right _ hε.le
      calc
        ‖z - t i‖ ≤ ‖z‖ + ‖(t i : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + |t i| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    nlinarith [Real.pi_pos]
  | inr j =>
    set m := mρ (j + 1)
    set r := rρ (j + 1)
    have hr := rρ_pos j
    refine ⟨2 * π * |Real.log (r / 2)| + 8 * π * (2 * ((R + |m|) / r) + 1), fun z hz => ?_⟩
    set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
    have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
    refine (arc_abs_log_integral_le hr hsq).trans ?_
    have hζ : ‖(z - m) / r‖ ≤ (R + |m|) / r := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      apply div_le_div_of_nonneg_right _ hr.le
      calc
        ‖z - m‖ ≤ ‖z‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hs := norm_root_le hsq
    have hq1 : Real.log (1 + ‖(z - m) / r + sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r + sq‖ by positivity)
      have := norm_add_le ((z - m) / r) sq
      linarith
    have hq2 : Real.log (1 + ‖(z - m) / r - sq‖) ≤ 2 * ((R + |m|) / r) + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖(z - m) / r - sq‖ by positivity)
      have := norm_sub_le ((z - m) / r) sq
      linarith
    nlinarith [Real.pi_pos]

/-! ### The hypotheses of `energy_log_nonpos` -/

lemma measurable_atom_kernel {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k l : Idx h) :
    Measurable fun p : ℝ × ℝ => Real.log ‖atomγ t ε k p.1 - atomγ t ε l p.2‖ := by
  apply Real.measurable_log.comp
  exact
    (continuous_norm.comp
        (((continuous_atomγ t ε k).comp continuous_fst).sub
          ((continuous_atomγ t ε l).comp continuous_snd))).measurable

/-- Torus integrability of the logarithmic kernel for each pair of atoms. -/
lemma atom_pair_integrable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖atomγ t ε k p.1 - atomγ t ε l p.2‖)
      (μcirc.prod μcirc) := by
  have hR0 : 0 ≤ (∑ i, |t i|) + |ε| + 3 := by
    have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [abs_nonneg ε]
  obtain ⟨C, hC⟩ := atom_point_abs_log_le t hε l hR0
  have hmeas := (measurable_atom_kernel t ε k l).aestronglyMeasurable (μ := μcirc.prod μcirc)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with θ
    have := atom_point_integrable t hε l (atomγ t ε k θ)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp this
  · refine Integrable.mono' (integrable_const C) hmeas.norm.integral_prod_right' ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have := hC (atomγ t ε k θ) (norm_atomγ_le t ε k θ)
    rw [intervalIntegral.integral_of_le (by positivity)] at this
    simpa [Real.norm_eq_abs] using this

/-- Point preimages under the atoms are countable. -/
lemma atom_preimage_countable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (l : Idx h) (c : ℂ) :
    {φ : ℝ | c = atomγ t ε l φ}.Countable := by
  cases l with
  | inl i =>
    refine (circleMap_preimage_countable (t i) hε.ne' c).mono ?_
    intro φ hφ
    simp only [Set.mem_ofPred_eq, atomγ] at hφ
    simp [hφ]
  | inr j =>
    refine (cos_preimage_countable ((c.re - mρ (j + 1)) / rρ (j + 1))).mono ?_
    intro φ hφ
    simp only [Set.mem_ofPred_eq, atomγ, arcCurve] at hφ
    have hr := rρ_pos j
    have : c.re = mρ (j + 1) + rρ (j + 1) * Real.cos φ := by rw [hφ, Complex.ofReal_re]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]; field_simp; ring

/-- Almost every pair of parameters gives distinct points. -/
lemma atom_pair_ae_ne {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    ∀ᵐ p ∂(μcirc.prod μcirc), atomγ t ε k p.1 ≠ atomγ t ε l p.2 := by
  rw [ae_iff]
  simp only [not_not]
  have hS : MeasurableSet {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2} :=
    (isClosed_eq ((continuous_atomγ t ε k).comp continuous_fst)
        ((continuous_atomγ t ε l).comp continuous_snd)).measurableSet
  rw [Measure.prod_apply hS]
  have : ∀ θ, μcirc (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2}) = 0 := by
    intro θ
    have hc := (atom_preimage_countable t hε l (atomγ t ε k θ)).measure_zero (volume : Measure ℝ)
    refine le_antisymm ?_ bot_le
    calc
      μcirc (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2}) ≤
          volume (Prod.mk θ ⁻¹' {p : ℝ × ℝ | atomγ t ε k p.1 = atomγ t ε l p.2}) :=
        (Measure.le_iff'.mp Measure.restrict_le_self) _
      _ = volume {φ : ℝ | atomγ t ε k θ = atomγ t ε l φ} := rfl
      _ = 0 := hc
  simp only [this, lintegral_zero]

/-- Symmetry of the pair integrals of the logarithmic kernel. -/
lemma pairInt_log_symm {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) k l =
      pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) l k := by
  rw [pairInt_eq_prod _ _ _ _ (atom_pair_integrable t hε k l),
    pairInt_eq_prod _ _ _ _ (atom_pair_integrable t hε l k), ← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

/-- **Lemma 6.2 for the configuration atoms.** -/
theorem atom_energy_nonpos (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    energy (atomS (37 * n) (Kr n)) (atomγ t ε) (fun z w => Real.log ‖z - w‖) ≤ 0 :=
  energy_log_nonpos (continuous_atomγ t ε) (norm_atomγ_le t ε) (atomS_mass n hn)
    (atom_pair_integrable t hε) (atom_pair_ae_ne t hε)

end Zeta5Irrational
