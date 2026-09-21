/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadTailUnion

/-! # Minimal Scale Tail -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Quantitative minimal scale from bad-tail events

This file contains the abstract minimal-scale construction used by
Theorem `t.homogenization.quenched`.  The construction is paired with a
tail-event inclusion, so the stochastic integrability of the scale is proved
from quantitative bounds on `badTailEvent`.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Above-scale good event for an abstract family of bad events. -/
def goodTailFrom (Bad : ℕ → Set Ω) (M : ℕ) (ω : Ω) : Prop :=
  ∀ K : ℕ, M ≤ K → ω ∉ Bad K

/-- The sample has a deterministic scale, not below `N0`, above which all bad
events are absent. -/
def hasGoodTailFrom (N0 : ℕ) (Bad : ℕ → Set Ω) (ω : Ω) : Prop :=
  ∃ M : ℕ, N0 ≤ M ∧ goodTailFrom Bad M ω

/-- The first scale not below `N0` above which all bad events are absent.
On the exceptional set where no such scale exists, the value is `N0`; the
pointwise estimate is only used on `hasGoodTailFrom`, while the tail estimate
below remains valid for the total function. -/
noncomputable def quenchedMinimalScaleIndex
    (N0 : ℕ) (Bad : ℕ → Set Ω) (ω : Ω) : ℕ :=
  by
    classical
    exact if h : hasGoodTailFrom N0 Bad ω then Nat.find h else N0

/-- The triadic random minimal scale associated with
`quenchedMinimalScaleIndex`. -/
noncomputable def quenchedMinimalScale
    (N0 : ℕ) (Bad : ℕ → Set Ω) (ω : Ω) : ℝ :=
  (3 : ℝ) ^ quenchedMinimalScaleIndex N0 Bad ω

omit [MeasurableSpace Ω] in
theorem one_le_quenchedMinimalScale
    (N0 : ℕ) (Bad : ℕ → Set Ω) (ω : Ω) :
    1 ≤ quenchedMinimalScale N0 Bad ω := by
  dsimp [quenchedMinimalScale]
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)

omit [MeasurableSpace Ω] in
theorem quenchedMinimalScaleIndex_spec
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω}
    (hgood : hasGoodTailFrom N0 Bad ω) :
    N0 ≤ quenchedMinimalScaleIndex N0 Bad ω ∧
      goodTailFrom Bad (quenchedMinimalScaleIndex N0 Bad ω) ω := by
  classical
  have hfind := Nat.find_spec hgood
  simpa [quenchedMinimalScaleIndex, hgood] using hfind

omit [MeasurableSpace Ω] in
theorem quenchedMinimalScaleIndex_le_of_goodTail
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω} {M : ℕ}
    (hN0M : N0 ≤ M) (hM : goodTailFrom Bad M ω) :
    quenchedMinimalScaleIndex N0 Bad ω ≤ M := by
  classical
  let hgood : hasGoodTailFrom N0 Bad ω := ⟨M, hN0M, hM⟩
  have hidx_eq : quenchedMinimalScaleIndex N0 Bad ω = Nat.find hgood := by
    unfold quenchedMinimalScaleIndex
    rw [dif_pos hgood]
  rw [hidx_eq]
  exact Nat.find_min' hgood ⟨hN0M, hM⟩

omit [MeasurableSpace Ω] in
theorem mem_badTailEvent_of_lt_quenchedMinimalScaleIndex
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω} {N : ℕ}
    (hN0N : N0 ≤ N)
    (hN : N < quenchedMinimalScaleIndex N0 Bad ω) :
    ω ∈ badTailEvent Bad N := by
  classical
  by_cases htail : ω ∈ badTailEvent Bad N
  · exact htail
  · have hN_good : goodTailFrom Bad N ω := by
      intro K hNK hbad
      exact htail ⟨K, hNK, hbad⟩
    have hidx_le_N :
        quenchedMinimalScaleIndex N0 Bad ω ≤ N :=
      quenchedMinimalScaleIndex_le_of_goodTail
        (N0 := N0) (Bad := Bad) (ω := ω) hN0N hN_good
    omega

omit [MeasurableSpace Ω] in
theorem quenchedMinimalScaleIndex_tail_subset_badTailEvent
    {N0 : ℕ} {Bad : ℕ → Set Ω} {N : ℕ}
    (hN0N : N0 ≤ N) :
    {ω | N < quenchedMinimalScaleIndex N0 Bad ω} ⊆ badTailEvent Bad N := by
  intro ω hω
  exact mem_badTailEvent_of_lt_quenchedMinimalScaleIndex
    (N0 := N0) (Bad := Bad) hN0N hω

omit [MeasurableSpace Ω] in
theorem not_hasGoodTailFrom_subset_badTailEvent
    {N0 : ℕ} {Bad : ℕ → Set Ω} {N : ℕ}
    (hN0N : N0 ≤ N) :
    {ω | ¬ hasGoodTailFrom N0 Bad ω} ⊆ badTailEvent Bad N := by
  intro ω hω
  by_contra htail
  have hgoodN : goodTailFrom Bad N ω := by
    intro K hNK hbad
    exact htail ⟨K, hNK, hbad⟩
  exact hω ⟨N, hN0N, hgoodN⟩

/-- Quantitative bad-tail bounds imply that the exceptional set with no good
tail has measure zero.  The hypothesis is deliberately an epsilon formulation:
downstream files can supply it from any explicit geometric or
stretched-exponential bad-tail estimate. -/
theorem measureReal_not_hasGoodTailFrom_eq_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {N0 : ℕ} {Bad : ℕ → Set Ω}
    (hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, N0 ≤ N ∧ μ.real (badTailEvent Bad N) ≤ ε) :
    μ.real {ω | ¬ hasGoodTailFrom N0 Bad ω} = 0 := by
  let E : Set Ω := {ω | ¬ hasGoodTailFrom N0 Bad ω}
  have hnonneg : 0 ≤ μ.real E := by positivity
  by_contra hne
  have hpos : 0 < μ.real E := lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨N, hN0N, hN⟩ := hsmall (μ.real E / 2) (by linarith)
  have hsubset : E ⊆ badTailEvent Bad N :=
    not_hasGoodTailFrom_subset_badTailEvent
      (N0 := N0) (Bad := Bad) hN0N
  have hmono : μ.real E ≤ μ.real (badTailEvent Bad N) :=
    measureReal_mono (μ := μ) hsubset
  nlinarith

theorem ae_hasGoodTailFrom
    {μ : Measure Ω} [IsFiniteMeasure μ] {N0 : ℕ} {Bad : ℕ → Set Ω}
    (hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, N0 ≤ N ∧ μ.real (badTailEvent Bad N) ≤ ε) :
    ∀ᵐ ω ∂μ, hasGoodTailFrom N0 Bad ω := by
  have hzero :
      μ.real {ω | ¬ hasGoodTailFrom N0 Bad ω} = 0 :=
    measureReal_not_hasGoodTailFrom_eq_zero
      (μ := μ) (N0 := N0) (Bad := Bad) hsmall
  have hnull :
      μ {ω | ¬ hasGoodTailFrom N0 Bad ω} = 0 :=
    (measureReal_eq_zero_iff).1 hzero
  exact ae_iff.mpr hnull

theorem rpow_three_log_div_log_eq
    {x : ℝ} (hx : 0 < x) :
    Real.rpow (3 : ℝ) (Real.log x / Real.log 3) = x := by
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  calc
    Real.rpow (3 : ℝ) (Real.log x / Real.log 3)
        = Real.exp (Real.log (3 : ℝ) * (Real.log x / Real.log 3)) := by
            simpa using
              Real.rpow_def_of_pos
                (x := (3 : ℝ)) (y := Real.log x / Real.log 3)
                (by norm_num : (0 : ℝ) < 3)
    _ = Real.exp (Real.log x) := by
            congr 1
            field_simp [hlog3_pos.ne']
    _ = x := Real.exp_log hx

theorem rpow_three_natCeil_log_div_log_le_three_mul
    {x : ℝ} (hx : 1 ≤ x) :
    Real.rpow (3 : ℝ)
        ((Nat.ceil (Real.log x / Real.log 3) : ℕ) : ℝ) ≤
      3 * x := by
  let y : ℝ := Real.log x / Real.log 3
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (Real.log_nonneg hx) hlog3_pos.le
  have hceil_lt : ((Nat.ceil y : ℕ) : ℝ) < y + 1 :=
    Nat.ceil_lt_add_one hy_nonneg
  have hpow_le :
      Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ) ≤
        Real.rpow (3 : ℝ) (y + 1) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hceil_lt.le
  calc
    Real.rpow (3 : ℝ)
        ((Nat.ceil (Real.log x / Real.log 3) : ℕ) : ℝ)
        = Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ) := by simp [y]
    _ ≤ Real.rpow (3 : ℝ) (y + 1) := hpow_le
    _ = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) (1 : ℝ) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 3) y 1
    _ = x * 3 := by
        rw [rpow_three_log_div_log_eq hx_pos]
        norm_num
    _ = 3 * x := by ring

theorem le_rpow_three_natCeil_log_div_log
    {x : ℝ} (hx : 1 ≤ x) :
    x ≤
      Real.rpow (3 : ℝ)
        ((Nat.ceil (Real.log x / Real.log 3) : ℕ) : ℝ) := by
  let y : ℝ := Real.log x / Real.log 3
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hceil : y ≤ ((Nat.ceil y : ℕ) : ℝ) := Nat.le_ceil y
  calc
    x = Real.rpow (3 : ℝ) y := by
        rw [rpow_three_log_div_log_eq hx_pos]
    _ ≤ Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) hceil
    _ =
        Real.rpow (3 : ℝ)
          ((Nat.ceil (Real.log x / Real.log 3) : ℕ) : ℝ) := by simp [y]

/-- Discrete bad-tail bounds imply the continuous `Γ_η` tail of the triadic
minimal scale.  The factor `3` is the triadic rounding loss. -/
theorem isBigOWith_quenchedMinimalScale_of_badTailEvent_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {N0 : ℕ} {Bad : ℕ → Set Ω} {B η : ℝ}
    (hη_pos : 0 < η) (hB : 1 ≤ B)
    (htail :
      ∀ N : ℕ, N0 ≤ N →
        μ.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - N0 : ℕ) : ℝ)) / B) ^ η))) :
    IsBigOWith μ (gammaSigma η) (quenchedMinimalScale N0 Bad)
      (3 * ((3 : ℝ) ^ N0) * B) := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff]
  intro s hs
  let x : ℝ := B * s
  let j : ℕ := Nat.ceil (Real.log x / Real.log 3)
  let N : ℕ := N0 + j
  have hs_nonneg : 0 ≤ s := le_trans zero_le_one hs
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx_one : 1 ≤ x := by
    dsimp [x]
    nlinarith
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_one
  have hj_upper :
      Real.rpow (3 : ℝ) (j : ℝ) ≤ 3 * x := by
    simpa [j] using
      rpow_three_natCeil_log_div_log_le_three_mul (x := x) hx_one
  have hj_lower :
      x ≤ Real.rpow (3 : ℝ) (j : ℝ) := by
    simpa [j] using
      le_rpow_three_natCeil_log_div_log (x := x) hx_one
  have hN0N : N0 ≤ N := by
    dsimp [N]
    exact Nat.le_add_right N0 j
  have hsubset :
      upperTailEvent (quenchedMinimalScale N0 Bad)
          ((3 * ((3 : ℝ) ^ N0) * B) * s) ⊆
        badTailEvent Bad N := by
    intro ω hω
    have hpowN_le :
        (3 : ℝ) ^ N ≤ (3 * ((3 : ℝ) ^ N0) * B) * s := by
      have hpow_add :
          (3 : ℝ) ^ N = (3 : ℝ) ^ N0 * (3 : ℝ) ^ j := by
        dsimp [N]
        rw [pow_add]
      have hpowj_eq :
          (3 : ℝ) ^ j = Real.rpow (3 : ℝ) (j : ℝ) := by
        exact (Real.rpow_natCast (3 : ℝ) j).symm
      rw [hpow_add, hpowj_eq]
      calc
        (3 : ℝ) ^ N0 * Real.rpow (3 : ℝ) (j : ℝ)
            ≤ (3 : ℝ) ^ N0 * (3 * x) := by
              exact mul_le_mul_of_nonneg_left hj_upper (by positivity)
        _ = (3 * ((3 : ℝ) ^ N0) * B) * s := by
              dsimp [x]
              ring
    have hpowN_lt_idx :
        (3 : ℝ) ^ N < (3 : ℝ) ^ quenchedMinimalScaleIndex N0 Bad ω := by
      dsimp [upperTailEvent, quenchedMinimalScale] at hω
      exact lt_of_le_of_lt hpowN_le hω
    have hN_lt_idx : N < quenchedMinimalScaleIndex N0 Bad ω :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hpowN_lt_idx
    exact mem_badTailEvent_of_lt_quenchedMinimalScaleIndex
      (N0 := N0) (Bad := Bad) hN0N hN_lt_idx
  have hmeasure :
      μ.real
          (upperTailEvent (quenchedMinimalScale N0 Bad)
            ((3 * ((3 : ℝ) ^ N0) * B) * s)) ≤
        μ.real (badTailEvent Bad N) :=
    measureReal_mono (μ := μ) hsubset
  have hN_sub : N - N0 = j := by
    dsimp [N]
    omega
  have hratio_lower : s ≤ Real.rpow (3 : ℝ) (j : ℝ) / B := by
    have hmul : s * B ≤ Real.rpow (3 : ℝ) (j : ℝ) := by
      simpa [x, mul_comm, mul_left_comm, mul_assoc] using hj_lower
    exact (le_div_iff₀ hB_pos).2 hmul
  have hratio_nonneg : 0 ≤ Real.rpow (3 : ℝ) (j : ℝ) / B :=
    div_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) hB_pos.le
  have hpow :
      s ^ η ≤ (Real.rpow (3 : ℝ) (j : ℝ) / B) ^ η :=
    Real.rpow_le_rpow hs_nonneg hratio_lower hη_pos.le
  calc
    μ.real
        (upperTailEvent (quenchedMinimalScale N0 Bad)
          ((3 * ((3 : ℝ) ^ N0) * B) * s))
        ≤ μ.real (badTailEvent Bad N) := hmeasure
    _ ≤
        Real.exp
          (-(((Real.rpow (3 : ℝ) ((N - N0 : ℕ) : ℝ)) / B) ^ η)) :=
        htail N hN0N
    _ =
        Real.exp (-( (Real.rpow (3 : ℝ) (j : ℝ) / B) ^ η)) := by
        rw [hN_sub]
    _ ≤ Real.exp (-(s ^ η)) := by
        exact Real.exp_le_exp.mpr (by linarith)

theorem isBigO_quenchedMinimalScale_of_badTailEvent_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {N0 : ℕ} {Bad : ℕ → Set Ω} {B η : ℝ}
    (hη_pos : 0 < η) (hB : 1 ≤ B)
    (htail :
      ∀ N : ℕ, N0 ≤ N →
        μ.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - N0 : ℕ) : ℝ)) / B) ^ η))) :
    IsBigO μ (gammaSigma η) (quenchedMinimalScale N0 Bad)
      (3 * ((3 : ℝ) ^ N0) * B) := by
  have hwith :=
    isBigOWith_quenchedMinimalScale_of_badTailEvent_bound
      (μ := μ) (N0 := N0) (Bad := Bad) (B := B) (η := η)
      hη_pos hB htail
  rw [IsBigO]
  exact hwith.of_le fun ω => by
    dsimp [quenchedMinimalScale]
    rw [abs_of_nonneg]
    positivity

omit [MeasurableSpace Ω] in
theorem not_mem_bad_of_quenchedMinimalScaleIndex_le
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω}
    (hgood : hasGoodTailFrom N0 Bad ω)
    {N K : ℕ}
    (hidxN : quenchedMinimalScaleIndex N0 Bad ω ≤ N) (hNK : N ≤ K) :
    ω ∉ Bad K := by
  have hspec := quenchedMinimalScaleIndex_spec
    (N0 := N0) (Bad := Bad) (ω := ω) hgood
  exact hspec.2 K (hidxN.trans hNK)

omit [MeasurableSpace Ω] in
theorem quenchedMinimalScaleIndex_le_of_scale_le_pow
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω} {m : ℕ}
    (hscale : quenchedMinimalScale N0 Bad ω ≤ (3 : ℝ) ^ m) :
    quenchedMinimalScaleIndex N0 Bad ω ≤ m := by
  dsimp [quenchedMinimalScale] at hscale
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hscale

omit [MeasurableSpace Ω] in
theorem rpow_three_div_quenchedMinimalScale_eq_index
    {N0 : ℕ} {Bad : ℕ → Set Ω} {ω : Ω} {m : ℕ} {α : ℝ}
    (hscale : quenchedMinimalScale N0 Bad ω ≤ (3 : ℝ) ^ m) :
    ((3 : ℝ) ^ m / quenchedMinimalScale N0 Bad ω) ^ (-α) =
      (3 : ℝ) ^
        (-α * ((m - quenchedMinimalScaleIndex N0 Bad ω : ℕ) : ℝ)) := by
  let L : ℕ := quenchedMinimalScaleIndex N0 Bad ω
  have hLm : L ≤ m := by
    simpa [L] using
      quenchedMinimalScaleIndex_le_of_scale_le_pow
        (N0 := N0) (Bad := Bad) (ω := ω) hscale
  have hratio :
      (3 : ℝ) ^ m / quenchedMinimalScale N0 Bad ω =
        (3 : ℝ) ^ (m - L) := by
    dsimp [quenchedMinimalScale, L]
    rw [div_eq_mul_inv]
    exact (pow_sub₀ (3 : ℝ) (by norm_num) hLm).symm
  rw [hratio]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

omit [MeasurableSpace Ω] in
theorem le_of_not_mem_badScaleEvent
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {N m n : ℕ} {ω : Ω}
    (hnot : ω ∉ badScaleEvent H t α N)
    (hnm : n < m) (hNm : N ≤ m) :
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω ≤
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ)) := by
  exact le_of_not_gt fun hgt => hnot ⟨m, n, hnm, hNm, hgt⟩

omit [MeasurableSpace Ω] in
/-- Above the constructed scale, absence of the corresponding bad-scale event
gives the discounted estimate for the abstract observable `H`. -/
theorem badScaleEvent_estimate_above_quenchedMinimalScale
    {N0 : ℕ} {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {ω : Ω}
    (hgood : hasGoodTailFrom N0 (badScaleEvent H t α) ω)
    {m n : ℕ}
    (hscale :
      quenchedMinimalScale N0 (badScaleEvent H t α) ω ≤ (3 : ℝ) ^ m)
    (hnm : n < m) :
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω ≤
      ((3 : ℝ) ^ m /
        quenchedMinimalScale N0 (badScaleEvent H t α) ω) ^ (-α) := by
  let L : ℕ :=
    quenchedMinimalScaleIndex N0 (badScaleEvent H t α) ω
  have hLm : L ≤ m := by
    simpa [L] using
      quenchedMinimalScaleIndex_le_of_scale_le_pow
        (N0 := N0) (Bad := badScaleEvent H t α) (ω := ω) hscale
  have hnot : ω ∉ badScaleEvent H t α L := by
    exact not_mem_bad_of_quenchedMinimalScaleIndex_le
      (N0 := N0) (Bad := badScaleEvent H t α) (ω := ω)
      hgood (N := L) (K := L) le_rfl le_rfl
  have hmain :
      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω ≤
        (3 : ℝ) ^ (-α * ((m - L : ℕ) : ℝ)) :=
    le_of_not_mem_badScaleEvent
      (H := H) (t := t) (α := α) (N := L) (m := m) (n := n)
      hnot hnm hLm
  simpa [L, rpow_three_div_quenchedMinimalScale_eq_index
    (N0 := N0) (Bad := badScaleEvent H t α) (ω := ω)
    (m := m) (α := α) hscale] using hmain

end

end Section57
end Ch05
end Book
end Homogenization
