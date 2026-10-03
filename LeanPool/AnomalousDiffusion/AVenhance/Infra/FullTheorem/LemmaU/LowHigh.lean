/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.ModeEnergy

/-!
# Lemma U: low-mode increments and high-mode amplitudes

For an abstract mode system, the low modes have a Hölder-`1/2`-in-time increment bound, and each
high mode is controlled by its initial amplitude plus the forcing `G`.  Combining the two gives
the total squared increment bound `Σ (c a t - c a s)²` used by Lemma U.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace AVenhance.Infra.FullTheorem.LemmaU

theorem interval_integral_mono_ae_Ioc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ᵐ r ∂(volume.restrict (Ioc a b)), f r ≤ g r) :
    ∫ r in a..b, f r ≤ ∫ r in a..b, g r := by
  simpa only [intervalIntegral.integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 h

theorem intervalIntegrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun r => ∑ i ∈ s, f i r) volume a b := by
  have := IntervalIntegrable.sum s h
  convert this using 1
  ext r
  simp [Finset.sum_apply]

namespace ModeSystem

variable {ι : Type*} [Fintype ι] {κ B : ℝ} {lam : ι → ℝ} {c G : ι → ℝ → ℝ} {e : ℝ → ℝ}
  {Etot : ℝ}

theorem LowHigh.sub_of_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) : uIcc s t ⊆ uIcc (0 : ℝ) 1 := by
  rw [uIcc_of_le zero_le_one, uIcc_of_le hst]
  intro r hr
  exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩

theorem LowHigh.ae_Ioc_of_sub {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {P : ℝ → Prop} (h : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) 1)), P r) :
    ∀ᵐ r ∂(volume.restrict (Ioc s t)), P r :=
  ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hs.1 ht.2) h

/-- The low-mode increment bound. -/
theorem low_sum_le (hM : ModeSystem κ B lam c G e Etot) (low : Finset ι) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hlow : ∀ a ∈ low, lam a ≤ Λ) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    ∑ a ∈ low, (c a t - c a s) ^ 2 ≤ 2 * (t - s) * ((κ ^ 2 * Λ + B ^ 2) * Etot) := by
  have hsub := LowHigh.sub_of_mem hs ht hst
  have hq : ∀ a, IntervalIntegrable (fun r => κ * lam a * c a r + G a r) volume s t :=
    fun a => (hM.q_intervalIntegrable a).mono_set hsub
  have hq2 : ∀ a, IntervalIntegrable (fun r => (κ * lam a * c a r + G a r) ^ 2) volume s t :=
    fun a => (hM.q_sq_intervalIntegrable a).mono_set hsub
  have hper : ∀ a, (c a t - c a s) ^ 2 ≤
      (t - s) * ∫ r in s..t, (κ * lam a * c a r + G a r) ^ 2 := by
    intro a
    rw [hM.increment_eq a hs ht, neg_sq]
    exact sq_intervalIntegral_le hst (hq a) (hq2 a)
  have hsum1 : ∑ a ∈ low, (c a t - c a s) ^ 2 ≤
      (t - s) * ∑ a ∈ low, ∫ r in s..t, (κ * lam a * c a r + G a r) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => hper a)
  have hswap : ∑ a ∈ low, ∫ r in s..t, (κ * lam a * c a r + G a r) ^ 2 =
      ∫ r in s..t, ∑ a ∈ low, (κ * lam a * c a r + G a r) ^ 2 :=
    (intervalIntegral.integral_finsetSum (fun a _ => hq2 a)).symm
  set K2 : ℝ := 2 * (κ ^ 2 * Λ + B ^ 2) with hK2
  have hK2nn : 0 ≤ K2 := by
    have := hM.B_nonneg
    positivity
  have hesub : IntervalIntegrable e volume s t := hM.e_int.mono_set hsub
  have hpt : ∀ᵐ r ∂(volume.restrict (Ioc s t)),
      ∑ a ∈ low, (κ * lam a * c a r + G a r) ^ 2 ≤ K2 * e r := by
    have h1 := LowHigh.ae_Ioc_of_sub hs ht hM.bessel_c
    have h2 := LowHigh.ae_Ioc_of_sub hs ht hM.bessel_G
    filter_upwards [h1, h2] with r hr1 hr2
    have hlam := hM.lam_nonneg
    have hterm : ∀ a ∈ low, (κ * lam a * c a r + G a r) ^ 2 ≤
        2 * (κ ^ 2 * Λ) * (lam a * c a r ^ 2) + 2 * G a r ^ 2 := by
      intro a ha
      have hx : (κ * lam a * c a r) ^ 2 ≤ (κ ^ 2 * Λ) * (lam a * c a r ^ 2) := by
        have : (κ * lam a * c a r) ^ 2 = κ ^ 2 * lam a * (lam a * c a r ^ 2) := by ring
        rw [this]
        have h3 : κ ^ 2 * lam a ≤ κ ^ 2 * Λ := by
          gcongr; exact hlow a ha
        exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (hlam a) (sq_nonneg _))
      nlinarith [sq_nonneg (κ * lam a * c a r - G a r)]
    have hA : ∑ a ∈ low, lam a * c a r ^ 2 ≤ ∑ a, lam a * c a r ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => mul_nonneg (hlam a) (sq_nonneg _))
    have hB' : ∑ a ∈ low, G a r ^ 2 ≤ ∑ a, G a r ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => sq_nonneg _)
    calc ∑ a ∈ low, (κ * lam a * c a r + G a r) ^ 2
        ≤ ∑ a ∈ low, (2 * (κ ^ 2 * Λ) * (lam a * c a r ^ 2) + 2 * G a r ^ 2) :=
          Finset.sum_le_sum hterm
      _ = 2 * (κ ^ 2 * Λ) * ∑ a ∈ low, lam a * c a r ^ 2 + 2 * ∑ a ∈ low, G a r ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (κ ^ 2 * Λ) * e r + 2 * (B ^ 2 * e r) := by
          have hk : 0 ≤ 2 * (κ ^ 2 * Λ) := by positivity
          have := mul_le_mul_of_nonneg_left (hA.trans hr1) hk
          linarith [this, hB'.trans hr2]
      _ = K2 * e r := by rw [hK2]; ring
  have hint : ∫ r in s..t, ∑ a ∈ low, (κ * lam a * c a r + G a r) ^ 2 ≤
      ∫ r in s..t, K2 * e r :=
    interval_integral_mono_ae_Ioc hst (intervalIntegrable_finset_sum' _ (fun a _ => hq2 a))
      (hesub.const_mul K2) hpt
  have hmono : ∫ r in s..t, e r ≤ ∫ r in (0 : ℝ)..1, e r :=
    intervalIntegral.integral_mono_interval hs.1 hst ht.2
      (Filter.Eventually.of_forall (fun r => hM.e_nonneg r)) hM.e_int
  have hK : ∫ r in s..t, K2 * e r ≤ K2 * Etot := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hmono.trans hM.e_total) hK2nn
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  calc ∑ a ∈ low, (c a t - c a s) ^ 2
      ≤ (t - s) * ∑ a ∈ low, ∫ r in s..t, (κ * lam a * c a r + G a r) ^ 2 := hsum1
    _ ≤ (t - s) * (K2 * Etot) := by
        rw [hswap]
        exact mul_le_mul_of_nonneg_left (hint.trans hK) hts
    _ = 2 * (t - s) * ((κ ^ 2 * Λ + B ^ 2) * Etot) := by rw [hK2]; ring

/-- One high mode: its amplitude is controlled by its initial value and the forcing. -/
theorem high_mode_le (hM : ModeSystem κ B lam c G e Etot) (a : ι) (hlam : 0 < lam a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    c a t ^ 2 ≤ c a 0 ^ 2 + (1 / (2 * κ * lam a)) * ∫ r in (0 : ℝ)..t, G a r ^ 2 := by
  have hκ := hM.kappa_pos
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    simpa using LowHigh.sub_of_mem (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht ht.1
  have hq : IntervalIntegrable (fun r => κ * lam a * c a r + G a r) volume 0 t :=
    (hM.q_intervalIntegrable a).mono_set hsub
  have hG : IntervalIntegrable (G a) volume 0 t := (hM.G_int a).mono_set hsub
  have hG2 : IntervalIntegrable (fun r => G a r ^ 2) volume 0 t :=
    (hM.G_sq_intervalIntegrable a).mono_set hsub
  have hc' : ContinuousOn (c a) (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact (hM.c_cont a).mono (fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
  have hcI : IntervalIntegrable (c a) volume 0 t := hc'.intervalIntegrable
  have hc2 : IntervalIntegrable (fun r => c a r ^ 2) volume 0 t := (hc'.pow 2).intervalIntegrable
  have hcG : IntervalIntegrable (fun r => G a r * c a r) volume 0 t := hG.mul_continuousOn hc'
  have hpath : ∀ s ∈ Icc (0 : ℝ) t, c a s = c a 0 - ∫ r in (0 : ℝ)..s,
      (κ * lam a * c a r + G a r) :=
    fun s hs => hM.path a s ⟨hs.1, hs.2.trans ht.2⟩
  have henergy := scalar_path_energy ht.1 hpath hq
  have hexp : ∫ s in (0 : ℝ)..t, 2 * ((κ * lam a * c a s + G a s) * c a s) =
      2 * (κ * lam a) * (∫ s in (0 : ℝ)..t, c a s ^ 2) +
        2 * ∫ s in (0 : ℝ)..t, G a s * c a s := by
    have e : (fun s => 2 * ((κ * lam a * c a s + G a s) * c a s)) =
        fun s => (2 * (κ * lam a)) * c a s ^ 2 + 2 * (G a s * c a s) := by
      funext s; ring
    rw [e, intervalIntegral.integral_add (hc2.const_mul _) (hcG.const_mul _),
      intervalIntegral.integral_const_mul (2 * (κ * lam a)),
      intervalIntegral.integral_const_mul (2 : ℝ)]
  -- Young: 2 G c ≤ 2 κλ c² + G²/(2κλ)
  have hkl : 0 < 2 * κ * lam a := by positivity
  have hyoung : ∫ s in (0 : ℝ)..t, -(2 * (G a s * c a s)) ≤
      ∫ s in (0 : ℝ)..t, (2 * (κ * lam a) * c a s ^ 2 + (1 / (2 * κ * lam a)) * G a s ^ 2) := by
    refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ ?_
    · exact ((hcG.const_mul 2).neg)
    · exact (hc2.const_mul _).add (hG2.const_mul _)
    · intro s _
      have h0 : 0 ≤ (1 / (2 * κ * lam a)) * (G a s + 2 * κ * lam a * c a s) ^ 2 := by positivity
      have e : (1 / (2 * κ * lam a)) * (G a s + 2 * κ * lam a * c a s) ^ 2 =
          (1 / (2 * κ * lam a)) * G a s ^ 2 + 2 * (G a s * c a s) +
            2 * κ * lam a * c a s ^ 2 := by
        field_simp; ring
      nlinarith [e, h0]
  have hsplit : ∫ s in (0 : ℝ)..t, (2 * (κ * lam a) * c a s ^ 2 +
      (1 / (2 * κ * lam a)) * G a s ^ 2) =
      2 * (κ * lam a) * (∫ s in (0 : ℝ)..t, c a s ^ 2) +
        (1 / (2 * κ * lam a)) * ∫ s in (0 : ℝ)..t, G a s ^ 2 := by
    rw [intervalIntegral.integral_add (hc2.const_mul _) (hG2.const_mul _),
      intervalIntegral.integral_const_mul (2 * (κ * lam a)),
      intervalIntegral.integral_const_mul (1 / (2 * κ * lam a))]
  have hneg : ∫ s in (0 : ℝ)..t, -(2 * (G a s * c a s)) =
      -(2 * ∫ s in (0 : ℝ)..t, G a s * c a s) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hneg, hsplit] at hyoung
  linarith [henergy, hexp, hyoung]

/-- The high-mode amplitude bound, summed over modes with `λ ≥ L`. -/
theorem high_sum_le (hM : ModeSystem κ B lam c G e Etot) (high : Finset ι) {L D2 : ℝ}
    (hL : 0 < L) (hhigh : ∀ a ∈ high, L ≤ lam a)
    (hinit : ∑ a, lam a * c a 0 ^ 2 ≤ D2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑ a ∈ high, c a t ^ 2 ≤ D2 / L + B ^ 2 * Etot / (2 * κ * L) := by
  have hκ := hM.kappa_pos
  have hlam := hM.lam_nonneg
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    simpa using LowHigh.sub_of_mem (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht ht.1
  have hG2 : ∀ a, IntervalIntegrable (fun r => G a r ^ 2) volume 0 t :=
    fun a => (hM.G_sq_intervalIntegrable a).mono_set hsub
  have hmode : ∀ a ∈ high, c a t ^ 2 ≤ c a 0 ^ 2 / 1 +
      (1 / (2 * κ * L)) * ∫ r in (0 : ℝ)..t, G a r ^ 2 := by
    intro a ha
    have hpos : 0 < lam a := lt_of_lt_of_le hL (hhigh a ha)
    have h1 := hM.high_mode_le a hpos ht
    have hI : 0 ≤ ∫ r in (0 : ℝ)..t, G a r ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 (fun r _ => sq_nonneg _)
    have h2 : 1 / (2 * κ * lam a) ≤ 1 / (2 * κ * L) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := hhigh a ha
      nlinarith
    rw [div_one]
    calc _ ≤ _ := h1
      _ ≤ _ := by gcongr
  -- sum
  have hsum : ∑ a ∈ high, c a t ^ 2 ≤ ∑ a ∈ high, c a 0 ^ 2 +
      (1 / (2 * κ * L)) * ∑ a ∈ high, ∫ r in (0 : ℝ)..t, G a r ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun a ha => ?_)
    simpa using hmode a ha
  have hswap : ∑ a ∈ high, ∫ r in (0 : ℝ)..t, G a r ^ 2 =
      ∫ r in (0 : ℝ)..t, ∑ a ∈ high, G a r ^ 2 :=
    (intervalIntegral.integral_finsetSum (fun a _ => hG2 a)).symm
  have hsubset : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := hsub
  have hesub : IntervalIntegrable e volume 0 t := hM.e_int.mono_set hsub
  have hpt : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) t)), ∑ a ∈ high, G a r ^ 2 ≤ B ^ 2 * e r := by
    have h2 := LowHigh.ae_Ioc_of_sub (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht
      hM.bessel_G
    filter_upwards [h2] with r hr
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => sq_nonneg (G a r))).trans hr
  have hint : ∫ r in (0 : ℝ)..t, ∑ a ∈ high, G a r ^ 2 ≤ ∫ r in (0 : ℝ)..t, B ^ 2 * e r :=
    interval_integral_mono_ae_Ioc ht.1 (intervalIntegrable_finset_sum' _ (fun a _ => hG2 a))
      (hesub.const_mul _) hpt
  have hmono : ∫ r in (0 : ℝ)..t, e r ≤ ∫ r in (0 : ℝ)..1, e r :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun r => hM.e_nonneg r)) hM.e_int
  have hB2 : ∫ r in (0 : ℝ)..t, B ^ 2 * e r ≤ B ^ 2 * Etot := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hmono.trans hM.e_total) (sq_nonneg B)
  have hinitHigh : ∑ a ∈ high, c a 0 ^ 2 ≤ D2 / L := by
    rw [le_div_iff₀ hL]
    calc (∑ a ∈ high, c a 0 ^ 2) * L = ∑ a ∈ high, L * c a 0 ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun a _ => by ring)
      _ ≤ ∑ a ∈ high, lam a * c a 0 ^ 2 :=
          Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hhigh a ha) (sq_nonneg _))
      _ ≤ ∑ a, lam a * c a 0 ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun a _ _ => mul_nonneg (hlam a) (sq_nonneg _))
      _ ≤ D2 := hinit
  have hcoef : 0 ≤ 1 / (2 * κ * L) := by positivity
  calc ∑ a ∈ high, c a t ^ 2
      ≤ ∑ a ∈ high, c a 0 ^ 2 + (1 / (2 * κ * L)) * ∑ a ∈ high, ∫ r in (0 : ℝ)..t, G a r ^ 2 :=
        hsum
    _ ≤ D2 / L + (1 / (2 * κ * L)) * (B ^ 2 * Etot) := by
        rw [hswap]
        gcongr
        exact hint.trans hB2
    _ = D2 / L + B ^ 2 * Etot / (2 * κ * L) := by ring

/-- Total squared increment, split at the threshold predicate `P` (low modes). -/
theorem increment_sum_le (hM : ModeSystem κ B lam c G e Etot) (P : ι → Prop)
     {Λ L D2 : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 < L)
    (hlow : ∀ a, P a → lam a ≤ Λ) (hhigh : ∀ a, ¬ P a → L ≤ lam a)
    (hinit : ∑ a, lam a * c a 0 ^ 2 ≤ D2) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    ∑ a, (c a t - c a s) ^ 2 ≤ 2 * (t - s) * ((κ ^ 2 * Λ + B ^ 2) * Etot) +
      4 * (D2 / L + B ^ 2 * Etot / (2 * κ * L)) := by
  classical
  have hlowS := hM.low_sum_le (Finset.univ.filter P) hΛ
    (fun a ha => hlow a (Finset.mem_filter.mp ha).2) hs ht hst
  have hts := hM.high_sum_le (Finset.univ.filter (fun a => ¬ P a)) hL
    (fun a ha => hhigh a (Finset.mem_filter.mp ha).2) hinit ht
  have hss := hM.high_sum_le (Finset.univ.filter (fun a => ¬ P a)) hL
    (fun a ha => hhigh a (Finset.mem_filter.mp ha).2) hinit hs
  have hsplit : ∑ a, (c a t - c a s) ^ 2 =
      ∑ a ∈ Finset.univ.filter P, (c a t - c a s) ^ 2 +
        ∑ a ∈ Finset.univ.filter (fun a => ¬ P a), (c a t - c a s) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hhighInc : ∑ a ∈ Finset.univ.filter (fun a => ¬ P a), (c a t - c a s) ^ 2 ≤
      2 * ∑ a ∈ Finset.univ.filter (fun a => ¬ P a), c a t ^ 2 +
        2 * ∑ a ∈ Finset.univ.filter (fun a => ¬ P a), c a s ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun a _ => by nlinarith [sq_nonneg (c a t + c a s)])
  linarith

end ModeSystem

end AVenhance.Infra.FullTheorem.LemmaU

end
