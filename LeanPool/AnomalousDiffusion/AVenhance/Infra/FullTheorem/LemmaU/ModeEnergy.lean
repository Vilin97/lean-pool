/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.ScalarPaths

/-!
# Lemma U: the abstract mode system

A finite family of scalar paths `c a` with `c a' = -(κ λₐ c a + G a)`, together with an integrable
energy density `e` dominating `Σ λₐ (c a)²` and (after the factor `B²`) `Σ (G a)²`.  The two
consequences used by Lemma U are proved here, with no reference to PDEs or Fourier series:
the low-mode increment bound and the high-mode amplitude bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- Hypotheses on a finite family of mode paths. -/
structure ModeSystem {ι : Type*} [Fintype ι] (κ B : ℝ) (lam : ι → ℝ) (c G : ι → ℝ → ℝ)
    (e : ℝ → ℝ) (Etot : ℝ) : Prop where
  kappa_pos : 0 < κ
  B_nonneg : 0 ≤ B
  lam_nonneg : ∀ a, 0 ≤ lam a
  c_cont : ∀ a, ContinuousOn (c a) (Icc (0 : ℝ) 1)
  G_int : ∀ a, IntervalIntegrable (G a) volume 0 1
  path : ∀ a, ∀ t ∈ Icc (0 : ℝ) 1,
    c a t = c a 0 - ∫ r in (0 : ℝ)..t, (κ * lam a * c a r + G a r)
  e_nonneg : ∀ r, 0 ≤ e r
  e_int : IntervalIntegrable e volume 0 1
  e_total : ∫ r in (0 : ℝ)..1, e r ≤ Etot
  bessel_c : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) 1)), ∑ a, lam a * c a r ^ 2 ≤ e r
  bessel_G : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) 1)), ∑ a, G a r ^ 2 ≤ B ^ 2 * e r

namespace ModeSystem

variable {ι : Type*} [Fintype ι] {κ B : ℝ} {lam : ι → ℝ} {c G : ι → ℝ → ℝ} {e : ℝ → ℝ}
  {Etot : ℝ}

theorem ModeEnergy.uIcc_sub {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    uIcc s t ⊆ uIcc (0 : ℝ) 1 := by
  rw [uIcc_of_le zero_le_one]
  intro r hr
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hr
    exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
  · rw [uIcc_of_ge h] at hr
    exact ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩

theorem etot_nonneg (hM : ModeSystem κ B lam c G e Etot) : 0 ≤ Etot :=
  le_trans (intervalIntegral.integral_nonneg zero_le_one (fun r _ => hM.e_nonneg r))
    hM.e_total

theorem c_intervalIntegrable (hM : ModeSystem κ B lam c G e Etot) (a : ι) :
    IntervalIntegrable (c a) volume 0 1 :=
  (hM.c_cont a).intervalIntegrable_of_Icc zero_le_one

theorem G_sq_intervalIntegrable (hM : ModeSystem κ B lam c G e Etot) (a : ι) :
    IntervalIntegrable (fun r => G a r ^ 2) volume 0 1 := by
  have hmeas : AEStronglyMeasurable (G a) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have := hM.G_int a
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.aestronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have he : IntegrableOn e (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hM.e_int
  refine Integrable.mono' (he.const_mul (B ^ 2)) (hmeas.aemeasurable.pow_const
      2).aestronglyMeasurable ?_
  filter_upwards [hM.bessel_G] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (Finset.single_le_sum (f := fun a => G a r ^ 2) (fun a _ => sq_nonneg (G a r))
    (Finset.mem_univ a)).trans hr

theorem q_intervalIntegrable (hM : ModeSystem κ B lam c G e Etot) (a : ι) :
    IntervalIntegrable (fun r => κ * lam a * c a r + G a r) volume 0 1 :=
  ((hM.c_intervalIntegrable a).const_mul (κ * lam a)).add (hM.G_int a)

theorem q_sq_intervalIntegrable (hM : ModeSystem κ B lam c G e Etot) (a : ι) :
    IntervalIntegrable (fun r => (κ * lam a * c a r + G a r) ^ 2) volume 0 1 := by
  have hc' : ContinuousOn (c a) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]; exact hM.c_cont a
  have hc2 : IntervalIntegrable (fun r => c a r ^ 2) volume 0 1 :=
    ((hM.c_cont a).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hcG : IntervalIntegrable (fun r => G a r * c a r) volume 0 1 :=
    (hM.G_int a).mul_continuousOn hc'
  have e : (fun r => (κ * lam a * c a r + G a r) ^ 2) =
      fun r => ((κ * lam a) ^ 2 * c a r ^ 2 + (2 * (κ * lam a)) * (G a r * c a r)) +
        G a r ^ 2 := by
    funext r; ring
  rw [e]
  exact (((hc2.const_mul _).add (hcG.const_mul _)).add (hM.G_sq_intervalIntegrable a))

/-- The increment of one mode over `[s,t]`. -/
theorem increment_eq (hM : ModeSystem κ B lam c G e Etot) (a : ι) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    c a t - c a s = -∫ r in s..t, (κ * lam a * c a r + G a r) := by
  have hq := hM.q_intervalIntegrable a
  have h1 : IntervalIntegrable (fun r => κ * lam a * c a r + G a r) volume 0 s :=
    hq.mono_set (by
      rw [uIcc_of_le zero_le_one] at *
      have := ModeEnergy.uIcc_sub (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hs
      simpa using this)
  have h2 : IntervalIntegrable (fun r => κ * lam a * c a r + G a r) volume 0 t :=
    hq.mono_set (by
      have := ModeEnergy.uIcc_sub (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht
      simpa using this)
  rw [hM.path a t ht, hM.path a s hs, ← intervalIntegral.integral_interval_sub_left h2 h1]
  ring

end ModeSystem

end AVenhance.Infra.FullTheorem.LemmaU

end
