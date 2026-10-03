/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth

/-! # Regularity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization Filter Topology
open scoped Matrix.Norms.Elementwise ContDiff
namespace AVenhance.Infra.Section4
open AVenhance

/-- Entrywise proof avoids any choice of a matrix operator norm. -/
theorem coarseCoeff_matrix_mul_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {K F : E → CoarseMatrix} (hK : ContDiff ℝ n K) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => K x * F x) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun p _ =>
    (contDiff_pi.1 (contDiff_pi.1 hK i) p).mul
      (contDiff_pi.1 (contDiff_pi.1 hF p) j)

theorem coarseCoeffPolynomial_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {K F : E → CoarseMatrix} (a b κ : ℝ)
    (hK : ContDiff ℝ n K) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => coarseCoeffPolynomial a b κ (K x) (F x)) := by
  have hFt : ContDiff ℝ n (fun x => (F x).transpose) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.1 (contDiff_pi.1 hF j) i
  have hleft := coarseCoeff_matrix_mul_contDiff hK
    (hF.sub (show ContDiff ℝ n (fun _ : E => (1 : CoarseMatrix)) from contDiff_const))
  have hright := coarseCoeff_matrix_mul_contDiff
    (coarseCoeff_matrix_mul_contDiff
      (hFt.sub (show ContDiff ℝ n (fun _ : E => (1 : CoarseMatrix)) from contDiff_const))
      (hK.sub (show ContDiff ℝ n (fun _ : E => κ • (1 : CoarseMatrix)) from contDiff_const))) hF
  exact ((show ContDiff ℝ n (fun _ : E => a) from contDiff_const).smul hleft).add
    ((show ContDiff ℝ n (fun _ : E => b) from contDiff_const).smul hright)

/-- The same entrywise polynomial calculus on a closed space-time domain. -/
theorem coarseCoeff_matrix_mul_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {U : Set E} {K F : E → CoarseMatrix}
    (hK : ContDiffOn ℝ n K U) (hF : ContDiffOn ℝ n F U) :
    ContDiffOn ℝ n (fun x => K x * F x) U := by
  apply contDiffOn_pi.2
  intro i
  apply contDiffOn_pi.2
  intro j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun p _ =>
    (contDiffOn_pi.1 (contDiffOn_pi.1 hK i) p).mul
      (contDiffOn_pi.1 (contDiffOn_pi.1 hF p) j)

theorem coarseCoeffPolynomial_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {U : Set E} {K F : E → CoarseMatrix} (a b κ : ℝ)
    (hK : ContDiffOn ℝ n K U) (hF : ContDiffOn ℝ n F U) :
    ContDiffOn ℝ n (fun x => coarseCoeffPolynomial a b κ (K x) (F x)) U := by
  have hFt : ContDiffOn ℝ n (fun x => (F x).transpose) U :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.1 (contDiffOn_pi.1 hF j) i
  have hleft := coarseCoeff_matrix_mul_contDiffOn hK
    (hF.sub (show ContDiffOn ℝ n (fun _ : E => (1 : CoarseMatrix)) U from contDiffOn_const))
  have hright := coarseCoeff_matrix_mul_contDiffOn
    (coarseCoeff_matrix_mul_contDiffOn
      (hFt.sub (show ContDiffOn ℝ n (fun _ : E => (1 : CoarseMatrix)) U from contDiffOn_const))
      (hK.sub (show ContDiffOn ℝ n (fun _ : E => κ • (1 : CoarseMatrix)) U from
          contDiffOn_const))) hF
  exact ((show ContDiffOn ℝ n (fun _ : E => a) U from contDiffOn_const).smul hleft).add
    ((show ContDiffOn ℝ n (fun _ : E => b) U from contDiffOn_const).smul hright)

theorem CoarseCoeffForm.spatial_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κ : ℝ}
    {s : ℝ → Vec 2 → CoarseMatrix} (hs : CoarseCoeffForm I hΦ m κ s)
    (hm : 1 ≤ m) (t : ℝ) {n : ℕ∞ω}
    (hflow : ∀ l, ContDiff ℝ n (I.flowGrad hΦ m l t)) : ContDiff ℝ n (s t) := by
  obtain ⟨a, b, _, _, he⟩ := hs.window_form
  have hrep : s t = fun x => ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset,
      I.hatXiML m l t • coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t x) := by
    funext x
    rw [he, coarseCoeffWindow_eq_sum I hΦ hm]
  rw [hrep]
  exact ContDiff.sum fun l _ =>
    (show ContDiff ℝ n (fun _ : Vec 2 => I.hatXiML m l t) from contDiff_const).smul
      (coarseCoeffPolynomial_contDiff a b κ
        (show ContDiff ℝ n (fun _ : Vec 2 => I.Kmat κ m t) from contDiff_const) (hflow l))

/-- Joint smoothness uses a locally fixed finite window sum. -/
theorem CoarseCoeffForm.joint_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κ : ℝ}
    {s : ℝ → Vec 2 → CoarseMatrix} (hs : CoarseCoeffForm I hΦ m κ s) (hm : 1 ≤ m)
    (hK : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => I.Kmat κ m z.1))
    (hflow : ∀ l, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => I.flowGrad hΦ m l z.1 z.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => s z.1 z.2) := by
  obtain ⟨a, b, _, _, he⟩ := hs.window_form
  have hrep : (fun z : ℝ × Vec 2 => s z.1 z.2) = fun z => ∑' l : ℤ,
      I.hatXiML m l z.1 • coarseCoeffPolynomial a b κ (I.Kmat κ m z.1)
        (I.flowGrad hΦ m l z.1 z.2) := by
    funext z
    rw [he, coarseCoeffWindow_eq_tsum I hΦ hm]
  rw [hrep]
  apply Infra.Section5.RelativeError.contDiff_tsum_of_locallyFinite
  · intro l
    exact ((Infra.Section5.RelativeError.hatXiML_contDiff I m l).comp contDiff_fst).smul
      (coarseCoeffPolynomial_contDiff a b κ hK (hflow l))
  · rintro ⟨t, x⟩
    obtain ⟨S, hS⟩ := Infra.Section5.RelativeError.exists_finset_hatXi_vanish I hm t
    refine ⟨S, ?_⟩
    have hball : ∀ᶠ z : ℝ × Vec 2 in 𝓝 (t, x), |z.1 - t| < 1 := by
      have hc : Continuous (fun z : ℝ × Vec 2 => |z.1 - t|) := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
    filter_upwards [hball] with z hz l hl
    rw [hS z.1 hz l hl, zero_smul]

end AVenhance.Infra.Section4
