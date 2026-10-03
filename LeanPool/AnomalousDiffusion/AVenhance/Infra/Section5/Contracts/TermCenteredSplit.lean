/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitFlux

/-! # Divergence/nondivergence split of `twistie4ND`, `twistie5ND`

The proofs use the helper modules `TermCenteredSplitCalculus` (product rule),
    `TermCenteredSplitFields`
(smoothness/periodicity of the defect matrices), `TermCenteredSplitFlux` (generic finite-support
flux calculus) and `TermCenteredSplitAlgebra` (component forms). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `e.monster.twistie4.split` for the earlier body: `twistie4ND = (nondivergence part) - div
    (flux)`.
(In the corrected form, `twistie4` itself is `-div (flux)`: `twistie4_eq_neg_div_flux`.) -/
theorem twistie4ND_split (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (x : Vec 2) :
    twistie4ND I hΦ m κm T t x =
      twistie4Nd I hΦ m κm T t x - vecDiv (twistie4Flux I hΦ m κm T t) x := by
  rw [twistie4ND_eq_defect]
  exact sd_split_odd (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect4 I hΦ m κm k.1 t) (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => sd_defect4_contDiff I hΦ m κm k.1 t i j)
    (fun k j => contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt) j) x

/-- `e.monster.twistie5.split` for the earlier body `twistie5ND`. -/
theorem twistie5ND_split (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (x : Vec 2) :
    twistie5ND I hΦ m κm T t x =
      twistie5Nd I hΦ m κm T t x - vecDiv (twistie5Flux I hΦ m κm T t) x := by
  rw [twistie5ND_eq_defect]
  exact sd_split_odd (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect5 I hΦ m κm k.1 t) (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => sd_defect5_contDiff I hΦ m κm k.1 t i j)
    (fun k j => contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt) j) x

theorem twistie4Flux_smooth_periodic (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (twistie4Flux I hΦ m κm T t) ∧
      IsZ2Periodic (twistie4Flux I hΦ m κm T t) :=
  ⟨sd_flux_contDiff (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect4 I hΦ m κm k.1 t) (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => sd_defect4_contDiff I hΦ m κm k.1 t i j)
    (fun k j => contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt) j),
   sd_flux_periodic (fun k => I.xiMK m k.1 t) (fun k => sdDefect4 I hΦ m κm k.1 t)
    (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t) (fun k => sd_defect4_periodic I hΦ m κm k.1 t)
    (fun k => tf_G_slice_periodic I hΦ m T t (lIdx β I.Λ m k.1) hTp)⟩

theorem twistie5Flux_smooth_periodic (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (twistie5Flux I hΦ m κm T t) ∧
      IsZ2Periodic (twistie5Flux I hΦ m κm T t) :=
  ⟨sd_flux_contDiff (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect5 I hΦ m κm k.1 t) (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => sd_defect5_contDiff I hΦ m κm k.1 t i j)
    (fun k j => contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt) j),
   sd_flux_periodic (fun k => I.xiMK m k.1 t) (fun k => sdDefect5 I hΦ m κm k.1 t)
    (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t) (fun k => sd_defect5_periodic I hΦ m κm k.1 t)
    (fun k => tf_G_slice_periodic I hΦ m T t (lIdx β I.Λ m k.1) hTp)⟩

/-- The nondivergence parts are continuous in `x` (finite sums of continuous terms). -/
theorem twistie4Nd_continuous (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    Continuous (twistie4Nd I hΦ m κm T t) :=
  sd_nd_continuous (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect4 I hΦ m κm k.1 t) (fun k => gradG I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => (sd_defect4_contDiff I hΦ m κm k.1 t i j).continuous)
    (fun k i j => (tf_gradG_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt i j).continuous)

theorem twistie5Nd_continuous (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    Continuous (twistie5Nd I hΦ m κm T t) :=
  sd_nd_continuous (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect5 I hΦ m κm k.1 t) (fun k => gradG I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => (sd_defect5_contDiff I hΦ m κm k.1 t i j).continuous)
    (fun k i j => (tf_gradG_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt i j).continuous)

/-- Component form of the nondivergence part of `twistie4`:
`Σ_k ξ_k D_k : ∇G_k = Σ_k Σ_{a,j} (∂_aΧ_{k,j} ∘ X_k⁻¹) · f_{k,aj}` (choice 2). -/
theorem twistie4Nd_eq_sum (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (S : Finset {k : ℤ // Odd k})
    (hS : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → k ∈ S) (x : Vec 2) :
    twistie4Nd I hΦ m κm T t x =
      ∑ k ∈ S, ∑ a : Fin 2, ∑ j : Fin 2,
        sdFast4 I κm m k.1 t a j (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) *
          section5SlowChoice2 I hΦ m κm T k.1 t a j x := by
  have _hm := hm
  unfold twistie4Nd
  rw [sd_tsum_eq_sum S (fun k hk => hS k fun h => hk (by simp [h]))]
  exact Finset.sum_congr rfl fun k _ => sd_term4_eq I hΦ m κm T k.1 t x

/-- Component form of the nondivergence part of `twistie5` (choice 3). -/
theorem twistie5Nd_eq_sum (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (S : Finset {k : ℤ // Odd k})
    (hS : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → k ∈ S) (x : Vec 2) :
    twistie5Nd I hΦ m κm T t x =
      ∑ k ∈ S, ∑ a : Fin 2, ∑ j : Fin 2,
        sdFast5 I κm m k.1 t a j (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) *
          section5SlowChoice3 I hΦ m T k.1 t a j x := by
  have _hm := hm
  unfold twistie5Nd
  rw [sd_tsum_eq_sum S (fun k hk => hS k fun h => hk (by simp [h]))]
  exact Finset.sum_congr rfl fun k _ => sd_term5_eq I hΦ m κm T k.1 t x

end AVenhance.Infra.Section5.Contracts
end
