/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFluxEntries
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFluxAlg

/-! # Pointwise bounds for the fluxes and slow factors of `twistie4`, `twistie5`

The entrywise bounds are in `TermCenteredFluxEntries`, the real-algebra steps in
`TermCenteredFluxAlg`; absolute constants: `c = 64`, `c₀ = 28 * 2^16`, `c₁ = 7`. -/

@[expose] public section

open MeasureTheory Homogenization Matrix
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Section5.Integration

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- **Pointwise flux bound** (source `e.monster.est.8a`, `e.monster.est.9a`): with the
corrector amplitude `a_m ε_m²`, the fluxes `Σ ξ_k D_k G_k`, `Σ ξ_k E_k G_k` are bounded by
`c ε_{m-1}^{2δ} a_m ε_m² |∇T|` (`c` an absolute constant), for `t` arbitrary and `κm > 0`.  This
holds for all `x`, not only on a support, since the flux is a convex combination over the
supports of `ξ_{m,k}`. -/
theorem sd_flux_bound :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
      {m : ℕ} (_hm : 2 ≤ m) {κm : ℝ} (_hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
      (_hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (x : Vec 2),
      vecNormSq (twistie4Flux I hΦ m κm T t x) ≤
        (c * (epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2))) ^ 2 *
          vecNormSq (spaceGrad (T t) x) ∧
      vecNormSq (twistie5Flux I hΦ m κm T t x) ≤
        (c * (epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2))) ^ 2 *
          vecNormSq (spaceGrad (T t) x) := by
  refine ⟨64, by norm_num, ?_⟩
  intro I Φ hΦ m hm κm hκm T t hTt x
  set e := epsilon β I.Λ (m - 1) ^ (2 * delta β) with he
  set P := a β I.Λ m * epsilon β I.Λ m ^ 2 with hP
  set gT := Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hgT
  have hg : ∀ p, |spaceGrad (T t) x p| ≤ gT := fun p => abs_apply_le_sqrt_vecNormSq _ p
  have hsq : gT ^ 2 = vecNormSq (spaceGrad (T t) x) := Real.sq_sqrt (vecNormSq_nonneg _)
  rw [← hsq]
  constructor
  · refine scf_flux_sq (C := 16) (by norm_num) ?_
    intro i
    unfold twistie4Flux
    refine (sa_tsum_abs_le I (by omega) t _ (16 * (e * P * gT)) ?_ i).trans_eq rfl
    intro k hk j
    have hD := abs_mulVec_le (M := sdDefect4 I hΦ m κm k.1 t x) (μ := 2 * e * P)
      (fun u v => scf_sdDefect4_entry_le I hΦ hm hκm hk x u v)
      (fun p => scf_G_abs_le I hΦ hm hTt hk x hg p) j
    exact hD.trans_eq (by ring)
  · refine scf_flux_sq (C := 32) (by norm_num) ?_
    intro i
    unfold twistie5Flux
    refine (sa_tsum_abs_le I (by omega) t _ (32 * (e * P * gT)) ?_ i).trans_eq rfl
    intro k hk j
    have hD := abs_mulVec_le (M := sdDefect5 I hΦ m κm k.1 t x) (μ := 2 * e * (2 * P))
      (fun u v => scf_sdDefect5_entry_le I hΦ hm hκm hk x u v)
      (fun p => scf_G_abs_le I hΦ hm hTt hk x hg p) j
    exact hD.trans_eq (by ring)

/-- **Pointwise bounds of the slow factors** (`e.fg.choice.2`, `e.fg.choice.3`): with
`ε = ε_{m-1}`, `|f|² ≲ (κ ε^{2δ})² (ε⁻² |∇T|² + |∇∂_0T|² + |∇∂_1T|²)` (choice 2) and without `κ`
(choice 3).  Uses `|∇X^{-1} - I| ≤ ε^{2δ}`, `|∇X∘X⁻¹ - I| ≤ ε^{2δ}`, `|∂²X| ≤ 2^{16} ε⁻¹` on
`supp ξ_{m,k}` (and `ξ_{m,k} = 0` elsewhere). -/
theorem sd_slow_pointwise :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ ∀ (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
      (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 2 ≤ m) {κm : ℝ} (_hκm : 0 ≤ κm) (T : ℝ → Vec 2 → ℝ)
      {t : ℝ} (_hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (k : ℤ) (a j : Fin 2) (x : Vec 2),
      (section5SlowChoice2 I hΦ m κm T k t a j x) ^ 2 ≤
        (c₀ * κm * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 *
            vecNormSq (spaceGrad (T t) x) +
          (c₁ * κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
            (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) +
              vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x)) ∧
      (section5SlowChoice3 I hΦ m T k t a j x) ^ 2 ≤
        (c₀ * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 *
            vecNormSq (spaceGrad (T t) x) +
          (c₁ * epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
            (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) +
              vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x)) := by
  refine ⟨28 * 2 ^ 16, 7, by norm_num, by norm_num, ?_⟩
  intro I Φ hΦ m hm κm hκm T t hTt k a j x
  set e := epsilon β I.Λ (m - 1) ^ (2 * delta β) with he
  set q := (epsilon β I.Λ (m - 1))⁻¹ with hq
  set gT := Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hgT
  set h0 := Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x))
    with hh0
  set h1 := Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))
    with hh1
  have hg : ∀ p, |spaceGrad (T t) x p| ≤ gT := fun p => abs_apply_le_sqrt_vecNormSq _ p
  have hhh : ∀ i p, |spaceHess (T t) x i p| ≤ ![h0, h1] p := by
    intro i p
    fin_cases p
    · exact abs_apply_le_sqrt_vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) i
    · exact abs_apply_le_sqrt_vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x) i
  have hsq0 : gT ^ 2 = vecNormSq (spaceGrad (T t) x) := Real.sq_sqrt (vecNormSq_nonneg _)
  have hsq1 : h0 ^ 2 = vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) :=
    Real.sq_sqrt (vecNormSq_nonneg _)
  have hsq2 : h1 ^ 2 = vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x) :=
    Real.sq_sqrt (vecNormSq_nonneg _)
  have he0 : 0 ≤ e := scf_e_nonneg I
  have hq0 : 0 ≤ q := inv_nonneg.2 (epsilon_pos' I _).le
  have hgn : 0 ≤ gT := Real.sqrt_nonneg _
  have hh0n : 0 ≤ h0 := Real.sqrt_nonneg _
  have hh1n : 0 ≤ h1 := Real.sqrt_nonneg _
  have hxi := Infra.Section3.xiMK_mem_Icc I (by omega : 1 ≤ m) k t
  rw [← hsq0, ← hsq1, ← hsq2]
  -- the common bound on `∇G`
  have key : I.xiMK m k t ≠ 0 → ∀ i, |gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
      2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT := fun hξ i => by
    simpa using scf_gradG_abs_le I hΦ hm hTt hξ x hg hhh i j
  have hS2 : I.xiMK m k t ≠ 0 → |∑ i : Fin 2,
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
      2 * e * (2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT) := fun hξ => by
    have hs := abs_mulVec_le
      (M := (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1)ᵀ)
      (μ := e) (g := fun i => gradG I hΦ m T (lIdx β I.Λ m k) t x i j)
      (fun u v => gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ x v u) (key hξ) a
    simpa [Matrix.mulVec, dotProduct] using hs
  have hS3 : I.xiMK m k t ≠ 0 → |∑ i : Fin 2,
      (1 - (flowGradK I hΦ m k t x).transpose) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
      2 * e * (2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT) := fun hξ => by
    have hs := abs_mulVec_le
      (M := (1 - (flowGradK I hΦ m k t x).transpose)ᵀ)
      (μ := e) (g := fun i => gradG I hΦ m T (lIdx β I.Λ m k) t x i j)
      (fun u v => scf_one_sub_transpose_le I hΦ hm hξ x v u) (key hξ) a
    simpa [Matrix.mulVec, dotProduct] using hs
  have hpos : 0 ≤ e * (4 * h0 + 4 * h1 + 16 * (2 ^ 16 * q) * gT) := by positivity
  constructor
  · refine scf_slow_sq hκm he0 hq0 hgn hh0n hh1n ?_
    unfold section5SlowChoice2
    by_cases hξ : I.xiMK m k t = 0
    · rw [hξ, zero_mul, zero_mul, abs_zero]
      have := mul_nonneg hκm hpos
      linarith
    · refine (scf_slow_abs hxi.1 hxi.2 hκm (hS2 hξ)).trans_eq ?_
      ring
  · have hf : |section5SlowChoice3 I hΦ m T k t a j x| ≤
        1 * e * (4 * h0 + 4 * h1 + 16 * (2 ^ 16 * q) * gT) := by
      unfold section5SlowChoice3
      by_cases hξ : I.xiMK m k t = 0
      · rw [hξ, zero_mul, abs_zero]
        linarith
      · refine (scf_slow_abs' hxi.1 hxi.2 (hS3 hξ)).trans_eq ?_
        ring
    refine (scf_slow_sq zero_le_one he0 hq0 hgn hh0n hh1n hf).trans_eq ?_
    ring

end AVenhance.Infra.Section5.Contracts
end
