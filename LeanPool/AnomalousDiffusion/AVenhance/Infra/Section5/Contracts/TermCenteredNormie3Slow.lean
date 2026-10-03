/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Fast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplitAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.CellMeanPull

/-! # Slow factor of `normie3`

`slow_{pj} = ξ_k Σ_i (F_k)_{pi} (∇G_k)_{ij}` (`n3Slow`), so that
`ξ_k frob (F_kᵀ M(Y_k x)) ∇G_k = Σ_{p,j} M_{pj}(Y_k x) · slow_{pj}(x)`.  Here: the termwise and
finite-sum representation of `normie3`, smoothness / periodicity, and the pointwise bound
`slow² ≲ ε_{m-1}⁻² |∇T|² + |∇∂_0T|² + |∇∂_1T|²` (no small factor: `|F_k| ≤ 2` only). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The slow factor `ξ_k Σ_i (F_k)_{pi} (∇G_k)_{ij}` of `normie3`. -/
def n3Slow (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (p j : Fin 2) (x : Vec 2) : ℝ :=
  I.xiMK m k t * ∑ i : Fin 2,
    flowGradK I hΦ m k t x p i * gradG I hΦ m T (lIdx β I.Λ m k) t x i j

theorem n3Slow_zero (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (p j : Fin 2) (h : I.xiMK m k t = 0) : n3Slow I hΦ m T k t p j = fun _ => 0 := by
  funext x
  simp [n3Slow, h]

/-- Termwise component form of `normie3`. -/
theorem n3_term_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    I.xiMK m k t * frob
      ((flowGradK I hΦ m k t x).transpose * (I.flux κm m t - cellFlux I hΦ m κm k t x))
      (gradG I hΦ m T (lIdx β I.Λ m k) t x) =
      ∑ p : Fin 2, ∑ j : Fin 2,
        n3Fast I κm m k t p j (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) *
          n3Slow I hΦ m T k t p j x := by
  by_cases hξ : I.xiMK m k t = 0
  · simp [hξ, n3Slow]
  · simp only [n3Fast_of_xi_ne_zero I κm k t _ _ hξ, LeftJacobian.cellFlux_eq_cellFluxCell_comp,
      frob, n3Slow, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
      Fin.sum_univ_two, flowGradK]
    ring

/-- Finite-sum form of `normie3` over any set containing the support of `ξ_{m,·}(t)`. -/
theorem normie3_eq_sum (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (S : Finset {k : ℤ // Odd k})
    (hS : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → k ∈ S) (x : Vec 2) :
    normie3 I hΦ m κm T t x =
      ∑ k ∈ S, ∑ p : Fin 2, ∑ j : Fin 2,
        n3Fast I κm m k.1 t p j (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) *
          n3Slow I hΦ m T k.1 t p j x := by
  unfold normie3
  rw [sd_tsum_eq_sum S (fun k hk => hS k fun h => hk (by simp [h]))]
  exact Finset.sum_congr rfl fun k _ => n3_term_eq I hΦ m κm T k.1 t x

/-! ### Smoothness and periodicity -/

theorem n3Slow_smooth_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) (k : ℤ) (p j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (n3Slow I hΦ m T k t p j) ∧
      Infra.Ergodic.IsZPeriodic (n3Slow I hΦ m T k t p j) := by
  have hmain : ContDiff ℝ (⊤ : ℕ∞) (n3Slow I hΦ m T k t p j) ∧
      IsZ2Periodic (n3Slow I hΦ m T k t p j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => I.xiMK m k t * ∑ i : Fin 2,
        I.flowGrad hΦ m (lIdx β I.Λ m k) t x p i * gradG I hΦ m T (lIdx β I.Λ m k) t x i j) ∧
      IsZ2Periodic (fun x => I.xiMK m k t * ∑ i : Fin 2,
        I.flowGrad hΦ m (lIdx β I.Λ m k) t x p i * gradG I hΦ m T (lIdx β I.Λ m k) t x i j)
    refine ⟨contDiff_const.mul (ContDiff.sum fun i _ => ?_),
      sds_isZ2Periodic_const_mul _ (sds_isZ2Periodic_sum _ fun i _ => ?_)⟩
    · exact (sdj_contDiff_flowGrad_entry (I := I) hΦ m _ t p i).mul
        (tf_gradG_slice_contDiff I hΦ m T t _ hTt i j)
    · exact sds_isZ2Periodic_mul (sds_flowGrad_periodic I hΦ m _ t p i)
        (tf_gradG_slice_periodic I hΦ m T t _ hTp i j)
  exact ⟨hmain.1, sds_isZPeriodic_of_isZ2Periodic hmain.2⟩

/-! ### Pointwise bound -/

/-- Squaring step: `|f| ≤ 8 h₀ + 8 h₁ + 32 (2^16 q) g` gives `f² ≤ (2^22 q)² g² + 14² (h₀² +
    h₁²)`. -/
theorem n3_slow_sq {f q gT h0 h1 : ℝ} (hq : 0 ≤ q) (hg : 0 ≤ gT) (h0n : 0 ≤ h0) (h1n : 0 ≤ h1)
    (hf : |f| ≤ 8 * h0 + 8 * h1 + 32 * (2 ^ 16 * q) * gT) :
    f ^ 2 ≤ (2 ^ 22 * q) ^ 2 * gT ^ 2 + 14 ^ 2 * (h0 ^ 2 + h1 ^ 2) := by
  have hb : 0 ≤ 8 * h0 + 8 * h1 + 32 * (2 ^ 16 * q) * gT := by positivity
  have hf2 : f ^ 2 ≤ (8 * h0 + 8 * h1 + 32 * (2 ^ 16 * q) * gT) ^ 2 := by
    have := sq_le_sq' (abs_le.1 hf).1 (abs_le.1 hf).2
    simpa using this
  have h3 := sa_sq3 (8 * h0) (8 * h1) (32 * (2 ^ 16 * q) * gT)
  have hq2 : 0 ≤ (q * gT) ^ 2 := sq_nonneg _
  have hh0 : 0 ≤ h0 ^ 2 := sq_nonneg _
  have hh1 : 0 ≤ h1 ^ 2 := sq_nonneg _
  have e1 : 3 * ((8 * h0) ^ 2 + (8 * h1) ^ 2 + (32 * (2 ^ 16 * q) * gT) ^ 2) =
      192 * h0 ^ 2 + 192 * h1 ^ 2 + 3 * 2 ^ 42 * (q * gT) ^ 2 := by ring
  have e2 : (2 ^ 22 * q) ^ 2 * gT ^ 2 = 2 ^ 44 * (q * gT) ^ 2 := by ring
  rw [e2]
  nlinarith [hf2, h3, e1, hq2, hh0, hh1]

/-- **Pointwise bound of the slow factor** of `normie3`: with `ε = ε_{m-1}`,
`slow² ≲ ε⁻² |∇T|² + |∇∂_0T|² + |∇∂_1T|²` (no small factor). -/
theorem n3_slow_pointwise (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (T : ℝ → Vec 2 → ℝ)
    {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (k : ℤ) (p j : Fin 2) (x : Vec 2) :
    (n3Slow I hΦ m T k t p j x) ^ 2 ≤
      (2 ^ 22 * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 * vecNormSq (spaceGrad (T t) x) +
        14 ^ 2 * (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) +
          vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x)) := by
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
  have hq0 : 0 ≤ q := inv_nonneg.2 (epsilon_pos' I _).le
  have hgn : 0 ≤ gT := Real.sqrt_nonneg _
  have hh0n : 0 ≤ h0 := Real.sqrt_nonneg _
  have hh1n : 0 ≤ h1 := Real.sqrt_nonneg _
  have hxi := Infra.Section3.xiMK_mem_Icc I (by omega : 1 ≤ m) k t
  rw [← hsq0, ← hsq1, ← hsq2]
  by_cases hξ : I.xiMK m k t = 0
  · rw [n3Slow_zero I hΦ m T k t p j hξ]
    have : 0 ≤ (2 ^ 22 * q) ^ 2 * gT ^ 2 + 14 ^ 2 * (h0 ^ 2 + h1 ^ 2) := by positivity
    simpa using this
  · refine n3_slow_sq hq0 hgn hh0n hh1n ?_
    have hF : ∀ u v, |flowGradK I hΦ m k t x u v| ≤ 2 := fun u v =>
      abs_le_two_of_sub_one (scf_e_le_one I) (fun u v => flowGrad_sub_one_le hΦ hm k hξ x u v) u v
    have key : ∀ i, |gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
        2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT := fun i => by
      simpa using scf_gradG_abs_le I hΦ hm hTt hξ x hg hhh i j
    have hS : |∑ i : Fin 2, flowGradK I hΦ m k t x p i *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
        4 * (2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT) := by
      simp only [Fin.sum_univ_two]
      have := abs_add_le_of_le (abs_mul_le_of_le (hF p 0) (key 0))
        (abs_mul_le_of_le (hF p 1) (key 1))
      linarith
    unfold n3Slow
    rw [abs_mul]
    have hxi' : |I.xiMK m k t| ≤ 1 := by
      rw [abs_of_nonneg hxi.1]
      exact hxi.2
    calc |I.xiMK m k t| * |∑ i : Fin 2, flowGradK I hΦ m k t x p i *
          gradG I hΦ m T (lIdx β I.Λ m k) t x i j|
        ≤ 1 * (4 * (2 * (h0 + h1) + 8 * (2 ^ 16 * q) * gT)) :=
          mul_le_mul hxi' hS (abs_nonneg _) zero_le_one
      _ = 8 * h0 + 8 * h1 + 32 * (2 ^ 16 * q) * gT := by ring

end AVenhance.Infra.Section5.Contracts
end
