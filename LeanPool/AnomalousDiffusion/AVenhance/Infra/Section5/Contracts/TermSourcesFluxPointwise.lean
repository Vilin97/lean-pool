/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorLocalization
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterialRates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi

/-! # Pointwise bounds for the `twistie3`, `normie1`, `normie2` fluxes

At a fixed time `t > 0` and point `x`, with `μ = κ_m + a_m ε_m²`:

* `|D(t,x)_{ij}| ≤ μ` for the diffusion matrix on the support of any odd `ξ_{m,k}`;
* `∑_k ξ_{m,k} = 1`, `0 ≤ ξ_{m,k}` turn the `k`-uniform entry bound into a bound of the flux;
* `twistie3`: `∇T − G_{l_k} = −(∇X∘X⁻¹ − I)∇T` (source `e.monster.est.7`);
* `normie1`: `ΧTilde_k ∇G_{l_k}` is the Hessian remainder of the leading-error work
  (source `e.monster.est.10`);
* `normie2`: `D ∇HTilde_m` (source `e.monster.est.11`).

The conclusions are squared-norm bounds `|flux|² ≤ ∑_j c_j |V_j|²` in the shape consumed by
`saTimeL2_le`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Section5.Integration

theorem sa_vecNormSq_eq (v : Vec 2) : vecNormSq v = v 0 * v 0 + v 1 * v 1 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two]

theorem sa_vecNormSq_le {v : Vec 2} {W : ℝ} (h : ∀ i, |v i| ≤ W) : vecNormSq v ≤ 2 * W ^ 2 := by
  rw [sa_vecNormSq_eq]
  have h0 : v 0 ^ 2 ≤ W ^ 2 := sq_le_sq' (abs_le.1 (h 0)).1 (abs_le.1 (h 0)).2
  have h1 : v 1 ^ 2 ≤ W ^ 2 := sq_le_sq' (abs_le.1 (h 1)).1 (abs_le.1 (h 1)).2
  nlinarith

theorem sa_sq3 (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

theorem sa_sigma_abs_le (i j : Fin 2) : |sigmaMat i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [sigmaMat]

theorem sa_one_abs_le (i j : Fin 2) : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- On the support of an odd `ξ_{m,k}` the diffusion matrix has entries at most `κ_m + a_m ε_m²`. -/
theorem sa_diffusion_entry_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {k : ℤ} (hk : Odd k) {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2)
    (i j : Fin 2) :
    |diffusionMatrix I hΦ m κm t x i j| ≤ κm + a β I.Λ m * epsilon β I.Λ m ^ 2 := by
  have hψ : |psiTilde I hΦ m t x| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := by
    rw [psiTilde_eq_selected_mode I hΦ m hm k t x hk hξ, abs_mul]
    have hz := Infra.Section3.zetaProd_mem_Icc I hm k t
    rw [abs_of_nonneg hz.1]
    calc I.zetaProd m k t * |psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)|
        ≤ 1 * (a β I.Λ m * epsilon β I.Λ m ^ 2) :=
          mul_le_mul hz.2 (Infra.Section4.amnr_psi_abs_le I m k _) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hentry : diffusionMatrix I hΦ m κm t x i j =
      κm * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + psiTilde I hΦ m t x * sigmaMat i j := by
    simp [diffusionMatrix]
  rw [hentry]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos hκ]
    calc κm * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ κm * 1 :=
        mul_le_mul_of_nonneg_left (sa_one_abs_le i j) hκ.le
      _ = κm := mul_one _
  · rw [abs_mul]
    calc |psiTilde I hΦ m t x| * |sigmaMat i j| ≤ _ * 1 :=
        mul_le_mul_of_nonneg_left (sa_sigma_abs_le i j) (abs_nonneg _)
      _ = _ := mul_one _
      _ ≤ _ := hψ

/-- A cutoff is nonzero for some odd index at every time. -/
theorem sa_exists_xi_ne_zero {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∃ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := Infra.Section3.xiMK_odd_partition_finset I hm t
  simp only [hcon, Finset.sum_const_zero] at h
  exact zero_ne_one h

/-- **Convex-combination bound.** -/
theorem sa_tsum_abs_le {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (w : {k : ℤ // Odd k} → Vec 2) (W : ℝ)
    (hw : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ i, |w k i| ≤ W) (i : Fin 2) :
    |(∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t • w k) i| ≤ W := by
  classical
  set U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset with hU
  have hzero : ∀ k ∉ U, I.xiMK m k.1 t • w k = 0 := by
    intro k hk
    have : I.xiMK m k.1 t = 0 := by
      by_contra hne
      exact hk (by simpa [hU] using hne)
    simp [this]
  rw [tsum_eq_sum (L := SummationFilter.unconditional {k : ℤ // Odd k}) (s := U) hzero]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ U, |I.xiMK m k.1 t * w k i| ≤ I.xiMK m k.1 t * W := by
    intro k hk
    have hk' : I.xiMK m k.1 t ≠ 0 := by simpa [hU] using hk
    rw [abs_mul, abs_of_nonneg (xiMK_nonneg' I m k.1 t)]
    exact mul_le_mul_of_nonneg_left (hw k hk' i) (xiMK_nonneg' I m k.1 t)
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [← Finset.sum_mul, Infra.Section3.xiMK_odd_partition_finset I hm t, one_mul]

/-! ### `twistie3` -/

theorem sa_gradT_sub_G_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {T : ℝ → Vec 2 → ℝ}
    {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (k : ℤ) (hξ : I.xiMK m k t ≠ 0) (x : Vec 2)
    {gT : ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT) (j : Fin 2) :
    |(spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k) t x) j| ≤
      2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * gT := by
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hX := (((contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp))
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
  have hG := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x hT hX
    (xFlow_xFlowInv I hΦ m _ t x)
  have hid : spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k) t x =
      -((I.flowGrad hΦ m (lIdx β I.Λ m k) t x - 1).mulVec (spaceGrad (T t) x)) := by
    rw [hG, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hid, Pi.neg_apply, abs_neg]
  exact abs_mulVec_le (fun u v => flowGrad_sub_one_le hΦ hm k hξ x u v) hg j

theorem sa_twistie3Flux_vecNormSq_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) :
    vecNormSq (twistie3Flux I hΦ m κm T t x) ≤
      (6 * ((κm + a β I.Λ m * epsilon β I.Λ m ^ 2) *
        epsilon β I.Λ (m - 1) ^ (2 * delta β))) ^ 2 * vecNormSq (spaceGrad (T t) x) := by
  set μ := κm + a β I.Λ m * epsilon β I.Λ m ^ 2 with hμ
  set e := epsilon β I.Λ (m - 1) ^ (2 * delta β) with he
  set gT := Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hgT
  have hg : ∀ p, |spaceGrad (T t) x p| ≤ gT := fun p => abs_apply_le_sqrt_vecNormSq _ p
  have hsq : gT ^ 2 = vecNormSq (spaceGrad (T t) x) := Real.sq_sqrt (vecNormSq_nonneg _)
  have hcomp : ∀ i, |twistie3Flux I hΦ m κm T t x i| ≤ 4 * μ * e * gT := by
    intro i
    unfold twistie3Flux
    refine (sa_tsum_abs_le I (by omega) t _ _ ?_ i).trans_eq rfl
    intro k hk j
    have hk' := k.2
    have hD := abs_mulVec_le (M := diffusionMatrix I hΦ m κm t x) (μ := μ)
      (fun u v => sa_diffusion_entry_le I hΦ (by omega) hκ hk' hk x u v)
      (fun p => sa_gradT_sub_G_abs_le I hΦ hm hTt k.1 hk x hg p) j
    refine hD.trans_eq ?_
    ring
  have h2 := sa_vecNormSq_le hcomp
  refine h2.trans ?_
  rw [← hsq]
  nlinarith [sq_nonneg (μ * e * gT)]

/-! ### `normie2` -/

theorem sa_normie2Flux_vecNormSq_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    vecNormSq (normie2Flux I hΦ m κm T t x) ≤
      (3 * (κm + a β I.Λ m * epsilon β I.Λ m ^ 2)) ^ 2 *
        vecNormSq (spaceGrad (fun z => I.Hm hΦ m κm T t z) x) := by
  set μ := κm + a β I.Λ m * epsilon β I.Λ m ^ 2 with hμ
  set g := spaceGrad (fun z => I.Hm hΦ m κm T t z) x with hg
  set gT := Real.sqrt (vecNormSq g) with hgT
  have hgb : ∀ p, |g p| ≤ gT := fun p => abs_apply_le_sqrt_vecNormSq _ p
  have hsq : gT ^ 2 = vecNormSq g := Real.sq_sqrt (vecNormSq_nonneg _)
  obtain ⟨k, hk⟩ := sa_exists_xi_ne_zero I (by omega : 1 ≤ m) t
  have hcomp : ∀ i, |normie2Flux I hΦ m κm T t x i| ≤ 2 * μ * gT := fun i =>
    abs_mulVec_le (M := diffusionMatrix I hΦ m κm t x) (μ := μ)
      (fun u v => sa_diffusion_entry_le I hΦ (by omega) hκ k.2 hk x u v) hgb i
  have h2 := sa_vecNormSq_le hcomp
  refine h2.trans ?_
  rw [← hsq]
  nlinarith [sq_nonneg (μ * gT)]

/-! ### `normie1` -/

/-- `ΧTilde_{m,k} ∇G_{l_k}` is the Hessian remainder field of the leading-error work. -/
theorem sa_chiGradG_eq_hessian (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (k : ℤ) (x : Vec 2) (i : Fin 2) :
    chiGradG I hΦ m κm T k t x i = leadingErrHessian I hΦ m κm T k t x i := by
  unfold chiGradG leadingErrHessian
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := spaceGrad_G_component I hΦ m T (lIdx β I.Λ m k) hTt x i j
  have hg : gradG I hΦ m T (lIdx β I.Λ m k) t x i j =
      spaceGrad (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i := rfl
  rw [hg, h]
  rfl

theorem sa_chiGradG_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (k : ℤ)
    (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) {gT : ℝ} {h : Fin 2 → ℝ}
    (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT)
    (hh : ∀ i p, |spaceHess (T t) x i p| ≤ h p) (i : Fin 2) :
    |chiGradG I hΦ m κm T k t x i| ≤
      epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
        (4 * (h 0 + h 1) + 16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT) := by
  rw [sa_chiGradG_eq_hessian I hΦ m κm hTt k x i]
  have he1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one (epsilon_pos' I _).le (epsilon_le_one' I _)
      (by linarith [delta_pos' I])
  have hA := gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ x
  have hFl := flowGrad_sub_one_le hΦ hm k hξ x
  have hχ : ∀ j, |I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j| ≤
      epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) := fun j =>
    (Infra.Section3.chiMK_component_abs_le I (by omega) κm hκ k t _ j).trans
      (corrector_size_le (a_nonneg' I m) (epsilon_pos' I m) hκ)
  have hA2 := abs_le_two_of_sub_one he1 (fun u v => hA u v)
  have hFl2 := abs_le_two_of_sub_one he1 (fun u v => hFl u v)
  exact hessian_component_le (χ := I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (g := spaceGrad (T t) x) (Fl := I.flowGrad hΦ m (lIdx β I.Λ m k) t x)
    (a := fun q => gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i q)
    (Dd := fun p j q => xFlowHess I hΦ m (lIdx β I.Λ m k) t
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j q)
    (Hs := fun p => spaceHess (T t) x i p) (h := h) hχ (fun j p => hFl2 j p)
    (fun q => hA2 i q) (fun p j q => abs_xFlowHess_le hΦ hm k hξ _ p j q) (fun p => hh i p) hg

theorem sa_normie1Flux_vecNormSq_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) :
    vecNormSq (normie1Flux I hΦ m κm T t x) ≤
      (40 * (2 * ((κm + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm))) *
        (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹))) ^ 2 * vecNormSq (spaceGrad (T t) x) +
    (10 * (2 * ((κm + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm))))) ^ 2 *
        vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x) +
    (10 * (2 * ((κm + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm))))) ^ 2 *
        vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x) := by
  set μ := κm + a β I.Λ m * epsilon β I.Λ m ^ 2 with hμ
  set cχ := epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) with hcχ
  set Dd := 2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ with hDd
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
  have hμ0 : 0 ≤ μ := by
    have := a_nonneg' I m
    have := epsilon_pos' I m
    positivity
  have hc0 : 0 ≤ cχ := by
    have := a_nonneg' I m
    have := epsilon_pos' I m
    positivity
  have hD0 : 0 ≤ Dd := by
    have := epsilon_pos' I (m - 1)
    positivity
  have hh0n : 0 ≤ h0 := Real.sqrt_nonneg _
  have hh1n : 0 ≤ h1 := Real.sqrt_nonneg _
  have hgn : 0 ≤ gT := Real.sqrt_nonneg _
  set u := 2 * (μ * cχ) with hu
  have hcomp : ∀ i, |normie1Flux I hΦ m κm T t x i| ≤
      u * (4 * h0 + 4 * h1 + 16 * Dd * gT) := by
    intro i
    unfold normie1Flux
    refine (sa_tsum_abs_le I (by omega) t _ _ ?_ i).trans_eq rfl
    intro k hk j
    have hk' := k.2
    have hD := abs_mulVec_le (M := diffusionMatrix I hΦ m κm t x) (μ := μ)
      (fun u v => sa_diffusion_entry_le I hΦ (by omega) hκ hk' hk x u v)
      (fun p => sa_chiGradG_abs_le I hΦ hm hκ hTt k.1 hk x hg hhh p) j
    refine hD.trans_eq ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hu]
    ring
  have h2 := sa_vecNormSq_le hcomp
  refine h2.trans ?_
  rw [← hsq0, ← hsq1, ← hsq2]
  have h3 := sa_sq3 (4 * h0) (4 * h1) (16 * Dd * gT)
  have hu0 : 0 ≤ u := by positivity
  have key : (4 * h0 + 4 * h1 + 16 * Dd * gT) ^ 2 ≤
      48 * h0 ^ 2 + 48 * h1 ^ 2 + 768 * Dd ^ 2 * gT ^ 2 := by nlinarith [h3]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  calc 2 * (u * (4 * h0 + 4 * h1 + 16 * Dd * gT)) ^ 2
      = 2 * u ^ 2 * (4 * h0 + 4 * h1 + 16 * Dd * gT) ^ 2 := by ring
    _ ≤ 2 * u ^ 2 * (48 * h0 ^ 2 + 48 * h1 ^ 2 + 768 * Dd ^ 2 * gT ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ _ := by
        have e1 : 0 ≤ u ^ 2 * h0 ^ 2 := by positivity
        have e2 : 0 ≤ u ^ 2 * h1 ^ 2 := by positivity
        have e3 : 0 ≤ u ^ 2 * Dd ^ 2 * gT ^ 2 := by positivity
        nlinarith [e1, e2, e3]

end AVenhance.Infra.Section5.Contracts
end
