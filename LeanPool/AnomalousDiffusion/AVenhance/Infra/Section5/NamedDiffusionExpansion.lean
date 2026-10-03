/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SelectedDiffusionDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SelectedDiffusionFluxSubtype
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum

/-! The selected diffusion divergence written in the named Section 5.1 terms. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- Expand the ansatz diffusion divergence into the selected
corrector contributions and the named mismatch, chi-gradient, and `H_m`
terms. The differentiability assumptions are local product-rule inputs. -/
theorem frozen_ansatz_diffusion_named_expansion
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (hT : ∀ y, HasFDerivAt (T t) (fderiv ℝ (T t) y) y)
    (hH : ∀ y, HasFDerivAt (I.Hm hΦ m κ T t)
      (fderiv ℝ (I.Hm hΦ m κ T t) y) y)
    (hχ : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
      HasFDerivAt (I.chiTilde hΦ m κ k t)
        (fderiv ℝ (I.chiTilde hΦ m κ k t) y) y)
    (hGglobal : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
      HasFDerivAt (fun z => G I hΦ m T (lIdx β I.Λ m k) t z)
        (fderiv ℝ (fun z => G I hΦ m T (lIdx β I.Λ m k) t z) y) y)
    (hB : ∀ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      ∀ i j, HasFDerivAt (fun y => correctorFlux I hΦ m κ q.1 t y i j)
        (fderiv ℝ (fun y => correctorFlux I hΦ m κ q.1 t y i j) x) x)
    (hG : ∀ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      HasFDerivAt (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y)
        (fderiv ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x) x)
    {LM LC LH : Vec 2 →L[ℝ] Vec 2}
    (hM : HasFDerivAt (fun y =>
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y -
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t •
              G I hΦ m T (lIdx β I.Λ m q.1) t y)) LM x)
    (hC : HasFDerivAt (fun y =>
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t •
          (diffusionMatrix I hΦ m κ t y).mulVec
            (chiGradG I hΦ m κ T q.1 t y)) LC x)
    (hHflux : HasFDerivAt (fun y =>
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.Hm hΦ m κ T t) y)) LH x) :
    vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.ansatz hΦ m κ T t) y)) x =
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t *
          (vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
              (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
            vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
              (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
            frob (correctorFlux I hΦ m κ q.1 t x)
              (gradMatrix (G I hΦ m T (lIdx β I.Λ m q.1) t) x) +
            vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
              (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
              (G I hΦ m T (lIdx β I.Λ m q.1) t x))) -
      twistie3 I hΦ m κ T t x - normie1 I hΦ m κ T t x -
        normie2 I hΦ m κ T t x := by
  classical
  let S := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hxi (q : {k : ℤ // Odd k}) (hq : q ∈ S) :
      I.xiMK m q.1 t ≠ 0 := by
    exact (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mp hq
  have hpartition : ∑ q ∈ S, I.xiMK m q.1 t = 1 := by
    dsimp [S]
    calc
      _ = ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
          I.xiMK m q.1 t • (1 : ℝ) := by simp
      _ = ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t • (1 : ℝ) :=
        (xiMK_odd_tsum_eq_subtype_support_sum I m hm t
          (fun _ : {k : ℤ // Odd k} => (1 : ℝ))).symm
      _ = 1 := by
        simpa using AVenhance.Infra.Section3.xiMK_odd_partition I hm t
  have hflux := frozen_ansatz_diffusion_flux_decomposition_odd_support
    I hΦ m hm κ T t hT hH hχ hGglobal
  have hbase := selected_ansatz_diffusion_divergence I hΦ m hm κ T t x
    S hxi hB hG hM hC hHflux hflux
  let mismatch : Vec 2 → Vec 2 := fun y =>
    (diffusionMatrix I hΦ m κ t y).mulVec
      (spaceGrad (T t) y -
        ∑ q ∈ S, I.xiMK m q.1 t •
          G I hΦ m T (lIdx β I.Λ m q.1) t y)
  let chiField : Vec 2 → Vec 2 := fun y =>
    ∑ q ∈ S, I.xiMK m q.1 t •
      (diffusionMatrix I hΦ m κ t y).mulVec
        (chiGradG I hΦ m κ T q.1 t y)
  let hField : Vec 2 → Vec 2 := fun y =>
    (diffusionMatrix I hΦ m κ t y).mulVec
      (spaceGrad (I.Hm hΦ m κ T t) y)
  have hmix (y : Vec 2) :
      mismatch y = ∑ q ∈ S, I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m q.1) t y) := by
    dsimp [mismatch]
    ext i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpartition]
    ring
  have hmisField : mismatch = fun y =>
      ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m q.1) t y) := by
    funext y
    rw [hmix]
    symm
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m q.1) t y))
  have hchiField : chiField = fun y =>
      ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κ t y).mulVec
          (chiGradG I hΦ m κ T q.1 t y) := by
    funext y
    dsimp [chiField]
    change (∑ q ∈ S, I.xiMK m q.1 t •
      (diffusionMatrix I hΦ m κ t y).mulVec
        (chiGradG I hΦ m κ T q.1 t y)) = _
    symm
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => (diffusionMatrix I hΦ m κ t y).mulVec
        (chiGradG I hΦ m κ T q.1 t y))
  have hmis : vecDiv mismatch x =
      -twistie3 I hΦ m κ T t x := by
    rw [hmisField]
    simp [twistie3]
  have hchiDiv : vecDiv chiField x =
      -normie1 I hΦ m κ T t x := by
    rw [hchiField]
    simp [normie1]
  have hHdiv : vecDiv hField x =
      -normie2 I hΦ m κ T t x := by
    change vecDiv hField x = -(-vecDiv hField x)
    ring
  rw [hbase]
  rw [hmis, hchiDiv, hHdiv]
  ring

end AVenhance.Infra.Section5

end
