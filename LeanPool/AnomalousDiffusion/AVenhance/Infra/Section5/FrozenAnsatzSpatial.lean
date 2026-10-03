/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnsatzGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain

/-! Fixed-time spatial differentiation of the cutoff ansatz. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- At a fixed time the ansatz series is exactly a finite sum over the
support of `xiMK`; the spatial gradient therefore follows from the ordinary
finite-sum product rule. -/
theorem ansatz_spaceGrad
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    {LT LH : Vec 2 →L[ℝ] ℝ} (LP : ℤ → Vec 2 →L[ℝ] ℝ)
    (hT : HasFDerivAt (T t) LT x)
    (hH : HasFDerivAt (I.Hm hΦ m κm T t) LH x)
    (hP : ∀ k ∈ (I.xiMK_support_finite m t).toFinset,
      HasFDerivAt
        (fun y => vecDot (I.chiTilde hΦ m κm k t y)
          (G I hΦ m T (lIdx β I.Λ m k) t y))
        (LP k) x)
    (i : Fin 2) :
    spaceGrad (I.ansatz hΦ m κm T t) x i =
      spaceGrad (T t) x i +
        (∑ k ∈ (I.xiMK_support_finite m t).toFinset,
          I.xiMK m k t * spaceGrad
            (fun y => vecDot (I.chiTilde hΦ m κm k t y)
              (G I hΦ m T (lIdx β I.Λ m k) t y)) x i) +
        spaceGrad (I.Hm hΦ m κm T t) x i := by
  let S : Finset ℤ := (I.xiMK_support_finite m t).toFinset
  let P : ℤ → Vec 2 → ℝ := fun k y =>
    vecDot (I.chiTilde hΦ m κm k t y)
      (G I hΦ m T (lIdx β I.Λ m k) t y)
  have hzero (k : ℤ) (hk : k ∉ S) : I.xiMK m k t = 0 := by
    by_contra hne
    exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)
  have hseries (y : Vec 2) :
      (∑' k : ℤ, I.xiMK m k t * P k y) =
        ∑ k ∈ S, I.xiMK m k t * P k y := by
    apply tsum_eq_sum (s := S)
    intro k hk
    simp [hzero k hk]
  have hseriesG (y : Vec 2) :
      (∑' k : ℤ, I.xiMK m k t *
        vecDot (I.chiTilde hΦ m κm k t y)
          (spaceGrad (fun z => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t z))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) =
        ∑ k ∈ S, I.xiMK m k t * P k y := by
    simpa [P, G] using hseries y
  have hrepr : I.ansatz hΦ m κm T t =
      fun y => T t y + (∑ k ∈ S, I.xiMK m k t * P k y) +
        I.Hm hΦ m κm T t y := by
    funext y
    simp only [Ingredients.ansatz]
    rw [hseriesG y]
  rw [hrepr]
  exact spaceGrad_finiteWeightedSum S (T t) (I.Hm hΦ m κm T t)
    (fun k => I.xiMK m k t) P x LP hT hH
    (by simpa [P, S] using hP) i

/-- Corrected line-2 spatial expansion of the ansatz. The finite sum
uses the selected flow `l_k` in both the corrector and the pulled gradient. -/
theorem ansatz_spaceGrad_expanded
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    {LT LH : Vec 2 →L[ℝ] ℝ}
    (Lχ LG : ℤ → Vec 2 →L[ℝ] Vec 2)
    (hT : HasFDerivAt (T t) LT x)
    (hH : HasFDerivAt (I.Hm hΦ m κm T t) LH x)
    (hχ : ∀ k ∈ (I.xiMK_support_finite m t).toFinset,
      HasFDerivAt (I.chiTilde hΦ m κm k t) (Lχ k) x)
    (hG : ∀ k ∈ (I.xiMK_support_finite m t).toFinset,
      HasFDerivAt (fun y => G I hΦ m T (lIdx β I.Λ m k) t y)
        (LG k) x)
    (i : Fin 2) :
    spaceGrad (I.ansatz hΦ m κm T t) x i =
      spaceGrad (T t) x i +
        (∑ k ∈ (I.xiMK_support_finite m t).toFinset,
          I.xiMK m k t *
            ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
                (G I hΦ m T (lIdx β I.Λ m k) t x) i +
              ∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
                spaceGrad
                  (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i)) +
        spaceGrad (I.Hm hΦ m κm T t) x i := by
  let S := (I.xiMK_support_finite m t).toFinset
  let P : ℤ → Vec 2 → ℝ := fun k y =>
    vecDot (I.chiTilde hΦ m κm k t y)
      (G I hΦ m T (lIdx β I.Λ m k) t y)
  let LP : ℤ → Vec 2 →L[ℝ] ℝ := fun k =>
    vecDotDerivativeAt
      (χ := I.chiTilde hΦ m κm k t)
      (G := G I hΦ m T (lIdx β I.Λ m k) t)
      x (Lχ k) (LG k)
  have hP : ∀ k ∈ S, HasFDerivAt (P k) (LP k) x := by
    intro k hk
    exact hasFDerivAt_vecDot (hχ k (by simpa [S] using hk))
      (hG k (by simpa [S] using hk))
  have hbase := ansatz_spaceGrad I hΦ m κm T t x LP hT hH hP i
  have hsum :
      (∑ k ∈ S, I.xiMK m k t * spaceGrad (P k) x i) =
        ∑ k ∈ S, I.xiMK m k t *
          ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t x) i +
            ∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
              spaceGrad
                (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [spaceGrad_vecDot
      (hχ k (by simpa [S] using hk))
      (hG k (by simpa [S] using hk)) i]
  have hbaseP :
      spaceGrad (I.ansatz hΦ m κm T t) x i =
        spaceGrad (T t) x i +
          (∑ k ∈ S, I.xiMK m k t * spaceGrad (P k) x i) +
          spaceGrad (I.Hm hΦ m κm T t) x i := by
    simpa [P, S] using hbase
  have hadd :
      (spaceGrad (T t) x i +
          (∑ k ∈ S, I.xiMK m k t * spaceGrad (P k) x i)) +
          spaceGrad (I.Hm hΦ m κm T t) x i =
        (spaceGrad (T t) x i +
          (∑ k ∈ S, I.xiMK m k t *
            ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
                (G I hΦ m T (lIdx β I.Λ m k) t x) i +
              ∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
                spaceGrad
                  (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i))) +
          spaceGrad (I.Hm hΦ m κm T t) x i := by
    rw [hsum]
  simpa only [S, P] using hbaseP.trans hadd

end AVenhance.Infra.Section5

end
