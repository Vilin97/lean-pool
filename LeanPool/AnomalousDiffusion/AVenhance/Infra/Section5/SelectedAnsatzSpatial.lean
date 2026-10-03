/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenAnsatzSpatial

/-! The exact selected-flow spatial gradient of the line-2 ansatz. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem SelectedAnsatzSpatial.chiMK_eq_zero_of_not_odd (κ : ℝ) (m : ℕ) (k : ℤ)
    (hk : ¬ Odd k) (t : ℝ) : I.chiMK κ m k t = 0 := by
  have h1 : k % 4 ≠ 1 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  have h3 : k % 4 ≠ 3 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  have hu : uShear β I.Λ m k = fun _ => 0 := by
    funext x
    simp [uShear, h1, h3]
  funext x
  simp [Ingredients.chiMK, hu]

theorem SelectedAnsatzSpatial.chiTilde_eq_zero_of_not_odd (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (hk : ¬ Odd k) (t : ℝ) :
    I.chiTilde hΦ m κ k t = fun _ => 0 := by
  funext x
  simp [Ingredients.chiTilde, SelectedAnsatzSpatial.chiMK_eq_zero_of_not_odd I κ m k hk t]

/-- The gradient of the ansatz, reorganized into its selected odd
flows. The mismatch flux is kept explicitly as
`∇T - Σ_{k odd} ξ_{m,k} G_{l_k}`; together with the selected corrector fluxes
this is exactly the line-2 gradient. -/
theorem ansatz_spaceGrad_selected
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
      (∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
        I.xiMK m k t *
          ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t x) i +
            G I hΦ m T (lIdx β I.Λ m k) t x i)) +
      (spaceGrad (T t) x i -
        ∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
          I.xiMK m k t * G I hΦ m T (lIdx β I.Λ m k) t x i) +
      (∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
        I.xiMK m k t *
          (∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
            spaceGrad (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i)) +
      spaceGrad (I.Hm hΦ m κm T t) x i := by
  let S := (I.xiMK_support_finite m t).toFinset
  let p : ℤ → Prop := Odd
  let a : ℤ → ℝ := fun k => I.xiMK m k t *
    (gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t x) i
  let c : ℤ → ℝ := fun k => I.xiMK m k t *
    ∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
      spaceGrad (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i
  let g : ℤ → ℝ := fun k => I.xiMK m k t *
    G I hΦ m T (lIdx β I.Λ m k) t x i
  have heven (k : ℤ) (hk : ¬ Odd k) : a k + c k = 0 := by
    have hχ := SelectedAnsatzSpatial.chiTilde_eq_zero_of_not_odd I hΦ m κm k hk t
    have hχx : I.chiTilde hΦ m κm k t x = 0 := by rw [hχ]
    have hgradχ : gradMatrix (I.chiTilde hΦ m κm k t) x = 0 := by
      ext p q
      change spaceGrad (fun y => I.chiTilde hΦ m κm k t y q) x p = 0
      rw [hχ]
      simp [spaceGrad]
    simp only [a, c, hχx, hgradχ, Matrix.zero_mulVec, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    ring
  have hsumOdd : (∑ k ∈ S, (a k + c k)) =
      ∑ k ∈ S.filter p, (a k + c k) := by
    have hnotSum :
        (∑ k ∈ S.filter (fun k => ¬ p k), (a k + c k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact heven k (Finset.mem_filter.mp hk |>.2)
    rw [← Finset.sum_filter_add_sum_filter_not S p (fun k => a k + c k)]
    rw [hnotSum]
    simp
  have hsplit : (∑ k ∈ S.filter p, (a k + c k)) =
      (∑ k ∈ S.filter p, a k) + (∑ k ∈ S.filter p, c k) := by
    rw [← Finset.sum_add_distrib]
  have hselected :
      (∑ k ∈ S.filter p, I.xiMK m k t *
        ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t x) i +
          G I hΦ m T (lIdx β I.Λ m k) t x i)) =
        (∑ k ∈ S.filter p, a k) + (∑ k ∈ S.filter p, g k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp [a, g]
    ring
  have hcompress :
      (∑ k ∈ S, (a k + c k)) =
        (∑ k ∈ S.filter p, a k) + (∑ k ∈ S.filter p, c k) := by
    rw [hsumOdd, hsplit]
  have hbase := ansatz_spaceGrad_expanded I hΦ m κm T t x Lχ LG
    hT hH hχ hG i
  change spaceGrad (I.ansatz hΦ m κm T t) x i = _ at hbase
  rw [hbase]
  have hrewrite :
      (∑ k ∈ S, I.xiMK m k t *
        ((gradMatrix (I.chiTilde hΦ m κm k t) x).mulVec
          (G I hΦ m T (lIdx β I.Λ m k) t x) i +
          ∑ j : Fin 2, I.chiTilde hΦ m κm k t x j *
            spaceGrad (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i)) =
        ∑ k ∈ S, (a k + c k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [a, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hrewrite]
  rw [hcompress]
  simp only [S, p]
  rw [hselected]
  ring

end AVenhance.Infra.Section5

end
