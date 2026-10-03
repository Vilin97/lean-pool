/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure

/-! Cutoff localization of the shear coefficient on a selected mode. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- On the support of an odd fine cutoff, the odd-mode sum defining the
pulled shear coefficient reduces to that selected mode. -/
theorem psiTilde_eq_selected_mode
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : Odd k) (hxi : I.xiMK m k t ≠ 0) :
    psiTilde I hΦ m t x =
      I.zetaProd m k t * psi β I.Λ m k
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) := by
  have htail (l : {l : ℤ // Odd l}) (hl : l ≠ ⟨k, hk⟩) :
      I.hatZetaML m (lIdx β I.Λ m l) t * I.zetaMK m l t *
          psi β I.Λ m l
            (I.xFlowInv hΦ m (lIdx β I.Λ m l) t x) = 0 := by
    have hne : l.1 ≠ k := by
      intro heq
      apply hl
      exact Subtype.ext heq
    have hz : I.zetaMK m l.1 t = 0 := by
      by_contra hzk
      have hzero := Infra.Section3.xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne
        I hm (k := l.1) (l := k) l.property hk (Ne.symm hne) t hzk
      exact hxi hzero
    simp [hz]
  unfold psiTilde
  rw [tsum_eq_single ⟨k, hk⟩ htail]
  simp [Ingredients.zetaProd]

/-- The full twisted diffusion matrix agrees with the selected corrector
matrix wherever its odd cutoff is nonzero. -/
theorem diffusionMatrix_mul_one_plus_gradChi_eq_correctorFlux
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : Odd k) (hxi : I.xiMK m k t ≠ 0) :
    (fun y => diffusionMatrix I hΦ m κ t y *
        (1 + gradChiTilde I hΦ m κ k t y)) =
      correctorFlux I hΦ m κ k t := by
  funext y
  rw [show diffusionMatrix I hΦ m κ t y =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (I.zetaProd m k t * psi β I.Λ m k
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat by
        change κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          psiTilde I hΦ m t y • sigmaMat = _
        rw [psiTilde_eq_selected_mode I hΦ m hm k t y hk hxi]]
  rfl

end AVenhance.Infra.Section5
