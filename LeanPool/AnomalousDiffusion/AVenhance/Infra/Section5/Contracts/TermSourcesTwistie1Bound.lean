/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Jets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Time
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # The time bound for `twistie1` in terms of the space-time gradients of `T`

`se_time_bound`: for `t ∈ (0,1)` the slice estimate `se_slice_hMinus` and the weighted pointwise
bound `se_gradDiv_vecNormSq_le` (the `G(t) = ‖∇ ∇·(B ∇T)(t)‖²` term), integrated in time by
`se_time_assembly`, give the bound by the space-time energies of the gradients of the words of
length `≤ 2` applied to `T`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

/-- The energy of `∇ ∇·(B ∇T)` at time `t` by the weighted word energies of `T`. -/
theorem se_gdNormSq_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (κm : ℝ) (Tn : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hT : ContDiff ℝ ∞ (Tn t)) {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) x| ≤
      D * w.length.factorial * L ^ w.length) :
    gradNormSq (seGd I hΦ m κm Tn t) ≤ ∑ w ∈ scWords2,
      (14336 * D ^ 2 * (L ^ (2 - w.length)) ^ 2) * gradNormSq (scWordGrad Tn w t) := by
  have hBs := se_B_smooth I hΦ (by omega : 1 ≤ m) κm t
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun x => I.Kmat κm m t + I.sMat hΦ m κm t x) :=
    RelativeError.contDiff_matrix_of_entries hBs
  have hWint : ∀ w, IntegrableOn (fun x => vecNormSq
      (spaceGrad (iterateSpatialWord w (Tn t)) x)) unitCube :=
    fun w => LeftToShow.integrableOn_unitCube_of_continuous (sc_wordEnergy_continuous hT w)
  have hgd : Continuous (seGd I hΦ m κm Tn t) := se_seGd_continuous I hΦ m κm t hBs hT
  unfold gradNormSq
  simp only [scWordGrad]
  rw [show (∑ w ∈ scWords2, (14336 * D ^ 2 * (L ^ (2 - w.length)) ^ 2) *
      ∫ x in unitCube, vecNormSq (spaceGrad (iterateSpatialWord w (Tn t)) x)) =
      ∫ x in unitCube, 14336 * D ^ 2 * ∑ w ∈ scWords2, (L ^ (2 - w.length)) ^ 2 *
        vecNormSq (spaceGrad (iterateSpatialWord w (Tn t)) x) from by
    rw [integral_const_mul, integral_finsetSum _ fun w _ => ((hWint w).const_mul _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_const_mul]; ring]
  refine integral_mono (LeftToShow.integrableOn_unitCube_of_continuous
    (LeftToShow.continuous_vecNormSq_two.comp hgd)) ?_ fun x => ?_
  · exact (integrable_finsetSum _ fun w _ => (hWint w).const_mul _).const_mul _
  · have := se_gradDiv_vecNormSq_le hA hT x hD hL (A := fun x => I.Kmat κm m t +
      I.sMat hΦ m κm t x) (v := Tn t) (fun p _ j k => by
        have h := hBb j k p x
        simpa only [iterateMatrixWord, RelativeError.iterateSpatialWord_eq_amnrSpaceWord] using h)
    exact this

/-- **The time bound of `twistie1`.** -/
theorem se_time_bound {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (Tn : ℝ → Vec 2 → ℝ)
    (hTc : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => Tn p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ ∞ (Tn t))
    (hTper : ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (Tn t))
    (hmean : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (twistie1 I hΦ m κm Tn t))
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 8)
    {D M L : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hL : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L)
    (hBb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j w x,
      |amnrSpaceWord w (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) x| ≤
        D * w.length.factorial * L ^ w.length)
    (hTb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w (Tn t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal (M * w.length.factorial * L ^ w.length))
    (hsep : 2 ≤ ((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ)) :
    timeHMinusOneNorm (fun t => twistie1 I hΦ m κm Tn t) ≤
      ENNReal.ofReal (72 * Real.sqrt 2 *
        ((seCE / (ergodicFrequency β I.Λ m : ℝ) * 4 *
            (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm))) *
          Real.sqrt (∑ w ∈ scWords2, (14336 * D ^ 2 * (L ^ (2 - w.length)) ^ 2) *
            spaceTimeGradNormSq (scWordGrad Tn w)) +
         seCE * (2048 * 40 * D * M * L ^ 3) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  have hεm : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have haM : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hεm _).le
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hNr : (0 : ℝ) < (ergodicFrequency β I.Λ m : ℝ) := by
    have := ergodicFrequency_pos (Λ := I.Λ) (m := m) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    exact_mod_cast this
  have hCE := seCE_nonneg
  have hGχ0 : 0 ≤ epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) := by positivity
  have hCF0 : 0 ≤ 2048 * 40 * D * M * L ^ 3 := by positivity
  unfold timeHMinusOneNorm
  refine le_trans (se_time_assembly (fun w t => scWordGrad Tn w t)
    (fun w => 14336 * D ^ 2 * (L ^ (2 - w.length)) ^ 2)
    (P₁ := seCE / (ergodicFrequency β I.Λ m : ℝ) * 4 *
      (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)))
    (P₂ := seCE * (2048 * 40 * D * M * L ^ 3) *
      (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
      Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))
    (H := fun t => hMinusOneNorm (twistie1 I hΦ m κm Tn t))
    (G := fun t => gradNormSq (seGd I hΦ m κm Tn t))
    (by positivity) (by have := (Real.exp_pos (-((16 * L)⁻¹ / 2 ^ 11) *
        (ergodicFrequency β I.Λ m : ℝ) / 4096)).le; positivity)
    (fun w _ => by positivity)
    (fun w _ i => sc_wordGrad_continuousOn hTc w i)
    (fun t _ => by unfold gradNormSq; exact integral_nonneg fun x => vecNormSq_nonneg _)
    (fun t ht => ?_) (fun t ht => se_gdNormSq_le I hΦ hm κm Tn (hTs t ht) hD hL0.le (hBb t ht)))
    le_rfl
  have := se_slice_hMinus I hΦ hm hκm Tn (hmean t ht) hsmall
    (se_B_smooth I hΦ (by omega) κm t) (se_B_periodic I hΦ m κm t) (hTs t ht) (hTper t ht)
    (CB := D) (M := M) (L := L) hD hM hL (hBb t ht) (hTb t ht) hsep
  refine this.trans (le_of_eq ?_)
  congr 1
  ring

end AVenhance.Infra.Section5.Contracts
end
