/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CoefficientProductBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds

/-! Actual forcing coefficient jets assembled from source primitive estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Smoothness of the actual flow average follows from local finiteness. -/
theorem amnr_flowAverage_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) (p j : Fin 2) :
    ContDiff ℝ N (amnrFlowAverage I hΦ m p j) := by
  exact contDiffOn_univ.mp (amnr_cutoff_tsum_contDiffOn I hm isOpen_univ
    (N := N) (fun l z => I.flowGrad hΦ m l z.1 z.2 p j)
    (fun l => ((amnr_flowGrad_joint_contDiff_infty I hΦ m l p j).of_le (by simp)).contDiffOn))

/-- The actual coefficient has the finite joint regularity of Kmat. -/
theorem amnr_temperatureCoefficient_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (κprev : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ (AVenhance.Nstar β) (amnrTemperatureCoefficient I hΦ m κm κprev i j) := by
  have hK (p : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun z : AmnrSpace => I.Kmat κm m z.1 i p) :=
    ((contDiff_apply ℝ ℝ p).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp
      (Section3.Kmat_contDiff I hm hκm))).comp contDiff_fst
  have hmain := (ContDiff.sum (s := Finset.univ) (fun p _ =>
    (hK p).mul (amnr_flowAverage_contDiff I hΦ hm (AVenhance.Nstar β) p j))).sub
      (contDiff_const (c := κprev * (if i = j then 1 else 0)))
  have hP (a b' : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun z : AmnrSpace =>
        (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b') := by
    exact (((contDiff_apply ℝ ℝ b').comp ((contDiff_apply ℝ (Fin 2 → ℝ) a).comp
      (Section3.Kmat_contDiff I hm hκm))).comp contDiff_fst).sub contDiff_const
  have hA (a b' : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (amnrFlowAverageA0Plus I hΦ m a b' i j) := by
    have hleft (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 a i) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l a i).of_le (by simp)).contDiffOn
    have hright (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 b' j) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l b' j).of_le (by simp)).contDiffOn
    exact contDiffOn_univ.mp (amnrFlowAverageA0Plus_contDiffOn I hΦ hm isOpen_univ
      (N := AVenhance.Nstar β) a b' i j hleft hright)
  have hquad : ContDiff ℝ (AVenhance.Nstar β)
      (amnrTemperatureQuadraticAverage I hΦ m κm i j) := by
    unfold amnrTemperatureQuadraticAverage
    apply ContDiff.sum
    intro a _
    apply ContDiff.sum
    intro b' _
    exact (hP a b').mul ((hA a b').sub
      ((contDiff_const (c := if i = a then 1 else 0)).mul
        (amnr_flowAverage_contDiff I hΦ hm (AVenhance.Nstar β) b' j)))
  have he := funext (amnrTemperatureCoefficient_eq_average I hΦ hm κm κprev i j)
  rw [he]
  exact hmain.add hquad

/-- Mixed coefficient jets from the two actual left-Jacobian cutoff averages and
the Kmat entries. The quadratic tensor is contracted row by row; its two flow
factors are already represented by `amnrFlowAverageA0Plus`. -/
theorem amnr_temperatureCoefficient_mixed_bound_of_components
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    (i j : Fin 2) {S T A B C D : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ AVenhance.Nstar β)
    (z : AmnrSpace)
    (hKbound : ∀ p v, v.Sublist w →
      ∀ y, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (fun y => I.Kmat κm m y.1 i p) y| ≤ A * amnrWeight S T v)
    (hGbound : ∀ p v, v.Sublist w →
      ∀ y, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (amnrFlowAverage I hΦ m p j) y| ≤ B * amnrWeight S T v)
    (hPbound : ∀ a b' v, v.Sublist w →
      ∀ y, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (fun y => (I.Kmat κm m y.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b') y| ≤
          C * amnrWeight S T v)
    (hHbound : ∀ a b' v, v.Sublist w →
      ∀ y, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (fun y => amnrFlowAverageA0Plus I hΦ m a b' i j y -
          (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b' j y) y| ≤
          D * amnrWeight S T v) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
      (amnrTemperatureCoefficient I hΦ m κm κprev i j) z| ≤
      (2 * (2 : ℝ) ^ AVenhance.Nstar β * A * B +
        |κprev * (if i = j then 1 else 0)| +
        4 * (2 : ℝ) ^ AVenhance.Nstar β * C * D) * amnrWeight S T w := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  have hb : ContDiff ℝ (AVenhance.Nstar β) b :=
    amnr_previous_velocity_contDiff I hΦ hm (AVenhance.Nstar β)
  have hK (p : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun y : AmnrSpace => I.Kmat κm m y.1 i p) :=
    ((contDiff_apply ℝ ℝ p).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp
      (Section3.Kmat_contDiff I hm hκm))).comp contDiff_fst
  have hG (p : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (amnrFlowAverage I hΦ m p j) :=
    amnr_flowAverage_contDiff I hΦ hm (AVenhance.Nstar β) p j
  have hP (a b' : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun y : AmnrSpace =>
        (I.Kmat κm m y.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b') := by
    exact (((contDiff_apply ℝ ℝ b').comp ((contDiff_apply ℝ (Fin 2 → ℝ) a).comp
      (Section3.Kmat_contDiff I hm hκm))).comp contDiff_fst).sub contDiff_const
  have hAplus (a b' : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (amnrFlowAverageA0Plus I hΦ m a b' i j) := by
    have hleft (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 a i) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l a i).of_le (by simp)).contDiffOn
    have hright (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 b' j) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l b' j).of_le (by simp)).contDiffOn
    exact contDiffOn_univ.mp (amnrFlowAverageA0Plus_contDiffOn I hΦ hm isOpen_univ
      (N := AVenhance.Nstar β) a b' i j hleft hright)
  have hH (a b' : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun y : AmnrSpace => amnrFlowAverageA0Plus I hΦ m a b' i j y -
        (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b' j y) :=
    (hAplus a b').sub ((contDiff_const (c := if i = a then 1 else 0)).mul (hG b'))
  have hmain : ContDiff ℝ (AVenhance.Nstar β)
      (fun y : AmnrSpace =>
        (∑ p : Fin 2, I.Kmat κm m y.1 i p * amnrFlowAverage I hΦ m p j y) -
          κprev * (if i = j then 1 else 0)) :=
    (ContDiff.sum (s := Finset.univ) (fun p _ => (hK p).mul (hG p))).sub contDiff_const
  have hquad : ContDiff ℝ (AVenhance.Nstar β)
      (amnrTemperatureQuadraticAverage I hΦ m κm i j) := by
    unfold amnrTemperatureQuadraticAverage
    apply ContDiff.sum
    intro a _
    apply ContDiff.sum
    intro b' _
    exact (hP a b').mul (hH a b')
  have he : amnrTemperatureCoefficient I hΦ m κm κprev i j =
      (fun y => (∑ p : Fin 2,
        I.Kmat κm m y.1 i p * amnrFlowAverage I hΦ m p j y) -
          κprev * (if i = j then 1 else 0) +
        amnrTemperatureQuadraticAverage I hΦ m κm i j y) :=
    funext (amnrTemperatureCoefficient_eq_average I hΦ (m := m) hm κm κprev i j)
  have hadd := amnrWord_add_contDiffOn isOpen_univ hb.contDiffOn hmain.contDiffOn hquad.contDiffOn w
    ((amnrBudget_length_le w).trans hw)
  rw [he]
  change |amnrWord b w
    ((fun y => (∑ p : Fin 2,
      I.Kmat κm m y.1 i p * amnrFlowAverage I hΦ m p j y) -
        κprev * (if i = j then 1 else 0)) +
      amnrTemperatureQuadraticAverage I hΦ m κm i j) z| ≤ _
  rw [hadd (mem_univ z)]
  have hmainBound := amnr_matrix_product_sub_const_word_bound
    (d := κprev * (if i = j then 1 else 0)) hb hK hG hS hT hA hB w hw
    (fun p v hv y => hKbound p v hv y) (fun p v hv y => hGbound p v hv y) z
  have hquadBound := amnr_matrix_double_product_word_bound hb hP hH hS hT hC hD
    w hw (fun a b' v hv y => hPbound a b' v hv y)
    (fun a b' v hv y => hHbound a b' v hv y) z
  exact ((abs_add_le _ _).trans (add_le_add hmainBound hquadBound)).trans_eq (by ring)

end AVenhance.Infra.Section4
