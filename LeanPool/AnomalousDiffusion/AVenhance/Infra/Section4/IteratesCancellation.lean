/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTime

/-! Transported primitive contraction cancellation for the first increment. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The first-increment contraction has a transported half-square cancellation.
The endpoint energy is retained at an arbitrary terminal time. Joint C1 and
smooth periodic spatial slices suffice; no quantitative estimate is assumed. -/
theorem iterate_material_matrix_square_cancellation
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ i j, ContDiffOn ℝ 1 (fun p : AmnrSpace => Q p.1 i j) (Set.Ici 0 ×ˢ Set.univ))
    (hH : ∀ i j, ContDiffOn ℝ 1 (fun p : AmnrSpace => H p.1 p.2 i j) (Set.Ici 0 ×ˢ Set.univ))
    (hHs : ∀ t, 0 < t → ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => H t x i j))
    (hHp : ∀ t, 0 < t → ∀ i j, IsZ2Periodic (fun x => H t x i j))
    {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : AmnrSpace =>
      (∑ i : Fin 2, ∑ j : Fin 2, Q p.1 i j * H p.1 p.2 i j) *
      deriv (fun s => ∑ i : Fin 2, ∑ j : Fin 2, Q s i j * H s p.2 i j) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hG : Integrable (fun p : AmnrSpace =>
      (∑ i : Fin 2, ∑ j : Fin 2, deriv (fun s => Q s i j) p.1 * H p.1 p.2 i j) *
      (∑ i : Fin 2, ∑ j : Fin 2, Q p.1 i j * H p.1 p.2 i j))
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hJ : Integrable (fun p : AmnrSpace =>
      (∑ i : Fin 2, ∑ j : Fin 2, Q p.1 i j *
        amnrMaterial (streamVel φ) (fun s y => H s y i j) p.1 p.2) *
      (∑ i : Fin 2, ∑ j : Fin 2, Q p.1 i j * H p.1 p.2 i j))
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ t in 0..T, ∫ x in unitCube,
      (∑ i : Fin 2, ∑ j : Fin 2, deriv (fun s => Q s i j) t * H t x i j) *
      (∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j)) =
      (l2NormSq (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Q T i j * H T x i j) -
        l2NormSq (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Q 0 i j * H 0 x i j)) / 2 -
      (∫ t in 0..T, ∫ x in unitCube,
        (∑ i : Fin 2, ∑ j : Fin 2, Q t i j *
          amnrMaterial (streamVel φ) (fun s y => H s y i j) t x) *
        (∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j)) := by
  let f := fun t x => ∑ i : Fin 2, ∑ j : Fin 2, Q t i j * H t x i j
  let g := fun t x => ∑ i : Fin 2, ∑ j : Fin 2, deriv (fun s => Q s i j) t * H t x i j
  let h := fun t x => ∑ i : Fin 2, ∑ j : Fin 2, Q t i j *
    amnrMaterial (streamVel φ) (fun s y => H s y i j) t x
  have hf : ContDiffOn ℝ 1 (fun p : AmnrSpace => f p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hQ i j).mul (hH i j)
  have hfs (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (f t) := by
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul (hHs t ht i j)
  have hfp (t : ℝ) (ht : 0 < t) : IsZ2Periodic (f t) := by
    intro k x
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun r : ℝ => Q t i j * r) (hHp t ht i j k x)
  have hsquare := iterate_material_time_square_pairing hφ hf hfs hfp hT hI
  have hpoint (t : ℝ) (ht : 0 < t) (x : Vec 2) :
      f t x * amnrMaterial (streamVel φ) f t x = g t x * f t x + h t x * f t x := by
    have hmem : Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ nhds (t, x) :=
      prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem
    have hqd (i j : Fin 2) : DifferentiableAt ℝ (fun s => Q s i j) t := by
      have hj := ((hQ i j).contDiffAt hmem).differentiableAt (by norm_num)
      exact hj.comp (f := fun s : ℝ => (s, x)) t
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).differentiableAt
    have hhd (i j : Fin 2) : DifferentiableAt ℝ (fun p : AmnrSpace => H p.1 p.2 i j) (t, x) :=
      ((hH i j).contDiffAt hmem).differentiableAt (by norm_num)
    have he := iterate_material_matrix_contract (b := streamVel φ) hqd hhd
    change amnrMaterial (streamVel φ) f t x = g t x + h t x at he
    rw [he]
    ring
  have heq : (fun t => ∫ x in unitCube, f t x * amnrMaterial (streamVel φ) f t x) =ᵐ[
      volume.restrict (Set.uIoc 0 T)]
      (fun t => (∫ x in unitCube, g t x * f t x) + (∫ x in unitCube, h t x * f t x)) := by
    filter_upwards [hG.prod_right_ae, hJ.prod_right_ae, ae_restrict_mem measurableSet_uIoc]
      with t hg hh ht
    rw [Set.uIoc_of_le hT] at ht
    have he : (fun x => f t x * amnrMaterial (streamVel φ) f t x) =
        (fun x => g t x * f t x + h t x * f t x) := funext (hpoint t ht.1)
    rw [he]
    exact integral_add hg hh
  rw [intervalIntegral.integral_congr_ae_restrict heq] at hsquare
  have hg : IntervalIntegrable (fun t => ∫ x in unitCube, g t x * f t x) volume 0 T :=
    intervalIntegrable_iff.mpr hG.integral_prod_left
  have hh : IntervalIntegrable (fun t => ∫ x in unitCube, h t x * f t x) volume 0 T :=
    intervalIntegrable_iff.mpr hJ.integral_prod_left
  rw [intervalIntegral.integral_add hg hh] at hsquare
  change (∫ t in 0..T, ∫ x in unitCube, g t x * f t x) =
    (l2NormSq (f T) - l2NormSq (f 0)) / 2 - (∫ t in 0..T, ∫ x in unitCube, h t x * f t x)
  linarith only [hsquare]

/-- The actual primitive gains one time derivative over Kmat. This retains
the finite approved regularity instead of assuming an infinitely smooth cutoff. -/
theorem iterateKmatPrimitive_entry_contDiff {β : ℝ} (I : Ingredients β)
    {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) (i j : Fin 2) :
    ContDiff ℝ ((Nstar β : WithTop ℕ∞) + 1)
      (fun t => iterateKmatPrimitive I κ m t i j) := by
  have hK : ContDiff ℝ (Nstar β : ℕ∞) (fun t => I.Kmat κ m t i j) :=
    contDiff_pi.mp (contDiff_pi.mp (Infra.Section3.Kmat_contDiff I hm hκ) i) j
  let g := fun t => I.Kmat κ m t i j - timeAvgMat (I.Kmat κ m) i j
  have hg : ContDiff ℝ (Nstar β : ℕ∞) g := hK.sub contDiff_const
  have hd (t : ℝ) : HasDerivAt (fun s => iterateKmatPrimitive I κ m s i j) (g t) t :=
    (hg.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · intro h
    simp at h
  · have heq : deriv (fun t => iterateKmatPrimitive I κ m t i j) = g :=
      funext (fun t => (hd t).deriv)
    rw [heq]
    exact hg

/-- The primitive satisfies the joint C1 input of the transported contraction
cancellation, as a proved property of the actual formula. -/
theorem iterateKmatPrimitive_entry_joint_contDiff {β : ℝ} (I : Ingredients β)
    {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) (i j : Fin 2) :
    ContDiff ℝ 1 (fun p : AmnrSpace => iterateKmatPrimitive I κ m p.1 i j) := by
  have hq : ContDiff ℝ 1 (fun t => iterateKmatPrimitive I κ m t i j) :=
    (iterateKmatPrimitive_entry_contDiff I hκ hm i j).of_le (by simp)
  exact hq.comp contDiff_fst

end AVenhance.Infra.Section4
