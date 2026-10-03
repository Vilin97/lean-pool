/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedVelocityTerm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPositiveGrouping

/-! Integrated all-order drift errors with linear lower-energy dependence. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
variable {s : ℝ}

theorem IteratesTruncatedVelocityEnergy.velocity_list_integrable {α : Type*} (P : List α) (f : α →
    AmnrSpace → ℝ)
    (hf : ∀ p ∈ P, IntegrableOn (f p) (iterateTruncatedCell s)) :
    IntegrableOn (fun z => (P.map (fun p => f p z)).sum) (iterateTruncatedCell s) := by
  induction P with
  | nil => exact integrableOn_zero
  | cons p P ih =>
    exact (hf p List.mem_cons_self).add
      (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))

theorem IteratesTruncatedVelocityEnergy.velocity_list_integral {α : Type*} (P : List α) (f : α →
    AmnrSpace → ℝ)
    (hf : ∀ p ∈ P, IntegrableOn (f p) (iterateTruncatedCell s)) :
    (∫ z in (iterateTruncatedCell s), (P.map (fun p => f p z)).sum) =
      (P.map (fun p => ∫ z in (iterateTruncatedCell s), f p z)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have ht : ∀ q ∈ P, IntegrableOn (f q) (iterateTruncatedCell s) := fun q hq => hf q
        (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf p List.mem_cons_self)
        (IteratesTruncatedVelocityEnergy.velocity_list_integrable P f ht), ih ht]

theorem IteratesTruncatedVelocityEnergy.velocity_list_abs_sum {α : Type*} (P : List α) (f : α → ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- The actual split sum is bounded linearly by the lower scalar energy
bounds. This is the form used in the norm recurrence, before induction. -/
theorem iterate_truncated_velocity_split_linear_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ} {a : AmnrSpace → ℝ}
    (hs1 : s ≤ 1)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (P : List (List (Fin 2) × List (Fin 2))) (D G : ℕ → ℝ) {H : ℝ}
    (hD : ∀ j, 0 ≤ D j) (hG : ∀ j, 0 ≤ G j) (hH : 0 ≤ H)
    (hjet : ∀ t x p, p ∈ P → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ D p.1.length)
    (hEa : (∫ z in timeCube, a z ^ 2) ≤ H ^ 2)
    (hEv : ∀ p ∈ P,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤ (G p.2.length) ^
          2) :
    |∫ z in (iterateTruncatedCell s), a z * iterateVelocitySplit P (b z.1) (v z.1) z.2| ≤
      2 * H * (P.map (fun p => D p.1.length * G p.2.length)).sum := by
  let f := fun (p : List (Fin 2) × List (Fin 2)) (j : Fin 2) (z : AmnrSpace) =>
    a z * (iterateSpatialWord p.1 (fun y => b z.1 y j) z.2 *
      spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2 j)
  have hf (p : List (Fin 2) × List (Fin 2)) (j : Fin 2) : IntegrableOn (f p j)
      (iterateTruncatedCell s) := by
    have hq := (iterateSpatialWord_smooth_up_to_initial (u := fun t x => b t x j)
      (contDiffOn_pi.mp hb j) p.1).continuousOn
    have hg := (continuous_apply j).comp_continuousOn
      (iterate_word_gradient_smooth_up_to_initial hv p.2).continuousOn
    exact (iterate_timeCube_integrable_of_continuousOn (ha.mul (hq.mul hg))).mono_set
      (iterateTruncatedCell_subset hs1)
  have hterm (p : List (Fin 2) × List (Fin 2)) (hp : p ∈ P) (j : Fin 2) :
      |∫ z in (iterateTruncatedCell s), f p j z| ≤ D p.1.length * H * G p.2.length :=
    iterate_truncated_velocity_word_term_linear_bound hs1 hb hv ha p.1 p.2 j (hD _) hH (hG _)
      (fun t x => hjet t x p hp j) hEa (hEv p hp)
  have he : (fun z : AmnrSpace => a z * iterateVelocitySplit P (b z.1) (v z.1) z.2) =
      (fun z => ∑ j : Fin 2, (P.map (fun p => f p j z)).sum) := by
    funext z
    unfold iterateVelocitySplit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← List.sum_map_mul_left]
  rw [he, integral_finsetSum Finset.univ (fun j _ =>
      IteratesTruncatedVelocityEnergy.velocity_list_integrable P _ (fun p _ => hf p j))]
  simp_rw [IteratesTruncatedVelocityEnergy.velocity_list_integral P _ (fun p _ => hf p _)]
  calc
    _ ≤ ∑ j : Fin 2, |(P.map (fun p => ∫ z in (iterateTruncatedCell s), f p j z)).sum| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 2, (P.map (fun p => D p.1.length * H * G p.2.length)).sum := by
      apply Finset.sum_le_sum
      intro j _
      exact (IteratesTruncatedVelocityEnergy.velocity_list_abs_sum P _).trans (List.sum_le_sum
          (fun p hp => hterm p hp j))
    _ = _ := by
      simp only [Fin.sum_univ_two]
      have hs : (P.map (fun p => D p.1.length * H * G p.2.length)).sum =
          H * (P.map (fun p => D p.1.length * G p.2.length)).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro p _
        ring
      rw [hs]
      ring

/-- The actual drift error has an explicit binomially grouped linear energy
bound. Every scalar gradient premise is at a strictly lower word length. -/
theorem iterate_truncated_material_error_linear_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ} {a : AmnrSpace → ℝ}
    (hs1 : s ≤ 1)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (D G : ℕ → ℝ) {H : ℝ}
    (hD : ∀ j, 0 ≤ D j) (hG : ∀ j, 0 ≤ G j) (hH : 0 ≤ H)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ D p.1.length)
    (hEa : (∫ z in timeCube, a z ^ 2) ≤ H ^ 2)
    (hEv : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤ (G p.2.length) ^
          2) :
    |∫ z in (iterateTruncatedCell s), a z * iterateWordMaterialError (fun z : AmnrSpace => b z.1
        z.2) w
      (fun z => v z.1 z.2) z| ≤
      2 * H * ∑ j ∈ Finset.range w.length,
        (Nat.choose w.length (j + 1) : ℝ) * D (j + 1) * G (w.length - (j + 1)) := by
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro z hz
    exact ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have he : (fun z : AmnrSpace => a z * iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) z) =ᵐ[
      volume.restrict (iterateTruncatedCell s)]
      (fun z => a z * iterateVelocitySplit
        ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) (b z.1) (v z.1) z.2) := by
    apply (ae_restrict_mem (iterateTruncatedCell_isOpen s).measurableSet).mono
    intro z hz
    dsimp only
    change a z * iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) (z.1, z.2) = _
    rw [iterateWordMaterialError_lower_velocity (hb.mono hmono) (hv.mono hmono) hz.1.1]
    rfl
  rw [integral_congr_ae he]
  have h := iterate_truncated_velocity_split_linear_energy_bound hs1 hb hv ha
    ((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)) D G hD hG hH hjet hEa hEv
  rw [iterateSpatialSplits_positive_sum_by_two_orders w (fun j k => D j * G k)] at h
  simpa only [mul_assoc] using h

end AVenhance.Infra.Section4
