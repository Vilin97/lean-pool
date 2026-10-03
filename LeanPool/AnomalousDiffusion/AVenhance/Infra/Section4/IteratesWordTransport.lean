/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFlux

/-! Slice material calculus without assuming an evolution equation. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Exact material commutation on a positive-time slice, independently of a PDE. -/
theorem iterate_material_spatial_word_expansion
    {b : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (amnrMaterial b u t) x =
      amnrMaterial b (fun s => iterateSpatialWord w (u s)) t x +
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) (t, x) := by
  let U : Set AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ Set.univ
  let B : AmnrSpace → Vec 2 := fun z => b z.1 z.2
  let f : AmnrSpace → ℝ := fun z => u z.1 z.2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := hu
  have hslice : ∀ y : Vec 2, (t, y) ∈ U := fun y => ⟨ht, Set.mem_univ y⟩
  have hm := iterate_amnrWord_smoothOn hU hb hf [none]
  have heq : (fun y => amnrOp B none f (t, y)) = amnrMaterial b u t := by
    funext y
    exact amnrOp_material ((hf.contDiffAt (hU.mem_nhds (hslice y))).differentiableAt (by simp))
  have hleft := iterate_amnrWord_spatial_slice hU hb hm hslice w x
  change amnrWord B (w.map some) (amnrOp B none f) (t, x) =
    iterateSpatialWord w (fun y => amnrOp B none f (t, y)) x at hleft
  rw [heq] at hleft
  have hcomm := iterate_spatial_word_material_expansion hU hb hf w (hslice x)
  have hw := iterate_amnrWord_smoothOn hU hb hf (w.map some)
  have heqword : Set.EqOn
      (fun z : AmnrSpace => amnrWord B (w.map some) f z)
      (fun z => iterateSpatialWord w (u z.1) z.2) U := by
    intro z hz
    exact iterate_amnrWord_spatial_slice hU hb hf (fun y => ⟨hz.1, Set.mem_univ y⟩) w z.2
  have hnear := Filter.eventuallyEq_of_mem (hU.mem_nhds (hslice x)) (fun z hz => heqword hz)
  have hderiv : fderiv ℝ (amnrWord B (w.map some) f) (t, x) =
      fderiv ℝ (fun z : AmnrSpace => iterateSpatialWord w (u z.1) z.2) (t, x) :=
    hnear.fderiv_eq
  have hopen : amnrOp B none (amnrWord B (w.map some) f) (t, x) =
      amnrMaterial b (fun s => iterateSpatialWord w (u s)) t x := by
    unfold amnrOp
    rw [hderiv]
    exact amnrOp_material (((hw.contDiffAt (hU.mem_nhds (hslice x))).congr_of_eventuallyEq
      hnear.symm).differentiableAt (by simp))
  change amnrWord B (w.map some) (amnrOp B none f) (t, x) =
    amnrOp B none (amnrWord B (w.map some) f) (t, x) +
      iterateWordMaterialError B w f (t, x) at hcomm
  rw [hopen] at hcomm
  linarith only [hleft, hcomm]

/-- A vanishing drift has no material commutator at any spatial order. -/
theorem iterateWordMaterialError_zero (w : List (Fin 2)) (f : AmnrSpace → ℝ) :
    iterateWordMaterialError (fun _ => (0 : Vec 2)) w f = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext z
    simp only [iterateWordMaterialError, ih, iterateVelocityCommutator,
      amnrOp, fderiv_fun_const, Pi.zero_apply, zero_apply]
    change (fderiv ℝ (fun _ : AmnrSpace => (0 : ℝ)) z) _ +
      (fderiv ℝ (amnrWord (fun _ => 0) (w.map some) f) z) (0 : AmnrSpace) = 0
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, add_zero]

/-- Ordered spatial derivatives commute with the actual time derivative.
The scalar field need only be smooth on the positive-time domain. -/
theorem iterateSpatialWord_time {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (fun y => deriv (fun s => u s y) t) x =
      deriv (fun s => iterateSpatialWord w (u s) x) t := by
  have h := iterate_material_spatial_word_expansion
    (b := fun _ _ => 0) contDiffOn_const hu ht w x
  rw [iterateWordMaterialError_zero] at h
  have hz : amnrMaterial (fun _ _ => 0) u t = fun y => deriv (fun s => u s y) t := by
    funext y
    simp [amnrMaterial, vecDot]
  rw [hz] at h
  simpa [amnrMaterial, vecDot] using h

end AVenhance.Infra.Section4
