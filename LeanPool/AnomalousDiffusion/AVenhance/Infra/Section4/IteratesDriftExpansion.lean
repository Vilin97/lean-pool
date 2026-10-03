/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordTransport

/-! The material error is exactly the ordered velocity-gradient Leibniz error. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The scalar transport term has its full ordered product expansion. -/
theorem iterateSpatialWord_transport {b : Vec 2 → Vec 2} {u : Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (fun y => vecDot (b y) (spaceGrad u y)) x =
      ∑ j : Fin 2, ((iterateSpatialSplits w).map (fun p =>
        iterateSpatialWord p.1 (fun y => b y j) x *
        spaceGrad (iterateSpatialWord p.2 u) x j)).sum := by
  have hbj (j : Fin 2) := contDiff_pi.mp hb j
  have hgj (j : Fin 2) := contDiff_pi.mp (iterate_gradient_smooth hu) j
  unfold vecDot
  rw [iterateSpatialWord_sum Finset.univ _ (fun j _ => (hbj j).mul (hgj j))]
  apply Finset.sum_congr rfl
  intro j _
  have h := iterateSpatialWord_mul (hbj j) (hgj j) w x
  change iterateSpatialWord w ((fun y => b y j) * (fun y => spaceGrad u y j)) x = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [iterateSpatialWord_gradient hu p.2 j]

/-- Smoothness of the actual time derivative on a positive-time spatial slice. -/
theorem iterate_time_slice_smooth {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => deriv (fun s => u s x) t) := by
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod (isOpen_univ : IsOpen (Set.univ : Set
      (Vec 2)))
  have hm := iterate_amnrWord_smoothOn hU
    (b := fun _ => (0 : Vec 2)) contDiffOn_const hu [none]
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hc := hm.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  have heq : (fun x => amnrWord (fun _ => (0 : Vec 2)) [none]
      (fun z => u z.1 z.2) (t, x)) = fun x => deriv (fun s => u s x) t := by
    funext x
    change amnrOp (fun _ => 0) none (fun z => u z.1 z.2) (t, x) = _
    rw [amnrOp_material ((hu.contDiffAt (hU.mem_nhds
      (show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ from ⟨ht, Set.mem_univ x⟩))).differentiableAt (by
          simp))]
    simp [amnrMaterial, vecDot]
  exact heq ▸ hc

/-- The explicit recursive material error equals the velocity product error.
Time commutation is proved, so no commuted equation is supplied as a premise. -/
theorem iterateWordMaterialError_transport
    {b : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => u z.1 z.2) (t, x) =
      (∑ j : Fin 2, ((iterateSpatialSplits w).map (fun p =>
        iterateSpatialWord p.1 (fun y => b t y j) x *
        spaceGrad (iterateSpatialWord p.2 (u t)) x j)).sum) -
      vecDot (b t x) (spaceGrad (iterateSpatialWord w (u t)) x) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hs := hu.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  have hbs := hb.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  dsimp only [Function.comp_def] at hs hbs
  have htransport : ContDiff ℝ (⊤ : ℕ∞) (fun y => vecDot (b t y) (spaceGrad (u t) y)) := by
    unfold vecDot
    exact ContDiff.sum (fun j _ => (contDiff_pi.mp hbs j).mul
      (contDiff_pi.mp (iterate_gradient_smooth hs) j))
  have he := iterate_material_spatial_word_expansion hb hu ht w x
  have htword := iterateSpatialWord_time hu ht w x
  have hlin := iterateSpatialWord_linear (iterate_time_slice_smooth hu ht) htransport 1 w
  have hp := iterateSpatialWord_transport hbs hs w x
  unfold amnrMaterial at he
  simp only [one_mul] at hlin
  rw [hlin] at he
  dsimp only at he hp
  rw [htword, hp] at he
  linarith only [he]

end AVenhance.Infra.Section4
