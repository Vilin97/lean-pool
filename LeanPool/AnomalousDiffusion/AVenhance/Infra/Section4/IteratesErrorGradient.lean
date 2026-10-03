/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityLower

/-! Exact derivative of the actual lower material error. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual scalar transport field is smooth. -/
theorem iterate_transport_smooth {b : Vec 2 → Vec 2} {u : Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => vecDot (b x) (spaceGrad u x)) := by
  unfold vecDot
  exact ContDiff.sum (fun j _ => (contDiff_pi.mp hb j).mul
    (contDiff_pi.mp (iterate_gradient_smooth hu) j))

/-- One spatial derivative of actual transport separates the velocity jet
 from transport of the differentiated scalar. -/
theorem iterate_transport_gradient_formula {b : Vec 2 → Vec 2} {u : Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x : Vec 2) (j : Fin 2) :
    spaceGrad (fun y => vecDot (b y) (spaceGrad u y)) x j =
      (∑ k : Fin 2, spaceGrad (fun y => b y k) x j * spaceGrad u x k) +
      vecDot (b x) (spaceGrad (fun y => spaceGrad u y j) x) := by
  have he := iterateSpatialWord_transport hb hu [j] x
  simp only [iterateSpatialSplits, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.append_nil,
    iterateSpatialWord, add_zero] at he
  simpa only [vecDot, Finset.sum_add_distrib] using he

/-- Differentiating Err_w gives Err_(j::w) minus the one-jet velocity term.
 This formula contains only derivatives of actual fields and no PDE premise. -/
theorem iterate_material_error_gradient_formula
    {b : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t)
    (w : List (Fin 2)) (x : Vec 2) (j : Fin 2) :
    spaceGrad (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => u z.1 z.2) (t, y)) x j =
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) (j :: w)
        (fun z => u z.1 z.2) (t, x) -
      ∑ k : Fin 2, spaceGrad (fun y => b t y k) x j *
        spaceGrad (iterateSpatialWord w (u t)) x k := by
  have hbs : ContDiff ℝ (⊤ : ℕ∞) (b t) :=
    hb.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have hus : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hu.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have hw := iterateSpatialWord_smooth hus w
  have htr := iterate_transport_smooth hbs hus
  have hpr := iterate_transport_smooth hbs hw
  have he : (fun y => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => u z.1 z.2) (t, y)) =
      fun y => iterateSpatialWord w (fun z => vecDot (b t z) (spaceGrad (u t) z)) y -
        vecDot (b t y) (spaceGrad (iterateSpatialWord w (u t)) y) := by
    funext y
    rw [iterateWordMaterialError_transport hb hu ht w y,
      ← iterateSpatialWord_transport hbs hus w y]
  have hcons := iterateWordMaterialError_transport hb hu ht (j :: w) x
  rw [← iterateSpatialWord_transport hbs hus (j :: w) x] at hcons
  rw [he, hcons]
  have hd := ((iterateSpatialWord_smooth htr w).differentiable (by simp)).differentiableAt (x := x)
  have hp := (hpr.differentiable (by simp)).differentiableAt (x := x)
  unfold spaceGrad at hd hp ⊢
  rw [fderiv_fun_sub hd hp]
  change spaceGrad (iterateSpatialWord w (fun z => vecDot (b t z) (spaceGrad (u t) z))) x j -
    spaceGrad (fun y => vecDot (b t y) (spaceGrad (iterateSpatialWord w (u t)) y)) x j = _
  rw [iterate_transport_gradient_formula hbs hw]
  change _ = spaceGrad (iterateSpatialWord w (fun z => vecDot (b t z) (spaceGrad (u t) z))) x j -
    vecDot (b t x) (spaceGrad (iterateSpatialWord (j :: w) (u t)) x) - _
  simp only [iterateSpatialWord]
  unfold spaceGrad
  ring

end AVenhance.Infra.Section4
