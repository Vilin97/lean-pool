/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible

/-! Connect joint commutator words to the actual spatially differentiated PDE. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- On a full spatial slice of an open domain, joint spatial words equal
ordered spatial derivatives of the slice. Only positive-time germs are used. -/
theorem iterate_amnrWord_spatial_slice {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {t : ℝ} (ht : ∀ x, (t, x) ∈ U) (w : List (Fin 2)) (x : Vec 2) :
    amnrWord b (w.map some) f (t, x) = iterateSpatialWord w (fun y => f (t, y)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have hw := iterate_amnrWord_smoothOn hU hb hf (w.map some)
    have hd := (hw.contDiffAt (hU.mem_nhds (ht x))).differentiableAt (by simp)
    have hc := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    have heq : (fun y => amnrWord b (w.map some) f (t, y)) =
        iterateSpatialWord w (fun y => f (t, y)) := by funext y; exact ih y
    have hderiv := hc.fderiv
    change fderiv ℝ (fun y => amnrWord b (w.map some) f (t, y)) x = _ at hderiv
    rw [heq] at hderiv
    simp only [List.map_cons, amnrWord, iterateSpatialWord]
    unfold amnrOp amnrDirection spaceGrad
    rw [hderiv]
    rfl

/-- Exact all-order commuted material equation on the positive-time domain.
The error is the explicit drift commutator; forcing regularity remains a
structural input rather than a differentiated equation hypothesis. -/
theorem iterate_classical_commuted_word_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (hF : ContDiff ℝ (⊤ : ℕ∞) (F t))
    (w : List (Fin 2)) (x : Vec 2) :
    amnrMaterial b (fun s => iterateSpatialWord w (u s)) t x =
      κ * spaceLap (iterateSpatialWord w (u t)) x + iterateSpatialWord w (F t) x -
      iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
        (fun z => u z.1 z.2) (t, x) := by
  let U : Set AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ Set.univ
  let B : AmnrSpace → Vec 2 := fun z => b z.1 z.2
  let f : AmnrSpace → ℝ := fun z => u z.1 z.2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := hsol.1.mono (by
    intro z hz
    exact ⟨(show 0 < z.1 from hz.1).le, Set.mem_univ z.2⟩)
  have hslice : ∀ y : Vec 2, (t, y) ∈ U := fun y => ⟨ht, Set.mem_univ y⟩
  have hm := iterate_amnrWord_smoothOn hU hb hf [none]
  have heq : (fun y => amnrOp B none f (t, y)) = amnrMaterial b u t := by
    funext y
    exact amnrOp_material ((hf.contDiffAt (hU.mem_nhds (hslice y))).differentiableAt (by simp))
  have hleft := iterate_amnrWord_spatial_slice hU hb hm hslice w x
  change amnrWord B (w.map some) (amnrOp B none f) (t, x) =
    iterateSpatialWord w (fun y => amnrOp B none f (t, y)) x at hleft
  rw [heq, iterate_classical_material_word_equation hsol ht hF w] at hleft
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

end AVenhance.Infra.Section4
