/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEquation

/-! Exact ordered spatial Leibniz expansions for coefficient-gradient products. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- Each ordered derivative is assigned to exactly one of the two factors. -/
def iterateSpatialSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w => (iterateSpatialSplits w).flatMap (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)])

/-- The full ordered expansion has exactly 2^n summands, before grouping
by the order falling on a coefficient. -/
theorem iterateSpatialSplits_length (w : List (Fin 2)) :
    (iterateSpatialSplits w).length = 2 ^ w.length := by
  have hlen (P : List (List (Fin 2) × List (Fin 2))) :
      (P.map (fun _ => (2 : ℕ))).sum = 2 * P.length := by
    induction P with
    | nil => rfl
    | cons p P ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialSplits, List.length_flatMap]
    change ((iterateSpatialSplits w).map (fun _ => (2 : ℕ))).sum = 2 ^ (w.length + 1)
    rw [hlen, ih, pow_succ]
    omega

theorem IteratesWordLeibniz.iterate_word_list_differentiable (L : List (Vec 2 → ℝ)) (x : Vec 2)
    (h : ∀ f ∈ L, DifferentiableAt ℝ f x) : DifferentiableAt ℝ L.sum x := by
  induction L with
  | nil => exact differentiableAt_const _
  | cons f L ih =>
    exact (h f List.mem_cons_self).add (ih (fun g hg => h g (List.mem_cons_of_mem f hg)))

theorem IteratesWordLeibniz.iterate_word_list_gradient (L : List (Vec 2 → ℝ)) (x : Vec 2) (i : Fin
    2)
    (h : ∀ f ∈ L, DifferentiableAt ℝ f x) :
    spaceGrad L.sum x i = (L.map (fun f => spaceGrad f x i)).sum := by
  induction L with
  | nil => simp [spaceGrad]
  | cons f L ih =>
    have hf := h f List.mem_cons_self
    have ht : ∀ g ∈ L, DifferentiableAt ℝ g x := fun g hg => h g (List.mem_cons_of_mem f hg)
    have hs := IteratesWordLeibniz.iterate_word_list_differentiable L x ht
    simp only [List.sum_cons, List.map_cons]
    unfold spaceGrad at *
    rw [fderiv_add hf hs, add_apply, ih ht]

/-- Exact Leibniz rule at every spatial order. Repeated derivative letters
are retained as separate ordered splits, producing the correct multiplicity. -/
theorem iterateSpatialWord_mul {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (f * g) x =
      ((iterateSpatialSplits w).map (fun p =>
        iterateSpatialWord p.1 f x * iterateSpatialWord p.2 g x)).sum := by
  induction w generalizing x with
  | nil => simp only [iterateSpatialWord, iterateSpatialSplits, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, Pi.mul_apply]
  | cons i w ih =>
    let L := (iterateSpatialSplits w).map
      (fun p => fun y => iterateSpatialWord p.1 f y * iterateSpatialWord p.2 g y)
    have heq : iterateSpatialWord w (f * g) = L.sum := by
      funext y
      rw [ih]
      dsimp only [L]
      induction iterateSpatialSplits w with
      | nil => rfl
      | cons p P ih =>
        simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
          congrArg (fun a => iterateSpatialWord p.1 f y * iterateSpatialWord p.2 g y + a) ih
    have hL : ∀ a ∈ L, DifferentiableAt ℝ a x := by
      intro a ha
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact ((iterateSpatialWord_smooth hf p.1).differentiable (by simp) x).mul
        ((iterateSpatialWord_smooth hg p.2).differentiable (by simp) x)
    change spaceGrad (iterateSpatialWord w (f * g)) x i = _
    rw [heq, IteratesWordLeibniz.iterate_word_list_gradient L x i hL]
    have hterms : L.map (fun a => spaceGrad a x i) =
        (iterateSpatialSplits w).map (fun p =>
          iterateSpatialWord (i :: p.1) f x * iterateSpatialWord p.2 g x +
          iterateSpatialWord p.1 f x * iterateSpatialWord (i :: p.2) g x) := by
      simp only [L, List.map_map]
      apply List.map_congr_left
      intro p _
      have hdf := (iterateSpatialWord_smooth hf p.1).differentiable (by simp) x
      have hdg := (iterateSpatialWord_smooth hg p.2).differentiable (by simp) x
      simp only [iterateSpatialWord, spaceGrad]
      dsimp only [Function.comp_def]
      rw [fderiv_fun_mul hdf hdg]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    rw [hterms]
    simp only [iterateSpatialSplits, List.map_flatMap, List.map_cons, List.map_nil,
      ]
    induction iterateSpatialSplits w with
    | nil => rfl
    | cons p P ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.sum_append]
      rw [ih]
      simp only [List.sum_nil, add_zero]

end AVenhance.Infra.Section4
