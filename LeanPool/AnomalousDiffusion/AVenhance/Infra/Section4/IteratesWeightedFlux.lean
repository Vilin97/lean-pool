/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientWords

/-! Weighted Young estimates for the actual coefficient-gradient Leibniz terms. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The actual entrywise spatial derivative of a matrix coefficient. -/
def iterateMatrixWord (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : List (Fin 2)) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => iterateSpatialWord w (fun y => A y i j) x

/-- A specified list of actual Leibniz terms, retaining their multiplicities. -/
def iterateSplitFlux (P : List (List (Fin 2) × List (Fin 2)))
    (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ) (x : Vec 2) : Vec 2 :=
  fun i => ∑ j : Fin 2, (P.map (fun p =>
    iterateSpatialWord p.1 (fun y => A y i j) x *
      spaceGrad (iterateSpatialWord p.2 v) x j)).sum

/-- The specified flux is exactly a sum of matrix-gradient products. -/
theorem iterateSplitFlux_eq_sum
    (P : List (List (Fin 2) × List (Fin 2)))
    (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ) (x : Vec 2) :
    iterateSplitFlux P A v x = (P.map (fun p =>
      (iterateMatrixWord A p.1 x).mulVec (spaceGrad (iterateSpatialWord p.2 v) x))).sum := by
  induction P with
  | nil => funext i; simp [iterateSplitFlux]
  | cons p P ih =>
    have he : iterateSplitFlux (p :: P) A v x =
        (iterateMatrixWord A p.1 x).mulVec (spaceGrad (iterateSpatialWord p.2 v) x) +
          iterateSplitFlux P A v x := by
      funext i
      unfold iterateSplitFlux iterateMatrixWord Matrix.mulVec dotProduct
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      rw [Finset.sum_add_distrib]
    rw [he, ih, List.map_cons, List.sum_cons]

theorem IteratesWeightedFlux.iterate_dot_list_sum (a : Vec 2) (P : List (Vec 2)) :
    vecDot a P.sum = (P.map (vecDot a)).sum := by
  induction P with
  | nil => simp [vecDot]
  | cons b P ih =>
    simp only [List.sum_cons, List.map_cons]
    unfold vecDot at *
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ih]

theorem IteratesWeightedFlux.iterate_abs_list_sum {α : Type*} (P : List α) (f : α → ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- Weighted Young's inequality for any actual subset of the Leibniz terms.
The weights allocate dissipation across terms; the remainder consists only
of the actual lower scalar gradients and coefficient jet bounds. -/
theorem iterate_split_flux_pairing_abs_bound
    (P : List (List (Fin 2) × List (Fin 2)))
    (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ) (x : Vec 2) (a : Vec 2)
    (ρ D : List (Fin 2) × List (Fin 2) → ℝ)
    (hρ : ∀ p ∈ P, 0 < ρ p)
    (hA : ∀ p ∈ P, ∀ i j, |iterateSpatialWord p.1 (fun y => A y i j) x| ≤ D p) :
    |vecDot a (iterateSplitFlux P A v x)| ≤
      (P.map ρ).sum * vecNormSq a +
      (P.map (fun p => D p ^ 2 / ρ p *
        vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x))).sum := by
  rw [iterateSplitFlux_eq_sum, IteratesWeightedFlux.iterate_dot_list_sum]
  simp only [List.map_map, Function.comp_def]
  calc
    _ ≤ (P.map (fun p => |vecDot a
        ((iterateMatrixWord A p.1 x).mulVec (spaceGrad (iterateSpatialWord p.2 v) x))|)).sum :=
      IteratesWeightedFlux.iterate_abs_list_sum P _
    _ ≤ (P.map (fun p => ρ p * vecNormSq a + D p ^ 2 / ρ p *
        vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x))).sum := by
      apply List.sum_le_sum
      intro p hp
      exact iterate_matrix_pairing_abs_bound (hρ p hp) _ _ _ (hA p hp)
    _ = _ := by
      rw [List.sum_map_add, List.sum_map_mul_right]

/-- Continuity of the actual squared vector norm. -/
theorem iterate_vecNormSq_continuous {a : Vec 2 → Vec 2} (ha : Continuous a) :
    Continuous (fun x => vecNormSq (a x)) := by
  unfold vecNormSq vecDot
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).comp ha).mul ((continuous_apply i).comp ha))

theorem IteratesWeightedFlux.iterate_continuous_list_sum {α : Type*} (P : List α)
    (f : α → Vec 2 → ℝ) (hf : ∀ p ∈ P, Continuous (f p)) :
    Continuous (fun x => (P.map (fun p => f p x)).sum) := by
  induction P with
  | nil => exact continuous_const
  | cons p P ih =>
    exact (hf p List.mem_cons_self).add
      (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))

end AVenhance.Infra.Section4
