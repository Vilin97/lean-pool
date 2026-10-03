/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordLeibniz

/-! All-order divergence-form forcing with exact coefficient-gradient products. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Ordered spatial derivatives commute with each coordinate gradient. -/
theorem iterateSpatialWord_gradient {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) (j : Fin 2) :
    iterateSpatialWord w (fun x => spaceGrad f x j) =
      fun x => spaceGrad (iterateSpatialWord w f) x j := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    exact iterate_coordinate_derivatives_commute (iterateSpatialWord_smooth hf w) j i x

/-- Ordered spatial differentiation commutes with every finite smooth sum. -/
theorem iterateSpatialWord_sum {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, iterateSpatialWord w (f i) x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    unfold spaceGrad
    rw [fderiv_fun_sum (fun i hi =>
      (iterateSpatialWord_smooth (hf i hi) w).differentiable (by simp) x)]
    simp only [sum_apply]

/-- The differentiated vector flux keeps every coefficient-gradient Leibniz
term, including the principal term with no derivative on the coefficient. -/
def iterateWordFlux (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) : Vec 2 := fun i =>
  ∑ j : Fin 2, ((iterateSpatialSplits w).map (fun p =>
    iterateSpatialWord p.1 (fun y => A y i j) x *
      spaceGrad (iterateSpatialWord p.2 v) x j)).sum

/-- Each component of the differentiated actual flux is exactly the expanded
flux, with multiplicities supplied by the ordered splits. -/
theorem iterateSpatialWord_matrix_flux
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) (i : Fin 2) :
    iterateSpatialWord w (fun x => (A x).mulVec (spaceGrad v x) i) =
      fun x => iterateWordFlux A v w x i := by
  have ha (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j) :=
    contDiff_pi.mp (contDiff_pi.mp hA i) j
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad v x j) :=
    contDiff_pi.mp (iterate_gradient_smooth hv) j
  change iterateSpatialWord w (fun x => ∑ j : Fin 2, A x i j * spaceGrad v x j) = _
  rw [iterateSpatialWord_sum Finset.univ _ (fun j _ => (ha j).mul (hg j))]
  funext x
  unfold iterateWordFlux
  apply Finset.sum_congr rfl
  intro j _
  have hp := iterateSpatialWord_mul (ha j) (hg j) w x
  change iterateSpatialWord w ((fun y => A y i j) * (fun y => spaceGrad v y j)) x = _
  rw [hp]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [iterateSpatialWord_gradient hv p.2 j]

/-- Spatial words commute with divergence of the actual smooth vector flux. -/
theorem iterateSpatialWord_divergence {H : Vec 2 → Vec 2}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (w : List (Fin 2)) :
    iterateSpatialWord w (vecDiv H) =
      vecDiv (fun x i => iterateSpatialWord w (fun y => H y i) x) := by
  have hh (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => H y i) := contDiff_pi.mp hH i
  have hg (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad (fun z => H z i) y i) :=
    contDiff_pi.mp (iterate_gradient_smooth (hh i)) i
  unfold vecDiv
  rw [iterateSpatialWord_sum Finset.univ _ (fun i _ => hg i)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (iterateSpatialWord_gradient (hh i) w i) x

/-- Exact all-order forcing in divergence form. No differentiated forcing
formula is supplied as a hypothesis. -/
theorem iterateSpatialWord_matrix_forcing_divergence
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) :
    iterateSpatialWord w (vecDiv (fun x => (A x).mulVec (spaceGrad v x))) =
      vecDiv (iterateWordFlux A v w) := by
  have hH : ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (spaceGrad v x)) := by
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * spaceGrad v x j)
    apply ContDiff.sum
    intro j _
    exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      (contDiff_pi.mp (iterate_gradient_smooth hv) j)
  rw [iterateSpatialWord_divergence hH]
  congr 1
  funext x i
  exact congrFun (iterateSpatialWord_matrix_flux hA hv w i) x

end AVenhance.Infra.Section4
