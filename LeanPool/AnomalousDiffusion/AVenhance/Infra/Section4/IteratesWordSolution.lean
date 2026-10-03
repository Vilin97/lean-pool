/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEnergy

/-! Actual differentiated classical solutions, including the initial boundary. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Spatial smoothness of the actual forcing follows from the classical PDE
and actual drift smoothness; it is not an extra forcing regularity premise. -/
theorem iterate_classical_forcing_spatial_smooth
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (F t) := by
  let U : Set AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ Set.univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2) U :=
    hsol.1.mono (fun z hz => ⟨(show 0 < z.1 from hz.1).le, Set.mem_univ z.2⟩)
  have hm := iterate_amnrWord_smoothOn hU hb hu [none]
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hmaterial : ContDiff ℝ (⊤ : ℕ∞) (amnrMaterial b u t) := by
    have hc := hm.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
    have heq : (fun x => amnrWord (fun z : AmnrSpace => b z.1 z.2) [none]
        (fun z => u z.1 z.2) (t, x)) = amnrMaterial b u t := by
      funext x
      exact amnrOp_material ((hu.contDiffAt (hU.mem_nhds
        (show (t, x) ∈ U from ⟨ht, Set.mem_univ x⟩))).differentiableAt (by simp))
    exact heq ▸ hc
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hsol.1.comp_contDiff hmap (fun x => ⟨ht.le, Set.mem_univ x⟩)
  have heq : F t = fun x => amnrMaterial b u t x - κ * spaceLap (u t) x := by
    funext x
    have he := iterate_material_equation hsol ht x
    linarith only [he]
  rw [heq]
  exact hmaterial.sub (contDiff_const.mul (iterate_laplacian_smooth hs))

/-- Every spatial word of the actual scalar solves its actual differentiated
PDE, with the explicit drift commutator subtracted from the forcing. Joint
smoothness up to zero and the initial trace are proved from the original
classical carrier. No differentiated classical equation is assumed. -/
theorem iterate_classical_spatial_word_sol
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    IsClassicalSol b κ
      (fun t x => iterateSpatialWord w (F t) x -
        iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
          (fun z => u z.1 z.2) (t, x))
      (iterateSpatialWord w u₀) (fun t => iterateSpatialWord w (u t)) := by
  refine ⟨iterateSpatialWord_smooth_up_to_initial hsol.1 w, ?_, ?_, ?_⟩
  · intro t ht
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    exact iterateSpatialWord_periodic
      (hsol.1.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)) (hsol.2.1 t ht) w
  · intro x
    exact congrFun (iterate_classical_word_initial hsol w) x
  · intro t ht x
    have he := iterate_classical_commuted_word_equation hsol hb ht
      (iterate_classical_forcing_spatial_smooth hsol hb ht) w x
    unfold amnrMaterial at he
    unfold advDiffOp
    linarith only [he]

end AVenhance.Infra.Section4
