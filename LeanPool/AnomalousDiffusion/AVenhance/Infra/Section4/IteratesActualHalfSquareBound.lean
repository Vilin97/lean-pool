/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHalfSquareBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCancellationRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! # Iterates Actual Half Square Bound

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The first-increment oscillatory pairing uses the actual K primitive and
 actual Hessian, with both material and terminal energies explicitly retained. -/
theorem iterate_actual_hessian_half_square_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t)) (w : List (Fin 2))
    {D G M T s : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hQb : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube,
      (iterateSpatialWord (j :: k :: w) (u z.1) z.2) ^ 2) ≤ G ^ 2)
    (hME : ∀ j k, (∫ z in timeCube,
      (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord (j :: k :: w) (u t)) z.1 z.2) ^ 2) ≤ M ^ 2)
    (hTE : ∀ j k, l2NormSq (iterateSpatialWord (j :: k :: w) (u s)) ≤ T ^ 2) :
    |∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (u t) x) *
      (∑ j : Fin 2, ∑ k : Fin 2, iterateKmatPrimitive I κm m t j k *
        iterateSpatialWord (j :: k :: w) (u t) x)| ≤
      8 * D ^ 2 * T ^ 2 + 16 * D ^ 2 * M * G := by
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hKc (j k : Fin 2) : Continuous (fun t => I.Kmat κm m t j k) :=
    (continuous_apply k).comp ((continuous_apply j).comp
      (AVenhance.Infra.Section3.Kmat_contDiff I hm hκm).continuous)
  have hd (t : ℝ) (j k : Fin 2) : HasDerivAt
      (fun r => iterateKmatPrimitive I κm m r j k)
      (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) t :=
    ((hKc j k).sub continuous_const).integral_hasStrictDerivAt 0 t |>.hasDerivAt
  have hQd (j k : Fin 2) : Continuous
      (fun t => deriv (fun r => iterateKmatPrimitive I κm m r j k) t) := by
    have he : (fun t => deriv (fun r => iterateKmatPrimitive I κm m r j k) t) =
        fun t => I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k :=
      funext (fun t => (hd t j k).deriv)
    rw [he]
    exact (hKc j k).sub continuous_const
  have hslice (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hu.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have he := iterate_material_half_square_bound hφ
    (fun j k => (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).contDiffOn) hQd
    (fun j k => (iterateSpatialWord_smooth_up_to_initial hu (j :: k :: w)).of_le (by simp))
    (fun t ht j k => iterateSpatialWord_smooth (hslice t ht) (j :: k :: w))
    (fun t ht j k => iterateSpatialWord_periodic (hslice t ht) (hup t ht) (j :: k :: w))
    (fun j k => by simp [iterateKmatPrimitive]) hD hG hM hs hs1 hQb hE hME hTE
  simpa only [(hd _ _ _).deriv] using he

end AVenhance.Infra.Section4
