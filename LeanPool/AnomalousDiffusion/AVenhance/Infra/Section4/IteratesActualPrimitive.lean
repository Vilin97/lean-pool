/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialPrimitiveSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxTimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCancellation

/-! Material primitive identity for actual differentiated increments. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Apply material primitive integration by parts to the actual finite
increment sequence. The terminal term is retained; all natural integrability
and regularity premises are discharged. -/
theorem iterate_increment_material_primitive_pairing {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 1 ≤ m) (hκm : 0 < κm) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w r : List (Fin 2)) (j k : Fin 2) {s : ℝ} (hs : 0 ≤ s) :
    let u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)
    let v := fun t => iterateSpatialWord r (iterateIncrement T i t)
    let q := fun t => iterateKmatPrimitive I κm m t j k
    (∫ t in 0..s, ∫ x in unitCube,
      (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) * u t x * v t x) =
      (∫ x in unitCube, u s x * (q s * v s x)) -
      (∫ t in 0..s, ∫ x in unitCube, q t * u t x * amnrMaterial (streamVel (Φ (m - 1))) v t x) -
      (∫ t in 0..s, ∫ x in unitCube, q t * v t x * amnrMaterial (streamVel (Φ (m - 1))) u t x) := by
  dsimp only
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hu := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi) w
  have hv := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)) r
  have hslice {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (t : ℝ) (ht : 0 < t) :
      ContDiff ℝ (⊤ : ℕ∞) (f t) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have hper (a : ℕ) (ha : a ≤ Nstar β) (p : List (Fin 2)) (t : ℝ) (ht : 0 < t) :
      IsZ2Periodic (iterateSpatialWord p (iterateIncrement T a t)) :=
    iterateSpatialWord_periodic
      (hslice (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 ha) t ht)
      (iterateIncrement_periodic I hΦ hT hθ.2.1 ha ht.le) p
  have hK : Continuous (fun t => I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) :=
    (contDiff_pi.mp (contDiff_pi.mp (AVenhance.Infra.Section3.Kmat_contDiff I hm hκm) j)
        k).continuous.sub continuous_const
  have hdq (t : ℝ) (_ : 0 < t) : HasDerivAt (fun t => iterateKmatPrimitive I κm m t j k)
      (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) t :=
    (hK.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hp := iterate_material_primitive_pairing_of_smooth hφ
    (hu.of_le (by simp)) (hv.of_le (by simp))
    (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).contDiffOn hdq
    (hslice hu) (hslice hv) (hper (i + 1) hi w) (hper i (by omega) r) hs hK
  simpa only [iterateKmatPrimitive, intervalIntegral.integral_same, zero_mul, mul_zero,
      integral_zero, sub_zero] using hp

end AVenhance.Infra.Section4
