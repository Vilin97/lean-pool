/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixIntegralSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEnergy

/-! # Iterates Boundary Squared Gain

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- The terminal boundary pairing has a quarter of the current scalar energy
and a squared primitive gain on the preceding two-higher scalar order. -/
theorem iterate_word_boundary_squared_gain
    {u v : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hup : IsZ2Periodic u) (hvp : IsZ2Periodic v)
    (w : List (Fin 2)) (a : ℕ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    {D L Cs q B : ℝ} (hD : 0 ≤ D) (hL : 0 < L) (hCs : 0 ≤ Cs) (hq : 0 ≤ q)
    (hQ : ∀ j k, |Q j k| ≤ D) (hscale : D * L ^ 2 ≤ Cs * q)
    (hE : ∀ j k, l2NormSq (iterateSpatialWord (j :: k :: w) v) ≤
      B ^ 2 * (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2) :
    |∫ x in unitCube, vecDot (spaceGrad (iterateSpatialWord w u) x)
      (Q.mulVec (spaceGrad (iterateSpatialWord w v) x))| ≤
      l2NormSq (iterateSpatialWord w u) / 4 +
      16 * Cs ^ 2 * q ^ 2 * B ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hp := iterate_primitive_boundary_pairing_bound (iterateSpatialWord_smooth hu w)
    (iterateSpatialWord_smooth hv w) (iterateSpatialWord_periodic hu hup w)
    (iterateSpatialWord_periodic hv hvp w) Q (by norm_num : (0 : ℝ) < 1 / 4) hQ
  have hi (j k : Fin 2) := iterate_unitCube_integrable_of_continuous
    ((iterateSpatialWord_smooth hv (j :: k :: w)).continuous.pow 2)
  change ∀ j k, IntegrableOn (fun x => (iterateSpatialWord (j :: k :: w) v x) ^ 2) unitCube at hi
  have hsum : (∫ x in unitCube, ∑ j : Fin 2, ∑ k : Fin 2,
      (spaceGrad (fun y => spaceGrad (iterateSpatialWord w v) y k) x j) ^ 2) ≤
      4 * B ^ 2 * (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
    change (∫ x in unitCube, ∑ j : Fin 2, ∑ k : Fin 2,
      (iterateSpatialWord (j :: k :: w) v x) ^ 2) ≤ _
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hi
        j k))]
    simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k)]
    change (∑ j : Fin 2, ∑ k : Fin 2, l2NormSq (iterateSpatialWord (j :: k :: w) v)) ≤ _
    have ht := add_le_add (add_le_add (hE 0 0) (hE 0 1)) (add_le_add (hE 1 0) (hE 1 1))
    simp only [Fin.sum_univ_two]
    linarith only [ht]
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr hscale
  have hterm : 16 * D ^ 2 * B ^ 2 *
      (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 ≤
      16 * Cs ^ 2 * q ^ 2 * B ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_right hs
      (by positivity : 0 ≤ 16 * B ^ 2 * (((w.length + 2 + a).factorial : ℝ) * L ^ w.length) ^ 2)
    convert ht using 1
    · simp only [pow_add]
      ring
    · ring
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ D ^ 2 / (1 / 4 : ℝ))
  unfold l2NormSq at hp ⊢
  nlinarith only [hp, hm, hterm]

end AVenhance.Infra.Section4
