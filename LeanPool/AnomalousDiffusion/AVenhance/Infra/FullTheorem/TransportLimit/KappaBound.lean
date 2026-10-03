/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.DriftData

/-!
# The viscous remainder vanishes with the diffusivity

`|κ ∫∫ D·G| ≤ (√κ/2) (κ ∫∫ |D|² + ∑ᵢ ∫∫ Gᵢ²)` by a pointwise weighted Young inequality, so
together with the energy bound `κ ∫∫ |D|² ≤ ‖θ₀‖²/2` the remainder is `O(√κ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

theorem abs_young_weighted (e x y : ℝ) (he : 0 ≤ e) :
    |e ^ 2 * (x * y)| ≤ e / 2 * (e ^ 2 * x ^ 2 + y ^ 2) := by
  have h : |(e * x) * y| ≤ ((e * x) ^ 2 + y ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (e * x + y), sq_nonneg (e * x - y)]
  have h2 : |e ^ 2 * (x * y)| = e * |(e * x) * y| := by
    rw [show e ^ 2 * (x * y) = e * ((e * x) * y) by ring, abs_mul, abs_of_nonneg he]
  rw [h2]
  calc e * |(e * x) * y| ≤ e * (((e * x) ^ 2 + y ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h he
    _ = e / 2 * (e ^ 2 * x ^ 2 + y ^ 2) := by ring

theorem kappa_term_bound {D G : ℝ × Vec 2 → Vec 2}
    (hD : ∀ i, MemLp (fun p => D p i) 2 (volume.restrict timeCube))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict timeCube))
    {κ : ℝ} (hκ : 0 < κ) :
    |κ * ∫ p in timeCube, vecDot (D p) (G p)| ≤
      Real.sqrt κ / 2 * (κ * (∫ p in timeCube, vecNormSq (D p)) +
        ∑ i : Fin 2, ∫ p in timeCube, G p i ^ 2) := by
  have hDi (i : Fin 2) : Integrable (fun p => D p i ^ 2) (volume.restrict timeCube) :=
    (memLp_two_iff_integrable_sq (hD i).aestronglyMeasurable).1 (hD i)
  have hGi (i : Fin 2) : Integrable (fun p => G p i ^ 2) (volume.restrict timeCube) :=
    (memLp_two_iff_integrable_sq (hG i).aestronglyMeasurable).1 (hG i)
  have hDG (i : Fin 2) : Integrable (fun p => D p i * G p i) (volume.restrict timeCube) :=
    ((hD i).mul (hG i) : MemLp (fun p => D p i * G p i) 1 _).integrable le_rfl
  set e := Real.sqrt κ with he
  have hκe : κ = e ^ 2 := (Real.sq_sqrt hκ.le).symm
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  let W : ℝ × Vec 2 → ℝ := fun p =>
    ∑ i : Fin 2, e / 2 * (e ^ 2 * D p i ^ 2 + G p i ^ 2)
  have iW : Integrable W (volume.restrict timeCube) :=
    integrable_finsetSum _ fun i _ => (((hDi i).const_mul (e ^ 2)).add (hGi i)).const_mul (e / 2)
  have hpt : ∀ p, ‖κ * vecDot (D p) (G p)‖ ≤ W p := by
    intro p
    rw [Real.norm_eq_abs, vecDot, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hκe]
    exact abs_young_weighted e (D p i) (G p i) he0
  have hint : Integrable (fun p => κ * vecDot (D p) (G p)) (volume.restrict timeCube) := by
    have : Integrable (fun p => ∑ i : Fin 2, κ * (D p i * G p i)) (volume.restrict timeCube) :=
      integrable_finsetSum _ fun i _ => (hDG i).const_mul κ
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [vecDot, ← Finset.mul_sum]
  have h1 := norm_integral_le_of_norm_le iW (Filter.Eventually.of_forall hpt)
    (f := fun p => κ * vecDot (D p) (G p))
  rw [integral_const_mul] at h1
  have hWint : ∫ p in timeCube, W p =
      e / 2 * (e ^ 2 * (∫ p in timeCube, vecNormSq (D p)) +
        ∑ i : Fin 2, ∫ p in timeCube, G p i ^ 2) := by
    have hN : ∫ p in timeCube, vecNormSq (D p) = ∑ i : Fin 2, ∫ p in timeCube, D p i ^ 2 := by
      rw [← integral_finsetSum _ (fun i _ => hDi i)]
      congr 1; funext p
      simp [vecNormSq, vecDot, sq]
    rw [hN]
    have hI (i : Fin 2) : ∫ p in timeCube, e / 2 * (e ^ 2 * D p i ^ 2 + G p i ^ 2) =
        e / 2 * (e ^ 2 * (∫ p in timeCube, D p i ^ 2) + ∫ p in timeCube, G p i ^ 2) := by
      rw [integral_const_mul, integral_add ((hDi i).const_mul _) (hGi i), integral_const_mul]
    change ∫ p in timeCube, ∑ i : Fin 2, e / 2 * (e ^ 2 * D p i ^ 2 + G p i ^ 2) = _
    have hIi (i : Fin 2) : Integrable
        (fun p : ℝ × Vec 2 => e / 2 * (e ^ 2 * D p i ^ 2 + G p i ^ 2))
        (volume.restrict timeCube) :=
      (((hDi i).const_mul (e ^ 2)).add (hGi i)).const_mul (e / 2)
    rw [integral_finsetSum _ (fun i _ => hIi i)]
    rw [Finset.sum_congr rfl (fun i _ => hI i)]
    simp only [Fin.sum_univ_two]
    ring
  rw [Real.norm_eq_abs, hWint] at h1
  rw [hκe]
  rw [hκe] at h1
  exact h1

end AVenhance.Infra.FullTheorem.TransportLimit
