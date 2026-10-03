/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusiveMaterialScale

/-! # Iterates Homogeneous Hessian Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual homogeneous Hessian material energy follows from scalar
conditional analytic gradient energies and the drift derivative profile. -/
theorem iterate_homogeneous_hessian_material_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (j k : Fin 2)
    {B N r L C : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hκ : 0 < κ) (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hscale : B * r ≤ C * κ * L ^ 2)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits (j :: k :: w)).filter
      (fun p => decide (1 ≤ p.1.length)) → ∀ a,
      |iterateSpatialWord p.1 (fun y => b t y a) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length + 3 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤
        (N / Real.sqrt κ) ^ 2 * ((q.length.factorial : ℝ) * L ^ q.length) ^ 2) :
    (∫ z in timeCube,
      (amnrMaterial b (fun t => iterateSpatialWord (j :: k :: w) (u t)) z.1 z.2) ^ 2) ≤
      (8 + 64 * C ^ 2) * κ * N ^ 2 *
        (((w.length + 3).factorial : ℝ) * L ^ (w.length + 3)) ^ 2 := by
  have ht := iterate_analytic_homogeneous_material_energy_bound hsol hb (j :: k :: w) 0
    hB hr hC hκ hL hg hscale hjet
    (fun q hq => by simpa only [Nat.add_zero] using hE q (by simpa using hq))
  simp only [List.length_cons, Nat.add_zero] at ht
  have hn := iterate_diffusive_material_normalization (N := N) hκ
  have he : (8 + 64 * C ^ 2) * κ ^ 2 * (N / Real.sqrt κ) ^ 2 =
      (8 + 64 * C ^ 2) * κ * N ^ 2 := by
    calc
      _ = (8 + 64 * C ^ 2) * (κ ^ 2 * (N / Real.sqrt κ) ^ 2) := by ring
      _ = _ := by rw [hn]; ring
  rw [he] at ht
  exact ht

end AVenhance.Infra.Section4
