/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHalfSquareBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousHessianMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHessianComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHalfSquareScale

/-! # Iterates Actual Homogeneous Half Square

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual first-increment half-square has a q-squared analytic budget.
Material energies are derived from the homogeneous PDE, not assumed. -/
theorem iterate_actual_homogeneous_half_square_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κ : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κ)
    {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel (Φ (m - 1))) κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    {B N r L C D q s : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hq : 0 ≤ q) (hL : 0 < L) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hg : 2 * (r / L) ^ 2 ≤ 1 / 2) (hscale : B * r ≤ C * κ * L ^ 2)
    (hQb : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D)
    (hQscale : D * L ^ 2 ≤ C * q)
    (hjet : ∀ j k t x p, p ∈ (iterateSpatialSplits (j :: k :: w)).filter
      (fun p => decide (1 ≤ p.1.length)) → ∀ a,
      |iterateSpatialWord p.1 (fun y => streamVel (Φ (m - 1)) t y a) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ v : List (Fin 2), v.length ≤ w.length + 3 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (u t))) ≤
        (N / Real.sqrt κ) ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2)
    (hTE : ∀ j k, l2NormSq (iterateSpatialWord (j :: k :: w) (u s)) ≤
      (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2) :
    |∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (u t) x) *
      (∑ j : Fin 2, ∑ k : Fin 2, iterateKmatPrimitive I κm m t j k *
        iterateSpatialWord (j :: k :: w) (u t) x)| ≤
      (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 * q ^ 2 *
        (N * ((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
  let R := Real.sqrt (8 + 64 * C ^ 2)
  let G := N / Real.sqrt κ * ((w.length + 1).factorial : ℝ) * L ^ (w.length + 1)
  let M := R * Real.sqrt κ * N * ((w.length + 3).factorial : ℝ) * L ^ (w.length + 3)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRs : R ^ 2 = 8 + 64 * C ^ 2 := Real.sq_sqrt (by positivity)
  have hGe (j k : Fin 2) :
      (∫ z in timeCube, (iterateSpatialWord (j :: k :: w) (u z.1) z.2) ^ 2) ≤ G ^ 2 := by
    have ht := (iterate_hessian_word_component_energy_bound hsol.1 w j k).trans
      (hE (k :: w) (by simp))
    simpa only [G, List.length_cons, mul_pow, mul_assoc] using ht
  have hMe (j k : Fin 2) :
      (∫ z in timeCube, (amnrMaterial (streamVel (Φ (m - 1)))
        (fun t => iterateSpatialWord (j :: k :: w) (u t)) z.1 z.2) ^ 2) ≤ M ^ 2 := by
    have ht := iterate_homogeneous_hessian_material_energy_bound hsol hb w j k
      hB hr hC hκ hL hg hscale (hjet j k) hE
    have he : M ^ 2 = (8 + 64 * C ^ 2) * κ * N ^ 2 *
        (((w.length + 3).factorial : ℝ) * L ^ (w.length + 3)) ^ 2 := by
      dsimp only [M]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hRs, Real.sq_sqrt hκ.le]
      ring
    rw [he]
    exact ht
  have ht := iterate_actual_hessian_half_square_bound I hΦ hm hκm hsol.1 (fun t ht => hsol.2.1 t
      ht.le) w
    hD (by dsimp only [G]; positivity) (by dsimp only [M]; positivity)
    hs hs1 hQb hGe hMe hTE
  have hMG : M * G = R * N ^ 2 * ((w.length + 1).factorial : ℝ) *
      ((w.length + 3).factorial : ℝ) * L ^ (w.length + 1) * L ^ (w.length + 3) := by
    have hn := iterate_diffusive_material_product (N := N) (R := R) hκ
    calc
      _ = ((R * Real.sqrt κ * N) * (N / Real.sqrt κ)) *
        ((w.length + 1).factorial : ℝ) * ((w.length + 3).factorial : ℝ) *
        L ^ (w.length + 1) * L ^ (w.length + 3) := by dsimp only [M, G]; ring
      _ = _ := by rw [hn]
  have ht' : 8 * D ^ 2 * (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      16 * D ^ 2 * M * G =
      8 * D ^ 2 * (N * ((w.length + 2).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 +
      16 * D ^ 2 * R * N ^ 2 * ((w.length + 1).factorial : ℝ) *
        ((w.length + 3).factorial : ℝ) * L ^ (w.length + 1) * L ^ (w.length + 3) := by
    rw [mul_assoc (16 * D ^ 2) M G, hMG]
    ring
  rw [ht'] at ht
  exact ht.trans (iterate_half_square_scale_bound w.length hD hL hC hq hR hQscale)

end AVenhance.Infra.Section4
