/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesOscillatory

/-! Matrix Young allocation on each actual terminal-time cell. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Matrix Young control on the space-time cell. -/
theorem iterate_spacetime_matrix_absolute_integral_bound
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {a b : ℝ → Vec 2 → Vec 2} {ρ D : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t x i j, |A t x i j| ≤ D)
    (ha : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (a p.1 p.2)) timeCube)
    (hb : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (b p.1 p.2)) timeCube)
    (hp : IntegrableOn (fun p : ℝ × Vec 2 =>
      vecDot (a p.1 p.2) ((A p.1 p.2).mulVec (b p.1 p.2))) timeCube) :
    (∫ p in timeCube, |vecDot (a p.1 p.2) ((A p.1 p.2).mulVec (b p.1 p.2))|) ≤
      ρ * spaceTimeGradNormSq a + D ^ 2 / ρ * spaceTimeGradNormSq b := by
  have h := integral_mono hp.abs ((ha.const_mul ρ).add (hb.const_mul (D ^ 2 / ρ)))
    (fun p => iterate_matrix_pairing_abs_bound hρ (A p.1 p.2) (a p.1 p.2) (b p.1 p.2)
      (hA p.1 p.2))
  change (∫ p in timeCube, |vecDot (a p.1 p.2) ((A p.1 p.2).mulVec (b p.1 p.2))|) ≤
    (∫ p in timeCube, ρ * vecNormSq (a p.1 p.2) + D ^ 2 / ρ * vecNormSq (b p.1 p.2)) at h
  rw [integral_add (ha.const_mul ρ) (hb.const_mul (D ^ 2 / ρ)),
    integral_const_mul, integral_const_mul] at h
  exact h

/-- Every terminal signed matrix pairing has the full nonnegative Young budget. -/
theorem iterate_truncated_matrix_pairing_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {a b : ℝ → Vec 2 → Vec 2} {ρ D : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t x i j, |A t x i j| ≤ D)
    (ha : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (a p.1 p.2)) timeCube)
    (hb : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (b p.1 p.2)) timeCube)
    (hp : IntegrableOn (fun p : ℝ × Vec 2 =>
      vecDot (a p.1 p.2) ((A p.1 p.2).mulVec (b p.1 p.2))) timeCube) :
    |∫ p in iterateTruncatedCell s, vecDot (a p.1 p.2) ((A p.1 p.2).mulVec (b p.1 p.2))| ≤
      ρ * spaceTimeGradNormSq a + D ^ 2 / ρ * spaceTimeGradNormSq b := by
  exact (iterate_truncated_integral_abs_le hp hs1).trans
    (iterate_spacetime_matrix_absolute_integral_bound hρ hA ha hb hp)

end AVenhance.Infra.Section4
