/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCurlCovariance

/-!
# Finite-support sums in physical coordinates

These identities only use finite support and the literal real-coordinate maps.
They let a physical wave assembly retain an unrestricted label `finsum` while
identifying its value with the finite active-label sum.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SignedPhysicalSumCalculus

open Set Function ProblemStatement HarmonicCalculus
open scoped BigOperators

theorem finsum_eq_sum_of_zero_off {α E : Type*} [AddCommMonoid E]
    (s : Finset α) (f : α → E) (hz : ∀ l, l ∉ s → f l = 0) :
    (∑ᶠ l, f l) = ∑ l ∈ s, f l := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro l hl
  by_contra hn
  exact hl (hz l hn)

theorem sum_realCoordinate (v : ComplexVector) :
    (∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (v i)) =
      PhysicalCurlCovariance.realVector v := by
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_succ, PhysicalWaveSum.realCoordinate_apply,
      coordinateVector, PhysicalCurlCovariance.realVector_apply]

/-- An unrestricted scalar-label sum becomes the finite real-part sum once
the labels outside the specified finite set vanish. -/
theorem real_finsum_eq_sum {α : Type*} (s : Finset α) (p : α → ℂ) (q : α → ℝ)
    (hz : ∀ l, l ∉ s → p l = 0) (hreal : ∀ l, (p l).re = q l) :
    (∑ᶠ l, p l).re = ∑ l ∈ s, q l := by
  rw [finsum_eq_sum_of_zero_off s p hz]
  change Complex.reCLM (∑ l ∈ s, p l) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun l _ => hreal l)

/-- Reconstructing the Euclidean vector after the componentwise label sums
agrees exactly with summing the real vectors of the active labels. -/
theorem realCoordinate_finsum_eq_sum {α : Type*} (s : Finset α)
    (F : α → ComplexVector) (G : α → Space)
    (hz : ∀ l, l ∉ s → F l = 0)
    (hreal : ∀ l, PhysicalCurlCovariance.realVector (F l) = G l) :
    (∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (∑ᶠ l, F l i)) =
      ∑ l ∈ s, G l := by
  classical
  have hs (i : Fin 3) : (∑ᶠ l, F l i) = ∑ l ∈ s, F l i :=
    finsum_eq_sum_of_zero_off s (fun l => F l i) (fun l hl => congrFun (hz l hl) i)
  calc
    _ = ∑ i : Fin 3, ∑ l ∈ s, PhysicalWaveSum.realCoordinate i (F l i) := by
      simp only [hs, map_sum]
    _ = ∑ l ∈ s, ∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (F l i) :=
      Finset.sum_comm
    _ = ∑ l ∈ s, G l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [sum_realCoordinate, hreal]

end NavierStokes.SignedPhysicalSumCalculus
