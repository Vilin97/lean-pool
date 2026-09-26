/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Data.Finset.Density
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite word spaces

Uniform density, fibers, and elementary averaging results used in the density Hales--Jewett
argument.  We use `Finset.dens` for uniform density, `Sum.elim` to concatenate words on disjoint
coordinate types, and `Equiv.sumArrowEquivProdArrow` for the underlying decomposition of a word on
a sum of coordinate types.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHalesJewett

/-- The fiber of a word family above a fixed prefix.  Words on a sum of coordinate types are
concatenations `Sum.elim x y` of their two parts. -/
def fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) :=
  Finset.univ.filter fun y ↦ Sum.elim x y ∈ A

@[simp]
lemma mem_fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {A : Finset (ι ⊕ κ → α)} {x : ι → α} {y : κ → α} :
    y ∈ fiber A x ↔ Sum.elim x y ∈ A := by
  simp [fiber]

/-- Uniform density is the average of the uniform densities of the fibers. -/
lemma average_density_fiber {α ι κ : Type*} [Fintype (ι → α)] [Fintype (κ → α)]
    [Fintype (ι ⊕ κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    (𝔼 x : ι → α, ((fiber A x).dens : ℝ)) = (A.dens : ℝ) := by
  classical
  simp_rw [← Finset.expect_indicator_one]
  rw [← Finset.expect_product']
  apply Finset.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ α).symm
  · simp
  · rintro ⟨x, y⟩ -
    simp [Set.indicator_apply, Equiv.sumArrowEquivProdArrow]

/-- A bounded function with large average exceeds a lower threshold on a quantitatively large
set. -/
lemma density_ge_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (a b : ℝ) (hf₁ : ∀ x, f x ≤ 1)
    (hba : b < a) (havg : a ≤ 𝔼 x : X, f x) :
    (a - b) / (1 - b) ≤
      ((Finset.univ.filter fun x ↦ b ≤ f x).dens : ℝ) := by
  classical
  let H := Finset.univ.filter fun x ↦ b ≤ f x
  change (a - b) / (1 - b) ≤ (H.dens : ℝ)
  have h1b : 0 < 1 - b := by
    rw [sub_pos]
    exact hba.trans_le <| havg.trans <|
      Finset.expect_le Finset.univ_nonempty fun x _ ↦ hf₁ x
  rw [div_le_iff₀ h1b, sub_le_iff_le_add]
  apply havg.trans
  convert Finset.expect_le_expect (s := Finset.univ) (f := f)
    (g := fun x ↦ b + (1 - b) * Set.indicator (H : Set X) 1 x) ?_ using 1
  · symm
    rw [Finset.expect_add_distrib]
    simp only [Fintype.expect_const, ← Finset.mul_expect, Finset.expect_indicator_one]
    ring
  · intro x _
    by_cases hx : b ≤ f x <;> simp [H, hx] <;> linarith [hf₁ x]

end DensityHalesJewett
