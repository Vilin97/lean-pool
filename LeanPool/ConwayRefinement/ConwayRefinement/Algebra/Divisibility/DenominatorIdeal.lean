/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.Ideal.Defs

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Denominator ideals and four-factor refinement

For a subring `R` of a field and a field element `ξ`, the denominator ideal

`I_ξ(R) = {x ∈ R | ξ * x ∈ R}`

packages the possible denominators for `ξ`. Given two nonzero elements `x, y ∈ I_ξ(R)`, their
tautological rank-one equality

`x * (ξ * y) = y * (ξ * x)`

has a four-factor refinement in `R` exactly when `x` and `y` have a common divisor which still
belongs to `I_ξ(R)`. Consequently, a subring of a field has four-factor refinement exactly when
every pair in every denominator ideal has such a common divisor. This is the binary form of the
denominator-ideal criterion used by Zafrullah to characterize pre-Schreier domains.
-/

universe u

public section

namespace Subring

variable {K : Type u} [Field K]

/-- The elements of a subring whose product with `ξ` still lies in the subring. -/
def denominatorIdeal (R : Subring K) (ξ : K) : Ideal R where
  carrier := {x | ξ * (x : K) ∈ R}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simpa [mul_add] using R.add_mem hx hy
  smul_mem' c x hx := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using R.mul_mem c.2 hx

@[simp]
theorem mem_denominatorIdeal_iff (R : Subring K) (ξ : K) (x : R) :
    x ∈ denominatorIdeal R ξ ↔ ξ * (x : K) ∈ R :=
  Iff.rfl

/-- Multiplication by the fraction defining a denominator ideal, with codomain restricted back to
the subring. -/
def denominatorNumerator (R : Subring K) (ξ : K) (x : denominatorIdeal R ξ) : R :=
  ⟨ξ * (x : R), x.2⟩

@[simp]
theorem coe_denominatorNumerator (R : Subring K) (ξ : K)
    (x : denominatorIdeal R ξ) :
    (denominatorNumerator R ξ x : K) = ξ * (x : R) :=
  (rfl)

/-- Two nonzero elements of a denominator ideal have a nonzero common divisor in that ideal
exactly when their associated rank-one equality has a four-factor refinement in the subring. -/
theorem exists_common_divisor_denominatorIdeal_iff_exists_fourFactorRefinement
    (R : Subring K) (ξ : K) (x y : denominatorIdeal R ξ) (hx : (x : R) ≠ 0) :
    (∃ s : denominatorIdeal R ξ,
        (s : R) ∣ (x : R) ∧ (s : R) ∣ (y : R)) ↔
      ∃ e f g h : R,
        (x : R) = e * f ∧ denominatorNumerator R ξ y = g * h ∧
          (y : R) = e * g ∧ denominatorNumerator R ξ x = f * h := by
  constructor
  · rintro ⟨s, ⟨f, hxf⟩, ⟨g, hyg⟩⟩
    let h : R := denominatorNumerator R ξ s
    refine ⟨s, f, g, h, hxf, ?_, hyg, ?_⟩
    · apply Subtype.ext
      change ξ * (y : R) = (g : K) * (h : K)
      rw [hyg]
      change ξ * ((s : K) * g) = (g : K) * (ξ * s)
      ring
    · apply Subtype.ext
      change ξ * (x : R) = (f : K) * (h : K)
      rw [hxf]
      change ξ * ((s : K) * f) = (f : K) * (ξ * s)
      ring
  · rintro ⟨e, f, g, h, hxf, _, hyg, hxh⟩
    have hf0 : (f : K) ≠ 0 := by
      intro hf
      apply hx
      rw [hxf]
      apply Subtype.ext
      simp [hf]
    have hxfK : (x : K) = (e : K) * f := congrArg Subtype.val hxf
    have hxhK : ξ * (x : K) = (f : K) * h := congrArg Subtype.val hxh
    have hξe : ξ * (e : K) = (h : K) := by
      apply mul_right_cancel₀ hf0
      calc
        (ξ * (e : K)) * f = ξ * ((e : K) * f) := by ring
        _ = ξ * (x : K) := by rw [hxfK]
        _ = (f : K) * h := hxhK
        _ = (h : K) * f := by ring
    let s : denominatorIdeal R ξ :=
      ⟨e, (mem_denominatorIdeal_iff R ξ e).2 (by rw [hξe]; exact h.2)⟩
    exact ⟨s, ⟨f, hxf⟩, ⟨g, hyg⟩⟩

/-- A subring of a field has four-factor refinement exactly when every pair in every denominator
ideal has a common divisor belonging to that denominator ideal. -/
theorem hasFourFactorRefinement_iff_forall_denominatorIdeal_exists_common_divisor
    (R : Subring K) :
    HasFourFactorRefinement R ↔
      ∀ (ξ : K) (x y : denominatorIdeal R ξ),
        ∃ s : denominatorIdeal R ξ, (s : R) ∣ (x : R) ∧ (s : R) ∣ (y : R) := by
  constructor
  · intro hR ξ x y
    by_cases hx : (x : R) = 0
    · refine ⟨y, ⟨0, by simp [hx]⟩, ⟨1, by simp⟩⟩
    · apply
        (exists_common_divisor_denominatorIdeal_iff_exists_fourFactorRefinement R ξ x y hx).2
      apply hR.refine
      apply Subtype.ext
      change (x : K) * (ξ * (y : R)) = (y : K) * (ξ * (x : R))
      ring
  · intro h
    apply hasFourFactorRefinement_def.mpr
    intro a b c d habcd
    by_cases hb : b = 0
    · subst b
      have hcd : c * d = 0 := by simpa using habcd.symm
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hcd with hc | hd
      · subst c
        exact ⟨a, 1, 0, d, by simp⟩
      · subst d
        exact ⟨1, a, c, 0, by simp⟩
    · have hbK : (b : K) ≠ 0 := fun h0 ↦ hb (Subtype.ext h0)
      let ξ : K := (d : K) / b
      have hξb : ξ * (b : K) = d := by
        dsimp [ξ]
        field_simp
      have habcdK : (a : K) * b = (c : K) * d := congrArg Subtype.val habcd
      have hξc : ξ * (c : K) = a := by
        dsimp [ξ]
        field_simp
        simpa [mul_comm] using habcdK.symm
      let x : denominatorIdeal R ξ :=
        ⟨b, (mem_denominatorIdeal_iff R ξ b).2 (by rw [hξb]; exact d.2)⟩
      let y : denominatorIdeal R ξ :=
        ⟨c, (mem_denominatorIdeal_iff R ξ c).2 (by rw [hξc]; exact a.2)⟩
      obtain ⟨s, hsx, hsy⟩ := h ξ x y
      obtain ⟨e, f, g, k, hxef, hykg, hyeg, hxhk⟩ :=
        (exists_common_divisor_denominatorIdeal_iff_exists_fourFactorRefinement
          R ξ x y (by exact hb)).1 ⟨s, hsx, hsy⟩
      have hnumx : denominatorNumerator R ξ x = d := by
        apply Subtype.ext
        exact hξb
      have hnumy : denominatorNumerator R ξ y = a := by
        apply Subtype.ext
        exact hξc
      refine ⟨g, k, e, f, ?_, hxef, ?_, ?_⟩
      · calc
          a = denominatorNumerator R ξ y := hnumy.symm
          _ = g * k := hykg
      · simpa [mul_comm] using hyeg
      · calc
          d = denominatorNumerator R ξ x := hnumx.symm
          _ = f * k := hxhk
          _ = k * f := mul_comm _ _

end Subring
