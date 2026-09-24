/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, jayyswan
-/
module

public import LeanPool.HasseMinkowski.HasseInvariant
public import LeanPool.HasseMinkowski.Prod
public import LeanPool.HasseMinkowski.HilbertSymbol.Padic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Rank criteria for the Hasse–Minkowski invariant

This file ports the local representability criteria of HassePrinciple's
`QuadraticForm/HasseMinkowskiInvariant.lean`, connecting the discriminant of a quadratic form
with the Hasse–Minkowski invariant:

* over a rank-two space, a nondegenerate form `Q` represents `a` exactly when
  `(a, -discr Q) = ε(Q)`;
* over a rank-three space, a nondegenerate form `Q` is isotropic exactly when
  `(-1, -discr Q) = ε(Q)`.

The proofs rest on the rank-three isotropy criterion
`weightedSumSquares_isotropic_iff_hilbertSym_eq_one` and the Hilbert-symbol square-class
computation `hilbertSym_mul_mul`, both of which are proved unconditionally here.

The well-definedness of `hasseMinkowskiInv` (that equivalent diagonal forms have the same
invariant) is *not* available in this project, so no theorem at the level of that form-level
invariant is stated.  The invariant-free (diagonal) forms of the criteria are stated and proved
with `hasseMinkowskiInvAux` and need no such hypothesis.

## Provenance

This file is a derived work.  It is based on `QuadraticForm/HasseMinkowskiInvariant.lean` of the
HassePrinciple project (<https://github.com/mariainesdff/HassePrinciple>,
Apache-2.0, Copyright (c) 2026 Nirvana Coppola,
María Inés de Frutos-Fernández), a Women in Numbers 7 collaboration.
It has been modified: the statements and proofs were rewritten for Lean 4.33 /
Mathlib without upstream's module system, and the development is extended beyond
what upstream proves.  Upstream declaration names are kept so that the two
developments can be compared side by side.  See the repository NOTICE file.
-/

@[expose] public section

open Module QuadraticMap

namespace QuadraticMap

namespace Equivalent

variable {R M₁ M₂ N : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid N] [Module R M₁] [Module R M₂] [Module R N]

-- Theorem: equivalent quadratic maps are isotropic simultaneously.
theorem isotropic_iff {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (h : Q₁.Equivalent Q₂) :
    HasseMinkowski.Isotropic Q₁ ↔ HasseMinkowski.Isotropic Q₂ := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨x, hx, hxQ⟩
    exact ⟨e x, fun h0 => hx (by simpa using congrArg (⇑e.symm) h0),
      by rw [e.map_app x, hxQ]⟩
  · rintro ⟨x, hx, hxQ⟩
    exact ⟨e.symm x, fun h0 => hx (by simpa using congrArg (⇑e) h0),
      by rw [e.symm.map_app x, hxQ]⟩

end Equivalent

end QuadraticMap

namespace HasseMinkowski

variable {k : Type*} [Field k]

/-! ### Hilbert-symbol helpers -/

-- Theorem: `hilbertSym a b = 1` exactly when the conic `z² = a x² + b y²` has a nontrivial
-- solution (for nonzero `a`, `b`).
theorem hilbertSym_eq_one_iff {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ↔
      ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  have h : ¬ (a = 0 ∨ b = 0) := by tauto
  unfold hilbertSym
  rw [ite_eq_right h]
  by_cases hs : ∃ z x y : k,
      (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
  · rw [ite_eq_left hs]
    exact ⟨fun _ => hs, fun _ => rfl⟩
  · rw [ite_eq_right hs]
    exact ⟨fun h1 => absurd h1 (by norm_num), fun h2 => absurd h2 hs⟩

-- Theorem: `hilbertSym a (-a) = 1` for `a ≠ 0`.
theorem hilbertSym_right_neg_self {a : k} (ha : a ≠ 0) : hilbertSym a (-a) = 1 :=
  hilbertSym_eq_one_of_sol ha (neg_ne_zero.mpr ha) ⟨0, 1, 1, by simp, by ring⟩

-- Theorem: `hilbertSym (-1) a` is its own inverse.
theorem hilbertSym_neg_one_mul_self {a : k} (ha : a ≠ 0) :
    hilbertSym (-1 : k) a * hilbertSym (-1) a = 1 := by
  rcases hilbertSym_eq_one_or_neg_one_of_ne_zero (by norm_num : (-1 : k) ≠ 0) ha with h | h
  · rw [h, mul_one]
  · rw [h, neg_mul_neg, one_mul]

section Bilin

variable [HasBilinHilbertSym k]

-- Theorem: `hilbertSym a a = hilbertSym a (-1)`.
theorem hilbertSym_self {a : k} : hilbertSym a a = hilbertSym a (-1) := by
  by_cases ha : a = 0
  · simp [hilbertSym, ha]
  · nth_rewrite 2 [show a = (-1 : k) * -a by ring]
    rw [HasBilinHilbertSym.mul_right_eq, hilbertSym_right_neg_self ha, mul_one]

-- Theorem: `hilbertSym a a = hilbertSym (-1) a`.
theorem hilbertSym_self_eq_left_neg_one {a : k} :
    hilbertSym a a = hilbertSym (-1) a := by
  rw [hilbertSym_self, hilbertSym_comm a (-1)]

-- Theorem: `hilbertSym (-(a * b)) b = hilbertSym a b`.
theorem hilbertSym_left_neg_mul {a b : k} : hilbertSym (-(a * b)) b = hilbertSym a b := by
  rw [show -(a * b) = ((-1 : k) * a) * b by ring]
  rw [HasBilinHilbertSym.mul_left_eq, HasBilinHilbertSym.mul_left_eq]
  by_cases hb : b = 0
  · simp [hilbertSym, hb]
  · calc (hilbertSym (-1 : k) b * hilbertSym a b) * hilbertSym b b
        = (hilbertSym (-1 : k) b * hilbertSym (-1) b) * hilbertSym a b := by
          rw [hilbertSym_self_eq_left_neg_one]; ring
      _ = 1 * hilbertSym a b := by rw [hilbertSym_neg_one_mul_self hb]
      _ = hilbertSym a b := one_mul _

-- Theorem: `hilbertSym (c * a) (c * b) = hilbertSym c (-(a * b)) * hilbertSym a b`.
theorem hilbertSym_mul_mul {a b c : k} :
    hilbertSym (c * a) (c * b) = hilbertSym c (-(a * b)) * hilbertSym a b := by
  by_cases hc : c = 0
  · subst hc; simp [hilbertSym]
  rw [show -(a * b) = (-1 : k) * (a * b) by ring]
  simp only [HasBilinHilbertSym.mul_left_eq, HasBilinHilbertSym.mul_right_eq]
  rw [hilbertSym_self_eq_left_neg_one, hilbertSym_comm (-1) c, hilbertSym_comm a c]
  ring

end Bilin

/-! ### The rank-three isotropy criterion -/

-- Theorem: the diagonal form `a x₀² + b x₁² + c x₂²` is isotropic exactly when
-- `(-c a, -c b) = 1` (for nonzero `a`, `b`, `c`).
theorem weightedSumSquares_isotropic_iff_hilbertSym_eq_one (a b c : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (weightedSumSquares k ![a, b, c]).Isotropic ↔ hilbertSym (-c * a) (-c * b) = 1 := by
  have key : ∀ x : Fin 3 → k,
      (weightedSumSquares k ![a, b, c]) x = a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 := by
    intro x
    simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]
  rw [hilbertSym_eq_one_iff (mul_ne_zero (neg_ne_zero.mpr hc) ha)
    (mul_ne_zero (neg_ne_zero.mpr hc) hb)]
  constructor
  · rintro ⟨x, hx, hxQ⟩
    rw [key] at hxQ
    refine ⟨c * x 2, x 0, x 1, ?_, ?_⟩
    · intro h0
      apply hx
      have h1 : c * x 2 = 0 := by simpa using congrArg Prod.fst h0
      have h2 : x 0 = 0 := by simpa using congrArg (fun p : k × k × k => p.2.1) h0
      have h3 : x 1 = 0 := by simpa using congrArg (fun p : k × k × k => p.2.2) h0
      have h2' : x 2 = 0 := (mul_eq_zero.mp h1).resolve_left hc
      funext i
      fin_cases i <;> simp [h2', h2, h3]
    · linear_combination c * hxQ
  · rintro ⟨z, x, y, hne, heq⟩
    refine ⟨![c * x, c * y, z], ?_, ?_⟩
    · intro h0
      apply hne
      have h1 := congr_fun h0 0
      have h2 := congr_fun h0 1
      have h3 := congr_fun h0 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at h1 h2 h3
      exact Prod.ext h3 (Prod.ext ((mul_eq_zero.mp h1).resolve_left hc)
        ((mul_eq_zero.mp h2).resolve_left hc))
    · rw [key]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination c * heq

-- Theorem: the special case `⟨a, b, 1⟩` of the rank-three isotropy criterion.
theorem weightedSumSquares_isotropic_iff_hilbertSym_eq_one' (a b : k) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (weightedSumSquares k ![a, b, 1]).Isotropic ↔ hilbertSym (-a) (-b) = 1 := by
  simpa using weightedSumSquares_isotropic_iff_hilbertSym_eq_one a b 1 ha hb one_ne_zero

-- Theorem: the weighted sum of squares with unit weights agrees with the one whose weights are
-- the coerced units.
theorem weightedSumSquares_units_coe {ι : Type*} [Fintype ι] (w : ι → kˣ) :
    weightedSumSquares k w = weightedSumSquares k (fun i => (w i : k)) := by
  apply QuadraticMap.ext
  intro x
  simp only [weightedSumSquares_apply, Units.smul_def, smul_eq_mul]

/-! ### The rank-three criterion for the Hasse–Minkowski invariant -/

section Criteria

variable [HasBilinHilbertSym k]

-- Theorem: the Hilbert-symbol identity behind the ternary criterion:
-- `(-c a, -c b) = (-1, -(a b c)) · (a,b)(a,c)(b,c)`.
theorem hilbertSym_mul_mul_neg (a b c : k) :
    hilbertSym (-c * a) (-c * b) =
      hilbertSym (-1) (-(a * b * c)) *
        (hilbertSym a b * hilbertSym a c * hilbertSym b c) := by
  have h1 := hilbertSym_mul_mul (a := a) (b := b) (c := -c)
  have h2 := hilbertSym_mul_mul (a := a * b) (b := c) (c := -1)
  simp only [neg_one_mul] at h2
  rw [h1, hilbertSym_comm (-c) (-(a * b)), h2, HasBilinHilbertSym.mul_left_eq]
  ring

-- Theorem: `x * y = 1 ↔ x = y` for signs `x`, `y`.
theorem mul_eq_one_iff_eq_of_signs {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ↔ x = y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num

-- Theorem: the rank-three criterion for a diagonal form: `⟨a,b,c⟩` is isotropic exactly when
-- `(-1, -(a b c)) = ε(⟨a,b,c⟩)`.
theorem represents_zero_iff_of_rank_three_diag (a b c : kˣ) :
    (weightedSumSquares k ![a, b, c]).Isotropic ↔
      hilbertSym (-1) (-((a : k) * (b : k) * (c : k))) = hasseMinkowskiInvAux ![a, b, c] := by
  change (weightedSumSquares k ![(a : k), (b : k), (c : k)]).Isotropic ↔
      hilbertSym (-1) (-((a : k) * (b : k) * (c : k))) = hasseMinkowskiInvAux ![a, b, c]
  rw [hasseMinkowskiInvAux_three,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one (a : k) (b : k) (c : k)
      a.ne_zero b.ne_zero c.ne_zero,
    hilbertSym_mul_mul_neg]
  refine mul_eq_one_iff_eq_of_signs ?_ ?_
  · exact hilbertSym_eq_one_or_neg_one_of_ne_zero (by norm_num) (by
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero a.ne_zero b.ne_zero) c.ne_zero))
  · rcases hilbertSym_eq_one_or_neg_one_of_ne_zero a.ne_zero b.ne_zero with h | h <;>
      rcases hilbertSym_eq_one_or_neg_one_of_ne_zero a.ne_zero c.ne_zero with h' | h' <;>
      rcases hilbertSym_eq_one_or_neg_one_of_ne_zero b.ne_zero c.ne_zero with h'' | h'' <;>
      simp [h, h', h'']

end Criteria

end HasseMinkowski
