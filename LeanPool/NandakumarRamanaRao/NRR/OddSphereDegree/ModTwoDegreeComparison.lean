/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AntipodalDegree

/-!
# Mod-two comparison of integer degree

Arithmetic and topological wrappers connecting parity of an integer degree with its reduction in
`ZMod 2`. The file provides cast/parity lemmas and comparison theorems for `degreeOfIso` and the
oriented degree API. Native coefficient-reduction and sphere top-class constructions are supplied
by the dedicated coefficient-reduction modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-! ## 1. Arithmetic parity / cast bridges `ℤ → ZMod 2`

These are pure arithmetic facts about the mod-2 reduction ring hom
`Int.castRingHom (ZMod 2)`; they carry the entire "comparison" between the
integer phrasing `Odd z` and the `F₂` phrasing `(z : ZMod 2) = 1`. They are
independent of all topology. -/

/-- **The parity bridge.** For an integer `z`, its reduction in `ZMod 2` is `1`
iff `z` is odd. This is the entire comparison content of Route A: it converts the
`F₂` statement `(degree f : ZMod 2) = 1` into the integer statement
`Odd (degree f)` and back. -/
theorem intCast_zmodTwo_eq_one_iff_odd (z : ℤ) : (z : ZMod 2) = 1 ↔ Odd z := by
  have h : ((z : ZMod 2) = 1) ↔ ((1 : ℤ) : ZMod 2) = (z : ZMod 2) := by
    rw [eq_comm]; norm_num
  rw [h, ZMod.intCast_eq_intCast_iff, Int.ModEq, Int.odd_iff]; omega

/-- For an integer `z`, its reduction in `ZMod 2` is `0` iff `z` is even. -/
theorem intCast_zmodTwo_eq_zero_iff_even (z : ℤ) : (z : ZMod 2) = 0 ↔ Even z := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.even_iff]; omega

/-- Forward direction of the parity bridge: an odd integer reduces to `1`. -/
theorem Odd.intCast_zmodTwo {z : ℤ} (h : Odd z) : (z : ZMod 2) = 1 :=
  (intCast_zmodTwo_eq_one_iff_odd z).mpr h

/-- Backward direction of the parity bridge: an integer reducing to `1` is odd. -/
theorem odd_of_intCast_zmodTwo_eq_one {z : ℤ} (h : (z : ZMod 2) = 1) : Odd z :=
  (intCast_zmodTwo_eq_one_iff_odd z).mp h

/-- An even integer reduces to `0`. -/
theorem Even.intCast_zmodTwo {z : ℤ} (h : Even z) : (z : ZMod 2) = 0 :=
  (intCast_zmodTwo_eq_zero_iff_even z).mpr h

/-- An integer reducing to `0` is even. -/
theorem even_of_intCast_zmodTwo_eq_zero {z : ℤ} (h : (z : ZMod 2) = 0) : Even z :=
  (intCast_zmodTwo_eq_zero_iff_even z).mp h

/-- The mod-2 reduction of any integer is either `0` or `1`. -/
theorem intCast_zmodTwo_eq_zero_or_one (z : ℤ) :
    (z : ZMod 2) = 0 ∨ (z : ZMod 2) = 1 := by
  rcases Int.even_or_odd z with h | h
  · exact Or.inl (Even.intCast_zmodTwo h)
  · exact Or.inr (Odd.intCast_zmodTwo h)

/-- **Multiplicativity of the reduction.** Reduction mod `2` is a ring hom, so it
takes products to products. This is the algebraic shadow of degree
multiplicativity `degree (g ∘ f) = degree g * degree f`. -/
theorem intCast_zmodTwo_mul (z w : ℤ) :
    ((z * w : ℤ) : ZMod 2) = (z : ZMod 2) * (w : ZMod 2) := by
  push_cast; ring

/-- **Conversion-free corollary.** Any integer that is `1` or `-1` reduces to `1`
in `ZMod 2`. This applies directly to `±1` degrees (homeomorphisms, the antipodal
map) without going through `Odd`. -/
theorem intCast_zmodTwo_eq_one_of_eq_one_or_neg_one {z : ℤ}
    (h : z = 1 ∨ z = -1) : (z : ZMod 2) = 1 := by
  rcases h with h | h <;> rw [h] <;> decide

/-! ### 1b. Parity equivalences and reversed cast bridges

These complete the elementary parity algebra needed by the
`ModTwoTopClassComparison` branch, so that no downstream module has to re-prove it.
They are pure arithmetic, independent of all topology. -/

/-- Reversed form of the parity bridge: `z` is odd iff its reduction in `ZMod 2`
is `1`. Convenient when the hypothesis is phrased as `Odd z`. -/
theorem odd_iff_intCast_zmodTwo_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 :=
  (intCast_zmodTwo_eq_one_iff_odd z).symm

/-- Reversed form of the even cast bridge: `z` is even iff its reduction in
`ZMod 2` is `0`. -/
theorem even_iff_intCast_zmodTwo_eq_zero (z : ℤ) : Even z ↔ (z : ZMod 2) = 0 :=
  (intCast_zmodTwo_eq_zero_iff_even z).symm

/-- An integer is odd iff it is not even (project-local re-export of
`Int.not_even_iff_odd`, in the `Odd ↔ ¬ Even` orientation). -/
theorem odd_iff_not_even (z : ℤ) : Odd z ↔ ¬ Even z :=
  Int.not_even_iff_odd.symm

/-- An integer fails to be even iff it is odd (project-local re-export of
`Int.not_even_iff_odd`). -/
theorem not_even_iff_odd (z : ℤ) : ¬ Even z ↔ Odd z :=
  Int.not_even_iff_odd

/-! ### 1c. Scalar action over `ZMod 2`

The algebraic shadow of the top-class fixed-point condition: in *any* `ZMod 2`
-module, a scalar fixes a nonzero vector iff the scalar is `1`. This is exactly
the step that turns `f_* z = a • z` with `z ≠ 0` into `a = 1`, used by the
top-homology scalar branch. It needs no one-dimensionality: `ZMod 2 = {0, 1}`. -/

/-- **Scalar action over `ZMod 2`.** For a nonzero vector `x` in a `ZMod 2`
-module, `a • x = x` iff `a = 1`. (The only other scalar is `0`, which sends `x`
to `0 ≠ x`.) -/
theorem zmodTwo_smul_eq_self_iff {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {x : M} (hx : x ≠ 0) (a : ZMod 2) : a • x = x ↔ a = 1 := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  constructor
  · intro h
    rcases ha with rfl | rfl
    · rw [zero_smul] at h; exact absurd h.symm hx
    · rfl
  · rintro rfl; rw [one_smul]

/-! ## 2. Mod-2 reduction of the conditional degree (Route A)

We attach the parity statement to the genuine integer degree `degreeOfIso e f`
by reducing it modulo `2`. Every statement is conditional on a chosen
identification `e : SphereTopHomologyIso n`, like the rest of the degree API. -/

/-- **The mod-2 degree comparison theorem.** The reduction of the integer degree
to `ZMod 2` equals `1` iff the integer degree is odd. This is the precise sense
in which "`(degree f : ZMod 2) = 1`" and "`Odd (degree f)`" are interchangeable —
the two phrasings of the final odd-degree theorem. -/
theorem degreeOfIso_intCast_zmodTwo_eq_one_iff_odd {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) :
    ((degreeOfIso e f : ZMod 2) = 1) ↔ Odd (degreeOfIso e f) :=
  intCast_zmodTwo_eq_one_iff_odd _

/-- **Multiplicativity of the mod-2 degree.** The reduction of the degree of a
composite is the product of the reductions. This descends `degreeOfIso_comp`
through the reduction ring hom. -/
theorem degreeOfIso_comp_intCast_zmodTwo {n : ℕ}
    (e : SphereTopHomologyIso n) (f g : C(Sphere n, Sphere n)) :
    ((degreeOfIso e (g.comp f) : ZMod 2))
      = (degreeOfIso e g : ZMod 2) * (degreeOfIso e f : ZMod 2) := by
  rw [degreeOfIso_comp, intCast_zmodTwo_mul]

/-- **The mod-2 degree of a self-homeomorphism is `1`** (its integer degree is
`±1`, hence odd). -/
theorem degreeOfIso_homeomorph_intCast_zmodTwo_eq_one {n : ℕ}
    (e : SphereTopHomologyIso n) (h : Sphere n ≃ₜ Sphere n) :
    ((degreeOfIso e (h : C(Sphere n, Sphere n)) : ZMod 2)) = 1 :=
  intCast_zmodTwo_eq_one_of_eq_one_or_neg_one
    (degreeOfIso_homeomorph_eq_one_or_neg_one e h)

/-- **The mod-2 degree of the antipodal map is `1`.** This is the `F₂` phrasing of
the proved parity fact `Odd (degree (antipodal n))`, and the parity content of
the classical value `degree (antipodal n) = (-1)^(n+1)` (which is `≡ 1 mod 2`). -/
theorem degreeOfIso_antipodal_intCast_zmodTwo_eq_one {n : ℕ}
    (e : SphereTopHomologyIso n) :
    ((degreeOfIso e (antipodal n) : ZMod 2)) = 1 :=
  Odd.intCast_zmodTwo (odd_degreeOfIso_antipodal e)

/-- **Mod-2 agreement with the target value, in `ZMod 2`.** The reduction of the
antipodal degree equals the reduction of `(-1)^(n+1)`; both are `1`. -/
theorem degreeOfIso_antipodal_intCast_zmodTwo_eq_neg_one_pow {n : ℕ}
    (e : SphereTopHomologyIso n) :
    ((degreeOfIso e (antipodal n) : ZMod 2))
      = (((-1 : ℤ) ^ (n + 1) : ℤ) : ZMod 2) := by
  rw [degreeOfIso_antipodal_intCast_zmodTwo_eq_one,
    Odd.intCast_zmodTwo (odd_neg_one_pow_succ n)]

/-! ## 3. Oriented-degree wrappers

The same mod-2 comparison statements on the bundled `SphereOrientation.degree`. -/

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The reduction of the integer degree to `ZMod 2` is `1` iff the degree is odd. -/
theorem degree_intCast_zmodTwo_eq_one_iff_odd {n : ℕ} (f : C(Sphere n, Sphere n)) :
    ((o.degree f : ZMod 2) = 1) ↔ Odd (o.degree f) :=
  degreeOfIso_intCast_zmodTwo_eq_one_iff_odd (o.iso n) f

/-- Multiplicativity of the mod-2 degree on the bundled orientation. -/
theorem degree_comp_intCast_zmodTwo {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    ((o.degree (g.comp f) : ZMod 2))
      = (o.degree g : ZMod 2) * (o.degree f : ZMod 2) :=
  degreeOfIso_comp_intCast_zmodTwo (o.iso n) f g

/-- The mod-2 degree of a self-homeomorphism is `1`. -/
theorem degree_homeomorph_intCast_zmodTwo_eq_one {n : ℕ}
    (h : Sphere n ≃ₜ Sphere n) :
    ((o.degree (h : C(Sphere n, Sphere n)) : ZMod 2)) = 1 :=
  degreeOfIso_homeomorph_intCast_zmodTwo_eq_one (o.iso n) h

/-- The mod-2 degree of the antipodal map is `1`. -/
theorem degree_antipodal_intCast_zmodTwo_eq_one {n : ℕ} :
    ((o.degree (antipodal n) : ZMod 2)) = 1 :=
  degreeOfIso_antipodal_intCast_zmodTwo_eq_one (o.iso n)

end SphereOrientation

end SphereOddDegree
