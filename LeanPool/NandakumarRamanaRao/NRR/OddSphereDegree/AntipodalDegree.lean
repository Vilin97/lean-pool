/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.DegreeFunctorialityAndHomotopy

/-!
# Degree of the antipodal map

Proves parity and mod-two statements for the antipodal degree and identifies the bundled
antipodal map with ambient negation. The exact integer formula
`degree(antipodal on Sⁿ) = (-1)^(n+1)` is exposed conditionally through
`DegreeEqAmbientDet`, the standard bridge from an orthogonal linear map to the sign of its
determinant.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-- The ambient antipodal linear map `x ↦ -x` on `ℝ^(n+1)`, abbreviated. Its
determinant is `(-1)^(n+1)` (`det_ambientNeg`). -/
abbrev ambientNeg (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  -LinearMap.id

/-! ## Parity of the target value `(-1)^(n+1)` -/

/-- `(-1)^(n+1)` is odd (it is `±1`). -/
theorem odd_neg_one_pow_succ (n : ℕ) : Odd ((-1 : ℤ) ^ (n + 1)) :=
  (Int.odd_iff.mpr (by decide)).pow

/-- `(-1)^(n+1) ≡ 1 (mod 2)`. -/
theorem neg_one_pow_succ_emod_two (n : ℕ) : ((-1 : ℤ) ^ (n + 1)) % 2 = 1 :=
  Int.odd_iff.mp (odd_neg_one_pow_succ n)

/-- `(-1)^(n+1)` is `1` or `-1`. -/
theorem neg_one_pow_succ_eq_one_or_neg_one (n : ℕ) :
    ((-1 : ℤ) ^ (n + 1)) = 1 ∨ ((-1 : ℤ) ^ (n + 1)) = -1 := by
  rcases Nat.even_or_odd (n + 1) with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

/-! ## Compatibility of `antipodal` with the ambient negation -/

/-- **Compatibility with ambient negation.** The bundled antipodal self-map
`antipodal n` is the restriction to the unit sphere of the ambient linear map
`-LinearMap.id`: on underlying vectors, `↑(antipodal n x) = (-LinearMap.id) ↑x`.
This is the precise sense in which the orientation sign `det_ambientNeg = (-1)^(n+1)`
governs the antipodal map. -/
theorem antipodal_coe_eq_ambientNeg {n : ℕ} (x : Sphere n) :
    ((antipodal n x : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))
      = ambientNeg n (x : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp [ambientNeg]

/-! ## Parity of the antipodal degree (unconditional given `e`) -/

/-- **The degree of the antipodal map is odd** (relative to any chosen
identification `e : Hₙ(Sⁿ;ℤ) ≅ ℤ`). This is the parity consequence of
`degree (antipodal n) = (-1)^(n+1)`, and it holds unconditionally on the sign:
the antipodal map is a self-homeomorphism, so its degree is `±1`, hence odd. -/
theorem odd_degreeOfIso_antipodal {n : ℕ} (e : SphereTopHomologyIso n) :
    Odd (degreeOfIso e (antipodal n)) := by
  rcases degreeOfIso_antipodal_eq_one_or_neg_one e with h | h <;> rw [h] <;> decide

/-- **The degree of the antipodal map is `≡ 1 (mod 2)`** (relative to any chosen
`e`). This is the parity statement `degree(antipodal) ≡ 1 mod 2` expressed as an integer remainder
statement. -/
theorem degreeOfIso_antipodal_emod_two {n : ℕ} (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) % 2 = 1 :=
  Int.odd_iff.mp (odd_degreeOfIso_antipodal e)

/-- **Mod-2 agreement with the target value.** The degree of the antipodal map
agrees with `(-1)^(n+1)` modulo `2`: both are odd. This is the parity content of
the full degree theorem, available now without the orientation sign. -/
theorem degreeOfIso_antipodal_emod_two_eq_neg_one_pow {n : ℕ}
    (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) % 2 = ((-1 : ℤ) ^ (n + 1)) % 2 := by
  rw [degreeOfIso_antipodal_emod_two, neg_one_pow_succ_emod_two]

/-! ## Conditional full theorem: degree = determinant sign ⇒ `(-1)^(n+1)`

The value is derived from the topological bridge "degree of a linear sphere map = sign of its
ambient determinant", expressed here as an explicit hypothesis. -/

/-- The hypothesis that the antipodal degree equals the determinant of its ambient linear map
`-LinearMap.id`. This specializes the linear-sphere-map degree formula to the antipodal map. -/
def DegreeEqAmbientDet {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  (degreeOfIso e (antipodal n) : ℝ) = LinearMap.det (ambientNeg n)

/-- **Conditional antipodal-degree theorem.** *If* the degree of the antipodal
map equals the determinant of its ambient linear map (`DegreeEqAmbientDet`), *then*
`degree (antipodal n) = (-1)^(n+1)`. The proof simply rewrites with the genuine
ambient determinant fact `det_ambientNeg`. -/
theorem degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det {n : ℕ}
    (e : SphereTopHomologyIso n) (h : DegreeEqAmbientDet e) :
    degreeOfIso e (antipodal n) = (-1) ^ (n + 1) := by
  rw [DegreeEqAmbientDet, det_ambientNeg] at h
  exact_mod_cast h

/-! ## Oriented-degree wrappers -/

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The degree of the antipodal map is odd. -/
theorem odd_degree_antipodal (n : ℕ) : Odd (o.degree (antipodal n)) :=
  odd_degreeOfIso_antipodal (o.iso n)

/-- The degree of the antipodal map is `≡ 1 (mod 2)`. -/
theorem degree_antipodal_emod_two (n : ℕ) : o.degree (antipodal n) % 2 = 1 :=
  degreeOfIso_antipodal_emod_two (o.iso n)

/-- **Conditional full theorem, oriented form.** If the antipodal degree equals
its ambient determinant, it equals `(-1)^(n+1)`. -/
theorem degree_antipodal_eq_neg_one_pow_of_eq_det (n : ℕ)
    (h : DegreeEqAmbientDet (o.iso n)) :
    o.degree (antipodal n) = (-1) ^ (n + 1) :=
  degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det (o.iso n) h

end SphereOrientation

end SphereOddDegree
