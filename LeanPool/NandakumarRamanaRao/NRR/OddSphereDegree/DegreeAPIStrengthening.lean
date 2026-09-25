/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomology
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Antipodal

/-!
# Strengthened sphere-degree API

Extends `degreeOfIso` and `SphereOrientation.degree` with categorical-sphere wrappers, constant
maps, homeomorphisms, and antipodal parity results. The declarations are parameterized by a
chosen top-homology isomorphism or orientation; later modules supply the unconditional
positive-dimensional orientation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace SphereOddDegree

/-! ## Degree of a `TopCat.sphere n` self-morphism

The degree relative to `e` reads off the integer scalar by which a self-morphism
of `TopCat.sphere n` acts on top homology. This is the most model-agnostic form
of the conditional degree: it consumes a raw categorical morphism, and the raw
`Sphere n` degree `degreeOfIso` is its image under the model transport. -/

/-- The integer **degree of a `TopCat.sphere n` self-morphism `g`** relative to a
chosen identification `e : Hₙ(Sⁿ; ℤ) ≅ ℤ`. The raw `Sphere n` degree is the
special case `g = toTopCatSphereSelfMap f` (see `degreeOfIso_eq_degreeOfIsoTop`). -/
def degreeOfIsoTop {n : ℕ} (e : SphereTopHomologyIso n)
    (g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ :=
  degreeRingHomOfIso _ e ((singularHomologyℤ n).map g)

/-- The degree of the identity morphism is `1`. -/
@[simp]
theorem degreeOfIsoTop_id {n : ℕ} (e : SphereTopHomologyIso n) :
    degreeOfIsoTop e (𝟙 (TopCat.sphere.{0} n)) = 1 := by
  rw [degreeOfIsoTop, (singularHomologyℤ n).map_id]
  exact map_one _

/-
The degree is multiplicative under categorical composition. Note that the
factors reverse: with `g` applied first and `h` second, the induced top-homology
endomorphism is `map g ≫ map h = map h * map g` in `End`, so the ring hom sends it
to `degree h * degree g`.
-/
theorem degreeOfIsoTop_comp {n : ℕ} (e : SphereTopHomologyIso n)
    (g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degreeOfIsoTop e (g ≫ h) = degreeOfIsoTop e h * degreeOfIsoTop e g := by
  unfold degreeOfIsoTop
  rw [(singularHomologyℤ n).map_comp, ← map_mul]
  rfl

/-- **Compatibility with the raw `Sphere n` degree.** The conditional degree
`degreeOfIso e f` is exactly the `TopCat`-degree of the model transport of `f`. -/
theorem degreeOfIso_eq_degreeOfIsoTop {n : ℕ} (e : SphereTopHomologyIso n)
    (f : C(Sphere n, Sphere n)) :
    degreeOfIso e f = degreeOfIsoTop e (toTopCatSphereSelfMap f) := rfl

/-- **Choice independence** of the `TopCat`-degree: it does not depend on the
chosen identification `e`. -/
theorem degreeOfIsoTop_well_defined {n : ℕ} (e e' : SphereTopHomologyIso n)
    (g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degreeOfIsoTop e g = degreeOfIsoTop e' g := by
  have key :
      (degreeRingEquivOfIso _ e).toRingHom.comp (degreeRingEquivOfIso _ e').symm.toRingHom
        = RingHom.id ℤ := Subsingleton.elim _ _
  have h := RingHom.ext_iff.mp key (degreeRingEquivOfIso _ e' ((singularHomologyℤ n).map g))
  rw [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, degreeRingEquivOfIso_apply,
    degreeRingEquivOfIso_apply] at h
  exact h

/-! ## Degree of one-point maps (`n ≥ 1`)

A single-valued self-map (`ContinuousMap.const`) of `Sphere n` factors through a
one-point space, whose `n`-th
homology vanishes for `n ≥ 1` (it is totally disconnected). Hence the induced
endomorphism of top homology is `0` and the degree is `0`. -/

/-- For `n ≥ 1` the `n`-th integral singular homology of the one-point space
`PUnit` is the zero object (a point is totally disconnected). -/
theorem singularHomologyℤ_punit_isZero {n : ℕ} (hn : n ≠ 0) :
    IsZero ((singularHomologyℤ n).obj (TopCat.of PUnit.{1})) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit.{1}) hn

/-- **The induced top-homology endomorphism of a one-point map is `0`** (`n ≥ 1`).
The single-valued self-map factors through the one-point space `PUnit`, and the
induced map on `Hₙ` therefore factors through `Hₙ(PUnit) = 0`. -/
theorem inducedOnTopHomology_const {n : ℕ} (hn : n ≠ 0) (c : Sphere n) :
    inducedOnTopHomology (ContinuousMap.const (Sphere n) c) = 0 := by
  let term : TopCat.sphere.{0} n ⟶ TopCat.of PUnit.{1} :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let pt : TopCat.of PUnit.{1} ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom ⟨fun _ => ULift.up c, continuous_const⟩
  have hfac : toTopCatSphereSelfMap (ContinuousMap.const (Sphere n) c) = term ≫ pt := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hpt : (singularHomologyℤ n).map pt = 0 :=
    (singularHomologyℤ_punit_isZero hn).eq_zero_of_src _
  rw [inducedOnTopHomology, hfac, (singularHomologyℤ n).map_comp, hpt,
    Limits.comp_zero]

/-- **Degree of a one-point map is `0`** for `n ≥ 1`. -/
theorem degreeOfIso_const {n : ℕ} (e : SphereTopHomologyIso n) (hn : n ≠ 0)
    (c : Sphere n) :
    degreeOfIso e (ContinuousMap.const (Sphere n) c) = 0 := by
  rw [degreeOfIso, inducedOnTopHomology_const hn c, map_zero]

/-! ## Degree of homeomorphisms is a unit

If `h` is a self-homeomorphism then `degree h · degree h⁻¹ = degree id = 1`, so the
degree is a unit of `ℤ`, i.e. `±1` (hence in particular odd). -/

/-- For a self-homeomorphism `h`, `degree h * degree h⁻¹ = 1`. -/
theorem degreeOfIso_homeomorph_mul_symm {n : ℕ} (e : SphereTopHomologyIso n)
    (h : Sphere n ≃ₜ Sphere n) :
    degreeOfIso e (h : C(Sphere n, Sphere n)) * degreeOfIso e (h.symm : C(Sphere n, Sphere n))
      = 1 := by
  rw [← degreeOfIso_comp]
  rw [show ((h : C(Sphere n, Sphere n)).comp (h.symm : C(Sphere n, Sphere n)))
        = ContinuousMap.id (Sphere n) from
      ContinuousMap.ext (fun x => h.apply_symm_apply x)]
  exact degreeOfIso_id e

/-- The degree of a self-homeomorphism is a unit of `ℤ`. -/
theorem isUnit_degreeOfIso_homeomorph {n : ℕ} (e : SphereTopHomologyIso n)
    (h : Sphere n ≃ₜ Sphere n) :
    IsUnit (degreeOfIso e (h : C(Sphere n, Sphere n))) :=
  IsUnit.of_mul_eq_one _ (degreeOfIso_homeomorph_mul_symm e h)

/-- **The degree of a self-homeomorphism is `±1`.** -/
theorem degreeOfIso_homeomorph_eq_one_or_neg_one {n : ℕ} (e : SphereTopHomologyIso n)
    (h : Sphere n ≃ₜ Sphere n) :
    degreeOfIso e (h : C(Sphere n, Sphere n)) = 1
      ∨ degreeOfIso e (h : C(Sphere n, Sphere n)) = -1 :=
  Int.isUnit_iff.mp (isUnit_degreeOfIso_homeomorph e h)

/-- **Parity wrapper.** The degree of a self-homeomorphism is odd. -/
theorem odd_degreeOfIso_homeomorph {n : ℕ} (e : SphereTopHomologyIso n)
    (h : Sphere n ≃ₜ Sphere n) :
    Odd (degreeOfIso e (h : C(Sphere n, Sphere n))) := by
  rcases degreeOfIso_homeomorph_eq_one_or_neg_one e h with hh | hh <;> rw [hh] <;> decide

/-! ## Degree of the antipodal map -/

/-- The square of the degree of the antipodal map is `1` (it is an involution). -/
theorem degreeOfIso_antipodal_sq {n : ℕ} (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) * degreeOfIso e (antipodal n) = 1 := by
  rw [← degreeOfIso_comp, antipodal_comp_antipodal]
  exact degreeOfIso_id e

/-- **The degree of the antipodal map is `±1`.** Which sign occurs is `(-1)^(n+1)`
after choosing the standard orientation identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`
(cf. `det_ambientNeg`). -/
theorem degreeOfIso_antipodal_eq_one_or_neg_one {n : ℕ} (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) = 1 ∨ degreeOfIso e (antipodal n) = -1 :=
  Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ (degreeOfIso_antipodal_sq e))

/-! ## Oriented-degree wrappers

The same facts repackaged on the bundled `SphereOrientation.degree`. -/

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The degree of a one-point map is `0` (`n ≥ 1`). -/
theorem degree_const {n : ℕ} (hn : n ≠ 0) (c : Sphere n) :
    o.degree (ContinuousMap.const (Sphere n) c) = 0 :=
  degreeOfIso_const (o.iso n) hn c

/-- The degree of a self-homeomorphism is `±1`. -/
theorem degree_homeomorph_eq_one_or_neg_one {n : ℕ} (h : Sphere n ≃ₜ Sphere n) :
    o.degree (h : C(Sphere n, Sphere n)) = 1
      ∨ o.degree (h : C(Sphere n, Sphere n)) = -1 :=
  degreeOfIso_homeomorph_eq_one_or_neg_one (o.iso n) h

/-- The degree of a self-homeomorphism is odd. -/
theorem odd_degree_homeomorph {n : ℕ} (h : Sphere n ≃ₜ Sphere n) :
    Odd (o.degree (h : C(Sphere n, Sphere n))) :=
  odd_degreeOfIso_homeomorph (o.iso n) h

/-- The degree of the antipodal map is `±1`. -/
theorem degree_antipodal_eq_one_or_neg_one (n : ℕ) :
    o.degree (antipodal n) = 1 ∨ o.degree (antipodal n) = -1 :=
  degreeOfIso_antipodal_eq_one_or_neg_one (o.iso n)

end SphereOrientation

end SphereOddDegree
