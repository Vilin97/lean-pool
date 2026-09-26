/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Tactic

/-!
# Affine point counts over canonical finite-field extensions

For a finite field `K` of characteristic `p`, Mathlib provides a chosen
degree-`n` extension `FiniteField.Extension K p n`.  This file base-changes a
bivariate polynomial to that field and counts its affine zeros.  It also
records the cardinality of the extension, compatibility with degree one, and
the geometric hypotheses preserved by this base change.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

/-- Affine zeros of a bivariate polynomial, represented by ordered pairs. -/
abbrev AffineBivariatePoint
    {F : Type*} [CommRing F] (f : MvPolynomial (Fin 2) F) :=
  {z : F × F // MvPolynomial.eval ![z.1, z.2] f = 0}

/-- The number of affine zeros of a bivariate polynomial over a finite
coefficient ring. -/
def affineBivariatePointCount
    {F : Type*} [CommRing F] [Finite F]
    (f : MvPolynomial (Fin 2) F) : ℕ :=
  Nat.card (AffineBivariatePoint f)

/-- Transport affine zeros along a coefficient-ring equivalence. -/
def affineBivariatePointMapEquiv
    {E F : Type*} [CommRing E] [CommRing F]
    (e : E ≃+* F) (f : MvPolynomial (Fin 2) E) :
    AffineBivariatePoint f ≃
      AffineBivariatePoint (MvPolynomial.map e.toRingHom f) :=
  Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) (fun z => by
    have heval :
        MvPolynomial.eval ![e z.1, e z.2]
            (MvPolynomial.map e.toRingHom f) =
          e (MvPolynomial.eval ![z.1, z.2] f) := by
      have hcoordinates :
          ![e z.1, e z.2] = e ∘ ![z.1, z.2] := by
        funext i
        fin_cases i <;> rfl
      rw [hcoordinates]
      exact (MvPolynomial.map_eval e.toRingHom ![z.1, z.2] f).symm
    change MvPolynomial.eval ![z.1, z.2] f = 0 ↔
      MvPolynomial.eval ![e z.1, e z.2]
        (MvPolynomial.map e.toRingHom f) = 0
    rw [heval, e.map_eq_zero_iff])

section Extension

variable (K : Type*) [Field K] [Finite K]
variable (p n : ℕ) [Fact p.Prime] [CharP K p] [NeZero n]

/-- The plane polynomial after extension of constants from `K` to the chosen
degree-`n` finite-field extension. -/
def extensionPlaneCurvePolynomial
    (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) (FiniteField.Extension K p n) :=
  MvPolynomial.map (algebraMap K (FiniteField.Extension K p n)) f

/-- The number of affine zeros after extension of constants to degree `n`. -/
def extensionAffinePointCount
    (f : MvPolynomial (Fin 2) K) : ℕ :=
  affineBivariatePointCount (extensionPlaneCurvePolynomial K p n f)

/-- The chosen degree-`n` extension has exactly `(#K)^n` elements. -/
theorem extensionField_natCard :
    Nat.card (FiniteField.Extension K p n) = Nat.card K ^ n :=
  FiniteField.natCard_extension K p n

section DegreeOne

omit [NeZero n] in
/-- The chosen degree-one extension is noncanonically equivalent to its base
field as a `K`-algebra. -/
def extensionOneAlgEquiv :
    FiniteField.Extension K p 1 ≃ₐ[K] K :=
  (FiniteField.algEquivExtension K p 1 K (by simp)).symm

omit [NeZero n] in
/-- Affine zeros over the chosen degree-one extension correspond exactly to
affine zeros over the base field. -/
def extensionOneAffinePointEquiv
    (f : MvPolynomial (Fin 2) K) :
    AffineBivariatePoint (extensionPlaneCurvePolynomial K p 1 f) ≃
      AffineBivariatePoint f := by
  let e := extensionOneAlgEquiv K p
  have hpoly :
      MvPolynomial.map e.toRingHom
          (extensionPlaneCurvePolynomial K p 1 f) = f := by
    rw [extensionPlaneCurvePolynomial, MvPolynomial.map_map]
    have hcomp :
        e.toRingHom.comp
            (algebraMap K (FiniteField.Extension K p 1)) =
          RingHom.id K := by
      ext c
      simp [e, extensionOneAlgEquiv]
    rw [hcomp, MvPolynomial.map_id]
  simpa only [hpoly] using
    affineBivariatePointMapEquiv e.toRingEquiv
      (extensionPlaneCurvePolynomial K p 1 f)

omit [NeZero n] in
/-- The degree-one extension point count is the original base-field point
count. -/
@[simp]
theorem extensionAffinePointCount_one
    (f : MvPolynomial (Fin 2) K) :
    extensionAffinePointCount K p 1 f =
      affineBivariatePointCount f := by
  exact Nat.card_congr (extensionOneAffinePointEquiv K p f)

end DegreeOne

/-- Absolute irreducibility is preserved after passing to the chosen finite
extension. -/
theorem extensionPlaneCurvePolynomial_absolutelyIrreducible
    (f : MvPolynomial (Fin 2) K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (FiniteField.Extension K p n)
          (AlgebraicClosure (FiniteField.Extension K p n)))
        (extensionPlaneCurvePolynomial K p n f)) := by
  have h := irreducible_map_of_irreducible_map_algebraicClosure
    ((algebraMap (FiniteField.Extension K p n)
        (AlgebraicClosure (FiniteField.Extension K p n))).comp
      (algebraMap K (FiniteField.Extension K p n))) f habsolute
  simpa only [extensionPlaneCurvePolynomial, MvPolynomial.map_map] using h

/-- Partial differentiation commutes with extension of constants. -/
@[simp]
theorem extensionPlaneCurvePolynomial_pderiv
    (f : MvPolynomial (Fin 2) K) (i : Fin 2) :
    MvPolynomial.pderiv i (extensionPlaneCurvePolynomial K p n f) =
      extensionPlaneCurvePolynomial K p n (MvPolynomial.pderiv i f) := by
  rw [extensionPlaneCurvePolynomial, extensionPlaneCurvePolynomial,
    MvPolynomial.pderiv_map]

/-- A nonzero partial derivative remains nonzero after extension of
constants. -/
theorem extensionPlaneCurvePolynomial_pderiv_ne_zero
    (f : MvPolynomial (Fin 2) K) (i : Fin 2)
    (hpartial : MvPolynomial.pderiv i f ≠ 0) :
    MvPolynomial.pderiv i (extensionPlaneCurvePolynomial K p n f) ≠ 0 := by
  rw [extensionPlaneCurvePolynomial_pderiv]
  intro hz
  apply hpartial
  apply MvPolynomial.map_injective
    (algebraMap K (FiniteField.Extension K p n))
    (algebraMap K (FiniteField.Extension K p n)).injective
  rw [map_zero]
  simpa only [extensionPlaneCurvePolynomial] using hz

/-- The function field of the base-changed absolutely irreducible plane
curve has the chosen extension as its exact constant field. -/
theorem extensionPlaneCurveFunctionField_algebraicClosure_eq_bot
    (f : MvPolynomial (Fin 2) K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let fE := MvPolynomial.map
      (algebraMap K (FiniteField.Extension K p n)) f
    let hfE := irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K (FiniteField.Extension K p n)) f habsolute
    letI := planeCurveCoordinateRing_isDomain hfE
    algebraicClosure (FiniteField.Extension K p n)
      (PlaneCurveFunctionField fE) = ⊥ :=
  planeCurveBaseChangeFunctionField_algebraicClosure_eq_bot
    (E := FiniteField.Extension K p n) f habsolute hpartialSecond

end Extension

end

end BGS.HasseWeil
