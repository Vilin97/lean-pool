/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFrobeniusDeflation

/-!
# The zero-coordinate-degree case of Frobenius reduction

An absolutely irreducible plane polynomial with zero degree in one
coordinate is a univariate polynomial in the other coordinate.  After
extension to an algebraic closure, irreducibility forces that univariate
polynomial to have degree one.  Consequently it has one rational root over
the original field and its affine plane zero set has exactly one point above
each value of the absent coordinate.
-/

namespace BGS.HasseWeil

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R]

theorem natDegree_uniqueAlgEquiv_fin_one
    (q : MvPolynomial (Fin 1) R) :
    (MvPolynomial.uniqueAlgEquiv R (Fin 1) q).natDegree =
      degreeOf 0 q := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    by_contra hcoeff
    have hm : Finsupp.single (0 : Fin 1) n ∈ q.support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hle := monomial_le_degreeOf (0 : Fin 1) hm
    have : n < n := by simpa using hle.trans_lt hn
    exact this.false
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    apply Polynomial.le_natDegree_of_ne_zero
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    change q.coeff (Finsupp.single (0 : Fin 1) (m 0)) ≠ 0
    have hmEq : Finsupp.single (0 : Fin 1) (m 0) = m := by
      simpa using (Finsupp.unique_single m).symm
    rw [hmEq]
    exact MvPolynomial.mem_support_iff.mp hm

def secondPolynomialOfFirstDegreeZero
    (f : MvPolynomial (Fin 2) R) : Polynomial R :=
  MvPolynomial.uniqueAlgEquiv R (Fin 1)
    ((MvPolynomial.finSuccEquiv R 1 f).coeff 0)

theorem finSuccEquiv_eq_C_coeff_zero_of_degreeOf_zero
    {f : MvPolynomial (Fin 2) R} (hdegree : degreeOf 0 f = 0) :
    MvPolynomial.finSuccEquiv R 1 f =
      Polynomial.C ((MvPolynomial.finSuccEquiv R 1 f).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  simpa [MvPolynomial.natDegree_finSuccEquiv] using hdegree

theorem degreeOf_one_eq_natDegree_secondPolynomialOfFirstDegreeZero
    {f : MvPolynomial (Fin 2) R} (hdegree : degreeOf 0 f = 0) :
    degreeOf 1 f = (secondPolynomialOfFirstDegreeZero f).natDegree := by
  let q := (MvPolynomial.finSuccEquiv R 1 f).coeff 0
  have hC := finSuccEquiv_eq_C_coeff_zero_of_degreeOf_zero hdegree
  have hqle : degreeOf 0 q ≤ degreeOf 1 f := by
    exact MvPolynomial.degreeOf_coeff_finSuccEquiv f 0 0
  have hfle : degreeOf 1 f ≤ degreeOf 0 q := by
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    have htail : m.tail ∈
        ((MvPolynomial.finSuccEquiv R 1 f).coeff (m 0)).support := by
      rw [MvPolynomial.mem_support_coeff_finSuccEquiv]
      simpa using hm
    have hmzero : m 0 = 0 := by
      by_contra hmzero
      have hz : (MvPolynomial.finSuccEquiv R 1 f).coeff (m 0) = 0 := by
        rw [hC]
        rw [Polynomial.coeff_C, if_neg hmzero]
      rw [hz] at htail
      simpa using htail
    have htailq : m.tail ∈ q.support := by
      rw [hmzero] at htail
      exact htail
    have hle := monomial_le_degreeOf (0 : Fin 1) htailq
    change m 1 ≤ degreeOf 0 q
    simpa [Finsupp.tail_apply] using hle
  rw [secondPolynomialOfFirstDegreeZero,
    natDegree_uniqueAlgEquiv_fin_one]
  exact le_antisymm hfle hqle

theorem degreeOf_map_eq_of_injective_local
    {S : Type*} [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (i : Fin 2)
    (f : MvPolynomial (Fin 2) R) :
    degreeOf i (map φ f) = degreeOf i f := by
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
    MvPolynomial.support_map_of_injective f hφ]

theorem degreeOf_one_eq_one_of_absolutelyIrreducible_degreeOf_zero
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f))
    (hdegree : degreeOf 0 f = 0) :
    degreeOf 1 f = 1 := by
  let F := AlgebraicClosure K
  let φ : K →+* F := algebraMap K F
  let fF : MvPolynomial (Fin 2) F := map φ f
  have hdegreeMap (i : Fin 2) : degreeOf i fF = degreeOf i f :=
    degreeOf_map_eq_of_injective_local φ (RingHom.injective φ) i f
  have hdegreeZeroF : degreeOf 0 fF = 0 := by
    rw [hdegreeMap]
    exact hdegree
  let qF : MvPolynomial (Fin 1) F :=
    (MvPolynomial.finSuccEquiv F 1 fF).coeff 0
  have hC : MvPolynomial.finSuccEquiv F 1 fF = Polynomial.C qF := by
    simpa [qF] using
      (finSuccEquiv_eq_C_coeff_zero_of_degreeOf_zero hdegreeZeroF)
  have hfinIrr : Irreducible (MvPolynomial.finSuccEquiv F 1 fF) :=
    habsolute.map (MvPolynomial.finSuccEquiv F 1).toMulEquiv
  have hCIrr : Irreducible (Polynomial.C qF) := by
    rw [← hC]
    exact hfinIrr
  letI : IsLocalHom
      (Polynomial.C : MvPolynomial (Fin 1) F →+*
        Polynomial (MvPolynomial (Fin 1) F)) :=
    ⟨fun _ hunit => Polynomial.isUnit_C.mp hunit⟩
  have hqIrr : Irreducible qF := hCIrr.of_map
  have hpolyIrr : Irreducible
      (MvPolynomial.uniqueAlgEquiv F (Fin 1) qF) :=
    hqIrr.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toMulEquiv
  have hpolyDegree :
      (MvPolynomial.uniqueAlgEquiv F (Fin 1) qF).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible F hpolyIrr)
  have hdegreeOneF : degreeOf 1 fF = 1 := by
    rw [degreeOf_one_eq_natDegree_secondPolynomialOfFirstDegreeZero
      hdegreeZeroF]
    simpa [secondPolynomialOfFirstDegreeZero, qF] using hpolyDegree
  rw [hdegreeMap] at hdegreeOneF
  exact hdegreeOneF

theorem eval_eq_secondPolynomialOfFirstDegreeZero
    {f : MvPolynomial (Fin 2) R} (hdegree : degreeOf 0 f = 0)
    (x y : R) :
    eval ![x, y] f = (secondPolynomialOfFirstDegreeZero f).eval y := by
  let q := (MvPolynomial.finSuccEquiv R 1 f).coeff 0
  have hC := finSuccEquiv_eq_C_coeff_zero_of_degreeOf_zero hdegree
  calc
    eval ![x, y] f =
        Polynomial.eval x
          (Polynomial.map (eval ![y])
            (MvPolynomial.finSuccEquiv R 1 f)) := by
      simpa using
        (MvPolynomial.eval_eq_eval_mv_eval' (R := R) ![y] x f)
    _ = eval ![y] q := by
      rw [hC]
      simp [q]
    _ = (secondPolynomialOfFirstDegreeZero f).eval y := by
      symm
      simpa [secondPolynomialOfFirstDegreeZero, q] using
        (MvPolynomial.eval₂_uniqueAlgEquiv
          (R := R) (σ := Fin 1)
          (f := q) (φ := RingHom.id R) (a := ![y]))

theorem card_affinePlaneCurveZeros_eq_card_of_degreeOf_zero
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f))
    (hdegree : degreeOf 0 f = 0) :
    (BGS.External.affinePlaneCurveZeros K f).card = Fintype.card K := by
  let q := secondPolynomialOfFirstDegreeZero f
  have hdegreeOne :=
    degreeOf_one_eq_one_of_absolutelyIrreducible_degreeOf_zero
      habsolute hdegree
  have hqnat : q.natDegree = 1 := by
    rw [← degreeOf_one_eq_natDegree_secondPolynomialOfFirstDegreeZero
      hdegree]
    exact hdegreeOne
  have hqdegree : q.degree = 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos Nat.zero_lt_one).2 hqnat
  let r : K := -((q.coeff 1)⁻¹ * q.coeff 0)
  have hqne : q ≠ 0 := by
    intro hq
    rw [hq, Polynomial.degree_zero] at hqdegree
    exact WithBot.bot_ne_coe hqdegree
  have hzero (y : K) : q.eval y = 0 ↔ y = r := by
    change q.IsRoot y ↔ y = r
    rw [← Polynomial.mem_roots hqne,
      Polynomial.roots_degree_eq_one hqdegree]
    simp [r]
  let e : {z // z ∈ BGS.External.affinePlaneCurveZeros K f} ≃ K :=
    { toFun := fun z => z.1.1
      invFun := fun x => ⟨(x, r), by
        rw [BGS.External.mem_affinePlaneCurveZeros_iff,
          eval_eq_secondPolynomialOfFirstDegreeZero hdegree]
        exact (hzero r).2 rfl⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hz := BGS.External.mem_affinePlaneCurveZeros_iff.mp z.2
          rw [eval_eq_secondPolynomialOfFirstDegreeZero hdegree] at hz
          exact ((hzero z.1.2).1 hz).symm
      right_inv := by intro x; rfl }
  calc
    (BGS.External.affinePlaneCurveZeros K f).card =
        Fintype.card {z // z ∈ BGS.External.affinePlaneCurveZeros K f} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card K := Fintype.card_congr e

end

end BGS.HasseWeil
