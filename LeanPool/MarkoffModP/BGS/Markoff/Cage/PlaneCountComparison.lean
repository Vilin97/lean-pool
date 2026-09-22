/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Cage.PowerCover

/-!
# Comparing the pulled cage cover with its affine plane models

The plane models retain the power parameter `t`, whereas the pulled cover
requires `t ≠ 0`.  On the diagonal the plane model also forgets the choice
between the two equal radicand roots.  This file isolates those two losses
and bounds them by the roots of explicit univariate polynomials.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

/-- A finite-field polynomial has at most its degree many distinct roots. -/
private lemma natCard_eval_eq_zero_le_natDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : f ≠ 0) :
    Nat.card {x : K // f.eval x = 0} <= f.natDegree := by
  classical
  let rootEmbedding : {x : K // f.eval x = 0} ↪ f.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        exact x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : f.roots.toFinset => (z : K)) h }
  let : Fintype {x : K // f.eval x = 0} := Fintype.ofFinite _
  calc
    Nat.card {x : K // f.eval x = 0} <= f.roots.toFinset.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
    _ <= f.roots.card := Multiset.toFinset_card_le _
    _ <= f.natDegree := Polynomial.card_roots' f

/-- The pulled radicand has degree at most `4d`. -/
lemma cagePulledRadicand_natDegree_le (K : Type*) [Field K]
    (xi : K) (d : Nat) :
    (cagePulledRadicand xi d).natDegree <= 4 * d := by
  rw [cagePulledRadicand_expanded]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- Rational points of the diagonal plane model. -/
abbrev CageDiagonalPlanePoint (p : Nat) [Fact p.Prime]
    (xi : ZMod p) (d : Nat) :=
  ↥(BGS.External.affinePlaneCurveZeros (ZMod p)
    (cageDiagonalPlanePolynomial xi d))

/-- A plane point together with the sign used to recover the second root. -/
abbrev CageDiagonalTaggedPlanePoint (p : Nat) [Fact p.Prime]
    (xi : ZMod p) (d : Nat) := CageDiagonalPlanePoint p xi d × Bool

/-- The tagged points which recover a unique pulled pair.  At a zero root,
the two signs coincide, so only `false` is retained. -/
def IsGoodDiagonalTaggedPoint {p : Nat} [Fact p.Prime]
    {xi : ZMod p} {d : Nat}
    (z : CageDiagonalTaggedPlanePoint p xi d) : Prop :=
  z.1.1.2 ≠ 0 ∧ (z.1.1.1 ≠ 0 ∨ z.2 = false)

/-- Away from the explicit exceptional set, a signed diagonal plane point
is exactly a pulled pair of roots. -/
def goodDiagonalTaggedPointEquivPulled
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi : ZMod p) (d : Nat) :
    {z : CageDiagonalTaggedPlanePoint p xi d //
      IsGoodDiagonalTaggedPoint z} ≃ CagePulledRootPair p xi xi d where
  toFun z := by
    let parameter : (ZMod p)ˣ := Units.mk0 z.1.1.1.2 z.2.1
    let root := z.1.1.1.1
    refine
      { parameter := parameter
        firstRoot := root
        secondRoot := if z.1.2 then -root else root
        firstEquation := ?_
        secondEquation := ?_ }
    · exact (eval_cageDiagonalPlanePolynomial_eq_zero_iff xi d root
          z.1.1.1.2).mp
        (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
    · have hfirst : root ^ 2 =
          (cagePulledRadicand xi d).eval z.1.1.1.2 :=
        (eval_cageDiagonalPlanePolynomial_eq_zero_iff xi d root
          z.1.1.1.2).mp
          (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
      split <;> simpa [parameter, root] using hfirst
  invFun z := by
    have hsquares : z.secondRoot = z.firstRoot ∨
        z.secondRoot = -z.firstRoot := by
      rw [← sq_eq_sq_iff_eq_or_eq_neg]
      exact z.secondEquation.trans z.firstEquation.symm
    let tag : Bool := if z.secondRoot = z.firstRoot then false else true
    have htag : z.secondRoot = if tag then -z.firstRoot else z.firstRoot := by
      dsimp [tag]
      split
      · simp_all
      · simp_all
    refine ⟨(⟨(z.firstRoot, (z.parameter : ZMod p)), ?_⟩, tag), ?_⟩
    · apply BGS.External.mem_affinePlaneCurveZeros_iff.mpr
      exact (eval_cageDiagonalPlanePolynomial_eq_zero_iff xi d
        z.firstRoot (z.parameter : ZMod p)).mpr z.firstEquation
    · refine ⟨z.parameter.ne_zero, ?_⟩
      by_cases hroot : z.firstRoot = 0
      · right
        have hsecond : z.secondRoot = 0 := by
          rcases hsquares with h | h <;> simp_all
        simp [tag, hroot, hsecond]
      · exact Or.inl hroot
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext <;> rfl
    · cases htag : z.1.2
      · simp [htag]
      · have hroot : z.1.1.1.1 ≠ 0 := by
          rcases z.2.2 with hroot | hfalse
          · exact hroot
          · simp [htag] at hfalse
        have hneg : -z.1.1.1.1 ≠ z.1.1.1.1 := by
          intro h
          have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod
            (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
          have hzero : z.1.1.1.1 + z.1.1.1.1 = 0 :=
            neg_eq_iff_add_eq_zero.mp h
          have hzero' : (2 : ZMod p) * z.1.1.1.1 = 0 := by
            simpa [two_mul] using hzero
          exact hroot ((mul_eq_zero.mp hzero').resolve_left htwo)
        simp [htag, hneg]
  right_inv z := by
    apply CagePulledRootPair.ext
    · apply Units.ext
      rfl
    · rfl
    · dsimp
      split
      · symm
        assumption
      · rename_i hne
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp
          (z.secondEquation.trans z.firstEquation.symm)) with h | h
        · exact (hne h).elim
        · exact h.symm

/-- The bad signed diagonal points inject into either the two signs above
`t = 0`, or a root of the pulled radicand with the duplicated sign. -/
def badDiagonalTaggedPointEmbedding
    (p : Nat) [Fact p.Prime] (xi : ZMod p) {d : Nat} (hd : 0 < d) :
    {z : CageDiagonalTaggedPlanePoint p xi d //
      ¬ IsGoodDiagonalTaggedPoint z} ↪
      ({root : ZMod p // root ^ 2 = xi ^ 2 - 4} × Bool) ⊕
        {parameter : ZMod p // (cagePulledRadicand xi d).eval parameter = 0} :=
  { toFun := fun z => by
      by_cases hparameter : z.1.1.1.2 = 0
      · exact Sum.inl ⟨⟨z.1.1.1.1, by
            have heq := (eval_cageDiagonalPlanePolynomial_eq_zero_iff xi d
              z.1.1.1.1 z.1.1.1.2).mp
                (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
            simpa [hparameter, cagePulledRadicand_eval_zero xi hd] using heq⟩,
          z.1.2⟩
      · exact Sum.inr ⟨z.1.1.1.2, by
          have hbad := z.2
          have hroot : z.1.1.1.1 = 0 := by
            by_contra hroot
            exact hbad ⟨hparameter, Or.inl hroot⟩
          have heq := (eval_cageDiagonalPlanePolynomial_eq_zero_iff xi d
            z.1.1.1.1 z.1.1.1.2).mp
              (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
          simpa [hroot] using heq.symm⟩
    inj' := by
      intro x y hxy
      by_cases hx : x.1.1.1.2 = 0
      · by_cases hy : y.1.1.1.2 = 0
        · simp only [hx, hy, ite_eq_left] at hxy
          have hpayload := Sum.inl.inj hxy
          apply Subtype.ext
          apply Prod.ext
          · apply Subtype.ext
            apply Prod.ext
            · exact congrArg (fun q => q.1.1) hpayload
            · exact hx.trans hy.symm
          · exact congrArg
              (fun q : ({root : ZMod p // root ^ 2 = xi ^ 2 - 4} × Bool) => q.2)
              hpayload
        · simp [hx, hy] at hxy
      · by_cases hy : y.1.1.1.2 = 0
        · simp [hx, hy] at hxy
        · simp only [hx, hy, ite_eq_right] at hxy
          have hpayload := Sum.inr.inj hxy
          have hparameter : x.1.1.1.2 = y.1.1.1.2 :=
            congrArg Subtype.val hpayload
          have hxroot : x.1.1.1.1 = 0 := by
            by_contra hroot
            exact x.2 ⟨hx, Or.inl hroot⟩
          have hyroot : y.1.1.1.1 = 0 := by
            by_contra hroot
            exact y.2 ⟨hy, Or.inl hroot⟩
          have hxtag : x.1.2 = true := by
            cases htag : x.1.2
            · exact (x.2 ⟨hx, Or.inr htag⟩).elim
            · rfl
          have hytag : y.1.2 = true := by
            cases htag : y.1.2
            · exact (y.2 ⟨hy, Or.inr htag⟩).elim
            · rfl
          apply Subtype.ext
          apply Prod.ext
          · apply Subtype.ext
            exact Prod.ext (hxroot.trans hyroot.symm) hparameter
          · exact hxtag.trans hytag.symm }

/-- In a field of odd characteristic, a scalar has at most two square roots. -/
private lemma natCard_sq_eq_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    Nat.card {x : K // x ^ 2 = a} <= 2 := by
  let f : K[X] := X ^ 2 - C a
  have hf : f ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hzero
    simp [f] at hcoeff
  let e : {x : K // x ^ 2 = a} ≃ {x : K // f.eval x = 0} :=
    Equiv.subtypeEquiv (Equiv.refl K) (by
      intro x
      simp [f, sub_eq_zero])
  calc
    Nat.card {x : K // x ^ 2 = a} = Nat.card {x : K // f.eval x = 0} :=
      Nat.card_congr e
    _ <= f.natDegree := natCard_eval_eq_zero_le_natDegree f hf
    _ = 2 := by simp [f]

/-- The diagonal exceptional set has size at most `4d + 4`: four signed
points can lie above `t = 0`, and every remaining exception is a zero of the
degree-`4d` pulled radicand. -/
lemma natCard_badDiagonalTaggedPoint_le
    (p : Nat) [Fact p.Prime] (xi : ZMod p) {d : Nat} (hd : 0 < d)
    (hXi : xi ^ 2 - 4 ≠ 0) :
    Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
      ¬ IsGoodDiagonalTaggedPoint z} <= 4 * d + 4 := by
  have hradicand : cagePulledRadicand xi d ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun q : (ZMod p)[X] => q.coeff (4 * d)) hzero
    rw [cagePulledRadicand_coeff_four_mul xi hd, coeff_zero] at hcoeff
    exact hXi hcoeff
  have hrootBound :
      Nat.card {root : ZMod p // root ^ 2 = xi ^ 2 - 4} <= 2 :=
    natCard_sq_eq_le_two _
  have hradicandBound :
      Nat.card {parameter : ZMod p //
        (cagePulledRadicand xi d).eval parameter = 0} <= 4 * d :=
    (natCard_eval_eq_zero_le_natDegree _ hradicand).trans
      (cagePulledRadicand_natDegree_le (ZMod p) xi d)
  have hinjective := Nat.card_le_card_of_injective
    (badDiagonalTaggedPointEmbedding p xi hd).toFun
    (badDiagonalTaggedPointEmbedding p xi hd).injective
  rw [Nat.card_sum, Nat.card_prod] at hinjective
  have hbool : Nat.card Bool = 2 := by simp
  rw [hbool] at hinjective
  omega

/-- Exact bookkeeping identity behind the diagonal comparison. -/
lemma two_mul_diagonalPlanePoint_card_eq_pulled_add_bad
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi : ZMod p) (d : Nat) :
    2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
        (cageDiagonalPlanePolynomial xi d)).card =
      Nat.card (CagePulledRootPair p xi xi d) +
        Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
          ¬ IsGoodDiagonalTaggedPoint z} := by
  classical
  have hgood :
      Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
        IsGoodDiagonalTaggedPoint z} =
        Nat.card (CagePulledRootPair p xi xi d) :=
    Nat.card_congr (goodDiagonalTaggedPointEquivPulled p hpTwo xi d)
  have hplane : Nat.card (CageDiagonalPlanePoint p xi d) =
      (BGS.External.affinePlaneCurveZeros (ZMod p)
        (cageDiagonalPlanePolynomial xi d)).card := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_coe
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (cageDiagonalPlanePolynomial xi d))
  have hbool : Nat.card Bool = 2 := by simp
  calc
    2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
        (cageDiagonalPlanePolynomial xi d)).card =
        Nat.card (CageDiagonalTaggedPlanePoint p xi d) := by
          rw [Nat.card_prod, hplane, hbool]
          omega
    _ = Nat.card
          ({z : CageDiagonalTaggedPlanePoint p xi d //
              IsGoodDiagonalTaggedPoint z} ⊕
            {z : CageDiagonalTaggedPlanePoint p xi d //
              ¬ IsGoodDiagonalTaggedPoint z}) :=
        (Nat.card_congr
          (Equiv.sumCompl (fun z : CageDiagonalTaggedPlanePoint p xi d =>
            IsGoodDiagonalTaggedPoint z))).symm
    _ = Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
            IsGoodDiagonalTaggedPoint z} +
          Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
            ¬ IsGoodDiagonalTaggedPoint z} := Nat.card_sum
    _ = Nat.card (CagePulledRootPair p xi xi d) +
          Nat.card {z : CageDiagonalTaggedPlanePoint p xi d //
            ¬ IsGoodDiagonalTaggedPoint z} := by rw [hgood]

/-- The pulled diagonal cover differs from twice its plane-model count by
at most the explicit exceptional contribution `4d + 4`. -/
theorem cagePulledRootPair_diagonal_card_comparison
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi : ZMod p) {d : Nat} (hd : 0 < d)
    (hXi : xi ^ 2 - 4 ≠ 0) :
    |(Nat.card (CagePulledRootPair p xi xi d) : Int) -
        2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
          (cageDiagonalPlanePolynomial xi d)).card| <= 4 * d + 4 := by
  have hexact := two_mul_diagonalPlanePoint_card_eq_pulled_add_bad
    p hpTwo xi d
  have hbad := natCard_badDiagonalTaggedPoint_le p xi hd hXi
  let bad := {z : CageDiagonalTaggedPlanePoint p xi d //
    ¬ IsGoodDiagonalTaggedPoint z}
  have hid :
      (Nat.card (CagePulledRootPair p xi xi d) : Int) -
          2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageDiagonalPlanePolynomial xi d)).card =
        -(Nat.card bad : Int) := by
    change 2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
      (cageDiagonalPlanePolynomial xi d)).card =
        Nat.card (CagePulledRootPair p xi xi d) + Nat.card bad at hexact
    exact_mod_cast (by omega :
      (Nat.card (CagePulledRootPair p xi xi d) : Int) -
          2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageDiagonalPlanePolynomial xi d)).card =
        -(Nat.card bad : Int))
  rw [hid, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast hbad

abbrev CageOffDiagonalPlanePoint (p : Nat) [Fact p.Prime]
    (xi eta : ZMod p) (d : Nat) :=
  ↥(BGS.External.affinePlaneCurveZeros (ZMod p)
    (cageOffDiagonalPlanePolynomial xi eta d))

def IsGoodOffDiagonalPlanePoint {p : Nat} [Fact p.Prime]
    {xi eta : ZMod p} {d : Nat} (z : CageOffDiagonalPlanePoint p xi eta d) : Prop :=
  z.1.1 ≠ 0 ∧ z.1.2 ≠ 0

def IsGoodOffDiagonalPulledPair {p : Nat} [Fact p.Prime]
    {xi eta : ZMod p} {d : Nat} (z : CagePulledRootPair p xi eta d) : Prop :=
  z.firstRoot + z.secondRoot ≠ 0

def goodOffDiagonalPulledToPlane
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : Nat) :
    {z : CagePulledRootPair p xi eta d // IsGoodOffDiagonalPulledPair z} →
      {z : CageOffDiagonalPlanePoint p xi eta d //
        IsGoodOffDiagonalPlanePoint z} := fun z => by
  let sumRoot := z.1.firstRoot + z.1.secondRoot
  refine ⟨⟨(sumRoot, (z.1.parameter : ZMod p)), ?_⟩,
    z.2, z.1.parameter.ne_zero⟩
  apply BGS.External.mem_affinePlaneCurveZeros_iff.mpr
  apply (eval_cageOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
    (two_ne_zero_zmod
      (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hpTwo)))
    xi eta d z.2).mpr
  exact ⟨z.1.firstRoot, z.1.secondRoot, z.1.firstEquation,
    z.1.secondEquation, rfl⟩

lemma goodOffDiagonalPulledToPlane_bijective
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : Nat) :
    Function.Bijective (goodOffDiagonalPulledToPlane p hpTwo xi eta d) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod
    (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
  constructor
  · intro x y hxy
    have hsum : x.1.firstRoot + x.1.secondRoot =
        y.1.firstRoot + y.1.secondRoot := by
      exact congrArg (fun z => z.1.1.1) hxy
    have hparameter : x.1.parameter = y.1.parameter := by
      apply Units.ext
      exact congrArg (fun z => z.1.1.2) hxy
    have hfirstSq : x.1.firstRoot ^ 2 = y.1.firstRoot ^ 2 := by
      rw [x.1.firstEquation, y.1.firstEquation, hparameter]
    have hsecondSq : x.1.secondRoot ^ 2 = y.1.secondRoot ^ 2 := by
      rw [x.1.secondEquation, y.1.secondEquation, hparameter]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hfirstSq with hfirst | hfirst
    · apply Subtype.ext
      apply CagePulledRootPair.ext hparameter hfirst
      linear_combination hsum - hfirst
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsecondSq with hsecond | hsecond
      · have hfirstZero : x.1.firstRoot = 0 := by
          have : (2 : ZMod p) * x.1.firstRoot = 0 := by
            rw [two_mul]
            linear_combination hsum - hsecond + hfirst
          exact (mul_eq_zero.mp this).resolve_left h2
        apply Subtype.ext
        apply CagePulledRootPair.ext hparameter
        · have hyfirstZero : y.1.firstRoot = 0 := by
            linear_combination hfirst - hfirstZero
          simp [hfirstZero, hyfirstZero]
        · exact hsecond
      · have hsumZero : x.1.firstRoot + x.1.secondRoot = 0 := by
          have : (2 : ZMod p) * (x.1.firstRoot + x.1.secondRoot) = 0 := by
            rw [two_mul]
            linear_combination hsum + hfirst + hsecond
          exact (mul_eq_zero.mp this).resolve_left h2
        exact (x.2 hsumZero).elim
  · intro z
    have hexists :=
      (eval_cageOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
        h2 xi eta d z.2.1).mp
        (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2)
    rcases hexists with ⟨firstRoot, secondRoot, hfirst, hsecond, hsum⟩
    let parameter : (ZMod p)ˣ := Units.mk0 z.1.1.2 z.2.2
    let pulled : CagePulledRootPair p xi eta d :=
      { parameter := parameter
        firstRoot := firstRoot
        secondRoot := secondRoot
        firstEquation := by simpa [parameter] using hfirst
        secondEquation := by simpa [parameter] using hsecond }
    have hpulledGood : IsGoodOffDiagonalPulledPair pulled := by
      change firstRoot + secondRoot ≠ 0
      rw [hsum]
      exact z.2.1
    refine ⟨⟨pulled, hpulledGood⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hsum
    · rfl

def goodOffDiagonalPulledEquivPlane
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : Nat) :
    {z : CagePulledRootPair p xi eta d // IsGoodOffDiagonalPulledPair z} ≃
      {z : CageOffDiagonalPlanePoint p xi eta d //
        IsGoodOffDiagonalPlanePoint z} :=
  Equiv.ofBijective _ (goodOffDiagonalPulledToPlane_bijective p hpTwo xi eta d)

private lemma rootCount_le_natDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : f ≠ 0) :
    Nat.card {x : K // f.eval x = 0} ≤ f.natDegree := by
  classical
  let embedding : {x : K // f.eval x = 0} ↪ f.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        exact x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : f.roots.toFinset => (z : K)) h }
  let : Fintype {x : K // f.eval x = 0} := Fintype.ofFinite _
  calc
    Nat.card {x : K // f.eval x = 0} ≤ f.roots.toFinset.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Fintype.card_le_of_injective embedding embedding.injective
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f

private lemma sqRootCount_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    Nat.card {x : K // x ^ 2 = a} ≤ 2 := by
  let f : K[X] := X ^ 2 - C a
  have hf : f ≠ 0 := by
    intro h
    have := congrArg (fun q : K[X] => q.coeff 2) h
    simp [f] at this
  let e : {x : K // x ^ 2 = a} ≃ {x : K // f.eval x = 0} :=
    Equiv.subtypeEquiv (Equiv.refl K) (by intro x; simp [f, sub_eq_zero])
  rw [Nat.card_congr e]
  exact (rootCount_le_natDegree f hf).trans_eq (by simp [f])

private lemma powerRootCount_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n : Nat} (hn : 0 < n) : Nat.card {x : K // x ^ n = 1} ≤ n := by
  let f : K[X] := X ^ n - 1
  have hf : f ≠ 0 := by
    simpa [f] using (monic_X_pow_sub_C (1 : K) hn.ne').ne_zero
  let e : {x : K // x ^ n = 1} ≃ {x : K // f.eval x = 0} :=
    Equiv.subtypeEquiv (Equiv.refl K) (by intro x; simp [f, sub_eq_zero])
  rw [Nat.card_congr e]
  exact (rootCount_le_natDegree f hf).trans_eq (by
    simpa [f] using (natDegree_X_pow_sub_C (R := K) (n := n) (r := 1)))

def badOffDiagonalPulledEmbedding
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) {d : Nat} (hd : 0 < d)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    {z : CagePulledRootPair p xi eta d //
      ¬ IsGoodOffDiagonalPulledPair z} ↪
    (Σ parameter : {t : ZMod p // t ^ (2 * d) = 1},
      {root : ZMod p // root ^ 2 =
        (cagePulledRadicand xi d).eval parameter.1}) :=
  { toFun := fun z => by
      have hsum : z.1.firstRoot + z.1.secondRoot = 0 :=
        not_ne_iff.mp z.2
      have hsecond : z.1.secondRoot = -z.1.firstRoot := by
        linear_combination hsum
      have hevals : (cagePulledRadicand xi d).eval
            (z.1.parameter : ZMod p) =
          (cagePulledRadicand eta d).eval
            (z.1.parameter : ZMod p) := by
        rw [← z.1.firstEquation, ← z.1.secondEquation, hsecond]
        ring
      have hdifference := congrArg
        (fun q : (ZMod p)[X] => q.eval (z.1.parameter : ZMod p))
        (cagePulledRadicand_sub xi eta d)
      have hproduct : (xi ^ 2 - eta ^ 2) *
          ((z.1.parameter : ZMod p) ^ (2 * d) - 1) ^ 2 = 0 := by
        simpa [hevals] using hdifference
      have hscalar : xi ^ 2 - eta ^ 2 ≠ 0 := sub_ne_zero.mpr hoffDiagonal
      have hpower : (z.1.parameter : ZMod p) ^ (2 * d) = 1 := by
        have hsquare := (mul_eq_zero.mp hproduct).resolve_left hscalar
        have hbase : (z.1.parameter : ZMod p) ^ (2 * d) - 1 = 0 := by
          apply mul_self_eq_zero.mp
          simpa [pow_two] using hsquare
        exact sub_eq_zero.mp hbase
      exact ⟨⟨(z.1.parameter : ZMod p), hpower⟩,
        ⟨z.1.firstRoot, z.1.firstEquation⟩⟩
    inj' := by
      intro x y hxy
      have hparameter : x.1.parameter = y.1.parameter := by
        apply Units.ext
        exact congrArg (fun z => (z.1.1 : ZMod p)) hxy
      have hfirst : x.1.firstRoot = y.1.firstRoot :=
        congrArg (fun z => z.2.1) hxy
      have hxsum : x.1.firstRoot + x.1.secondRoot = 0 := not_ne_iff.mp x.2
      have hysum : y.1.firstRoot + y.1.secondRoot = 0 := not_ne_iff.mp y.2
      apply Subtype.ext
      apply CagePulledRootPair.ext hparameter hfirst
      linear_combination hxsum - hysum - hfirst }

lemma badOffDiagonalPulled_card_le
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) {d : Nat} (hd : 0 < d)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    Nat.card {z : CagePulledRootPair p xi eta d //
      ¬ IsGoodOffDiagonalPulledPair z} ≤ 4 * d := by
  let base := {t : ZMod p // t ^ (2 * d) = 1}
  let fiber : base → Type := fun t =>
    {root : ZMod p // root ^ 2 = (cagePulledRadicand xi d).eval t.1}
  have hinj := Nat.card_le_card_of_injective
    (badOffDiagonalPulledEmbedding p hpTwo xi eta hd hoffDiagonal).toFun
    (badOffDiagonalPulledEmbedding p hpTwo xi eta hd hoffDiagonal).injective
  change Nat.card _ ≤ Nat.card (Σ t : base, fiber t) at hinj
  rw [Nat.card_sigma] at hinj
  have hfiber : ∀ t : base, Nat.card (fiber t) ≤ 2 :=
    fun t => sqRootCount_le_two _
  have hsum : ∑ t : base, Nat.card (fiber t) ≤ ∑ _t : base, 2 := by
    exact Finset.sum_le_sum fun t _ => hfiber t
  have hbase : Nat.card base ≤ 2 * d := powerRootCount_le (by omega)
  have hsum' : ∑ t : base, Nat.card (fiber t) ≤ Nat.card base * 2 := by
    simpa using hsum
  omega

def cageOffDiagonalZeroParameterPolynomial
    {K : Type*} [Field K] (xi eta : K) (d : Nat) : K[X] :=
  (X ^ 2 - C ((cagePulledRadicand xi d).eval 0 +
      (cagePulledRadicand eta d).eval 0)) ^ 2 -
    C (4 * (cagePulledRadicand xi d).eval 0 *
      (cagePulledRadicand eta d).eval 0)

lemma eval_cageOffDiagonalZeroParameterPolynomial
    {K : Type*} [Field K] (xi eta sumRoot : K) (d : Nat) :
    (cageOffDiagonalZeroParameterPolynomial xi eta d).eval sumRoot =
      MvPolynomial.eval ![sumRoot, 0]
        (cageOffDiagonalPlanePolynomial xi eta d) := by
  rw [eval_cageOffDiagonalPlanePolynomial]
  simp [cageOffDiagonalZeroParameterPolynomial]

lemma cageOffDiagonalZeroParameterPolynomial_natDegree_le
    {K : Type*} [Field K] (xi eta : K) (d : Nat) :
    (cageOffDiagonalZeroParameterPolynomial xi eta d).natDegree ≤ 4 := by
  unfold cageOffDiagonalZeroParameterPolynomial
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_pow_le).trans (by
      have hinside : (X ^ 2 - C ((cagePulledRadicand xi d).eval 0 +
          (cagePulledRadicand eta d).eval 0) : K[X]).natDegree ≤ 2 :=
        (natDegree_sub_le _ _).trans (max_le
          (natDegree_X_pow_le 2) ((natDegree_C _).le.trans (by omega)))
      omega)
  · exact (natDegree_C _).le.trans (by omega)

lemma cageOffDiagonalZeroParameterPolynomial_ne_zero
    {K : Type*} [Field K] (xi eta : K) (d : Nat) :
    cageOffDiagonalZeroParameterPolynomial xi eta d ≠ 0 := by
  have hquadratic : IsMonicOfDegree
      (X ^ 2 - C ((cagePulledRadicand xi d).eval 0 +
        (cagePulledRadicand eta d).eval 0) : K[X]) 2 :=
    (isMonicOfDegree_X_pow K 2).sub (by simp)
  have hmonic : (cageOffDiagonalZeroParameterPolynomial xi eta d).Monic := by
    unfold cageOffDiagonalZeroParameterPolynomial
    exact ((hquadratic.pow 2).sub (by
      have hpos : 0 < 2 * 2 := by norm_num
      simpa only [natDegree_C] using hpos)).monic
  exact hmonic.ne_zero

def badOffDiagonalPlaneEmbedding
    (p : Nat) [Fact p.Prime] (xi eta : ZMod p) {d : Nat}
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    {z : CageOffDiagonalPlanePoint p xi eta d //
      ¬ IsGoodOffDiagonalPlanePoint z} ↪
    {sumRoot : ZMod p //
      (cageOffDiagonalZeroParameterPolynomial xi eta d).eval sumRoot = 0} ⊕
    {parameter : ZMod p // parameter ^ (2 * d) = 1} :=
  { toFun := fun z => by
      by_cases hparameter : z.1.1.2 = 0
      · exact Sum.inl ⟨z.1.1.1, by
          rw [eval_cageOffDiagonalZeroParameterPolynomial]
          simpa [hparameter] using
            (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2)⟩
      · have hsumRoot : z.1.1.1 = 0 := by
          by_contra hsum
          exact z.2 ⟨hsum, hparameter⟩
        have hplane := BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2
        have hquartic :
            ((cagePulledRadicand xi d).eval z.1.1.2 -
              (cagePulledRadicand eta d).eval z.1.1.2) ^ 2 = 0 := by
          rw [eval_cageOffDiagonalPlanePolynomial] at hplane
          rw [hsumRoot] at hplane
          linear_combination hplane
        have hevals : (cagePulledRadicand xi d).eval z.1.1.2 =
            (cagePulledRadicand eta d).eval z.1.1.2 := by
          exact sub_eq_zero.mp (mul_self_eq_zero.mp (by
            simpa [pow_two] using hquartic))
        have hdifference := congrArg
          (fun q : (ZMod p)[X] => q.eval z.1.1.2)
          (cagePulledRadicand_sub xi eta d)
        have hproduct : (xi ^ 2 - eta ^ 2) *
            (z.1.1.2 ^ (2 * d) - 1) ^ 2 = 0 := by
          simpa [hevals] using hdifference
        have hsquare := (mul_eq_zero.mp hproduct).resolve_left
          (sub_ne_zero.mpr hoffDiagonal)
        have hbase : z.1.1.2 ^ (2 * d) - 1 = 0 := by
          apply mul_self_eq_zero.mp
          simpa [pow_two] using hsquare
        exact Sum.inr ⟨z.1.1.2, sub_eq_zero.mp hbase⟩
    inj' := by
      intro x y hxy
      by_cases hx : x.1.1.2 = 0
      · by_cases hy : y.1.1.2 = 0
        · simp only [hx, hy, ite_eq_left] at hxy
          have hpayload := Sum.inl.inj hxy
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (congrArg Subtype.val hpayload) (hx.trans hy.symm)
        · simp [hx, hy] at hxy
      · by_cases hy : y.1.1.2 = 0
        · simp [hx, hy] at hxy
        · simp only [hx, hy, ite_eq_right] at hxy
          have hpayload := Sum.inr.inj hxy
          have hparameter : x.1.1.2 = y.1.1.2 := congrArg Subtype.val hpayload
          have hxsum : x.1.1.1 = 0 := by
            by_contra hsum
            exact x.2 ⟨hsum, hx⟩
          have hysum : y.1.1.1 = 0 := by
            by_contra hsum
            exact y.2 ⟨hsum, hy⟩
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (hxsum.trans hysum.symm) hparameter }

lemma badOffDiagonalPlane_card_le
    (p : Nat) [Fact p.Prime] (xi eta : ZMod p) {d : Nat} (hd : 0 < d)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    Nat.card {z : CageOffDiagonalPlanePoint p xi eta d //
      ¬ IsGoodOffDiagonalPlanePoint z} ≤ 2 * d + 4 := by
  have hinj := Nat.card_le_card_of_injective
    (badOffDiagonalPlaneEmbedding p xi eta (d := d) hoffDiagonal).toFun
    (badOffDiagonalPlaneEmbedding p xi eta (d := d) hoffDiagonal).injective
  rw [Nat.card_sum] at hinj
  have hzeroParameter : Nat.card {sumRoot : ZMod p //
      (cageOffDiagonalZeroParameterPolynomial xi eta d).eval sumRoot = 0} ≤ 4 :=
    (rootCount_le_natDegree _
      (cageOffDiagonalZeroParameterPolynomial_ne_zero xi eta d)).trans
      (cageOffDiagonalZeroParameterPolynomial_natDegree_le xi eta d)
  have hpower : Nat.card {parameter : ZMod p //
      parameter ^ (2 * d) = 1} ≤ 2 * d := powerRootCount_le (by omega)
  omega

theorem cagePulledRootPair_offDiagonal_card_comparison
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) {d : Nat} (hd : 0 < d)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    |(Nat.card (CagePulledRootPair p xi eta d) : Int) -
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (cageOffDiagonalPlanePolynomial xi eta d)).card| ≤ 6 * d + 4 := by
  classical
  let : Finite (CagePulledRootPair p xi eta d) :=
    Finite.of_injective
      (fun z => (z.parameter, z.firstRoot, z.secondRoot)) (by
        intro x y h
        apply CagePulledRootPair.ext
        · exact congrArg Prod.fst h
        · exact congrArg (fun q => q.2.1) h
        · exact congrArg (fun q => q.2.2) h)
  let goodPulled := {z : CagePulledRootPair p xi eta d //
    IsGoodOffDiagonalPulledPair z}
  let badPulled := {z : CagePulledRootPair p xi eta d //
    ¬ IsGoodOffDiagonalPulledPair z}
  let goodPlane := {z : CageOffDiagonalPlanePoint p xi eta d //
    IsGoodOffDiagonalPlanePoint z}
  let badPlane := {z : CageOffDiagonalPlanePoint p xi eta d //
    ¬ IsGoodOffDiagonalPlanePoint z}
  have hsplitPulled : Nat.card (CagePulledRootPair p xi eta d) =
      Nat.card goodPulled + Nat.card badPulled := by
    calc
      Nat.card (CagePulledRootPair p xi eta d) =
          Nat.card (goodPulled ⊕ badPulled) :=
        (Nat.card_congr (Equiv.sumCompl
          (fun z : CagePulledRootPair p xi eta d =>
            IsGoodOffDiagonalPulledPair z))).symm
      _ = Nat.card goodPulled + Nat.card badPulled := Nat.card_sum
  have hplaneCard : Nat.card (CageOffDiagonalPlanePoint p xi eta d) =
      (BGS.External.affinePlaneCurveZeros (ZMod p)
        (cageOffDiagonalPlanePolynomial xi eta d)).card := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_coe
      (BGS.External.affinePlaneCurveZeros (ZMod p)
        (cageOffDiagonalPlanePolynomial xi eta d))
  have hsplitPlane :
      (BGS.External.affinePlaneCurveZeros (ZMod p)
          (cageOffDiagonalPlanePolynomial xi eta d)).card =
        Nat.card goodPlane + Nat.card badPlane := by
    calc
      _ = Nat.card (CageOffDiagonalPlanePoint p xi eta d) := hplaneCard.symm
      _ = Nat.card (goodPlane ⊕ badPlane) :=
        (Nat.card_congr (Equiv.sumCompl
          (fun z : CageOffDiagonalPlanePoint p xi eta d =>
            IsGoodOffDiagonalPlanePoint z))).symm
      _ = Nat.card goodPlane + Nat.card badPlane := Nat.card_sum
  have hgood : Nat.card goodPulled = Nat.card goodPlane :=
    Nat.card_congr (goodOffDiagonalPulledEquivPlane p hpTwo xi eta d)
  have hbadPulled : Nat.card badPulled ≤ 4 * d := by
    exact badOffDiagonalPulled_card_le p hpTwo xi eta hd hoffDiagonal
  have hbadPlane : Nat.card badPlane ≤ 2 * d + 4 := by
    exact badOffDiagonalPlane_card_le p xi eta hd hoffDiagonal
  have herror :
      |(Nat.card (CagePulledRootPair p xi eta d) : Int) -
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageOffDiagonalPlanePolynomial xi eta d)).card| ≤
        Nat.card badPulled + Nat.card badPlane := by
    rw [hsplitPulled, hsplitPlane, hgood]
    push_cast
    have habs := abs_sub (Nat.card badPulled : Int)
      (Nat.card badPlane : Int)
    simpa using habs
  exact herror.trans (by exact_mod_cast (by omega :
    Nat.card badPulled + Nat.card badPlane ≤ 6 * d + 4))

end

end BGS.Markoff
