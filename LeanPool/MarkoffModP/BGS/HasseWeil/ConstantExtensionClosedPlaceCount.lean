/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ClosedPlaceEulerRecurrence
import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionFinitePlaceBridge
import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceBridge

/-!
# Closed places and rational places after extension of constants

For an exact extension of constants `S / C`, the existing finite and
infinity normalization bridges both prove the residue-degree formula

`deg_S(Q) = deg_C(P) / gcd([S : C], deg_C(P))`.

This file combines the two branches into one presented-place type and proves
that an upstairs presented place is rational exactly when its downstairs
degree divides `[S : C]`.  Thus it identifies, place by place, the support of
the closed-place extension coefficient with rationality after constant
extension.

The global cardinality identity needs one further splitting theorem: the
fiber over a downstairs place of degree `d` must have cardinality
`gcd([S : C], d)`.  That multiplicity is not supplied by the current
finite/infinity bridge APIs, so no global count equality is asserted here.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

/-- Elementary arithmetic behind rationality after extension of constants. -/
theorem div_gcd_eq_one_iff_dvd (r d : ℕ) (hd : 0 < d) :
    d / Nat.gcd r d = 1 ↔ d ∣ r := by
  constructor
  · intro h
    have heq : d = Nat.gcd r d * 1 :=
      Nat.eq_mul_of_div_eq_right (Nat.gcd_dvd_right r d) h
    have hgcd : Nat.gcd r d = d := by simpa using heq.symm
    exact Nat.gcd_eq_right_iff_dvd.mp hgcd
  · intro h
    rw [Nat.gcd_eq_right_iff_dvd.mpr h]
    exact Nat.div_self hd

/-- The degree after extending constants divides an extension level exactly
when the original closed-place degree divides the multiplied level. -/
theorem div_gcd_dvd_iff_dvd_mul
    (extensionDegree placeDegree level : ℕ)
    (hextension : 0 < extensionDegree) :
    placeDegree / Nat.gcd extensionDegree placeDegree ∣ level ↔
      placeDegree ∣ extensionDegree * level := by
  let g := Nat.gcd extensionDegree placeDegree
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left placeDegree hextension
  have hgPlace : g ∣ placeDegree := Nat.gcd_dvd_right _ _
  have hgExtension : g ∣ extensionDegree := Nat.gcd_dvd_left _ _
  have hplace : g * (placeDegree / g) = placeDegree :=
    Nat.mul_div_cancel' hgPlace
  have hext : g * (extensionDegree / g) = extensionDegree :=
    Nat.mul_div_cancel' hgExtension
  have hcoprime :
      (placeDegree / g).Coprime (extensionDegree / g) :=
    (Nat.coprime_div_gcd_div_gcd hgpos).symm
  constructor
  · intro h
    have hdiv : placeDegree / g ∣ (extensionDegree / g) * level :=
      hcoprime.dvd_mul_left.mpr h
    have hmul : g * (placeDegree / g) ∣
        g * ((extensionDegree / g) * level) :=
      (Nat.mul_dvd_mul_iff_left hgpos).mpr hdiv
    simpa only [hplace, ← Nat.mul_assoc, hext] using hmul
  · intro h
    have hmul : g * (placeDegree / g) ∣
        g * ((extensionDegree / g) * level) := by
      simpa only [hplace, ← Nat.mul_assoc, hext] using h
    have hdiv : placeDegree / g ∣ (extensionDegree / g) * level :=
      (Nat.mul_dvd_mul_iff_left hgpos).mp hmul
    exact hcoprime.dvd_mul_left.mp hdiv

/-- Abstract finite-fiber form of the constant-extension contribution
identity.  If every object above `P` has degree `deg(P) / gcd(r, deg(P))`
and there are exactly `gcd(r, deg(P))` such objects, then the total degrees
in the two finite families agree. -/
theorem sum_degree_eq_sum_degree_of_div_gcd_and_fiber_card
    {Base Up : Type*} [Fintype Base] [Fintype Up]
    (down : Up → Base) (baseDegree : Base → ℕ) (upDegree : Up → ℕ)
    (extensionDegree : ℕ)
    (hdegree : ∀ Q, upDegree Q =
      baseDegree (down Q) /
        Nat.gcd extensionDegree (baseDegree (down Q)))
    (hfiber : ∀ P, Nat.card {Q : Up // down Q = P} =
      Nat.gcd extensionDegree (baseDegree P)) :
    (∑ Q, upDegree Q) = ∑ P, baseDegree P := by
  classical
  let : DecidableEq Base := Classical.decEq Base
  calc
    (∑ Q, upDegree Q) =
        ∑ z : Σ P, {Q : Up // down Q = P}, upDegree z.2.1 := by
      apply Fintype.sum_equiv (Equiv.sigmaFiberEquiv down).symm
      intro Q
      rfl
    _ = ∑ P, ∑ Q : {Q : Up // down Q = P}, upDegree Q.1 :=
      Fintype.sum_sigma _
    _ = ∑ P, Fintype.card {Q : Up // down Q = P} *
        (baseDegree P /
          Nat.gcd extensionDegree (baseDegree P)) := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_const_nat
      intro Q _
      rw [hdegree, Q.2]
    _ = ∑ P, Nat.gcd extensionDegree (baseDegree P) *
        (baseDegree P /
          Nat.gcd extensionDegree (baseDegree P)) := by
      simp_rw [← Nat.card_eq_fintype_card, hfiber]
    _ = ∑ P, baseDegree P := by
      apply Finset.sum_congr rfl
      intro P _
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

/-- Bounded divisor-support form of the preceding fiber identity.  It is the
exact combinatorial interface used by closed-place extension counts: the map
between all places need not have finite domain, because the two degree-bounded
families are supplied as finite types. -/
theorem sum_degree_dvd_eq_sum_degree_dvd_of_div_gcd_fibers
    {Base Up : Type*}
    (down : Up → Base) (baseDegree : Base → ℕ) (upDegree : Up → ℕ)
    (extensionDegree level : ℕ)
    (hextension : 0 < extensionDegree) (hlevel : 0 < level)
    [Fintype {P : Base // baseDegree P ≤ extensionDegree * level}]
    [Fintype {Q : Up // upDegree Q ≤ level}]
    (hdegree : ∀ Q, upDegree Q =
      baseDegree (down Q) /
        Nat.gcd extensionDegree (baseDegree (down Q)))
    (hfiber : ∀ P, Nat.card {Q : Up // down Q = P} =
      Nat.gcd extensionDegree (baseDegree P)) :
    (∑ Q : {Q : {Q : Up // upDegree Q ≤ level} //
        upDegree Q.1 ∣ level}, upDegree Q.1.1) =
      ∑ P : {P : {P : Base //
          baseDegree P ≤ extensionDegree * level} //
        baseDegree P.1 ∣ extensionDegree * level},
        baseDegree P.1.1 := by
  classical
  let BaseLE := {P : Base // baseDegree P ≤ extensionDegree * level}
  let UpLE := {Q : Up // upDegree Q ≤ level}
  let BaseDvd := {P : BaseLE //
    baseDegree P.1 ∣ extensionDegree * level}
  let UpDvd := {Q : UpLE // upDegree Q.1 ∣ level}
  let downDvd : UpDvd → BaseDvd := fun Q => by
    have hdiv : baseDegree (down Q.1.1) ∣ extensionDegree * level :=
      (div_gcd_dvd_iff_dvd_mul extensionDegree
        (baseDegree (down Q.1.1)) level hextension).mp (by
          rw [← hdegree Q.1.1]
          exact Q.2)
    exact ⟨⟨down Q.1.1,
      Nat.le_of_dvd (Nat.mul_pos hextension hlevel) hdiv⟩, hdiv⟩
  have hdownDvd (Q : UpDvd) : (downDvd Q).1.1 = down Q.1.1 := rfl
  have hfiberDvd (P : BaseDvd) :
      Nat.card {Q : UpDvd // downDvd Q = P} =
        Nat.gcd extensionDegree (baseDegree P.1.1) := by
    let e : {Q : UpDvd // downDvd Q = P} ≃
        {Q : Up // down Q = P.1.1} :=
      { toFun := fun Q => ⟨Q.1.1.1, by
          have h := congrArg (fun R : BaseDvd => R.1.1) Q.2
          exact h⟩
        invFun := fun Q => by
          have hbaseDiv : baseDegree (down Q.1) ∣
              extensionDegree * level := by
            simpa only [Q.2] using P.2
          have hupDiv : upDegree Q.1 ∣ level := by
            rw [hdegree]
            exact (div_gcd_dvd_iff_dvd_mul extensionDegree
              (baseDegree (down Q.1)) level hextension).mpr hbaseDiv
          let qDvd : UpDvd := ⟨⟨Q.1,
            Nat.le_of_dvd hlevel hupDiv⟩, hupDiv⟩
          refine ⟨qDvd, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          exact Q.2
        left_inv := fun Q => by
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun Q => by
          apply Subtype.ext
          rfl }
    calc
      Nat.card {Q : UpDvd // downDvd Q = P} =
          Nat.card {Q : Up // down Q = P.1.1} := Nat.card_congr e
      _ = Nat.gcd extensionDegree (baseDegree P.1.1) := hfiber P.1.1
  apply sum_degree_eq_sum_degree_of_div_gcd_and_fiber_card
    downDvd (fun P : BaseDvd => baseDegree P.1.1)
      (fun Q : UpDvd => upDegree Q.1.1) extensionDegree
  · intro Q
    simpa only [hdownDvd] using hdegree Q.1.1
  · exact hfiberDvd

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

-- The infinity bridge fixes classical decidable equality locally.  Reusing
-- the same definitions keeps its dependent place types definitionally equal
-- to the exhaustive place types in this file.
local instance (priority := 10000) closedPlaceRatFuncBaseDecidableEq :
    DecidableEq (RatFunc C) :=
  infinityBridgeDecidableEqRatFuncConstants C

local instance (priority := 10000) closedPlaceRatFuncConstantsDecidableEq :
    DecidableEq (RatFunc S) :=
  infinityBridgeDecidableEqRatFuncConstants S

local instance closedPlaceBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance closedPlaceTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

/-- Reciprocal-affine primes used to present places above infinity.  The
local algebra structure sends the polynomial variable to `X⁻¹`, exactly as
in `ConstantExtensionInfinityPlaceBridge`. -/
abbrev ExactConstantExtensionPresentedInfinityPlace :=
  letI : Algebra C[X] N :=
    infinityBridgeBaseReciprocalPolynomialAlgebra C N
  letI : IsScalarTower C C[X] N :=
    infinityBridgeBaseConstantPolynomialTower C N
  letI : Algebra C (integralClosure C[X] N) :=
    infinityBridgeOldNormalizationConstantAlgebra C N
  letI : IsScalarTower C C[X] (integralClosure C[X] N) :=
    infinityBridgeOldNormalizationConstantPolynomialTower C N
  letI : Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
    infinityBridgeTensorPolynomialAlgebra C S N
  {q : IsDedekindDomain.HeightOneSpectrum
      (S ⊗[C] integralClosure C[X] N) //
    q.asIdeal.under S[X] =
      Ideal.span ({Polynomial.X} : Set S[X])}

/-- A common presentation of finite and infinity places in the explicit
normalizations used by the two constant-extension bridge files. -/
abbrev ExactConstantExtensionPresentedPlace :=
  Sum
    (IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S)))
    (ExactConstantExtensionPresentedInfinityPlace C S N)

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The actual upstairs exhaustive place represented by a finite or
reciprocal-infinity normalization prime. -/
noncomputable def exactConstantExtensionPresentedUpstairsPlace
    (q : ExactConstantExtensionPresentedPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    FiniteExtensionPlace S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  cases q with
  | inl q =>
      exact .inl (exactConstantExtensionUpstairsFinitePlace
        C S N hExact q)
  | inr q =>
      exact .inr (exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q.1 q.2)

/-- The actual downstairs exhaustive place obtained by contraction. -/
noncomputable def exactConstantExtensionPresentedDownstairsPlace
    (q : ExactConstantExtensionPresentedPlace C S N) :
    FiniteExtensionPlace C N := by
  cases q with
  | inl q =>
      exact .inl (exactConstantExtensionDownstairsFinitePlace
        C S N hExact q)
  | inr q =>
      exact .inr (exactConstantExtensionDownstairsInfinityPlace
        C S N q.1 q.2)

/-- The finite and infinity residue-degree formulas combine into one formula
on presented exhaustive places. -/
theorem exactConstantExtensionPresentedPlace_degree_eq_div_gcd
    (q : ExactConstantExtensionPresentedPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedUpstairsPlace C S N hExact q) =
      finiteExtensionPlaceDegree C N
          (exactConstantExtensionPresentedDownstairsPlace C S N hExact q) /
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N
            (exactConstantExtensionPresentedDownstairsPlace
              C S N hExact q)) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  cases q with
  | inl q =>
      exact exactConstantExtensionFinitePlace_degree_eq_div_gcd
        C S N hExact q
  | inr q =>
      exact exactConstantExtensionInfinityPlace_degree_eq_div_gcd
        C S N hExact q.1 q.2

/-- A presented upstairs place is rational over `S` exactly when its
downstairs degree divides the constant-extension degree. -/
theorem exactConstantExtensionPresentedPlace_degree_eq_one_iff_dvd
    (q : ExactConstantExtensionPresentedPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedUpstairsPlace C S N hExact q) = 1 ↔
      finiteExtensionPlaceDegree C N
          (exactConstantExtensionPresentedDownstairsPlace C S N hExact q) ∣
        Module.finrank C S := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  rw [exactConstantExtensionPresentedPlace_degree_eq_div_gcd]
  exact div_gcd_eq_one_iff_dvd
    (Module.finrank C S)
    (finiteExtensionPlaceDegree C N
      (exactConstantExtensionPresentedDownstairsPlace C S N hExact q))
    (finiteExtensionPlaceDegree_pos C N
      (exactConstantExtensionPresentedDownstairsPlace C S N hExact q))

/-- Presented rational places are the same subtype as presented places whose
downstairs degree contributes to the closed-place extension coefficient. -/
def exactConstantExtensionPresentedRationalPlaceEquivDegreeDvd :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    {q : ExactConstantExtensionPresentedPlace C S N //
      finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedUpstairsPlace C S N hExact q) = 1} ≃
    {q : ExactConstantExtensionPresentedPlace C S N //
      finiteExtensionPlaceDegree C N
          (exactConstantExtensionPresentedDownstairsPlace C S N hExact q) ∣
        Module.finrank C S} := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  exact Equiv.subtypeEquivRight fun q =>
    exactConstantExtensionPresentedPlace_degree_eq_one_iff_dvd
      C S N hExact q

/-- Pointwise equality between the closed-place contribution and the
rational-presented-place indicator. -/
theorem exactConstantExtensionPresentedPlace_closedContribution_eq
    (q : ExactConstantExtensionPresentedPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    (if finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
          (exactConstantExtensionPresentedUpstairsPlace C S N hExact q) = 1
      then finiteExtensionPlaceDegree C N
        (exactConstantExtensionPresentedDownstairsPlace C S N hExact q)
      else 0) =
    (if finiteExtensionPlaceDegree C N
          (exactConstantExtensionPresentedDownstairsPlace C S N hExact q) ∣
        Module.finrank C S
      then finiteExtensionPlaceDegree C N
        (exactConstantExtensionPresentedDownstairsPlace C S N hExact q)
      else 0) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  by_cases hrat : finiteExtensionPlaceDegree S
      (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedUpstairsPlace C S N hExact q) = 1
  · have hdiv :=
      (exactConstantExtensionPresentedPlace_degree_eq_one_iff_dvd
        C S N hExact q).mp hrat
    simp [hrat, hdiv]
  · have hndiv : ¬ finiteExtensionPlaceDegree C N
        (exactConstantExtensionPresentedDownstairsPlace C S N hExact q) ∣
          Module.finrank C S := by
      intro hdiv
      exact hrat
        ((exactConstantExtensionPresentedPlace_degree_eq_one_iff_dvd
          C S N hExact q).mpr hdiv)
    simp [hrat, hndiv]

/-- Public unfolding of the closed-place extension coefficient. -/
theorem finiteExtensionClosedPlaceExtensionCount_eq_degreeDvdSum
    (r : ℕ) :
    finiteExtensionClosedPlaceExtensionCount C N r =
      letI := finiteExtensionPlaceDegreeLEFintype C N r
      ∑ P : {P : FiniteExtensionPlace C N //
          finiteExtensionPlaceDegree C N P ≤ r},
        if finiteExtensionPlaceDegree C N P.1 ∣ r then
          finiteExtensionPlaceDegree C N P.1 else 0 := by
  rfl

end

end BGS.HasseWeil
