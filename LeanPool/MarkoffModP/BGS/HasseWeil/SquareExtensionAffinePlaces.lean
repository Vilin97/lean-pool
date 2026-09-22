/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.AffinePointPlace
import LeanPool.MarkoffModP.BGS.HasseWeil.ExtensionPointCount
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-!
# Quadratic-extension affine points and base-field places

An affine point over the quadratic constant-field extension does not in
general determine a distinct place of the base function field: its Frobenius
conjugate has the same affine centre.  This file therefore passes through the
maximal ideal of the base coordinate ring and keeps the residue-degree
weight.  Fibres over a closed affine centre have cardinality at most the
degree of its residue field (and hence at most two).

The selected normalization place above each closed centre may have larger
residue field at a singular point.  This only strengthens the weighted
count.  The final estimate bounds all quadratic-extension affine points by
the positive divisor degree, and by the height for a nonzero function.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped BigOperators nonZeroDivisors Polynomial

noncomputable section

private theorem exists_dominatingPlace_of_nonzero_nonunit
    {A P E : Type*} [CommRing A] [IsDomain A] [CommRing P] [Field E]
    [Algebra A E] [IsFractionRing A E] [Algebra P E]
    [IsDedekindDomain (integralClosure P E)] [IsFractionRing (integralClosure P E) E]
    (m : MaximalSpectrum A)
    (hbase : ∀ x : P, algebraMap P E x ∈ (algebraMap A E).range)
    (b : integralClosure P E) (hb : b ≠ 0)
    (hunit : (b : E) ∈ (dominatingValuationSubring (L := E) m).nonunits) :
    ∃ q : HeightOneSpectrum (integralClosure P E),
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q =
        dominatingValuationSubring (L := E) m := by
  let V := dominatingValuationSubring (L := E) m
  have hV : V ≠ ⊤ := by
    intro htop
    have hnontrivial : V.valuation.IsNontrivial :=
      (Valuation.isNontrivial_iff_exists_lt_one V.valuation).2
        ⟨(b : E), Subtype.coe_ne_coe.mpr hb, hunit⟩
    exact ((ValuationSubring.eq_top_iff V).mp htop) hnontrivial
  have hbMem : b ∈ dominatingIntegralClosurePrime m hbase := by
    change integralClosureToDominatingValuationSubring m hbase b ∈
      IsLocalRing.maximalIdeal V
    exact ValuationSubring.coe_mem_nonunits_iff.mp hunit
  have hne : dominatingIntegralClosurePrime m hbase ≠ ⊥ := by
    intro hbot
    apply hb
    simpa only [hbot, Ideal.mem_bot] using hbMem
  exact ⟨dominatingIntegralClosurePlace m hbase hne,
    valuationSubringAt_dominatingIntegralClosurePlace_eq m hbase hne hV⟩

private theorem exists_dominatingPlace_of_base_element
    {A P E : Type*} [CommRing A] [IsDomain A] [CommRing P] [Field E]
    [Algebra A E] [IsFractionRing A E] [Algebra P E]
    [IsDedekindDomain (integralClosure P E)] [IsFractionRing (integralClosure P E) E]
    (m : MaximalSpectrum A)
    (hbase : ∀ x : P, algebraMap P E x ∈ (algebraMap A E).range)
    (hinj : Function.Injective (algebraMap P E))
    (p : P) (hp : p ≠ 0) (r : A) (hr : r ∈ m.asIdeal)
    (hmap : algebraMap P E p = algebraMap A E r) :
    ∃ q : HeightOneSpectrum (integralClosure P E),
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q =
        dominatingValuationSubring (L := E) m := by
  let b := algebraMap P (integralClosure P E) p
  have hb : b ≠ 0 := by
    intro h
    apply hp
    apply hinj
    have h' := congrArg (algebraMap (integralClosure P E) E) h
    simpa only [b, map_zero, ← IsScalarTower.algebraMap_apply] using h'
  apply exists_dominatingPlace_of_nonzero_nonunit m hbase b hb
  change algebraMap P E p ∈ (dominatingValuationSubring (L := E) m).nonunits
  rw [hmap]
  exact algebraMap_mem_dominatingValuationSubring_nonunits_of_mem m r hr

private theorem residue_finrank_le_of_dominating_valuation
    {K A E : Type*} [Field K] [CommRing A] [IsDomain A] [Field E]
    [Algebra K A] [Algebra K E] [Algebra A E] [IsScalarTower K A E]
    [IsFractionRing A E] (m : MaximalSpectrum A) (R : ValuationSubring E)
    [Algebra K R]
    [Module.Finite K (IsLocalRing.ResidueField R)]
    (hscalar : ∀ c : K, (algebraMap K R c : E) = algebraMap K E c)
    (hspec : R = dominatingValuationSubring (L := E) m) :
    Module.finrank K m.asIdeal.ResidueField ≤
      Module.finrank K (IsLocalRing.ResidueField R) := by
  let V := dominatingValuationSubring (A := A) (L := E) m
  let eVR : V ≃+* R :=
    { toFun := fun x => ⟨x.1, by rw [hspec]; exact x.2⟩
      invFun := fun x => ⟨x.1, by
        change x.1 ∈ dominatingValuationSubring m
        rw [← hspec]
        exact x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let ψ : A →+* R :=
    eVR.toRingHom.comp
      (coordinateRingToDominatingValuationSubring
        (A := A) (L := E) m)
  have hcenter : m.asIdeal =
      Ideal.comap ψ (IsLocalRing.maximalIdeal R) := by
    rw [pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
      (A := A) (L := E)]
    ext a
    change coordinateRingToDominatingValuationSubring m a ∈
        IsLocalRing.maximalIdeal V ↔
      eVR (coordinateRingToDominatingValuationSubring m a) ∈
        IsLocalRing.maximalIdeal R
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (not_congr (MulEquiv.isUnit_map (f := eVR.toMulEquiv))).symm
  have hψcoe (a : A) : ((ψ a : R) : E) = algebraMap A E a := by
    rfl
  let θ : A →ₐ[K] IsLocalRing.ResidueField R :=
    { toRingHom := (IsLocalRing.residue R).comp ψ
      commutes' := by
        intro c
        rw [IsScalarTower.algebraMap_apply K R
          (IsLocalRing.ResidueField R)]
        apply congrArg (IsLocalRing.residue R)
        apply Subtype.ext
        rw [hψcoe]
        change algebraMap A E (algebraMap K A c) = (algebraMap K R c : E)
        rw [← IsScalarTower.algebraMap_apply K A E]
        exact (hscalar c).symm }
  have hker : m.asIdeal = RingHom.ker θ := by
    ext a
    rw [RingHom.mem_ker]
    change a ∈ m.asIdeal ↔ IsLocalRing.residue R (ψ a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, hcenter]
    rfl
  let ι : m.asIdeal.ResidueField →ₐ[K]
      IsLocalRing.ResidueField R := by
    apply Ideal.ResidueField.liftₐ m.asIdeal θ hker.le
    intro a ha
    change IsUnit (θ a)
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply ha
    rw [hker]
    exact hzero
  exact LinearMap.finrank_le_finrank_of_injective (f := ι.toLinearMap) ι.injective

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Mathlib's chosen quadratic extension of the finite field `K`. -/
abbrev SquareExtension := FiniteField.Extension K p 2

/-- Affine zeros of the base-changed plane equation over the quadratic
extension. -/
abbrev SquareExtensionAffinePoint (f : MvPolynomial (Fin 2) K) :=
  AffineBivariatePoint (extensionPlaneCurvePolynomial K p 2 f)

/-- Evaluation of the base coordinate ring at a quadratic-extension affine
point. -/
def squareExtensionPointEval
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) :
    PlaneCurveCoordinateRing f →ₐ[K] SquareExtension K p where
  toRingHom := Ideal.Quotient.lift (Ideal.span {f})
    (MvPolynomial.eval₂Hom
      (algebraMap K (SquareExtension K p)) ![z.1.1, z.1.2]) (by
        intro g hg
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hg
        rw [map_mul]
        have hfzero : MvPolynomial.eval₂
            (algebraMap K (SquareExtension K p)) ![z.1.1, z.1.2] f = 0 := by
          rw [MvPolynomial.eval₂_eq_eval_map]
          exact z.2
        change MvPolynomial.eval₂
            (algebraMap K (SquareExtension K p)) ![z.1.1, z.1.2] f *
          MvPolynomial.eval₂
            (algebraMap K (SquareExtension K p)) ![z.1.1, z.1.2] a = 0
        rw [hfzero, zero_mul])
  commutes' c := by
    change MvPolynomial.eval₂
      (algebraMap K (SquareExtension K p)) ![z.1.1, z.1.2]
        (MvPolynomial.C c) = algebraMap K (SquareExtension K p) c
    simp

omit [DecidableEq K] in
@[simp]
theorem squareExtensionPointEval_coordinate
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) (i : Fin 2) :
    squareExtensionPointEval K p f z (planeCurveCoordinate f i) =
      ![z.1.1, z.1.2] i := by
  simp [squareExtensionPointEval, planeCurveCoordinate,
    planeCurveQuotientMap]

/-- The base closed affine centre of a quadratic-extension point.  The
kernel is maximal because the finite image of the evaluation homomorphism is
a field. -/
def squareExtensionPointMaximalIdeal
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) :
    MaximalSpectrum (PlaneCurveCoordinateRing f) := by
  let φ := squareExtensionPointEval K p f z
  let R := φ.range
  let : Finite R := inferInstance
  let : IsDomain R := inferInstance
  let : Field R := IsField.toField (Finite.isField_of_domain R)
  refine ⟨RingHom.ker φ, ?_⟩
  rw [← AlgHom.ker_rangeRestrict φ]
  exact RingHom.ker_isMaximal_of_surjective φ.rangeRestrict.toRingHom
    φ.rangeRestrict_surjective

omit [DecidableEq K] in
@[simp]
theorem squareExtensionPointMaximalIdeal_asIdeal
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) :
    (squareExtensionPointMaximalIdeal K p f z).asIdeal =
      RingHom.ker (squareExtensionPointEval K p f z) := by
  simp [squareExtensionPointMaximalIdeal]

/-- Closed affine centres arising from quadratic-extension points. -/
abbrev SquareExtensionClosedPoint (f : MvPolynomial (Fin 2) K) :=
  Set.range (squareExtensionPointMaximalIdeal K p f)

noncomputable instance squareExtensionAffinePointFintype
    (f : MvPolynomial (Fin 2) K) :
    Fintype (SquareExtensionAffinePoint K p f) :=
  Fintype.ofFinite _

/-- Send a quadratic-extension point to its base closed affine centre. -/
def squareExtensionClosedPointMap
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) :
    SquareExtensionClosedPoint K p f :=
  ⟨squareExtensionPointMaximalIdeal K p f z, ⟨z, rfl⟩⟩

omit [DecidableEq K] in
theorem squareExtensionClosedPointMap_surjective
    (f : MvPolynomial (Fin 2) K) :
    Function.Surjective (squareExtensionClosedPointMap K p f) := by
  rintro ⟨m, z, rfl⟩
  exact ⟨z, rfl⟩

noncomputable instance squareExtensionClosedPointFintype
    (f : MvPolynomial (Fin 2) K) :
    Fintype (SquareExtensionClosedPoint K p f) := by
  exact Fintype.ofFinite _

/-- The fibre of quadratic-extension points above one base closed affine
centre. -/
abbrev SquareExtensionClosedPointFiber
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :=
  {z : SquareExtensionAffinePoint K p f //
    squareExtensionClosedPointMap K p f z = m}

noncomputable instance squareExtensionClosedPointFiberFintype
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :
    Fintype (SquareExtensionClosedPointFiber K p f m) :=
  Fintype.ofFinite _

/-- A point in a fixed closed-centre fibre gives a `K`-embedding of that
centre's residue field into the quadratic extension. -/
def squareExtensionFiberResidueAlgHom
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f)
    (z : SquareExtensionClosedPointFiber K p f m) :
    m.1.asIdeal.ResidueField →ₐ[K] SquareExtension K p := by
  let φ := squareExtensionPointEval K p f z.1
  have hm : squareExtensionPointMaximalIdeal K p f z.1 = m.1 :=
    congrArg Subtype.val z.2
  have hker : m.1.asIdeal = RingHom.ker φ := by
    rw [← hm]
    exact squareExtensionPointMaximalIdeal_asIdeal K p f z.1
  apply Ideal.ResidueField.liftₐ m.1.asIdeal φ hker.le
  intro a ha
  change IsUnit (φ a)
  rw [isUnit_iff_ne_zero]
  intro hzero
  apply ha
  rw [hker]
  exact hzero

omit [DecidableEq K] in
theorem squareExtensionFiberResidueAlgHom_injective
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :
    Function.Injective
      (squareExtensionFiberResidueAlgHom K p f m) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have h := DFunLike.congr_fun hzw
      (algebraMap (PlaneCurveCoordinateRing f) m.1.asIdeal.ResidueField
        (planeCurveCoordinate f 0))
    simpa [squareExtensionFiberResidueAlgHom] using h
  · have h := DFunLike.congr_fun hzw
      (algebraMap (PlaneCurveCoordinateRing f) m.1.asIdeal.ResidueField
        (planeCurveCoordinate f 1))
    simpa [squareExtensionFiberResidueAlgHom] using h

omit [DecidableEq K] in
/-- A closed-centre fibre has cardinality at most the degree of its residue
field over `K`. -/
theorem squareExtensionClosedPointFiber_card_le_residueDegree
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :
    Fintype.card (SquareExtensionClosedPointFiber K p f m) ≤
      Module.finrank K m.1.asIdeal.ResidueField := by
  obtain ⟨z, hz⟩ := m.2
  let zf : SquareExtensionClosedPointFiber K p f m :=
    ⟨z, Subtype.ext hz⟩
  let ι := squareExtensionFiberResidueAlgHom K p f m zf
  let : Finite m.1.asIdeal.ResidueField :=
    Finite.of_injective ι ι.injective
  let : Fintype m.1.asIdeal.ResidueField := Fintype.ofFinite _
  let : Module.Finite K m.1.asIdeal.ResidueField :=
    Module.Finite.of_fg_top (by
      rw [Submodule.fg_def]
      exact ⟨Set.univ, Set.finite_univ, by simp⟩)
  let Φ := squareExtensionFiberResidueAlgHom K p f m
  calc
    Fintype.card (SquareExtensionClosedPointFiber K p f m) =
        Nat.card (SquareExtensionClosedPointFiber K p f m) :=
      Fintype.card_eq_nat_card
    _ ≤ Nat.card
        (m.1.asIdeal.ResidueField →ₐ[K] SquareExtension K p) :=
      Nat.card_le_card_of_injective Φ
        (squareExtensionFiberResidueAlgHom_injective K p f m)
    _ ≤ Module.finrank K m.1.asIdeal.ResidueField :=
      card_algHom_le_finrank K m.1.asIdeal.ResidueField
        (SquareExtension K p)

omit [DecidableEq K] in
/-- Every such closed affine centre has degree one or two. -/
theorem squareExtensionClosedPoint_residueDegree_le_two
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :
    Module.finrank K m.1.asIdeal.ResidueField ≤ 2 := by
  obtain ⟨z, hz⟩ := m.2
  let zf : SquareExtensionClosedPointFiber K p f m :=
    ⟨z, Subtype.ext hz⟩
  let ι := squareExtensionFiberResidueAlgHom K p f m zf
  have hdvd : Module.finrank K m.1.asIdeal.ResidueField ∣
      Module.finrank K (SquareExtension K p) :=
    FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨ι⟩
  rw [FiniteField.finrank_extension K p 2] at hdvd
  exact Nat.le_of_dvd (by omega) hdvd

/-- The residue field of a maximal ideal is canonically the residue field of
its localization at that ideal, as an algebra over any compatible base
field. -/
def atPrimeResidueAlgEquiv
    (B R : Type*) [CommRing B] [Algebra K B]
    [CommRing R] [Algebra B R] [Algebra K R] [IsScalarTower K B R]
    [IsLocalRing R] (q : Ideal B) [q.IsMaximal]
    [IsLocalization.AtPrime R q] :
    q.ResidueField ≃ₐ[K] IsLocalRing.ResidueField R := by
  let e₁ : (B ⧸ q) ≃ₐ[K] q.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (B ⧸ q) q.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q)
  let e : (B ⧸ q) ≃+* IsLocalRing.ResidueField R :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q R
  let e₂ : (B ⧸ q) ≃ₐ[K] IsLocalRing.ResidueField R :=
    { e with
      commutes' := by
        intro c
        change (IsLocalization.AtPrime.equivQuotMaximalIdeal q R)
            (Ideal.Quotient.mk q (algebraMap K B c)) =
          IsLocalRing.residue R (algebraMap K R c)
        rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
          IsScalarTower.algebraMap_apply K B R]
        rfl }
  exact e₁.symm.trans e₂

/-! ## A selected normalization place above each closed affine centre -/

omit [DecidableEq K] in
/-- The first coordinate satisfies the quadratic-extension Frobenius
polynomial at every quadratic-extension point. -/
theorem squareExtensionFrobeniusElement_mem_pointMaximalIdeal
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f) :
    planeCurveCoordinate f 0 ^ (Nat.card K) ^ 2 -
        planeCurveCoordinate f 0 ∈
      (squareExtensionPointMaximalIdeal K p f z).asIdeal := by
  let : Fintype (SquareExtension K p) := Fintype.ofFinite _
  rw [squareExtensionPointMaximalIdeal_asIdeal]
  change squareExtensionPointEval K p f z
    (planeCurveCoordinate f 0 ^ (Nat.card K) ^ 2 -
      planeCurveCoordinate f 0) = 0
  rw [map_sub, map_pow, squareExtensionPointEval_coordinate]
  have hcard : Fintype.card (SquareExtension K p) = (Nat.card K) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact FiniteField.natCard_extension K p 2
  rw [← hcard, FiniteField.pow_card, sub_self]

private theorem residue_finrank_le_finitePlace_degree
    (K E A : Type*) [Field K] [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [Algebra K E]
    [IsScalarTower K (RatFunc K) E]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra A E]
    [IsScalarTower K A E] [IsFractionRing A E]
    [IsDedekindDomain (RatFuncFiniteIntegralClosure K E)]
    [IsFractionRing (RatFuncFiniteIntegralClosure K E) E]
    (m : MaximalSpectrum A) (q : FiniteExtensionFinitePlace K E)
    (hspec : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q =
      dominatingValuationSubring (L := E) m) :
    Module.finrank K m.asIdeal.ResidueField ≤ finiteExtensionPlaceDegree K E (.inl q) := by
  let : Algebra (Polynomial K) E :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) E).comp
      (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K) E := IsScalarTower.of_algebraMap_eq' rfl
  let B := RatFuncFiniteIntegralClosure K E
  let : Algebra K B :=
    RingHom.toAlgebra
      ((algebraMap (Polynomial K) B).comp (algebraMap K (Polynomial K)))
  let : IsScalarTower K (Polynomial K) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (Polynomial K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      rfl)
  let : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) E]
    rfl)
  let R := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q
  let : Algebra K R :=
    RingHom.toAlgebra ((algebraMap B R).comp (algebraMap K B))
  let : IsScalarTower K B R := IsScalarTower.of_algebraMap_eq' rfl
  let e := atPrimeResidueAlgEquiv K B R q.asIdeal
  have hplace : finiteExtensionPlaceDegree K E (.inl q) =
      Module.finrank K q.asIdeal.ResidueField :=
    finiteExtensionFinitePlace_degree_eq_finrank_residueField K E q
  let : Module.Finite K q.asIdeal.ResidueField :=
    Module.finite_of_finrank_pos (by
      rw [← hplace]
      exact finiteExtensionPlaceDegree_pos K E (.inl q))
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.equiv e.toLinearEquiv
  have hle : Module.finrank K m.asIdeal.ResidueField ≤
      Module.finrank K (IsLocalRing.ResidueField R) :=
    residue_finrank_le_of_dominating_valuation m R (fun c => by
      change algebraMap B E (algebraMap K B c) = algebraMap K E c
      exact (IsScalarTower.algebraMap_apply K B E c).symm) hspec
  have heq : Module.finrank K (IsLocalRing.ResidueField R) =
      Module.finrank K q.asIdeal.ResidueField :=
    e.symm.toLinearEquiv.finrank_eq
  rw [hplace, ← heq]
  exact hle

omit [DecidableEq K] in
/-- Every base closed affine centre arising from a quadratic-extension point
has an exhaustive finite place above it. -/
theorem exists_squareExtensionClosedPoint_exhaustiveFinitePlace
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : IsDedekindDomain
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)) :=
      integralClosure.isDedekindDomain (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f)
    let : IsFractionRing
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f))
        (PlaneCurveFunctionField f) :=
      integralClosure.isFractionRing_of_finite_extension (RatFunc K)
        (PlaneCurveFunctionField f)
    ∃ q : HeightOneSpectrum
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)),
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f) q =
        dominatingValuationSubring m.1 := by
  intro inst hx alg poly tower finite separable dedekind fraction
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  let B := integralClosure (Polynomial K) E
  let hbase : ∀ P : Polynomial K,
      algebraMap (Polynomial K) E P ∈ (algebraMap A E).range :=
    polynomial_algebraMap_mem_planeCurveCoordinateRing_range hf hpartialSecond
  let V := dominatingValuationSubring (A := A) (L := E) m.1
  let r : A := planeCurveCoordinate f 0 ^ (Nat.card K) ^ 2 -
    planeCurveCoordinate f 0
  let P : Polynomial K := Polynomial.X ^ (Nat.card K) ^ 2 - Polynomial.X
  obtain ⟨z, hz⟩ := m.2
  have hm : squareExtensionPointMaximalIdeal K p f z = m.1 := hz
  have hr : r ∈ m.1.asIdeal := by
    rw [← hm]
    exact squareExtensionFrobeniusElement_mem_pointMaximalIdeal K p f z
  have hP0 : P ≠ 0 := by
    exact FiniteField.X_pow_card_pow_sub_X_ne_zero K (by omega)
      Finite.one_lt_card
  have hPMap : algebraMap (Polynomial K) E P =
      planeCurveFunction f 0 ^ (Nat.card K) ^ 2 -
        planeCurveFunction f 0 := by
    change ratFuncSpecialization (planeCurveFunction f 0) hx
      (algebraMap (Polynomial K) (RatFunc K) P) = _
    have hcomp := congrArg
      (fun h : Polynomial K →+* E => h P)
      (ratFuncSpecialization_comp_polynomial_algebraMap
        (planeCurveFunction f 0) hx)
    simpa only [P, RingHom.comp_apply, map_sub, map_pow,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hcomp
  have hrMap : algebraMap A E r =
      planeCurveFunction f 0 ^ (Nat.card K) ^ 2 -
        planeCurveFunction f 0 := by
    simp only [r, map_sub, map_pow]
    rfl
  have hinj : Function.Injective (algebraMap (Polynomial K) E) :=
    (algebraMap (RatFunc K) E).injective.comp (RatFunc.algebraMap_injective K)
  exact exists_dominatingPlace_of_base_element m.1 hbase hinj P hP0 r hr
    (hPMap.trans hrMap.symm)

/-- The selected exhaustive finite place above a quadratic-extension closed
affine centre. -/
def squareExtensionClosedPointExhaustiveFinitePlace
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    FiniteExtensionFinitePlace K (PlaneCurveFunctionField f) := by
  exact Classical.choose
    (exists_squareExtensionClosedPoint_exhaustiveFinitePlace
      K p hf hpartialSecond m)

omit [DecidableEq K] in
/-- The selected place has the prescribed dominating valuation subring. -/
theorem squareExtensionClosedPointExhaustiveFinitePlace_spec
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (PlaneCurveFunctionField f)
        (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m) =
      dominatingValuationSubring m.1 := by
  exact Classical.choose_spec
    (exists_squareExtensionClosedPoint_exhaustiveFinitePlace
      K p hf hpartialSecond m)

omit [DecidableEq K] in
/-- Distinct closed affine centres have distinct selected finite places. -/
theorem squareExtensionClosedPointExhaustiveFinitePlace_injective
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    Function.Injective
      (squareExtensionClosedPointExhaustiveFinitePlace
        K p hf hpartialSecond) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change Function.Injective
    (squareExtensionClosedPointExhaustiveFinitePlace
      K p hf hpartialSecond)
  intro m n hmn
  apply Subtype.ext
  apply MaximalSpectrum.ext
  apply pointIdeal_eq_of_dominatingValuationSubring_eq
    (A := PlaneCurveCoordinateRing f)
    (L := PlaneCurveFunctionField f)
  calc
    dominatingValuationSubring m.1 =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (squareExtensionClosedPointExhaustiveFinitePlace
            K p hf hpartialSecond m) :=
      (squareExtensionClosedPointExhaustiveFinitePlace_spec
        K p hf hpartialSecond m).symm
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (squareExtensionClosedPointExhaustiveFinitePlace
            K p hf hpartialSecond n) := by rw [hmn]
    _ = dominatingValuationSubring n.1 :=
      squareExtensionClosedPointExhaustiveFinitePlace_spec
        K p hf hpartialSecond n

/-- The residue degree of a closed affine centre is at most the degree of its
selected normalization place.  The inequality can be strict at a singular
centre. -/
theorem squareExtensionClosedPoint_residueDegree_le_placeDegree
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : DecidableEq (RatFunc K) := Classical.decEq _
    Module.finrank K m.1.asIdeal.ResidueField ≤
      finiteExtensionPlaceDegree K (PlaneCurveFunctionField f)
        (.inl (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m)) := by
  intro inst hx alg poly tower finite separable decEq
  let E := PlaneCurveFunctionField f
  let q : FiniteExtensionFinitePlace K E :=
    squareExtensionClosedPointExhaustiveFinitePlace
      K p hf hpartialSecond m
  let : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  exact residue_finrank_le_finitePlace_degree K E (PlaneCurveCoordinateRing f) m.1 q
    (squareExtensionClosedPointExhaustiveFinitePlace_spec K p hf hpartialSecond m)

/-- Quadratic-extension affine points are bounded by the sum of the degrees
of one selected normalization place above each closed affine centre.  The
residue degree is the weight that accounts for Frobenius-conjugate points. -/
theorem squareExtensionAffinePoint_card_le_selectedPlaceDegreeSum
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : DecidableEq (RatFunc K) := Classical.decEq _
    Fintype.card (SquareExtensionAffinePoint K p f) ≤
      ∑ m : SquareExtensionClosedPoint K p f,
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f)
          (.inl (squareExtensionClosedPointExhaustiveFinitePlace
            K p hf hpartialSecond m)) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  have hcard :
      Fintype.card (SquareExtensionAffinePoint K p f) =
        ∑ m : SquareExtensionClosedPoint K p f,
          Fintype.card (SquareExtensionClosedPointFiber K p f m) := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr
      (Equiv.sigmaFiberEquiv (squareExtensionClosedPointMap K p f)).symm
  rw [hcard]
  apply Finset.sum_le_sum
  intro m _hm
  exact (squareExtensionClosedPointFiber_card_le_residueDegree K p f m).trans
    (squareExtensionClosedPoint_residueDegree_le_placeDegree
      K p hf hpartialSecond m)

/-- If a nonzero function has positive order at one selected normalization
place above every closed affine centre arising over the quadratic extension,
then every such affine point is counted by the function's pole height. -/
theorem squareExtensionAffinePoint_card_le_finiteExtensionHeight_of_selectedPlace_orders_positive
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (u : PlaneCurveFunctionField f) (hu : u ≠ 0) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : DecidableEq (RatFunc K) := Classical.decEq _
    (∀ m : SquareExtensionClosedPoint K p f,
      0 < finiteExtensionPrincipalDivisor K (PlaneCurveFunctionField f) u
        (.inl (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m))) →
      Fintype.card (SquareExtensionAffinePoint K p f) ≤
        finiteExtensionHeight K (PlaneCurveFunctionField f) u := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  change
    (∀ m : SquareExtensionClosedPoint K p f,
      0 < finiteExtensionPrincipalDivisor K (PlaneCurveFunctionField f) u
        (.inl (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m))) →
      Fintype.card (SquareExtensionAffinePoint K p f) ≤
        finiteExtensionHeight K (PlaneCurveFunctionField f) u
  intro hpositive
  classical
  let place : SquareExtensionClosedPoint K p f →
      FiniteExtensionPlace K (PlaneCurveFunctionField f) := fun m =>
    .inl (squareExtensionClosedPointExhaustiveFinitePlace
      K p hf hpartialSecond m)
  have hplaceInjective : Function.Injective place := by
    intro m n hmn
    apply squareExtensionClosedPointExhaustiveFinitePlace_injective
      K p hf hpartialSecond
    exact Sum.inl_injective hmn
  let : DecidableEq (FiniteExtensionPlace K (PlaneCurveFunctionField f)) :=
    @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)
  let S : Finset (FiniteExtensionPlace K (PlaneCurveFunctionField f)) :=
    Finset.univ.image place
  have hsum :
      (∑ m : SquareExtensionClosedPoint K p f,
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) (place m)) =
      ∑ v ∈ S,
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) v := by
    symm
    exact Finset.sum_image hplaceInjective.injOn
  have hSpositive :
      ∀ v ∈ S,
        0 < finiteExtensionPrincipalDivisor K (PlaneCurveFunctionField f) u v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨m, _hm, rfl⟩
    exact hpositive m
  calc
    Fintype.card (SquareExtensionAffinePoint K p f) ≤
        ∑ m : SquareExtensionClosedPoint K p f,
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) (place m) := by
      exact squareExtensionAffinePoint_card_le_selectedPlaceDegreeSum
        K p hf hpartialSecond
    _ = ∑ v ∈ S,
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) v := hsum
    _ ≤ finiteExtensionHeight K (PlaneCurveFunctionField f) u :=
      sum_placeDegree_le_finiteExtensionHeight_of_orders_positive
        K (PlaneCurveFunctionField f) u hu S hSpositive

end

end BGS.HasseWeil
