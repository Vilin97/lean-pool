/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryIndependence
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageCurve
public import LeanPool.MarkoffModP.BGS.HasseWeil.PoleDivisor
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Plane monomial spaces for the Stepanov construction

This file packages the finite rectangular spaces spanned by the monomials
`x ^ i * y ^ j`.  It proves their dimension from linear independence, gives
a plane-curve independence criterion from the degree in one coordinate, and
records the mixed-radix exponent map occurring when an ordinary grid is
multiplied by a grid in the powered coordinates.

The final tower lemma is the algebraic form needed by Stepanov: if the
ordinary (digit) grid is independent over a subfield containing `x ^ s` and
`y ^ s`, and the powered grid is independent over the constant field, then
the twisted products

`x ^ (i + s * i') * y ^ (j + s * j')`

are independent over the constant field.  No Frobenius endomorphism is
introduced or assumed.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

/-- The rectangular family of plane monomials with `i < a` and `j < b`. -/
def planeMonomialGrid
    {L : Type*} [Monoid L]
    (x y : L) (a b : ℕ) : Fin a × Fin b → L :=
  fun ij ↦ x ^ (ij.1 : ℕ) * y ^ (ij.2 : ℕ)

/-- The finite `K`-subspace spanned by a rectangular plane-monomial grid. -/
def planeMonomialSpace
    (K : Type*) {L : Type*} [Field K] [CommRing L] [Algebra K L]
    (x y : L) (a b : ℕ) : Submodule K L :=
  Submodule.span K (Set.range (planeMonomialGrid x y a b))

theorem planeMonomialGrid_mem_space
    {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (x y : L) (a b : ℕ) (ij : Fin a × Fin b) :
    planeMonomialGrid x y a b ij ∈ planeMonomialSpace K x y a b :=
  Submodule.subset_span (Set.mem_range_self ij)

/-- A rectangular monomial space is finite, independently of any
linear-independence hypothesis. -/
theorem moduleFinite_planeMonomialSpace
    (K : Type*) {L : Type*} [Field K] [CommRing L] [Algebra K L]
    (x y : L) (a b : ℕ) :
    Module.Finite K (planeMonomialSpace K x y a b) := by
  exact Module.Finite.span_of_finite K
    (Set.finite_range (planeMonomialGrid x y a b))

/-- Linear independence identifies the finrank of a rectangular monomial
space with the number of grid points. -/
theorem finrank_planeMonomialSpace_eq_mul
    {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (x y : L) (a b : ℕ)
    (hLI : LinearIndependent K (planeMonomialGrid x y a b)) :
    Module.finrank K (planeMonomialSpace K x y a b) = a * b := by
  change Module.finrank K
    (Submodule.span K (Set.range (planeMonomialGrid x y a b))) = a * b
  rw [finrank_span_eq_card hLI, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

/-- Finite initial segments of the powers of a transcendental element are
linearly independent. -/
theorem linearIndependent_fin_powers_of_transcendental
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (z : A) (hz : Transcendental K z) (n : ℕ) :
    LinearIndependent K (fun i : Fin n ↦ z ^ (i : ℕ)) := by
  have hpolynomial : LinearIndependent K
      (fun i : Fin n ↦ (Polynomial.X : Polynomial K) ^ (i : ℕ)) := by
    simpa only [Polynomial.coe_basisMonomials,
      Polynomial.monomial_one_right_eq_X_pow, Function.comp_def] using
      (Polynomial.basisMonomials K).linearIndependent.comp
        (fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  have heval : LinearMap.ker (Polynomial.aeval z).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective
      ((transcendental_iff_injective.mp hz))
  have hmapped :=
    hpolynomial.map' (Polynomial.aeval z).toLinearMap heval
  change LinearIndependent K
    (fun i : Fin n ↦ (Polynomial.aeval z)
      ((Polynomial.X : Polynomial K) ^ (i : ℕ))) at hmapped
  simpa only [Polynomial.aeval_X_pow] using hmapped

/-- A tower criterion for a rectangular monomial grid.  Powers of the
transcendental lower coordinate supply one independent family, and powers of
the upper element below its minimal-polynomial degree supply the other. -/
theorem planeMonomialGrid_linearIndependent_of_transcendental_minpoly
    {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (x : F) (y : L) (a b : ℕ)
    (hx : Transcendental K x)
    (hb : b ≤ (minpoly F y).natDegree) :
    LinearIndependent K
      (planeMonomialGrid (algebraMap F L x) y a b) := by
  have hxPowers : LinearIndependent K (fun i : Fin a ↦ x ^ (i : ℕ)) :=
    linearIndependent_fin_powers_of_transcendental x hx a
  have hyPowers : LinearIndependent F (fun j : Fin b ↦ y ^ (j : ℕ)) := by
    simpa only [Function.comp_def, Fin.val_castLE] using
      (linearIndependent_pow y).comp (Fin.castLE hb)
        (Fin.castLE_injective hb)
  change LinearIndependent K
    (fun ij : Fin a × Fin b ↦
      (algebraMap F L x) ^ (ij.1 : ℕ) * y ^ (ij.2 : ℕ))
  simpa only [Algebra.smul_def, map_pow] using
    (linearIndependent_smul hxPowers hyPowers)

/-- The grid part of the Corvaja--Zannier auxiliary family is a linearly
independent rectangular monomial family. -/
theorem planeMonomialGrid_linearIndependent_of_auxiliaryFamily
    {C L : Type*} [Field C] [Field L] [Algebra C L]
    (u v : L) (h k : ℕ)
    (haux : LinearIndependent C (auxiliaryFamily u v h k)) :
    LinearIndependent C (planeMonomialGrid u v (k + 1) h) := by
  change LinearIndependent C
    (fun rs : Fin (k + 1) × Fin h ↦
      u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))
  simpa only [Function.comp_def, auxiliaryFamily] using
    haux.comp (fun rs : Fin (k + 1) × Fin h ↦ Sum.inr rs)
      Sum.inr_injective

/-- On an irreducible plane curve, monomials with arbitrary first exponent
and second exponent below the second-coordinate degree are independent. -/
theorem planeCurve_monomialGrid_linearIndependent
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (a b : ℕ) (hb : b ≤ MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    LinearIndependent K
      (planeMonomialGrid (planeCurveFunction f 0)
        (planeCurveFunction f 1) a b) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let xF : FirstCoordinateSubfield f := firstCoordinateInSubfield f
  have hxL : Transcendental K (planeCurveFunction f 0) :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hxF : Transcendental K xF := by
    apply (transcendental_algebraMap_iff
      (algebraMap (FirstCoordinateSubfield f)
        (PlaneCurveFunctionField f)).injective).mp
    change Transcendental K
      (algebraMap (FirstCoordinateSubfield f)
        (PlaneCurveFunctionField f) xF)
    simpa only [xF, firstCoordinateInSubfield,
      IntermediateField.algebraMap_apply] using hxL
  have hminpoly :
      (minpoly (FirstCoordinateSubfield f)
        (planeCurveFunction f 1)).natDegree =
      MvPolynomial.degreeOf 1 f :=
    natDegree_minpoly_secondCoordinate_eq_degreeOf_second
      hf hpartialSecond
  have hb' : b ≤ (minpoly (FirstCoordinateSubfield f)
      (planeCurveFunction f 1)).natDegree := by
    rw [hminpoly]
    exact hb
  simpa only [xF, firstCoordinateInSubfield,
    IntermediateField.algebraMap_apply] using
    planeMonomialGrid_linearIndependent_of_transcendental_minpoly
      xF (planeCurveFunction f 1) a b hxF hb'

/-- The bidegree criterion gives the exact dimension of the corresponding
plane-curve monomial space. -/
theorem finrank_planeCurve_monomialSpace_eq_mul
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (a b : ℕ) (hb : b ≤ MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank K
      (planeMonomialSpace K (planeCurveFunction f 0)
        (planeCurveFunction f 1) a b) = a * b := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact finrank_planeMonomialSpace_eq_mul
    (planeCurveFunction f 0) (planeCurveFunction f 1) a b
    (planeCurve_monomialGrid_linearIndependent
      hf hpartialSecond a b hb)

/-- The mixed-radix exponent attached to a low digit and a high digit. -/
def digitExponent {a a' : ℕ} (s : ℕ) (ii' : Fin a × Fin a') : ℕ :=
  (ii'.1 : ℕ) + s * (ii'.2 : ℕ)

/-- Low digits bounded by the radix make the mixed-radix exponent map
injective. -/
theorem digitExponent_injective
    {s a a' : ℕ} (ha : a ≤ s) :
    Function.Injective (digitExponent (a := a) (a' := a') s) := by
  rintro ⟨i, i'⟩ ⟨k, k'⟩ heq
  have hi : (i : ℕ) < s := i.isLt.trans_le ha
  have hk : (k : ℕ) < s := k.isLt.trans_le ha
  have hs : 0 < s := by omega
  have hlow : (i : ℕ) = (k : ℕ) := by
    have hmod := congrArg (fun n : ℕ ↦ n % s) heq
    change ((i : ℕ) + s * (i' : ℕ)) % s =
      ((k : ℕ) + s * (k' : ℕ)) % s at hmod
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] at hmod
    exact hmod
  have hhigh : (i' : ℕ) = (k' : ℕ) := by
    have hmul : s * (i' : ℕ) = s * (k' : ℕ) := by
      apply Nat.add_left_cancel (n := (i : ℕ))
      simpa only [digitExponent, hlow] using heq
    exact Nat.mul_left_cancel hs hmul
  exact Prod.ext (Fin.ext hlow) (Fin.ext hhigh)

/-- The pair of mixed-radix exponents used by the twisted monomial grid. -/
def twistedExponentGrid
    (s a b a' b' : ℕ) :
    (Fin a × Fin b) × (Fin a' × Fin b') → ℕ × ℕ :=
  fun z ↦
    ((z.1.1 : ℕ) + s * (z.2.1 : ℕ),
      (z.1.2 : ℕ) + s * (z.2.2 : ℕ))

/-- Digit bounds in both coordinates make the exponent-pair map injective. -/
theorem twistedExponentGrid_injective
    {s a b a' b' : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    Function.Injective (twistedExponentGrid s a b a' b') := by
  rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ ⟨⟨k, l⟩, ⟨k', l'⟩⟩ heq
  have hfirst : (i, i') = (k, k') :=
    digitExponent_injective ha (congrArg Prod.fst heq)
  have hsecond : (j, j') = (l, l') :=
    digitExponent_injective hb (congrArg Prod.snd heq)
  cases hfirst
  cases hsecond
  rfl

/-- The products of an ordinary monomial grid and its `s`-powered copy. -/
def twistedPlaneMonomialGrid
    {L : Type*} [Monoid L]
    (x y : L) (s a b a' b' : ℕ) :
    (Fin a × Fin b) × (Fin a' × Fin b') → L :=
  fun z ↦
    x ^ ((z.1.1 : ℕ) + s * (z.2.1 : ℕ)) *
      y ^ ((z.1.2 : ℕ) + s * (z.2.2 : ℕ))

/-- Send a pair of low and high digits to the encompassing rectangular
grid. -/
def twistedGridToGrid
    (s a b a' b' : ℕ) :
    (Fin a × Fin b) × (Fin a' × Fin b') →
      Fin (a + s * a') × Fin (b + s * b') :=
  fun z ↦
    (⟨(z.1.1 : ℕ) + s * (z.2.1 : ℕ),
      Nat.add_lt_add_of_lt_of_le z.1.1.isLt
        (Nat.mul_le_mul_left s z.2.1.isLt.le)⟩,
    ⟨(z.1.2 : ℕ) + s * (z.2.2 : ℕ),
      Nat.add_lt_add_of_lt_of_le z.1.2.isLt
        (Nat.mul_le_mul_left s z.2.2.isLt.le)⟩)

theorem twistedGridToGrid_injective
    {s a b a' b' : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    Function.Injective (twistedGridToGrid s a b a' b') := by
  intro z w hzw
  apply twistedExponentGrid_injective ha hb
  exact congrArg (fun q ↦ ((q.1 : ℕ), (q.2 : ℕ))) hzw

/-- Direct bidegree criterion for the twisted family.  The digit bounds make
the exponent encoding injective, while the final second-exponent range stays
below the curve's second-coordinate degree. -/
theorem planeCurve_twistedMonomialGrid_linearIndependent
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (s a b a' b' : ℕ)
    (ha : a ≤ s) (hb : b ≤ s)
    (hdegree : b + s * b' ≤ MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    LinearIndependent K
      (twistedPlaneMonomialGrid (planeCurveFunction f 0)
        (planeCurveFunction f 1) s a b a' b') := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have hgrid := planeCurve_monomialGrid_linearIndependent
    hf hpartialSecond (a + s * a') (b + s * b') hdegree
  have hsubfamily := hgrid.comp (twistedGridToGrid s a b a' b')
    (twistedGridToGrid_injective ha hb)
  change LinearIndependent K
    (fun z : (Fin a × Fin b) × (Fin a' × Fin b') ↦
      (planeCurveFunction f 0) ^
          ((z.1.1 : ℕ) + s * (z.2.1 : ℕ)) *
        (planeCurveFunction f 1) ^
          ((z.1.2 : ℕ) + s * (z.2.2 : ℕ)))
  simpa only [Function.comp_def, planeMonomialGrid,
    twistedGridToGrid] using hsubfamily

/-- In particular, under the direct bidegree criterion the twisted grid is
an injective family of functions. -/
theorem planeCurve_twistedMonomialGrid_injective
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (s a b a' b' : ℕ)
    (ha : a ≤ s) (hb : b ≤ s)
    (hdegree : b + s * b' ≤ MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    Function.Injective
      (twistedPlaneMonomialGrid (planeCurveFunction f 0)
        (planeCurveFunction f 1) s a b a' b') := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (planeCurve_twistedMonomialGrid_linearIndependent
    hf hpartialSecond s a b a' b' ha hb hdegree).injective

/-- Tower composition for Stepanov's twisted grid.  The ordinary grid is
independent over `F`; the powered grid, regarded inside `F`, is independent
over `K`.  Multiplication combines the two independent families. -/
theorem twistedPlaneMonomialGrid_linearIndependent_of_subfield
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : Subfield L) [Algebra K F] [IsScalarTower K F L]
    (x y : L) (s a b a' b' : ℕ)
    (hxs : x ^ s ∈ F) (hys : y ^ s ∈ F)
    (hdigit : LinearIndependent F (planeMonomialGrid x y a b))
    (hpowered : LinearIndependent K
      (planeMonomialGrid (⟨x ^ s, hxs⟩ : F)
        (⟨y ^ s, hys⟩ : F) a' b')) :
    LinearIndependent K
      (twistedPlaneMonomialGrid x y s a b a' b') := by
  have hproduct := linearIndependent_smul hpowered hdigit
  have hreindexed := hproduct.comp
    (fun z : (Fin a × Fin b) × (Fin a' × Fin b') ↦ (z.2, z.1))
    (Equiv.prodComm (Fin a × Fin b) (Fin a' × Fin b')).injective
  have hcoeX : F.subtype (⟨x ^ s, hxs⟩ : F) = x ^ s := rfl
  have hcoeY : F.subtype (⟨y ^ s, hys⟩ : F) = y ^ s := rfl
  change LinearIndependent K
    (fun z : (Fin a × Fin b) × (Fin a' × Fin b') ↦
      x ^ ((z.1.1 : ℕ) + s * (z.2.1 : ℕ)) *
        y ^ ((z.1.2 : ℕ) + s * (z.2.2 : ℕ)))
  simpa only [Function.comp_def, planeMonomialGrid,
    Algebra.smul_def, map_mul, map_pow,
    Subfield.algebraMap_ofSubfield, RingHom.coe_coe,
    hcoeX, hcoeY, Subtype.coe_mk, pow_mul, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using hreindexed

/-- The powered-image relation supplies the bidegree needed for a monomial
grid in the powered coordinates. -/
theorem planeCurve_poweredMonomialGrid_linearIndependent
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n a b : ℕ)
    (hb : b ≤
      (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree) :
    letI := planeCurveCoordinateRing_isDomain hf
    LinearIndependent K
      (planeMonomialGrid ((planeCurveFunction f 0) ^ m)
        ((planeCurveFunction f 1) ^ n) a b) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let xm : FirstPoweredCoordinateSubfield f m :=
    ⟨(planeCurveFunction f 0) ^ m,
      IntermediateField.mem_adjoin_simple_self K
        ((planeCurveFunction f 0) ^ m)⟩
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hxmL : Transcendental K ((planeCurveFunction f 0) ^ m) :=
    firstPoweredCoordinate_transcendental hf hpartialSecond m hm
  have hxm : Transcendental K xm := by
    apply (transcendental_algebraMap_iff
      (algebraMap (FirstPoweredCoordinateSubfield f m)
        (PlaneCurveFunctionField f)).injective).mp
    change Transcendental K
      (algebraMap (FirstPoweredCoordinateSubfield f m)
        (PlaneCurveFunctionField f) xm)
    simpa only [xm, IntermediateField.algebraMap_apply] using hxmL
  have hynIntegral : IsIntegral (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n) :=
    IsIntegral.of_finite (FirstPoweredCoordinateSubfield f m) _
  have hminpoly :
      (minpoly (FirstPoweredCoordinateSubfield f m)
        ((planeCurveFunction f 1) ^ n)).natDegree =
      (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree := by
    calc
      (minpoly (FirstPoweredCoordinateSubfield f m)
          ((planeCurveFunction f 1) ^ n)).natDegree =
          Module.finrank (FirstPoweredCoordinateSubfield f m)
            (PoweredImageOverFirst f m n) :=
        (IntermediateField.adjoin.finrank hynIntegral).symm
      _ = (poweredCoordinateImageRelation
          hf hpartialSecond m hm n).natDegree :=
        (poweredCoordinateImageRelation_natDegree_eq_finrank
          hf hpartialSecond m hm n).symm
  have hb' : b ≤ (minpoly (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n)).natDegree := by
    rw [hminpoly]
    exact hb
  simpa only [xm, IntermediateField.algebraMap_apply] using
    planeMonomialGrid_linearIndependent_of_transcendental_minpoly
      xm ((planeCurveFunction f 1) ^ n) a b hxm hb'

section PoleBudget

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance planeMonomialSpaceConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance planeMonomialSpaceConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Every monomial with `x`-exponent at most `n` and `y`-exponent below `b`
lies in the Riemann space with pole budget
`n · pole(x) + (b - 1) · pole(y)`. -/
theorem planeMonomialSpace_le_poleDivisorBudget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (n b : ℕ) :
    planeMonomialSpace K x y (n + 1) b ≤
      finiteExtensionRiemannSpace K L
        (n • finiteExtensionPoleDivisor K L x +
          (b - 1) • finiteExtensionPoleDivisor K L y) := by
  apply Submodule.span_le.mpr
  rintro z ⟨ij, rfl⟩
  apply finiteExtensionRiemannSpace_mono K L
    (D := (ij.1 : ℕ) • finiteExtensionPoleDivisor K L x +
      (ij.2 : ℕ) • finiteExtensionPoleDivisor K L y)
  · exact add_le_add
      (nsmul_le_nsmul_left
        (finiteExtensionPoleDivisor_effective K L x)
        (by omega))
      (nsmul_le_nsmul_left
        (finiteExtensionPoleDivisor_effective K L y)
        (by omega))
  · exact pow_mul_pow_mem_poleDivisor_budget
      K L x y hx hy (ij.1 : ℕ) (ij.2 : ℕ)

/-- Pole-budget containment is already useful before finite-dimensionality of
the ambient Riemann space has been established: it gives monotonicity of the
corresponding module ranks. -/
theorem rank_planeMonomialSpace_le_rank_poleDivisorBudget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (n b : ℕ) :
    Module.rank K (planeMonomialSpace K x y (n + 1) b) ≤
      Module.rank K
        (finiteExtensionRiemannSpace K L
          (n • finiteExtensionPoleDivisor K L x +
            (b - 1) • finiteExtensionPoleDivisor K L y)) :=
  Submodule.rank_mono
    (planeMonomialSpace_le_poleDivisorBudget K L x y hx hy n b)

/-- Once finite-dimensionality of the ambient Riemann space is available,
the same containment yields the numerical lower bound `(n + 1) * b`. -/
theorem add_one_mul_le_finrank_poleDivisorBudget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (n b : ℕ)
    (hLI : LinearIndependent K (planeMonomialGrid x y (n + 1) b))
    (hfinite : Module.Finite K
      (finiteExtensionRiemannSpace K L
        (n • finiteExtensionPoleDivisor K L x +
          (b - 1) • finiteExtensionPoleDivisor K L y))) :
    (n + 1) * b ≤ Module.finrank K
      (finiteExtensionRiemannSpace K L
        (n • finiteExtensionPoleDivisor K L x +
          (b - 1) • finiteExtensionPoleDivisor K L y)) := by
  let : Module.Finite K
      (finiteExtensionRiemannSpace K L
        (n • finiteExtensionPoleDivisor K L x +
          (b - 1) • finiteExtensionPoleDivisor K L y)) := hfinite
  calc
    (n + 1) * b = Module.finrank K
        (planeMonomialSpace K x y (n + 1) b) :=
      (finrank_planeMonomialSpace_eq_mul x y (n + 1) b hLI).symm
    _ ≤ Module.finrank K
        (finiteExtensionRiemannSpace K L
          (n • finiteExtensionPoleDivisor K L x +
            (b - 1) • finiteExtensionPoleDivisor K L y)) :=
      Submodule.finrank_mono
        (planeMonomialSpace_le_poleDivisorBudget
          K L x y hx hy n b)

end PoleBudget

end

end BGS.HasseWeil
