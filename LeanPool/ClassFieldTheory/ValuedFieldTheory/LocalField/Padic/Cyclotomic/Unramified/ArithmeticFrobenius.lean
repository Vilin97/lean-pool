/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# Arithmetic Frobenius on the unramified cyclotomic extension

Let `K` be a complete discretely valued field with finite residue field
`k = F_q`, let `ζ` be a primitive `n`-th root of unity, and suppose that `n`
is prime to the residue characteristic.  the unramified cyclotomic theorem states that
`K(ζ) / K` is unramified of degree the order of `q` modulo `n`, identifies
its Galois group with the residue Galois group and arithmetic Frobenius, and
proves `O_{K(ζ)} = O_K[ζ]`.

The proof follows the arithmetic construction directly and uses no comparison certificate:

* the exact least-positive-exponent characterization of the order of `q`
  modulo `n`;
* the cyclotomic polynomial as the primitive separable integral model in the
  the unramified base-change theorem Hensel core, giving unramifiedness and the degree formula;
* the canonical reduction homomorphism from field automorphisms to residue
  automorphisms, with injectivity from uniqueness of simple Hensel lifts and
  surjectivity from the genuine Galois cardinalities;
* arithmetic Frobenius, its formula `ζ ↦ ζ^q`, and generation of the Galois
  group;
* the reverse integral-ring inclusion by residue generation, ramification
  index one, and Nakayama, yielding `O_{K(ζ)} = O_K[ζ]`.
-/

@[expose] public section

noncomputable
section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial ZMod


/-- The integer `f` in the unramified cyclotomic theorem: the multiplicative order of the
residue cardinality `q` modulo `n`. -/
def padicCyclotomicUnramifiedResidueDegree (n q : ℕ) (hqn : q.Coprime n) : ℕ :=
  orderOf (ZMod.unitOfCoprime q hqn)

theorem padicCyclotomicUnramifiedResidueDegree_pos
    (n q : ℕ) (hqn : q.Coprime n) :
    0 < padicCyclotomicUnramifiedResidueDegree n q hqn := by
  exact orderOf_pos _

/-- The defining exponent satisfies `q^f = 1 mod n`. -/
theorem padicCyclotomicUnramifiedResidueDegree_modEq_one
    (n q : ℕ) (hqn : q.Coprime n) :
    q ^ padicCyclotomicUnramifiedResidueDegree n q hqn ≡ 1 [MOD n] := by
  have hpow := pow_orderOf_eq_one (ZMod.unitOfCoprime q hqn)
  have hval := congrArg Units.val hpow
  rw [Units.val_pow_eq_pow_val, coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hval
  exact hval

/-- Minimality of the exponent in the unramified cyclotomic theorem. -/
theorem padicCyclotomicUnramifiedResidueDegree_le_of_modEq_one
    (n q : ℕ) (hqn : q.Coprime n) {m : ℕ}
    (hm : 0 < m) (hqm : q ^ m ≡ 1 [MOD n]) :
    padicCyclotomicUnramifiedResidueDegree n q hqn ≤ m := by
  apply orderOf_le_of_pow_eq_one hm
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  exact hqm

/-- Literal least-positive-natural-number formulation of the degree in
the unramified cyclotomic theorem(i). -/
theorem padicCyclotomicUnramifiedResidueDegree_isLeast
    (n q : ℕ) (hqn : q.Coprime n) :
    0 < padicCyclotomicUnramifiedResidueDegree n q hqn ∧
      q ^ padicCyclotomicUnramifiedResidueDegree n q hqn ≡ 1 [MOD n] ∧
        ∀ m : ℕ, 0 < m → q ^ m ≡ 1 [MOD n] →
          padicCyclotomicUnramifiedResidueDegree n q hqn ≤ m := by
  exact
    ⟨padicCyclotomicUnramifiedResidueDegree_pos n q hqn,
      padicCyclotomicUnramifiedResidueDegree_modEq_one n q hqn,
      fun _ hm hqm ↦
        padicCyclotomicUnramifiedResidueDegree_le_of_modEq_one n q hqn hm hqm⟩


/-- A root of unity is integral over any coefficient ring acting on its
ambient field.  This is the element-level source for the unramified cyclotomic theorem(iii). -/
theorem padicCyclotomicUnramified_primitiveRoot_isIntegral
    {R : Type u} {L : Type v} [CommRing R] [Field L] [Algebra R L]
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    IsIntegral R ζ := by
  apply IsIntegral.of_pow hn
  rw [hζ.pow_eq_one]
  exact isIntegral_one

/-- Turn a literal equality with the integral closure into the standard
`IsIntegralClosure` instance. -/
private theorem padicCyclotomicUnramified_isIntegralClosure_of_subring_eq
    {K L : Type*} [Field K] [Field L]
    (V : Subring K) (W : Subring L) [Algebra V L]
    (h : W = (integralClosure V L).toSubring) :
    IsIntegralClosure W V L := by
  refine
    { algebraMap_injective := W.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxW : x ∈ W := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxW⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    change (y : L) ∈ (integralClosure V L).toSubring
    rw [← h]
    exact y.property

/-- Two simple roots over a local domain which have the same residue class
are equal.  This is the uniqueness half of Hensel's lemma, in the small
generality needed for the residue-action comparisons below and in the
generic unramified support lemma for the unramified cyclotomic theorem. -/
theorem padicCyclotomicUnramified_eq_of_roots_of_residue_eq_of_derivative_isUnit
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R[X]} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : IsLocalRing.residue R b = IsLocalRing.residue R a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : R[X] := f /ₘ (X - C a)
  have hfactor : (X - C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hqEval : q.eval a = f.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval f a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqResidue :
      IsLocalRing.residue R (q.eval b) =
        IsLocalRing.residue R (q.eval a) := by
    calc
      IsLocalRing.residue R (q.eval b) =
          (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R b) := by
        exact (Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) b).symm
      _ = (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R a) := by rw [hres]
      _ = IsLocalRing.residue R (q.eval a) := by
        exact Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) a
  have hqResidueNe : IsLocalRing.residue R (q.eval b) ≠ 0 := by
    rw [hqResidue]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnit
  have hqNe : q.eval b ≠ 0 := by
    intro hzero
    exact hqResidueNe (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hbEval : ((X - C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hbEval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hqNe)

section CanonicalResidueAction

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- Restriction of a `K`-automorphism to the target valuation ring.  The
target ring is the integral closure of the Henselian base valuation ring, so
this restriction is canonical. -/
noncomputable def padicCyclotomicUnramifiedGalIntegerRingEquiv
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) :
    LubinTate.Valuations.exponentialValuationSubring vL ≃+*
      LubinTate.Valuations.exponentialValuationSubring vL := by
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  letI : Algebra V L := algVL
  letI : SMul V L := algVL.toSMul
  letI : Module V L := algVL.toModule
  letI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  letI : IsIntegralClosure W V L := by
    exact padicCyclotomicUnramified_isIntegralClosure_of_subring_eq V W hclosure
  have hmem (τ : Gal(L/K)) (x : W) : τ (x : L) ∈ W := by
    have hx : IsIntegral V (x : L) :=
      (IsIntegralClosure.isIntegral_iff
        (A := W) (R := V) (B := L)).2 ⟨x, rfl⟩
    have hτ : IsIntegral V (τ (x : L)) :=
      IsIntegral.map τ.toAlgHom hx
    rcases (IsIntegralClosure.isIntegral_iff
      (A := W) (R := V) (B := L)).1 hτ with ⟨y, hy⟩
    exact hy ▸ y.property
  exact
    { toFun := fun x ↦ ⟨σ (x : L), hmem σ x⟩
      invFun := fun x ↦ ⟨σ.symm (x : L), hmem σ.symm x⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp
      map_mul' := by intro x y; ext; simp
      map_add' := by intro x y; ext; simp }

@[simp]
theorem padicCyclotomicUnramified_galIntegerRingEquiv_apply
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) (x : LubinTate.Valuations.exponentialValuationSubring vL) :
    ((padicCyclotomicUnramifiedGalIntegerRingEquiv
      vK vL hExt hhens σ x : LubinTate.Valuations.exponentialValuationSubring vL) : L) =
      σ (x : L) :=
  rfl

/-- The residue field attached to an exponential valuation. -/
abbrev padicCyclotomicUnramifiedResidueField {F : Type*} [Field F]
    (vF : LubinTate.Valuations.ExponentialValuation F) :=
  IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring vF)

/-- The canonical residue-field algebra structure of a valuation extension. -/
@[reducible] noncomputable def padicCyclotomicUnramifiedResidueAlgebra
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    Algebra (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) := by
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  exact (IsLocalRing.ResidueField.map i).toAlgebra

/-- Finite-dimensionality of the residue extension, transported to the
module structure induced by `padicCyclotomicUnramifiedResidueAlgebra`. -/
theorem padicCyclotomicUnramified_residueFiniteDimensional
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    FiniteDimensional (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hfinite :
      @FiniteDimensional k ell _ _ residueModule :=
    residueExtension_finiteDimensional_of_finiteDimensional
      vK vL hExt
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @FiniteDimensional k ell _ _ algebraModule
  rw [← hmodule]
  exact hfinite

omit [FiniteDimensional K L] in
/-- The residue degree uses the quotient-induced module structure;
this identifies it with the finrank for `padicCyclotomicUnramifiedResidueAlgebra`. -/
theorem padicCyclotomicUnramified_exponentialResidueDegree_eq_finrank
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    exponentialResidueDegree vK vL hExt =
      Module.finrank (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := exponentialValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @Module.finrank k ell _ _ residueModule =
    @Module.finrank k ell _ _ algebraModule
  rw [hmodule]

/-- A ring equivalence of a local extension which fixes the base ring induces
an algebra equivalence of residue fields. -/
private theorem padicCyclotomicUnramified_residueMapEquiv_commutes
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (i : R →+* S) [IsLocalHom i] (e : S ≃+* S)
    (hfix : ∀ x : R, e (i x) = i x) :
    letI : Algebra (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) :=
      (IsLocalRing.ResidueField.map i).toAlgebra
    ∀ x : IsLocalRing.ResidueField R,
      IsLocalRing.ResidueField.mapEquiv e (algebraMap
          (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) x) =
        algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) x := by
  let : Algebra (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.ResidueField.mapEquiv e
      (IsLocalRing.ResidueField.map i (IsLocalRing.residue R y)) =
    IsLocalRing.ResidueField.map i (IsLocalRing.residue R y)
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue S) (hfix y)

/-- The canonical action of `Gal(L/K)` on the residue extension. -/
noncomputable def padicCyclotomicUnramifiedGalResidueAlgEquiv
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    padicCyclotomicUnramifiedResidueField vL ≃ₐ[padicCyclotomicUnramifiedResidueField vK]
      padicCyclotomicUnramifiedResidueField vL := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let eW := padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens σ
  let eell : ell ≃+* ell := IsLocalRing.ResidueField.mapEquiv eW
  apply AlgEquiv.ofRingEquiv
  apply padicCyclotomicUnramified_residueMapEquiv_commutes i eW
  intro y
  apply Subtype.ext
  change σ (algebraMap K L (y : K)) = algebraMap K L (y : K)
  exact σ.commutes (y : K)

@[simp]
theorem padicCyclotomicUnramified_galResidueAlgEquiv_residue
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (σ : Gal(L/K)) (x : LubinTate.Valuations.exponentialValuationSubring vL) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens σ
        (IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring vL) x) =
      IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring vL)
        (padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens σ x) := by
  simp only [padicCyclotomicUnramifiedGalResidueAlgEquiv,
    AlgEquiv.ofRingEquiv_apply,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rfl

/-- The canonical residue action as a group homomorphism. -/
noncomputable def padicCyclotomicUnramifiedGalToResidueGal
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Gal(L/K) →*
      Gal(padicCyclotomicUnramifiedResidueField vL/padicCyclotomicUnramifiedResidueField vK) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  refine
    { toFun := padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens
      map_one' := ?_
      map_mul' := ?_ }
  · ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens 1
        (IsLocalRing.residue W y) = IsLocalRing.residue W y
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    change IsLocalRing.residue W
        (padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens 1 y) =
      IsLocalRing.residue W y
    apply congrArg (IsLocalRing.residue W)
    apply Subtype.ext
    change (1 : Gal(L/K)) (y : L) = (y : L)
    rfl
  · intro σ τ
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens (σ * τ)
        (IsLocalRing.residue W y) =
      padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens σ
        (padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens τ
          (IsLocalRing.residue W y))
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    change IsLocalRing.residue W
        (padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens (σ * τ) y) = _
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue,
      padicCyclotomicUnramified_galResidueAlgEquiv_residue]
    apply congrArg (IsLocalRing.residue W)
    apply Subtype.ext
    change (σ * τ) (y : L) = σ (τ (y : L))
    rfl

end CanonicalResidueAction

/-- A field generated by a primitive root of unity is normal; together with
separability this gives the Galois input used in the unramified cyclotomic theorem(ii). -/
theorem padicCyclotomicUnramified_isGalois_of_primitiveRoot_adjoin_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L]
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    IsGalois K L := by
  let P : K[X] := X ^ n - C 1
  let : P.IsSplittingField K L :=
    { splits' := by
        simpa [P] using Polynomial.X_pow_sub_one_splits hζ
      adjoin_rootSet' := by
        apply top_unique
        rw [← hζgen]
        apply Algebra.adjoin_mono
        intro x hx
        have hxζ : x = ζ := by simpa using hx
        subst x
        rw [Polynomial.mem_rootSet]
        constructor
        · exact (Polynomial.monic_X_pow_sub_C (1 : K) hn.ne').ne_zero
        · rw [Polynomial.aeval_def, Polynomial.eval₂_sub,
            Polynomial.eval₂_pow, Polynomial.eval₂_X,
            Polynomial.eval₂_C]
          simp [hζ.pow_eq_one] }
  let : Normal K L := Normal.of_isSplittingField P
  exact IsGalois.mk

section FiniteResidueCyclotomic

variable {k : Type u} {Ω : Type v}
variable [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
variable {p r n : ℕ} [hp : Fact p.Prime]

private theorem padicCyclotomicUnramified_order_pos (hpn : p.Coprime n) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro hn
  have hnot : ¬p ∣ n := hp.out.coprime_iff_not_dvd.mp hpn
  exact hnot (hn ▸ dvd_zero p)

/-- Finite-field degree calculation underlying the unramified cyclotomic theorem(i).

If `k` has cardinality `p^r` and `ζ` is a primitive `n`-th root in an
extension field, then the simple residue extension `k(ζ)` has degree equal
to the order of `p^r` modulo `n`.  This is the irreducible-factor calculation
used after reducing the cyclotomic polynomial. -/
theorem padicCyclotomicUnramified_residue_adjoin_finrank
    (hk : Fintype.card k = p ^ r) (hpn : p.Coprime n)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank k (IntermediateField.adjoin k ({ζ} : Set Ω)) =
      padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) := by
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζint : IsIntegral k ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hdiv : minpoly k ζ ∣ cyclotomic n k := by
    apply minpoly.dvd k ζ
    simpa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using
      hζ.isRoot_cyclotomic hn
  rw [IntermediateField.adjoin.finrank hζint]
  exact
    Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
      (p := p) (f := r) hk hpn hdiv (minpoly.irreducible hζint)

omit hp in
/-- Arithmetic Frobenius on a finite residue extension acts by the `q`-th
power, with `q = p^r`.  This is the action asserted in the unramified cyclotomic theorem(ii). -/
theorem padicCyclotomicUnramified_residue_frobenius_apply
    {ell : Type v} [Field ell] [Algebra k ell]
    [Algebra.IsAlgebraic k ell]
    (hk : Fintype.card k = p ^ r) (x : ell) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k ell x = x ^ (p ^ r) := by
  change x ^ Fintype.card k = x ^ (p ^ r)
  rw [hk]

/-- For the residue cyclotomic field `k(ζ)`, arithmetic Frobenius generates
the full Galois group, and the number of powers needed is the least `f` from
the unramified cyclotomic theorem(i). -/
theorem padicCyclotomicUnramified_residue_adjoin_galois_generated_by_frobenius
    (hk : Fintype.card k = p ^ r) (hpn : p.Coprime n)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) :
    let ell := IntermediateField.adjoin k ({ζ} : Set Ω)
    let hζint : IsIntegral k ζ :=
      padicCyclotomicUnramified_primitiveRoot_isIntegral
        (padicCyclotomicUnramified_order_pos hpn) hζ
    letI : FiniteDimensional k ell :=
      IntermediateField.adjoin.finiteDimensional hζint
    letI : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
    letI : Finite ell := Module.finite_of_finite k
    let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k ell
    (∀ σ : Gal(ell/k),
        ∃ i < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r),
          φ ^ i = σ) ∧
      ∀ x : ell, φ x = x ^ (p ^ r) := by
  let ell := IntermediateField.adjoin k ({ζ} : Set Ω)
  have hζint : IsIntegral k ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral
      (padicCyclotomicUnramified_order_pos hpn) hζ
  let : FiniteDimensional k ell :=
    IntermediateField.adjoin.finiteDimensional hζint
  let : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  let : Finite ell := Module.finite_of_finite k
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k ell
  change
    (∀ σ : Gal(ell/k),
      ∃ i < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r),
        φ ^ i = σ) ∧
      ∀ x : ell, φ x = x ^ (p ^ r)
  constructor
  · intro σ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k ell).2 σ
    refine ⟨i, ?_, hi⟩
    rw [← padicCyclotomicUnramified_residue_adjoin_finrank hk hpn hζ]
    exact i.isLt
  · intro x
    exact padicCyclotomicUnramified_residue_frobenius_apply hk x

end FiniteResidueCyclotomic

section LocalCyclotomicUnramified

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- the unramified cyclotomic theorem(i), local Hensel step.

For a Henselian exponential valuation with finite residue field of cardinality
`p^r`, adjoining a primitive `n`-th root of unity, with `p` prime to `n`, is a
finite unramified extension in the literal sense of the finite unramified-extension definition.  The
primitive integral model used here is the cyclotomic polynomial itself; its
reduction is separable because `n` is nonzero in the residue field. -/
theorem padicCyclotomicUnramified_finiteUnramifiedExtension
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring vK))]
    (hk : Fintype.card (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring vK)) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    FiniteUnramifiedExtension vK vL hExt := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let k := IsLocalRing.ResidueField V
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let algVW : Algebra V W := i.toAlgebra
  let : Algebra V W := algVW
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hζIntegral : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegral
  let a : W := ⟨ζ, hζmem⟩
  let F : V[X] := cyclotomic n V
  have hFmonic : F.Monic := by
    exact Polynomial.cyclotomic.monic n V
  have hFroot :
      (F.map ((algebraMap K L).comp V.subtype)).eval (a : L) = 0 := by
    change Polynomial.eval ζ
      ((cyclotomic n V).map ((algebraMap K L).comp V.subtype)) = 0
    rw [map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  have hFreduction :
      (F.map (IsLocalRing.residue V)).Separable := by
    simpa [F, k] using Polynomial.separable_cyclotomic n k
  exact
    finiteUnramifiedExtension_of_primitive_separable_integral_model
      vK vL hExt hhens a F hFmonic hFroot hFreduction hζgen

/-- the unramified cyclotomic theorem(i), degree calculation upstairs.

The integral minimal polynomial of `ζ` has irreducible reduction by the
Hensel step of the factor-lifting criterion.  That reduction is an irreducible factor of
the `n`-th cyclotomic polynomial over the finite residue field, so all of its
irreducible factors have degree `ord_n(p^r)`. -/
theorem padicCyclotomicUnramified_finrank_eq_residueDegree
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring vK))]
    (hk : Fintype.card (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring vK)) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    Module.finrank K L =
      padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let k := IsLocalRing.ResidueField V
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : Module V L := algVL.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : IsFractionRing V K := by
    change IsFractionRing Vv K
    have hfr : IsFractionRing Vv.valuation.valuationSubring K :=
      (Valuation.valuationSubring.integers
        (v := Vv.valuation)).isFractionRing
    rw [Vv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsIntegrallyClosed V := by
    change IsIntegrallyClosed Vv
    infer_instance
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegralV : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζIntegralK : IsIntegral K ζ :=
    Algebra.IsIntegral.isIntegral (R := K) ζ
  let G : V[X] := minpoly V ζ
  let qbar : k[X] := G.map (IsLocalRing.residue V)
  have hGmonic : G.Monic := minpoly.monic hζIntegralV
  have hGfield : G.map (algebraMap V K) = minpoly K ζ := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K hζIntegralV).symm
  have hGirreducible : Irreducible (G.map (algebraMap V K)) := by
    rw [hGfield]
    exact minpoly.irreducible hζIntegralK
  have hGdvd : G ∣ cyclotomic n V := by
    apply minpoly.isIntegrallyClosed_dvd hζIntegralV
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change
      ((cyclotomic n V).map ((algebraMap K L).comp V.subtype)).eval ζ = 0
    rw [map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  have hqDvd : qbar ∣ cyclotomic n k := by
    rcases hGdvd with ⟨H, hH⟩
    refine ⟨H.map (IsLocalRing.residue V), ?_⟩
    rw [← map_cyclotomic n (IsLocalRing.residue V), hH,
      Polynomial.map_mul]
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  have hqSep : qbar.Separable :=
    (Polynomial.separable_cyclotomic n k).of_dvd hqDvd
  have hhensV : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Vv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Vv.valuation.valuationSubring at hhens
    rw [Vv.valuationSubring_valuation] at hhens
    exact hhens
  have hqIrreducible : Irreducible qbar :=
    irreducible_residue_of_irreducible_of_separable_of_henselian
      Vv hhensV hGmonic hGirreducible hqSep
  have hfieldDegree :
      Module.finrank K L = (minpoly K ζ).natDegree := by
    have hAdjoin :
        IntermediateField.adjoin K ({ζ} : Set L) =
          (⊤ : IntermediateField K L) :=
      (IntermediateField.adjoin_eq_top_iff).2 hζgen
    calc
      Module.finrank K L = Module.finrank K
          (IntermediateField.adjoin K ({ζ} : Set L)) := by
        rw [hAdjoin]
        simp
      _ = (minpoly K ζ).natDegree :=
        IntermediateField.adjoin.finrank hζIntegralK
  have hqDegree : qbar.natDegree = Module.finrank K L := by
    calc
      qbar.natDegree = G.natDegree :=
        hGmonic.natDegree_map (IsLocalRing.residue V)
      _ = (G.map (algebraMap V K)).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective
          (show Function.Injective (algebraMap V K) from
            IsFractionRing.injective V K)]
      _ = (minpoly K ζ).natDegree := by rw [hGfield]
      _ = Module.finrank K L := hfieldDegree.symm
  rw [← hqDegree]
  exact
    Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
      (p := p) (f := r) hk hpn hqDvd hqIrreducible

/-- The canonical reduction homomorphism on Galois groups is injective for
the prime-to-residue-characteristic cyclotomic extension.  If two
automorphisms have the same residue action, their images of `ζ` are simple
roots of the cyclotomic polynomial with the same residue, hence are equal by
Hensel uniqueness; `ζ` generates the field. -/
theorem padicCyclotomicUnramified_galToResidueGal_injective
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Function.Injective (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : Module V L := algVL.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegral : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegral
  let a : W := ⟨ζ, hζmem⟩
  let F : W[X] := cyclotomic n W
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  let : NeZero (n : ell) := by
    refine ⟨?_⟩
    intro hzero
    apply hnCast
    apply (algebraMap k ell).injective
    calc
      algebraMap k ell (n : k) = (n : ell) := map_natCast _ n
      _ = 0 := hzero
      _ = algebraMap k ell 0 := (map_zero _).symm
  intro σ τ hστ
  let bσ : W :=
    padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens σ a
  let bτ : W :=
    padicCyclotomicUnramifiedGalIntegerRingEquiv vK vL hExt hhens τ a
  have hresEq : IsLocalRing.residue W bσ = IsLocalRing.residue W bτ := by
    have happ := congrArg
      (fun g : Gal(ell/k) ↦ g (IsLocalRing.residue W a)) hστ
    change padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens σ
        (IsLocalRing.residue W a) =
      padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens τ
        (IsLocalRing.residue W a) at happ
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue,
      padicCyclotomicUnramified_galResidueAlgEquiv_residue] at happ
    exact happ
  have hσPrimitive : IsPrimitiveRoot (σ ζ) n :=
    hζ.map_of_injective σ.injective
  have hτPrimitive : IsPrimitiveRoot (τ ζ) n :=
    hζ.map_of_injective τ.injective
  have hσRoot : F.IsRoot bσ := by
    apply W.subtype_injective
    change W.subtype (F.eval bσ) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, bσ] using hσPrimitive.isRoot_cyclotomic hn
  have hτRoot : F.IsRoot bτ := by
    apply W.subtype_injective
    change W.subtype (F.eval bτ) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, bτ] using hτPrimitive.isRoot_cyclotomic hn
  have hτResidueRoot :
      (cyclotomic n ell).IsRoot (IsLocalRing.residue W bτ) := by
    have hmap := hτRoot.map (f := IsLocalRing.residue W)
    simpa [F] using hmap
  have hderivResidueNe :
      IsLocalRing.residue W (F.derivative.eval bτ) ≠ 0 := by
    have hsep := Polynomial.separable_cyclotomic n ell
    have hne :
        (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W bτ) ≠ 0 := by
      simpa [Polynomial.IsRoot.def] using
        hsep.eval₂_derivative_ne_zero (RingHom.id ell)
          (Polynomial.IsRoot.def.mp hτResidueRoot)
    have hcompat :
        IsLocalRing.residue W (F.derivative.eval bτ) =
          (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W bτ) := by
      calc
        IsLocalRing.residue W (F.derivative.eval bτ) =
            (F.derivative.map (IsLocalRing.residue W)).eval
              (IsLocalRing.residue W bτ) := by
          exact (Polynomial.eval_map_apply
            (f := IsLocalRing.residue W) (p := F.derivative) bτ).symm
        _ = (cyclotomic n ell).derivative.eval
              (IsLocalRing.residue W bτ) := by
          rw [← Polynomial.derivative_map, show
            F.map (IsLocalRing.residue W) =
              cyclotomic n (IsLocalRing.ResidueField W) by simp [F]]
    rw [hcompat]
    exact hne
  have hderivUnit : IsUnit (F.derivative.eval bτ) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hderivResidueNe
  have hbEq : bσ = bτ :=
    padicCyclotomicUnramified_eq_of_roots_of_residue_eq_of_derivative_isUnit
      hτRoot hσRoot hresEq hderivUnit
  have hζEq : σ ζ = τ ζ := by
    have hval := congrArg Subtype.val hbEq
    simpa [bσ, bτ] using hval
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set L) := by
    rw [hζgen]
    trivial
  exact Algebra.adjoin_induction
    (R := K) (A := L) (s := ({ζ} : Set L))
    (p := fun x _ ↦ σ x = τ x)
    (fun y hy ↦ by
      have hyζ : y = ζ := by simpa using hy
      subst y
      exact hζEq)
    (fun y ↦ by
      change σ (algebraMap K L y) = τ (algebraMap K L y)
      rw [σ.commutes, τ.commutes])
    (fun x y _ _ hx hy ↦ by
      rw [map_add, map_add, hx, hy])
    (fun x y _ _ hx hy ↦ by
      rw [map_mul, map_mul, hx, hy]) hx

/-- the unramified cyclotomic theorem(ii), canonical Galois comparison: the reduction
homomorphism is bijective.  Injectivity is the Hensel-uniqueness argument
above; surjectivity follows by comparing the two genuine Galois group
cardinalities with the equal field and residue degrees from part (i). -/
theorem padicCyclotomicUnramified_galToResidueGal_bijective
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Function.Bijective
      (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  let : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  let : Finite ell := Module.finite_of_finite k
  have hUnramified : FiniteUnramifiedExtension vK vL hExt :=
    padicCyclotomicUnramified_finiteUnramifiedExtension
      vK vL hExt hhens hk hpn hζ hζgen
  let : Algebra.IsSeparable K L :=
    finiteUnramifiedExtension_isSeparable_of_henselian
      vK vL hExt hhens hUnramified
  let : IsGalois K L :=
    padicCyclotomicUnramified_isGalois_of_primitiveRoot_adjoin_eq_top
      (padicCyclotomicUnramified_order_pos hpn) hζ hζgen
  let : IsGalois k ell := inferInstance
  let : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let : Fintype Gal(ell/k) := Fintype.ofFinite Gal(ell/k)
  apply (Fintype.bijective_iff_injective_and_card
    (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens)).2
  refine ⟨padicCyclotomicUnramified_galToResidueGal_injective
    vK vL hExt hhens hk hpn hζ hζgen, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
  exact hUnramified.2.trans
    (padicCyclotomicUnramified_exponentialResidueDegree_eq_finrank vK vL hExt)

/-- the unramified cyclotomic theorem(ii): the canonical multiplicative equivalence obtained
from reduction of valuation-ring automorphisms. -/
noncomputable def padicCyclotomicUnramifiedGalEquivResidueGal
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    Gal(L/K) ≃*
      Gal(padicCyclotomicUnramifiedResidueField vL/padicCyclotomicUnramifiedResidueField vK) := by
  letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) :=
    padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  exact MulEquiv.ofBijective
    (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens)
    (padicCyclotomicUnramified_galToResidueGal_bijective
      vK vL hExt hhens hk hpn hζ hζgen)

/-- The arithmetic Frobenius in `Gal(K(ζ)/K)`, defined canonically as the
inverse image of finite-field Frobenius under the reduction equivalence. -/
noncomputable def padicCyclotomicUnramifiedArithmeticFrobenius
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    Gal(L/K) := by
  let k := padicCyclotomicUnramifiedResidueField vK
  let ell := padicCyclotomicUnramifiedResidueField vL
  letI : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  letI : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  letI : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  exact
    (padicCyclotomicUnramifiedGalEquivResidueGal
      vK vL hExt hhens hk hpn hζ hζgen).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k ell)

@[simp]
theorem padicCyclotomicUnramified_galEquivResidueGal_arithmeticFrobenius
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    letI : FiniteDimensional (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
    letI : Algebra.IsAlgebraic (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      Algebra.IsAlgebraic.of_finite _ _
    padicCyclotomicUnramifiedGalEquivResidueGal
        vK vL hExt hhens hk hpn hζ hζgen
        (padicCyclotomicUnramifiedArithmeticFrobenius
          vK vL hExt hhens hk hpn hζ hζgen) =
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) := by
  simp [padicCyclotomicUnramifiedArithmeticFrobenius]

/-- the unramified cyclotomic theorem(ii): arithmetic Frobenius sends the chosen primitive
root to its `q = p^r` power.  Both sides are simple cyclotomic roots and their
residues agree by construction of Frobenius, so Hensel uniqueness identifies
them upstairs. -/
theorem padicCyclotomicUnramifiedArithmeticFrobenius_apply_primitiveRoot
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    padicCyclotomicUnramifiedArithmeticFrobenius
        vK vL hExt hhens hk hpn hζ hζgen ζ = ζ ^ (p ^ r) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  let : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : Module V L := algVL.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      vK vL hExt hhens
  have hclosure : W = (integralClosure V L).toSubring := by
    change Wv.toSubring = (integralClosure Vv L).toSubring
    exact hclosureVv
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegral : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegral
  let a : W := ⟨ζ, hζmem⟩
  let φ : Gal(L/K) :=
    padicCyclotomicUnramifiedArithmeticFrobenius
      vK vL hExt hhens hk hpn hζ hζgen
  let b : W := padicCyclotomicUnramifiedGalIntegerRingEquiv
    vK vL hExt hhens φ a
  let c : W := a ^ (p ^ r)
  let F : W[X] := cyclotomic n W
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCast : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCast⟩
  let : NeZero (n : ell) := by
    refine ⟨?_⟩
    intro hzero
    apply hnCast
    apply (algebraMap k ell).injective
    calc
      algebraMap k ell (n : k) = (n : ell) := map_natCast _ n
      _ = 0 := hzero
      _ = algebraMap k ell 0 := (map_zero _).symm
  have hφReduction :
      padicCyclotomicUnramifiedGalEquivResidueGal
          vK vL hExt hhens hk hpn hζ hζgen φ =
        FiniteField.frobeniusAlgEquivOfAlgebraic k ell := by
    exact padicCyclotomicUnramified_galEquivResidueGal_arithmeticFrobenius
      vK vL hExt hhens hk hpn hζ hζgen
  have hresEq : IsLocalRing.residue W b = IsLocalRing.residue W c := by
    have happ := congrArg (fun g : Gal(ell/k) ↦
      g (IsLocalRing.residue W a)) hφReduction
    change padicCyclotomicUnramifiedGalResidueAlgEquiv vK vL hExt hhens φ
        (IsLocalRing.residue W a) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k ell
        (IsLocalRing.residue W a) at happ
    rw [padicCyclotomicUnramified_galResidueAlgEquiv_residue] at happ
    calc
      IsLocalRing.residue W b =
          FiniteField.frobeniusAlgEquivOfAlgebraic k ell
            (IsLocalRing.residue W a) := happ
      _ = (IsLocalRing.residue W a) ^ (p ^ r) :=
        padicCyclotomicUnramified_residue_frobenius_apply hk _
      _ = IsLocalRing.residue W c := by simp [c]
  have hφPrimitive : IsPrimitiveRoot (φ ζ) n :=
    hζ.map_of_injective φ.injective
  have hcPrimitive : IsPrimitiveRoot (ζ ^ (p ^ r)) n :=
    hζ.pow_of_coprime (p ^ r) (hpn.pow_left r)
  have hbRoot : F.IsRoot b := by
    apply W.subtype_injective
    change W.subtype (F.eval b) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, b] using hφPrimitive.isRoot_cyclotomic hn
  have hcRoot : F.IsRoot c := by
    apply W.subtype_injective
    change W.subtype (F.eval c) = W.subtype 0
    rw [← Polynomial.eval_map_apply]
    simpa [F, c, a] using hcPrimitive.isRoot_cyclotomic hn
  have hcResidueRoot :
      (cyclotomic n ell).IsRoot (IsLocalRing.residue W c) := by
    have hmap := hcRoot.map (f := IsLocalRing.residue W)
    simpa [F] using hmap
  have hderivResidueNe :
      IsLocalRing.residue W (F.derivative.eval c) ≠ 0 := by
    have hsep := Polynomial.separable_cyclotomic n ell
    have hne :
        (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W c) ≠ 0 := by
      simpa [Polynomial.IsRoot.def] using
        hsep.eval₂_derivative_ne_zero (RingHom.id ell)
          (Polynomial.IsRoot.def.mp hcResidueRoot)
    have hcompat :
        IsLocalRing.residue W (F.derivative.eval c) =
          (cyclotomic n ell).derivative.eval
            (IsLocalRing.residue W c) := by
      calc
        IsLocalRing.residue W (F.derivative.eval c) =
            (F.derivative.map (IsLocalRing.residue W)).eval
              (IsLocalRing.residue W c) := by
          exact (Polynomial.eval_map_apply
            (f := IsLocalRing.residue W) (p := F.derivative) c).symm
        _ = (cyclotomic n ell).derivative.eval
              (IsLocalRing.residue W c) := by
          rw [← Polynomial.derivative_map, show
            F.map (IsLocalRing.residue W) =
              cyclotomic n (IsLocalRing.ResidueField W) by simp [F]]
    rw [hcompat]
    exact hne
  have hderivUnit : IsUnit (F.derivative.eval c) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hderivResidueNe
  have hbc : b = c :=
    padicCyclotomicUnramified_eq_of_roots_of_residue_eq_of_derivative_isUnit
      hcRoot hbRoot hresEq hderivUnit
  have hval := congrArg Subtype.val hbc
  simpa [b, c, a, φ] using hval

/-- the unramified cyclotomic theorem(ii): arithmetic Frobenius generates the whole Galois
group, with exponents bounded by the degree `f = ord_n(p^r)`. -/
theorem padicCyclotomicUnramifiedArithmeticFrobenius_generates
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    ∀ σ : Gal(L/K),
      ∃ j < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r),
        padicCyclotomicUnramifiedArithmeticFrobenius
            vK vL hExt hhens hk hpn hζ hζgen ^ j = σ := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  let : FiniteDimensional k ell :=
    padicCyclotomicUnramified_residueFiniteDimensional vK vL hExt
  let : Algebra.IsAlgebraic k ell := Algebra.IsAlgebraic.of_finite k ell
  let : Finite ell := Module.finite_of_finite k
  let e := padicCyclotomicUnramifiedGalEquivResidueGal
    vK vL hExt hhens hk hpn hζ hζgen
  let φ := padicCyclotomicUnramifiedArithmeticFrobenius
    vK vL hExt hhens hk hpn hζ hζgen
  have heφ : e φ = FiniteField.frobeniusAlgEquivOfAlgebraic k ell :=
    padicCyclotomicUnramified_galEquivResidueGal_arithmeticFrobenius
      vK vL hExt hhens hk hpn hζ hζgen
  have hUnramified : FiniteUnramifiedExtension vK vL hExt :=
    padicCyclotomicUnramified_finiteUnramifiedExtension
      vK vL hExt hhens hk hpn hζ hζgen
  have hfieldDegree :
      Module.finrank K L =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) :=
    padicCyclotomicUnramified_finrank_eq_residueDegree
      vK hhens hk hpn hζ hζgen
  have hresidueDegree :
      Module.finrank k ell =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) := by
    have hdegree : Module.finrank K L = Module.finrank k ell :=
      hUnramified.2.trans
        (padicCyclotomicUnramified_exponentialResidueDegree_eq_finrank vK vL hExt)
    rw [← hdegree]
    exact hfieldDegree
  intro σ
  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k ell).2 (e σ)
  refine ⟨j, ?_, ?_⟩
  · rw [← hresidueDegree]
    exact j.isLt
  · apply e.injective
    rw [map_pow, heφ]
    exact hj

/-- Nakayama lifts generation modulo the maximal ideal to a finite algebra. -/
private theorem subalgebra_eq_top_of_residue_approximation
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] (A : Subalgebra R S)
    (hmap : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S)
    (hcongr : ∀ b : S, ∃ z : S, z ∈ A ∧ b - z ∈ IsLocalRing.maximalIdeal S) :
    A = ⊤ := by
  have htop : (⊤ : Submodule R S) ≤
      A.toSubmodule ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R S) := by
    intro b _
    obtain ⟨z, hz, hdiff⟩ := hcongr b
    have hdiffMap : b - z ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
      simpa only [hmap] using hdiff
    have hdiffSmul : b - z ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R S) := by
      simpa [Ideal.smul_top_eq_map] using hdiffMap
    have hsum : z + (b - z) ∈
        A.toSubmodule ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R S) :=
      Submodule.add_mem_sup hz hdiffSmul
    have hsum_eq : z + (b - z) = b := by ring
    simpa only [hsum_eq] using hsum
  have hle : (⊤ : Submodule R S) ≤ A.toSubmodule :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal R) (N := A.toSubmodule)
      (N' := (⊤ : Submodule R S)) Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)) htop
  exact Algebra.toSubmodule_eq_top.mp (le_antisymm le_top hle)

/-- A primitive root whose residue degree exhausts a finite extension generates its algebra. -/
private theorem primitive_root_adjoin_eq_top_of_degree
    {A B : Type*} [Field A] [Fintype A] [Field B] [Algebra A B]
    [FiniteDimensional A B] {p r n : ℕ} [Fact p.Prime]
    (hk : Fintype.card A = p ^ r) (hpn : p.Coprime n)
    (alpha : B) (ha : IsPrimitiveRoot alpha n)
    (hdegree : Module.finrank A B =
      padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r)) :
    Algebra.adjoin A ({alpha} : Set B) = ⊤ := by
  have hsub := padicCyclotomicUnramified_residue_adjoin_finrank hk hpn ha
  have htop : IntermediateField.adjoin A ({alpha} : Set B) = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by
      simpa using hsub.trans hdegree.symm)
  exact Algebra.adjoin_eq_top_of_primitive_element
    (Algebra.IsAlgebraic.isAlgebraic alpha) htop

omit [FiniteDimensional K L] in
/-- Extending a discrete exponential valuation gives a valuation ring that is not a field. -/
private theorem exponential_extension_valuationRing_not_isField
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hvdisc : LubinTate.Valuations.DiscreteExponentialValuation vK) :
    ¬ IsField (LubinTate.Valuations.exponentialValuationSubring vL) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  intro hfield
  let : Field W := hfield.toField
  obtain ⟨s, hs, _hvalues, pi, hpival⟩ := hvdisc
  have hpi0 : pi ≠ 0 :=
    LubinTate.Valuations.discretePrimeElement_ne_zero_of_value vK hpival
  let piV : V :=
    LubinTate.Valuations.discretePrimeElementInValuationSubring vK hs.le hpival
  have hpiV0 : piV ≠ 0 := by
    intro hzero
    exact hpi0 (congrArg Subtype.val hzero)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap K L).injective (congrArg Subtype.val hxy)
  have hiPi0 : i piV ≠ 0 := by simpa using hi.ne hpiV0
  have hiPiUnit : IsUnit (i piV) := isUnit_iff_ne_zero.mpr hiPi0
  have hzero :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit vL hiPiUnit
  have hvalue : vL ((((i piV : W)) : L)) = (s : WithTop ℝ) := by
    change vL (algebraMap K L pi) = (s : WithTop ℝ)
    rw [hExt, hpival]
  rw [hvalue] at hzero
  have hs0 : s = 0 :=
    WithTop.coe_eq_coe.mp (by simpa using hzero)
  exact (ne_of_gt hs) hs0

/-- the unramified cyclotomic theorem(iii), valuation-ring generation by the specified root.

The residue of `ζ` is again primitive of order `n`; its residue-field degree
equals the full residue degree by part (i).  Thus it generates the residue
extension.  Since the extension is unramified, the source maximal ideal maps
onto the target maximal ideal, and Nakayama applied to the finite integral
closure proves `O_L = O_K[ζ]`. -/
theorem padicCyclotomicUnramified_valuationSubring_adjoin_eq_top
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hvdisc : LubinTate.Valuations.DiscreteExponentialValuation vK)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring vK))]
    (hk : Fintype.card (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring vK)) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    let V := LubinTate.Valuations.exponentialValuationSubring vK
    let W := LubinTate.Valuations.exponentialValuationSubring vL
    let i := unramifiedValuationRingValuationRingMap vK vL hExt
    letI : Algebra V W := i.toAlgebra
    ∃ a : W, (a : L) = ζ ∧
      Algebra.adjoin V ({a} : Set W) = (⊤ : Subalgebra V W) := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let algVW : Algebra V W := i.toAlgebra
  let : Algebra V W := algVW
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : SMul V W := algVW.toSMul
  let : Module V L := algVL.toModule
  let : Module V W := algVW.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := W) (A := L) (by intro; rfl)
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : IsFractionRing V K :=
    inferInstanceAs (IsFractionRing Vv K)
  have hclosure : W = (integralClosure V L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian vK vL hExt hhens
  let : IsIntegralClosure W V L :=
    padicCyclotomicUnramified_isIntegralClosure_of_subring_eq V W hclosure
  let : IsDiscreteValuationRing V :=
    LubinTate.Valuations.discreteExponentialValuationSubring_isDiscreteValuationRing hvdisc
  let : IsFractionRing W L :=
    inferInstanceAs (IsFractionRing Wv L)
  have hUnramified : FiniteUnramifiedExtension vK vL hExt :=
    padicCyclotomicUnramified_finiteUnramifiedExtension
      vK vL hExt hhens hk hpn hζ hζgen
  let : Algebra.IsSeparable K L :=
    finiteUnramifiedExtension_isSeparable_of_henselian
      vK vL hExt hhens hUnramified
  let : IsDedekindDomain V := inferInstance
  let : Module.Finite V W := IsIntegralClosure.finite V K L W
  let : IsDedekindDomain W :=
    IsIntegralClosure.isDedekindDomain V K L W
  have hWnotField : ¬ IsField W :=
    exponential_extension_valuationRing_not_isField vK vL hExt hvdisc
  let : IsNoetherianRing W := inferInstance
  let : IsDiscreteValuationRing W :=
    ((IsDiscreteValuationRing.TFAE W hWnotField).out 3 1).mp
      (show IsDedekindDomain W from inferInstance)
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  have hresfin : FiniteDimensional k ell :=
    residueExtension_finiteDimensional_of_finiteDimensional
      vK vL hExt
  let : FiniteDimensional k ell := hresfin
  let residueModule : Module k ell := inferInstance
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  have hresidueModule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hresfinAlgebra :
      @FiniteDimensional k ell _ _ algebraModule := by
    rw [← hresidueModule]
    exact hresfin
  let : Algebra.IsAlgebraic k ell :=
    @Algebra.IsAlgebraic.of_finite k ell _ _ _ _ hresfinAlgebra
  have hn : 0 < n := padicCyclotomicUnramified_order_pos hpn
  have hζIntegralV : IsIntegral V ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  have hζmem : ζ ∈ W := by
    rw [hclosure]
    exact hζIntegralV
  let a : W := ⟨ζ, hζmem⟩
  let alpha : ell := IsLocalRing.residue W a
  let F : V[X] := cyclotomic n V
  have hFaW : Polynomial.aeval a F = 0 := by
    apply W.subtype_injective
    have hcompat :
        (algebraMap V L).comp (RingHom.id V) =
          W.subtype.comp (algebraMap V W) := by
      ext x
      rfl
    have hmap := Polynomial.map_aeval_eq_aeval_map hcompat F a
    have hroot : Polynomial.aeval ζ F = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      change ((cyclotomic n V).map
        ((algebraMap K L).comp V.subtype)).eval ζ = 0
      rw [map_cyclotomic]
      exact hζ.isRoot_cyclotomic hn
    change W.subtype (Polynomial.aeval a F) = W.subtype 0
    rw [hmap]
    simpa [F] using hroot
  let : CharP k p := charP_of_card_eq_prime_pow hk
  have hnCastK : (n : k) ≠ 0 := by
    intro hzero
    exact (hp.out.coprime_iff_not_dvd.mp hpn)
      ((CharP.cast_eq_zero_iff k p n).mp hzero)
  let : NeZero (n : k) := ⟨hnCastK⟩
  let : NeZero (n : ell) := ⟨fun hzero => hnCastK
    ((algebraMap k ell).injective
      ((_root_.map_natCast _ n).trans (hzero.trans (_root_.map_zero _).symm)))⟩
  have halphaRoot : IsRoot (cyclotomic n ell) alpha := by
    have hres :=
      unramifiedValuationRing_polynomial_aeval_residue_eq
        vK vL hExt F a
    dsimp only at hres
    rw [hFaW, map_zero] at hres
    have hmapF : F.map (IsLocalRing.residue V) = cyclotomic n k := by
      change F.map (IsLocalRing.residue V) =
        cyclotomic n (IsLocalRing.ResidueField V)
      simp [F]
    rw [hmapF] at hres
    change 0 = ((cyclotomic n k).map (algebraMap k ell)).eval alpha at hres
    rw [map_cyclotomic] at hres
    exact hres.symm
  have halphaPrimitive : IsPrimitiveRoot alpha n :=
    (Polynomial.isRoot_cyclotomic_iff (R := ell)).1 halphaRoot
  have hfieldDegree :
      Module.finrank K L =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) :=
    padicCyclotomicUnramified_finrank_eq_residueDegree
      vK hhens hk hpn hζ hζgen
  have hfullResidueDegreeAlgebra :
      @Module.finrank k ell _ _ algebraModule =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) := by
    rw [← hresidueModule]
    exact hUnramified.2.symm.trans hfieldDegree
  have halphaAlgTop : Algebra.adjoin k ({alpha} : Set ell) = ⊤ :=
    @primitive_root_adjoin_eq_top_of_degree k ell _ _ _ _ hresfinAlgebra
      p r n hp hk hpn alpha halphaPrimitive hfullResidueDegreeAlgebra
  have hIdentity :=
    ramificationInvariants_fundamental_identity_of_discrete_of_separable
      vK vL hExt hvdisc hhens
  have hresiduePos : 0 < exponentialResidueDegree vK vL hExt := by
    exact exponentialResidueDegree_pos_of_finiteDimensional vK vL hExt
  have hRamification : exponentialRamificationIndex vK vL = 1 := by
    have hdegree := hUnramified.2
    nlinarith
  have hidealRamification :
      Ideal.ramificationIdx'
          (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) = 1 := by
    have heq :=
      exponentialRamificationIndex_eq_ideal_ramificationIdx
        vK vL hExt hvdisc
    change exponentialRamificationIndex vK vL =
      Ideal.ramificationIdx'
        (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) at heq
    rw [← heq]
    exact hRamification
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap K L).injective (congrArg Subtype.val hxy)
  have hmapMaximal :
      Ideal.map i (IsLocalRing.maximalIdeal V) =
        IsLocalRing.maximalIdeal W := by
    have hmap :=
      ValuationTheory.map_maximalIdeal_eq_pow_ramificationIdx hi
    rw [hidealRamification, pow_one] at hmap
    exact hmap
  let A : Subalgebra V W := Algebra.adjoin V ({a} : Set W)
  have hcongr : ∀ b : W, ∃ z : W,
      z ∈ A ∧ b - z ∈ IsLocalRing.maximalIdeal W := by
    intro b
    have hbmem : IsLocalRing.residue W b ∈
        Algebra.adjoin k ({alpha} : Set ell) := by
      simp [halphaAlgTop]
    rcases Algebra.adjoin_mem_exists_aeval k alpha hbmem with
      ⟨fbar, hfbar⟩
    have hresSurj : Function.Surjective (IsLocalRing.residue V) :=
      Ideal.Quotient.mk_surjective
    rcases Polynomial.map_surjective
        (IsLocalRing.residue V) hresSurj fbar with ⟨P, hP⟩
    let z : W := Polynomial.aeval a P
    refine ⟨z, ?_, ?_⟩
    · exact Polynomial.aeval_mem_adjoin_singleton
        (R := V) (p := P) a
    · rw [← IsLocalRing.residue_eq_zero_iff]
      rw [map_sub]
      have hres :=
        unramifiedValuationRing_polynomial_aeval_residue_eq
          vK vL hExt P a
      dsimp only at hres
      change IsLocalRing.residue W z = _ at hres
      rw [hres, hP]
      rw [sub_eq_zero]
      simpa [alpha, Polynomial.aeval_def] using hfbar.symm
  refine ⟨a, rfl, ?_⟩
  exact subalgebra_eq_top_of_residue_approximation A hmapMaximal hcongr

/-- Finite-dimensional core of the complete the unramified cyclotomic theorem endpoint.
The public endpoint below derives finite-dimensionality from `L = K(ζ)`. -/
private theorem padicCyclotomicUnramified_of_finiteDimensional
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hvdisc : LubinTate.Valuations.DiscreteExponentialValuation vK)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    let V := LubinTate.Valuations.exponentialValuationSubring vK
    let W := LubinTate.Valuations.exponentialValuationSubring vL
    let i := unramifiedValuationRingValuationRingMap vK vL hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
    letI : Algebra V W := i.toAlgebra
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    FiniteUnramifiedExtension vK vL hExt ∧
      Module.finrank K L =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ∧
      (0 < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ∧
        (p ^ r) ^ padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ≡
          1 [MOD n] ∧
        ∀ m : ℕ, 0 < m → (p ^ r) ^ m ≡ 1 [MOD n] →
          padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ≤ m) ∧
      Function.Bijective
        (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens) ∧
      padicCyclotomicUnramifiedArithmeticFrobenius
          vK vL hExt hhens hk hpn hζ hζgen ζ = ζ ^ (p ^ r) ∧
      (∀ σ : Gal(L/K),
        ∃ j < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r),
          padicCyclotomicUnramifiedArithmeticFrobenius
              vK vL hExt hhens hk hpn hζ hζgen ^ j = σ) ∧
      ∃ a : W, (a : L) = ζ ∧
        Algebra.adjoin V ({a} : Set W) = (⊤ : Subalgebra V W) := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let i := unramifiedValuationRingValuationRingMap vK vL hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (padicCyclotomicUnramifiedResidueField vK)
      (padicCyclotomicUnramifiedResidueField vL) :=
    padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact padicCyclotomicUnramified_finiteUnramifiedExtension
      vK vL hExt hhens hk hpn hζ hζgen
  · exact padicCyclotomicUnramified_finrank_eq_residueDegree
      vK hhens hk hpn hζ hζgen
  · exact padicCyclotomicUnramifiedResidueDegree_isLeast
      n (p ^ r) (hpn.pow_left r)
  · exact padicCyclotomicUnramified_galToResidueGal_bijective
      vK vL hExt hhens hk hpn hζ hζgen
  · exact padicCyclotomicUnramifiedArithmeticFrobenius_apply_primitiveRoot
      vK vL hExt hhens hk hpn hζ hζgen
  · exact padicCyclotomicUnramifiedArithmeticFrobenius_generates
      vK vL hExt hhens hk hpn hζ hζgen
  · exact padicCyclotomicUnramified_valuationSubring_adjoin_eq_top
      vK vL hExt hvdisc hhens hk hpn hζ hζgen

end LocalCyclotomicUnramified

section LocalCyclotomicEndpoint

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A field generated by one integral element is finite-dimensional.  This
removes the redundant finite-dimensionality assumption from the literal
the unramified cyclotomic theorem endpoint. -/
private theorem padicCyclotomicUnramified_finiteDimensional_of_primitiveRoot_adjoin_eq_top
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    FiniteDimensional K L := by
  have hζIntegral : IsIntegral K ζ :=
    padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ
  let E := IntermediateField.adjoin K ({ζ} : Set L)
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hζIntegral
  have hAlgebraAdjoinLe :
      Algebra.adjoin K ({ζ} : Set L) ≤ E.toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    exact IntermediateField.subset_adjoin K ({ζ} : Set L) hx
  have htop : E = (⊤ : IntermediateField K L) := by
    apply top_unique
    intro x _hx
    exact hAlgebraAdjoinLe (hζgen.symm ▸ trivial)
  let : FiniteDimensional K (⊤ : IntermediateField K L) :=
    htop ▸ inferInstance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Complete arithmetic-Frobenius endpoint for the unramified cyclotomic extension.

For the extension generated by a primitive prime-to-`p` root of unity, this
packages: finite unramifiedness and the least-exponent degree formula; the
canonical Galois/residue-Galois comparison and its arithmetic Frobenius
generator; and `O_L = O_K[ζ]` for the specified `ζ`.  No separate
finite-dimensionality hypothesis is needed: it follows from `L = K(ζ)`. -/
theorem padicCyclotomicUnramified
    (vK : LubinTate.Valuations.ExponentialValuation K) (vL :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ x : K, vL (algebraMap K L x) = vK x)
    (hvdisc : LubinTate.Valuations.DiscreteExponentialValuation vK)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    {p r n : ℕ} [hp : Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField vK)]
    (hk : Fintype.card (padicCyclotomicUnramifiedResidueField vK) = p ^ r)
    (hpn : p.Coprime n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hζgen : Algebra.adjoin K ({ζ} : Set L) = ⊤) :
    letI : FiniteDimensional K L :=
      padicCyclotomicUnramified_finiteDimensional_of_primitiveRoot_adjoin_eq_top
        (padicCyclotomicUnramified_order_pos hpn) hζ hζgen
    let V := LubinTate.Valuations.exponentialValuationSubring vK
    let W := LubinTate.Valuations.exponentialValuationSubring vL
    let i := unramifiedValuationRingValuationRingMap vK vL hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
    letI : Algebra V W := i.toAlgebra
    letI : Algebra (padicCyclotomicUnramifiedResidueField vK)
        (padicCyclotomicUnramifiedResidueField vL) :=
      padicCyclotomicUnramifiedResidueAlgebra vK vL hExt
    FiniteUnramifiedExtension vK vL hExt ∧
      Module.finrank K L =
        padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ∧
      (0 < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ∧
        (p ^ r) ^ padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ≡
          1 [MOD n] ∧
        ∀ m : ℕ, 0 < m → (p ^ r) ^ m ≡ 1 [MOD n] →
          padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r) ≤ m) ∧
      Function.Bijective
        (padicCyclotomicUnramifiedGalToResidueGal vK vL hExt hhens) ∧
      padicCyclotomicUnramifiedArithmeticFrobenius
          vK vL hExt hhens hk hpn hζ hζgen ζ = ζ ^ (p ^ r) ∧
      (∀ σ : Gal(L/K),
        ∃ j < padicCyclotomicUnramifiedResidueDegree n (p ^ r) (hpn.pow_left r),
          padicCyclotomicUnramifiedArithmeticFrobenius
              vK vL hExt hhens hk hpn hζ hζgen ^ j = σ) ∧
      ∃ a : W, (a : L) = ζ ∧
        Algebra.adjoin V ({a} : Set W) = (⊤ : Subalgebra V W) := by
  let : FiniteDimensional K L :=
    padicCyclotomicUnramified_finiteDimensional_of_primitiveRoot_adjoin_eq_top
      (padicCyclotomicUnramified_order_pos hpn) hζ hζgen
  exact padicCyclotomicUnramified_of_finiteDimensional
    vK vL hExt hvdisc hhens hk hpn hζ hζgen

end LocalCyclotomicEndpoint

section IntegralInclusion

variable {R : Type u} {L : Type v}
variable [CommRing R] [Field L] [Algebra R L]

/-- The easy inclusion in the unramified cyclotomic theorem(iii): every root of unity is
integral, hence the algebra generated by a primitive root lies in the integral
closure.  The reverse inclusion for the local cyclotomic setting is proved by
`padicCyclotomicUnramified_valuationSubring_adjoin_eq_top` above. -/
theorem padicCyclotomicUnramified_adjoin_le_integralClosure
    {n : ℕ} {ζ : L} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Algebra.adjoin R ({ζ} : Set L) ≤ integralClosure R L := by
  exact adjoin_le_integralClosure
    (padicCyclotomicUnramified_primitiveRoot_isIntegral hn hζ)

end IntegralInclusion

end Valuations
end AlgebraicNumberTheory

end
