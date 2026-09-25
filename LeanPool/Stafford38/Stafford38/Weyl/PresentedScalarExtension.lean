/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence
public import LeanPool.Stafford38.Stafford38.Weyl.Universal
public import LeanPool.Stafford38.Stafford38.Weyl.PBW
public import LeanPool.Stafford38.Stafford38.Weyl.Filtration
public import LeanPool.Stafford38.Stafford38.Weyl.LeadingSymbol
public import LeanPool.Stafford38.Stafford38.Weyl.PBWMonicBridge
public import LeanPool.Stafford38.Stafford38.Weyl.EulerResidue
public import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdeal
public import LeanPool.Stafford38.Stafford38.Characteristic.GeometricSupportDescent
public import LeanPool.Stafford38.Stafford38.UniversalAssembly
public import LeanPool.Stafford38.Stafford38.CanonicalSupportVanishingReduction


/-!
# Coefficient extension for the presented Weyl algebra

This file records the concrete map needed before any characteristic-support
descent can be attempted.  The source is the quotient presentation over `k`
and the target is the same presentation over an extension field `K`.  The map
is defined by the quotient universal property; in particular, no PBW
identification or base-change theorem is used in its definition.

The file also proves injectivity, PBW normal-form and filtration transport,
PBW monicity, canonical-right-ideal transport in the usable direction, and the
resulting source-to-target order-initial-ideal inclusion.  The reverse filtered
comparison is recorded as an explicit contract below and proved in
`FilteredScalarLifting.lean`; no base-change equality is treated as
definitional.
-/

@[expose] public section

namespace Stafford38.Weyl.PresentedScalarExtension

open Stafford
open AlgebraicAnalysis
open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylUniversal
open Stafford38.WeylEulerResidue
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.GeometricSupportDescent
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.EulerSurjectivity

noncomputable section

universe u v

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

private theorem algebraMap_matrixJ (n : Nat) (i j : Fin n ⊕ Fin n) :
    algebraMap k K (Matrix.J (Fin n) k i j) = Matrix.J (Fin n) K i j := by
  cases i with
  | inl i =>
      cases j with
      | inl j => by_cases h : i = j <;> simp [Matrix.J, h]
      | inr j => simp [Matrix.J, Matrix.one_apply]
  | inr i =>
      cases j with
      | inl j => simp [Matrix.J, Matrix.one_apply]
      | inr j => by_cases h : i = j <;> simp [Matrix.J, h]

private theorem presentedWeylScalarExtension_commutator (n : Nat)
    (i j : Fin n ⊕ Fin n) :
    commutator
        (freeWeylGenerator (Matrix.J (Fin n) K) i)
        (freeWeylGenerator (Matrix.J (Fin n) K) j) =
      algebraMap k (PresentedWeyl K n) (Matrix.J (Fin n) k i j) := by
  rw [freeWeylGenerator_commutator]
  rw [IsScalarTower.algebraMap_apply k K (PresentedWeyl K n)]
  rw [algebraMap_matrixJ]

/-- The coefficient-extension homomorphism on the quotient presentation. -/
def presentedWeylScalarExtension (n : Nat) :
    PresentedWeyl k n →ₐ[k] PresentedWeyl K n :=
  freeWeylLift (Matrix.J (Fin n) k)
    (fun i => freeWeylGenerator (Matrix.J (Fin n) K) i)
    (by exact presentedWeylScalarExtension_commutator n)

@[simp]
theorem presentedWeylScalarExtension_generator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    presentedWeylScalarExtension (k := k) (K := K) n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) =
      freeWeylGenerator (Matrix.J (Fin n) K) i := by
  exact freeWeylLift_generator (Matrix.J (Fin n) k)
    (fun i => freeWeylGenerator (Matrix.J (Fin n) K) i)
    (presentedWeylScalarExtension_commutator n) i

theorem presentedWeylScalarExtension_scalar (n : Nat) (a : k) :
    presentedWeylScalarExtension (k := k) (K := K) n
        (algebraMap k (PresentedWeyl k n) a) =
      algebraMap k (PresentedWeyl K n) a := by
  exact (presentedWeylScalarExtension (k := k) (K := K) n).commutes a

theorem presentedWeylScalarExtension_map_mul (n : Nat)
    (a b : PresentedWeyl k n) :
    presentedWeylScalarExtension (k := k) (K := K) n (a * b) =
      presentedWeylScalarExtension (k := k) (K := K) n a *
        presentedWeylScalarExtension (k := k) (K := K) n b := by
  exact map_mul _ _ _

theorem presentedWeylScalarExtension_map_add (n : Nat)
    (a b : PresentedWeyl k n) :
    presentedWeylScalarExtension (k := k) (K := K) n (a + b) =
      presentedWeylScalarExtension (k := k) (K := K) n a +
        presentedWeylScalarExtension (k := k) (K := K) n b := by
  exact map_add _ _ _

theorem presentedWeylScalarExtension_commutes (n : Nat) (a : k) :
    presentedWeylScalarExtension (k := k) (K := K) n
        (algebraMap k (PresentedWeyl k n) a) =
      algebraMap k (PresentedWeyl K n) a := by
  exact (presentedWeylScalarExtension (k := k) (K := K) n).commutes a

/-! ## Compatibility with the recursive presentation -/

theorem presentedWeylScalarExtension_previous (n : Nat)
    (z : PresentedWeyl k n) :
    presentedWeylScalarExtension (k := k) (K := K) (n + 1)
        (previousWeylEmbedding k n z) =
      previousWeylEmbedding K n
        (presentedWeylScalarExtension (k := k) (K := K) n z) := by
  let f : PresentedWeyl k n →ₐ[k] PresentedWeyl K (n + 1) :=
    (presentedWeylScalarExtension (k := k) (K := K) (n + 1)).comp
      (previousWeylEmbedding k n)
  let g : PresentedWeyl k n →ₐ[k] PresentedWeyl K (n + 1) :=
    (previousWeylEmbedding K n).restrictScalars k |>.comp
      (presentedWeylScalarExtension (k := k) (K := K) n)
  have hfg : f = g := by
    apply freeWeyl_algHom_ext (k := k) (Matrix.J (Fin n) k) f g
    intro i
    simp [f, g, oldGenerator]
  exact DFunLike.congr_fun hfg z

theorem presentedWeylScalarExtension_orderedMonomial :
    ∀ (n : Nat) (a p : Fin n → ℕ),
      presentedWeylScalarExtension (k := k) (K := K) n
          (presentedOrderedMonomial k n a p) =
        presentedOrderedMonomial K n a p := by
  intro n
  induction n with
  | zero =>
      intro a p
      simp [presentedOrderedMonomial, presentedWeylScalarExtension]
  | succ n ih =>
      intro a p
      rw [presentedOrderedMonomial, map_mul, map_mul, map_pow, map_pow,
        presentedWeylScalarExtension_previous]
      rw [ih (fun i => a i.succ) (fun i => p i.succ)]
      simp [presentedOrderedMonomial, presentedCoordinate, presentedMomentum]

/-! ## The PBW-linear extension of coefficients -/

/-- Coefficient extension on the commutative symbol polynomial ring. -/
def symbolScalarExtension (n : Nat) :
    SymbolRing k n →ₐ[k] SymbolRing K n where
  toRingHom := MvPolynomial.map (algebraMap k K)
  commutes' := by
    intro a
    simp

@[simp]
theorem symbolScalarExtension_apply (n : Nat) (p : SymbolRing k n) :
    symbolScalarExtension (k := k) (K := K) n p =
      MvPolynomial.map (algebraMap k K) p :=
  rfl

theorem symbolScalarExtension_monomial (n : Nat)
    (m : PhaseVar n →₀ ℕ) (a : k) :
    symbolScalarExtension (k := k) (K := K) n
        (MvPolynomial.monomial m a) =
      MvPolynomial.monomial m (algebraMap k K a) := by
  simp [MvPolynomial.map_monomial]

/-- The `k`-linear map obtained by extending PBW coordinates and rebuilding in
the target presentation. -/
def pbwScalarLinearMap (n : Nat) :
    PresentedWeyl k n →ₗ[k] PresentedWeyl K n :=
  (presentedNormalFormLinearEquiv K n).symm.toLinearMap.restrictScalars k |>.comp
    ((symbolScalarExtension (k := k) (K := K) n).toLinearMap.comp
      (presentedNormalFormLinearEquiv k n).toLinearMap)

theorem pbwScalarLinearMap_basis (n : Nat)
    (m : PhaseVar n →₀ ℕ) :
    pbwScalarLinearMap (k := k) (K := K) n
        (presentedPBWBasis k n m) =
      presentedPBWBasis K n m := by
  simp only [pbwScalarLinearMap, LinearMap.comp_apply]
  change (presentedNormalFormLinearEquiv K n).symm
      (symbolScalarExtension (k := k) (K := K) n
        (presentedNormalFormLinearEquiv k n (presentedPBWBasis k n m))) =
    presentedPBWBasis K n m
  rw [presentedNormalFormLinearEquiv_basis,
    symbolScalarExtension_monomial]
  simp only [map_one]
  rw [← presentedNormalFormBasis_apply]
  rfl

@[simp]
theorem pbwScalarLinearMap_orderedMonomial (n : Nat)
    (m : PhaseVar n →₀ ℕ) :
    pbwScalarLinearMap (k := k) (K := K) n
        (presentedOrderedMonomial k n (fun i => m (.inl i)) (fun i => m (.inr i))) =
      presentedOrderedMonomial K n (fun i => m (.inl i)) (fun i => m (.inr i)) := by
  simpa only [presentedPBWBasis_apply] using pbwScalarLinearMap_basis (k := k) (K := K) n m

theorem presentedWeylScalarExtension_basis (n : Nat)
    (m : PhaseVar n →₀ ℕ) :
    presentedWeylScalarExtension (k := k) (K := K) n
        (presentedPBWBasis k n m) =
      presentedPBWBasis K n m := by
  rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
  exact presentedWeylScalarExtension_orderedMonomial n
    (fun i => m (.inl i)) (fun i => m (.inr i))

theorem presentedWeylScalarExtension_toLinearMap_eq_pbwScalarLinearMap
    (n : Nat) :
    (presentedWeylScalarExtension (k := k) (K := K) n).toLinearMap =
      pbwScalarLinearMap (k := k) (K := K) n := by
  apply Module.Basis.ext (presentedPBWBasis k n)
  intro m
  change presentedWeylScalarExtension (k := k) (K := K) n
      (presentedPBWBasis k n m) =
    pbwScalarLinearMap (k := k) (K := K) n
      (presentedPBWBasis k n m)
  rw [presentedWeylScalarExtension_basis, pbwScalarLinearMap_basis]

theorem presentedNormalFormLinearEquiv_scalarExtension (n : Nat)
    (z : PresentedWeyl k n) :
    presentedNormalFormLinearEquiv K n
        (presentedWeylScalarExtension (k := k) (K := K) n z) =
      symbolScalarExtension (k := k) (K := K) n
        (presentedNormalFormLinearEquiv k n z) := by
  have hmap := DFunLike.congr_fun
    (presentedWeylScalarExtension_toLinearMap_eq_pbwScalarLinearMap
      (k := k) (K := K) n) z
  change presentedWeylScalarExtension (k := k) (K := K) n z =
    pbwScalarLinearMap (k := k) (K := K) n z at hmap
  change presentedNormalFormLinearEquiv K n
      (presentedWeylScalarExtension (k := k) (K := K) n z) = _
  rw [hmap]
  simp [pbwScalarLinearMap, LinearMap.comp_apply]

/-! ## Injectivity and filtered transport -/

theorem symbolScalarExtension_injective (n : Nat) :
    Function.Injective (symbolScalarExtension (k := k) (K := K) n) := by
  exact MvPolynomial.map_injective (algebraMap k K)
    (FaithfulSMul.algebraMap_injective k K)

theorem presentedWeylScalarExtension_injective (n : Nat) :
    Function.Injective
      (presentedWeylScalarExtension (k := k) (K := K) n) := by
  intro a b hab
  have hnorm := congrArg (presentedNormalFormLinearEquiv K n) hab
  rw [presentedNormalFormLinearEquiv_scalarExtension,
    presentedNormalFormLinearEquiv_scalarExtension] at hnorm
  apply (presentedNormalFormLinearEquiv k n).injective
  exact (symbolScalarExtension_injective (k := k) (K := K) n) hnorm

theorem symbolScalarExtension_weightedHomogeneousComponent (n : Nat)
    (w : PhaseVar n → ℕ) (N : ℕ) (f : SymbolRing k n) :
    symbolScalarExtension (k := k) (K := K) n
        (MvPolynomial.weightedHomogeneousComponent w N f) =
      MvPolynomial.weightedHomogeneousComponent w N
        (symbolScalarExtension (k := k) (K := K) n f) := by
  classical
  ext m
  change (MvPolynomial.map (algebraMap k K)
        (MvPolynomial.weightedHomogeneousComponent w N f)).coeff m =
    (MvPolynomial.weightedHomogeneousComponent w N
        (MvPolynomial.map (algebraMap k K) f)).coeff m
  rw [MvPolynomial.coeff_map,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [finsupp_weight_eq_monomialWeight]
  by_cases hm : monomialWeight w m = N
  · simp? [hm]
    rw [MvPolynomial.coeff_map]
  · simp [hm]

theorem presentedWeylScalarExtension_mem_weightPiece (n : Nat)
    (w : PhaseVar n → ℕ) (N : ℕ) {z : PresentedWeyl k n}
    (hz : z ∈ presentedWeightPiece k w N) :
    presentedWeylScalarExtension (k := k) (K := K) n z ∈
      presentedWeightPiece K w N := by
  rw [mem_presentedWeightPiece] at hz ⊢
  rw [presentedNormalFormLinearEquiv_scalarExtension
    (k := k) (K := K) n z]
  intro m hm
  apply hz m
  intro hzero
  apply hm
  simp [MvPolynomial.coeff_map, hzero]

theorem presentedWeylScalarExtension_mem_orderPiece (n : Nat)
    (N : ℕ) {z : PresentedWeyl k n}
    (hz : z ∈ orderPiece k n N) :
    presentedWeylScalarExtension (k := k) (K := K) n z ∈
      orderPiece K n N := by
  exact presentedWeylScalarExtension_mem_weightPiece
    (k := k) (K := K) n (@orderWeight n) N hz

theorem presentedWeylScalarExtension_mem_bernsteinPiece (n : Nat)
    (N : ℕ) {z : PresentedWeyl k n}
    (hz : z ∈ bernsteinPiece k n N) :
    presentedWeylScalarExtension (k := k) (K := K) n z ∈
      bernsteinPiece K n N := by
  exact presentedWeylScalarExtension_mem_weightPiece
    (k := k) (K := K) n (@bernsteinWeight n) N hz

theorem presentedWeylScalarExtension_principalComponent (n : Nat)
    (w : PhaseVar n → ℕ) (N : ℕ) (z : PresentedWeyl k n) :
    symbolScalarExtension (k := k) (K := K) n
        (presentedPrincipalComponent k w N z) =
    presentedPrincipalComponent K w N
        (presentedWeylScalarExtension (k := k) (K := K) n z) := by
  change symbolScalarExtension (k := k) (K := K) n
      (MvPolynomial.weightedHomogeneousComponent w N
        (presentedNormalFormLinearEquiv k n z)) =
    MvPolynomial.weightedHomogeneousComponent w N
      (presentedNormalFormLinearEquiv K n
        (presentedWeylScalarExtension (k := k) (K := K) n z))
  rw [presentedNormalFormLinearEquiv_scalarExtension]
  exact symbolScalarExtension_weightedHomogeneousComponent
    (k := k) (K := K) n w N
      (presentedNormalFormLinearEquiv k n z)

theorem presentedWeylScalarExtension_isPBWMonicAt (n : Nat)
    (N : ℕ) {z : PresentedWeyl k (n + 1)}
    (hz : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N z) :
    IsPBWMonicAt K (.inr (0 : Fin (n + 1))) N
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) z) := by
  refine ⟨presentedWeylScalarExtension_mem_bernsteinPiece
    (k := k) (K := K) (n + 1) N hz.1, ?_⟩
  change (presentedNormalFormLinearEquiv K (n + 1)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) z)).coeff (Finsupp.single (.inr
          (0 : Fin (n + 1))) N) = 1
  have hnorm := presentedNormalFormLinearEquiv_scalarExtension
    (k := k) (K := K) (n + 1) z
  rw [hnorm]
  change (MvPolynomial.map (algebraMap k K)
        (presentedNormalFormLinearEquiv k (n + 1) z)).coeff (Finsupp.single (.inr (0 : Fin (n +
          1))) N) = 1
  rw [MvPolynomial.coeff_map]
  simp [hz.2]

@[simp]
theorem presentedWeylScalarExtension_coordinate (n : Nat) :
    presentedWeylScalarExtension (k := k) (K := K) (n + 1)
        (presentedCoordinate k n) = presentedCoordinate K n := by
  simp [presentedCoordinate]

@[simp]
theorem presentedWeylScalarExtension_momentum (n : Nat) :
    presentedWeylScalarExtension (k := k) (K := K) (n + 1)
        (presentedMomentum k n) = presentedMomentum K n := by
  simp [presentedMomentum]

theorem presentedWeylScalarExtension_mem_canonicalRightIdeal
    (n N : Nat) {d : PresentedWeyl k (n + 1)} {z : PresentedWeyl k (n + 1)}
    (hz : z ∈ canonicalRightIdeal (presentedCoordinate k n) d N) :
    presentedWeylScalarExtension (k := k) (K := K) (n + 1) z ∈
      canonicalRightIdeal (presentedCoordinate K n)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N := by
  let e := presentedWeylScalarExtension (k := k) (K := K) (n + 1)
  let J := canonicalRightIdeal (presentedCoordinate K n) (e d) N
  change e z ∈ J
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha
    · subst a
      exact firstGenerator_mem (presentedCoordinate K n) (e d) N
    · subst a
      simpa [e, J, map_mul, map_pow] using
        (secondGenerator_mem (presentedCoordinate K n) (e d) N)
  · simp [e, J]
  · intro a b _ _ ha hb
    simpa only [map_add] using J.add_mem ha hb
  · intro c a _ ha
    change e (a * c.unop) ∈ J
    rw [map_mul]
    change MulOpposite.op (e c.unop) • e a ∈ J
    exact J.smul_mem _ ha

/-! ## The safe initial-ideal comparison -/

/-- Every source order-initial generator maps to a target order-initial
generator.  This is the comparison needed for descent; it is intentionally a
one-way inclusion and makes no claim that the target initial ideal is the
extension of the source initial ideal. -/
theorem presentedWeylScalarExtension_map_orderInitialIdeal_le
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
    (orderInitialIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)).map
        (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom ≤
      orderInitialIdeal K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro P hP
  rcases hP with ⟨L, z, hz, hI, rfl⟩
  apply Ideal.subset_span
  refine ⟨L,
    presentedWeylScalarExtension (k := k) (K := K) (n + 1) z, ?_, ?_, ?_⟩
  · exact presentedWeylScalarExtension_mem_orderPiece
      (k := k) (K := K) (n + 1) L hz
  · exact presentedWeylScalarExtension_mem_canonicalRightIdeal
      (k := k) (K := K) n N hI
  · exact presentedWeylScalarExtension_principalComponent
      (k := k) (K := K) (n + 1) orderWeight L z

theorem target_orderCharacteristicSupport_subset_scalarExtended_zeroLocus
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
    orderCharacteristicSupport K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) ⊆
      PrimeSpectrum.zeroLocus
        ((orderInitialIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)).map
          (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom) := by
  rw [orderCharacteristicSupport_eq_zeroLocus]
  exact PrimeSpectrum.zeroLocus_anti_mono_ideal
    (presentedWeylScalarExtension_map_orderInitialIdeal_le
      (k := k) (K := K) n N d)

/-! ## PBW spanning after scalar extension -/

/-- The `K`-linear span of the image of the quotient-presented scalar map. -/
def scalarImageSpan (n : Nat) :
    Submodule K (PresentedWeyl K n) :=
  Submodule.span K (Set.range
    (presentedWeylScalarExtension (k := k) (K := K) n))

theorem target_mem_scalarImageSpan (n : Nat) (z : PresentedWeyl K n) :
    z ∈ scalarImageSpan (k := k) (K := K) n := by
  let f := presentedNormalFormLinearEquiv K n z
  have hreconstruct :
      z = ∑ m ∈ f.support,
        f.coeff m • presentedPBWBasis K n m := by
    apply (presentedNormalFormLinearEquiv K n).injective
    simp only [map_sum, map_smul, presentedNormalFormLinearEquiv_basis]
    change f = _
    calc
      f = ∑ m ∈ f.support,
          MvPolynomial.monomial m (f.coeff m) :=
        MvPolynomial.as_sum f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [MvPolynomial.smul_monomial]
        simp
  rw [hreconstruct]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨presentedPBWBasis k n m,
    presentedWeylScalarExtension_basis (k := k) (K := K) n m⟩

/-- The `K`-linear span of the scalar extensions of a source right ideal. -/
def scalarImageRightIdealSpan (n : Nat)
    (I : RightIdeal (PresentedWeyl k n)) :
    Submodule K (PresentedWeyl K n) :=
  Submodule.span K
    (presentedWeylScalarExtension (k := k) (K := K) n ''
      (I : Set (PresentedWeyl k n)))

theorem scalarImageRightIdealSpan_mul_right (n : Nat)
    (I : RightIdeal (PresentedWeyl k n))
    {a : PresentedWeyl K n}
    (ha : a ∈ scalarImageRightIdealSpan (k := k) (K := K) n I)
    (b : PresentedWeyl K n) :
    a * b ∈ scalarImageRightIdealSpan (k := k) (K := K) n I := by
  let e := presentedWeylScalarExtension (k := k) (K := K) n
  let S := scalarImageRightIdealSpan (k := k) (K := K) n I
  have hbase : ∀ (z : PresentedWeyl k n), z ∈ I →
      ∀ b : PresentedWeyl K n, e z * b ∈ S := by
    intro z hz b
    have hb : b ∈ scalarImageSpan (k := k) (K := K) n :=
      target_mem_scalarImageSpan (k := k) (K := K) n b
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro c hc
      rcases hc with ⟨c, hc, rfl⟩
      have hzc : z * c ∈ I := by
        change MulOpposite.op c • z ∈ I
        exact I.smul_mem _ hz
      change e z * e c ∈ S
      rw [← map_mul]
      exact Submodule.subset_span ⟨z * c, hzc, rfl⟩
    · simp [S, scalarImageRightIdealSpan]
    · intro b₁ b₂ _ _ hb₁ hb₂
      simpa [mul_add] using S.add_mem hb₁ hb₂
    · intro c b _ hb
      rw [Algebra.smul_def, ← mul_assoc,
        (Algebra.commutes c (e z)).symm, mul_assoc]
      simpa [Algebra.smul_def] using S.smul_mem c hb
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro z hz
    rcases hz with ⟨z, hz, rfl⟩
    exact hbase z hz b
  · simp [ scalarImageRightIdealSpan]
  · intro a₁ a₂ _ _ ha₁ ha₂
    simpa [add_mul] using S.add_mem ha₁ ha₂
  · intro c a _ ha
    rw [Algebra.smul_def, mul_assoc]
    simpa [Algebra.smul_def] using S.smul_mem c ha

theorem target_canonicalRightIdeal_le_scalarImageRightIdealSpan
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
      ∀ z, z ∈ canonicalRightIdeal (presentedCoordinate K n)
        (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N →
      z ∈ scalarImageRightIdealSpan (k := k) (K := K) (n + 1)
        (canonicalRightIdeal (presentedCoordinate k n) d N) := by
  let e := presentedWeylScalarExtension (k := k) (K := K) (n + 1)
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let S := scalarImageRightIdealSpan (k := k) (K := K) (n + 1) I
  intro z hz
  change z ∈ S
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha
    · subst a
      change e d ∈ S
      exact Submodule.subset_span ⟨d, firstGenerator_mem
        (presentedCoordinate k n) d N, rfl⟩
    · subst a
      change presentedCoordinate K n ^ N * e d ∈ S
      rw [← presentedWeylScalarExtension_coordinate
        (k := k) (K := K) n, ← map_pow, ← map_mul]
      exact Submodule.subset_span ⟨presentedCoordinate k n ^ N * d,
        secondGenerator_mem (presentedCoordinate k n) d N, rfl⟩
  · exact S.zero_mem
  · intro a b _ _ ha hb
    exact S.add_mem ha hb
  · intro c a _ ha
    change a * c.unop ∈ S
    exact scalarImageRightIdealSpan_mul_right (k := k) (K := K)
      (n + 1) I ha c.unop

theorem scalarImageRightIdealSpan_eq_top (n : Nat) :
    scalarImageRightIdealSpan (k := k) (K := K) n
        (⊤ : RightIdeal (PresentedWeyl k n)) = ⊤ := by
  apply top_unique
  intro z _
  simpa [scalarImageRightIdealSpan, scalarImageSpan] using
    (target_mem_scalarImageSpan (k := k) (K := K) n z)

/-! ## The filtered lifting contract -/

theorem symbolScalarExtension_toRingHom (n : Nat) :
    (symbolScalarExtension (k := k) (K := K) n).toRingHom =
      scalarPolynomialMap (k := k) (K := K) (PhaseVar n) := rfl

/-- The exact filtered statement for support descent.  It asks that
every target order-initial generator be represented by the scalar extension
of source initial generators.  It is stronger than the unfiltered PBW span
proved above and is deliberately not identified with a definitional
base-change equality.  `FilteredScalarLifting.lean` proves this contract by
flat base change of the ideal/order-piece intersection. -/
def FilteredInitialLifting : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    orderInitialIdeal (AlgebraicClosure k)
        (canonicalRightIdeal (presentedCoordinate (AlgebraicClosure k) n)
          (presentedWeylScalarExtension (k := k)
            (K := AlgebraicClosure k) (n + 1) d) N) ≤
      (orderInitialIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)).map
        (scalarPolynomialMap (k := k) (K := AlgebraicClosure k)
          (PhaseVar (n + 1)))

theorem canonicalSupportDescent_of_filteredInitialLifting
    (hfiltered : FilteredInitialLifting.{u}) :
    Stafford38.CanonicalSupportVanishingReduction.CanonicalSupportDescent.{u} := by
  intro hclosed k _ _ n N d hN hd
  let e := presentedWeylScalarExtension (k := k)
    (K := AlgebraicClosure k) (n + 1)
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let IK := canonicalRightIdeal (presentedCoordinate (AlgebraicClosure k) n)
    (e d) N
  have hdK : IsPBWMonicAt (AlgebraicClosure k)
      (.inr (0 : Fin (n + 1))) N (e d) := by
    exact presentedWeylScalarExtension_isPBWMonicAt
      (k := k) (K := AlgebraicClosure k) n N hd
  have hsupportK : orderCharacteristicSupport (AlgebraicClosure k) IK = ∅ := by
    exact hclosed (AlgebraicClosure k) n N (e d) hN hdK
  have htopK : orderInitialIdeal (AlgebraicClosure k) IK = ⊤ :=
    (orderCharacteristicSupport_eq_empty_iff (AlgebraicClosure k) IK).mp
      hsupportK
  have htopMap :
      (orderInitialIdeal k I).map
          (scalarPolynomialMap (k := k) (K := AlgebraicClosure k)
            (PhaseVar (n + 1))) = ⊤ := by
    apply top_unique
    rw [← htopK]
    exact hfiltered k n N d
  have htop : orderInitialIdeal k I = ⊤ := by
    exact (map_scalarPolynomialMap_eq_top_iff
      (J := orderInitialIdeal k I)).mp htopMap
  exact (orderCharacteristicSupport_eq_empty_iff k I).mpr htop


end

end Stafford38.Weyl.PresentedScalarExtension
