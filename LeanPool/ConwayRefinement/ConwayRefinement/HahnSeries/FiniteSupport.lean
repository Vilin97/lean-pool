/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.HahnSeries.Cardinal

/-!
# Finite-support Hahn series

This file packages finite-support Hahn series as the specialization at `Cardinal.aleph0` of
Mathlib's cardinal-bounded Hahn-series subring. It also pulls that subring back to nonpositive
Hahn series. The latter is the ring denoted by `K(G^{≤ 0})` in LM24.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}

section HahnSeries

variable [PartialOrder G] [AddCommMonoid G] [IsOrderedCancelAddMonoid G] [Ring K]

/-- The subring of Hahn series with finite support. -/
def finiteSupportSubring : Subring K⟦G⟧ :=
  let _ : Fact (Cardinal.aleph0.{u} ≤ Cardinal.aleph0.{u}) := ⟨le_rfl⟩
  HahnSeries.cardSuppLTSubring G K Cardinal.aleph0

/-- Membership in the finite-support subring is finiteness of the Hahn-series support. -/
@[simp]
theorem mem_finiteSupportSubring_iff (b : K⟦G⟧) :
    b ∈ (finiteSupportSubring : Subring K⟦G⟧) ↔ b.support.Finite := by
  let : Fact (Cardinal.aleph0.{u} ≤ Cardinal.aleph0.{u}) := ⟨le_rfl⟩
  rw [finiteSupportSubring, HahnSeries.mem_cardSuppLTSubring, HahnSeries.cardSupp]
  exact Cardinal.lt_aleph0_iff_set_finite

end HahnSeries

namespace Nonpositive

/-- The additive monoid of nonpositive exponents. -/
abbrev exponentMonoid (G : Type u) [PartialOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] : AddSubmonoid G where
  carrier := Set.Iic 0
  zero_mem' := le_rfl
  add_mem' := add_nonpos

/-- Zero is the largest nonpositive exponent. -/
instance exponentMonoidOrderTop (G : Type u) [PartialOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] : OrderTop (exponentMonoid G) where
  top := 0
  le_top g := g.2

@[simp]
theorem exponentMonoid_top_eq_zero (G : Type u) [PartialOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] : (⊤ : exponentMonoid G) = 0 :=
  rfl

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Ring K]

/-- The subring of nonpositive Hahn series with finite support. -/
def finiteSupportSubring : Subring (Nonpositive G K) :=
  HahnSeries.finiteSupportSubring.comap (HahnSeries.nonpositiveSubring G K).subtype

/-- The type of finite-support nonpositive Hahn series. -/
abbrev FiniteSupportRing :=
  (finiteSupportSubring : Subring (Nonpositive G K))

/-! The structures on the finite-support ring, named here rather than rebuilt at each use.
`Zero` is the one that matters: it is asked for by every comparison against `0`, and resolving it
through the `Subring` membership classes is not cheap. -/

instance : Zero (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : One (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : Semiring (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : Ring (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- The finite-support ring acts faithfully on the series ring, because it is a subring of it.
Named here because the generic route to this instance goes through torsion-freeness and freeness
first and is too expensive to re-run at every use. -/
instance : FaithfulSMul (FiniteSupportRing (G := G) (K := K)) (Nonpositive G K) :=
  ⟨fun h ↦ Subtype.ext (eq_of_smul_eq_smul h)⟩

/-- Membership in the nonpositive finite-support subring is finiteness of the underlying support.
-/
@[simp]
theorem mem_finiteSupportSubring_iff (b : Nonpositive G K) :
    b ∈ (finiteSupportSubring : Subring (Nonpositive G K)) ↔
      (b : K⟦G⟧).support.Finite := by
  rw [finiteSupportSubring, Subring.mem_comap]
  rw [HahnSeries.mem_finiteSupportSubring_iff]
  simp only [Subring.subtype_apply]

end Nonpositive

namespace Nonpositive

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [CommRing K]

instance : CommRing (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- The coefficient field embeds in the finite-support ring as constant Hahn series. -/
def finiteSupportScalarHom :
    K →+* (finiteSupportSubring : Subring (Nonpositive G K)) :=
  (C : K →+* Nonpositive G K).codRestrict finiteSupportSubring fun k ↦ by
    rw [mem_finiteSupportSubring_iff, coe_C]
    exact Set.Finite.subset (Set.finite_singleton (0 : G))
      HahnSeries.support_single_subset

/-- The canonical coefficient-algebra structure on the finite-support ring. -/
noncomputable instance finiteSupportAlgebra :
    Algebra K (finiteSupportSubring : Subring (Nonpositive G K)) :=
  finiteSupportScalarHom.toAlgebra

/-- Scalar multiplication in the finite-support algebra is multiplication by a constant
series. -/
theorem smul_finiteSupport_eq_scalar_mul
    (k : K) (b : (finiteSupportSubring : Subring (Nonpositive G K))) :
    k • b = finiteSupportScalarHom k * b := by
  rw [Algebra.smul_def]
  rfl

/-- The scalar map is the constant-series embedding on underlying Hahn series. -/
@[simp]
theorem coe_finiteSupportScalarHom (k : K) :
    ((((finiteSupportScalarHom (G := G) k :
        (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧)) = HahnSeries.C k :=
  coe_C k

/-- The constant-series embedding into the finite-support ring is injective. -/
theorem finiteSupportScalarHom_injective :
    Function.Injective (finiteSupportScalarHom (G := G) :
      K → (finiteSupportSubring : Subring (Nonpositive G K))) := by
  intro k l hkl
  have hcoeff := congrArg
    (fun b : (finiteSupportSubring : Subring (Nonpositive G K)) ↦
      ((b : Nonpositive G K) : K⟦G⟧)) hkl
  apply (HahnSeries.C_injective (R := K) (Γ := G))
  simpa only [coe_finiteSupportScalarHom] using hcoeff

/-- Read a finite-support nonpositive Hahn series as its finitely supported coefficient
function on the nonpositive exponents. -/
def finiteSupportCoefficients :
    (finiteSupportSubring : Subring (Nonpositive G K)) →ₗ[K]
      (exponentMonoid G →₀ K) where
  toFun b := Finsupp.ofSupportFinite
    (fun g ↦ ((b : Nonpositive G K) : K⟦G⟧).coeff g)
    (by
      rw [show Function.support (fun g : exponentMonoid G ↦
          ((b : Nonpositive G K) : K⟦G⟧).coeff g) =
          ((b : Nonpositive G K) : K⟦G⟧).support.preimage Subtype.val from rfl]
      apply Set.Finite.preimage Subtype.val_injective.injOn
      exact (mem_finiteSupportSubring_iff (b : Nonpositive G K)).mp b.2)
  map_add' b c := by
    ext g
    simp only [Finsupp.ofSupportFinite_coe]
    exact HahnSeries.coeff_add
  map_smul' k b := by
    ext g
    simp only [Finsupp.ofSupportFinite_coe]
    change (((((finiteSupportScalarHom (G := G) k) * b :
      (finiteSupportSubring : Subring (Nonpositive G K))) :
        Nonpositive G K) : K⟦G⟧).coeff g) = _
    rw [Subring.coe_mul]
    change ((C k : Nonpositive G K) * (b : Nonpositive G K) : K⟦G⟧).coeff g = _
    rw [coe_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
    rfl

/-- Evaluating the coefficient map returns the corresponding Hahn-series coefficient. -/
@[simp]
theorem finiteSupportCoefficients_apply
    (b : (finiteSupportSubring : Subring (Nonpositive G K)))
    (g : exponentMonoid G) :
    finiteSupportCoefficients b g = ((b : Nonpositive G K) : K⟦G⟧).coeff g := by
  exact congrFun Finsupp.ofSupportFinite_coe g

private theorem finiteSupportCoefficients_injective :
    Function.Injective
      (finiteSupportCoefficients (G := G) (K := K)) := by
  intro b c hbc
  apply Subtype.ext
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext g
  by_cases hg : g ≤ 0
  · have h := DFunLike.congr_fun hbc ⟨g, hg⟩
    simpa only [finiteSupportCoefficients_apply] using h
  · have hgb : g ∉ ((b : Nonpositive G K) : K⟦G⟧).support := by
      intro hsupport
      exact hg (support_subset (b : Nonpositive G K) hsupport)
    have hgc : g ∉ ((c : Nonpositive G K) : K⟦G⟧).support := by
      intro hsupport
      exact hg (support_subset (c : Nonpositive G K) hsupport)
    rw [HahnSeries.mem_support] at hgb hgc
    exact (not_ne_iff.mp hgb).trans (not_ne_iff.mp hgc).symm

private theorem finiteSupportCoefficients_surjective :
    Function.Surjective
      (finiteSupportCoefficients (G := G) (K := K)) := by
  intro f
  let e : exponentMonoid G ↪ G := Function.Embedding.subtype _
  let f' : G →₀ K := Finsupp.embDomain e f
  let bHahn : K⟦G⟧ := HahnSeries.ofFinsupp f'
  have hbSupport : bHahn.support ⊆ Set.Iic 0 := by
    intro g hg
    have hgf' : f' g ≠ 0 := by
      simpa [bHahn, HahnSeries.mem_support] using hg
    have hgrange : g ∈ Set.range e := by
      contrapose! hgf'
      exact Finsupp.embDomain_of_notMem_range e f g hgf'
    obtain ⟨x, rfl⟩ := hgrange
    exact x.2
  let b : Nonpositive G K :=
    ⟨bHahn, (mem_nonpositiveSubring (x := bHahn)).mpr hbSupport⟩
  have hbFinite : ((b : Nonpositive G K) : K⟦G⟧).support.Finite := by
    change (Function.support (f' : G → K)).Finite
    exact f'.hasFiniteSupport
  let bd : (finiteSupportSubring : Subring (Nonpositive G K)) := ⟨b, by
    rw [mem_finiteSupportSubring_iff]
    exact hbFinite⟩
  refine ⟨bd, ?_⟩
  ext g
  rw [finiteSupportCoefficients_apply]
  change f' g = f g
  exact Finsupp.embDomain_apply_self e f g

/-- Finite-support nonpositive Hahn series are linearly equivalent to finitely supported
coefficient functions on the nonpositive exponents. -/
def finiteSupportFinsuppEquiv :
    (finiteSupportSubring : Subring (Nonpositive G K)) ≃ₗ[K]
      (exponentMonoid G →₀ K) :=
  LinearEquiv.ofBijective finiteSupportCoefficients
    ⟨finiteSupportCoefficients_injective, finiteSupportCoefficients_surjective⟩

/-- The finite-support linear equivalence evaluates as the coefficient map. -/
@[simp]
theorem finiteSupportFinsuppEquiv_apply
    (b : (finiteSupportSubring : Subring (Nonpositive G K))) :
    finiteSupportFinsuppEquiv b = finiteSupportCoefficients b :=
  (rfl)

/-- The finite-support monomial `t^g`, for a nonpositive exponent `g`. -/
def finiteSupportMonomial (g : exponentMonoid G) :
    (finiteSupportSubring : Subring (Nonpositive G K)) :=
  ⟨single (g : G) (1 : K) (show (g : G) ≤ 0 from g.2), by
    rw [mem_finiteSupportSubring_iff, coe_single]
    exact Set.Finite.subset (Set.finite_singleton (g : G))
      (HahnSeries.support_single_subset (a := (g : G)) (r := (1 : K)))⟩

/-- The underlying Hahn series of a finite-support monomial is the corresponding singleton. -/
@[simp]
theorem coe_finiteSupportMonomial (g : exponentMonoid G) :
    (((finiteSupportMonomial (K := K) g :
        (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧) = HahnSeries.single (g : G) (1 : K) :=
  coe_single (g : G) (1 : K) g.2

/-- Multiplication of finite-support monomials adds their exponents. -/
@[simp]
theorem finiteSupportMonomial_mul (g h : exponentMonoid G) :
    finiteSupportMonomial (K := K) g * finiteSupportMonomial (K := K) h =
      finiteSupportMonomial (K := K)
        ⟨(g : G) + (h : G), add_nonpos g.2 h.2⟩ := by
  apply Subtype.ext
  change
    (finiteSupportMonomial (K := K) g : Nonpositive G K) *
        (finiteSupportMonomial (K := K) h : Nonpositive G K) =
      (finiteSupportMonomial (K := K)
        ⟨(g : G) + (h : G), add_nonpos g.2 h.2⟩ : Nonpositive G K)
  apply Subtype.ext
  change
    (((finiteSupportMonomial (K := K) g : Nonpositive G K) : K⟦G⟧) *
        ((finiteSupportMonomial (K := K) h : Nonpositive G K) : K⟦G⟧)) = _
  rw [coe_finiteSupportMonomial, coe_finiteSupportMonomial,
    coe_finiteSupportMonomial, HahnSeries.single_mul_single, one_mul]

/-- The coefficient function of `t^g` is the standard finitely supported basis vector. -/
@[simp]
theorem finiteSupportCoefficients_monomial (g : exponentMonoid G) :
    finiteSupportCoefficients (finiteSupportMonomial (K := K) g) =
      Finsupp.single g 1 := by
  classical
  ext x
  rw [finiteSupportCoefficients_apply]
  rw [coe_finiteSupportMonomial]
  change (HahnSeries.single (g : G) (1 : K)).coeff x = _
  rw [HahnSeries.coeff_single, Finsupp.single_apply]
  by_cases hgx : g = x
  · subst x
    simp
  · have hval : (x : G) ≠ g := by
      intro h
      exact hgx (Subtype.ext h.symm)
    simp [hgx, hval]

/-- The monomials `t^g`, indexed by the nonpositive exponents, form the canonical coefficient
basis of the finite-support ring. -/
def finiteSupportBasis :
    Module.Basis (exponentMonoid G) K
      (finiteSupportSubring : Subring (Nonpositive G K)) :=
  (Finsupp.basisSingleOne (R := K)).map finiteSupportFinsuppEquiv.symm

/-- The canonical finite-support basis vector at `g` is the monomial `t^g`. -/
@[simp]
theorem finiteSupportBasis_apply (g : exponentMonoid G) :
    finiteSupportBasis (K := K) g = finiteSupportMonomial (K := K) g := by
  apply finiteSupportCoefficients_injective
  rw [finiteSupportCoefficients_monomial]
  change finiteSupportFinsuppEquiv
      (finiteSupportFinsuppEquiv.symm (Finsupp.single g 1)) = _
  exact finiteSupportFinsuppEquiv.apply_symm_apply _

/-- The coordinate of a finite-support series at `g` is its Hahn-series coefficient at `g`. -/
@[simp]
theorem finiteSupportBasis_repr_apply
    (b : (finiteSupportSubring : Subring (Nonpositive G K)))
    (g : exponentMonoid G) :
    finiteSupportBasis.repr b g = ((b : Nonpositive G K) : K⟦G⟧).coeff g := by
  change finiteSupportFinsuppEquiv b g = _
  exact finiteSupportCoefficients_apply b g

end Nonpositive

end HahnSeries
