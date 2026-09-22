/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.ValuedAdicComplete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.CompatibleInverseLimit
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.Models
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Topology.Homeomorph.TransferInstance
/-!
# Adic completion and inverse limits

This file contains the algebraic and topological projective-limit descriptions
of adically complete rings, complete discrete valuation rings, and their unit
groups.
-/

noncomputable section

namespace LubinTate
namespace Valuations

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, algebraic form: an adically complete ring is canonically
isomorphic to its adic completion. -/
def adicCompletionAlgEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    R ≃ₐ[R] AdicCompletion I R :=
  AdicCompletion.ofAlgEquiv I

/-- The canonical isomorphism to the adic completion is induced by the usual
completion map. -/
theorem adicCompletionAlgEquiv_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (x : R) :
    adicCompletionAlgEquiv I x = AdicCompletion.of I R x := by
  exact AdicCompletion.ofAlgEquiv_apply (S := R) I x

/-- The finite coordinates of the canonical adic-completion isomorphism are
the usual quotient classes modulo `I ^ n`. -/
theorem adicCompletion_eval_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (n : ℕ) (x : R) :
    AdicCompletion.evalₐ I n (adicCompletionAlgEquiv I x) =
      Ideal.Quotient.mk (I ^ n) x := by
  rw [adicCompletionAlgEquiv_apply]
  exact AdicCompletion.evalₐ_of (R := R) I n x

/-- The adic inverse-limit equivalence, projective-limit surjectivity in coordinates: every
compatible adic-completion point is represented by a unique element of the
original complete ring, and all finite coordinates agree with reduction modulo
`I ^ n`. -/
theorem adicCompletion_coordinates_surjective
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (z : AdicCompletion I R) :
    ∃ x : R,
      adicCompletionAlgEquiv I x = z ∧
        ∀ n : ℕ,
          Ideal.Quotient.mk (I ^ n) x = AdicCompletion.evalₐ I n z := by
  refine ⟨(adicCompletionAlgEquiv I).symm z, ?_, ?_⟩
  · simp
  · intro n
    simp [adicCompletionAlgEquiv,
      AdicCompletion.mk_ofAlgEquiv_symm]

/-- The adic inverse-limit equivalence, uniqueness in coordinates: two elements with the same
finite reductions modulo every `I ^ n` are equal. -/
theorem adicCompletion_coordinates_injective
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {x y : R}
    (h :
      ∀ n : ℕ,
        Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  have hsub : ∀ n : ℕ, x - y ∈ I ^ n := by
    intro n
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := I ^ n) (x := x) (y := y)).1 (h n)
  have hz : x - y = 0 := by
    apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hsub n
  exact sub_eq_zero.mp hz

/-- A finite adic quotient with its discrete topology fixed in the type. -/
structure DiscreteAdicQuotient
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) where
  /-- The underlying residue class modulo `I ^ n`. -/
  val : R ⧸ I ^ n

namespace DiscreteAdicQuotient

/-- Defines `equiv`. -/
def equiv {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteAdicQuotient I n ≃ R ⧸ I ^ n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- A discrete adic quotient inherits its commutative ring structure from the concrete quotient. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    CommRing (DiscreteAdicQuotient I n) :=
  (equiv I n).commRing

/-- Each adic quotient is equipped with the discrete topology. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    TopologicalSpace (DiscreteAdicQuotient I n) := ⊥

/-- The selected topology on an adic quotient is discrete. -/
instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteTopology (DiscreteAdicQuotient I n) :=
  ⟨rfl⟩

/-- Defines `of`. -/
def of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : DiscreteAdicQuotient I n :=
  ⟨x⟩

/-- Forgetting the discrete adic wrapper after insertion recovers the original quotient element. -/
@[simp]
theorem val_of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : (of I n x).val = x :=
  rfl

/-- The explicit boundary homeomorphism to the raw quotient equipped with
the discrete topology. -/
def homeomorph {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    @Homeomorph (DiscreteAdicQuotient I n) (R ⧸ I ^ n)
      (inferInstance : TopologicalSpace (DiscreteAdicQuotient I n))
      (⊥ : TopologicalSpace (R ⧸ I ^ n)) := by
  letI : TopologicalSpace (R ⧸ I ^ n) := ⊥
  letI : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  exact
    { toEquiv := equiv I n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete adic homeomorphism evaluates as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : DiscreteAdicQuotient I n) : homeomorph I n x = x.val :=
  rfl

/-- The inverse quotient equivalence inserts a concrete quotient into its discrete copy. -/
@[simp]
theorem equiv_symm_apply {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (x : R ⧸ I ^ n) :
    (equiv I n).symm x = of I n x :=
  rfl

end DiscreteAdicQuotient

/-- The adic inverse-limit object `lim_n R/I^n`.  This is an opaque public
type; its compatible-family implementation is exposed only through the named
equivalence and coordinate API below. -/
def adicQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
    (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn)

/-- The implementation representation of the all-level adic inverse limit. -/
def adicQuotientInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I ≃
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
        (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) := by
  unfold adicQuotientInverseLimit
  exact Equiv.refl _

/-- Compatible adic quotient families form a commutative ring coordinatewise. -/
instance adicQuotientInverseLimit.instCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (adicQuotientInverseLimit I) :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).commRing

/-- The algebraic representation equivalence of the all-level adic inverse
limit. -/
def adicQuotientInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I ≃+*
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
        (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).ringEquiv

/-- Build an all-level adic inverse-limit point from a compatible family. -/
def adicQuotientInverseLimitMk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m) :
    adicQuotientInverseLimit I :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Coordinate evaluation from the explicit projective limit. -/
def adicQuotientInverseLimitEval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicQuotientInverseLimit I →+* R ⧸ I ^ n where
  toFun x := (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Evaluation of an adic inverse-limit family returns its component at the selected level. -/
@[simp]
theorem adicQuotientInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m)
    (n : ℕ) :
    adicQuotientInverseLimitEval I n
        (adicQuotientInverseLimitMk I x compatible) = x n := by
  rfl

/-- Adic inverse-limit elements are equal when all coordinate evaluations agree. -/
@[ext]
theorem adicQuotientInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicQuotientInverseLimit I}
    (h : ∀ n : ℕ, adicQuotientInverseLimitEval I n x =
      adicQuotientInverseLimitEval I n y) :
    x = y := by
  apply (adicQuotientInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The explicit projective-limit coordinates are compatible with quotient
transition maps. -/
theorem adicQuotientInverseLimit_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : adicQuotientInverseLimit I) :
    Ideal.Quotient.factorPow I hmn
        (adicQuotientInverseLimitEval I n x) =
      adicQuotientInverseLimitEval I m x :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- The canonical prodiscrete topology on the all-level inverse limit.  The
finite quotient stages are discrete inside this one representation boundary;
their raw topology instances do not escape into public theorem statements. -/
noncomputable instance adicQuotientInverseLimit.instTopologicalSpace
    {R : Type*} [CommRing R] (I : Ideal R) :
    TopologicalSpace (adicQuotientInverseLimit I) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  exact (adicQuotientInverseLimitCompatibleFamiliesEquiv I).topologicalSpace

private noncomputable def adicQuotientInverseLimitRepresentationHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) :
    letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
    adicQuotientInverseLimit I ≃ₜ
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
        (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  exact (adicQuotientInverseLimitCompatibleFamiliesEquiv I).homeomorph

/-- Coordinate evaluation into a type whose discreteness is recorded in the
type itself. -/
def adicQuotientInverseLimitDiscreteEval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicQuotientInverseLimit I → DiscreteAdicQuotient I n :=
  fun x => DiscreteAdicQuotient.of I n
    (adicQuotientInverseLimitEval I n x)

/-- Evaluation from the adic inverse limit to each discrete quotient is continuous. -/
theorem adicQuotientInverseLimit_discreteEval_continuous
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Continuous (adicQuotientInverseLimitDiscreteEval I n) := by
  let : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  let representation := adicQuotientInverseLimitRepresentationHomeomorph I
  have hraw : Continuous fun x : adicQuotientInverseLimit I =>
      (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n :=
    (continuous_apply n).comp
      (continuous_subtype_val.comp representation.continuous)
  have hmodel :=
    (DiscreteAdicQuotient.homeomorph I n).symm.continuous.comp hraw
  change Continuous (fun x : adicQuotientInverseLimit I =>
    DiscreteAdicQuotient.of I n
      ((adicQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n))
  exact hmodel

/-- The quotient algebra equivalence induced by equal ideals sends inverse
representatives as expected. -/
theorem quotientEquivAlgOfEq_apply_symm
    {R : Type*} [CommRing R] {I J : Ideal R}
    (h₁ h₂ : I = J) (y : R ⧸ J) :
    (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂).symm y) = y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂.symm) (Ideal.Quotient.mk J r)) =
    Ideal.Quotient.mk J r
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]

/-- Adic transition maps commute with quotient equivalences arising from equal powers. -/
theorem transitionMap_quotientEquivAlgOfEq
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (hm : (I ^ m • ⊤ : Ideal R) = I ^ m)
    (hn : (I ^ n • ⊤ : Ideal R) = I ^ n)
    (y : R ⧸ I ^ n) :
    (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn).symm y)) =
      Ideal.Quotient.factorPow I hmn y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn.symm)
          (Ideal.Quotient.mk (I ^ n) r))) =
    Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) r)
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [AdicCompletion.transitionMap_ideal_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The finite quotient coordinates of an adic-completion point are compatible
under the transition maps. -/
theorem adicCompletion_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
      AdicCompletion.evalₐ I m z := by
  rcases AdicCompletion.mk_surjective I R z with ⟨seq, rfl⟩
  simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow] using
    (AdicCompletion.Ideal.mk_eq_mk I hmn seq)

/-- The map from the adic completion to the explicit projective limit
`lim_n R/I^n`. -/
def adicCompletionToQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R → adicQuotientInverseLimit I :=
  fun z =>
    adicQuotientInverseLimitMk I
      (fun n => AdicCompletion.evalₐ I n z)
      (fun hmn => adicCompletion_eval_factorPow I hmn z)

/-- The inverse map from the explicit projective limit `lim_n R/I^n` to the
adic completion. -/
def adicQuotientInverseLimitToCompletion
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I → AdicCompletion I R :=
  fun x =>
    ⟨fun n =>
      let h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      (Ideal.quotientEquivAlgOfEq R h).symm
        (adicQuotientInverseLimitEval I n x),
    by
      intro m n hmn
      let hm : (I ^ m • ⊤ : Ideal R) = I ^ m := by ext r; simp
      let hn : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      apply (Ideal.quotientEquivAlgOfEq R hm).injective
      rw [transitionMap_quotientEquivAlgOfEq I hmn hm hn]
      rw [quotientEquivAlgOfEq_apply_symm]
      exact adicQuotientInverseLimit_eval_factorPow I hmn x⟩

/-- The map from the adic inverse limit to the completion has the prescribed
residue at every level. -/
theorem adicQuotientInverseLimit_toCompletion_eval
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (adicQuotientInverseLimitToCompletion I x) =
      adicQuotientInverseLimitEval I n x := by
  change (Ideal.quotientEquivAlgOfEq R (by ext r; simp))
      ((adicQuotientInverseLimitToCompletion I x).val n) =
    adicQuotientInverseLimitEval I n x
  dsimp [adicQuotientInverseLimitToCompletion]
  rw [quotientEquivAlgOfEq_apply_symm]

/-- Mapping an inverse-limit family to the completion and back recovers the family. -/
theorem adicQuotientInverseLimit_left_inverse
    {R : Type*} [CommRing R] (I : Ideal R) (z : AdicCompletion I R) :
    adicQuotientInverseLimitToCompletion I
        (adicCompletionToQuotientInverseLimit I z) = z := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicQuotientInverseLimit_toCompletion_eval]
  rfl

/-- Mapping a completion element to its residue family and back recovers the element. -/
theorem adicQuotientInverseLimit_right_inverse
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) :
    adicCompletionToQuotientInverseLimit I
        (adicQuotientInverseLimitToCompletion I x) = x := by
  ext n
  change AdicCompletion.evalₐ I n
      (adicQuotientInverseLimitToCompletion I x) =
    adicQuotientInverseLimitEval I n x
  rw [adicQuotientInverseLimit_toCompletion_eval]

/-- The adic inverse-limit equivalence, algebraic projective-limit form:
the adic completion is canonically isomorphic to `lim_n R/I^n`. -/
def adicCompletionEquivQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R ≃+* adicQuotientInverseLimit I where
  toFun := adicCompletionToQuotientInverseLimit I
  invFun := adicQuotientInverseLimitToCompletion I
  left_inv := adicQuotientInverseLimit_left_inverse I
  right_inv := adicQuotientInverseLimit_right_inverse I
  map_mul' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x * y) =
      AdicCompletion.evalₐ I n x * AdicCompletion.evalₐ I n y
    simp
  map_add' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x + y) =
      AdicCompletion.evalₐ I n x + AdicCompletion.evalₐ I n y
    simp

/-- The adic inverse-limit equivalence, canonical map from a ring to the explicit projective
limit of its quotients. -/
def adicQuotientInverseLimitCanonicalMap
    {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* adicQuotientInverseLimit I where
  toFun x := adicQuotientInverseLimitMk I
    (fun n => Ideal.Quotient.mk (I ^ n) x)
    (fun _ => rfl)
  map_one' := by ext n; rfl
  map_mul' x y := by ext n; rfl
  map_zero' := by ext n; rfl
  map_add' x y := by ext n; rfl

/-- The adic inverse-limit equivalence, if `R` is complete for the `I`-adic topology, the
canonical map `R → lim_n R/I^n` is a ring isomorphism. -/
def adicQuotientInverseLimitEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    R ≃+* adicQuotientInverseLimit I :=
  (adicCompletionAlgEquiv I).toRingEquiv.trans
    (adicCompletionEquivQuotientInverseLimit I)

/-- The complete-ring projective-limit isomorphism is induced by reduction
modulo `I^n` in each coordinate. -/
theorem adicQuotientInverseLimitEquiv_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (x : R) (n : ℕ) :
    adicQuotientInverseLimitEval I n
        (adicQuotientInverseLimitEquiv I x) =
      Ideal.Quotient.mk (I ^ n) x := by
  change AdicCompletion.evalₐ I n
      (adicCompletionAlgEquiv I x) =
    Ideal.Quotient.mk (I ^ n) x
  rw [adicCompletion_eval_apply]

/-- Reduction modulo `I^n` is continuous from the `I`-adic topology to the
discrete finite quotient topology. -/
private theorem quotient_mk_continuous_adic_raw
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    @Continuous R (R ⧸ I ^ n) I.adicTopology
      (⊥ : TopologicalSpace (R ⧸ I ^ n))
      (Ideal.Quotient.mk (I ^ n)) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace (R ⧸ I ^ n) := ⊥
  let : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  change Filter.Tendsto (Ideal.Quotient.mk (I ^ n)) (𝓝 x)
    (𝓝 (Ideal.Quotient.mk (I ^ n) x))
  rw [@nhds_discrete (R ⧸ I ^ n) _ _]
  rw [Filter.tendsto_def]
  intro s hs
  rw [mem_pure] at hs
  exact (Ideal.hasBasis_nhds_adic I x).mem_iff.mpr ⟨n, trivial, by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hq : Ideal.Quotient.mk (I ^ n) (x + z) =
        Ideal.Quotient.mk (I ^ n) x := by
      apply Ideal.Quotient.eq.mpr
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
    simpa [hq] using hs⟩

/-- Reduction from the type-level adic ring to the named discrete quotient
model is continuous. -/
theorem quotient_mk_continuous_adic
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Continuous fun x :
        WithTopology R I.adicTopology =>
      DiscreteAdicQuotient.of I n
        (Ideal.Quotient.mk (I ^ n) x.ofTopology) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace (R ⧸ I ^ n) := ⊥
  let : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  have hraw := quotient_mk_continuous_adic_raw I n
  have hunderlying :
      Continuous fun x :
          WithTopology R I.adicTopology =>
        Ideal.Quotient.mk (I ^ n) x.ofTopology :=
    hraw.comp (WithTopology.continuous_ofTopology I.adicTopology)
  have hmodel :=
    (DiscreteAdicQuotient.homeomorph I n).symm.continuous.comp hunderlying
  convert hmodel using 1
  rfl

private noncomputable def adicQuotientCompatibleFamiliesHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    letI : TopologicalSpace R := I.adicTopology
    letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
    R ≃ₜ compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
      (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology (R ⧸ I ^ n) := fun _ => ⟨rfl⟩
  let e := (adicQuotientInverseLimitEquiv I).trans
    (adicQuotientInverseLimitRepresentation I)
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact Continuous.subtype_mk
      (continuous_pi fun n => by
        convert quotient_mk_continuous_adic_raw I n using 1
        funext x
        exact adicCompletion_eval_apply I n x)
      (fun x => by
        intro m n hmn
        exact adicCompletion_eval_factorPow I hmn
          ((adicCompletionAlgEquiv I) x))
  · rw [continuous_iff_continuousAt]
    intro q
    rw [ContinuousAt]
    rw [Filter.tendsto_def]
    intro s hs
    rcases (Ideal.hasBasis_nhds_adic I (e.symm q)).mem_iff.mp hs with
      ⟨n, _hn, hns⟩
    let cylinder : Set
        (compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
          (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn)) :=
      {q' | q'.1 n = q.1 n}
    have hcont_coord :
        Continuous fun q' :
            compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
              (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) =>
          q'.1 n := by
      exact (continuous_apply n).comp continuous_subtype_val
    have hcyl_open : IsOpen cylinder := by
      exact (isOpen_discrete ({q.1 n} : Set (R ⧸ I ^ n))).preimage hcont_coord
    have hqmem : q ∈ cylinder := rfl
    exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
      intro q' hq'
      apply hns
      have hred' : Ideal.Quotient.mk (I ^ n) (e.symm q') = q'.1 n := by
        calc
          Ideal.Quotient.mk (I ^ n) (e.symm q') = (e (e.symm q')).1 n :=
            (adicQuotientInverseLimitEquiv_apply I (e.symm q') n).symm
          _ = q'.1 n := by
            simp [e.apply_symm_apply q']
      have hred : Ideal.Quotient.mk (I ^ n) (e.symm q) = q.1 n := by
        calc
          Ideal.Quotient.mk (I ^ n) (e.symm q) = (e (e.symm q)).1 n :=
            (adicQuotientInverseLimitEquiv_apply I (e.symm q) n).symm
          _ = q.1 n := by
            simp [e.apply_symm_apply q]
      have hmk : Ideal.Quotient.mk (I ^ n) (e.symm q') =
          Ideal.Quotient.mk (I ^ n) (e.symm q) := by
        rw [hred', hred, hq']
      have hmem : e.symm q' - e.symm q ∈ I ^ n := by
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
          (I := I ^ n) (x := e.symm q') (y := e.symm q)).1 hmk
      refine ⟨e.symm q' - e.symm q, hmem, ?_⟩
      ring)

/-- The canonical equivalence from an adically complete ring, represented by
an adic type-level source and the opaque prodiscrete inverse-limit target. -/
noncomputable def adicQuotientInverseLimitHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    WithTopology R I.adicTopology ≃ₜ
      adicQuotientInverseLimit I := by
  letI : TopologicalSpace R := I.adicTopology
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  let source := WithTopology.homeomorph
    (α := R) (topology := I.adicTopology)
  let algebraic := adicQuotientCompatibleFamiliesHomeomorph I
  let target := adicQuotientInverseLimitRepresentationHomeomorph I
  exact source.trans (algebraic.trans target.symm)

/-- The opaque positive-indexed projective-limit object
`lim_n R/I^(n+1)`. -/
def adicPositiveQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
    (fun {_ _} hmn =>
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn))

/-- The implementation representation of the positive-indexed ring limit. -/
def adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveQuotientInverseLimit I ≃
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
        (fun {_ _} hmn =>
          Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) := by
  unfold adicPositiveQuotientInverseLimit
  exact Equiv.refl _

/-- Positive-level compatible adic quotient families form a commutative ring. -/
instance adicPositiveQuotientInverseLimit.instCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (adicPositiveQuotientInverseLimit I) :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).commRing

/-- Defines `adicPositiveQuotientInverseLimitRepresentation`. -/
def adicPositiveQuotientInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveQuotientInverseLimit I ≃+*
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
        (fun {_ _} hmn =>
          Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).ringEquiv

/-- Defines `adicPositiveQuotientInverseLimitMk`. -/
def adicPositiveQuotientInverseLimitMk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (x n) = x m) :
    adicPositiveQuotientInverseLimit I :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Defines `adicPositiveQuotientInverseLimitEval`. -/
def adicPositiveQuotientInverseLimitEval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveQuotientInverseLimit I →+* R ⧸ I ^ (n + 1) where
  toFun x :=
    (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Positive-level evaluation returns the selected adic quotient component. -/
@[simp]
theorem adicPositiveQuotientInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (x n) = x m)
    (n : ℕ) :
    adicPositiveQuotientInverseLimitEval I n
        (adicPositiveQuotientInverseLimitMk I x compatible) = x n := by
  rfl

/-- Positive adic inverse-limit elements are determined by all of their components. -/
@[ext]
theorem adicPositiveQuotientInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicPositiveQuotientInverseLimit I}
    (h : ∀ n : ℕ, adicPositiveQuotientInverseLimitEval I n x =
      adicPositiveQuotientInverseLimitEval I n y) :
    x = y := by
  apply (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Positive-level evaluation is compatible with the factor map between ideal powers. -/
theorem adicPositiveQuotientInverseLimit_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : adicPositiveQuotientInverseLimit I) :
    Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)
        (adicPositiveQuotientInverseLimitEval I n x) =
      adicPositiveQuotientInverseLimitEval I m x :=
  (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- The positive adic inverse limit carries the topology induced by its discrete coordinates. -/
noncomputable instance adicPositiveQuotientInverseLimit.instTopologicalSpace
    {R : Type*} [CommRing R] (I : Ideal R) :
    TopologicalSpace (adicPositiveQuotientInverseLimit I) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  exact
    (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).topologicalSpace

private noncomputable def
    adicPositiveQuotientInverseLimitRepresentationHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) :
    letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
    adicPositiveQuotientInverseLimit I ≃ₜ
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
        (fun {_ _} hmn =>
          Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  exact
    (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I).homeomorph

/-- Defines `adicPositiveQuotientInverseLimitDiscreteEval`. -/
def adicPositiveQuotientInverseLimitDiscreteEval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveQuotientInverseLimit I → DiscreteAdicQuotient I (n + 1) :=
  fun x => DiscreteAdicQuotient.of I (n + 1)
    (adicPositiveQuotientInverseLimitEval I n x)

/-- Every positive-level coordinate evaluation into a discrete adic quotient is continuous. -/
theorem adicPositiveQuotientInverseLimit_discreteEval_continuous
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Continuous (adicPositiveQuotientInverseLimitDiscreteEval I n) := by
  let : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  let representation :=
    adicPositiveQuotientInverseLimitRepresentationHomeomorph I
  have hraw : Continuous fun x : adicPositiveQuotientInverseLimit I =>
      (adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n :=
    (continuous_apply n).comp
      (continuous_subtype_val.comp representation.continuous)
  have hmodel :=
    (DiscreteAdicQuotient.homeomorph I (n + 1)).symm.continuous.comp hraw
  change Continuous (fun x : adicPositiveQuotientInverseLimit I =>
    DiscreteAdicQuotient.of I (n + 1)
      ((adicPositiveQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n))
  exact hmodel

/-- Defines `adicQuotientInverseLimitToPositive`. -/
def adicQuotientInverseLimitToPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I →
      adicPositiveQuotientInverseLimit I :=
  fun x =>
    adicPositiveQuotientInverseLimitMk I
      (fun n => adicQuotientInverseLimitEval I (n + 1) x)
      (fun hmn =>
        adicQuotientInverseLimit_eval_factorPow I
          (Nat.succ_le_succ hmn) x)

/-- Defines `adicPositiveQuotientInverseLimitToAll`. -/
def adicPositiveQuotientInverseLimitToAll
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveQuotientInverseLimit I →
      adicQuotientInverseLimit I :=
  fun x =>
    adicQuotientInverseLimitMk I (fun n => match n with
      | 0 => 0
      | k + 1 => adicPositiveQuotientInverseLimitEval I k x)
    (by
      intro m n hmn
      cases m with
      | zero =>
          have : Subsingleton (R ⧸ I ^ 0) := by
            simpa only [pow_zero, Ideal.one_eq_top] using
              (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
          exact Subsingleton.elim _ _
      | succ m =>
          cases n with
          | zero => cases hmn
          | succ n =>
              exact adicPositiveQuotientInverseLimit_eval_factorPow I
                (Nat.succ_le_succ_iff.mp hmn) x)

/-- Restricting an all-level adic family to positive levels and extending back is the identity. -/
theorem adicPositiveQuotientInverseLimit_toPositive_toAll
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicPositiveQuotientInverseLimit I) :
    adicQuotientInverseLimitToPositive I
        (adicPositiveQuotientInverseLimitToAll I x) = x := by
  ext n
  rfl

/-- Extending a positive-level adic family and restricting again is the identity. -/
theorem adicQuotientInverseLimit_toAll_toPositive
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) :
    adicPositiveQuotientInverseLimitToAll I
        (adicQuotientInverseLimitToPositive I x) = x := by
  ext n
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      exact Subsingleton.elim _ _
  | succ n =>
      rfl

/-- The all-level quotient inverse limit is equivalent to the canonical
positive-indexed one. -/
def adicQuotientInverseLimitEquivPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I ≃+*
      adicPositiveQuotientInverseLimit I where
  toFun := adicQuotientInverseLimitToPositive I
  invFun := adicPositiveQuotientInverseLimitToAll I
  left_inv := adicQuotientInverseLimit_toAll_toPositive I
  right_inv := adicPositiveQuotientInverseLimit_toPositive_toAll I
  map_mul' x y := by
    ext n
    rfl
  map_add' x y := by
    ext n
    rfl

/-- The adic inverse-limit equivalence, canonical map from a ring to the positive-indexed
projective limit of its quotients. -/
def adicPositiveQuotientInverseLimitCanonicalMap
    {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* adicPositiveQuotientInverseLimit I where
  toFun x := adicPositiveQuotientInverseLimitMk I
    (fun n => Ideal.Quotient.mk (I ^ (n + 1)) x)
    (fun _ => rfl)
  map_one' := by ext n; rfl
  map_mul' x y := by ext n; rfl
  map_zero' := by ext n; rfl
  map_add' x y := by ext n; rfl

/-- The adic inverse-limit equivalence, if `R` is complete for the `I`-adic topology, the
canonical map `R → lim_n R/I^(n+1)` is a ring isomorphism. -/
def adicPositiveQuotientInverseLimitEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    R ≃+* adicPositiveQuotientInverseLimit I :=
  (adicQuotientInverseLimitEquiv I).trans
    (adicQuotientInverseLimitEquivPositive I)

/-- The positive-indexed projective-limit isomorphism is induced by reduction
modulo `I^(n+1)` in each coordinate. -/
theorem adicPositiveQuotientInverseLimitEquiv_apply
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (x : R) (n : ℕ) :
    adicPositiveQuotientInverseLimitEval I n
        (adicPositiveQuotientInverseLimitEquiv I x) =
      Ideal.Quotient.mk (I ^ (n + 1)) x :=
  adicQuotientInverseLimitEquiv_apply I x (n + 1)

private noncomputable def adicPositiveQuotientCompatibleFamiliesHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    letI : TopologicalSpace R := I.adicTopology
    letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
    R ≃ₜ compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
      (fun {_ _} hmn =>
        Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology (R ⧸ I ^ (n + 1)) := fun _ => ⟨rfl⟩
  let e := (adicPositiveQuotientInverseLimitEquiv I).trans
    (adicPositiveQuotientInverseLimitRepresentation I)
  let c := (adicPositiveQuotientInverseLimitRepresentation I).toRingHom.comp
    (adicPositiveQuotientInverseLimitCanonicalMap I)
  refine
    { toFun := fun x => c x
      invFun := fun q => e.symm q
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro x
    have hc : c x = e x := by
      ext n
      exact (adicPositiveQuotientInverseLimitEquiv_apply I x n).symm
    change e.symm (c x) = x
    rw [hc]
    exact e.left_inv x
  · intro q
    ext n
    change Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q) = q.1 n
    calc
      Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q) = (e (e.symm q)).1 n :=
        (adicPositiveQuotientInverseLimitEquiv_apply I (e.symm q) n).symm
      _ = q.1 n := by simp [e.apply_symm_apply q]
  · change Continuous fun x : R => c x
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        simpa [c, adicPositiveQuotientInverseLimitCanonicalMap] using
          (quotient_mk_continuous_adic_raw I (n + 1)))
      (by
        intro x m n hmn
        rfl)
  · rw [continuous_iff_continuousAt]
    intro q
    rw [ContinuousAt, Filter.tendsto_def]
    intro s hs
    rcases (Ideal.hasBasis_nhds_adic I (e.symm q)).mem_iff.mp hs with
      ⟨n, _hn, hns⟩
    let cylinder : Set
        (compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ (n + 1))
          (fun {_ _} hmn =>
            Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn))) :=
      {q' | q'.1 n = q.1 n}
    have hcont_coord :
        Continuous fun q' : compatibleRingFamilies
            (fun n : ℕ => R ⧸ I ^ (n + 1))
            (fun {_ _} hmn =>
              Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)) =>
          q'.1 n := by
      exact (continuous_apply n).comp continuous_subtype_val
    have hcyl_open : IsOpen cylinder := by
      exact
        (isOpen_discrete ({q.1 n} : Set (R ⧸ I ^ (n + 1)))).preimage
          hcont_coord
    have hqmem : q ∈ cylinder := rfl
    exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
      intro q' hq'
      apply hns
      have hred' : Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q') = q'.1 n := by
        calc
          Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q') = (e (e.symm q')).1 n :=
            (adicPositiveQuotientInverseLimitEquiv_apply
              I (e.symm q') n).symm
          _ = q'.1 n := by simp [e.apply_symm_apply q']
      have hred : Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q) = q.1 n := by
        calc
          Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q) = (e (e.symm q)).1 n :=
            (adicPositiveQuotientInverseLimitEquiv_apply
              I (e.symm q) n).symm
          _ = q.1 n := by simp [e.apply_symm_apply q]
      have hmk : Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q') =
          Ideal.Quotient.mk (I ^ (n + 1)) (e.symm q) := by
        rw [hred', hred, hq']
      have hmem_succ : e.symm q' - e.symm q ∈ I ^ (n + 1) := by
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
          (I := I ^ (n + 1)) (x := e.symm q') (y := e.symm q)).1 hmk
      have hmem : e.symm q' - e.symm q ∈ I ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n) hmem_succ
      refine ⟨e.symm q' - e.symm q, hmem, ?_⟩
      ring)

/-- The positive-indexed topological inverse-limit equivalence with both
topologies fixed by their types. -/
noncomputable def adicPositiveQuotientInverseLimitHomeomorph
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    WithTopology R I.adicTopology ≃ₜ
      adicPositiveQuotientInverseLimit I := by
  letI : TopologicalSpace R := I.adicTopology
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ (n + 1)) := fun _ => ⊥
  let source := WithTopology.homeomorph
    (α := R) (topology := I.adicTopology)
  let algebraic := adicPositiveQuotientCompatibleFamiliesHomeomorph I
  let target := adicPositiveQuotientInverseLimitRepresentationHomeomorph I
  exact source.trans (algebraic.trans target.symm)

end Valuations
end LubinTate
