/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.Stafford38.Weyl.PresentedScalarExtension
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Basis


/-!
# Filtered scalar lifting for the presented Weyl algebra

This file isolates the filtered linear-algebra step which is not supplied by
unfiltered PBW spanning.  The point is that an element of the intersection of
two scalar-extended subspaces has a bounded source representative.  The proof
uses the exact kernel statement for tensoring a quotient map; no target
initial generators and no strictness assertion are used.

The small finite-dimensional example at the end records the cancellation
falsifier: an arbitrary high-degree representation need not be termwise
bounded, even though a bounded representation exists.
-/

@[expose] public section

namespace Stafford38.Weyl.FilteredScalarLifting

open scoped TensorProduct

open Stafford
open AlgebraicAnalysis
open Stafford38.Characteristic
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylUniversal
open Stafford38.WeylEulerResidue
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.Weyl.PresentedScalarExtension

noncomputable section


universe u v

variable {R S M : Type*}

section RangeBaseChange

variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/- The image of the tensor extension of a subtype is exactly the submodule
   base-change defined by `Submodule.baseChange`. -/
theorem range_baseChange_subtype (p : Submodule R M) :
    LinearMap.range (p.subtype.baseChange S) = p.baseChange S :=
  rfl

end RangeBaseChange

section FilteredIntersection

variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

example [SMulCommClass R S S] :
    Module S (S ⊗[R] M) := by infer_instance

theorem baseChange_mono
    {p q : Submodule R M} (hpq : p ≤ q) :
    p.baseChange S ≤ q.baseChange S := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span]
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨m, hm, rfl⟩
  exact Submodule.subset_span ⟨m, hpq hm, rfl⟩

/-!
Tensoring with a flat coefficient module preserves intersections of
submodules.  The proof is deliberately phrased through the quotient map of
`q`: the reverse inclusion is a kernel statement, not an appeal to an
unfiltered spanning equality.
-/
theorem baseChange_inf_eq [SMulCommClass R S S]
    [Module.Flat R S] (p q : Submodule R M) :
    p.baseChange S ⊓ q.baseChange S = (p ⊓ q).baseChange S := by
  apply le_antisymm
  · intro z hz
    let f : p →ₗ[R] M ⧸ q := q.mkQ.comp p.subtype
    have hqzero :
        TensorProduct.AlgebraTensorModule.lTensor S S q.mkQ z = 0 := by
      have hzq := hz.2
      rw [Submodule.baseChange_eq_span] at hzq
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hzq
      · intro a ha
        rcases ha with ⟨m, hm, rfl⟩
        have hmker : m ∈ LinearMap.ker q.mkQ := by
          rw [Submodule.ker_mkQ q]
          exact hm
        change (1 : S) ⊗ₜ[R] q.mkQ m = 0
        rw [LinearMap.mem_ker.mp hmker]
        simp
      · simp
      · intro a b _ _ ha hb
        simp only [map_add, ha, hb, add_zero]
      · intro c a _ ha
        simp only [map_smul, ha, smul_zero]
    have hpRange : z ∈ LinearMap.range (p.subtype.baseChange S) := by
      rw [range_baseChange_subtype p]
      exact hz.1
    obtain ⟨y, hy⟩ := hpRange
    change TensorProduct.AlgebraTensorModule.lTensor S S p.subtype y = z at hy
    have hyker : y ∈ LinearMap.ker
        (TensorProduct.AlgebraTensorModule.lTensor S S f) := by
      apply LinearMap.mem_ker.mpr
      calc
        TensorProduct.AlgebraTensorModule.lTensor S S f y =
            TensorProduct.AlgebraTensorModule.lTensor S S q.mkQ
              (TensorProduct.AlgebraTensorModule.lTensor S S p.subtype y) := by
                rw [TensorProduct.AlgebraTensorModule.lTensor_comp]
                rfl
        _ = TensorProduct.AlgebraTensorModule.lTensor S S q.mkQ z := by
              rw [hy]
        _ = 0 := hqzero
    have hyspan : y ∈
        LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor S S
          (LinearMap.ker f).subtype) := by
      rw [← Module.Flat.ker_lTensor_eq (S := S) (M := S) f]
      exact hyker
    obtain ⟨v, hv⟩ := hyspan
    change (LinearMap.ker f).subtype.baseChange S v = y at hv
    let g : LinearMap.ker f →ₗ[R] ↥(p ⊓ q) :=
      { toFun := fun u =>
          ⟨(u : M), ⟨u.1.property, by
            have hu : (u : M) ∈ LinearMap.ker q.mkQ := by
              change q.mkQ (u : M) = 0
              exact u.property
            exact Eq.mp (congrArg (fun r : Submodule R M => (u : M) ∈ r)
              (Submodule.ker_mkQ q)) hu⟩⟩
        map_add' := by
          intro u v
          ext
          simp
        map_smul' := by
          intro a u
          ext
          simp }
    have hcomp :
        p.subtype.comp (LinearMap.ker f).subtype =
          (p ⊓ q).subtype.comp g := by
      ext u
      rfl
    have hz' : z = (p ⊓ q).subtype.baseChange S
        (g.baseChange S v) := by
      calc
        z = p.subtype.baseChange S y := hy.symm
        _ = p.subtype.baseChange S
            ((LinearMap.ker f).subtype.baseChange S v) := by rw [hv]
        _ = (p.subtype.comp (LinearMap.ker f).subtype).baseChange S v := by
              rw [LinearMap.baseChange_comp]
              rfl
        _ = ((p ⊓ q).subtype.comp g).baseChange S v := by rw [hcomp]
        _ = (p ⊓ q).subtype.baseChange S (g.baseChange S v) := by
              rw [LinearMap.baseChange_comp]
              rfl
    rw [hz']
    rw [← range_baseChange_subtype (p ⊓ q)]
    exact ⟨g.baseChange S v, rfl⟩
  · intro z hz
    exact ⟨baseChange_mono inf_le_left hz,
      baseChange_mono inf_le_right hz⟩

end FilteredIntersection

section WeylTensorBridge

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-!
The two PBW bases identify the ordinary tensor base-change with the target
presented Weyl algebra.  This is the concrete bridge that turns the abstract
intersection theorem above into a bounded PBW decomposition.
-/
/-- The scalar-extension equivalence identifying the two presented Weyl algebras through their
PBW bases. -/
def pbwTensorEquiv (n : Nat) :
    (K ⊗[k] PresentedWeyl k n) ≃ₗ[K] PresentedWeyl K n :=
  (presentedPBWBasis k n).baseChange K |>.equiv
    (presentedPBWBasis K n) (Equiv.refl (PhaseVar n →₀ ℕ))

theorem pbwTensorEquiv_tmul_one (n : Nat) (z : PresentedWeyl k n) :
    pbwTensorEquiv (k := k) (K := K) n (1 ⊗ₜ[k] z) =
      presentedWeylScalarExtension (k := k) (K := K) n z := by
  let f : PresentedWeyl k n →ₗ[k] PresentedWeyl K n :=
    (pbwTensorEquiv (k := k) (K := K) n).toLinearMap.restrictScalars k |>.comp
      (TensorProduct.mk k K (PresentedWeyl k n) 1)
  have hf : f =
      (presentedWeylScalarExtension (k := k) (K := K) n).toLinearMap := by
    apply Module.Basis.ext (presentedPBWBasis k n)
    intro m
    dsimp [f]
    change pbwTensorEquiv (k := k) (K := K) n
        (1 ⊗ₜ[k] presentedPBWBasis k n m) =
      presentedWeylScalarExtension (k := k) (K := K) n
        (presentedPBWBasis k n m)
    rw [← Module.Basis.baseChange_apply, pbwTensorEquiv, Module.Basis.equiv_apply,
      presentedWeylScalarExtension_basis]
    rfl
  exact DFunLike.congr_fun hf z

theorem pbwTensorEquiv_map_orderPiece (n L : Nat) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) n).toLinearMap
        ((orderPiece k n L).baseChange K) =
      orderPiece K n L := by
  rw [orderPiece, presentedWeightPiece_eq_span,
    Submodule.baseChange_span, orderPiece,
    presentedWeightPiece_eq_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    rcases ha with ⟨m, hm, rfl⟩
    refine ⟨m, hm, ?_⟩
    calc
      (pbwTensorEquiv (k := k) (K := K) n)
          ((TensorProduct.mk k K (PresentedWeyl k n) 1)
            (presentedPBWBasis k n m)) =
          pbwTensorEquiv (k := k) (K := K) n
            (1 ⊗ₜ[k] presentedPBWBasis k n m) := rfl
      _ = presentedWeylScalarExtension (k := k) (K := K) n
          (presentedPBWBasis k n m) :=
        pbwTensorEquiv_tmul_one (k := k) (K := K) n
          (presentedPBWBasis k n m)
      _ = presentedPBWBasis K n m :=
        presentedWeylScalarExtension_basis (k := k) (K := K) n m
  · rintro ⟨m, hm, rfl⟩
    refine ⟨1 ⊗ₜ[k] presentedPBWBasis k n m,
      ⟨presentedPBWBasis k n m, ⟨m, hm, rfl⟩, rfl⟩, ?_⟩
    calc
      pbwTensorEquiv (k := k) (K := K) n
          (1 ⊗ₜ[k] presentedPBWBasis k n m) =
          presentedWeylScalarExtension (k := k) (K := K) n
            (presentedPBWBasis k n m) :=
        pbwTensorEquiv_tmul_one (k := k) (K := K) n
          (presentedPBWBasis k n m)
      _ = presentedPBWBasis K n m :=
        presentedWeylScalarExtension_basis (k := k) (K := K) n m

theorem pbwTensorEquiv_map_baseChange (n : Nat)
    (J : Submodule k (PresentedWeyl k n)) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) n).toLinearMap
        (J.baseChange K) =
      Submodule.span K
        (presentedWeylScalarExtension (k := k) (K := K) n ''
          (J : Set (PresentedWeyl k n))) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨m, hm, ?_⟩
    exact (pbwTensorEquiv_tmul_one (k := k) (K := K) n m).symm
  · rintro ⟨m, hm, rfl⟩
    refine ⟨1 ⊗ₜ[k] m, ⟨m, hm, rfl⟩, ?_⟩
    exact pbwTensorEquiv_tmul_one (k := k) (K := K) n m

theorem pbwTensorEquiv_map_rightIdeal (n : Nat)
    (I : RightIdeal (PresentedWeyl k n)) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) n).toLinearMap
        ((rightIdealKSubmodule k I).baseChange K) =
      scalarImageRightIdealSpan (k := k) (K := K) n I := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span,
    scalarImageRightIdealSpan]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨m, hm, ?_⟩
    exact (pbwTensorEquiv_tmul_one (k := k) (K := K) n m).symm
  · rintro ⟨m, hm, rfl⟩
    refine ⟨1 ⊗ₜ[k] m, ⟨m, hm, rfl⟩, ?_⟩
    exact pbwTensorEquiv_tmul_one (k := k) (K := K) n m

theorem pbwTensorEquiv_map_canonicalRightIdeal
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
        ((rightIdealKSubmodule k
          (canonicalRightIdeal (presentedCoordinate k n) d N)).baseChange K) =
      rightIdealKSubmodule K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) := by
  rw [pbwTensorEquiv_map_rightIdeal]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a, ha, rfl⟩
    exact presentedWeylScalarExtension_mem_canonicalRightIdeal
      (k := k) (K := K) n N ha
  · intro z hz
    exact target_canonicalRightIdeal_le_scalarImageRightIdealSpan
      (k := k) (K := K) n N d z hz

theorem pbwTensorEquiv_map_canonicalRightIdeal_inf_orderPiece
    (n N L : Nat) (d : PresentedWeyl k (n + 1)) :
    Submodule.map (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
        ((rightIdealKSubmodule k
          (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
          orderPiece k (n + 1) L).baseChange K) =
      rightIdealKSubmodule K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) ⊓
        orderPiece K (n + 1) L := by
  rw [← baseChange_inf_eq
      (R := k) (S := K)
      (rightIdealKSubmodule k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (orderPiece k (n + 1) L)]
  rw [Submodule.map_inf
      (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
      (pbwTensorEquiv (k := k) (K := K) (n + 1)).injective,
    pbwTensorEquiv_map_canonicalRightIdeal,
    pbwTensorEquiv_map_orderPiece]

theorem target_canonicalRightIdeal_orderPiece_mem_source_span
    (n N L : Nat) (d : PresentedWeyl k (n + 1))
    {z : PresentedWeyl K (n + 1)}
    (hzIdeal : z ∈ canonicalRightIdeal (presentedCoordinate K n)
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N)
    (hzOrder : z ∈ orderPiece K (n + 1) L) :
    z ∈ Submodule.span K
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) ''
    ((rightIdealKSubmodule k
          (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
          orderPiece k (n + 1) L) :
          Set (PresentedWeyl k (n + 1)))) := by
  let J : Submodule k (PresentedWeyl k (n + 1)) :=
    rightIdealKSubmodule k
      (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
      orderPiece k (n + 1) L
  change z ∈ Submodule.span K
    (presentedWeylScalarExtension (k := k) (K := K) (n + 1) ''
      (J : Set (PresentedWeyl k (n + 1))))
  rw [← pbwTensorEquiv_map_baseChange (k := k) (K := K) (n + 1) J]
  rw [pbwTensorEquiv_map_canonicalRightIdeal_inf_orderPiece]
  exact ⟨hzIdeal, hzOrder⟩

theorem target_canonicalRightIdeal_orderPiece_exists_fin_decomposition
    (n N L : Nat) (d : PresentedWeyl k (n + 1))
    {z : PresentedWeyl K (n + 1)}
    (hzIdeal : z ∈ canonicalRightIdeal (presentedCoordinate K n)
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N)
    (hzOrder : z ∈ orderPiece K (n + 1) L) :
    ∃ (r : Nat) (c : Fin r → K)
      (w : Fin r →
        ↥(rightIdealKSubmodule k
          (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
          orderPiece k (n + 1) L)),
      ∑ i, c i •
        presentedWeylScalarExtension (k := k) (K := K) (n + 1)
          (w i : PresentedWeyl k (n + 1)) = z := by
  classical
  have hzSpan := target_canonicalRightIdeal_orderPiece_mem_source_span
    (k := k) (K := K) n N L d hzIdeal hzOrder
  rcases (Submodule.mem_span_set').mp hzSpan with ⟨r, c, g, hg⟩
  let J : Submodule k (PresentedWeyl k (n + 1)) :=
    rightIdealKSubmodule k
      (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
      orderPiece k (n + 1) L
  let w : Fin r → J := fun i =>
    ⟨Classical.choose (g i).property,
      (Classical.choose_spec (g i).property).1⟩
  have hw (i : Fin r) :
      presentedWeylScalarExtension (k := k) (K := K) (n + 1)
          (w i : PresentedWeyl k (n + 1)) = (g i : PresentedWeyl K (n + 1)) :=
    (Classical.choose_spec (g i).property).2
  refine ⟨r, c, w, ?_⟩
  calc
    ∑ i, c i • presentedWeylScalarExtension (k := k) (K := K) (n + 1)
        (w i : PresentedWeyl k (n + 1)) =
        ∑ i, c i • (g i : PresentedWeyl K (n + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hw i]
    _ = z := hg

theorem target_orderInitialIdeal_le_map_source_orderInitialIdeal
    (n N : Nat) (d : PresentedWeyl k (n + 1)) :
    orderInitialIdeal K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N) ≤
      (orderInitialIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)).map
        (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom := by
  apply Ideal.span_le.mpr
  intro P hP
  rcases hP with ⟨L, z, hzOrder, hzIdeal, rfl⟩
  let I : RightIdeal (PresentedWeyl k (n + 1)) :=
    canonicalRightIdeal (presentedCoordinate k n) d N
  let IK : RightIdeal (PresentedWeyl K (n + 1)) :=
    canonicalRightIdeal (presentedCoordinate K n)
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) d) N
  let J : Submodule k (PresentedWeyl k (n + 1)) :=
    rightIdealKSubmodule k I ⊓ orderPiece k (n + 1) L
  have hzMap : z ∈ Submodule.map
      (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
        (J.baseChange K) := by
    change z ∈ Submodule.map
      (pbwTensorEquiv (k := k) (K := K) (n + 1)).toLinearMap
        ((rightIdealKSubmodule k
          (canonicalRightIdeal (presentedCoordinate k n) d N) ⊓
          orderPiece k (n + 1) L).baseChange K)
    rw [pbwTensorEquiv_map_canonicalRightIdeal_inf_orderPiece]
    exact ⟨hzIdeal, hzOrder⟩
  have hzSpan : z ∈ Submodule.span K
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) ''
        (J : Set (PresentedWeyl k (n + 1)))) := by
    rw [← pbwTensorEquiv_map_baseChange (k := k) (K := K) (n + 1) J]
    exact hzMap
  let M : Ideal (SymbolRing K (n + 1)) :=
    (orderInitialIdeal k I).map
      (symbolScalarExtension (k := k) (K := K) (n + 1)).toRingHom
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hzSpan
  · intro a ha
    rcases ha with ⟨w, hw, rfl⟩
    have hwOrder : w ∈ orderPiece k (n + 1) L := hw.2
    have hwIdeal : w ∈ I := hw.1
    have hsource : presentedPrincipalComponent k orderWeight L w ∈
        orderInitialIdeal k I := by
      exact orderPrincipalComponent_mem_initialIdeal k I w hwOrder hwIdeal
    have hmap : symbolScalarExtension (k := k) (K := K) (n + 1)
          (presentedPrincipalComponent k orderWeight L w) ∈ M := by
      exact Ideal.mem_map_of_mem _ hsource
    change presentedPrincipalComponent K orderWeight L
      (presentedWeylScalarExtension (k := k) (K := K) (n + 1) w) ∈ M
    rw [← presentedWeylScalarExtension_principalComponent
      (k := k) (K := K) (n + 1) orderWeight L w]
    exact hmap
  · simpa only [map_zero, SetLike.mem_coe] using M.zero_mem
  · intro a b _ _ ha hb
    simpa only [map_add, SetLike.mem_coe] using
      M.add_mem (SetLike.mem_coe.mp ha) (SetLike.mem_coe.mp hb)
  · intro c a _ ha
    rw [map_smul, Algebra.smul_def]
    exact Ideal.mul_mem_left M _ (SetLike.mem_coe.mp ha)

/-- Flat filtered lifting discharges the exact algebraic-closure descent
contract isolated by `PresentedScalarExtension`. -/
theorem filteredInitialLifting : FilteredInitialLifting.{u} := by
  intro k _ _ n N d
  exact target_orderInitialIdeal_le_map_source_orderInitialIdeal
    (k := k) (K := AlgebraicClosure k) n N d

/-- The scalar-extension input consumed by the terminal Stafford reduction is
therefore unconditional. -/
theorem canonicalSupportDescent :
    CanonicalSupportVanishingReduction.CanonicalSupportDescent.{u} :=
  canonicalSupportDescent_of_filteredInitialLifting filteredInitialLifting

section CancellationFalsifier

/-!
An unfiltered representation cannot be truncated term by term.  Here the
low piece is the first coordinate axis, while the source span is all of
`ℚ × ℚ`.  The displayed representation of `(1, 0)` has two summands outside
the low piece whose second coordinates cancel.  The preceding flat
intersection theorem is the surviving filtration-on-span replacement.
-/
theorem cancellation_falsifier :
    let F : Submodule ℚ (ℚ × ℚ) :=
      Submodule.span ℚ ({(1, 0)} : Set (ℚ × ℚ))
    let I : Submodule ℚ (ℚ × ℚ) :=
      Submodule.span ℚ ({(1, 1), (0, 1)} : Set (ℚ × ℚ))
    let z : ℚ × ℚ := (1, 0)
    z ∈ I ⊓ F ∧
      (1, 1) ∉ F ∧
      (0, 1) ∉ F ∧
      ((1, 1) : ℚ × ℚ) - ((0, 1) : ℚ × ℚ) = z := by
  dsimp
  let F : Submodule ℚ (ℚ × ℚ) :=
    Submodule.span ℚ ({(1, 0)} : Set (ℚ × ℚ))
  let I : Submodule ℚ (ℚ × ℚ) :=
    Submodule.span ℚ ({(1, 1), (0, 1)} : Set (ℚ × ℚ))
  have hzF : ((1, 0) : ℚ × ℚ) ∈ F := by
    apply Submodule.subset_span
    simp []
  have huI : ((1, 1) : ℚ × ℚ) ∈ I := by
    apply Submodule.subset_span
    simp []
  have hvI : ((0, 1) : ℚ × ℚ) ∈ I := by
    apply Submodule.subset_span
    simp []
  have hzI : ((1, 0) : ℚ × ℚ) ∈ I := by
    have hdiff := I.sub_mem huI hvI
    have heq : ((1, 1) : ℚ × ℚ) - ((0, 1) : ℚ × ℚ) = (1, 0) := by
      ext <;> norm_num
    rw [← heq]
    exact hdiff
  have huF : ((1, 1) : ℚ × ℚ) ∉ F := by
    intro hu
    change ((1, 1) : ℚ × ℚ) ∈
      Submodule.span ℚ ({(1, 0)} : Set (ℚ × ℚ)) at hu
    rw [Submodule.mem_span_singleton] at hu
    rcases hu with ⟨c, hc⟩
    have := congrArg Prod.snd hc
    simp at this
  have hvF : ((0, 1) : ℚ × ℚ) ∉ F := by
    intro hv
    change ((0, 1) : ℚ × ℚ) ∈
      Submodule.span ℚ ({(1, 0)} : Set (ℚ × ℚ)) at hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨c, hc⟩
    have := congrArg Prod.snd hc
    simp at this
  refine ⟨⟨hzI, hzF⟩, huF, hvF, ?_⟩
  ext <;> norm_num

end CancellationFalsifier

end WeylTensorBridge

/-- After scalar descent, the terminal theorem has exactly the three genuine
mathematical inputs: an order-zero unit coordinate predecessor, post-extension
symbol control, and the asymptotic Laurent conormal producer. -/
theorem universalStatement_of_three_inputs
    (hunit :
      CanonicalSupportVanishingReduction.CanonicalStrictUnitCoordinatePreimage.{u})
    (hcontrol :
      CanonicalSupportVanishingReduction.CanonicalLaurentSymbolControl.{u})
    (hasymptotic :
      CanonicalSupportVanishingReduction.CanonicalAsymptoticLaurentProducer.{u}) :
    Stafford38.UniversalStatement.{u} :=
  CanonicalSupportVanishingReduction.universalStatement_of_four_inputs
    hunit hcontrol hasymptotic canonicalSupportDescent

end
end Stafford38.Weyl.FilteredScalarLifting
