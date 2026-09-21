/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientReesAction
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientReesExact
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientSpecialFibre
import LeanPool.Stafford38.Stafford38.Characteristic.OrderReesTwoJet

/-!
# The filtered quotient two-jet module

This file constructs the concrete right module over the order-Rees two-jet.
The underlying additive quotient is the filtered Rees direct sum modulo the
image of the square of the successor shift.  The scalar ring is opposite, so
its action retains written right Weyl multiplication.

No trace theorem, minimal-prime statement, or Gabber theorem is asserted.
-/

namespace Stafford38.CharacteristicFilteredQuotientTwoJet

open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotientRees
open Stafford38.CharacteristicFilteredQuotientReesAction
open Stafford38.CharacteristicFilteredQuotientReesExact
open Stafford38.CharacteristicFilteredQuotientSpecialFibre
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylOrderRees

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

local instance quotientOrderAssociatedGradedSymbolModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (Stafford38.Characteristic.SymbolRing k n)
      (Stafford38.CharacteristicFilteredQuotientGraded.QuotientOrderAssociatedGraded k I) :=
  inferInstanceAs (Module (Stafford38.Characteristic.SymbolRing k n)
    (OrderAssociatedGradedModule k I))

local instance filteredRightQuotientSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (PresentedWeyl k n)ᵐᵒᵖ
      (Stafford38.CharacteristicFilteredQuotient.FilteredRightQuotient k I) :=
  filteredRightQuotientOpSMul k I

local instance filteredRightQuotientModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (PresentedWeyl k n)ᵐᵒᵖ
      (Stafford38.CharacteristicFilteredQuotient.FilteredRightQuotient k I) :=
  filteredRightQuotientOpModule k I

local instance orderPieceOpGradedMonoid :
    SetLike.GradedMonoid
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k) where
  one_mem := by
    rw [mem_orderPieceOp_iff]
    exact (Stafford38.CharacteristicAssociatedGradedModule.orderPieceOne
      (n := n) k).property
  mul_mem := by
    intro N M y z hy hz
    rw [mem_orderPieceOp_iff] at hy hz ⊢
    rw [MulOpposite.unop_mul]
    simpa [Nat.add_comm] using
      Stafford38.WeylFiltration.mul_mem_orderPiece k hz hy

local instance orderPieceOpGradedSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SetLike.GradedSMul
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k)
      (Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I) where
  smul_mem := by
    intro M N y q hy hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [mem_orderPieceOp_iff] at hy
    refine ⟨z * y.unop, ?_, ?_⟩
    · simpa [Nat.add_comm] using
        Stafford38.WeylFiltration.mul_mem_orderPiece k hz hy
    rfl

/-!
Lean 4.33 matches instance arguments only up to instance transparency, so
Mathlib's internal graded-module chain no longer derives from the
`SetLike.GradedSMul` above: the `VAdd ℕ ℕ` it picks is the one derived from
`Add`, not from `AddAction`.  These are Mathlib's own constructions written in
this file's shape, exactly as already done in `FilteredQuotientReesAction`.
-/

local instance orderPieceOpGMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    GradedMonoid.GMulAction
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { SetLike.toGSMul
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k)
      (Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I) with
    one_smul := fun ⟨_i, _m⟩ =>
      Sigma.subtype_ext (zero_vadd _ _) (one_smul _ _)
    mul_smul := fun ⟨_i, _a⟩ ⟨_j, _a'⟩ ⟨_l, _b⟩ =>
      Sigma.subtype_ext (add_vadd _ _ _) (mul_smul _ _ _) }

local instance orderPieceOpGdistribMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.GdistribMulAction
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { orderPieceOpGMulAction (n := n) k I with
    smul_add := fun _a _b _c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun _a => Subtype.ext <| smul_zero _ }

local instance orderPieceOpGmodule
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.Gmodule
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { orderPieceOpGdistribMulAction (n := n) k I with
    add_smul := fun _a _a' _b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun _b => Subtype.ext <| zero_smul _ _ }

/-- The image of the square of the Rees-parameter shift. -/
def quotientOrderReesTwoJetSubmodule
    (I : RightIdeal (PresentedWeyl k n)) :
    Submodule k (QuotientOrderReesModule k I) :=
  LinearMap.range
    ((quotientOrderReesShift k I).comp (quotientOrderReesShift k I))

/-- The filtered quotient direct sum modulo the action of `T²`. -/
abbrev FilteredQuotientTwoJet
    (I : RightIdeal (PresentedWeyl k n)) :=
  QuotientOrderReesModule k I ⧸ quotientOrderReesTwoJetSubmodule k I

/-- `Module.ofMinimalAxioms` below states its conclusion over the additive
monoid derived from `AddCommGroup`, while the quotient's own additive monoid
is `Submodule.Quotient.addCommMonoid`.  Under Lean 4.33's instance
transparency those are no longer interchangeable, so `add_smul`, `neg_smul`
and `mul_smul` would not apply to the source action.  Aligning the monoid here
is the same repair made for the filtered quotient itself. -/
instance (priority := 10000) filteredQuotientTwoJetAddCommMonoid
    (I : RightIdeal (PresentedWeyl k n)) :
    AddCommMonoid (FilteredQuotientTwoJet k I) :=
  AddCommGroup.toAddCommMonoid

/-- The canonical quotient map onto the module two-jet. -/
def filteredQuotientTwoJetQuotient
    (I : RightIdeal (PresentedWeyl k n)) :
    QuotientOrderReesModule k I →ₗ[k] FilteredQuotientTwoJet k I :=
  (quotientOrderReesTwoJetSubmodule k I).mkQ

@[simp] theorem filteredQuotientTwoJetQuotient_apply
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) :
    filteredQuotientTwoJetQuotient k I x = Submodule.Quotient.mk x :=
  rfl

private theorem oppositeOrderPieceSum_smul_comm
    (I : RightIdeal (PresentedWeyl k n))
    (r : OppositeOrderPieceSum (n := n) k) (a : k)
    (x : QuotientOrderReesModule k I) :
    r • (a • x) = a • (r • x) := by
  induction r using DirectSum.induction_on with
  | zero => simp
  | of M y =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | of N q =>
          rw [← DirectSum.of_smul]
          rw [DirectSum.Gmodule.of_smul_of,
            DirectSum.Gmodule.of_smul_of]
          rw [← DirectSum.of_smul]
          congr 1
          apply Subtype.ext
          exact (filteredRightMul k I y.val.unop).map_smul a q
      | add x z hx hz =>
          simpa only [smul_add, map_add] using congrArg₂ (fun p q => p + q) hx hz
  | add r s hr hs =>
      simpa only [add_smul, smul_add, map_add] using congrArg₂ (fun p q => p + q) hr hs

local instance quotientOrderReesModule_smulCommClass
    (I : RightIdeal (PresentedWeyl k n)) :
    SMulCommClass (OrderReesRing (n := n) k)ᵐᵒᵖ k
      (QuotientOrderReesModule k I) where
  smul_comm r a x := by
    change
      (orderPieceOpDirectSumEquivReesOp (n := n) k).symm r • (a • x) =
        a • ((orderPieceOpDirectSumEquivReesOp (n := n) k).symm r • x)
    exact oppositeOrderPieceSum_smul_comm k I _ _ _

theorem op_smul_mem_quotientOrderReesTwoJetSubmodule
    (I : RightIdeal (PresentedWeyl k n))
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ)
    {x : QuotientOrderReesModule k I}
    (hx : x ∈ quotientOrderReesTwoJetSubmodule k I) :
    r • x ∈ quotientOrderReesTwoJetSubmodule k I := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨r • y, ?_⟩
  change quotientOrderReesShift k I (quotientOrderReesShift k I (r • y)) =
    r • quotientOrderReesShift k I (quotientOrderReesShift k I y)
  calc
    quotientOrderReesShift k I (quotientOrderReesShift k I (r • y)) =
        quotientOrderReesShift k I
          (r • quotientOrderReesShift k I y) := by
      congr 1
      simpa only [MulOpposite.op_unop,
        orderReesParameter_op_smul_eq_shift] using
        (orderReesParameter_op_smul_comm k I r.unop y)
    _ = r • quotientOrderReesShift k I
        (quotientOrderReesShift k I y) := by
      simpa only [MulOpposite.op_unop,
        orderReesParameter_op_smul_eq_shift] using
        (orderReesParameter_op_smul_comm k I r.unop
          (quotientOrderReesShift k I y))

/-- The source opposite-Rees action descends to the additive two-jet
quotient. -/
def quotientOrderReesSourceAction
    (I : RightIdeal (PresentedWeyl k n))
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) :
    FilteredQuotientTwoJet k I →ₗ[k] FilteredQuotientTwoJet k I :=
  (quotientOrderReesTwoJetSubmodule k I).mapQ
    (quotientOrderReesTwoJetSubmodule k I)
    (DistribSMul.toLinearMap k (QuotientOrderReesModule k I) r)
    (by
      intro x hx
      exact op_smul_mem_quotientOrderReesTwoJetSubmodule k I r hx)

@[simp] theorem quotientOrderReesSourceAction_mk
    (I : RightIdeal (PresentedWeyl k n))
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ)
    (x : QuotientOrderReesModule k I) :
    quotientOrderReesSourceAction k I r (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (r • x) :=
  rfl

/-- The inherited source-Rees scalar multiplication on the two-jet
quotient. -/
def filteredQuotientTwoJetSourceSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (OrderReesRing (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  ⟨fun r x => quotientOrderReesSourceAction k I r x⟩

/-! The scalar multiplication is deliberately *not* registered as a separate
instance.  Registering it alongside the module below gives two syntactically
different routes to the same `SMul`, and under Lean 4.33 `add_smul`,
`neg_smul` and `mul_smul` then fail to rewrite goals stated through the
standalone route.  The module instance supplies the action. -/

/-- Before scalar factorization, the module two-jet is an honest module over
the opposite source Rees ring. -/
def filteredQuotientTwoJetSourceModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (OrderReesRing (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  letI : SMul (OrderReesRing (n := n) k)ᵐᵒᵖ (FilteredQuotientTwoJet k I) :=
    filteredQuotientTwoJetSourceSMul k I
  Module.ofMinimalAxioms
    (fun r x y => by
      refine Submodule.Quotient.induction_on _ x ?_
      intro x
      refine Submodule.Quotient.induction_on _ y ?_
      intro y
      change Submodule.Quotient.mk (r • (x + y)) = _
      rw [smul_add]
      rfl)
    (fun r s x => by
      refine Submodule.Quotient.induction_on _ x ?_
      intro x
      change Submodule.Quotient.mk ((r + s) • x) = _
      rw [add_smul]
      rfl)
    (fun r s x => by
      refine Submodule.Quotient.induction_on _ x ?_
      intro x
      change Submodule.Quotient.mk ((r * s) • x) = _
      rw [mul_smul]
      rfl)
    (fun x => by
      refine Submodule.Quotient.induction_on _ x ?_
      intro x
      change Submodule.Quotient.mk ((1 :
        (OrderReesRing (n := n) k)ᵐᵒᵖ) • x) = _
      rw [one_smul]
      )

local instance filteredQuotientTwoJetSourceModuleInstance
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (OrderReesRing (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  filteredQuotientTwoJetSourceModule k I

@[simp] theorem source_op_smul_mk
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k)
    (x : QuotientOrderReesModule k I) :
    MulOpposite.op r • (Submodule.Quotient.mk x :
      FilteredQuotientTwoJet k I) =
        Submodule.Quotient.mk (MulOpposite.op r • x) :=
  rfl

theorem source_parameter_sq_op_smul_eq_zero
    (I : RightIdeal (PresentedWeyl k n))
    (x : FilteredQuotientTwoJet k I) :
    MulOpposite.op (orderReesParameter (n := n) k ^ 2) • x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rw [source_op_smul_mk]
  rw [show MulOpposite.op (orderReesParameter (n := n) k ^ 2) =
      MulOpposite.op (orderReesParameter (n := n) k) *
        MulOpposite.op (orderReesParameter (n := n) k) by
    apply MulOpposite.unop_injective
    simp [pow_two]]
  rw [mul_smul, orderReesParameter_op_smul_eq_shift,
    orderReesParameter_op_smul_eq_shift]
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- The source elements acting by zero on the module two-jet form a
two-sided ideal. -/
def quotientOrderReesTwoJetAnnihilator
    (I : RightIdeal (PresentedWeyl k n)) :
    TwoSidedIdeal (OrderReesRing (n := n) k) :=
  TwoSidedIdeal.mk'
    {r | ∀ x : FilteredQuotientTwoJet k I, MulOpposite.op r • x = 0}
    (by intro x; exact zero_smul _ x)
    (by
      intro r s hr hs x
      rw [MulOpposite.op_add, add_smul, hr x, hs x, add_zero])
    (by
      intro r hr x
      rw [MulOpposite.op_neg, neg_smul, hr x, neg_zero])
    (by
      intro r s hs x
      rw [MulOpposite.op_mul, mul_smul, hs])
    (by
      intro r s hr x
      rw [MulOpposite.op_mul, mul_smul, hr, smul_zero])

theorem orderReesTwoJetIdeal_le_moduleAnnihilator
    (I : RightIdeal (PresentedWeyl k n)) :
    orderReesTwoJetIdeal (n := n) k ≤
      quotientOrderReesTwoJetAnnihilator k I := by
  intro r hr
  rw [orderReesTwoJetIdeal, TwoSidedIdeal.mem_span_iff] at hr
  apply hr (quotientOrderReesTwoJetAnnihilator k I)
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  subst z
  change ∀ x : FilteredQuotientTwoJet k I,
    MulOpposite.op (orderReesParameter (n := n) k ^ 2 - 0) • x = 0
  simpa using source_parameter_sq_op_smul_eq_zero k I

theorem source_op_smul_eq_zero_of_mem_twoJetIdeal
    (I : RightIdeal (PresentedWeyl k n))
    {r : OrderReesRing (n := n) k}
    (hr : r ∈ orderReesTwoJetIdeal (n := n) k)
    (x : FilteredQuotientTwoJet k I) :
    MulOpposite.op r • x = 0 := by
  have h := orderReesTwoJetIdeal_le_moduleAnnihilator k I hr
  change ∀ y : FilteredQuotientTwoJet k I,
    MulOpposite.op (r - 0) • y = 0 at h
  simpa only [sub_zero] using h x

/-- Action of one opposite two-jet scalar, obtained by factoring the source
right action through the two-sided `T²` quotient. -/
def quotientOrderReesTwoJetAction
    (I : RightIdeal (PresentedWeyl k n))
    (q : (OrderReesTwoJet (n := n) k)ᵐᵒᵖ) :
    FilteredQuotientTwoJet k I →ₗ[k] FilteredQuotientTwoJet k I :=
  Quotient.lift
    (fun r : OrderReesRing (n := n) k =>
      quotientOrderReesSourceAction k I (MulOpposite.op r))
    (by
      intro r s hrs
      apply LinearMap.ext
      intro x
      have hrs' : r - s ∈ orderReesTwoJetIdeal (n := n) k :=
        ((orderReesTwoJetIdeal (n := n) k).rel_iff r s).mp hrs
      have hzero := source_op_smul_eq_zero_of_mem_twoJetIdeal k I hrs' x
      rw [MulOpposite.op_sub, sub_smul] at hzero
      exact sub_eq_zero.mp hzero)
    q.unop

@[simp] theorem quotientOrderReesTwoJetAction_quotient
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k) :
    quotientOrderReesTwoJetAction k I
        (MulOpposite.op (orderReesTwoJetQuotient (n := n) k r)) =
      quotientOrderReesSourceAction k I (MulOpposite.op r) :=
  rfl

/-- Scalar multiplication by the opposite order-Rees two-jet. -/
def filteredQuotientTwoJetSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (OrderReesTwoJet (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  ⟨fun q x => quotientOrderReesTwoJetAction k I q x⟩

/-! As for the source action above, this scalar multiplication is not
registered as a separate instance: the module instance below is the single
route to it, so that `mul_smul` and friends rewrite. -/

private theorem exists_twoJet_op_representative
    (q : (OrderReesTwoJet (n := n) k)ᵐᵒᵖ) :
    ∃ r : OrderReesRing (n := n) k,
      q = MulOpposite.op (orderReesTwoJetQuotient (n := n) k r) := by
  obtain ⟨r, hr⟩ := Quotient.mk''_surjective q.unop
  refine ⟨r, ?_⟩
  rw [← MulOpposite.op_unop q]
  apply congrArg MulOpposite.op
  exact hr.symm

/-- The concrete module two-jet is a right module over the order-Rees
two-jet, represented as a left module over the opposite ring. -/
def filteredQuotientTwoJetModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (OrderReesTwoJet (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  letI : SMul (OrderReesTwoJet (n := n) k)ᵐᵒᵖ (FilteredQuotientTwoJet k I) :=
    filteredQuotientTwoJetSMul k I
  Module.ofMinimalAxioms
    (fun q x y => (quotientOrderReesTwoJetAction k I q).map_add x y)
    (fun q s x => by
      obtain ⟨r, rfl⟩ := exists_twoJet_op_representative (n := n) k q
      obtain ⟨t, rfl⟩ := exists_twoJet_op_representative (n := n) k s
      change MulOpposite.op (r + t) • x =
        MulOpposite.op r • x + MulOpposite.op t • x
      rw [MulOpposite.op_add, add_smul])
    (fun q s x => by
      obtain ⟨r, rfl⟩ := exists_twoJet_op_representative (n := n) k q
      obtain ⟨t, rfl⟩ := exists_twoJet_op_representative (n := n) k s
      change MulOpposite.op (t * r) • x =
        MulOpposite.op r • (MulOpposite.op t • x)
      rw [MulOpposite.op_mul, mul_smul])
    (fun x => by
      change MulOpposite.op (1 : OrderReesRing (n := n) k) • x = x
      rw [MulOpposite.op_one, one_smul])

noncomputable instance filteredQuotientTwoJetModuleInstance
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (OrderReesTwoJet (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  filteredQuotientTwoJetModule k I

@[simp] theorem twoJet_quotient_op_smul_mk
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k)
    (x : QuotientOrderReesModule k I) :
    MulOpposite.op (orderReesTwoJetQuotient (n := n) k r) •
        (Submodule.Quotient.mk x : FilteredQuotientTwoJet k I) =
      Submodule.Quotient.mk (MulOpposite.op r • x) :=
  rfl

@[simp] theorem twoJet_op_smul_mk
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k)
    (x : QuotientOrderReesModule k I) :
    MulOpposite.op (orderReesTwoJetQuotient (n := n) k r) •
        (Submodule.Quotient.mk x : FilteredQuotientTwoJet k I) =
      Submodule.Quotient.mk (MulOpposite.op r • x) :=
  rfl

/-- Action of the square-zero two-jet parameter. -/
def quotientOrderReesTwoJetCAct
    (I : RightIdeal (PresentedWeyl k n)) :
    FilteredQuotientTwoJet k I →ₗ[k] FilteredQuotientTwoJet k I :=
  quotientOrderReesTwoJetAction k I
    (MulOpposite.op (orderReesTwoJetParameter (n := n) k))

theorem quotientOrderReesTwoJetCAct_apply
    (I : RightIdeal (PresentedWeyl k n))
    (x : FilteredQuotientTwoJet k I) :
    quotientOrderReesTwoJetCAct k I x =
      MulOpposite.op (orderReesTwoJetParameter (n := n) k) • x :=
  rfl

@[simp] theorem quotientOrderReesTwoJetCAct_mk
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) :
    quotientOrderReesTwoJetCAct k I (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (quotientOrderReesShift k I x) := by
  rw [quotientOrderReesTwoJetCAct_apply, orderReesTwoJetParameter,
    twoJet_op_smul_mk, orderReesParameter_op_smul_eq_shift]

theorem quotientOrderReesTwoJetCAct_sq_eq_zero
    (I : RightIdeal (PresentedWeyl k n))
    (x : FilteredQuotientTwoJet k I) :
    quotientOrderReesTwoJetCAct k I
        (quotientOrderReesTwoJetCAct k I x) = 0 := by
  change MulOpposite.op (orderReesTwoJetParameter (n := n) k) •
      (MulOpposite.op (orderReesTwoJetParameter (n := n) k) • x) = 0
  rw [← mul_smul]
  have hc : MulOpposite.op (orderReesTwoJetParameter (n := n) k) *
      MulOpposite.op (orderReesTwoJetParameter (n := n) k) = 0 := by
    apply MulOpposite.unop_injective
    simpa [pow_two] using orderReesTwoJetParameter_sq (n := n) k
  rw [hc, zero_smul]

/-- Exactness of the square-zero parameter on the module two-jet. -/
theorem quotientOrderReesTwoJetCAct_ker_eq_range
    (I : RightIdeal (PresentedWeyl k n)) :
    LinearMap.ker (quotientOrderReesTwoJetCAct k I) =
      LinearMap.range (quotientOrderReesTwoJetCAct k I) := by
  apply le_antisymm
  · intro q hq
    refine Submodule.Quotient.induction_on _ q ?_ hq
    intro x hx
    rw [LinearMap.mem_ker, quotientOrderReesTwoJetCAct_mk] at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    have hshift : quotientOrderReesShift k I y = x := by
      apply quotientOrderReesShift_injective k I
      simpa [LinearMap.comp_apply] using hy
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [quotientOrderReesTwoJetCAct_mk, hshift]
  · intro q hq
    obtain ⟨x, rfl⟩ := hq
    rw [LinearMap.mem_ker]
    exact quotientOrderReesTwoJetCAct_sq_eq_zero k I x

/-- Specialization of the module two-jet to the actual associated graded
module. -/
def filteredQuotientTwoJetRho
    (I : RightIdeal (PresentedWeyl k n)) :
    FilteredQuotientTwoJet k I →ₗ[k] OrderAssociatedGradedModule k I :=
  (quotientOrderReesTwoJetSubmodule k I).liftQ
    (quotientOrderReesToAssociatedGraded k I)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      have hcomp := LinearMap.congr_fun
        (quotientOrderReesToAssociatedGraded_comp_shift k I)
        (quotientOrderReesShift k I y)
      show quotientOrderReesToAssociatedGraded k I _ = 0
      simpa [LinearMap.comp_apply] using hcomp)

@[simp] theorem filteredQuotientTwoJetRho_mk
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) :
    filteredQuotientTwoJetRho k I (Submodule.Quotient.mk x) =
      quotientOrderReesToAssociatedGraded k I x :=
  rfl

theorem filteredQuotientTwoJetRho_surjective
    (I : RightIdeal (PresentedWeyl k n)) :
    Function.Surjective (filteredQuotientTwoJetRho k I) := by
  intro g
  obtain ⟨x, hx⟩ := quotientOrderReesToAssociatedGraded_surjective k I g
  exact ⟨Submodule.Quotient.mk x, hx⟩

theorem filteredQuotientTwoJetRho_ker_eq_range_cAct
    (I : RightIdeal (PresentedWeyl k n)) :
    LinearMap.ker (filteredQuotientTwoJetRho k I) =
      LinearMap.range (quotientOrderReesTwoJetCAct k I) := by
  apply le_antisymm
  · intro q hq
    refine Submodule.Quotient.induction_on _ q ?_ hq
    intro x hx
    rw [LinearMap.mem_ker, filteredQuotientTwoJetRho_mk] at hx
    have hxker : x ∈ LinearMap.ker
        (quotientOrderReesToAssociatedGraded k I) :=
      LinearMap.mem_ker.mpr hx
    rw [quotientOrderReesToAssociatedGraded_ker_eq_range_shift] at hxker
    obtain ⟨y, hy⟩ := hxker
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [quotientOrderReesTwoJetCAct_mk, hy]
  · intro q hq
    obtain ⟨x, rfl⟩ := hq
    rw [LinearMap.mem_ker]
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    rw [quotientOrderReesTwoJetCAct_mk,
      filteredQuotientTwoJetRho_mk]
    have hcomp := LinearMap.congr_fun
      (quotientOrderReesToAssociatedGraded_comp_shift k I) y
    exact hcomp

private theorem source_specialization_compatible_of_of
    (I : RightIdeal (PresentedWeyl k n))
    {N M : ℕ} (q : Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N)
    (y : Stafford38.WeylFiltration.orderPiece k n M) :
    (quotientOrderReesToAssociatedGraded k I
        (MulOpposite.op (orderReesMonomial k M y) •
          DirectSum.of
            (fun L => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I L)
            N q) : OrderAssociatedGradedModule k I) =
      orderReesSpecialization (n := n) k (orderReesMonomial k M y) •
        (quotientOrderReesToAssociatedGraded k I
          (DirectSum.of
            (fun L => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I L)
            N q) : OrderAssociatedGradedModule k I) := by
  obtain ⟨z, hz, hq⟩ := q.property
  let zp : Stafford38.WeylFiltration.orderPiece k n N := ⟨z, hz⟩
  have hq' : q = Stafford38.CharacteristicFilteredQuotient.orderPieceToQuotientPiece
      k I N zp := by
    apply Subtype.ext
    exact hq.symm
  subst q
  rw [orderReesMonomial_op_smul_of,
    quotientOrderReesToAssociatedGraded_of,
    quotientOrderReesToAssociatedGraded_of,
    orderReesSpecialization_monomial]
  change Stafford38.CharacteristicAssociatedGradedModule.orderAssociatedGradedOf
      k I (M + N)
        (Stafford38.CharacteristicFilteredQuotient.orderPieceToQuotientGraded
          k I (M + N)
          ⟨(zp : PresentedWeyl k n) * y,
            by simpa [Nat.add_comm] using
              Stafford38.WeylFiltration.mul_mem_orderPiece k
                zp.property y.property⟩) =
    (Stafford38.WeylAssociatedGraded.principalComponentOnPiece k
        (@Stafford38.WeylFiltration.orderWeight n) M y :
      Stafford38.Characteristic.SymbolRing k n) •
      Stafford38.CharacteristicAssociatedGradedModule.orderAssociatedGradedOf
        k I N
          (Stafford38.CharacteristicFilteredQuotient.orderPieceToQuotientGraded
            k I N zp)
  rw [Stafford38.CharacteristicAssociatedGradedModule.smul_orderAssociatedGradedOf_mk_eq_of_mul]
  apply (orderAssociatedGradedLinearEquivCharacteristic k I).injective
  rw [orderAssociatedGradedLinearEquivCharacteristic_of_mk,
    orderAssociatedGradedLinearEquivCharacteristic_of_mk]
  congr 1
  change Stafford38.WeylLeadingSymbol.presentedPrincipalComponent k
      (@Stafford38.WeylFiltration.orderWeight n) (M + N)
        ((zp : PresentedWeyl k n) * (y : PresentedWeyl k n)) =
    Stafford38.WeylLeadingSymbol.presentedPrincipalComponent k
      (@Stafford38.WeylFiltration.orderWeight n) (N + M)
        ((zp : PresentedWeyl k n) * (y : PresentedWeyl k n))
  rw [Nat.add_comm M N]

private theorem source_specialization_compatible_directSum
    (I : RightIdeal (PresentedWeyl k n))
    (s : OppositeOrderPieceSum (n := n) k)
    (x : QuotientOrderReesModule k I) :
    (quotientOrderReesToAssociatedGraded k I
        ((orderPieceOpDirectSumEquivReesOp (n := n) k s) • x) :
      OrderAssociatedGradedModule k I) =
      orderReesSpecialization (n := n) k
          (orderPieceOpDirectSumEquivReesOp (n := n) k s).unop •
        (quotientOrderReesToAssociatedGraded k I x :
          OrderAssociatedGradedModule k I) := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of M y =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | of N q =>
          let yp : Stafford38.WeylFiltration.orderPiece k n M :=
            ⟨y.val.unop,
              (mem_orderPieceOp_iff (n := n) k M y.val).mp y.property⟩
          rw [show orderPieceOpDirectSumEquivReesOp (n := n) k
              (DirectSum.of
                (fun L => CharacteristicFilteredQuotientReesAction.orderPieceOp
                  (n := n) k L) M y) =
                orderPieceOpToReesOp (n := n) k M y from
              orderPieceOpDirectSumToReesOp_of (n := n) k M y]
          change (quotientOrderReesToAssociatedGraded k I
              (MulOpposite.op (orderReesMonomial k M yp) •
                DirectSum.of
                  (fun L =>
                    Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece
                      k I L) N q) :
                OrderAssociatedGradedModule k I) =
            orderReesSpecialization (n := n) k
                (orderReesMonomial k M yp) •
              (quotientOrderReesToAssociatedGraded k I
                (DirectSum.of
                  (fun L =>
                    Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece
                      k I L) N q) :
                OrderAssociatedGradedModule k I)
          exact source_specialization_compatible_of_of k I q yp
      | add x y hx hy =>
          simpa [smul_add, map_add] using
            congrArg₂ (fun p q => p + q) hx hy
  | add s t hs ht =>
      simpa [map_add, add_smul] using
        congrArg₂ (fun p q => p + q) hs ht

/-- The source order-Rees action specializes to the symbol-ring action on
the actual associated graded module. -/
theorem quotientOrderReesToAssociatedGraded_action_compatibility
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k)
    (x : QuotientOrderReesModule k I) :
    (quotientOrderReesToAssociatedGraded k I
        (MulOpposite.op r • x) : OrderAssociatedGradedModule k I) =
      orderReesSpecialization (n := n) k r •
        (quotientOrderReesToAssociatedGraded k I x :
          OrderAssociatedGradedModule k I) := by
  let s := (orderPieceOpDirectSumEquivReesOp (n := n) k).symm
    (MulOpposite.op r)
  have hs := source_specialization_compatible_directSum k I s x
  have heq : orderPieceOpDirectSumEquivReesOp (n := n) k s =
      MulOpposite.op r := by
    exact (orderPieceOpDirectSumEquivReesOp (n := n) k).apply_symm_apply _
  rw [heq] at hs
  simpa only [MulOpposite.unop_op] using hs

/-- The factored two-jet action and the actual associated-graded
specialization are compatible. -/
theorem filteredQuotientTwoJetRho_action_compatibility
    (I : RightIdeal (PresentedWeyl k n))
    (b : OrderReesTwoJet (n := n) k)
    (m : FilteredQuotientTwoJet k I) :
    filteredQuotientTwoJetRho k I (MulOpposite.op b • m) =
      orderReesTwoJetSpecialization (n := n) k b •
        filteredQuotientTwoJetRho k I m := by
  obtain ⟨r, hr⟩ := exists_twoJet_op_representative (n := n) k
    (MulOpposite.op b)
  have hb : b = orderReesTwoJetQuotient (n := n) k r := by
    simpa using congrArg MulOpposite.unop hr
  rw [hb]
  refine Submodule.Quotient.induction_on _ m ?_
  intro x
  rw [twoJet_op_smul_mk, filteredQuotientTwoJetRho_mk,
    filteredQuotientTwoJetRho_mk,
    orderReesTwoJetSpecialization_quotient]
  exact quotientOrderReesToAssociatedGraded_action_compatibility k I r x


end

end Stafford38.CharacteristicFilteredQuotientTwoJet
