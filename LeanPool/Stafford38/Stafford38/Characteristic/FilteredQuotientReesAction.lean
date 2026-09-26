/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.OrderRees
public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientRees
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Algebra.Module.Equiv.Opposite


/-!
# The right order-Rees action on the filtered quotient

This file constructs the actual right action.  Scalars are taken in the
opposite of the order-Rees ring, so homogeneous scalar action is written
right Weyl multiplication and raises filtration degree additively.
-/

@[expose] public section

namespace Stafford38.CharacteristicFilteredQuotientReesAction

open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientRees
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylOrderRees

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-! ## The transparent right action on the additive quotient -/

/-- Right multiplication by a Weyl operator on the additive quotient. -/
def filteredRightMul (I : RightIdeal (PresentedWeyl k n))
    (y : PresentedWeyl k n) :
    FilteredRightQuotient k I →ₗ[k] FilteredRightQuotient k I :=
  (rightIdealKSubmodule k I).mapQ (rightIdealKSubmodule k I)
    { toFun := fun z => z * y
      map_add' := fun z w => add_mul z w y
      map_smul' := fun c z => Algebra.smul_mul_assoc c z y }
    (by
      intro z hz
      change z * y ∈ I
      exact I.smul_mem (MulOpposite.op y) hz)

@[simp]
theorem filteredRightMul_mk
    (I : RightIdeal (PresentedWeyl k n))
    (y z : PresentedWeyl k n) :
    filteredRightMul k I y (Submodule.Quotient.mk z) =
      (rightIdealKSubmodule k I).mkQ (z * y) :=
  rfl

@[simp]
theorem filteredRightMul_one
    (I : RightIdeal (PresentedWeyl k n))
    (q : FilteredRightQuotient k I) :
    filteredRightMul k I 1 q = q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro z
  change (rightIdealKSubmodule k I).mkQ (z * 1) =
    (rightIdealKSubmodule k I).mkQ z
  rw [mul_one]

/-- The right Weyl scalar action underlying the following module instance. -/
@[instance_reducible]
def filteredRightQuotientOpSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (PresentedWeyl k n)ᵐᵒᵖ (FilteredRightQuotient k I) :=
  ⟨fun y q => filteredRightMul k I y.unop q⟩

/-- The opposite Weyl action on the filtered right quotient. -/
local instance filteredRightQuotientSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (PresentedWeyl k n)ᵐᵒᵖ (FilteredRightQuotient k I) :=
  filteredRightQuotientOpSMul k I

/-- The additive quotient is an honest right module over the Weyl algebra. -/
@[instance_reducible]
def filteredRightQuotientOpModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (PresentedWeyl k n)ᵐᵒᵖ (FilteredRightQuotient k I) :=
  Module.ofMinimalAxioms
    (fun y q₁ q₂ => by
      refine Submodule.Quotient.induction_on _ q₁ ?_
      intro z
      refine Submodule.Quotient.induction_on _ q₂ ?_
      intro w
      change (rightIdealKSubmodule k I).mkQ ((z + w) * y.unop) = _
      rw [add_mul]
      change (rightIdealKSubmodule k I).mkQ (z * y.unop + w * y.unop) =
        (rightIdealKSubmodule k I).mkQ (z * y.unop) +
          (rightIdealKSubmodule k I).mkQ (w * y.unop)
      exact (rightIdealKSubmodule k I).mkQ.map_add _ _)
    (fun y₁ y₂ q => by
      refine Submodule.Quotient.induction_on _ q ?_
      intro z
      change (rightIdealKSubmodule k I).mkQ (z * (y₁ + y₂).unop) = _
      rw [MulOpposite.unop_add, mul_add]
      change (rightIdealKSubmodule k I).mkQ
          (z * y₁.unop + z * y₂.unop) =
        (rightIdealKSubmodule k I).mkQ (z * y₁.unop) +
          (rightIdealKSubmodule k I).mkQ (z * y₂.unop)
      exact (rightIdealKSubmodule k I).mkQ.map_add _ _)
    (fun y₁ y₂ q => by
      refine Submodule.Quotient.induction_on _ q ?_
      intro z
      change (rightIdealKSubmodule k I).mkQ (z * (y₁ * y₂).unop) = _
      rw [MulOpposite.unop_mul]
      change (rightIdealKSubmodule k I).mkQ (z * (y₂.unop * y₁.unop)) =
        (rightIdealKSubmodule k I).mkQ ((z * y₂.unop) * y₁.unop)
      rw [mul_assoc])
    (fun q => by
      refine Submodule.Quotient.induction_on _ q ?_
      intro z
      change (rightIdealKSubmodule k I).mkQ (z * (1 : PresentedWeyl k n)) = _
      rw [mul_one]
      rfl)

/-- The right Weyl module structure on the filtered quotient, expressed using opposite scalars. -/
local instance filteredRightQuotientModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (PresentedWeyl k n)ᵐᵒᵖ (FilteredRightQuotient k I) :=
  filteredRightQuotientOpModule k I

@[simp]
theorem op_smul_filtered_mk
    (I : RightIdeal (PresentedWeyl k n))
    (y z : PresentedWeyl k n) :
    MulOpposite.op y • (Submodule.Quotient.mk z) =
      (rightIdealKSubmodule k I).mkQ (z * y) :=
  rfl

/-! ## Opposite homogeneous pieces and their filtered action -/

/-- The degree-`N` order piece, placed in the opposite Weyl algebra. -/
def orderPieceOp (N : ℕ) : Submodule k (PresentedWeyl k n)ᵐᵒᵖ :=
  (orderPiece k n N).map (MulOpposite.opLinearEquiv k).toLinearMap

theorem mem_orderPieceOp_iff (N : ℕ) (y : (PresentedWeyl k n)ᵐᵒᵖ) :
    y ∈ orderPieceOp (n := n) k N ↔
      y.unop ∈ orderPiece k n N := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hy
    exact ⟨y.unop, hy, by simp⟩

local instance orderPieceOpGradedMonoid :
    SetLike.GradedMonoid (orderPieceOp (n := n) k) where
  one_mem := by
    rw [mem_orderPieceOp_iff]
    exact (orderPieceOne (n := n) k).property
  mul_mem := by
    intro N M y z hy hz
    rw [mem_orderPieceOp_iff] at hy hz ⊢
    rw [MulOpposite.unop_mul]
    simpa [Nat.add_comm] using mul_mem_orderPiece k hz hy

local instance orderPieceOpGradedSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SetLike.GradedSMul (orderPieceOp (n := n) k)
      (quotientOrderPiece k I) where
  smul_mem := by
    intro M N y q hy hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [mem_orderPieceOp_iff] at hy
    refine ⟨z * y.unop, ?_, ?_⟩
    · simpa [Nat.add_comm] using mul_mem_orderPiece k hz hy
    rfl

/-! ## Coefficient decomposition of the Rees ring -/

/-- The external direct sum of opposite homogeneous order pieces. -/
abbrev OppositeOrderPieceSum :=
  DirectSum ℕ (fun N => orderPieceOp (n := n) k N)

/-- Insert the coefficients of an opposite Rees polynomial in the external
direct sum of opposite filtered pieces. -/
def orderReesOpCoefficients
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) :
    OppositeOrderPieceSum (n := n) k :=
    DirectSum.mk _ r.unop.val.support fun N =>
      ⟨MulOpposite.op (r.unop.val.coeff N),
        (mem_orderPieceOp_iff k N _).2 (r.unop.property N)⟩

@[simp]
theorem orderReesOpCoefficients_apply
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) (N : ℕ) :
    ((orderReesOpCoefficients (n := n) k r) N :
      (PresentedWeyl k n)ᵐᵒᵖ) =
      MulOpposite.op (r.unop.val.coeff N) := by
  by_cases hN : N ∈ r.unop.val.support
  · rw [orderReesOpCoefficients, DirectSum.mk_apply_of_mem hN]
  · rw [orderReesOpCoefficients, DirectSum.mk_apply_of_notMem hN]
    rw [Polynomial.notMem_support_iff.mp hN]
    rfl

/-- Coefficient decomposition as an additive homomorphism. -/
def orderReesOpToDirectSum :
    (OrderReesRing (n := n) k)ᵐᵒᵖ →+ OppositeOrderPieceSum (n := n) k where
  toFun := orderReesOpCoefficients (n := n) k
  map_zero' := by
    ext N
    change ((orderReesOpCoefficients (n := n) k 0) N :
      (PresentedWeyl k n)ᵐᵒᵖ) = 0
    rw [orderReesOpCoefficients_apply]
    simp
  map_add' r s := by
    ext N
    change ((orderReesOpCoefficients (n := n) k (r + s)) N :
      (PresentedWeyl k n)ᵐᵒᵖ) =
        ((orderReesOpCoefficients (n := n) k r) N :
          (PresentedWeyl k n)ᵐᵒᵖ) +
        ((orderReesOpCoefficients (n := n) k s) N :
          (PresentedWeyl k n)ᵐᵒᵖ)
    rw [orderReesOpCoefficients_apply, orderReesOpCoefficients_apply]
    simp

@[simp]
theorem orderReesOpToDirectSum_apply
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) (N : ℕ) :
    ((orderReesOpToDirectSum (n := n) k r) N :
      (PresentedWeyl k n)ᵐᵒᵖ) =
      MulOpposite.op (r.unop.val.coeff N) := by
  exact orderReesOpCoefficients_apply k r N

/-! ## The coefficient ring equivalence -/

/-- A homogeneous opposite filtered coefficient as an opposite Rees
monomial. -/
def orderPieceOpToReesOp (N : ℕ) :
    orderPieceOp (n := n) k N →+
      (OrderReesRing (n := n) k)ᵐᵒᵖ where
  toFun y :=
    let hy : (y : (PresentedWeyl k n)ᵐᵒᵖ).unop ∈ orderPiece k n N :=
      (mem_orderPieceOp_iff (n := n) k N y).1 y.property
    MulOpposite.op <| orderReesMonomial k N ⟨y.val.unop, hy⟩
  map_zero' := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    simp [orderReesMonomial]
  map_add' y z := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    simp [orderReesMonomial]

private theorem orderPieceOpToReesOp_one :
    orderPieceOpToReesOp (n := n) k 0
        (@GradedMonoid.GOne.one ℕ
          (fun N => orderPieceOp (n := n) k N) _ _) = 1 := by
  apply MulOpposite.unop_injective
  apply Subtype.ext
  simp [orderPieceOpToReesOp, orderReesMonomial]

private theorem orderPieceOpToReesOp_mul
    {N M : ℕ} (y : orderPieceOp (n := n) k N)
    (z : orderPieceOp (n := n) k M) :
    orderPieceOpToReesOp (n := n) k (N + M)
        (@GradedMonoid.GMul.mul ℕ
          (fun L => orderPieceOp (n := n) k L) _ _ N M y z) =
      orderPieceOpToReesOp (n := n) k N y *
        orderPieceOpToReesOp (n := n) k M z := by
  apply MulOpposite.unop_injective
  apply Subtype.ext
  simp only [orderPieceOpToReesOp,
    MulOpposite.unop_mul]
  simp [orderReesMonomial, Polynomial.monomial_mul_monomial,
    Nat.add_comm]

/-- Recompose opposite homogeneous coefficients into an opposite Rees
polynomial. -/
def orderPieceOpDirectSumToReesOp :
    OppositeOrderPieceSum (n := n) k →+*
      (OrderReesRing (n := n) k)ᵐᵒᵖ :=
  DirectSum.toSemiring (fun N => orderPieceOpToReesOp (n := n) k N)
    (by exact orderPieceOpToReesOp_one (n := n) k)
    (by exact orderPieceOpToReesOp_mul (n := n) k)

@[simp]
theorem orderPieceOpDirectSumToReesOp_of
    (N : ℕ) (y : orderPieceOp (n := n) k N) :
    orderPieceOpDirectSumToReesOp (n := n) k
        (DirectSum.of (fun M => orderPieceOp (n := n) k M) N y) =
      orderPieceOpToReesOp (n := n) k N y := by
  exact DirectSum.toSemiring_of _ _ _ _ _

theorem orderPieceOpDirectSumToReesOp_coeff
    (x : OppositeOrderPieceSum (n := n) k) (N : ℕ) :
    ((orderPieceOpDirectSumToReesOp (n := n) k x).unop.val.coeff N) =
      ((x N : orderPieceOp (n := n) k N) :
        (PresentedWeyl k n)ᵐᵒᵖ).unop := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of M y =>
      rw [orderPieceOpDirectSumToReesOp_of]
      by_cases hMN : M = N
      · subst N
        simp [orderPieceOpToReesOp, orderReesMonomial]
      · simp [orderPieceOpToReesOp, orderReesMonomial,
          Polynomial.coeff_monomial, DirectSum.of_apply, hMN]
  | add x y hx hy =>
      rw [map_add]
      change (((orderPieceOpDirectSumToReesOp (n := n) k x).unop.val +
          (orderPieceOpDirectSumToReesOp (n := n) k y).unop.val).coeff N) = _
      rw [Polynomial.coeff_add, hx, hy]
      rfl

theorem orderPieceOpDirectSumToReesOp_leftInverse :
    Function.LeftInverse (orderReesOpToDirectSum (n := n) k)
      (orderPieceOpDirectSumToReesOp (n := n) k) := by
  intro x
  ext N
  change (((orderReesOpToDirectSum (n := n) k)
      (orderPieceOpDirectSumToReesOp (n := n) k x)) N :
        (PresentedWeyl k n)ᵐᵒᵖ) =
    (x N : (PresentedWeyl k n)ᵐᵒᵖ)
  rw [orderReesOpToDirectSum_apply]
  rw [orderPieceOpDirectSumToReesOp_coeff]
  exact MulOpposite.op_unop _

theorem orderPieceOpDirectSumToReesOp_rightInverse :
    Function.RightInverse (orderReesOpToDirectSum (n := n) k)
      (orderPieceOpDirectSumToReesOp (n := n) k) := by
  intro r
  apply MulOpposite.unop_injective
  apply Subtype.ext
  apply Polynomial.ext
  intro N
  rw [orderPieceOpDirectSumToReesOp_coeff]
  rw [orderReesOpToDirectSum_apply]
  exact MulOpposite.unop_op _

/-- The coefficient decomposition is an equivalence of rings, with the
opposite multiplication recording written right Weyl multiplication. -/
def orderPieceOpDirectSumEquivReesOp :
    OppositeOrderPieceSum (n := n) k ≃+*
      (OrderReesRing (n := n) k)ᵐᵒᵖ :=
  RingEquiv.ofBijective (orderPieceOpDirectSumToReesOp (n := n) k)
    ⟨(orderPieceOpDirectSumToReesOp_leftInverse (n := n) k).injective,
      (orderPieceOpDirectSumToReesOp_rightInverse (n := n) k).surjective⟩

@[simp]
theorem orderPieceOpDirectSumEquivReesOp_symm_apply
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) :
    (orderPieceOpDirectSumEquivReesOp (n := n) k).symm r =
      orderReesOpToDirectSum (n := n) k r := by
  apply (orderPieceOpDirectSumEquivReesOp (n := n) k).injective
  rw [RingEquiv.apply_symm_apply]
  exact (orderPieceOpDirectSumToReesOp_rightInverse (n := n) k r).symm

/-! ## The right Rees action -/

/-!
Lean 4.33 matches instance arguments only up to instance transparency.  The
`VAdd ℕ ℕ` that elaboration picks here is the one derived from `Add`, while
`SetLike.gmulAction` and its successors state their conclusions with the one
derived from `AddAction`, so Mathlib's internal graded-module instances no
longer apply to the pieces above.  The three instances below are Mathlib's
own constructions written in this file's shape; each proof obligation is
discharged exactly as upstream.
-/

/-- The graded action of opposite order pieces on quotient order pieces. -/
local instance orderPieceOpGMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    GradedMonoid.GMulAction (fun N => orderPieceOp (n := n) k N)
      (fun N => quotientOrderPiece k I N) :=
  { SetLike.toGSMul (orderPieceOp (n := n) k) (quotientOrderPiece k I) with
    one_smul := fun ⟨_i, _m⟩ =>
      Sigma.subtype_ext (zero_vadd _ _) (one_smul _ _)
    mul_smul := fun ⟨_i, _a⟩ ⟨_j, _a'⟩ ⟨_l, _b⟩ =>
      Sigma.subtype_ext (add_vadd _ _ _) (mul_smul _ _ _) }

/-- The distributive graded action of opposite order pieces on quotient order pieces. -/
local instance orderPieceOpGdistribMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.GdistribMulAction (fun N => orderPieceOp (n := n) k N)
      (fun N => quotientOrderPiece k I N) :=
  { orderPieceOpGMulAction (n := n) k I with
    smul_add := fun _a _b _c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun _a => Subtype.ext <| smul_zero _ }

/-- The graded module structure of quotient order pieces over the opposite order pieces. -/
local instance orderPieceOpGmodule
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.Gmodule (fun N => orderPieceOp (n := n) k N)
      (fun N => quotientOrderPiece k I N) :=
  { orderPieceOpGdistribMulAction (n := n) k I with
    add_smul := fun _a _a' _b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun _b => Subtype.ext <| zero_smul _ _ }

/-- The honest right order-Rees module structure.  Its scalar ring is
opposite because `op r • q` means `q * r` in written Weyl order. -/
noncomputable instance quotientOrderReesModuleOrderReesOpModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (OrderReesRing (n := n) k)ᵐᵒᵖ
      (QuotientOrderReesModule k I) :=
  Module.compHom (QuotientOrderReesModule k I)
    (orderPieceOpDirectSumEquivReesOp (n := n) k).symm.toRingHom

instance quotientOrderReesSMul (I : RightIdeal (PresentedWeyl k n)) :
    SMul (OrderReesRing (n := n) k)ᵐᵒᵖ (QuotientOrderReesModule k I) :=
  (quotientOrderReesModuleOrderReesOpModule k I).toSMul

theorem op_smul_mem_quotientOrderPiece
    (I : RightIdeal (PresentedWeyl k n))
    {N M : ℕ} (q : quotientOrderPiece k I N)
    (y : orderPiece k n M) :
    filteredRightMul k I y (q : FilteredRightQuotient k I) ∈
      quotientOrderPiece k I (M + N) := by
  obtain ⟨z, hz, hq⟩ := q.property
  refine ⟨z * (y : PresentedWeyl k n),
    ?_, ?_⟩
  · simpa [Nat.add_comm] using mul_mem_orderPiece k hz y.property
  rw [← hq]
  rfl

theorem cast_quotientOrderPiece_coe
    (I : RightIdeal (PresentedWeyl k n))
    {A B : ℕ} (h : A = B) (q : quotientOrderPiece k I A) :
    ((h ▸ q : quotientOrderPiece k I B) : FilteredRightQuotient k I) = q := by
  subst B
  rfl

/-- Homogeneous Rees action is represented by written right Weyl
multiplication and has the sum of the declared degrees. -/
theorem orderReesMonomial_op_smul_of
    (I : RightIdeal (PresentedWeyl k n))
    {N M : ℕ} (q : quotientOrderPiece k I N)
    (y : orderPiece k n M) :
    MulOpposite.op (orderReesMonomial k M y) •
      DirectSum.of (fun L => quotientOrderPiece k I L) N q =
      DirectSum.of (fun L => quotientOrderPiece k I L) (M + N)
        ⟨filteredRightMul k I y (q : FilteredRightQuotient k I),
          op_smul_mem_quotientOrderPiece k I q y⟩ := by
  change
    (orderPieceOpDirectSumEquivReesOp (n := n) k).symm
        (MulOpposite.op (orderReesMonomial k M y)) •
      DirectSum.of (fun L => quotientOrderPiece k I L) N q = _
  rw [orderPieceOpDirectSumEquivReesOp_symm_apply]
  have hcoeff :
      orderReesOpToDirectSum (n := n) k
          (MulOpposite.op (orderReesMonomial k M y)) =
        DirectSum.of (fun L => orderPieceOp (n := n) k L) M
          ⟨MulOpposite.op (y : PresentedWeyl k n),
            (mem_orderPieceOp_iff k M _).2 y.property⟩ := by
    ext L
    by_cases hLM : M = L
    · subst L
      rw [DirectSum.of_eq_same]
      rw [orderReesOpToDirectSum_apply]
      simp [orderReesMonomial]
    · rw [DirectSum.of_eq_of_ne M L _ (Ne.symm hLM)]
      rw [orderReesOpToDirectSum_apply]
      simp [orderReesMonomial, Polynomial.coeff_monomial, hLM]
  rw [hcoeff, DirectSum.Gmodule.of_smul_of]
  congr 1

/-- The opposite Rees parameter decomposes as the degree-one unit
coefficient. -/
theorem orderReesParameter_op_decomposition :
    (orderPieceOpDirectSumEquivReesOp (n := n) k).symm
        (MulOpposite.op (orderReesParameter (n := n) k)) =
      DirectSum.of (fun L => orderPieceOp (n := n) k L) 1
        ⟨MulOpposite.op (1 : PresentedWeyl k n),
          (mem_orderPieceOp_iff k 1 _).2
            (presentedWeightPiece_mono k orderWeight (Nat.zero_le 1)
              (orderPieceOne (n := n) k).property)⟩ := by
  rw [orderPieceOpDirectSumEquivReesOp_symm_apply]
  ext L
  by_cases hL : L = 1
  · subst L
    rw [DirectSum.of_eq_same]
    rw [orderReesOpToDirectSum_apply]
    simp [orderReesParameter_coe]
  · rw [DirectSum.of_eq_of_ne 1 L _ hL]
    rw [orderReesOpToDirectSum_apply]
    simp [orderReesParameter_coe, Polynomial.coeff_X,  Ne.symm hL]

/-- The central Rees parameter acts exactly as the previously constructed
successor shift. -/
theorem orderReesParameter_op_smul_eq_shift
    (I : RightIdeal (PresentedWeyl k n))
    (q : QuotientOrderReesModule k I) :
    MulOpposite.op (orderReesParameter (n := n) k) • q =
      quotientOrderReesShift k I q := by
  induction q using DirectSum.induction_on with
  | zero => simp
  | of N q =>
      change MulOpposite.op
          (orderReesMonomial k 1
            ⟨1, presentedWeightPiece_mono k orderWeight (Nat.zero_le 1)
              (orderPieceOne (n := n) k).property⟩) •
          DirectSum.of (fun L => quotientOrderPiece k I L) N q = _
      rw [orderReesMonomial_op_smul_of k I q
        ⟨1, presentedWeightPiece_mono k orderWeight (Nat.zero_le 1)
          (orderPieceOne (n := n) k).property⟩]
      let q' : quotientOrderPiece k I (1 + N) :=
        ⟨q, by
          simpa [Nat.one_add] using
            quotientOrderPiece_mono k I (Nat.le_succ N) q.property⟩
      have hq' :
          (⟨filteredRightMul k I 1
                (q : FilteredRightQuotient k I),
              op_smul_mem_quotientOrderPiece k I q
                ⟨1, presentedWeightPiece_mono k orderWeight (Nat.zero_le 1)
                  (orderPieceOne (n := n) k).property⟩⟩ :
            quotientOrderPiece k I (1 + N)) = q' := by
        apply Subtype.ext
        exact filteredRightMul_one k I q
      rw [hq']
      rw [quotientOrderReesShift_of]
      ext L
      by_cases hL : N + 1 = L
      · subst L
        simp only [DirectSum.of_apply, Nat.one_add, Nat.succ_eq_add_one, ↓reduceDIte,
          SetLike.coe_eq_coe]
        apply Subtype.ext
        simp only [quotientOrderPieceSucc, Submodule.coe_inclusion]
        exact (cast_quotientOrderPiece_coe k I (Nat.one_add N) q').trans rfl
      · simp [DirectSum.of_apply, Nat.one_add, hL]
  | add q r hq hr =>
      rw [smul_add, map_add, hq, hr]

/-- Functional exact-signature form of parameter action. -/
theorem orderReesParameter_op_smul_fun_eq_shift
    (I : RightIdeal (PresentedWeyl k n)) :
    (fun q : QuotientOrderReesModule k I =>
      MulOpposite.op (orderReesParameter (n := n) k) • q) =
        quotientOrderReesShift k I := by
  funext q
  exact orderReesParameter_op_smul_eq_shift k I q

/-- Centrality of the Rees parameter is reflected by commuting scalar
operators on the right Rees module. -/
theorem orderReesParameter_op_smul_comm
    (I : RightIdeal (PresentedWeyl k n))
    (r : OrderReesRing (n := n) k)
    (q : QuotientOrderReesModule k I) :
    MulOpposite.op (orderReesParameter (n := n) k) •
        (MulOpposite.op r • q) =
      MulOpposite.op r •
        (MulOpposite.op (orderReesParameter (n := n) k) • q) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
  exact (orderReesParameter_mul_comm k r).symm


end

end Stafford38.CharacteristicFilteredQuotientReesAction
