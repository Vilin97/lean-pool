/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import LeanPool.ComputableReal.ComputableRSeq

/-!
# The quotient field of interval-Cauchy sequences

`Computableℝ` is the quotient of `ComputableℝSeq` by the equivalence relation of
converging to the same real value. This file equips it with its commutative ring,
field, and linear order structures. The ring operations are executable interval
arithmetic; inversion and the comparison `Decidable` instances go through the
classical `ComputableℝSeq.sign` and are `noncomputable`.
-/

/-- Computable reals, defined as the quotient of ComputableℝSeq sequences -- sequences with
  Cauchy sequences of lower and upper bounds that converge to the same value -- by the equivalence
  relation of having the same converged value. This is similar to how reals are quotients of Cauchy
  sequence (without any guarantees on lower/upper bounds). -/
def Computableℝ :=
  @Quotient ComputableℝSeq ComputableℝSeq.equiv

namespace Computableℝ

/-- Definition of `mk`. -/
def mk : ComputableℝSeq → Computableℝ :=
  Quotient.mk ComputableℝSeq.equiv

/-- Definition of `val`. -/
def val : Computableℝ → ℝ := Quotient.lift ComputableℝSeq.val (fun _ _ h ↦ h)

@[simp]
theorem val_mk_eq_val : (mk x).val = x.val :=
  rfl

@[simp]
theorem val_quot_eq_val (x : ComputableℝSeq) : val (⟦x⟧ : Computableℝ) = x.val :=
  rfl

theorem eq_iff_seq_val (x y : ComputableℝSeq) : (mk x).val = (mk y).val ↔ mk x = mk y :=
  ⟨fun h ↦ Quotient.eq.2 h, Quotient.eq.1⟩

@[simp]
theorem eq_iff_eq_val (x y : Computableℝ) : x.val = y.val ↔ x = y :=
  ⟨by
    let ⟨x',hx'⟩ := Quotient.exists_rep x
    let ⟨y',hy'⟩ := Quotient.exists_rep y
    subst hx'
    subst hy'
    exact (eq_iff_seq_val x' y').1,
  congrArg val⟩

/-- Alternate version of mapℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def mapℝ' (f : ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ, ∀ x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  Quotient.map f (fun a b h₂ ↦ h.elim fun _ h ↦ (h₂ ▸ h a).trans (h b).symm)

/-- Given a unary function on sequences that clearly matches function on reals, lift it. -/
def mapℝ (f : ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ} (h : ∀ x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  mapℝ' f ⟨f₂, h⟩

theorem mapℝ'_eq_mapℝ : mapℝ' f h = mapℝ f h₂ := by
  rfl

/-- Alternate version of map₂ℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def map₂ℝ' (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ → ℝ, ∀ x y,
    (f x y).val = f₂ x.val y.val) : Computableℝ → Computableℝ → Computableℝ :=
  Quotient.map₂ f (fun a b h₂ y z h₃ ↦ h.elim fun _ h ↦ (h₂ ▸ h₃ ▸ h a y).trans (h b z).symm)

/-- Given a binary function that clearly mimics a standard real function, lift that. -/
def map₂ℝ (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ → ℝ}
    (h : ∀ x y, (f x y).val = f₂ x.val y.val) :
    Computableℝ → Computableℝ → Computableℝ :=
  map₂ℝ' f ⟨f₂, h⟩

theorem map₂ℝ'_eq_map₂ℝ : map₂ℝ' f h = map₂ℝ f h₂ := by
  ext
  rw [map₂ℝ]

@[simp]
theorem val_mapℝ_eq_val : (@mapℝ f f₂ h x).val = f₂ x.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  rw [mapℝ, mapℝ', Quotient.map_mk]
  apply h

@[simp]
theorem val_map₂ℝ_eq_val : (@map₂ℝ f f₂ h x y).val = f₂ x.val y.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [map₂ℝ, map₂ℝ', Quotient.map₂_mk]
  apply h

instance instComputableAdd : Add Computableℝ :=
  ⟨map₂ℝ (· + ·) ComputableℝSeq.val_add⟩

instance instComputableMul : Mul Computableℝ :=
  ⟨map₂ℝ (· * ·) ComputableℝSeq.val_mul⟩

instance instComputableNeg : Neg Computableℝ :=
  ⟨mapℝ (- ·) ComputableℝSeq.val_neg⟩

instance instComputableSub : Sub Computableℝ :=
  ⟨map₂ℝ (· - ·) ComputableℝSeq.val_sub⟩

instance instComputableZero : Zero Computableℝ :=
  ⟨mk 0⟩

instance instComputableOne : One Computableℝ :=
  ⟨mk 1⟩

variable (x y : Computableℝ)

@[simp]
theorem val_add : (x + y).val = x.val + y.val :=
  val_map₂ℝ_eq_val

@[simp]
theorem val_mul : (x * y).val = x.val * y.val :=
  val_map₂ℝ_eq_val

@[simp]
theorem val_neg : (-x).val = -(x.val) :=
  val_mapℝ_eq_val

@[simp]
theorem val_sub : (x - y).val = x.val - y.val :=
  val_map₂ℝ_eq_val

@[simp]
theorem val_zero : (0 : Computableℝ).val = 0 :=
  ComputableℝSeq.val_zero

@[simp]
theorem val_one : (1 : Computableℝ).val = 1 :=
  ComputableℝSeq.val_one

theorem add_mk (x y : ComputableℝSeq) : mk x + mk y = mk (x + y) :=
  rfl

theorem mul_mk (x y : ComputableℝSeq) : mk x * mk y = mk (x * y) :=
  rfl

theorem sub_mk (x y : ComputableℝSeq) : mk x - mk y = mk (x - y) :=
  rfl

theorem neg_mk (x : ComputableℝSeq) : -mk x = mk (-x) :=
  rfl

instance instCommRing : CommRing Computableℝ := by
  refine { natCast := fun n => mk n
           intCast := fun z => mk z
           zero := 0
           one := 1
           mul := (· * ·)
           add := (· + ·)
           neg := (- ·)
           sub := (· - ·)
           npow := npowRec --todo faster instances
           nsmul := nsmulRec
           zsmul := zsmulRec
           add_assoc := ?_, zero_add := ?_, add_zero := ?_, add_comm := ?_,
           left_distrib := ?_, right_distrib := ?_, zero_mul := ?_, mul_zero := ?_,
           mul_assoc := ?_, one_mul := ?_, mul_one := ?_, neg_add_cancel := ?_,
           mul_comm := ?_, natCast_succ := ?_, sub_eq_add_neg := ?_ }
  all_goals
    intros
    first
    | rfl
    | rw [← eq_iff_eq_val]
      simp
      try ring_nf!

@[simp]
theorem val_natpow (x : Computableℝ) (n : ℕ) : (x ^ n).val = x.val ^ n := by
  induction n
  · rw [pow_zero, val_one, pow_zero]
  · rename_i ih
    rw [pow_succ, pow_succ, val_mul, ih]

theorem val_nsmul (x : Computableℝ) (n : ℕ) : (n • x).val = n • x.val := by
  induction n
  · simp
  · rename_i ih
    simpa using ih

section safeInv

private def nz_quot_equiv := Equiv.subtypeQuotientEquivQuotientSubtype
    (fun x : ComputableℝSeq ↦ x.val ≠ 0)
    (fun x : Computableℝ ↦ x ≠ 0)
    (fun _ ↦ ⟨
      fun h h₂ ↦ by
        rw [← eq_iff_eq_val, val_zero] at h₂
        exact h h₂,
      fun (h : ¬_ = 0) h₂ ↦ by
        rw [← eq_iff_eq_val, val_zero] at h
        exact h h₂⟩)
    (fun _ _ ↦ Iff.rfl)

/-- Auxiliary inverse definition that operates on the nonzero Computableℝ values. -/
noncomputable def safeInv' : { x : Computableℝ // x ≠ 0 } → { x : Computableℝ // x ≠ 0 } :=
  fun v ↦ nz_quot_equiv.invFun <| Quotient.map _ fun x y h₁ ↦ by
    change (ComputableℝSeq.invNz x).val.val = (ComputableℝSeq.invNz y).val.val
    rw [ComputableℝSeq.val_invNz x, ComputableℝSeq.val_invNz y, h₁]
  (nz_quot_equiv.toFun v)

/-- Inverse of a nonzero Computableℝ, safe (terminating) as long as x is nonzero. -/
noncomputable irreducible_def safeInv (hnz : x ≠ 0) : Computableℝ := safeInv' ⟨x, hnz⟩

@[simp]
theorem safeInv_val (hnz : x ≠ 0) : (x.safeInv hnz).val = x.val⁻¹ := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  have : (nz_quot_equiv { val := ⟦x'⟧, property := hnz : { x : Computableℝ // x ≠ 0 } }) =
      ⟦{ val := x', property := (by
        rw [show (0 : Computableℝ) = ⟦0⟧ by rfl] at hnz
        contrapose! hnz
        rwa [← Computableℝ.val_zero, ← val_quot_eq_val, eq_iff_eq_val] at hnz
      )}⟧ := by
    apply Equiv.subtypeQuotientEquivQuotientSubtype_mk
  rw [safeInv, safeInv', val, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Quotient.lift_mk, this,
    Quotient.map_mk, nz_quot_equiv, Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk,
    Quotient.lift_mk, ComputableℝSeq.val_invNz]

end safeInv

section field

noncomputable instance instComputableInv : Inv Computableℝ :=
  ⟨mapℝ' (·⁻¹) ⟨(·⁻¹), ComputableℝSeq.val_inv⟩⟩

@[simp]
theorem inv_val : (x⁻¹).val = (x.val)⁻¹ := by
  change (mapℝ' _ _ _).val = (x.val)⁻¹
  rw [mapℝ'_eq_mapℝ]
  exact val_mapℝ_eq_val (h := ComputableℝSeq.val_inv)

noncomputable instance instField : Field Computableℝ := { instCommRing with
  qsmul := _
  nnqsmul := _
  exists_pair_ne := ⟨0, 1, by
    rw [ne_eq, ← eq_iff_eq_val, val_zero, val_one]
    exact zero_ne_one⟩
  mul_inv_cancel := by
    intro a ha
    rw [← eq_iff_eq_val, val_mul, inv_val, val_one]
    have : val a ≠ 0 := by rwa [← val_zero, ne_eq, eq_iff_eq_val]
    field_simp
  inv_zero := by rw [← eq_iff_eq_val]; simp
    }

@[simp]
theorem div_val : (x / y).val = x.val / y.val := by
  change (x * y⁻¹).val = _
  rw [val_mul, inv_val]
  field_simp

end field

section ordered

variable (x y : Computableℝ)

/-- Definition of `lt`. -/
def lt : Prop := by
  apply Quotient.lift (fun z ↦ z.sign = SignType.pos) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]

instance instLT : LT Computableℝ :=
  ⟨lt⟩

/-- Definition of `le`. -/
def le : Prop := by
  apply Quotient.lift (fun z ↦ SignType.zero ≤ z.sign) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]

instance instLE : LE Computableℝ :=
  ⟨le⟩

@[simp]
theorem lt_iff_lt : x.val < y.val ↔ x < y := by
  change x.val < y.val ↔ lt x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [lt, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_pos_iff, ComputableℝSeq.val_sub, sub_pos]

@[simp]
theorem le_iff_le : x.val ≤ y.val ↔ x ≤ y := by
  change x.val ≤ y.val ↔ le x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [le, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_sound, SignType.zero_eq_zero, sign_nonneg_iff]
  rw [ComputableℝSeq.val_sub, sub_nonneg]

noncomputable instance instDecidableLE : DecidableRel (fun (x y : Computableℝ) ↦ x ≤ y) :=
  fun a b ↦ by
    change Decidable (le a b)
    rw [le]
    infer_instance

--TODO: add a faster `min` and `max` that don't require sign computation.
noncomputable instance instPartialOrder : PartialOrder Computableℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := by simp only [← le_iff_le]; exact le_refl _
  le_trans a b c hab hbc := by
    simp only [← le_iff_le] at *; linarith
  le_antisymm a b hab hba := by
    rw [← eq_iff_eq_val]; simp only [← le_iff_le] at *; linarith
  lt_iff_le_not_ge a b := by
    simp only [← le_iff_le, ← lt_iff_lt]; exact lt_iff_le_not_ge

noncomputable instance instLinearOrder : LinearOrder Computableℝ where
  toPartialOrder := instPartialOrder
  toDecidableLE := inferInstance
  le_total a b := by
    simp only [← le_iff_le]; exact le_total _ _

instance instIsOrderedAddMonoid : IsOrderedAddMonoid Computableℝ where
  add_le_add_left a b hab c := by
    simp only [← le_iff_le, val_add] at *
    linarith

instance instZeroLEOneClass : ZeroLEOneClass Computableℝ where
  zero_le_one := by
    simp only [← le_iff_le, val_zero, val_one]
    exact zero_le_one

instance instIsStrictOrderedRing : IsStrictOrderedRing Computableℝ :=
  .of_mul_pos fun a b ha hb => by
    simp only [← lt_iff_lt, val_mul, val_zero] at *
    exact mul_pos ha hb

end ordered

end Computableℝ
