/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.Commensurable
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Group

/-!
# Hecke Rings: Basic Definitions

Basic definitions for Hecke rings following Shimura Ch. 3: `HeckePair`, double coset
spaces `HeckeCoset` and `HeckeLeftCoset`, the Hecke ring type `𝕋`, and foundational double coset
lemmas.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G)
  (h₀ : H.toSubmonoid ≤ Δ) (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

/-- The conjugation action on `H` as a set product: `gHg⁻¹ = {g} * H * {g⁻¹}`. -/
lemma conjAct_smul_coe_eq (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x; refine ⟨?_, ?_⟩ <;> intro h
  · rw [Set.mem_smul_set] at h; obtain ⟨a, ha⟩ := h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha; rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, inv_mul_cancel_right, inv_mul_cancel_left, ha.1]
  · rw [Set.mem_smul_set]; use g⁻¹ * x * g
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]; group
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, SetLike.mem_coe, Int.reduceNeg, zpow_neg, zpow_one,
      and_true] at *
    rwa [← mul_assoc] at h

/-- Conjugation by an element of `H` fixes `H`. -/
lemma conjAct_smul_elt_eq (h : H) :
    ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this; norm_cast at *

/-- A left coset contained in another left coset is equal to it. -/
lemma leftCoset_eq_of_subset (a b : G)
    (h : {a} * (H : Set G) ⊆ {b} * H) : {a} * (H : Set G) = {b} * H := by
  have ha : a ∈ {a} * (H : Set G) := by rw [Set.mem_mul]; use a; simp
  have hb := h ha; rw [Set.mem_mul] at hb
  obtain ⟨b', hb', y, hy, hb_eq⟩ := hb; simp only [mem_singleton_iff] at hb'
  rw [← hb_eq, hb', ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup hy]

/-- An arithmetic group pair `(H, Δ)` consisting of a subgroup `H` and a submonoid `Δ`
of a group `G`, satisfying `H ≤ Δ ≤ commensurator(H)`. -/
structure HeckePair (G : Type*) [Group G] where
  /-- The distinguished subgroup `H` of the arithmetic pair. -/
  H : Subgroup G
  /-- The commensurating submonoid `Δ` of the arithmetic pair. -/
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/-- Two elements of `Δ` define the same double coset `HgH = HhH`. -/
def dcRel (P : HeckePair G) (g h : P.Δ) : Prop :=
  DoubleCoset.doubleCoset (g : G) P.H P.H = DoubleCoset.doubleCoset (h : G) P.H P.H

/-- The setoid on `Δ` identifying elements with the same double coset. -/
instance dcSetoid (P : HeckePair G) : Setoid P.Δ where
  r := dcRel P
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `HgH = HhH`.
    This is the basis type for the Hecke ring. -/
abbrev HeckeCoset (P : HeckePair G) := Quotient (dcSetoid P)

noncomputable instance (P : HeckePair G) : DecidableEq (HeckeCoset P) := Classical.decEq _

/-- Two elements of `Δ` define the same left coset `gH = hH`. -/
def lcRel (P : HeckePair G) (g h : P.Δ) : Prop :=
  ({(g : G)} : Set G) * (P.H : Set G) = {(h : G)} * P.H

/-- The setoid on `Δ` identifying elements with the same left coset. -/
instance lcSetoid (P : HeckePair G) : Setoid P.Δ where
  r := lcRel P
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A Hecke left coset: an equivalence class of `Δ`-elements under `gH = hH`. -/
def HeckeLeftCoset (P : HeckePair G) := Quotient (lcSetoid P)

noncomputable instance (P : HeckePair G) : DecidableEq (HeckeLeftCoset P) := Classical.decEq _

namespace HeckeCoset

variable {P : HeckePair G}

/-- The underlying set `HgH`, well-defined on the quotient. -/
noncomputable def toSet (D : HeckeCoset P) : Set G :=
  Quotient.lift (fun (g : P.Δ) => DoubleCoset.doubleCoset (g : G) P.H P.H)
    (fun a b (h : @Setoid.r _ (dcSetoid P) a b) => h) D

/-- A representative `g : Δ` (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset P) : P.Δ := Quotient.out D

/-- `⟦g⟧ = ⟦h⟧ ↔ HgH = HhH`. -/
lemma eq_iff (g h : P.Δ) : (⟦g⟧ : HeckeCoset P) = ⟦h⟧ ↔
    DoubleCoset.doubleCoset (g : G) P.H P.H = DoubleCoset.doubleCoset (h : G) P.H P.H :=
  Quotient.eq (r := dcSetoid P)

/-- The carrier set of `⟦g⟧` is definitionally `HgH`. -/
@[simp] lemma toSet_mk (g : P.Δ) :
    HeckeCoset.toSet (⟦g⟧ : HeckeCoset P) = DoubleCoset.doubleCoset (g : G) P.H P.H := rfl

/-- Membership in `toSet ⟦g⟧` is membership in the double coset `HgH`. -/
lemma mem_toSet_mk (g : P.Δ) (x : G) :
    x ∈ HeckeCoset.toSet (⟦g⟧ : HeckeCoset P) ↔ x ∈ DoubleCoset.doubleCoset (g : G) P.H P.H :=
  Iff.rfl

/-- If two `HeckeCoset`s have the same `toSet`, they are equal. -/
lemma ext_toSet {D₁ D₂ : HeckeCoset P} (h : HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂) :
    D₁ = D₂ := by
  exact Quotient.ind₂ (fun g₁ g₂ => by intro h; exact Quotient.sound h) D₁ D₂ h

/-- The carrier set equals the double coset of the representative. -/
lemma toSet_eq_rep (D : HeckeCoset P) :
    HeckeCoset.toSet D = DoubleCoset.doubleCoset (HeckeCoset.rep D : G) P.H P.H := by
  refine Quotient.inductionOn D fun g => ?_
  simp only [toSet_mk]
  have h := Quotient.out_eq (⟦g⟧ : HeckeCoset P)
  exact (Quotient.exact h).symm

/-- The representative lies in its double coset. -/
lemma rep_mem (D : HeckeCoset P) : (HeckeCoset.rep D : G) ∈ HeckeCoset.toSet D := by
  rw [toSet_eq_rep]; exact DoubleCoset.mem_doubleCoset_self P.H P.H _

/-- If `x ∈ HgH`, then `HxH = HgH`. The fundamental double coset absorption lemma. -/
lemma doubleCoset_eq_of_mem {g : P.Δ} {x : G}
    (hx : x ∈ DoubleCoset.doubleCoset (g : G) P.H P.H) :
    DoubleCoset.doubleCoset x P.H P.H = DoubleCoset.doubleCoset (g : G) P.H P.H := by
  obtain ⟨_, ⟨l, hl, _, rfl, rfl⟩, r, hr, rfl⟩ := hx
  -- x = l * g * r with l ∈ H, r ∈ H. H(lgr)H = HgH
  simp only [DoubleCoset.doubleCoset]
  ext y; simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨_, ⟨a * l, P.H.mul_mem ha hl, _, rfl, rfl⟩, r * b, P.H.mul_mem hr hb, by group⟩
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨_, ⟨a * l⁻¹, P.H.mul_mem ha (P.H.inv_mem hl), _, rfl, rfl⟩,
      r⁻¹ * b, P.H.mul_mem (P.H.inv_mem hr) hb, by group⟩

/-- `⟦g₁⟧ = ⟦g₂⟧` when `g₁` is in the double coset of `g₂`. -/
lemma eq_mk_of_mem {g₁ g₂ : P.Δ}
    (h : (g₁ : G) ∈ DoubleCoset.doubleCoset (g₂ : G) P.H P.H) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦g₂⟧ :=
  (eq_iff g₁ g₂).mpr (doubleCoset_eq_of_mem h)

/-- The identity double coset `H1H = H`. -/
def one (P : HeckePair G) : HeckeCoset P := ⟦⟨1, P.Δ.one_mem⟩⟧

/-- Induction: to prove something for all double cosets, prove it for `⟦g⟧`. -/
protected lemma ind {motive : HeckeCoset P → Prop}
    (h : ∀ g : P.Δ, motive ⟦g⟧) : ∀ D, motive D := Quotient.ind h

/-- Two-argument induction. -/
protected lemma ind₂ {motive : HeckeCoset P → HeckeCoset P → Prop}
    (h : ∀ g₁ g₂ : P.Δ, motive ⟦g₁⟧ ⟦g₂⟧) : ∀ D₁ D₂, motive D₁ D₂ := Quotient.ind₂ h

/-- The representative of `HeckeCoset.one` belongs to `H`. -/
lemma one_rep_mem_H (P : HeckePair G) : ((one P).rep : G) ∈ P.H := by
  have hm := rep_mem (one P)
  rw [toSet_eq_rep] at hm
  have h2 := @Quotient.exact _ (dcSetoid P) (rep (one P)) ⟨(1 : G), P.Δ.one_mem⟩
    (Quotient.out_eq (⟦⟨(1 : G), P.Δ.one_mem⟩⟧ : HeckeCoset P))
  change _ = _ at h2
  rw [h2, mem_doubleCoset] at hm
  obtain ⟨a, ha, b, hb, hab⟩ := hm
  rw [show (⟨(1 : G), P.Δ.one_mem⟩ : P.Δ).1 = (1 : G) from rfl, mul_one] at hab
  rw [hab]; exact P.H.mul_mem ha hb

end HeckeCoset

namespace HeckeLeftCoset

variable {P : HeckePair G}

/-- The underlying set `gH`, well-defined on the quotient. -/
noncomputable def toSet (D : HeckeLeftCoset P) : Set G :=
  Quotient.lift (fun (g : P.Δ) => ({(g : G)} : Set G) * (P.H : Set G))
    (fun _ _ (h : lcRel P _ _) => h) D

/-- A representative `g : Δ`. -/
noncomputable def rep (D : HeckeLeftCoset P) : P.Δ := Quotient.out D

/-- The identity left coset `1H = H`. -/
def one (P : HeckePair G) : HeckeLeftCoset P := ⟦⟨1, P.Δ.one_mem⟩⟧

/-- Induction for left cosets. -/
protected lemma ind {motive : HeckeLeftCoset P → Prop}
    (h : ∀ g : P.Δ, motive ⟦g⟧) : ∀ D, motive D := Quotient.ind h

end HeckeLeftCoset

/-- Left-multiplying the representative by an element of `H` does not change the double coset. -/
lemma doset_mul_left_eq_self (P : HeckePair G) (h : P.H) (g : G) :
    DoubleCoset.doubleCoset ((h : G) * g) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1, 1, 1]; rw [Subgroup.subgroup_mul_singleton h.2]

/-- Right-multiplying the representative by an element of `H` does not change the double coset. -/
lemma DoubleCoset.doubleCoset_mul_right_eq_self (P : HeckePair G)
    (h : P.H) (g : G) : DoubleCoset.doubleCoset (g * h) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1]; rw [mul_assoc, Subgroup.singleton_mul_subgroup h.2]

/-- Associativity of group multiplication lifts to double coset representatives. -/
lemma DoubleCoset.doubleCoset_mul_assoc (f g h : G) :
    DoubleCoset.doubleCoset ((f * g) * h) H H =
    DoubleCoset.doubleCoset (f * (g * h)) H H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]

/-- Scalar multiplication by a group element is the same as singleton set multiplication. -/
lemma smul_eq_singleton_mul (s : Set G) (g : G) : g • s = {g} * s :=
  Set.singleton_smul.symm

/-- A subgroup `H` is the union of left cosets of any sub-subgroup `K ≤ H`. -/
lemma set_eq_iUnion_leftCosets (K : Subgroup G) (hK : K ≤ H) :
    (H : Set G) = ⋃ (i : H ⧸ K.subgroupOf H), (i.out : G) • (K : Set G) := by
  ext a; constructor
  · intro ha; simp only [Set.mem_iUnion]
    use (⟨a, ha⟩ : H)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    rw [hh]; simp only [coe_mul]
    refine Set.mem_smul_set.mpr ?h.intro.a
    have : (h : H) • (K : Set G) = K := by
      apply smul_coe_set; exact Subgroup.mem_subgroupOf.mp (SetLike.coe_mem _)
    use h⁻¹; simp only [SetLike.mem_coe, inv_mem_iff, smul_eq_mul, mul_inv_cancel_right,
      and_true]; exact Subgroup.mem_subgroupOf.mp (SetLike.coe_mem h)
  · intro ha; simp only [Set.mem_iUnion] at ha; obtain ⟨i, hi⟩ := ha
    have : Quotient.out i • (K : Set G) ⊆ (H : Set G) := by
      intro a ha; rw [Set.mem_smul_set] at ha; obtain ⟨h, hh⟩ := ha
      rw [← hh.2]; simp only [SetLike.mem_coe]
      rw [show Quotient.out i • h = Quotient.out i * h from rfl]
      exact mul_mem (by simp) (hK hh.1)
    exact this hi

/-- The conjugate subgroup `gHg⁻¹` is closed under multiplication. -/
lemma conjAct_mul_self_eq_self (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) := by
  rw [conjAct_smul_coe_eq,
    show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) =
      {g} * ↑H * (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by simp_rw [← mul_assoc],
    Set.singleton_mul_singleton]
  conv => enter [1, 1, 2]; simp
  conv => enter [1, 1]; rw [mul_assoc, coe_mul_coe H]

/-- The intersection `H ∩ gHg⁻¹` acts trivially on `gHg⁻¹` by left multiplication. -/
lemma inter_mul_conjAct_eq_conjAct (g : G) :
    ((H : Set G) ∩ (ConjAct.toConjAct g • H)) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) := by
  have := Set.inter_mul_subset (s₁ := (H : Set G))
    (s₂ := (ConjAct.toConjAct g • H)) (t := (ConjAct.toConjAct g • H))
  refine Subset.antisymm ?_ ?_
  · exact le_trans this (by simp [conjAct_mul_self_eq_self])
  · exact subset_mul_right _ ⟨Subgroup.one_mem H,
      Subgroup.one_mem (ConjAct.toConjAct g • H)⟩

/-- Right multiplication by a singleton is cancellative. -/
lemma mul_singleton_right_cancel (g : G) (K L : Set G)
    (h : K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2; simpa using h2

/-- A double coset `HgH` decomposes as a disjoint union of left cosets of `H`. -/
lemma DoubleCoset.doubleCoset_eq_iUnion_leftCosets (g : G) :
    DoubleCoset.doubleCoset g H H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      (i.out * g) • (H : Set G) := by
  rw [DoubleCoset.doubleCoset]
  have := set_eq_iUnion_leftCosets H
    (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this)
    ((ConjAct.toConjAct g • H) : Set G)
  rw [Set.iUnion_mul, inter_comm] at h2
  apply mul_singleton_right_cancel g⁻¹
  rw [conjAct_smul_coe_eq] at *; simp_rw [← mul_assoc] at h2; rw [h2]
  have : (Subgroup.map H.subtype
      ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H := by simp
  rw [this]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjAct_eq_conjAct H g
    rw [conjAct_smul_coe_eq] at this
    have hr : ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹} =
      (i.out : G) • (((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹}) := by simp_rw [smul_mul_assoc]
    rw [hr]; simp_rw [← mul_assoc] at this
    conv => enter [1, 2]; rw [this]
    simp_rw [smul_eq_singleton_mul, ← Set.singleton_mul_singleton, ← mul_assoc]
  convert Set.iUnion_congr h1; rw [Set.iUnion_mul]

/-- The product of two double cosets simplifies using `H * H = H` on the left. -/
lemma doubleCoset_mul_doubleCoset_left (g h : G) :
    DoubleCoset.doubleCoset g H H * DoubleCoset.doubleCoset h H H =
    DoubleCoset.doubleCoset g H H * {h} * H := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H]

/-- The product of two double cosets simplifies using `H * H = H` on the right. -/
lemma doubleCoset_mul_doubleCoset_right (g h : G) :
    DoubleCoset.doubleCoset g H H * DoubleCoset.doubleCoset h H H =
    H * {g} * DoubleCoset.doubleCoset h H H := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc],
    coe_mul_coe H, ← mul_assoc]

/-- The set-theoretic product of two double cosets is a union of double cosets. -/
lemma doubleCoset_mul_eq_iUnion_doubleCoset (g h : G) :
    DoubleCoset.doubleCoset g (H : Set G) H *
      DoubleCoset.doubleCoset h (H : Set G) H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset (g * i.out * h : G) H H := by
  rw [doubleCoset_mul_doubleCoset_right, DoubleCoset.doubleCoset_eq_iUnion_leftCosets,
    Set.mul_iUnion]
  simp_rw [DoubleCoset.doubleCoset]
  apply Set.iUnion_congr fun i => by
    rw [smul_eq_singleton_mul,
      show (H : Set G) * {g} * ({↑(Quotient.out i) * h} * ↑H) =
        H * {g} * {↑(Quotient.out i) * h} * ↑H by simp_rw [← mul_assoc],
      ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
      ← Set.singleton_mul_singleton]
    simp_rw [← mul_assoc]

/-- The double coset `HhH` is a constant union indexed by the trivial quotient. -/
lemma DoubleCoset.doubleCoset_one_mul (h : G) :
    DoubleCoset.doubleCoset h (H : Set G) H =
    ⋃ (_ : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset h H H := by simp [Set.iUnion_const]

/-- The Hecke ring type: formal `Z`-linear combinations of double cosets `HeckeCoset P`.
    Changed from `def` to `abbrev` for transparency in instance resolution (Lean 4.29+). -/
abbrev 𝕋 (P : HeckePair G) (Z : Type*) [CommRing Z] := Finsupp (HeckeCoset P) Z

/-- The Hecke module type: formal `Z`-linear combinations of left cosets `HeckeLeftCoset P`.
    Changed from `def` to `abbrev` for transparency in instance resolution (Lean 4.29+). -/
abbrev HeckeModule (P : HeckePair G) (Z : Type*) [CommRing Z] := Finsupp (HeckeLeftCoset P) Z

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

/-- The decomposition quotient `H / (H ∩ gHg⁻¹)` for a concrete `g : Δ`.
    Indexes the left cosets in the decomposition of `HgH`. -/
abbrev decompQuot (P : HeckePair G) (g : P.Δ) :=
  P.H ⧸ (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H

/-- The decomposition quotient is finite because `Δ ≤ commensurator(H)`. -/
noncomputable instance instFintypeDecompQuot (P : HeckePair G) (g : P.Δ) :
    Fintype (decompQuot P g) :=
  Subgroup.fintypeOfIndexNeZero (P.h₁ g.2).1

/-- Products of the form `a · h · b` with `h ∈ H`, `a, b ∈ Δ` remain in `Δ`. -/
lemma delta_mul_mem (i : H) (a b : Δ) (h₀ : H.toSubmonoid ≤ Δ) :
    a * (i : G) * b ∈ Δ := by
  rw [mul_assoc]; exact Submonoid.mul_mem _ a.2 (Submonoid.mul_mem _ (h₀ i.2) b.2)

/-- The additive commutative group structure on the Hecke ring. -/
noncomputable instance instAddCommGroup𝕋 : AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeCoset P) →₀ Z))

/-- The additive commutative group structure on the Hecke module. -/
noncomputable instance instAddCommGroupHeckeModule : AddCommGroup (HeckeModule P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeLeftCoset P) →₀ Z))

end HeckeRing
