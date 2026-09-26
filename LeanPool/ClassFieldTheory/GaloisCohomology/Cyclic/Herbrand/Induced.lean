/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
public import LeanPool.ClassFieldTheory.ProCGroups.InducedFunctions
public import Mathlib.Logic.Equiv.Fin.Rotate
/-!
# Multiplicative induced modules

This file supplies the multiplicative induced-module model used in the
Herbrand quotient calculation.  If `H ≤ G` acts on a commutative group `B`, then
`Ind_H^G B` is represented by the equivariant functions

`f : G → B`,  `f (h * x) = h • f x`.

The ambient group acts by right translation.  This convention is the one
used for the products of the local multiplicative groups above a place.
The basic equivariant-function model is supplied by `ProCGroups.InducedFunctions`;
this module adds the cyclic-coordinate and Herbrand calculations.
-/

@[expose] public section

noncomputable
section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uB

variable {G : Type uG} {B : Type uB}

/-- A one-step cyclic rotation whose wrap-around coordinate is acted on by
`τ`. -/
def twistedFinRotate {K C : Type*} [Group K] [CommGroup C]
    [MulDistribMulAction K C] {n : ℕ} [NeZero n]
    (τ : K) (v : Fin n → C) (i : Fin n) : C :=
  if finRotate n i = 0 then τ • v 0
  else v (finRotate n i)

/-- Cancellation of all non-wrap-around factors in a twisted rotation. -/
theorem prod_twistedFinRotate_div
    {K C : Type*} [Group K] [CommGroup C]
    [MulDistribMulAction K C] {n : ℕ} [NeZero n]
    (τ : K) (v : Fin n → C) :
    (∏ i : Fin n, twistedFinRotate τ v i) *
        (∏ i : Fin n, v i)⁻¹ =
      τ • v 0 * (v 0)⁻¹ := by
  classical
  let u : Fin n → C :=
    fun j ↦ if j = 0 then τ • v 0 else v j
  have hrotate :
      (∏ i : Fin n, twistedFinRotate τ v i) =
        ∏ j : Fin n, u j := by
    exact Fintype.prod_equiv
      (finRotate n) (twistedFinRotate τ v) u
      (fun i ↦ rfl)
  let R : C :=
    ∏ j ∈ (Finset.univ.erase (0 : Fin n)), v j
  have hu :
      (∏ j : Fin n, u j) = (τ • v 0) * R := by
    rw [← Finset.mul_prod_erase Finset.univ u
      (Finset.mem_univ (0 : Fin n))]
    simp only [u, ite_eq_left, R]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hj0 : j ≠ 0 :=
      Finset.ne_of_mem_erase hj
    simp [hj0]
  have hv :
      (∏ j : Fin n, v j) = v 0 * R := by
    rw [← Finset.mul_prod_erase Finset.univ v
      (Finset.mem_univ (0 : Fin n))]
  rw [hrotate, hu, hv]
  simp only [mul_inv_rev]
  calc
    (τ • v 0) * R * (R⁻¹ * (v 0)⁻¹) =
        (τ • v 0) * (v 0)⁻¹ *
          (R * R⁻¹) := by ac_rfl
    _ = τ • v 0 * (v 0)⁻¹ := by simp

/-- Multiplication by the cyclic generator advances `finRotate`, with the
last coordinate wrapping to the full-period power. -/
theorem pow_mul_eq_pow_finRotate
    {X : Type*} [Monoid X] {n : ℕ} [NeZero n]
    (a : X) (i : Fin n) :
    a ^ i.1 * a =
      if finRotate n i = 0 then a ^ n
      else a ^ (finRotate n i).1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        simp [pow_succ]
      · have hil : i.1 < n :=
          Fin.val_lt_last hi
        rw [finRotate_of_lt hil]
        simp [pow_succ]

/-- Partial product of a finite vector. -/
def finPartialProduct {C : Type*} [CommMonoid C]
    {n : ℕ} (v : Fin n → C) (k : ℕ) : C :=
  (Finset.range k).prod fun i ↦
    if hi : i < n then v ⟨i, hi⟩ else 1

@[simp]
theorem finPartialProduct_zero
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) :
    finPartialProduct v 0 = 1 := by
  simp [finPartialProduct]

theorem finPartialProduct_succ
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) (i : Fin n) :
    finPartialProduct v (i.1 + 1) =
      finPartialProduct v i.1 * v i := by
  simp [finPartialProduct,
    Finset.prod_range_succ, i.2]

theorem finPartialProduct_full
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) :
    finPartialProduct v n = ∏ i : Fin n, v i := by
  simpa [finPartialProduct] using
    (Finset.prod_fin_eq_prod_range v).symm

/-- A split homomorphism induces an equivalence of quotients when it
identifies the selected subgroups and its remaining kernel lies in the
source subgroup. -/
noncomputable def quotientMulEquivOfSplit
    {X Y : Type*} [CommGroup X] [CommGroup Y]
    (N : Subgroup X) (M : Subgroup Y)
    (f : X →* Y) (s : Y →* X)
    (hfs : ∀ y : Y, f (s y) = y)
    (hfN : ∀ x : X, x ∈ N → f x ∈ M)
    (hsM : ∀ y : Y, y ∈ M → s y ∈ N)
    (hker : ∀ x : X, f x = 1 → x ∈ N) :
    X ⧸ N ≃* Y ⧸ M := by
  let qf : (X ⧸ N) →* (Y ⧸ M) :=
    QuotientGroup.map N M f (fun x hx ↦ hfN x hx)
  let qs : (Y ⧸ M) →* (X ⧸ N) :=
    QuotientGroup.map M N s (fun y hy ↦ hsM y hy)
  refine MonoidHom.toMulEquiv qf qs ?_ ?_
  · apply QuotientGroup.monoidHom_ext
    ext x
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply hker
    simp [hfs]
  · apply QuotientGroup.monoidHom_ext
    ext y
    apply QuotientGroup.eq_iff_div_mem.mpr
    simp [hfs]

export ProCGroups.InducedFunctions
  (inducedSubgroup InducedModule inducedEvaluation inducedEvaluation_apply)

/-- Compatibility name for the canonical action supplied by the common core.
This alias is not registered as an additional instance. -/
abbrev inducedMulDistribMulAction [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    MulDistribMulAction G (InducedModule (B := B) H) :=
  ProCGroups.InducedFunctions.inducedMulDistribMulAction H

/-- Evaluation at the identity identifies the fixed points of an induced
module with the fixed points for the inducing subgroup. -/
noncomputable def inducedFixedEquiv [Group G] (H : Subgroup G)
    [CommGroup B] [MulDistribMulAction H B] :
    fixedSubgroup G (InducedModule (B := B) H) ≃*
      fixedSubgroup H B where
  toFun f := ⟨f.1.1 1, by
    intro h
    have hcov := f.1.2 h 1
    have hfix := congrArg
      (fun q : InducedModule (B := B) H ↦ q.1 1) (f.2 h.1)
    change f.1.1 (h.1 * 1) = h • f.1.1 1 at hcov
    change f.1.1 (1 * h.1) = f.1.1 1 at hfix
    have hcov' : h • f.1.1 1 = f.1.1 h.1 := by
      simpa using hcov.symm
    have hfix' : f.1.1 h.1 = f.1.1 1 := by
      simpa using hfix
    exact hcov'.trans hfix'⟩
  invFun b := ⟨⟨fun _ ↦ b.1, by
      intro h x
      exact (b.2 h).symm⟩,
    by
      intro g
      apply Subtype.ext
      funext x
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hx := congrArg
      (fun q : InducedModule (B := B) H ↦ q.1 1) (f.2 x)
    change f.1.1 (1 * x) = f.1.1 1 at hx
    simpa using hx.symm
  right_inv b := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := rfl

@[simp]
theorem inducedFixedEquiv_apply_coe [Group G] (H : Subgroup G)
    [CommGroup B] [MulDistribMulAction H B]
    (f : fixedSubgroup G (InducedModule (B := B) H)) :
    (inducedFixedEquiv H f : B) = f.1.1 1 :=
  rfl

section CyclicCoordinates

variable [CommGroup G] [Fintype G]

omit [Fintype G] in
/-- A chosen generator of a finite cyclic group also generates its quotient
by any subgroup. -/
theorem quotientGenerator_generates (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ q : G ⧸ H, q ∈
      Subgroup.zpowers (QuotientGroup.mk' H σ) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  exact congrArg (QuotientGroup.mk' H) hk

omit [Fintype G] in
/-- The image of a cyclic generator in `G/H` has order `[G:H]`. -/
theorem quotientGenerator_order (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    orderOf (QuotientGroup.mk' H σ) = H.index := by
  rw [H.index_eq_card]
  exact orderOf_eq_card_of_forall_mem_zpowers
    (quotientGenerator_generates H σ hgen)

/-- The powers `1, σ, ..., σ^([G:H]-1)` form the canonical transversal
used in the cyclic induced-module calculation. -/
noncomputable def cyclicCosetEquiv (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    H × Fin H.index ≃ G := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  refine Equiv.ofBijective
    (fun p : H × Fin H.index ↦ p.1.1 * σ ^ p.2.1) ⟨?_, ?_⟩
  · intro p q hpq
    have hquot :
        (QuotientGroup.mk' H σ) ^ p.2.1 =
          (QuotientGroup.mk' H σ) ^ q.2.1 := by
      have hpone : QuotientGroup.mk' H p.1.1 = 1 :=
        (QuotientGroup.eq_one_iff p.1.1).mpr p.1.2
      have hqone : QuotientGroup.mk' H q.1.1 = 1 :=
        (QuotientGroup.eq_one_iff q.1.1).mpr q.1.2
      calc
        (QuotientGroup.mk' H σ) ^ p.2.1 =
            QuotientGroup.mk' H (p.1.1 * σ ^ p.2.1) := by
          rw [map_mul, map_pow, hpone, one_mul]
        _ = QuotientGroup.mk' H (q.1.1 * σ ^ q.2.1) :=
          congrArg (QuotientGroup.mk' H) hpq
        _ = (QuotientGroup.mk' H σ) ^ q.2.1 := by
          rw [map_mul, map_pow, hqone, one_mul]
    have hmod : p.2.1 ≡ q.2.1 [MOD H.index] := by
      have hm := (pow_eq_pow_iff_modEq
        (x := QuotientGroup.mk' H σ)).mp hquot
      rw [quotientGenerator_order H σ hgen] at hm
      exact hm
    have hij : p.2.1 = q.2.1 :=
      Nat.ModEq.eq_of_lt_of_lt hmod p.2.2 q.2.2
    have hfin : p.2 = q.2 := Fin.ext hij
    cases p with
    | mk ph pi =>
      cases q with
      | mk qh qi =>
        dsimp at hfin hpq ⊢
        subst qi
        apply congrArg (fun h : H ↦ (h, pi))
        apply Subtype.ext
        exact mul_right_cancel hpq
  · intro x
    have hcover := IsCyclic.image_range_card
      (a := QuotientGroup.mk' H σ)
      (quotientGenerator_generates H σ hgen)
    rw [← H.index_eq_card] at hcover
    have hxmem : QuotientGroup.mk' H x ∈
        Finset.image (fun i : ℕ ↦
          (QuotientGroup.mk' H σ) ^ i)
          (Finset.range H.index) := by
      rw [hcover]
      simp
    obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp hxmem
    have hdiv : x / σ ^ i ∈ H := by
      apply QuotientGroup.eq_iff_div_mem.mp
      simpa using hqi.symm
    refine
      ⟨(⟨x / σ ^ i, hdiv⟩,
        ⟨i, Finset.mem_range.mp hi⟩), ?_⟩
    exact div_mul_cancel x (σ ^ i)

@[simp]
theorem cyclicCosetEquiv_apply (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (h : H) (i : Fin H.index) :
    cyclicCosetEquiv H σ hgen (h, i) =
      h.1 * σ ^ i.1 := by
  exact congrFun
    (Equiv.coe_ofBijective
      (fun p : H × Fin H.index => p.1.1 * σ ^ p.2.1)
      (cyclicCosetEquiv H σ hgen).bijective) (h, i)

omit [Fintype G] in
/-- The power `σ^[G:H]` belongs to `H`. -/
theorem cyclic_pow_index_mem (H : Subgroup G) (σ : G) :
    σ ^ H.index ∈ H :=
  H.pow_index_mem σ

omit [Fintype G] in
/-- In a cyclic group, `σ^[G:H]` generates `H`. -/
theorem zpowers_pow_index_eq [Finite G] (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    Subgroup.zpowers (σ ^ H.index) = H := by
  classical
  let := Fintype.ofFinite G
  have hn0 : H.index ≠ 0 := by
    rw [H.index_eq_card]
    exact Nat.card_pos.ne'
  have horder : orderOf σ = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hindex_dvd_order : H.index ∣ orderOf σ := by
    rw [horder]
    exact H.index_dvd_card
  have hpowOrder :
      orderOf (σ ^ H.index) = Nat.card H := by
    calc
      orderOf (σ ^ H.index) =
          orderOf σ / H.index :=
        orderOf_pow_of_dvd hn0 hindex_dvd_order
      _ = Nat.card G / H.index := by rw [horder]
      _ = Nat.card H := by
        rw [← H.index_mul_card]
        exact Nat.mul_div_cancel_left
          (Nat.card H) (Nat.pos_of_ne_zero hn0)
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr
      (cyclic_pow_index_mem H σ)
  · rw [Nat.card_zpowers, hpowOrder]

/-- The canonical generator of `H` attached to `σ`. -/
def subgroupGenerator (H : Subgroup G) (σ : G) : H :=
  ⟨σ ^ H.index, cyclic_pow_index_mem H σ⟩

omit [Fintype G] in
@[simp]
theorem subgroupGenerator_coe (H : Subgroup G) (σ : G) :
    (subgroupGenerator H σ : G) = σ ^ H.index :=
  rfl

omit [Fintype G] in
/-- The canonical element `σ^[G:H]` generates `H`. -/
theorem subgroupGenerator_generates [Finite G] (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ h : H, h ∈ Subgroup.zpowers (subgroupGenerator H σ) := by
  classical
  let := Fintype.ofFinite G
  intro h
  have hh : h.1 ∈
      Subgroup.zpowers (σ ^ H.index) := by
    rw [zpowers_pow_index_eq H σ hgen]
    exact h.2
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.mp hh
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply Subtype.ext
  exact hk

end CyclicCoordinates

section InducedCoordinates

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- Restriction to the canonical cyclic transversal identifies an induced
module with a finite product of copies of the inducing group. -/
noncomputable def inducedCoordinates (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    InducedModule (B := B) H ≃*
      (Fin H.index → B) where
  toFun f i := f.1 (σ ^ i.1)
  invFun v := ⟨fun x ↦
      let p := (cyclicCosetEquiv H σ hgen).symm x
      p.1 • v p.2,
    by
      intro h x
      let e := cyclicCosetEquiv H σ hgen
      let p := e.symm x
      have hp : p.1.1 * σ ^ p.2.1 = x := by
        have hx := e.apply_symm_apply x
        change p.1.1 * σ ^ p.2.1 = x at hx
        exact hx
      have hsymm :
          e.symm (h.1 * x) = (h * p.1, p.2) := by
        apply e.injective
        rw [e.apply_symm_apply]
        change h.1 * x =
          (h * p.1).1 * σ ^ p.2.1
        rw [← hp]
        simp only [Subgroup.coe_mul]
        exact (mul_assoc h.1 p.1.1
          (σ ^ p.2.1)).symm
      change
        (e.symm (h.1 * x)).1 •
            v (e.symm (h.1 * x)).2 =
          h • p.1 • v p.2
      rw [hsymm]
      exact mul_smul h p.1 (v p.2)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    let e := cyclicCosetEquiv H σ hgen
    let p := e.symm x
    have hp : p.1.1 * σ ^ p.2.1 = x := by
      have hx := e.apply_symm_apply x
      change p.1.1 * σ ^ p.2.1 = x at hx
      exact hx
    change p.1 • f.1 (σ ^ p.2.1) = f.1 x
    rw [← hp]
    exact (f.2 p.1 (σ ^ p.2.1)).symm
  right_inv v := by
    funext i
    let e := cyclicCosetEquiv H σ hgen
    have hsymm : e.symm (σ ^ i.1) = (1, i) := by
      apply e.injective
      simp [e]
    change
      (e.symm (σ ^ i.1)).1 •
          v (e.symm (σ ^ i.1)).2 = v i
    rw [hsymm]
    exact one_smul H (v i)
  map_mul' f k := by
    funext i
    rfl

@[simp]
theorem inducedCoordinates_apply (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (i : Fin H.index) :
    inducedCoordinates H σ hgen f i =
      f.1 (σ ^ i.1) :=
  rfl

/-- The multiplicative section supported on the first transversal
coordinate. -/
def inducedFirstCoordinateHom :
    B →* (Fin H.index → B) where
  toFun b i := if i.1 = 0 then b else 1
  map_one' := by
    funext i
    split <;> rfl
  map_mul' b c := by
    funext i
    by_cases hi : i.1 = 0 <;> simp [hi]

/-- The canonical multiplicative section from the inducing group. -/
noncomputable def inducedSection (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    B →* InducedModule (B := B) H :=
  (inducedCoordinates H σ hgen).symm.toMonoidHom.comp
    (inducedFirstCoordinateHom H)

@[simp]
theorem inducedSection_apply_one (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) (b : B) :
    (inducedSection H σ hgen b).1 1 = b := by
  have hn : 0 < H.index := by
    rw [H.index_eq_card]
    exact Nat.card_pos
  let i0 : Fin H.index := ⟨0, hn⟩
  have h :=
    (inducedCoordinates_apply H σ hgen
      ((inducedCoordinates H σ hgen).symm
        (inducedFirstCoordinateHom H b)) i0).symm.trans
      (congrFun
        ((inducedCoordinates H σ hgen).apply_symm_apply
          (inducedFirstCoordinateHom H b)) i0)
  change (inducedSection H σ hgen b).1 (σ ^ (0 : ℕ)) = b at h
  simpa only [pow_zero] using h

/-- Product over the canonical transversal. -/
noncomputable def inducedCoordinateProduct (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    InducedModule (B := B) H →* B where
  toFun f :=
    ∏ i : Fin H.index,
      inducedCoordinates H σ hgen f i
  map_one' := by simp
  map_mul' f k := by
    simp only [map_mul, Pi.mul_apply,
      Finset.prod_mul_distrib]

@[simp]
theorem inducedCoordinateProduct_apply (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedCoordinateProduct H σ hgen f =
      ∏ i : Fin H.index, f.1 (σ ^ i.1) :=
  rfl

/-- The first-coordinate section is a right inverse to the transversal
product. -/
theorem inducedCoordinateProduct_section (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) (b : B) :
    inducedCoordinateProduct H σ hgen
        (inducedSection H σ hgen b) = b := by
  classical
  have hn : 0 < H.index := by
    rw [H.index_eq_card]
    exact Nat.card_pos
  let i0 : Fin H.index := ⟨0, hn⟩
  change (∏ i : Fin H.index,
    inducedCoordinates H σ hgen
      ((inducedCoordinates H σ hgen).symm
        (inducedFirstCoordinateHom H b)) i) = b
  rw [(inducedCoordinates H σ hgen).apply_symm_apply
    (inducedFirstCoordinateHom H b)]
  refine Finset.prod_eq_single i0 ?_ ?_
  · intro i _hi hne
    have hi0 : i.1 ≠ 0 := by
      intro hi
      apply hne
      exact Fin.ext hi
    simp [inducedFirstCoordinateHom, hi0]
  · intro hnot
    exact (hnot (Finset.mem_univ i0)).elim

end InducedCoordinates

section InducedHerbrandH0

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- A subgroup of a finite group is equipped with its finite enumeration. -/
local instance inducedEvaluationSubgroupFintype : Fintype H := Fintype.ofFinite H

/-- Norm compatibility under evaluation:
`ev₁(N_G f) = N_H(∏_{G/H} f)`. -/
theorem inducedEvaluation_tateNorm (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedEvaluation H
        (tateNorm G (InducedModule (B := B) H) f) =
      tateNorm H B
        (inducedCoordinateProduct H σ hgen f) := by
  classical
  let e := cyclicCosetEquiv H σ hgen
  let ev : InducedModule (B := B) H →* B :=
    inducedEvaluation H
  calc
    inducedEvaluation H
          (tateNorm G (InducedModule (B := B) H) f) =
        ∏ g : G, f.1 g := by
      calc
        inducedEvaluation H
              (tateNorm G
                (InducedModule (B := B) H) f) =
            ∏ g : G, ev (g • f) := by
          simp only [tateNorm, ev, map_prod]
        _ = ∏ g : G, f.1 g := by
          apply Finset.prod_congr rfl
          intro g _hg
          change f.1 (1 * g) = f.1 g
          rw [one_mul]
    _ = ∏ p : H × Fin H.index, f.1 (e p) := by
      exact Fintype.prod_equiv e.symm
        (fun g : G ↦ f.1 g)
        (fun p : H × Fin H.index ↦ f.1 (e p))
        (fun g ↦ by
          rw [e.apply_symm_apply])
    _ = ∏ h : H, ∏ i : Fin H.index,
          h • f.1 (σ ^ i.1) := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro h _hh
      apply Finset.prod_congr rfl
      intro i _hi
      change
        f.1 (h.1 * σ ^ i.1) =
          h • f.1 (σ ^ i.1)
      exact f.2 h (σ ^ i.1)
    _ = ∏ h : H,
          h • (∏ i : Fin H.index,
            f.1 (σ ^ i.1)) := by
      apply Finset.prod_congr rfl
      intro h _hh
      exact
        (map_prod
          (MulDistribMulAction.toMonoidHom B h)
          (fun i : Fin H.index ↦ f.1 (σ ^ i.1))
          Finset.univ).symm
    _ = tateNorm H B
          (inducedCoordinateProduct H σ hgen f) := by
      simp only [tateNorm,
        inducedCoordinateProduct_apply]

/-- Under evaluation of fixed points, global and subgroup norm images
correspond. -/
theorem inducedFixedEquiv_mem_tateNormSubgroup_iff
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (x : fixedSubgroup G
      (InducedModule (B := B) H)) :
    x.1 ∈ tateNormSubgroup G
        (InducedModule (B := B) H) ↔
      (inducedFixedEquiv H x).1 ∈
        tateNormSubgroup H B := by
  constructor
  · rintro ⟨f, hf⟩
    refine
      ⟨inducedCoordinateProduct H σ hgen f, ?_⟩
    calc
      tateNorm H B
            (inducedCoordinateProduct H σ hgen f) =
          inducedEvaluation H
            (tateNorm G
              (InducedModule (B := B) H) f) :=
        (inducedEvaluation_tateNorm
          H σ hgen f).symm
      _ = inducedEvaluation H x.1 :=
        congrArg (inducedEvaluation H) hf
      _ = (inducedFixedEquiv H x).1 := rfl
  · rintro ⟨b, hb⟩
    refine ⟨inducedSection H σ hgen b, ?_⟩
    let y : fixedSubgroup G
        (InducedModule (B := B) H) :=
      ⟨tateNorm G (InducedModule (B := B) H)
          (inducedSection H σ hgen b),
        fun g ↦ smul_tateNorm_eq
          (G := G)
          (A := InducedModule (B := B) H) g _⟩
    have hy :
        inducedFixedEquiv H y =
          inducedFixedEquiv H x := by
      apply Subtype.ext
      change
        inducedEvaluation H y.1 =
          (inducedFixedEquiv H x).1
      calc
        inducedEvaluation H y.1 =
            tateNorm H B
              (inducedCoordinateProduct H σ hgen
                (inducedSection H σ hgen b)) :=
          inducedEvaluation_tateNorm H σ hgen
            (inducedSection H σ hgen b)
        _ = tateNorm H B b := by
          rw [inducedCoordinateProduct_section
            H σ hgen b]
        _ = (inducedFixedEquiv H x).1 := hb
    exact congrArg Subtype.val
      ((inducedFixedEquiv H).injective hy)

/-- Multiplicative Shapiro lemma in Tate degree zero. -/
noncomputable def inducedHerbrandH0Equiv (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    HerbrandH0 G (InducedModule (B := B) H) ≃*
      HerbrandH0 H B := by
  let e :
      fixedSubgroup G (InducedModule (B := B) H) ≃*
        fixedSubgroup H B :=
    inducedFixedEquiv H
  let NG :=
    (tateNormSubgroup G
      (InducedModule (B := B) H)).subgroupOf
      (fixedSubgroup G
        (InducedModule (B := B) H))
  let NH :=
    (tateNormSubgroup H B).subgroupOf
      (fixedSubgroup H B)
  exact quotientMulEquivOfSplit
    NG NH e.toMonoidHom e.symm.toMonoidHom
    (fun y ↦ e.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact
        (inducedFixedEquiv_mem_tateNormSubgroup_iff
          H σ hgen x).mp hx)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have h :=
        (inducedFixedEquiv_mem_tateNormSubgroup_iff
          H σ hgen (e.symm y)).mpr
          (by simpa [e] using hy)
      simpa [e] using h)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply e.injective
        simpa [e] using hx
      rw [hx1]
      exact NG.one_mem)

end InducedHerbrandH0

section InducedHerbrandHMinusOne

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- A subgroup of a finite group is equipped with its finite enumeration. -/
local instance inducedCoordinatesSubgroupFintype : Fintype H := Fintype.ofFinite H

omit [Fintype G] in
local instance [Finite G] : NeZero H.index := ⟨by
  rw [H.index_eq_card]
  exact Nat.card_pos.ne'⟩

/-- In canonical coordinates, right translation by `σ` is the cyclic shift
whose wrap-around is acted on by `σ^[G:H]`. -/
theorem inducedCoordinates_smul_generator (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (i : Fin H.index) :
    inducedCoordinates H σ hgen (σ • f) i =
      twistedFinRotate (subgroupGenerator H σ)
        (inducedCoordinates H σ hgen f) i := by
  unfold twistedFinRotate
  change
    f.1 (σ ^ i.1 * σ) =
      if finRotate H.index i = 0 then
        subgroupGenerator H σ •
          f.1 (σ ^ (0 : Fin H.index).1)
      else
        f.1 (σ ^ (finRotate H.index i).1)
  rw [pow_mul_eq_pow_finRotate]
  split_ifs with hi
  · have hcov :=
      f.2 (subgroupGenerator H σ) 1
    change
      f.1 (σ ^ H.index * 1) =
        subgroupGenerator H σ • f.1 1 at hcov
    simpa using hcov
  · rfl

/-- The transversal product sends a `σ`-coboundary to the corresponding
`σ^[G:H]`-coboundary. -/
theorem inducedCoordinateProduct_sigmaMinusOne
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedCoordinateProduct H σ hgen
        (sigmaMinusOne G
          (InducedModule (B := B) H) σ f) =
      sigmaMinusOne H B
        (subgroupGenerator H σ) (f.1 1) := by
  let v : Fin H.index → B :=
    inducedCoordinates H σ hgen f
  rw [show
      sigmaMinusOne G
          (InducedModule (B := B) H) σ f =
        σ • f * f⁻¹ by rfl,
    map_mul, map_inv]
  change
    (∏ i : Fin H.index,
        inducedCoordinates H σ hgen (σ • f) i) *
        (∏ i : Fin H.index, v i)⁻¹ =
      sigmaMinusOne H B
        (subgroupGenerator H σ) (f.1 1)
  calc
    (∏ i : Fin H.index,
          inducedCoordinates H σ hgen (σ • f) i) *
          (∏ i : Fin H.index, v i)⁻¹ =
        (∏ i : Fin H.index,
          twistedFinRotate
            (subgroupGenerator H σ) v i) *
          (∏ i : Fin H.index, v i)⁻¹ := by
      congr 2
      funext i
      exact inducedCoordinates_smul_generator
        H σ hgen f i
    _ = subgroupGenerator H σ • v 0 *
          (v 0)⁻¹ :=
      prod_twistedFinRotate_div
        (subgroupGenerator H σ) v
    _ = sigmaMinusOne H B
          (subgroupGenerator H σ) (f.1 1) := by
      have hv0 : v 0 = f.1 1 := by
        simpa only [Fin.val_zero, pow_zero] using
          (inducedCoordinates_apply H σ hgen f (0 : Fin H.index))
      simpa only [sigmaMinusOne] using
        congrArg (fun b : B => subgroupGenerator H σ • b * b⁻¹) hv0

/-- If the product of the canonical coordinates is one, successive partial
products construct a `σ`-primitive. -/
theorem inducedCoordinateProduct_eq_one_mem_augmentation
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (hf :
      inducedCoordinateProduct H σ hgen f = 1) :
    f ∈ augmentationSubgroup G
      (InducedModule (B := B) H) σ := by
  let e : InducedModule (B := B) H ≃*
      (Fin H.index → B) :=
    inducedCoordinates H σ hgen
  let v : Fin H.index → B := e f
  let p : Fin H.index → B :=
    fun i ↦ finPartialProduct v i.1
  let c : InducedModule (B := B) H :=
    e.symm p
  have hc : e c = p := e.apply_symm_apply p
  have hprod :
      (∏ i : Fin H.index, v i) = 1 := by
    change
      inducedCoordinateProduct H σ hgen f = 1 at hf
    exact hf
  have hfull :
      finPartialProduct v H.index = 1 := by
    rw [finPartialProduct_full]
    exact hprod
  refine ⟨c, ?_⟩
  apply e.injective
  funext i
  change
    c.1 (σ ^ i.1 * σ) *
        (c.1 (σ ^ i.1))⁻¹ = v i
  have hci :
      c.1 (σ ^ i.1) = p i :=
    congrFun hc i
  by_cases hi : i.1 + 1 < H.index
  · let j : Fin H.index := ⟨i.1 + 1, hi⟩
    have hcj :
        c.1 (σ ^ j.1) = p j :=
      congrFun hc j
    have hpow :
        σ ^ i.1 * σ = σ ^ j.1 :=
      (pow_succ σ i.1).symm
    rw [hpow, hcj, hci]
    change
      finPartialProduct v (i.1 + 1) *
          (finPartialProduct v i.1)⁻¹ = v i
    rw [finPartialProduct_succ v i]
    simp [mul_assoc]
  · have hle : i.1 + 1 ≤ H.index :=
      Nat.succ_le_iff.mpr i.2
    have heq : i.1 + 1 = H.index :=
      le_antisymm hle (Nat.le_of_not_gt hi)
    have hc0 : c.1 1 = 1 := by
      have h := congrFun hc (0 : Fin H.index)
      change
        c.1 (σ ^ (0 : Fin H.index).1) =
          p 0 at h
      simpa [p] using h
    have hcwrap :
        c.1 (σ ^ i.1 * σ) = 1 := by
      calc
        c.1 (σ ^ i.1 * σ) =
            c.1 (σ ^ (i.1 + 1)) := by
          rw [pow_succ]
        _ = c.1 (σ ^ H.index) := by
          rw [heq]
        _ = subgroupGenerator H σ • c.1 1 := by
          simpa only [subgroupGenerator_coe, mul_one] using
            c.2 (subgroupGenerator H σ) 1
        _ = 1 := by
          rw [hc0, MulDistribMulAction.smul_one]
    have hsucc :=
      finPartialProduct_succ v i
    rw [heq] at hsucc
    have hmul :
        finPartialProduct v i.1 * v i = 1 :=
      hsucc.symm.trans hfull
    rw [hcwrap, hci, one_mul]
    change
      (finPartialProduct v i.1)⁻¹ = v i
    exact (mul_eq_one_iff_inv_eq).mp hmul

/-- The transversal product carries the ambient norm kernel into the
subgroup norm kernel. -/
theorem inducedCoordinateProduct_mem_normKernel
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {f : InducedModule (B := B) H}
    (hf : f ∈ normKernelSubgroup G
      (InducedModule (B := B) H)) :
    inducedCoordinateProduct H σ hgen f ∈
      normKernelSubgroup H B := by
  change
    tateNorm G (InducedModule (B := B) H) f = 1 at hf
  change
    tateNorm H B
      (inducedCoordinateProduct H σ hgen f) = 1
  calc
    tateNorm H B
          (inducedCoordinateProduct H σ hgen f) =
        inducedEvaluation H
          (tateNorm G
            (InducedModule (B := B) H) f) :=
      (inducedEvaluation_tateNorm
        H σ hgen f).symm
    _ = inducedEvaluation H 1 :=
      congrArg (inducedEvaluation H) hf
    _ = 1 := rfl

/-- The canonical section carries the subgroup norm kernel into the ambient
norm kernel. -/
theorem inducedSection_mem_normKernel (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {b : B} (hb : b ∈ normKernelSubgroup H B) :
    inducedSection H σ hgen b ∈
      normKernelSubgroup G
        (InducedModule (B := B) H) := by
  change tateNorm H B b = 1 at hb
  let y : fixedSubgroup G
      (InducedModule (B := B) H) :=
    ⟨tateNorm G (InducedModule (B := B) H)
        (inducedSection H σ hgen b),
      fun g ↦ smul_tateNorm_eq
        (G := G)
        (A := InducedModule (B := B) H) g _⟩
  have hey : inducedFixedEquiv H y = 1 := by
    apply Subtype.ext
    change inducedEvaluation H y.1 = 1
    calc
      inducedEvaluation H y.1 =
          tateNorm H B
            (inducedCoordinateProduct H σ hgen
              (inducedSection H σ hgen b)) :=
        inducedEvaluation_tateNorm H σ hgen
          (inducedSection H σ hgen b)
      _ = tateNorm H B b := by
        rw [inducedCoordinateProduct_section
          H σ hgen b]
      _ = 1 := hb
  have hy : y = 1 :=
    (inducedFixedEquiv H).injective hey
  exact congrArg Subtype.val hy

/-- The transversal product maps augmentation subgroups compatibly. -/
theorem inducedCoordinateProduct_mem_augmentation
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {f : InducedModule (B := B) H}
    (hf : f ∈ augmentationSubgroup G
      (InducedModule (B := B) H) σ) :
    inducedCoordinateProduct H σ hgen f ∈
      augmentationSubgroup H B
        (subgroupGenerator H σ) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨c.1 1, ?_⟩
  exact
    (inducedCoordinateProduct_sigmaMinusOne
      H σ hgen c).symm

/-- The canonical section maps subgroup coboundaries to ambient
coboundaries. -/
theorem inducedSection_mem_augmentation (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {b : B}
    (hb : b ∈ augmentationSubgroup H B
      (subgroupGenerator H σ)) :
    inducedSection H σ hgen b ∈
      augmentationSubgroup G
        (InducedModule (B := B) H) σ := by
  obtain ⟨c, rfl⟩ := hb
  let a₁ : InducedModule (B := B) H :=
    inducedSection H σ hgen
      (sigmaMinusOne H B
        (subgroupGenerator H σ) c)
  let a₂ : InducedModule (B := B) H :=
    sigmaMinusOne G
      (InducedModule (B := B) H) σ
      (inducedSection H σ hgen c)
  have hnu₁ :
      inducedCoordinateProduct H σ hgen a₁ =
        sigmaMinusOne H B
          (subgroupGenerator H σ) c :=
    inducedCoordinateProduct_section H σ hgen _
  have hnu₂ :
      inducedCoordinateProduct H σ hgen a₂ =
        sigmaMinusOne H B
          (subgroupGenerator H σ) c := by
    calc
      inducedCoordinateProduct H σ hgen a₂ =
          sigmaMinusOne H B
            (subgroupGenerator H σ)
            ((inducedSection H σ hgen c).1 1) :=
        inducedCoordinateProduct_sigmaMinusOne
          H σ hgen
            (inducedSection H σ hgen c)
      _ = sigmaMinusOne H B
            (subgroupGenerator H σ) c := by
        rw [inducedSection_apply_one
          H σ hgen c]
  let d : InducedModule (B := B) H :=
    a₁ * a₂⁻¹
  have hnud :
      inducedCoordinateProduct H σ hgen d = 1 := by
    calc
      inducedCoordinateProduct H σ hgen d =
          inducedCoordinateProduct H σ hgen a₁ *
            (inducedCoordinateProduct
              H σ hgen a₂)⁻¹ := by
        simp only [d, map_mul, map_inv]
      _ = 1 := by
        rw [hnu₁, hnu₂, mul_inv_cancel]
  have hd :
      d ∈ augmentationSubgroup G
        (InducedModule (B := B) H) σ :=
    inducedCoordinateProduct_eq_one_mem_augmentation
      H σ hgen d hnud
  have ha₂ :
      a₂ ∈ augmentationSubgroup G
        (InducedModule (B := B) H) σ :=
    ⟨inducedSection H σ hgen c, rfl⟩
  have hmul :=
    (augmentationSubgroup G
      (InducedModule (B := B) H) σ).mul_mem
        hd ha₂
  have heq : d * a₂ = a₁ := by simp [d]
  rw [heq] at hmul
  exact hmul

/-- Restriction of the transversal product to norm kernels. -/
noncomputable def inducedNormKernelProductHom (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    normKernelSubgroup G
        (InducedModule (B := B) H) →*
      normKernelSubgroup H B where
  toFun f :=
    ⟨inducedCoordinateProduct H σ hgen f.1,
      inducedCoordinateProduct_mem_normKernel
        H σ hgen f.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      (inducedCoordinateProduct H σ hgen)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      (inducedCoordinateProduct H σ hgen)
        x.1 y.1

/-- Restriction of the canonical section to norm kernels. -/
noncomputable def inducedNormKernelSectionHom (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    normKernelSubgroup H B →*
      normKernelSubgroup G
        (InducedModule (B := B) H) where
  toFun b :=
    ⟨inducedSection H σ hgen b.1,
      inducedSection_mem_normKernel
        H σ hgen b.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (inducedSection H σ hgen)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (inducedSection H σ hgen)
      x.1 y.1

/-- Multiplicative Shapiro lemma in Tate degree minus one. -/
noncomputable def inducedHerbrandHMinusOneEquiv
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    HerbrandHMinusOne G
        (InducedModule (B := B) H) σ ≃*
      HerbrandHMinusOne H B
        (subgroupGenerator H σ) := by
  let f :
      normKernelSubgroup G
          (InducedModule (B := B) H) →*
        normKernelSubgroup H B :=
    inducedNormKernelProductHom H σ hgen
  let s :
      normKernelSubgroup H B →*
        normKernelSubgroup G
          (InducedModule (B := B) H) :=
    inducedNormKernelSectionHom H σ hgen
  let IG :=
    (augmentationSubgroup G
      (InducedModule (B := B) H) σ).subgroupOf
        (normKernelSubgroup G
          (InducedModule (B := B) H))
  let IH :=
    (augmentationSubgroup H B
      (subgroupGenerator H σ)).subgroupOf
        (normKernelSubgroup H B)
  exact quotientMulEquivOfSplit
    IG IH f s
    (fun y ↦ by
      apply Subtype.ext
      exact inducedCoordinateProduct_section
        H σ hgen y.1)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact inducedCoordinateProduct_mem_augmentation
        H σ hgen hx)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact inducedSection_mem_augmentation
        H σ hgen hy)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf]
      apply
        inducedCoordinateProduct_eq_one_mem_augmentation
          H σ hgen x.1
      exact congrArg Subtype.val hx)

end InducedHerbrandHMinusOne

section FiniteCyclicGroup

variable [Group G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- The canonical generator of a subgroup, exposed without requiring a
global `CommGroup G` instance.  Commutativity is derived from the supplied
cyclic generator. -/
noncomputable def subgroupGeneratorOfGenerator (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) : H := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact subgroupGenerator H σ

omit [Fintype G] in
@[simp]
theorem subgroupGeneratorOfGenerator_coe (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    (subgroupGeneratorOfGenerator H σ hgen : G) =
      σ ^ H.index :=
  rfl

omit [Fintype G] in
/-- The derived element `σ^[G:H]` generates `H`. -/
theorem subgroupGeneratorOfGenerator_generates [Finite G] (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ h : H,
      h ∈ Subgroup.zpowers
        (subgroupGeneratorOfGenerator H σ hgen) := by
  classical
  let := Fintype.ofFinite G
  let : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  let : CommGroup G := IsCyclic.commGroup
  have hτ :
      subgroupGeneratorOfGenerator H σ hgen =
        subgroupGenerator H σ :=
    Subtype.ext (by rfl)
  rw [hτ]
  exact subgroupGenerator_generates H σ hgen

/-- Cyclic-transversal coordinates for an ordinary finite cyclic group. -/
noncomputable def inducedCoordinatesOfFiniteCyclic
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    InducedModule (B := B) H ≃*
      (Fin H.index → B) := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact inducedCoordinates H σ hgen

/-- Tate-degree-zero Shapiro equivalence for an ordinary finite cyclic
group. -/
noncomputable def inducedHerbrandH0EquivOfFiniteCyclic
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    letI : Fintype H := Fintype.ofFinite H
    HerbrandH0 G (InducedModule (B := B) H) ≃*
      HerbrandH0 H B := by
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact inducedHerbrandH0Equiv H σ hgen

/-- Tate-degree-minus-one Shapiro equivalence for an ordinary finite cyclic
group. -/
noncomputable def inducedHerbrandHMinusOneEquivOfFiniteCyclic
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    letI : Fintype H := Fintype.ofFinite H
    HerbrandHMinusOne G
        (InducedModule (B := B) H) σ ≃*
      HerbrandHMinusOne H B
        (subgroupGeneratorOfGenerator H σ hgen) := by
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  have hτ :
      subgroupGeneratorOfGenerator H σ hgen =
        subgroupGenerator H σ :=
    Subtype.ext (by rfl)
  rw [hτ]
  exact inducedHerbrandHMinusOneEquiv H σ hgen

end FiniteCyclicGroup

end CyclicCohomology
