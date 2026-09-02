/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import LeanPool.CommonNeighbourConjecture.Saxl.Basic

/-!
# Affine actions and the regular-difference criterion

This file gives a local affine group whose executable representation is the
semidirect product of the additive translation group by a distributive action.
It proves the part of paper Lemma 3.1 used by every affine construction.
-/

namespace Saxl

open scoped Pointwise

variable (H V : Type*) [Group H] [AddCommGroup V] [DistribMulAction H V]

/-- A vector whose stabilizer in the linear group is trivial. -/
def IsRegularVector (v : V) : Prop :=
  ∀ h : H, h • v = v → h = 1

/-- The set of regular vectors for the linear action. -/
def regularVectors : Set V := {v | IsRegularVector H V v}

/-- If the complement of the two-fold sumset is smaller than the original
set in a finite additive group, then every element is a three-fold sum. -/
theorem threefold_add_eq_univ_of_card_compl_twofold_lt
    {A : Type*} [AddCommGroup A] [Finite A] (R : Set A)
    (hcard : (R + R)ᶜ.ncard < R.ncard) :
    (R + R) + R = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  let T : Set A := (fun r ↦ v - r) '' R
  have hTcard : T.ncard = R.ncard := by
    exact Set.ncard_image_of_injective R sub_right_injective
  have hinter : (T ∩ (R + R)).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    have hsub : T ⊆ (R + R)ᶜ := by
      intro a haT
      rw [Set.mem_compl_iff]
      intro haRR
      have ha : a ∈ T ∩ (R + R) := ⟨haT, haRR⟩
      rw [hn] at ha
      exact ha
    have hle : T.ncard ≤ (R + R)ᶜ.ncard := Set.ncard_le_ncard hsub
    rw [hTcard] at hle
    exact (Nat.not_le_of_lt hcard) hle
  obtain ⟨a, ⟨r, hr, har⟩, haRR⟩ := hinter
  have hadd : a + r ∈ (R + R) + R := Set.add_mem_add haRR hr
  convert hadd using 1
  rw [← har]
  simp

/-- The action of `H` on the multiplicative wrapper of the additive group `V`. -/
def affineLinearAut : H →* MulAut (Multiplicative V) :=
  (MulAutMultiplicative V).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut H V)

/-- The affine semidirect product `V ⋊ H`. -/
abbrev AffineGroup := Multiplicative V ⋊[affineLinearAut H V] H

@[simp]
theorem affineLinearAut_apply (h : H) (v : Multiplicative V) :
    (affineLinearAut H V h v).toAdd = h • v.toAdd := rfl

instance affineMulAction : MulAction (AffineGroup H V) V where
  smul g x := g.left.toAdd + g.right • x
  one_smul x := by
    change (0 : V) + (1 : H) • x = x
    rw [one_smul, zero_add]
  mul_smul g k x := by
    change
      (g.left * affineLinearAut H V g.right k.left).toAdd +
          (g.right * k.right) • x =
        g.left.toAdd + g.right • (k.left.toAdd + k.right • x)
    simp only [toAdd_mul, affineLinearAut_apply, mul_smul, smul_add]
    abel

@[simp]
theorem affine_smul_def (g : AffineGroup H V) (x : V) :
    g • x = g.left.toAdd + g.right • x := rfl

/-- After translating the first point to zero, an affine tuple is a base
exactly when its difference tuple has trivial kernel in the linear group. -/
theorem affine_isBaseTuple_cons_iff {n : Nat} (x : V) (w : Fin n → V) :
    IsBaseTuple (AffineGroup H V) V (Fin.cons x w) ↔
      IsBaseTuple H V (fun i ↦ w i - x) := by
  constructor
  · intro hbase h hfix
    let g : AffineGroup H V :=
      ⟨Multiplicative.ofAdd (x - h • x), h⟩
    let t : Fin (n + 1) → V := Fin.cons x w
    have hgfix : ∀ i, g • t i = t i := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change g • x = x
          change (x - h • x) + h • x = x
          abel
      | succ i =>
          change g • w i = w i
          change (x - h • x) + h • w i = w i
          have hi := hfix i
          rw [smul_sub] at hi
          calc
            x - h • x + h • w i = x + (h • w i - h • x) := by abel
            _ = x + (w i - x) := by rw [hi]
            _ = w i := by abel
    have hg_one : g = 1 := hbase g (by simpa [t] using hgfix)
    have := congrArg SemidirectProduct.right hg_one
    simpa [g] using this
  · intro hkernel g hfix
    have hg0 : g • x = x := hfix 0
    have hdiff : ∀ i, g.right • (w i - x) = w i - x := by
      intro i
      have hgi : g • w i = w i := hfix i.succ
      change g.left.toAdd + g.right • x = x at hg0
      change g.left.toAdd + g.right • w i = w i at hgi
      rw [smul_sub]
      calc
        g.right • w i - g.right • x =
            (g.left.toAdd + g.right • w i) -
              (g.left.toAdd + g.right • x) := by abel
        _ = w i - x := by rw [hgi, hg0]
    have hright : g.right = 1 := hkernel g.right hdiff
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change g.left.toAdd = 0
      change g.left.toAdd + g.right • x = x at hg0
      simpa [hright] using hg0
    · exact hright

/-- The kernel-only neighbourhood of zero for generalized affine adjacency.
An element belongs when it can be completed by `tail` further vectors so that
the resulting linear tuple has trivial kernel, while adjoining zero keeps the
full affine tuple set-like. -/
def generalizedAffineKernelSet (tail : Nat) : Set V :=
  {v | ∃ z : Fin tail → V,
    Function.Injective (Fin.cons 0 (Fin.cons v z)) ∧
      IsBaseTuple H V (Fin.cons v z)}

/-- Generalized affine adjacency depends only on the difference of the two
displayed vertices, and the condition is entirely a kernel condition for the
linear group after translation to zero. -/
theorem generalizedAffineAdjacent_iff_mem_kernelSet (tail : Nat) (x y : V) :
    GeneralizedAdjacent (AffineGroup H V) V tail x y ↔
      y - x ∈ generalizedAffineKernelSet H V tail := by
  constructor
  · rintro ⟨z, hinj, hbase⟩
    let subX : V → V := fun a ↦ a - x
    have hinj' := (sub_left_injective (b := x)).comp hinj
    change Function.Injective (subX ∘ Fin.cons x (Fin.cons y z)) at hinj'
    simp only [Fin.comp_cons] at hinj'
    dsimp only [subX, Function.comp_apply] at hinj'
    rw [sub_self] at hinj'
    have hkernel :=
      (affine_isBaseTuple_cons_iff H V x (Fin.cons y z)).mp hbase
    change IsBaseTuple H V (subX ∘ Fin.cons y z) at hkernel
    simp only [Fin.comp_cons] at hkernel
    dsimp only [subX, Function.comp_apply] at hkernel
    exact ⟨fun i ↦ z i - x, hinj', hkernel⟩
  · rintro ⟨z, hinj, hkernel⟩
    let addX : V → V := fun a ↦ x + a
    have hinj' := (add_right_injective x).comp hinj
    change Function.Injective
      (addX ∘ Fin.cons 0 (Fin.cons (y - x) z)) at hinj'
    simp only [Fin.comp_cons] at hinj'
    dsimp only [addX, Function.comp_apply] at hinj'
    abel_nf at hinj'
    refine ⟨fun i ↦ x + z i, hinj', ?_⟩
    apply (affine_isBaseTuple_cons_iff H V x
      (Fin.cons y (fun i ↦ x + z i))).mpr
    convert hkernel using 1
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp

/-- The generalized affine common-neighbour criterion: a target is covered
precisely by the two-fold sum of the kernel-only zero-neighbourhood. -/
theorem generalizedAffine_hasCommonNeighbour_zero_iff (tail : Nat) (v : V) :
    HasCommonNeighbour V
        (GeneralizedAdjacent (AffineGroup H V) V tail) 0 v ↔
      ∃ r₁ r₂,
        r₁ ∈ generalizedAffineKernelSet H V tail ∧
          r₂ ∈ generalizedAffineKernelSet H V tail ∧ v = r₁ + r₂ := by
  constructor
  · rintro ⟨z, h0z, hzv⟩
    refine ⟨z, v - z, ?_, ?_, ?_⟩
    · simpa using
        (generalizedAffineAdjacent_iff_mem_kernelSet H V tail 0 z).mp h0z
    · simpa using
        (generalizedAffineAdjacent_iff_mem_kernelSet H V tail z v).mp hzv
    · abel
  · rintro ⟨r₁, r₂, hr₁, hr₂, rfl⟩
    refine ⟨r₁, ?_, ?_⟩
    · exact (generalizedAffineAdjacent_iff_mem_kernelSet H V tail 0 r₁).mpr
        (by simpa using hr₁)
    · exact
        (generalizedAffineAdjacent_iff_mem_kernelSet H V tail r₁ (r₁ + r₂)).mpr
          (by simpa using hr₂)

/-- Pointwise-set form of the generalized affine sumset criterion. -/
theorem generalizedAffine_hasCommonNeighbour_zero_iff_mem_add
    (tail : Nat) (v : V) :
    HasCommonNeighbour V
        (GeneralizedAdjacent (AffineGroup H V) V tail) 0 v ↔
      v ∈ generalizedAffineKernelSet H V tail +
        generalizedAffineKernelSet H V tail := by
  rw [generalizedAffine_hasCommonNeighbour_zero_iff H V tail]
  constructor
  · rintro ⟨r₁, r₂, hr₁, hr₂, rfl⟩
    exact Set.add_mem_add hr₁ hr₂
  · intro hv
    obtain ⟨r₁, hr₁, r₂, hr₂, hsum⟩ := Set.mem_add.mp hv
    exact ⟨r₁, r₂, hr₁, hr₂, hsum.symm⟩

/-- Translation reduces an affine ordered pair to a regular difference. -/
theorem affine_pairBase_iff_regular_sub (x y : V) :
    Adjacent (AffineGroup H V) V x y ↔ IsRegularVector H V (y - x) := by
  constructor
  · intro hbase h hdiff
    let g : AffineGroup H V :=
      ⟨Multiplicative.ofAdd (x - h • x), h⟩
    have hgx : g • x = x := by
      change (x - h • x) + h • x = x
      abel
    have hsmul_sub : h • y - h • x = y - x := by
      simpa only [smul_sub] using hdiff
    have hgy : g • y = y := by
      change (x - h • x) + h • y = y
      calc
        x - h • x + h • y = x + (h • y - h • x) := by abel
        _ = x + (y - x) := by rw [hsmul_sub]
        _ = y := by abel
    have hg_one : g = 1 := hbase g (by
      intro i
      fin_cases i
      · exact hgx
      · exact hgy)
    have := congrArg SemidirectProduct.right hg_one
    simpa [g] using this
  · intro hregular g hfix
    have hgx : g • x = x := hfix 0
    have hgy : g • y = y := hfix 1
    have hdiff : g.right • (y - x) = y - x := by
      change g.left.toAdd + g.right • x = x at hgx
      change g.left.toAdd + g.right • y = y at hgy
      rw [smul_sub]
      calc
        g.right • y - g.right • x =
            (g.left.toAdd + g.right • y) -
              (g.left.toAdd + g.right • x) := by abel
        _ = y - x := by rw [hgy, hgx]
    have hright : g.right = 1 := hregular g.right hdiff
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change g.left.toAdd = 0
      change g.left.toAdd + g.right • x = x at hgx
      simpa [hright] using hgx
    · exact hright

/-- A regular vector is nonzero when the linear group is nontrivial. -/
theorem isRegularVector_ne_zero [Nontrivial H] {v : V}
    (hv : IsRegularVector H V v) : v ≠ 0 := by
  intro hvzero
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  apply hh
  apply hv h
  simp [hvzero]

/-- A nontrivial affine action has exact base size two as soon as its linear
group has a regular vector. -/
theorem affine_exactBaseSize_two [Nontrivial H]
    (hregular : ∃ v, IsRegularVector H V v) :
    ExactBaseSize (AffineGroup H V) V 2 := by
  rw [exactBaseSize_two_iff]
  constructor
  · obtain ⟨r, hr⟩ := hregular
    exact ⟨0, r, (isRegularVector_ne_zero H V hr).symm,
      (affine_pairBase_iff_regular_sub H V 0 r).2 (by simpa using hr)⟩
  · intro x
    obtain ⟨h, hh⟩ := exists_ne (1 : H)
    intro hbot
    let g : AffineGroup H V := ⟨Multiplicative.ofAdd (x - h • x), h⟩
    have hgmem : g ∈ MulAction.stabilizer (AffineGroup H V) x := by
      rw [MulAction.mem_stabilizer_iff]
      change (x - h • x) + h • x = x
      abel
    have gone : g = 1 := by
      rw [hbot] at hgmem
      simpa using hgmem
    apply hh
    exact congrArg SemidirectProduct.right gone

/-- At generalized tail zero, the kernel-only zero-neighbourhood is exactly
the ordinary regular-vector set (for a nontrivial linear group). -/
theorem generalizedAffineKernelSet_zero [Nontrivial H] :
    generalizedAffineKernelSet H V 0 = regularVectors H V := by
  ext v
  constructor
  · rintro ⟨z, _hinj, hbase⟩
    change IsRegularVector H V v
    intro h hh
    apply hbase h
    intro i
    fin_cases i
    exact hh
  · intro hv
    change IsRegularVector H V v at hv
    have hv0 : v ≠ 0 := isRegularVector_ne_zero H V hv
    refine ⟨Fin.elim0, ?_, ?_⟩
    · simpa [Fin.cons_injective_iff, Function.Injective] using
        (And.intro hv0.symm hv0)
    · simpa [IsBaseTuple, IsRegularVector] using hv

/-- For a nontrivial affine linear group, generalized adjacency at exact
base-size parameter two (`tail = 0`) recovers ordinary Saxl adjacency. -/
theorem generalizedAffineAdjacent_zero_iff_adjacent [Nontrivial H] (x y : V) :
    GeneralizedAdjacent (AffineGroup H V) V 0 x y ↔
      Adjacent (AffineGroup H V) V x y := by
  rw [generalizedAffineAdjacent_iff_mem_kernelSet H V 0 x y,
    generalizedAffineKernelSet_zero H V]
  exact (affine_pairBase_iff_regular_sub H V x y).symm

/-- The affine common-neighbour criterion in sumset form. -/
theorem affine_hasCommonNeighbour_zero_iff (v : V) :
    HasCommonNeighbour V (Adjacent (AffineGroup H V) V) 0 v ↔
      ∃ r₁ r₂,
        IsRegularVector H V r₁ ∧ IsRegularVector H V r₂ ∧ v = r₁ + r₂ := by
  constructor
  · rintro ⟨z, h0z, hzv⟩
    refine ⟨z, v - z, ?_, ?_, ?_⟩
    · simpa using (affine_pairBase_iff_regular_sub H V 0 z).mp h0z
    · simpa using (affine_pairBase_iff_regular_sub H V z v).mp hzv
    · abel
  · rintro ⟨r₁, r₂, hr₁, hr₂, rfl⟩
    refine ⟨r₁, ?_, ?_⟩
    · exact (affine_pairBase_iff_regular_sub H V 0 r₁).mpr (by simpa using hr₁)
    · exact (affine_pairBase_iff_regular_sub H V r₁ (r₁ + r₂)).mpr (by
        simpa using hr₂)

/-- Pointwise-set form of the ordinary affine sumset criterion. -/
theorem affine_hasCommonNeighbour_zero_iff_mem_add (v : V) :
    HasCommonNeighbour V (Adjacent (AffineGroup H V) V) 0 v ↔
      v ∈ regularVectors H V + regularVectors H V := by
  rw [affine_hasCommonNeighbour_zero_iff H V]
  constructor
  · rintro ⟨r₁, r₂, hr₁, hr₂, rfl⟩
    exact Set.add_mem_add hr₁ hr₂
  · intro hv
    obtain ⟨r₁, hr₁, r₂, hr₂, hsum⟩ := Set.mem_add.mp hv
    exact ⟨r₁, r₂, hr₁, hr₂, hsum.symm⟩

/-- A direct obstruction theorem for affine common neighbours. -/
theorem affine_core_counterexample (v : V)
    (hbase : ∃ r, IsRegularVector H V r)
    (hv : ¬ IsRegularVector H V v)
    (hsum : ∀ x, ¬ IsRegularVector H V x ∨ ¬ IsRegularVector H V (v - x)) :
    (∃ x y, Adjacent (AffineGroup H V) V x y) ∧
      ¬ Adjacent (AffineGroup H V) V 0 v ∧
      ¬ HasCommonNeighbour V (Adjacent (AffineGroup H V) V) 0 v := by
  constructor
  · obtain ⟨r, hr⟩ := hbase
    exact ⟨0, r, (affine_pairBase_iff_regular_sub H V 0 r).mpr (by simpa using hr)⟩
  constructor
  · intro hadj
    exact hv (by
      simpa using (affine_pairBase_iff_regular_sub H V 0 v).mp hadj)
  · intro hcommon
    obtain ⟨r₁, r₂, hr₁, hr₂, hvsum⟩ :=
      (affine_hasCommonNeighbour_zero_iff H V v).mp hcommon
    rcases hsum r₁ with hnr₁ | hnr₂
    · exact hnr₁ hr₁
    · apply hnr₂
      simpa [hvsum, add_comm] using hr₂

/-- If the linear action is faithful, then the induced affine action is faithful. -/
theorem affine_faithful_of_linear_faithful [FaithfulSMul H V] :
    FaithfulSMul (AffineGroup H V) V := by
  constructor
  intro g k hact
  have hlin : ∀ x : V, g.right • x = k.right • x := by
    intro x
    calc
      g.right • x = g • x - g • 0 := by simp [affine_smul_def]
      _ = k • x - k • 0 := congrArg₂ (· - ·) (hact x) (hact 0)
      _ = k.right • x := by simp [affine_smul_def]
  have hright : g.right = k.right := FaithfulSMul.eq_of_smul_eq_smul hlin
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    have hzero := hact 0
    change g.left.toAdd + g.right • 0 = k.left.toAdd + k.right • 0 at hzero
    simpa using hzero
  · exact hright

/-- An irreducible linear group over a prime field has a preprimitive affine action. -/
theorem affine_primitive_of_irreducible
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) V]
    [SMulCommClass H (ZMod p) V]
    [Representation.IsIrreducible
      (Representation.ofDistribMulAction (ZMod p) H V)] :
    MulAction.IsPreprimitive (AffineGroup H V) V := by
  let : MulAction.IsPretransitive (AffineGroup H V) V := {
    exists_smul_eq x y := by
      refine ⟨⟨Multiplicative.ofAdd (y - x), 1⟩, ?_⟩
      change (y - x) + (1 : H) • x = y
      simp }
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (0 : V)
  intro B hzero hB
  let K : AddSubgroup V := {
    carrier := B
    zero_mem' := hzero
    add_mem' := by
      intro x y hx hy
      let tx : AffineGroup H V := ⟨Multiplicative.ofAdd x, 1⟩
      have htx0 : tx • (0 : V) = x := by simp [tx, affine_smul_def]
      have htx0_mem : tx • (0 : V) ∈ B := by simpa only [htx0] using hx
      have hEq : tx • B = B := hB.smul_eq_of_mem hzero htx0_mem
      have : tx • y ∈ tx • B := Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
      rw [hEq] at this
      simpa [tx, affine_smul_def] using this
    neg_mem' := by
      intro x hx
      let tn : AffineGroup H V := ⟨Multiplicative.ofAdd (-x), 1⟩
      have htnx : tn • x = (0 : V) := by simp [tn, affine_smul_def]
      have htnx_mem : tn • x ∈ B := by simpa only [htnx] using hzero
      have hEq : tn • B = B := hB.smul_eq_of_mem hx htnx_mem
      have : tn • (0 : V) ∈ tn • B := Set.mem_smul_set.mpr ⟨0, hzero, rfl⟩
      rw [hEq] at this
      simpa [tn, affine_smul_def] using this }
  let ρ : Representation (ZMod p) H V :=
    Representation.ofDistribMulAction (ZMod p) H V
  let W : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule p K
    apply_mem_toSubmodule := by
      intro h x hx
      let lh : AffineGroup H V := ⟨1, h⟩
      have hlh0 : lh • (0 : V) = 0 := by simp [lh, affine_smul_def]
      have hlh0_mem : lh • (0 : V) ∈ B := by simpa only [hlh0] using hzero
      have hEq : lh • B = B := hB.smul_eq_of_mem hzero hlh0_mem
      have : lh • x ∈ lh • B := Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
      rw [hEq] at this
      simpa [ρ, K, lh, affine_smul_def] using this }
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · left
    intro x hx y hy
    have hx' : x ∈ W := hx
    have hy' : y ∈ W := hy
    rw [hW] at hx' hy'
    simpa using hx'.trans hy'.symm
  · right
    ext x
    simp only [Set.mem_univ, iff_true]
    have : x ∈ W := by
      rw [hW]
      exact Submodule.mem_top
    exact this

end Saxl
