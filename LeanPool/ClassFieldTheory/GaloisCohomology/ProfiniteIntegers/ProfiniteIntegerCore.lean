/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration

/-! # Profinite Integer Core -/

@[expose] public section
namespace ClassFormation

/-!
# Profinite completion of the integers

We construct `ℤ̂` as the topological closure of the diagonal image of `ℤ`
inside the product of all positive cyclic quotients `ZMod n`.  This realizes
the canonical reduction maps and the dense integer embedding directly in
Mathlib.
-/

open scoped Topology

/-- A positive modulus indexing the finite quotients of the profinite integers. -/
structure ZHatIndex where
  /-- The natural-number modulus. -/
  modulus : ℕ
  /-- Every index has a positive modulus. -/
  positive : 0 < modulus

/-- The modulus of a profinite-integer index is nonzero. -/
instance (i : ZHatIndex) : NeZero i.modulus :=
  ⟨Nat.ne_of_gt i.positive⟩

/-- Package a positive natural number as a profinite-integer modulus. -/
def zHatIndex (n : ℕ) (hn : 0 < n) : ZHatIndex :=
  ⟨n, hn⟩

/-- The product of the finite cyclic rings over all positive moduli. -/
abbrev ZHatAmbient : Type 0 :=
  ∀ i : ZHatIndex, ZMod i.modulus

/-- The diagonal ring homomorphism from the integers into all finite cyclic quotients. -/
def zHatDiagonal : ℤ →+* ZHatAmbient where
  toFun a i := (a : ZMod i.modulus)
  map_zero' := by
    funext i
    exact Int.cast_zero
  map_one' := by
    funext i
    exact Int.cast_one
  map_add' a b := by
    funext i
    exact Int.cast_add a b
  map_mul' a b := by
    funext i
    exact Int.cast_mul a b

/-- The diagonal image of the integers in the product of finite cyclic rings. -/
def zHatIntegerSubring : Subring ZHatAmbient :=
  zHatDiagonal.range

/-- The closure of the integer diagonal in the product of finite cyclic rings. -/
abbrev ZHatClosureModel : Type 0 :=
  zHatIntegerSubring.topologicalClosure

/-- The profinite completion `ℤ̂ = lim ℤ/nℤ` over all positive moduli.

This is deliberately a `def`, rather than an `abbrev`: clients use the
reduction maps and the representation equivalence below instead of depending
on the closure subtype. -/
def ZHat : Type 0 :=
  ZHatClosureModel

/-- The closure model equips `ZHat` with its canonical commutative ring structure. -/
instance : CommRing ZHat := by
  change CommRing ZHatClosureModel
  infer_instance

/-- The closure model equips `ZHat` with its subspace topology. -/
instance : TopologicalSpace ZHat := by
  change TopologicalSpace ZHatClosureModel
  infer_instance

/-- Ring operations on `ZHat` are continuous for the closure-model topology. -/
instance : IsTopologicalRing ZHat := by
  change IsTopologicalRing ZHatClosureModel
  infer_instance

/-- The closure-model topology on `ZHat` is Hausdorff. -/
instance : T2Space ZHat := by
  change T2Space ZHatClosureModel
  infer_instance

/-- The profinite integer model is totally disconnected. -/
instance : TotallyDisconnectedSpace ZHat := by
  change TotallyDisconnectedSpace ZHatClosureModel
  infer_instance

/-- The profinite integer closure model is compact. -/
instance : CompactSpace ZHat :=
  Topology.IsClosedEmbedding.compactSpace
    (Subring.isClosed_topologicalClosure zHatIntegerSubring).isClosedEmbedding_subtypeVal

/-- `ZHat` as Mathlib's bundled profinite additive group. -/
def zHatProfiniteAddGrp : ProfiniteAddGrp :=
  ProfiniteAddGrp.of ZHat

/-- The multiplicative presentation of `ZHat` remains totally disconnected. -/
instance : TotallyDisconnectedSpace (Multiplicative ZHat) := by
  change TotallyDisconnectedSpace ZHat
  infer_instance

/-- The multiplicative presentation of `ZHat` as Mathlib's bundled profinite
group.  Its multiplication is addition in `ZHat`. -/
def zHatMulProfiniteGrp : ProfiniteGrp :=
  ProfiniteGrp.of (Multiplicative ZHat)

/-- The canonical continuous reduction `ℤ̂ → ℤ/nℤ`. -/
def zHatReduction (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ZHat (ZMod n) where
  toFun x := (show ZHatClosureModel from x).1 (zHatIndex n hn)
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    change Continuous
      (fun x : ZHatClosureModel => x.1 (zHatIndex n hn))
    exact (continuous_apply (zHatIndex n hn)).comp continuous_subtype_val

/-- Reduction agrees with the ordinary integer cast.  This is the public
computation rule; it does not expose the closure model used to construct
`ZHat`. -/
@[simp] theorem zHatReduction_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction n hn (a : ZHat) = (a : ZMod n) :=
  rfl

/-- Reduction modulo one sends every profinite integer to the unique residue class. -/
@[simp] theorem zHatReduction_one (n : ℕ) (hn : 0 < n) :
    zHatReduction n hn (1 : ZHat) = 1 := by
  simpa only [Int.cast_one] using zHatReduction_intCast n hn 1

namespace ZHat

/-- Profinite integers are determined by all positive-modulus reductions. -/
@[ext]
theorem ext {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) :
    x = y := by
  apply Subtype.ext
  funext i
  rcases i with ⟨n, hn⟩
  exact h n hn

end ZHat

/-- Reduction maps commute with reduction along a divisibility relation. -/
theorem zHatReduction_transition {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (x : ZHat) :
    ZMod.castHom hmn (ZMod m) (zHatReduction n hn x) =
      zHatReduction m hm x := by
  let f : ZHatAmbient → ZMod m :=
    fun z => ZMod.castHom hmn (ZMod m) (z (zHatIndex n hn))
  let g : ZHatAmbient → ZMod m :=
    fun z => z (zHatIndex m hm)
  have hfg : Set.EqOn f g (zHatIntegerSubring : Set ZHatAmbient) := by
    rintro _ ⟨a, rfl⟩
    exact map_intCast (ZMod.castHom hmn (ZMod m)) a
  have hf : Continuous f :=
    continuous_of_discreteTopology.comp (continuous_apply (zHatIndex n hn))
  have hg : Continuous g :=
    continuous_apply (zHatIndex m hm)
  exact hfg.closure hf hg x.property

/-- The ordinary integers have dense image in their profinite completion. -/
theorem denseRange_intCast_zHat :
    DenseRange (Int.castRingHom ZHat) := by
  have hinclusion : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring)) := by
    apply (denseRange_inclusion_iff
      (Subring.le_topologicalClosure zHatIntegerSubring)).2
    change closure (zHatIntegerSubring : Set ZHatAmbient) ⊆
      closure (zHatIntegerSubring : Set ZHatAmbient)
    exact Set.Subset.rfl
  have hdiagonal : DenseRange zHatDiagonal.rangeRestrict :=
    zHatDiagonal.rangeRestrict_surjective.denseRange
  have hcomp : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring) ∘
        zHatDiagonal.rangeRestrict) :=
    hinclusion.comp hdiagonal
      (continuous_inclusion
        (Subring.le_topologicalClosure zHatIntegerSubring))
  have heq :
      Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring) ∘
          zHatDiagonal.rangeRestrict =
        (fun a : ℤ => Int.castRingHom ZHat a) := by
    funext a
    apply Subtype.ext
    funext i
    rfl
  rw [heq] at hcomp
  exact hcomp

/-- The element `1` topologically generates the additive profinite integers,
written multiplicatively. -/
theorem zHatOne_topologicallyGenerates :
    TopologicallyGenerates
      (G := Multiplicative ZHat)
      ({Multiplicative.ofAdd (1 : ZHat)} : Set (Multiplicative ZHat)) := by
  let f : Multiplicative ℤ →* Multiplicative ZHat :=
    AddMonoidHom.toMultiplicative (Int.castRingHom ZHat).toAddMonoidHom
  have hf : DenseRange f := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → Multiplicative ZHat) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → Multiplicative ZHat) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [f, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  simpa [f] using
    (topologicallyGenerates_singleton_of_denseRange_mint f hf)

end ClassFormation
