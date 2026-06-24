/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Derivation.Basic
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.Tactics

/-!
# LeanPool.LowDimSolvClassification.Semidirect
-/

section lie_semidirect

variable {K : Type*} (L J : Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L]
    [LieAlgebra K J]
  (φ : L →ₗ⁅K⁆ LieDerivation K J J)

/-- The semidirect product of two Lie algebras `L` and `J`, defined by specifying a homomorphism
from `L` to the Lie algebra of derivations of `J`. The homomorphism `φ` indexes the type, but does
not appear in the underlying carrier; consuming it via `id` keeps the linter happy. -/
def LieSemidirectProduct (φ : L →ₗ⁅K⁆ LieDerivation K J J) : Type _ :=
  (id φ : L →ₗ⁅K⁆ LieDerivation K J J) |> fun _ ↦ L × J

variable {K : Type*} {L J : Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L]
    [LieAlgebra K J]
  {φ : L →ₗ⁅K⁆ LieDerivation K J J}

@[inherit_doc]
notation:35 L " ⋉[" φ:35 "] " J:35 => LieSemidirectProduct L J φ

namespace LieSemidirectProduct

@[ext]
theorem ext {a b : L ⋉[φ] J} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by
  unfold LieSemidirectProduct
  ext <;> assumption

instance : AddCommGroup (LieSemidirectProduct L J φ) := (inferInstance : AddCommGroup (L × J))

instance : Module K (LieSemidirectProduct L J φ) := (inferInstance : Module K (L × J))

@[simp]
theorem add_left (a b : L ⋉[φ] J) : (a + b).1 = a.1 + b.1 := rfl

@[simp]
theorem add_right (a b : L ⋉[φ] J) : (a + b).2 = a.2 + b.2 := rfl

@[simp]
theorem zero_left : (0 : L ⋉[φ] J).1 = 0 := rfl

@[simp]
theorem zero_right : (0 : L ⋉[φ] J).2 = 0 := rfl

@[simp]
theorem neg_left (a : L ⋉[φ] J) : (-a).1 = -a.1 := rfl

@[simp]
theorem neg_right (a : L ⋉[φ] J) : (-a).2 = -a.2 := rfl

@[simp]
theorem smul_left (k : K) (a : L ⋉[φ] J) : (k • a).1 = k • a.1 := rfl

@[simp]
theorem smul_right (k : K) (a : L ⋉[φ] J) : (k • a).2 = k • a.2 := rfl

instance : Bracket (L ⋉[φ] J) (L ⋉[φ] J) := {
  bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩
}

lemma bracket_def (a b : L ⋉[φ] J) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩ := rfl

instance : LieRing (L ⋉[φ] J) := {
  (inferInstance : AddCommGroup (L ⋉[φ] J)) with
  add_lie := by
    intro x y z
    simp only [bracket_def, add_left, add_right]
    congr 1
    · simp only [add_lie]
    · simp only [LieDerivation.coe_add, Pi.add_apply, map_add, add_lie]
      module
  lie_add := by
    intro x y z
    simp only [bracket_def, add_left, add_right]
    congr 1
    · simp only [lie_add]
    · simp only [map_add, LieDerivation.coe_add, Pi.add_apply, lie_add]
      module
  lie_self :=by
    intro x
    simp only [bracket_def, lie_self, sub_self, add_zero]
    congr
  leibniz_lie := by
    intro x y z
    simp only [bracket_def]
    congr 1
    · simp only [lie_lie, sub_add_cancel]
    · simp only [map_add, map_sub, LieDerivation.apply_lie_eq_sub, LieHom.map_lie,
      LieDerivation.lie_apply, lie_add, lie_sub, add_lie, sub_lie, lie_lie]
      simplify_lie
}

instance : LieAlgebra K (L ⋉[φ] J) := {
  lie_smul := by
    intro k y z
    simp only [bracket_def, smul_left, lie_smul, smul_right, map_smul,
      LieDerivation.coe_smul, Pi.smul_apply]
    ext
    · simp []
    · simp [smul_sub]
}

/-- TODO. -/
def inl : L →ₗ⁅K⁆ L ⋉[φ] J := {
  toFun := fun x ↦ ⟨x, 0⟩,
  map_add' := by
    intro x y
    ext
    · simp only [add_left]
    · simp only [add_right, add_zero]
  map_smul' := by
    intro k x
    ext
    · simp only [RingHom.id_apply, smul_left]
    · simp only [RingHom.id_apply, smul_right, smul_zero]
  map_lie' := by
    intro x y
    ext
    · simp only [bracket_def]
    · simp only [bracket_def, map_zero, sub_self, lie_self, add_zero]
}

/-- TODO. -/
def inr : J →ₗ⁅K⁆ L ⋉[φ] J := {
  toFun := fun x ↦ ⟨0, x⟩,
  map_add' := by
    intro x y
    ext
    · simp only [add_left, add_zero]
    · simp only [add_right]
  map_smul' := by
    intro k x
    ext
    · simp only [RingHom.id_apply, smul_left, smul_zero]
    · simp only [RingHom.id_apply, smul_right]
  map_lie' := by
    intro x y
    ext <;>
      simp only [bracket_def, lie_self, map_zero, LieDerivation.coe_zero, Pi.zero_apply,
        sub_self, zero_add]
}

/-- TODO. -/
def fst : L ⋉[φ] J →ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.1,
  map_add' := by
    intro x y
    simp only [add_left]
  map_smul' := by
    intro k x
    simp only [smul_left, RingHom.id_apply]
  map_lie' := by
    intro x y
    simp only [bracket_def]
}

@[simp]
theorem fst_inl (x : L) : fst (inl x : L ⋉[φ] J) = x := rfl

@[simp]
theorem fst_inr (x : J) : fst (inr x : L ⋉[φ] J) = 0 := rfl

@[simp]
theorem fst_inl' (x : L) : (inl x : L ⋉[φ] J).1 = x := rfl

@[simp]
theorem fst_inr' (x : J) : (inr x : L ⋉[φ] J).1 = 0 := rfl

@[simp]
theorem snd_inl' (x : L) : (inl x : L ⋉[φ] J).2 = 0 := rfl

@[simp]
theorem snd_inr' (x : J) : (inr x : L ⋉[φ] J).2 = x := rfl

@[simp]
theorem inl_left_add_inr_right (x : L ⋉[φ] J) : inl x.1 + inr x.2 = x := by
  ext
  · simp only [add_left, fst_inl', fst_inr', add_zero]
  · simp only [add_right, snd_inl', snd_inr', zero_add]

variable (φ : L →ₗ⁅K⁆ LieDerivation K J J)

/-- TODO. -/
def leftSubalgebra : LieSubalgebra K (L ⋉[φ] J) := LieHom.range inl

/-- TODO. -/
def rightIdeal : LieIdeal K (L ⋉[φ] J) := LieHom.ker fst

/-- TODO. -/
def rightIdealEquivRight : rightIdeal φ ≃ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.val.2
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, add_right]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, smul_right, RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    change x.1 = 0 at hx
    change y.1 = 0 at hy
    change (⁅(⟨x, hx⟩ : rightIdeal φ).val, (⟨y, hy⟩ : rightIdeal φ).val⁆ : L ⋉[φ] J).2 = ⁅x.2, y.2⁆
    simp only [bracket_def]
    rw [hx, hy]
    simp [map_zero]
  invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.1 = 0 := x.prop
    ext
    · rw [this]
    · rfl
  right_inv := fun _ ↦ rfl
}

theorem range_inr_eq_ker_fst : LieHom.range inr = (rightIdeal φ).toLieSubalgebra := by
  ext x
  unfold rightIdeal
  rw [← LieSubalgebra.mem_coe (LieIdeal.toLieSubalgebra K (L ⋉[φ] J) fst.ker),
    LieIdeal.coe_toLieSubalgebra, SetLike.mem_coe, LieHom.mem_ker]
  constructor
  · intro ⟨y, h⟩
    rw [← h, LieHom.coe_toLinearMap, fst_inr]
  · intro h
    use x.2
    rw [LieHom.coe_toLinearMap]
    nth_rw 2 [← inl_left_add_inr_right x]
    simp only [fst, LieHom.coe_mk] at h
    rw [h]
    simp only [map_zero, zero_add]

theorem finrank_eq [StrongRankCondition K] [Module.Free K L] [Module.Free K J]
      [Module.Finite K L] [Module.Finite K J] :
    Module.finrank K (L ⋉[φ] J) = Module.finrank K L + Module.finrank K J :=
  Module.finrank_prod

-- `LieRing.ofAssociativeRing` is a local instance in Mathlib (a `def`, not a global instance), so
-- we re-enable it locally to view the commutative ring `K` as a Lie ring over itself.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Any semidirect product of the base field with an abelian Lie algebra is almost abelian. -/
theorem isAlmostAbelian {φ : K →ₗ⁅K⁆ LieDerivation K L L} [IsLieAbelian L]
    [StrongRankCondition K] [Module.Free K L] [Module.Finite K L] :
    LieAlgebra.IsAlmostAbelian K (K ⋉[φ] L) := by
  refine ⟨rightIdeal φ, ?_, ?_⟩
  · exact (rightIdealEquivRight φ).injective.isLieAbelian (by assumption)
  · rw [finrank_eq, Module.finrank_self,
      LinearEquiv.finrank_eq (rightIdealEquivRight φ).toLinearEquiv, add_comm]

end LieSemidirectProduct

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

end lie_semidirect

section lie_direct

/- Direct product/sum of Lie algebra -/

variable {K L J : Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]

instance instBracketProdLeanPool : Bracket (L × J) (L × J) := {
  bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩
}

lemma Prod.bracket_def (a b : L × J) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩ := rfl

instance instLieRingProdLeanPool : LieRing (L × J) := {
  (inferInstance : AddCommGroup (L × J)) with
  add_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, add_lie, Prod.snd_add,
    Prod.mk_add_mk]
  lie_add := fun _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, lie_add, Prod.snd_add,
    Prod.mk_add_mk, implies_true]
  lie_self := fun _ ↦ by simp only [Prod.bracket_def, lie_self, Prod.mk_zero_zero]
  leibniz_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, lie_lie, Prod.mk_add_mk,
    sub_add_cancel]
}

instance instLieAlgebraProdLeanPool : LieAlgebra K (L × J) := {
  lie_smul := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.smul_fst, lie_smul, Prod.smul_snd,
    Prod.smul_mk]
}

variable (K L J : Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]

/-- TODO. -/
def LieHom.inl : L →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨x, 0⟩,
  map_add' := by
    intro x y
    ext <;> simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro k x
    ext <;> simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}

/-- TODO. -/
def LieHom.inr : J →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨0, x⟩,
  map_add' := by
    intro x y
    ext <;> simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro k x
    ext <;> simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}

/-- TODO. -/
def LieHom.fst : L × J →ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.1,
  map_add' := by
    intro x y
    simp only [Prod.fst_add]
  map_smul' := by
    intro k x
    simp only [Prod.smul_fst, RingHom.id_apply]
  map_lie' := rfl
}

/-- TODO. -/
def LieHom.snd : L × J →ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.2,
  map_add' := by
    intro x y
    simp only [Prod.snd_add]
  map_smul' := by
    intro k x
    simp only [Prod.smul_snd, RingHom.id_apply]
  map_lie' := rfl
}

/-- TODO. -/
def leftIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.snd K L J)

/-- TODO. -/
def leftIdealEquivLeft : leftIdeal K L J ≃ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.val.1
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.fst_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_fst,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    change (⁅(⟨x, hx⟩ : leftIdeal K L J).val, (⟨y, hy⟩ : leftIdeal K L J).val⁆ : L × J).1 = ⁅x.1,
      y.1⁆
    rfl
  invFun := fun x ↦ ⟨⟨x, 0⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.2 = 0 := x.prop
    ext
    · rfl
    · rw [this]
  right_inv := fun _ ↦ rfl
}

/-- TODO. -/
def rightIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.fst K L J)

/-- TODO. -/
def rightIdealEquivRight : rightIdeal K L J ≃ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.val.2
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.snd_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_snd,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    change (⁅(⟨x, hx⟩ : rightIdeal K L J).val, (⟨y, hy⟩ : rightIdeal K L J).val⁆ : L × J).2 = ⁅x.2,
      y.2⁆
    rfl
  invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.1 = 0 := x.prop
    ext
    · rw [this]
    · rfl
  right_inv := fun _ ↦ rfl
}

/-- TODO. -/
def Prod.toLieSemidirectProduct : (L × J) ≃ₗ⁅K⁆ L ⋉[(0 : L →ₗ⁅K⁆ LieDerivation K J J)] J := {
  LinearEquiv.refl K (L × J) with
  map_lie' := by
    simp only [LinearEquiv.refl_toLinearMap, bracket_def, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.id_coe, id_eq, LieSemidirectProduct.bracket_def,
      LieHom.coe_zero, Pi.zero_apply, LieDerivation.coe_zero, sub_self, zero_add, implies_true]
}

end lie_direct
