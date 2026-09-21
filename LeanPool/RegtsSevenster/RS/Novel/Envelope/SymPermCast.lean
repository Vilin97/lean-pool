/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPerm

/-!
# The action along the standard embeddings

A tower's compatibility field asks that vanishing propagate along
the standard embeddings `S_m ↪ S_n`: an element of the group algebra
killed at arity `m` stays killed at arity `n`.  For the action on a
tensor power this is a factorisation rather than a coincidence.
Extending a permutation by fixed slots tensors its action with the
identity on the new factors, so the level-`n` representation
restricted along `symCast` is the level-`m` representation followed
by repeated whiskering — and whiskering, being an algebra map, sends
zero to zero.

The whiskering algebra map is where the linear structure of the
category is used: additivity of `▷` is `MonoidalPreadditive` and its
ℂ-homogeneity is `MonoidalLinear`.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## Whiskering as an algebra map -/

/-- **Whiskering by a fixed object is an algebra map** on
endomorphisms.  Multiplicativity is functoriality of `▷` — note that
`End` multiplies in the order opposite to composition, which is why
no reversal appears. -/
noncomputable def whiskerAlg
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (P X : A) : End P →ₐ[ℂ] End (P ⊗ X) where
  toFun f := f ▷ X
  map_one' := MonoidalCategory.id_whiskerRight P X
  map_mul' f g := MonoidalCategory.comp_whiskerRight g f X
  map_zero' := MonoidalPreadditive.zero_whiskerRight
  map_add' f g := MonoidalPreadditive.add_whiskerRight f g
  commutes' c := by
    show (c • 𝟙 P) ▷ X = c • 𝟙 (P ⊗ X)
    rw [MonoidalLinear.smul_whiskerRight,
      MonoidalCategory.id_whiskerRight]

/-- **Repeated whiskering**: the algebra map carrying an
endomorphism of `X ^ ⊗ m` to the endomorphism of `X ^ ⊗ (m + k)`
that acts on the first `m` factors and fixes the last `k`. -/
noncomputable def whiskerPowAlg
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (X : A) (m : ℕ) :
    (k : ℕ) → (End (tensorPow A X m) →ₐ[ℂ] End (tensorPow A X (m + k)))
  | 0 => AlgHom.id ℂ _
  | k + 1 =>
      (whiskerAlg (tensorPow A X (m + k)) X).comp (whiskerPowAlg X m k)

/-! ## The action factors through whiskering -/

/-- Extending along the identity embedding changes nothing. -/
private theorem viaEmbedding_castLEEmb_self {m : ℕ}
    (σ : Equiv.Perm (Fin m)) :
    σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m 0)) = σ :=
  Equiv.ext fun x => by
    have hx : Fin.castLEEmb (Nat.le_add_right m 0) x = x := Fin.ext rfl
    have h := Equiv.Perm.viaEmbedding_apply σ
      (Fin.castLEEmb (Nat.le_add_right m 0)) x
    rw [hx] at h
    rw [h]
    exact Fin.ext rfl

/-- **The action of an extended permutation is the whiskered
action**: a permutation of `Fin m`, extended to `Fin (m + k)` by
fixing the last `k` slots, acts on the first `m` tensor factors and
fixes the last `k`. -/
theorem permMor_viaEmbedding
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (X : A) (m : ℕ) [SymmetricCategory A] :
    ∀ (k : ℕ) (σ : Equiv.Perm (Fin m)),
      permMor X (m + k)
          (σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m k))) =
        whiskerPowAlg X m k (permMor X m σ)
  | 0, σ => by
      rw [viaEmbedding_castLEEmb_self]
      rfl
  | k + 1, σ => by
      -- The `rw` is stated at arity `m + k + 1`; the goal reads it at
      -- the definitionally equal `m + (k + 1)`, so `exact` closes it.
      have h := permMor_extPerm X (m + k)
        (σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m k)))
      rw [viaEmbedding_castLEEmb_succ]
      exact h.trans
        (congrArg (· ▷ X) (permMor_viaEmbedding X m k σ))

/-- **The representation restricted along the standard embedding**
is the lower representation followed by repeated whiskering. -/
theorem permAlg_symCast
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (X : A) [SymmetricCategory A] (m k : ℕ)
    (x : SymGroupAlgebra m) :
    permAlg X (m + k) (symCast (Nat.le_add_right m k) x) =
      whiskerPowAlg X m k (permAlg X m x) := by
  have hext : (permAlg X (m + k)).comp (symCast (Nat.le_add_right m k)) =
      (whiskerPowAlg X m k).comp (permAlg X m) := by
    refine MonoidAlgebra.algHom_ext fun σ => ?_
    show permAlg X (m + k) (symCast _ (MonoidAlgebra.single σ 1)) =
      whiskerPowAlg X m k (permAlg X m (MonoidAlgebra.single σ 1))
    have hsym : symCast (Nat.le_add_right m k)
        (MonoidAlgebra.single σ (1 : ℂ)) =
        MonoidAlgebra.single
          (σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m k)))
          (1 : ℂ) := by
      show MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ 1) =
        MonoidAlgebra.single _ 1
      exact MonoidAlgebra.mapDomain_single
    rw [hsym, permAlg_single, permAlg_single]
    exact permMor_viaEmbedding X m k σ
  exact DFunLike.congr_fun hext x

/-- **Vanishing propagates along the standard embeddings.**  This is
the `compat` field of a tower, for the action on a tensor power. -/
theorem permAlg_compat
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (X : A) [SymmetricCategory A] {m n : ℕ}
    (h : m ≤ n) (x : SymGroupAlgebra m) (hx : permAlg X m x = 0) :
    permAlg X n (symCast h x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [permAlg_symCast, hx, map_zero]

end RS
