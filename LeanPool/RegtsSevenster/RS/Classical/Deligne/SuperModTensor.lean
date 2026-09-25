/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModule

/-!
# The tensor product of two super modules

For a super-commutative ℂ-algebra `S` and two modules `M`, `N` over
it (`RS.SuperCommAlgebra.Mod`) this file builds the tensor product
`M ⊗_S N` as another `S`-module, together with the canonical
balanced map into it and its universal property.

The underlying ℤ/2-graded ℂ-space is the graded tensor product of
`RS.SuperVect.tensorObj`: the even part of `M ⊗_ℂ N` is
`(M₀ ⊗ N₀) × (M₁ ⊗ N₁)` and the odd part is `(M₀ ⊗ N₁) × (M₁ ⊗ N₀)`,
where `M₀ = M.even` and `M₁ = M.odd`.  Balancing over `S` is
imposed by quotienting each degree by the span of the relators
listed below.

## The sign convention

A left module over a super-commutative algebra is a right module
under `m · a = (−1)^{|a||m|} a · m`, and the balancing relation of
the tensor product is `(m · a) ⊗ n = m ⊗ (a · n)`.  Written with
left actions throughout, the relator at homogeneous `a`, `m`, `n`
is

  `(a · m) ⊗ n − (−1)^{|a||m|} m ⊗ (a · n)`,

so the only sign is a `−1` when *both* the scalar and the left
argument are odd; the parity of `n` never enters.  The eight
relator families are `relEvenXYZ` in total degree
`|a| + |m| + |n| = 0` and `relOddXYZ` in total degree `1`, four
each, indexed by the parity pattern `(|a|, |m|, |n|)`.

The `S`-action on the quotient is the action on the *left* factor,
with no sign: `a · (m ⊗ n) = (a · m) ⊗ n`.  It descends because
`a · ((b · m) ⊗ n − (−1)^{|b||m|} m ⊗ (b · n))` is `(−1)^{|a||b|}`
times the relator of `b` at `(a · m, n)`; this is the one place
where the super-commutativity of `S` is used, and it is the reason
the construction needs a *commutative* base.

## Contents

* `RS.SuperCommAlgebra.Mod.actEE_actEE_comm` and its five
  companions: an even scalar commutes with every scalar, and two
  odd scalars anticommute, in their action on a module.
* `RS.tensorLeftDiag`, `RS.tensorLeftSwap`: the two shapes of a
  parity block acting on the left factor of a two-summand graded
  tensor product, degree-preserving and degree-reversing.
* `RS.descendAct`: descent of a bilinear action along a pair of
  quotients.
* `RS.SuperCommAlgebra.Mod.balEven`, `balOdd`: the balancing
  submodules, and `preActEE`, `preActEO`, `preActOE`, `preActOO`:
  the four action blocks before quotienting, with the ten module
  laws proved at that level.
* `RS.SuperCommAlgebra.Mod.tensor`: the tensor product as an
  `S`-module.
* `RS.SuperCommAlgebra.Mod.tmulEE`, `tmulEO`, `tmulOE`, `tmulOO`:
  the canonical map, with its eight balancing laws and its eight
  action laws.
* `RS.SuperCommAlgebra.Mod.liftEven`, `liftOdd` and
  `liftEven_unique`, `liftOdd_unique`: the universal property,
  packaged as `exists_unique_liftEven` and `exists_unique_liftOdd`.
-/

namespace RS

open scoped TensorProduct

universe u u' v w w'

/-! ## Parity blocks acting on the left factor -/

section GradedBlocks

variable (P Q : Type*)

/-- A pair of parity blocks acting on the *left* factor of a
two-summand graded tensor product, in the degree-preserving
pattern: each summand stays where it is. -/
noncomputable def tensorLeftDiag
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {A : Type*}
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂]
    [Module ℂ X₂] [AddCommGroup Y₁] [Module ℂ Y₁] [AddCommGroup Y₂]
    [Module ℂ Y₂]
    (f : A →ₗ[ℂ] X₁ →ₗ[ℂ] X₂)
    (g : A →ₗ[ℂ] Y₁ →ₗ[ℂ] Y₂) :
    A →ₗ[ℂ] (X₁ ⊗[ℂ] P) × (Y₁ ⊗[ℂ] Q) →ₗ[ℂ]
      (X₂ ⊗[ℂ] P) × (Y₂ ⊗[ℂ] Q) where
  toFun a := ((f a).rTensor P).prodMap ((g a).rTensor Q)
  map_add' a b := by
    rw [map_add, map_add, LinearMap.rTensor_add,
      LinearMap.rTensor_add, LinearMap.prodMap_add]
  map_smul' r a := by
    rw [RingHom.id_apply, map_smul, map_smul, LinearMap.rTensor_smul,
      LinearMap.rTensor_smul, LinearMap.prodMap_smul]

/-- The degree-preserving block pattern, evaluated. -/
@[simp]
theorem tensorLeftDiag_apply
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {A : Type*}
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂]
    [Module ℂ X₂] [AddCommGroup Y₁] [Module ℂ Y₁] [AddCommGroup Y₂]
    [Module ℂ Y₂]
    (f : A →ₗ[ℂ] X₁ →ₗ[ℂ] X₂)
    (g : A →ₗ[ℂ] Y₁ →ₗ[ℂ] Y₂) (a : A)
    (t : (X₁ ⊗[ℂ] P) × (Y₁ ⊗[ℂ] Q)) :
    tensorLeftDiag P Q f g a t =
      ((f a).rTensor P t.1, (g a).rTensor Q t.2) := rfl

/-- A pair of parity blocks acting on the *left* factor of a
two-summand graded tensor product, in the degree-reversing
pattern: the two summands are interchanged. -/
noncomputable def tensorLeftSwap
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {A : Type*}
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂]
    [Module ℂ X₂] [AddCommGroup Y₁] [Module ℂ Y₁] [AddCommGroup Y₂]
    [Module ℂ Y₂]
    (f : A →ₗ[ℂ] X₁ →ₗ[ℂ] X₂)
    (g : A →ₗ[ℂ] Y₁ →ₗ[ℂ] Y₂) :
    A →ₗ[ℂ] (X₁ ⊗[ℂ] P) × (Y₁ ⊗[ℂ] Q) →ₗ[ℂ]
      (Y₂ ⊗[ℂ] Q) × (X₂ ⊗[ℂ] P) where
  toFun a := (tensorLeftDiag Q P g f a).comp
    (LinearEquiv.prodComm ℂ (X₁ ⊗[ℂ] P) (Y₁ ⊗[ℂ] Q)).toLinearMap
  map_add' a b := by rw [map_add, LinearMap.add_comp]
  map_smul' r a := by
    rw [RingHom.id_apply, map_smul, LinearMap.smul_comp]

/-- The degree-reversing block pattern, evaluated. -/
@[simp]
theorem tensorLeftSwap_apply
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {A : Type*}
    {X₁ : Type*} {X₂ : Type*} {Y₁ : Type*} {Y₂ : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂]
    [Module ℂ X₂] [AddCommGroup Y₁] [Module ℂ Y₁] [AddCommGroup Y₂]
    [Module ℂ Y₂]
    (f : A →ₗ[ℂ] X₁ →ₗ[ℂ] X₂)
    (g : A →ₗ[ℂ] Y₁ →ₗ[ℂ] Y₂) (a : A)
    (t : (X₁ ⊗[ℂ] P) × (Y₁ ⊗[ℂ] Q)) :
    tensorLeftSwap P Q f g a t =
      ((g a).rTensor Q t.2, (f a).rTensor P t.1) := rfl

end GradedBlocks

/-! ## Descent of an action along a quotient -/

section Descend

variable {A T T' : Type*}

/-- Descend a bilinear action along a pair of quotients: a
bilinear action of `A` carrying a submodule `R` of its source into
a submodule `R'` of its target induces an action on the
quotients. -/
noncomputable def descendAct
    [AddCommGroup A] [Module ℂ A] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup T'] [Module ℂ T']
    (R : Submodule ℂ T) (R' : Submodule ℂ T')
    (f : A →ₗ[ℂ] T →ₗ[ℂ] T')
    (h : ∀ a : A, ∀ t ∈ R, f a t ∈ R') :
    A →ₗ[ℂ] (T ⧸ R) →ₗ[ℂ] (T' ⧸ R') :=
  (R.liftQ (LinearMap.flip (f.compr₂ R'.mkQ)) (by
    intro t ht
    rw [LinearMap.mem_ker]
    exact LinearMap.ext fun a =>
      (Submodule.Quotient.mk_eq_zero R').mpr (h a t ht))).flip

/-- The descended action, evaluated on a class. -/
@[simp]
theorem descendAct_apply
    [AddCommGroup A] [Module ℂ A] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup T'] [Module ℂ T']
    (R : Submodule ℂ T) (R' : Submodule ℂ T')
    (f : A →ₗ[ℂ] T →ₗ[ℂ] T') (h : ∀ a : A, ∀ t ∈ R, f a t ∈ R')
    (a : A) (t : T) :
    descendAct R R' f h a (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (f a t) := rfl

end Descend

namespace SuperCommAlgebra.Mod

/-! ## Commutation of the action blocks -/

section Commutation

variable {S : SuperCommAlgebra.{u, u'}} (M : S.Mod.{u, u', w, w'})

/-- Two even scalars commute on the even component. -/
theorem actEE_actEE_comm (a b : S.even) (m : M.even) :
    M.actEE a (M.actEE b m) = M.actEE b (M.actEE a m) := by
  rw [← M.assoc_eee, S.comm_ee, M.assoc_eee]

/-- Two even scalars commute on the odd component. -/
theorem actEO_actEO_comm (a b : S.even) (m : M.odd) :
    M.actEO a (M.actEO b m) = M.actEO b (M.actEO a m) := by
  rw [← M.assoc_eeo, S.comm_ee, M.assoc_eeo]

/-- An even scalar commutes with an odd one, on the even
component. -/
theorem actEO_actOE (a : S.even) (c : S.odd) (m : M.even) :
    M.actEO a (M.actOE c m) = M.actOE c (M.actEE a m) := by
  rw [← M.assoc_eoe, S.comm_eo, M.assoc_oee]

/-- An even scalar commutes with an odd one, on the odd
component. -/
theorem actEE_actOO (a : S.even) (c : S.odd) (m : M.odd) :
    M.actEE a (M.actOO c m) = M.actOO c (M.actEO a m) := by
  rw [← M.assoc_eoo, S.comm_eo, M.assoc_oeo]

/-- Two odd scalars anticommute, on the even component. -/
theorem actOO_actOE_neg (c d : S.odd) (m : M.even) :
    M.actOO c (M.actOE d m) = -M.actOO d (M.actOE c m) := by
  rw [← M.assoc_ooe, S.comm_oo, map_neg, LinearMap.neg_apply,
    M.assoc_ooe]

/-- Two odd scalars anticommute, on the odd component. -/
theorem actOE_actOO_neg (c d : S.odd) (m : M.odd) :
    M.actOE c (M.actOO d m) = -M.actOE d (M.actOO c m) := by
  rw [← M.assoc_ooo, S.comm_oo, map_neg, LinearMap.neg_apply,
    M.assoc_ooo]

end Commutation

/-! ## The graded tensor product over ℂ -/

section Tensor

variable {S : SuperCommAlgebra.{u, u'}} (M N : S.Mod.{u, u', w, w'})

/-- The even component of the graded ℂ-tensor product of the
underlying super spaces. -/
abbrev tenEven : Type max w w' :=
  (M.even ⊗[ℂ] N.even) × (M.odd ⊗[ℂ] N.odd)

/-- The odd component of the graded ℂ-tensor product of the
underlying super spaces. -/
abbrev tenOdd : Type max w w' :=
  (M.even ⊗[ℂ] N.odd) × (M.odd ⊗[ℂ] N.even)

/-! ### The balancing relators -/

/-- The even-degree relator at parity pattern even-even-even. -/
def relEvenEEE (b : S.even) (m : M.even) (n : N.even) :
    tenEven M N :=
  (M.actEE b m ⊗ₜ[ℂ] n - m ⊗ₜ[ℂ] N.actEE b n, 0)

/-- The even-degree relator at parity pattern even-odd-odd. -/
def relEvenEOO (b : S.even) (m : M.odd) (n : N.odd) :
    tenEven M N :=
  (0, M.actEO b m ⊗ₜ[ℂ] n - m ⊗ₜ[ℂ] N.actEO b n)

/-- The even-degree relator at parity pattern odd-even-odd.  The
scalar is odd and the left argument even, so the Koszul sign is
`+1`. -/
def relEvenOEO (c : S.odd) (m : M.even) (n : N.odd) :
    tenEven M N :=
  (-(m ⊗ₜ[ℂ] N.actOO c n), M.actOE c m ⊗ₜ[ℂ] n)

/-- The even-degree relator at parity pattern odd-odd-even.  Both
the scalar and the left argument are odd, so the Koszul sign is
`−1` and the two terms are added. -/
def relEvenOOE (c : S.odd) (m : M.odd) (n : N.even) :
    tenEven M N :=
  (M.actOO c m ⊗ₜ[ℂ] n, m ⊗ₜ[ℂ] N.actOE c n)

/-- The odd-degree relator at parity pattern even-even-odd. -/
def relOddEEO (b : S.even) (m : M.even) (n : N.odd) :
    tenOdd M N :=
  (M.actEE b m ⊗ₜ[ℂ] n - m ⊗ₜ[ℂ] N.actEO b n, 0)

/-- The odd-degree relator at parity pattern even-odd-even. -/
def relOddEOE (b : S.even) (m : M.odd) (n : N.even) :
    tenOdd M N :=
  (0, M.actEO b m ⊗ₜ[ℂ] n - m ⊗ₜ[ℂ] N.actEE b n)

/-- The odd-degree relator at parity pattern odd-even-even.  The
Koszul sign is `+1`. -/
def relOddOEE (c : S.odd) (m : M.even) (n : N.even) :
    tenOdd M N :=
  (-(m ⊗ₜ[ℂ] N.actOE c n), M.actOE c m ⊗ₜ[ℂ] n)

/-- The odd-degree relator at parity pattern odd-odd-odd.  The
Koszul sign is `−1`. -/
def relOddOOO (c : S.odd) (m : M.odd) (n : N.odd) :
    tenOdd M N :=
  (M.actOO c m ⊗ₜ[ℂ] n, m ⊗ₜ[ℂ] N.actOO c n)

/-- The balancing submodule in even degree: the span of the four
even-degree relator families. -/
def balEven : Submodule ℂ (tenEven M N) :=
  Submodule.span ℂ
    ({t | ∃ b m n, t = relEvenEEE M N b m n} ∪
      {t | ∃ b m n, t = relEvenEOO M N b m n} ∪
      {t | ∃ c m n, t = relEvenOEO M N c m n} ∪
      {t | ∃ c m n, t = relEvenOOE M N c m n})

/-- The balancing submodule in odd degree: the span of the four
odd-degree relator families. -/
def balOdd : Submodule ℂ (tenOdd M N) :=
  Submodule.span ℂ
    ({t | ∃ b m n, t = relOddEEO M N b m n} ∪
      {t | ∃ b m n, t = relOddEOE M N b m n} ∪
      {t | ∃ c m n, t = relOddOEE M N c m n} ∪
      {t | ∃ c m n, t = relOddOOO M N c m n})

/-- The even-even-even relators are balanced. -/
theorem relEvenEEE_mem (b : S.even) (m : M.even) (n : N.even) :
    relEvenEEE M N b m n ∈ balEven M N :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨b, m, n, rfl⟩)))

/-- The even-odd-odd relators are balanced. -/
theorem relEvenEOO_mem (b : S.even) (m : M.odd) (n : N.odd) :
    relEvenEOO M N b m n ∈ balEven M N :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨b, m, n, rfl⟩)))

/-- The odd-even-odd relators are balanced. -/
theorem relEvenOEO_mem (c : S.odd) (m : M.even) (n : N.odd) :
    relEvenOEO M N c m n ∈ balEven M N :=
  Submodule.subset_span (Or.inl (Or.inr ⟨c, m, n, rfl⟩))

/-- The odd-odd-even relators are balanced. -/
theorem relEvenOOE_mem (c : S.odd) (m : M.odd) (n : N.even) :
    relEvenOOE M N c m n ∈ balEven M N :=
  Submodule.subset_span (Or.inr ⟨c, m, n, rfl⟩)

/-- The even-even-odd relators are balanced. -/
theorem relOddEEO_mem (b : S.even) (m : M.even) (n : N.odd) :
    relOddEEO M N b m n ∈ balOdd M N :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨b, m, n, rfl⟩)))

/-- The even-odd-even relators are balanced. -/
theorem relOddEOE_mem (b : S.even) (m : M.odd) (n : N.even) :
    relOddEOE M N b m n ∈ balOdd M N :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨b, m, n, rfl⟩)))

/-- The odd-even-even relators are balanced. -/
theorem relOddOEE_mem (c : S.odd) (m : M.even) (n : N.even) :
    relOddOEE M N c m n ∈ balOdd M N :=
  Submodule.subset_span (Or.inl (Or.inr ⟨c, m, n, rfl⟩))

/-- The odd-odd-odd relators are balanced. -/
theorem relOddOOO_mem (c : S.odd) (m : M.odd) (n : N.odd) :
    relOddOOO M N c m n ∈ balOdd M N :=
  Submodule.subset_span (Or.inr ⟨c, m, n, rfl⟩)

/-- The negated odd-even-odd relators, in expanded form. -/
theorem relEvenOEO_neg_mem (c : S.odd) (m : M.even) (n : N.odd) :
    ((m ⊗ₜ[ℂ] N.actOO c n, -(M.actOE c m ⊗ₜ[ℂ] n)) : tenEven M N)
      ∈ balEven M N := by
  have h := neg_mem (relEvenOEO_mem M N c m n)
  simpa [relEvenOEO] using h

/-- The negated odd-odd-even relators, in expanded form. -/
theorem relEvenOOE_neg_mem (c : S.odd) (m : M.odd) (n : N.even) :
    ((-(M.actOO c m ⊗ₜ[ℂ] n), -(m ⊗ₜ[ℂ] N.actOE c n)) :
        tenEven M N) ∈ balEven M N := by
  have h := neg_mem (relEvenOOE_mem M N c m n)
  simpa [relEvenOOE] using h

/-- The negated odd-even-even relators, in expanded form. -/
theorem relOddOEE_neg_mem (c : S.odd) (m : M.even) (n : N.even) :
    ((m ⊗ₜ[ℂ] N.actOE c n, -(M.actOE c m ⊗ₜ[ℂ] n)) : tenOdd M N)
      ∈ balOdd M N := by
  have h := neg_mem (relOddOEE_mem M N c m n)
  simpa [relOddOEE] using h

/-- The negated odd-odd-odd relators, in expanded form. -/
theorem relOddOOO_neg_mem (c : S.odd) (m : M.odd) (n : N.odd) :
    ((-(M.actOO c m ⊗ₜ[ℂ] n), -(m ⊗ₜ[ℂ] N.actOO c n)) :
        tenOdd M N) ∈ balOdd M N := by
  have h := neg_mem (relOddOOO_mem M N c m n)
  simpa [relOddOOO] using h

/-! ### The four action blocks before quotienting -/

/-- An even scalar acting on the left factor of the even part. -/
noncomputable def preActEE :
    S.even →ₗ[ℂ] tenEven M N →ₗ[ℂ] tenEven M N :=
  tensorLeftDiag N.even N.odd M.actEE M.actEO

/-- An even scalar acting on the left factor of the odd part. -/
noncomputable def preActEO :
    S.even →ₗ[ℂ] tenOdd M N →ₗ[ℂ] tenOdd M N :=
  tensorLeftDiag N.odd N.even M.actEE M.actEO

/-- An odd scalar acting on the left factor of the even part. -/
noncomputable def preActOE :
    S.odd →ₗ[ℂ] tenEven M N →ₗ[ℂ] tenOdd M N :=
  tensorLeftSwap N.even N.odd M.actOE M.actOO

/-- An odd scalar acting on the left factor of the odd part. -/
noncomputable def preActOO :
    S.odd →ₗ[ℂ] tenOdd M N →ₗ[ℂ] tenEven M N :=
  tensorLeftSwap N.odd N.even M.actOE M.actOO

/-- The even-even block, evaluated. -/
@[simp]
theorem preActEE_apply (a : S.even) (t : tenEven M N) :
    preActEE M N a t =
      ((M.actEE a).rTensor N.even t.1,
        (M.actEO a).rTensor N.odd t.2) := rfl

/-- The even-odd block, evaluated. -/
@[simp]
theorem preActEO_apply (a : S.even) (t : tenOdd M N) :
    preActEO M N a t =
      ((M.actEE a).rTensor N.odd t.1,
        (M.actEO a).rTensor N.even t.2) := rfl

/-- The odd-even block, evaluated. -/
@[simp]
theorem preActOE_apply (c : S.odd) (t : tenEven M N) :
    preActOE M N c t =
      ((M.actOO c).rTensor N.odd t.2,
        (M.actOE c).rTensor N.even t.1) := rfl

/-- The odd-odd block, evaluated. -/
@[simp]
theorem preActOO_apply (c : S.odd) (t : tenOdd M N) :
    preActOO M N c t =
      ((M.actOO c).rTensor N.even t.2,
        (M.actOE c).rTensor N.odd t.1) := rfl

/-! ### The module laws before quotienting -/

/-- The unit acts as the identity on the even part. -/
theorem preActEE_one (t : tenEven M N) :
    preActEE M N S.one t = t := by
  have h1 : M.actEE S.one = LinearMap.id := LinearMap.ext M.one_act_e
  have h2 : M.actEO S.one = LinearMap.id := LinearMap.ext M.one_act_o
  rw [preActEE_apply, h1, h2, LinearMap.rTensor_id_apply,
    LinearMap.rTensor_id_apply]

/-- The unit acts as the identity on the odd part. -/
theorem preActEO_one (t : tenOdd M N) :
    preActEO M N S.one t = t := by
  have h1 : M.actEE S.one = LinearMap.id := LinearMap.ext M.one_act_e
  have h2 : M.actEO S.one = LinearMap.id := LinearMap.ext M.one_act_o
  rw [preActEO_apply, h1, h2, LinearMap.rTensor_id_apply,
    LinearMap.rTensor_id_apply]

/-- Associativity at parity pattern even-even-even. -/
theorem preActEE_mulEE (x y : S.even) (t : tenEven M N) :
    preActEE M N (S.mulEE x y) t
      = preActEE M N x (preActEE M N y t) := by
  have h1 : M.actEE (S.mulEE x y) = M.actEE x ∘ₗ M.actEE y :=
    LinearMap.ext (M.assoc_eee x y)
  have h2 : M.actEO (S.mulEE x y) = M.actEO x ∘ₗ M.actEO y :=
    LinearMap.ext (M.assoc_eeo x y)
  simp only [preActEE_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern even-even-odd. -/
theorem preActEO_mulEE (x y : S.even) (t : tenOdd M N) :
    preActEO M N (S.mulEE x y) t
      = preActEO M N x (preActEO M N y t) := by
  have h1 : M.actEE (S.mulEE x y) = M.actEE x ∘ₗ M.actEE y :=
    LinearMap.ext (M.assoc_eee x y)
  have h2 : M.actEO (S.mulEE x y) = M.actEO x ∘ₗ M.actEO y :=
    LinearMap.ext (M.assoc_eeo x y)
  simp only [preActEO_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern even-odd-even. -/
theorem preActOE_mulEO (x : S.even) (u : S.odd) (t : tenEven M N) :
    preActOE M N (S.mulEO x u) t
      = preActEO M N x (preActOE M N u t) := by
  have h1 : M.actOO (S.mulEO x u) = M.actEE x ∘ₗ M.actOO u :=
    LinearMap.ext (M.assoc_eoo x u)
  have h2 : M.actOE (S.mulEO x u) = M.actEO x ∘ₗ M.actOE u :=
    LinearMap.ext (M.assoc_eoe x u)
  simp only [preActOE_apply, preActEO_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern even-odd-odd. -/
theorem preActOO_mulEO (x : S.even) (u : S.odd) (t : tenOdd M N) :
    preActOO M N (S.mulEO x u) t
      = preActEE M N x (preActOO M N u t) := by
  have h1 : M.actOO (S.mulEO x u) = M.actEE x ∘ₗ M.actOO u :=
    LinearMap.ext (M.assoc_eoo x u)
  have h2 : M.actOE (S.mulEO x u) = M.actEO x ∘ₗ M.actOE u :=
    LinearMap.ext (M.assoc_eoe x u)
  simp only [preActOO_apply, preActEE_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern odd-even-even. -/
theorem preActOE_mulOE (u : S.odd) (x : S.even) (t : tenEven M N) :
    preActOE M N (S.mulOE u x) t
      = preActOE M N u (preActEE M N x t) := by
  have h1 : M.actOO (S.mulOE u x) = M.actOO u ∘ₗ M.actEO x :=
    LinearMap.ext (M.assoc_oeo u x)
  have h2 : M.actOE (S.mulOE u x) = M.actOE u ∘ₗ M.actEE x :=
    LinearMap.ext (M.assoc_oee u x)
  simp only [preActOE_apply, preActEE_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern odd-even-odd. -/
theorem preActOO_mulOE (u : S.odd) (x : S.even) (t : tenOdd M N) :
    preActOO M N (S.mulOE u x) t
      = preActOO M N u (preActEO M N x t) := by
  have h1 : M.actOO (S.mulOE u x) = M.actOO u ∘ₗ M.actEO x :=
    LinearMap.ext (M.assoc_oeo u x)
  have h2 : M.actOE (S.mulOE u x) = M.actOE u ∘ₗ M.actEE x :=
    LinearMap.ext (M.assoc_oee u x)
  simp only [preActOO_apply, preActEO_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern odd-odd-even. -/
theorem preActEE_mulOO (u v : S.odd) (t : tenEven M N) :
    preActEE M N (S.mulOO u v) t
      = preActOO M N u (preActOE M N v t) := by
  have h1 : M.actEE (S.mulOO u v) = M.actOO u ∘ₗ M.actOE v :=
    LinearMap.ext (M.assoc_ooe u v)
  have h2 : M.actEO (S.mulOO u v) = M.actOE u ∘ₗ M.actOO v :=
    LinearMap.ext (M.assoc_ooo u v)
  simp only [preActEE_apply, preActOO_apply, preActOE_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-- Associativity at parity pattern odd-odd-odd. -/
theorem preActEO_mulOO (u v : S.odd) (t : tenOdd M N) :
    preActEO M N (S.mulOO u v) t
      = preActOE M N u (preActOO M N v t) := by
  have h1 : M.actEE (S.mulOO u v) = M.actOO u ∘ₗ M.actOE v :=
    LinearMap.ext (M.assoc_ooe u v)
  have h2 : M.actEO (S.mulOO u v) = M.actOE u ∘ₗ M.actOO v :=
    LinearMap.ext (M.assoc_ooo u v)
  simp only [preActEO_apply, preActOE_apply, preActOO_apply]
  rw [h1, h2, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]

/-! ### The blocks preserve balancing -/

/-- An even scalar carries the even balancing submodule into
itself. -/
theorem preActEE_mem_balEven (a : S.even) (t : tenEven M N)
    (ht : t ∈ balEven M N) : preActEE M N a t ∈ balEven M N := by
  have key : balEven M N ≤
      Submodule.comap (preActEE M N a) (balEven M N) := by
    refine Submodule.span_le.mpr ?_
    intro s hs
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
      ⟨c, m, n, rfl⟩) | ⟨c, m, n, rfl⟩)
    · simp only [relEvenEEE, preActEE_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [M.actEE_actEE_comm]
      exact relEvenEEE_mem M N b (M.actEE a m) n
    · simp only [relEvenEOO, preActEE_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [M.actEO_actEO_comm]
      exact relEvenEOO_mem M N b (M.actEO a m) n
    · simp only [relEvenOEO, preActEE_apply, map_neg,
        LinearMap.rTensor_tmul]
      rw [M.actEO_actOE]
      exact relEvenOEO_mem M N c (M.actEE a m) n
    · simp only [relEvenOOE, preActEE_apply,
        LinearMap.rTensor_tmul]
      rw [M.actEE_actOO]
      exact relEvenOOE_mem M N c (M.actEO a m) n
  exact key ht

/-- An even scalar carries the odd balancing submodule into
itself. -/
theorem preActEO_mem_balOdd (a : S.even) (t : tenOdd M N)
    (ht : t ∈ balOdd M N) : preActEO M N a t ∈ balOdd M N := by
  have key : balOdd M N ≤
      Submodule.comap (preActEO M N a) (balOdd M N) := by
    refine Submodule.span_le.mpr ?_
    intro s hs
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
      ⟨c, m, n, rfl⟩) | ⟨c, m, n, rfl⟩)
    · simp only [relOddEEO, preActEO_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [M.actEE_actEE_comm]
      exact relOddEEO_mem M N b (M.actEE a m) n
    · simp only [relOddEOE, preActEO_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [M.actEO_actEO_comm]
      exact relOddEOE_mem M N b (M.actEO a m) n
    · simp only [relOddOEE, preActEO_apply, map_neg,
        LinearMap.rTensor_tmul]
      rw [M.actEO_actOE]
      exact relOddOEE_mem M N c (M.actEE a m) n
    · simp only [relOddOOO, preActEO_apply,
        LinearMap.rTensor_tmul]
      rw [M.actEE_actOO]
      exact relOddOOO_mem M N c (M.actEO a m) n
  exact key ht

/-- An odd scalar carries the even balancing submodule into the
odd one. -/
theorem preActOE_mem_balOdd (c : S.odd) (t : tenEven M N)
    (ht : t ∈ balEven M N) : preActOE M N c t ∈ balOdd M N := by
  have key : balEven M N ≤
      Submodule.comap (preActOE M N c) (balOdd M N) := by
    refine Submodule.span_le.mpr ?_
    intro s hs
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
      ⟨d, m, n, rfl⟩) | ⟨d, m, n, rfl⟩)
    · simp only [relEvenEEE, preActOE_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [← M.actEO_actOE]
      exact relOddEOE_mem M N b (M.actOE c m) n
    · simp only [relEvenEOO, preActOE_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [← M.actEE_actOO]
      exact relOddEEO_mem M N b (M.actOO c m) n
    · simp only [relEvenOEO, preActOE_apply, map_neg,
        LinearMap.rTensor_tmul]
      rw [M.actOO_actOE_neg, TensorProduct.neg_tmul]
      exact relOddOOO_neg_mem M N d (M.actOE c m) n
    · simp only [relEvenOOE, preActOE_apply,
        LinearMap.rTensor_tmul]
      rw [M.actOE_actOO_neg, TensorProduct.neg_tmul]
      exact relOddOEE_neg_mem M N d (M.actOO c m) n
  exact key ht

/-- An odd scalar carries the odd balancing submodule into the
even one. -/
theorem preActOO_mem_balEven (c : S.odd) (t : tenOdd M N)
    (ht : t ∈ balOdd M N) : preActOO M N c t ∈ balEven M N := by
  have key : balOdd M N ≤
      Submodule.comap (preActOO M N c) (balEven M N) := by
    refine Submodule.span_le.mpr ?_
    intro s hs
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
      ⟨d, m, n, rfl⟩) | ⟨d, m, n, rfl⟩)
    · simp only [relOddEEO, preActOO_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [← M.actEO_actOE]
      exact relEvenEOO_mem M N b (M.actOE c m) n
    · simp only [relOddEOE, preActOO_apply, map_sub, map_zero,
        LinearMap.rTensor_tmul]
      rw [← M.actEE_actOO]
      exact relEvenEEE_mem M N b (M.actOO c m) n
    · simp only [relOddOEE, preActOO_apply, map_neg,
        LinearMap.rTensor_tmul]
      rw [M.actOO_actOE_neg, TensorProduct.neg_tmul]
      exact relEvenOOE_neg_mem M N d (M.actOE c m) n
    · simp only [relOddOOO, preActOO_apply,
        LinearMap.rTensor_tmul]
      rw [M.actOE_actOO_neg, TensorProduct.neg_tmul]
      exact relEvenOEO_neg_mem M N d (M.actOO c m) n
  exact key ht

/-! ### The tensor product -/

/-- **The tensor product of two super modules** over a
super-commutative ℂ-algebra: the graded ℂ-tensor product of the
underlying super spaces, quotiented in each degree by the
balancing relators, with the `S`-action induced from the action on
the left factor. -/
noncomputable def tensor : S.Mod where
  even := tenEven M N ⧸ balEven M N
  odd := tenOdd M N ⧸ balOdd M N
  actEE := descendAct _ _ (preActEE M N) (preActEE_mem_balEven M N)
  actEO := descendAct _ _ (preActEO M N) (preActEO_mem_balOdd M N)
  actOE := descendAct _ _ (preActOE M N) (preActOE_mem_balOdd M N)
  actOO := descendAct _ _ (preActOO M N) (preActOO_mem_balEven M N)
  one_act_e m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, preActEE_one]
  one_act_o m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, preActEO_one]
  assoc_eee x y m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActEE_mulEE]
  assoc_eeo x y m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActEO_mulEE]
  assoc_eoe x u m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActOE_mulEO]
  assoc_eoo x u m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActOO_mulEO]
  assoc_oee u x m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActOE_mulOE]
  assoc_oeo u x m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActOO_mulOE]
  assoc_ooe u v m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActEE_mulOO]
  assoc_ooo u v m := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [descendAct_apply, descendAct_apply, descendAct_apply,
      preActEO_mulOO]

/-! ### The canonical balanced map -/

/-- The canonical map, even times even. -/
noncomputable def tmulEE :
    M.even →ₗ[ℂ] N.even →ₗ[ℂ] (tensor M N).even :=
  LinearMap.compr₂ (TensorProduct.mk ℂ M.even N.even)
    ((balEven M N).mkQ ∘ₗ LinearMap.inl ℂ _ _)

/-- The canonical map, odd times odd. -/
noncomputable def tmulOO :
    M.odd →ₗ[ℂ] N.odd →ₗ[ℂ] (tensor M N).even :=
  LinearMap.compr₂ (TensorProduct.mk ℂ M.odd N.odd)
    ((balEven M N).mkQ ∘ₗ LinearMap.inr ℂ _ _)

/-- The canonical map, even times odd. -/
noncomputable def tmulEO :
    M.even →ₗ[ℂ] N.odd →ₗ[ℂ] (tensor M N).odd :=
  LinearMap.compr₂ (TensorProduct.mk ℂ M.even N.odd)
    ((balOdd M N).mkQ ∘ₗ LinearMap.inl ℂ _ _)

/-- The canonical map, odd times even. -/
noncomputable def tmulOE :
    M.odd →ₗ[ℂ] N.even →ₗ[ℂ] (tensor M N).odd :=
  LinearMap.compr₂ (TensorProduct.mk ℂ M.odd N.even)
    ((balOdd M N).mkQ ∘ₗ LinearMap.inr ℂ _ _)

/-- The even-even canonical map, evaluated.  Not a `simp` lemma:
the quotient class is the implementation, and `tmulEE` is the
interface the computation rules downstream are stated in. -/
theorem tmulEE_apply (m : M.even) (n : N.even) :
    tmulEE M N m n =
      Submodule.Quotient.mk ((m ⊗ₜ[ℂ] n, 0) : tenEven M N) := rfl

/-- The odd-odd canonical map, evaluated.  Not a `simp` lemma, for
the reason given at `tmulEE_apply`. -/
theorem tmulOO_apply (m : M.odd) (n : N.odd) :
    tmulOO M N m n =
      Submodule.Quotient.mk ((0, m ⊗ₜ[ℂ] n) : tenEven M N) := rfl

/-- The even-odd canonical map, evaluated.  Not a `simp` lemma, for
the reason given at `tmulEE_apply`. -/
theorem tmulEO_apply (m : M.even) (n : N.odd) :
    tmulEO M N m n =
      Submodule.Quotient.mk ((m ⊗ₜ[ℂ] n, 0) : tenOdd M N) := rfl

/-- The odd-even canonical map, evaluated.  Not a `simp` lemma, for
the reason given at `tmulEE_apply`. -/
theorem tmulOE_apply (m : M.odd) (n : N.even) :
    tmulOE M N m n =
      Submodule.Quotient.mk ((0, m ⊗ₜ[ℂ] n) : tenOdd M N) := rfl

/-! #### Balancing -/

/-- Balancing at parity pattern even-even-even. -/
theorem tmulEE_balanced_eee (b : S.even) (m : M.even) (n : N.even) :
    tmulEE M N (M.actEE b m) n = tmulEE M N m (N.actEE b n) := by
  rw [tmulEE_apply, tmulEE_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, sub_zero]
  exact relEvenEEE_mem M N b m n

/-- Balancing at parity pattern even-odd-odd. -/
theorem tmulOO_balanced_eoo (b : S.even) (m : M.odd) (n : N.odd) :
    tmulOO M N (M.actEO b m) n = tmulOO M N m (N.actEO b n) := by
  rw [tmulOO_apply, tmulOO_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, sub_zero]
  exact relEvenEOO_mem M N b m n

/-- Balancing at parity pattern odd-even-odd. -/
theorem tmulOO_balanced_oeo (c : S.odd) (m : M.even) (n : N.odd) :
    tmulOO M N (M.actOE c m) n = tmulEE M N m (N.actOO c n) := by
  rw [tmulOO_apply, tmulEE_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, zero_sub, sub_zero]
  exact relEvenOEO_mem M N c m n

/-- Balancing at parity pattern odd-odd-even: both arguments are
odd, so the Koszul sign appears. -/
theorem tmulEE_balanced_ooe (c : S.odd) (m : M.odd) (n : N.even) :
    tmulEE M N (M.actOO c m) n = -tmulOO M N m (N.actOE c n) := by
  rw [tmulEE_apply, tmulOO_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.neg_mk, neg_zero, Prod.mk_sub_mk, sub_zero,
    sub_neg_eq_add, zero_add]
  exact relEvenOOE_mem M N c m n

/-- Balancing at parity pattern even-even-odd. -/
theorem tmulEO_balanced_eeo (b : S.even) (m : M.even) (n : N.odd) :
    tmulEO M N (M.actEE b m) n = tmulEO M N m (N.actEO b n) := by
  rw [tmulEO_apply, tmulEO_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, sub_zero]
  exact relOddEEO_mem M N b m n

/-- Balancing at parity pattern even-odd-even. -/
theorem tmulOE_balanced_eoe (b : S.even) (m : M.odd) (n : N.even) :
    tmulOE M N (M.actEO b m) n = tmulOE M N m (N.actEE b n) := by
  rw [tmulOE_apply, tmulOE_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, sub_zero]
  exact relOddEOE_mem M N b m n

/-- Balancing at parity pattern odd-even-even. -/
theorem tmulOE_balanced_oee (c : S.odd) (m : M.even) (n : N.even) :
    tmulOE M N (M.actOE c m) n = tmulEO M N m (N.actOE c n) := by
  rw [tmulOE_apply, tmulEO_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.mk_sub_mk, zero_sub, sub_zero]
  exact relOddOEE_mem M N c m n

/-- Balancing at parity pattern odd-odd-odd: both arguments are
odd, so the Koszul sign appears. -/
theorem tmulEO_balanced_ooo (c : S.odd) (m : M.odd) (n : N.odd) :
    tmulEO M N (M.actOO c m) n = -tmulOE M N m (N.actOO c n) := by
  rw [tmulEO_apply, tmulOE_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Prod.neg_mk, neg_zero, Prod.mk_sub_mk, sub_zero,
    sub_neg_eq_add, zero_add]
  exact relOddOOO_mem M N c m n

/-! #### The action on the canonical map -/

/-- An even scalar acts on the left factor, even times even. -/
theorem actEE_tmulEE (a : S.even) (m : M.even) (n : N.even) :
    (tensor M N).actEE a (tmulEE M N m n)
      = tmulEE M N (M.actEE a m) n := rfl

/-- An even scalar acts on the left factor, odd times odd. -/
theorem actEE_tmulOO (a : S.even) (m : M.odd) (n : N.odd) :
    (tensor M N).actEE a (tmulOO M N m n)
      = tmulOO M N (M.actEO a m) n := rfl

/-- An even scalar acts on the left factor, even times odd. -/
theorem actEO_tmulEO (a : S.even) (m : M.even) (n : N.odd) :
    (tensor M N).actEO a (tmulEO M N m n)
      = tmulEO M N (M.actEE a m) n := rfl

/-- An even scalar acts on the left factor, odd times even. -/
theorem actEO_tmulOE (a : S.even) (m : M.odd) (n : N.even) :
    (tensor M N).actEO a (tmulOE M N m n)
      = tmulOE M N (M.actEO a m) n := rfl

/-- An odd scalar acts on the left factor, even times even. -/
theorem actOE_tmulEE (c : S.odd) (m : M.even) (n : N.even) :
    (tensor M N).actOE c (tmulEE M N m n)
      = tmulOE M N (M.actOE c m) n := by
  change Submodule.Quotient.mk
      (preActOE M N c ((m ⊗ₜ[ℂ] n, 0) : tenEven M N))
    = Submodule.Quotient.mk
      ((0, M.actOE c m ⊗ₜ[ℂ] n) : tenOdd M N)
  rw [preActOE_apply]
  simp only [LinearMap.rTensor_tmul, map_zero]

/-- An odd scalar acts on the left factor, odd times odd. -/
theorem actOE_tmulOO (c : S.odd) (m : M.odd) (n : N.odd) :
    (tensor M N).actOE c (tmulOO M N m n)
      = tmulEO M N (M.actOO c m) n := by
  change Submodule.Quotient.mk
      (preActOE M N c ((0, m ⊗ₜ[ℂ] n) : tenEven M N))
    = Submodule.Quotient.mk
      ((M.actOO c m ⊗ₜ[ℂ] n, 0) : tenOdd M N)
  rw [preActOE_apply]
  simp only [LinearMap.rTensor_tmul, map_zero]

/-- An odd scalar acts on the left factor, even times odd. -/
theorem actOO_tmulEO (c : S.odd) (m : M.even) (n : N.odd) :
    (tensor M N).actOO c (tmulEO M N m n)
      = tmulOO M N (M.actOE c m) n := by
  change Submodule.Quotient.mk
      (preActOO M N c ((m ⊗ₜ[ℂ] n, 0) : tenOdd M N))
    = Submodule.Quotient.mk
      ((0, M.actOE c m ⊗ₜ[ℂ] n) : tenEven M N)
  rw [preActOO_apply]
  simp only [LinearMap.rTensor_tmul, map_zero]

/-- An odd scalar acts on the left factor, odd times even. -/
theorem actOO_tmulOE (c : S.odd) (m : M.odd) (n : N.even) :
    (tensor M N).actOO c (tmulOE M N m n)
      = tmulEE M N (M.actOO c m) n := by
  change Submodule.Quotient.mk
      (preActOO M N c ((0, m ⊗ₜ[ℂ] n) : tenOdd M N))
    = Submodule.Quotient.mk
      ((M.actOO c m ⊗ₜ[ℂ] n, 0) : tenEven M N)
  rw [preActOO_apply]
  simp only [LinearMap.rTensor_tmul, map_zero]

/-! ### The universal property -/

section Universal

variable {P : Type v}

/-- **The even-degree lift**: a pair of ℂ-bilinear maps out of the
even-even and odd-odd blocks, balanced against the four
even-degree relator families, factors through the even part of the
tensor product. -/
noncomputable def liftEven [AddCommGroup P] [Module ℂ P]
    (fee : M.even →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (foo : M.odd →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (hee : ∀ (b : S.even) (m : M.even) (n : N.even),
      fee (M.actEE b m) n = fee m (N.actEE b n))
    (hoo : ∀ (b : S.even) (m : M.odd) (n : N.odd),
      foo (M.actEO b m) n = foo m (N.actEO b n))
    (hoeo : ∀ (c : S.odd) (m : M.even) (n : N.odd),
      foo (M.actOE c m) n = fee m (N.actOO c n))
    (hooe : ∀ (c : S.odd) (m : M.odd) (n : N.even),
      fee (M.actOO c m) n = -foo m (N.actOE c n)) :
    (tensor M N).even →ₗ[ℂ] P :=
  (balEven M N).liftQ
    ((TensorProduct.lift fee).coprod (TensorProduct.lift foo)) (by
      refine Submodule.span_le.mpr ?_
      intro s hs
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
        ⟨c, m, n, rfl⟩) | ⟨c, m, n, rfl⟩)
      · simp only [relEvenEEE, LinearMap.coprod_apply, map_sub,
          map_zero, TensorProduct.lift.tmul, add_zero, sub_eq_zero]
        exact hee b m n
      · simp only [relEvenEOO, LinearMap.coprod_apply, map_sub,
          map_zero, TensorProduct.lift.tmul, zero_add, sub_eq_zero]
        exact hoo b m n
      · simp only [relEvenOEO, LinearMap.coprod_apply, map_neg,
          TensorProduct.lift.tmul, neg_add_eq_zero]
        exact (hoeo c m n).symm
      · simp only [relEvenOOE, LinearMap.coprod_apply,
          TensorProduct.lift.tmul, add_eq_zero_iff_eq_neg]
        exact hooe c m n)

/-- **The odd-degree lift**: a pair of ℂ-bilinear maps out of the
even-odd and odd-even blocks, balanced against the four odd-degree
relator families, factors through the odd part of the tensor
product. -/
noncomputable def liftOdd [AddCommGroup P] [Module ℂ P]
    (feo : M.even →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (foe : M.odd →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (heeo : ∀ (b : S.even) (m : M.even) (n : N.odd),
      feo (M.actEE b m) n = feo m (N.actEO b n))
    (heoe : ∀ (b : S.even) (m : M.odd) (n : N.even),
      foe (M.actEO b m) n = foe m (N.actEE b n))
    (hoee : ∀ (c : S.odd) (m : M.even) (n : N.even),
      foe (M.actOE c m) n = feo m (N.actOE c n))
    (hooo : ∀ (c : S.odd) (m : M.odd) (n : N.odd),
      feo (M.actOO c m) n = -foe m (N.actOO c n)) :
    (tensor M N).odd →ₗ[ℂ] P :=
  (balOdd M N).liftQ
    ((TensorProduct.lift feo).coprod (TensorProduct.lift foe)) (by
      refine Submodule.span_le.mpr ?_
      intro s hs
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hs with (((⟨b, m, n, rfl⟩ | ⟨b, m, n, rfl⟩) |
        ⟨c, m, n, rfl⟩) | ⟨c, m, n, rfl⟩)
      · simp only [relOddEEO, LinearMap.coprod_apply, map_sub,
          map_zero, TensorProduct.lift.tmul, add_zero, sub_eq_zero]
        exact heeo b m n
      · simp only [relOddEOE, LinearMap.coprod_apply, map_sub,
          map_zero, TensorProduct.lift.tmul, zero_add, sub_eq_zero]
        exact heoe b m n
      · simp only [relOddOEE, LinearMap.coprod_apply, map_neg,
          TensorProduct.lift.tmul, neg_add_eq_zero]
        exact (hoee c m n).symm
      · simp only [relOddOOO, LinearMap.coprod_apply,
          TensorProduct.lift.tmul, add_eq_zero_iff_eq_neg]
        exact hooo c m n)

/-- The even-degree lift computes on even-even products. -/
@[simp]
theorem liftEven_tmulEE
    [AddCommGroup P] [Module ℂ P] (fee : M.even →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (foo : M.odd →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (hee : ∀ (b : S.even) (m : M.even) (n : N.even), fee (M.actEE b m) n =
      fee m (N.actEE b n))
    (hoo : ∀ (b : S.even) (m : M.odd) (n : N.odd), foo (M.actEO b m) n = foo
      m (N.actEO b n))
    (hoeo : ∀ (c : S.odd) (m : M.even) (n : N.odd), foo (M.actOE c m) n =
      fee m (N.actOO c n))
    (hooe : ∀ (c : S.odd) (m : M.odd) (n : N.even), fee (M.actOO c m) n =
      -foo m (N.actOE c n))
    (m : M.even) (n : N.even) :
    liftEven M N fee foo hee hoo hoeo hooe (tmulEE M N m n)
      = fee m n := by
  change TensorProduct.lift fee (m ⊗ₜ[ℂ] n)
      + TensorProduct.lift foo 0 = fee m n
  rw [map_zero, add_zero, TensorProduct.lift.tmul]

/-- The even-degree lift computes on odd-odd products. -/
@[simp]
theorem liftEven_tmulOO
    [AddCommGroup P] [Module ℂ P] (fee : M.even →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (foo : M.odd →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (hee : ∀ (b : S.even) (m : M.even) (n : N.even), fee (M.actEE b m) n =
      fee m (N.actEE b n))
    (hoo : ∀ (b : S.even) (m : M.odd) (n : N.odd), foo (M.actEO b m) n = foo
      m (N.actEO b n))
    (hoeo : ∀ (c : S.odd) (m : M.even) (n : N.odd), foo (M.actOE c m) n =
      fee m (N.actOO c n))
    (hooe : ∀ (c : S.odd) (m : M.odd) (n : N.even), fee (M.actOO c m) n =
      -foo m (N.actOE c n))
    (m : M.odd) (n : N.odd) :
    liftEven M N fee foo hee hoo hoeo hooe (tmulOO M N m n)
      = foo m n := by
  change TensorProduct.lift fee 0
      + TensorProduct.lift foo (m ⊗ₜ[ℂ] n) = foo m n
  rw [map_zero, zero_add, TensorProduct.lift.tmul]

/-- The odd-degree lift computes on even-odd products. -/
@[simp]
theorem liftOdd_tmulEO
    [AddCommGroup P] [Module ℂ P] (feo : M.even →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (foe : M.odd →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (heeo : ∀ (b : S.even) (m : M.even) (n : N.odd), feo (M.actEE b m) n =
      feo m (N.actEO b n))
    (heoe : ∀ (b : S.even) (m : M.odd) (n : N.even), foe (M.actEO b m) n =
      foe m (N.actEE b n))
    (hoee : ∀ (c : S.odd) (m : M.even) (n : N.even), foe (M.actOE c m) n =
      feo m (N.actOE c n))
    (hooo : ∀ (c : S.odd) (m : M.odd) (n : N.odd), feo (M.actOO c m) n =
      -foe m (N.actOO c n))
    (m : M.even) (n : N.odd) :
    liftOdd M N feo foe heeo heoe hoee hooo (tmulEO M N m n)
      = feo m n := by
  change TensorProduct.lift feo (m ⊗ₜ[ℂ] n)
      + TensorProduct.lift foe 0 = feo m n
  rw [map_zero, add_zero, TensorProduct.lift.tmul]

/-- The odd-degree lift computes on odd-even products. -/
@[simp]
theorem liftOdd_tmulOE
    [AddCommGroup P] [Module ℂ P] (feo : M.even →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (foe : M.odd →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (heeo : ∀ (b : S.even) (m : M.even) (n : N.odd), feo (M.actEE b m) n =
      feo m (N.actEO b n))
    (heoe : ∀ (b : S.even) (m : M.odd) (n : N.even), foe (M.actEO b m) n =
      foe m (N.actEE b n))
    (hoee : ∀ (c : S.odd) (m : M.even) (n : N.even), foe (M.actOE c m) n =
      feo m (N.actOE c n))
    (hooo : ∀ (c : S.odd) (m : M.odd) (n : N.odd), feo (M.actOO c m) n =
      -foe m (N.actOO c n))
    (m : M.odd) (n : N.even) :
    liftOdd M N feo foe heeo heoe hoee hooo (tmulOE M N m n)
      = foe m n := by
  change TensorProduct.lift feo 0
      + TensorProduct.lift foe (m ⊗ₜ[ℂ] n) = foe m n
  rw [map_zero, zero_add, TensorProduct.lift.tmul]

/-- **Uniqueness in even degree**: the even part of the tensor
product is generated by the even-even and odd-odd products. -/
theorem liftEven_unique [AddCommGroup P] [Module ℂ P]
    (g g' : (tensor M N).even →ₗ[ℂ] P)
    (hE : ∀ m n, g (tmulEE M N m n) = g' (tmulEE M N m n))
    (hO : ∀ m n, g (tmulOO M N m n) = g' (tmulOO M N m n)) :
    g = g' :=
  Submodule.linearMap_qext _
    (LinearMap.prod_ext (TensorProduct.ext' hE) (TensorProduct.ext' hO))

/-- **Uniqueness in odd degree**: the odd part of the tensor
product is generated by the even-odd and odd-even products. -/
theorem liftOdd_unique [AddCommGroup P] [Module ℂ P]
    (g g' : (tensor M N).odd →ₗ[ℂ] P)
    (hE : ∀ m n, g (tmulEO M N m n) = g' (tmulEO M N m n))
    (hO : ∀ m n, g (tmulOE M N m n) = g' (tmulOE M N m n)) :
    g = g' :=
  Submodule.linearMap_qext _
    (LinearMap.prod_ext (TensorProduct.ext' hE) (TensorProduct.ext' hO))

/-- **The universal property in even degree**: a balanced pair of
ℂ-bilinear maps out of the even-even and odd-odd blocks factors
uniquely through the even part of the tensor product. -/
theorem exists_unique_liftEven
    [AddCommGroup P] [Module ℂ P] (fee : M.even →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (foo : M.odd →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (hee : ∀ (b : S.even) (m : M.even) (n : N.even), fee (M.actEE b m) n =
      fee m (N.actEE b n))
    (hoo : ∀ (b : S.even) (m : M.odd) (n : N.odd), foo (M.actEO b m) n = foo
      m (N.actEO b n))
    (hoeo : ∀ (c : S.odd) (m : M.even) (n : N.odd), foo (M.actOE c m) n =
      fee m (N.actOO c n))
    (hooe : ∀ (c : S.odd) (m : M.odd) (n : N.even), fee (M.actOO c m) n =
      -foo m (N.actOE c n)) :
    ∃! g : (tensor M N).even →ₗ[ℂ] P,
      (∀ m n, g (tmulEE M N m n) = fee m n) ∧
        (∀ m n, g (tmulOO M N m n) = foo m n) :=
  ⟨liftEven M N fee foo hee hoo hoeo hooe,
    ⟨liftEven_tmulEE M N fee foo hee hoo hoeo hooe,
      liftEven_tmulOO M N fee foo hee hoo hoeo hooe⟩,
    fun g hg => liftEven_unique M N g _
      (fun m n => (hg.1 m n).trans
        (liftEven_tmulEE M N fee foo hee hoo hoeo hooe m n).symm)
      (fun m n => (hg.2 m n).trans
        (liftEven_tmulOO M N fee foo hee hoo hoeo hooe m n).symm)⟩

/-- **The universal property in odd degree**: a balanced pair of
ℂ-bilinear maps out of the even-odd and odd-even blocks factors
uniquely through the odd part of the tensor product. -/
theorem exists_unique_liftOdd
    [AddCommGroup P] [Module ℂ P] (feo : M.even →ₗ[ℂ] N.odd →ₗ[ℂ] P)
    (foe : M.odd →ₗ[ℂ] N.even →ₗ[ℂ] P)
    (heeo : ∀ (b : S.even) (m : M.even) (n : N.odd), feo (M.actEE b m) n =
      feo m (N.actEO b n))
    (heoe : ∀ (b : S.even) (m : M.odd) (n : N.even), foe (M.actEO b m) n =
      foe m (N.actEE b n))
    (hoee : ∀ (c : S.odd) (m : M.even) (n : N.even), foe (M.actOE c m) n =
      feo m (N.actOE c n))
    (hooo : ∀ (c : S.odd) (m : M.odd) (n : N.odd), feo (M.actOO c m) n =
      -foe m (N.actOO c n)) :
    ∃! g : (tensor M N).odd →ₗ[ℂ] P,
      (∀ m n, g (tmulEO M N m n) = feo m n) ∧
        (∀ m n, g (tmulOE M N m n) = foe m n) :=
  ⟨liftOdd M N feo foe heeo heoe hoee hooo,
    ⟨liftOdd_tmulEO M N feo foe heeo heoe hoee hooo,
      liftOdd_tmulOE M N feo foe heeo heoe hoee hooo⟩,
    fun g hg => liftOdd_unique M N g _
      (fun m n => (hg.1 m n).trans
        (liftOdd_tmulEO M N feo foe heeo heoe hoee hooo m n).symm)
      (fun m n => (hg.2 m n).trans
        (liftOdd_tmulOE M N feo foe heeo heoe hoee hooo m n).symm)⟩

end Universal

end Tensor

end SuperCommAlgebra.Mod

end RS
