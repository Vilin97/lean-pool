/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainUnit

/-!
# The colimit algebra of the splitting chain

A chain of objects with one-step transitions has a filtered colimit
over the `v`-small copy of `ℕ`.  Given stagewise multiplications
compatible with the transitions, the colimit carries a multiplication;
given a bottom-stage unit with stagewise unit laws, it becomes a
monoid object, commutative when the stagewise multiplication is
commutative up to the index transport.  The development is generic
over any monoidal category in which tensoring preserves the chain
colimits — the ind-category of a small monoidal category qualifies by
`RS.tensorLeft_ind_preservesColimitsOfShape` and its right-hand
twin — so the splitting chain of `ChainDelta` can be instantiated
later with `B n := chainStage A M M' n` and `δ n := chainDelta`.

The multiplication is assembled in two passes of `colimit.desc`
through the preservation isomorphisms, mirroring the merge pattern of
`BigTensor`: first against a fixed stage in the second slot, then over
the second slot.  All colimit-level laws are cast-free because the
stage inclusions absorb the index transports.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

/- `open MonObj` would activate the scoped notation `ι` for
`GrpObj.inv`, clashing with the cocone fields; the packaged unit
and multiplication are therefore spelt with explicit projections. -/

universe v u

variable {E : Type u}

/-- Transport of a chain object along an equality of indices. -/
def chainCast [Category.{v} E] (B : ℕ → E)
    {a b : ℕ} (h : a = b) : B a ⟶ B b :=
  eqToHom (congrArg B h)

/-- The trivial index transport is the identity. -/
@[simp]
theorem chainCast_rfl [Category.{v} E] (B : ℕ → E)
    (a : ℕ) :
    chainCast B (rfl : a = a) = 𝟙 (B a) := rfl

/-- Index transports compose. -/
@[reassoc (attr := simp)]
theorem chainCast_trans [Category.{v} E] (B : ℕ → E)
    {a b c : ℕ} (h : a = b) (h' : b = c) :
    chainCast B h ≫ chainCast B h' = chainCast B (h.trans h') := by
  subst h h'
  simp

/-- The chain diagram over the `v`-small copy of `ℕ`, the shape at
which the receiving category is assumed to have colimits. -/
noncomputable def chainDiagram
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1)) :
    SmallNat.{v} ⥤ E :=
  smallNatEquiv.inverse ⋙ chainFunctor B δ

/-- The colimit object of the chain. -/
noncomputable def chainColimit
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] : E :=
  colimit (chainDiagram B δ)

/-- The stage inclusion into the chain colimit. -/
noncomputable def chainColimitι
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    (n : ℕ) : B n ⟶ chainColimit B δ :=
  colimit.ι (chainDiagram B δ) (smallNatEquiv.functor.obj n)

/-- The chain morphisms are absorbed by the stage inclusions. -/
@[reassoc (attr := simp)]
theorem chainMap_chainColimitι
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    {a b : ℕ} (h : a ≤ b) :
    chainMap B δ h ≫ chainColimitι B δ b = chainColimitι B δ a := by
  exact colimit.w (chainDiagram B δ)
    (smallNatEquiv.functor.map (homOfLE h))

/-- The transitions are absorbed by the stage inclusions. -/
@[reassoc (attr := simp)]
theorem delta_chainColimitι
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    (n : ℕ) :
    δ n ≫ chainColimitι B δ (n + 1) = chainColimitι B δ n := by
  have h := chainMap_chainColimitι B δ (Nat.le_succ n)
  rwa [chainMap_le_succ] at h

/-- The index transports are absorbed by the stage inclusions. -/
@[reassoc (attr := simp)]
theorem chainCast_chainColimitι
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    {a b : ℕ} (h : a = b) :
    chainCast B h ≫ chainColimitι B δ b = chainColimitι B δ a := by
  subst h
  rw [chainCast_rfl, Category.id_comp]

/-- Maps out of the chain colimit agree once they agree on all
stages. -/
theorem chainColimit_hom_ext
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    {Z : E} {f g : chainColimit B δ ⟶ Z}
    (w : ∀ n : ℕ, chainColimitι B δ n ≫ f =
      chainColimitι B δ n ≫ g) : f = g := by
  apply colimit.hom_ext
  intro k
  exact w (smallNatEquiv.inverse.obj k)

/-! ## The colimit multiplication

Stagewise multiplications compatible with the transitions assemble
into a multiplication on the chain colimit.  The two compatibility
squares are taken as hypotheses; only the left one needs an index
transport, since `(i + 1) + 1 + j` is not definitionally
`(i + 1 + j) + 1`. -/

/-- Multiplying after a chain morphism in the first slot agrees with
multiplying first, once both land in the colimit. -/
theorem mul_chainMap_ι_left
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    {i i' : ℕ} (h : i ≤ i') (j : ℕ) :
    (chainMap B δ h ▷ B j) ≫ mu i' j ≫
        chainColimitι B δ (i' + 1 + j) =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  induction i', h using Nat.le_induction with
  | base =>
    rw [chainMap_self, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
  | succ i' hii ih =>
    rw [chainMap_succ_of_le B δ hii, comp_whiskerRight,
      Category.assoc, reassoc_of% (hδl i' j),
      chainCast_chainColimitι, delta_chainColimitι]
    exact ih

/-- Multiplying after a chain morphism in the second slot agrees with
multiplying first, once both land in the colimit. -/
theorem mul_chainMap_ι_right
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    (i : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (B i ◁ chainMap B δ h) ≫ mu i j' ≫
        chainColimitι B δ (i + 1 + j') =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  induction j', h using Nat.le_induction with
  | base =>
    rw [chainMap_self, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  | succ j' hjj ih =>
    rw [chainMap_succ_of_le B δ hjj,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% (hδr i j')]
    have hι : δ (i + 1 + j') ≫
        chainColimitι B δ (i + 1 + (j' + 1)) =
        chainColimitι B δ (i + 1 + j') :=
      delta_chainColimitι B δ (i + 1 + j')
    rw [hι]
    exact ih

/-- The multiply-then-include maps against a fixed stage in the
second slot form a cocone on the chain diagram tensored on the right
with that stage. -/
noncomputable def chainMulCocone
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (j : ℕ) :
    Cocone (chainDiagram B δ ⋙ tensorRight (B j)) where
  pt := chainColimit B δ
  ι :=
    { app := fun k =>
        mu (smallNatEquiv.inverse.obj k) j ≫
          chainColimitι B δ (smallNatEquiv.inverse.obj k + 1 + j)
      naturality := fun {k k'} f => by
        show (chainMap B δ
            (leOfHom (smallNatEquiv.inverse.map f)) ▷ B j) ≫
            (mu (smallNatEquiv.inverse.obj k') j ≫
              chainColimitι B δ
                (smallNatEquiv.inverse.obj k' + 1 + j)) =
          (mu (smallNatEquiv.inverse.obj k) j ≫
            chainColimitι B δ
              (smallNatEquiv.inverse.obj k + 1 + j)) ≫
            𝟙 (chainColimit B δ)
        rw [Category.comp_id]
        exact mul_chainMap_ι_left B δ mu hδl
          (leOfHom (smallNatEquiv.inverse.map f)) j }

/-- Partial multiplication of the chain colimit against a fixed stage
in the second slot. -/
noncomputable def chainMulStage
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    (j : ℕ) :
    chainColimit B δ ⊗ B j ⟶ chainColimit B δ :=
  ((preservesColimitIso (tensorRight (B j))
      (chainDiagram B δ)).hom ≫
    colimit.desc _ (chainMulCocone B δ mu hδl j) :
    (tensorRight (B j)).obj (colimit (chainDiagram B δ)) ⟶
      chainColimit B δ)

/-- On a stage, the partial multiplication is multiply-then-include. -/
@[reassoc]
theorem ι_chainMulStage [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    (i j : ℕ) :
    (chainColimitι B δ i ▷ B j) ≫ chainMulStage B δ mu hδl j =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  show (tensorRight (B j)).map (colimit.ι (chainDiagram B δ)
      (smallNatEquiv.functor.obj i)) ≫
      chainMulStage B δ mu hδl j =
    mu i j ≫ chainColimitι B δ (i + 1 + j)
  rw [chainMulStage, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainMulCocone B δ mu hδl j)
    (smallNatEquiv.functor.obj i)

/-- Maps out of the chain colimit tensored on the right are
determined by their restrictions to the stages. -/
theorem chainColimit_tensorRight_hom_ext
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    {X Z : E}
    {f g : chainColimit B δ ⊗ X ⟶ Z}
    (w : ∀ i : ℕ, (chainColimitι B δ i ▷ X) ≫ f =
      (chainColimitι B δ i ▷ X) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso (tensorRight X)
    (chainDiagram B δ)).inv).mp
  apply colimit.hom_ext
  intro k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w (smallNatEquiv.inverse.obj k)

/-- The partial multiplications are natural in the stage. -/
@[reassoc]
theorem chainMulStage_natural
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    {j j' : ℕ} (h : j ≤ j') :
    (chainColimit B δ ◁ chainMap B δ h) ≫
        chainMulStage B δ mu hδl j' =
      chainMulStage B δ mu hδl j := by
  apply chainColimit_tensorRight_hom_ext B δ
  intro i
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    ι_chainMulStage, ι_chainMulStage]
  exact mul_chainMap_ι_right B δ mu hδr i h

/-- Maps out of the chain colimit tensored on the left are
determined by their restrictions to the stages. -/
theorem tensorLeft_chainColimit_hom_ext
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    {X Z : E}
    {f g : X ⊗ chainColimit B δ ⟶ Z}
    (w : ∀ j : ℕ, (X ◁ chainColimitι B δ j) ≫ f =
      (X ◁ chainColimitι B δ j) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso (tensorLeft X)
    (chainDiagram B δ)).inv).mp
  apply colimit.hom_ext
  intro k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w (smallNatEquiv.inverse.obj k)

/-- The partial multiplications form a cocone on the chain diagram
tensored on the left with the chain colimit. -/
noncomputable def chainMulTotalCocone
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)] :
    Cocone (chainDiagram B δ ⋙ tensorLeft (chainColimit B δ)) where
  pt := chainColimit B δ
  ι :=
    { app := fun k =>
        chainMulStage B δ mu hδl (smallNatEquiv.inverse.obj k)
      naturality := fun {k k'} f => by
        show (chainColimit B δ ◁ chainMap B δ
            (leOfHom (smallNatEquiv.inverse.map f))) ≫
            chainMulStage B δ mu hδl
              (smallNatEquiv.inverse.obj k') =
          chainMulStage B δ mu hδl
              (smallNatEquiv.inverse.obj k) ≫
            𝟙 (chainColimit B δ)
        rw [Category.comp_id]
        exact chainMulStage_natural B δ mu hδl hδr
          (leOfHom (smallNatEquiv.inverse.map f)) }

/-- **The colimit multiplication**: the partial multiplications
assembled over the second slot. -/
noncomputable def chainColimitMul
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)] :
    chainColimit B δ ⊗ chainColimit B δ ⟶ chainColimit B δ :=
  ((preservesColimitIso (tensorLeft (chainColimit B δ))
      (chainDiagram B δ)).hom ≫
    colimit.desc _ (chainMulTotalCocone B δ mu hδl hδr) :
    (tensorLeft (chainColimit B δ)).obj
        (colimit (chainDiagram B δ)) ⟶
      chainColimit B δ)

/-- On a stage in the second slot, the colimit multiplication is the
partial multiplication. -/
@[reassoc]
theorem whiskerLeft_ι_chainColimitMul
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (j : ℕ) :
    (chainColimit B δ ◁ chainColimitι B δ j) ≫
        chainColimitMul B δ mu hδl hδr =
      chainMulStage B δ mu hδl j := by
  show (tensorLeft (chainColimit B δ)).map
      (colimit.ι (chainDiagram B δ)
        (smallNatEquiv.functor.obj j)) ≫
      chainColimitMul B δ mu hδl hδr =
    chainMulStage B δ mu hδl j
  rw [chainColimitMul, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainMulTotalCocone B δ mu hδl hδr)
    (smallNatEquiv.functor.obj j)

/-- **Defining equation of the colimit multiplication**: on a pair of
stages it is multiply-then-include. -/
@[reassoc]
theorem ι_tensorHom_chainColimitMul
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (i j : ℕ) :
    (chainColimitι B δ i ⊗ₘ chainColimitι B δ j) ≫
        chainColimitMul B δ mu hδl hδr =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  rw [tensorHom_def, Category.assoc,
    whiskerLeft_ι_chainColimitMul, ι_chainMulStage]

/-- The multiply-then-include maps against a fixed stage in the
first slot form a cocone on the chain diagram tensored on the left
with that stage. -/
noncomputable def chainMulLCocone
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    (i : ℕ) :
    Cocone (chainDiagram B δ ⋙ tensorLeft (B i)) where
  pt := chainColimit B δ
  ι :=
    { app := fun k =>
        mu i (smallNatEquiv.inverse.obj k) ≫
          chainColimitι B δ (i + 1 + smallNatEquiv.inverse.obj k)
      naturality := fun {k k'} f => by
        show (B i ◁ chainMap B δ
            (leOfHom (smallNatEquiv.inverse.map f))) ≫
            (mu i (smallNatEquiv.inverse.obj k') ≫
              chainColimitι B δ
                (i + 1 + smallNatEquiv.inverse.obj k')) =
          (mu i (smallNatEquiv.inverse.obj k) ≫
            chainColimitι B δ
              (i + 1 + smallNatEquiv.inverse.obj k)) ≫
            𝟙 (chainColimit B δ)
        rw [Category.comp_id]
        exact mul_chainMap_ι_right B δ mu hδr i
          (leOfHom (smallNatEquiv.inverse.map f)) }

/-- Partial multiplication of a fixed stage in the first slot
against the chain colimit. -/
noncomputable def chainMulStageL
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (i : ℕ) :
    B i ⊗ chainColimit B δ ⟶ chainColimit B δ :=
  ((preservesColimitIso (tensorLeft (B i))
      (chainDiagram B δ)).hom ≫
    colimit.desc _ (chainMulLCocone B δ mu hδr i) :
    (tensorLeft (B i)).obj (colimit (chainDiagram B δ)) ⟶
      chainColimit B δ)

/-- On a stage, the left partial multiplication is
multiply-then-include. -/
@[reassoc]
theorem ι_chainMulStageL [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (i j : ℕ) :
    (B i ◁ chainColimitι B δ j) ≫ chainMulStageL B δ mu hδr i =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  show (tensorLeft (B i)).map (colimit.ι (chainDiagram B δ)
      (smallNatEquiv.functor.obj j)) ≫
      chainMulStageL B δ mu hδr i =
    mu i j ≫ chainColimitι B δ (i + 1 + j)
  rw [chainMulStageL, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainMulLCocone B δ mu hδr i)
    (smallNatEquiv.functor.obj j)

/-- On a stage in the first slot, the colimit multiplication is the
left partial multiplication. -/
@[reassoc]
theorem ι_whiskerRight_chainColimitMul
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (i : ℕ) :
    (chainColimitι B δ i ▷ chainColimit B δ) ≫
        chainColimitMul B δ mu hδl hδr =
      chainMulStageL B δ mu hδr i := by
  apply tensorLeft_chainColimit_hom_ext B δ
  intro j
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    whiskerLeft_ι_chainColimitMul, ι_chainMulStage,
    ι_chainMulStageL]

/-- Maps out of the tensor square of the chain colimit are
determined by pairs of stages. -/
theorem chainColimit_pair_hom_ext
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    {Z : E}
    {f g : chainColimit B δ ⊗ chainColimit B δ ⟶ Z}
    (w : ∀ i j : ℕ,
      (chainColimitι B δ i ⊗ₘ chainColimitι B δ j) ≫ f =
        (chainColimitι B δ i ⊗ₘ chainColimitι B δ j) ≫ g) :
    f = g := by
  apply tensorLeft_chainColimit_hom_ext B δ
  intro j
  apply chainColimit_tensorRight_hom_ext B δ
  intro i
  rw [← Category.assoc, ← Category.assoc,
    show chainColimitι B δ i ▷ B j ≫
        chainColimit B δ ◁ chainColimitι B δ j =
      chainColimitι B δ i ⊗ₘ chainColimitι B δ j from
        (tensorHom_def _ _).symm]
  exact w i j

/-- Sandwich extensionality: maps out of a tensor product with the
chain colimit in the middle slot are determined by the stages
there. -/
theorem chainColimit_sandwich_hom_ext
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (X Y : E) {Z : E}
    {f g : X ⊗ (chainColimit B δ ⊗ Y) ⟶ Z}
    (w : ∀ j : ℕ, (X ◁ chainColimitι B δ j ▷ Y) ≫ f =
      (X ◁ chainColimitι B δ j ▷ Y) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso
    (tensorRight Y ⋙ tensorLeft X) (chainDiagram B δ)).inv).mp
  apply colimit.hom_ext
  intro k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w (smallNatEquiv.inverse.obj k)

/-! ## The unit and the monoid laws

The colimit unit is the bottom-stage unit followed by the stage
inclusion.  The monoid laws hold on the colimit whenever their
stagewise forms hold; the index transports disappear into the stage
inclusions. -/

/-- The colimit unit: the bottom-stage unit followed by the stage
inclusion. -/
noncomputable def chainColimitUnit
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (u : 𝟙_ E ⟶ B 0) : 𝟙_ E ⟶ chainColimit B δ :=
  u ≫ chainColimitι B δ 0

/-- **Left unit law** of the colimit multiplication, from the
stagewise left unit law. -/
theorem chainColimit_one_mul
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (u : 𝟙_ E ⟶ B 0)
    (hul : ∀ j, (u ▷ B j) ≫ mu 0 j =
      (λ_ (B j)).hom ≫ chainMap B δ (Nat.le_add_left j (0 + 1))) :
    (chainColimitUnit B δ u ▷ chainColimit B δ) ≫
        chainColimitMul B δ mu hδl hδr =
      (λ_ (chainColimit B δ)).hom := by
  apply tensorLeft_chainColimit_hom_ext B δ
  intro j
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    whiskerLeft_ι_chainColimitMul, chainColimitUnit,
    comp_whiskerRight, Category.assoc, ι_chainMulStage,
    reassoc_of% (hul j), chainMap_chainColimitι,
    leftUnitor_naturality]

/-- **Right unit law** of the colimit multiplication, from the
stagewise right unit law. -/
theorem chainColimit_mul_one
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (u : 𝟙_ E ⟶ B 0)
    (hur : ∀ i, (B i ◁ u) ≫ mu i 0 = (ρ_ (B i)).hom ≫ δ i) :
    (chainColimit B δ ◁ chainColimitUnit B δ u) ≫
        chainColimitMul B δ mu hδl hδr =
      (ρ_ (chainColimit B δ)).hom := by
  apply chainColimit_tensorRight_hom_ext B δ
  intro i
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    ι_whiskerRight_chainColimitMul, chainColimitUnit,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ι_chainMulStageL, reassoc_of% (hur i)]
  have hι : δ i ≫ chainColimitι B δ (i + 1 + 0) =
      chainColimitι B δ i :=
    delta_chainColimitι B δ i
  rw [hι, rightUnitor_naturality]

/-- Stagewise associativity, pushed into the colimit: the index
transport is absorbed by the stage inclusion. -/
theorem mul_assoc_ι [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hassoc : ∀ i j k, (mu i j ▷ B k) ≫ mu (i + 1 + j) k =
      (α_ (B i) (B j) (B k)).hom ≫ (B i ◁ mu j k) ≫
        mu i (j + 1 + k) ≫ chainCast B
          (by omega : i + 1 + (j + 1 + k) = i + 1 + j + 1 + k))
    (i j k : ℕ) :
    (mu i j ▷ B k) ≫ mu (i + 1 + j) k ≫
        chainColimitι B δ (i + 1 + j + 1 + k) =
      (α_ (B i) (B j) (B k)).hom ≫ (B i ◁ mu j k) ≫
        mu i (j + 1 + k) ≫
        chainColimitι B δ (i + 1 + (j + 1 + k)) := by
  rw [reassoc_of% (hassoc i j k), chainCast_chainColimitι]

/-- **Associativity** of the colimit multiplication, from stagewise
associativity. -/
theorem chainColimit_mul_assoc
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (hassoc : ∀ i j k, (mu i j ▷ B k) ≫ mu (i + 1 + j) k =
      (α_ (B i) (B j) (B k)).hom ≫ (B i ◁ mu j k) ≫
        mu i (j + 1 + k) ≫ chainCast B
          (by omega : i + 1 + (j + 1 + k) = i + 1 + j + 1 + k)) :
    (chainColimitMul B δ mu hδl hδr ▷ chainColimit B δ) ≫
        chainColimitMul B δ mu hδl hδr =
      (α_ (chainColimit B δ) (chainColimit B δ)
          (chainColimit B δ)).hom ≫
        (chainColimit B δ ◁ chainColimitMul B δ mu hδl hδr) ≫
        chainColimitMul B δ mu hδl hδr := by
  apply tensorLeft_chainColimit_hom_ext B δ
  intro k
  conv_lhs =>
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      whiskerLeft_ι_chainColimitMul]
  conv_rhs =>
    rw [associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      whiskerLeft_ι_chainColimitMul]
  apply (cancel_epi (α_ (chainColimit B δ) (chainColimit B δ)
    (B k)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply chainColimit_tensorRight_hom_ext B δ
  intro i
  conv_lhs =>
    rw [associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, ι_whiskerRight_chainColimitMul]
  conv_rhs =>
    rw [← whisker_exchange_assoc, ι_whiskerRight_chainColimitMul]
  apply chainColimit_sandwich_hom_ext B δ (B i) (B k)
  intro j
  conv_lhs =>
    rw [associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ι_chainMulStageL,
      comp_whiskerRight, Category.assoc, ι_chainMulStage,
      mul_assoc_ι B δ mu hassoc i j k,
      Iso.inv_hom_id_assoc]
  conv_rhs =>
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      ι_chainMulStage, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, ι_chainMulStageL]

/-- **The chain colimit as a monoid object**: the unit is the
included bottom-stage unit and the multiplication is assembled from
the stagewise multiplications. -/
@[reducible]
noncomputable def chainColimitMonObj
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (u : 𝟙_ E ⟶ B 0)
    (hul : ∀ j, (u ▷ B j) ≫ mu 0 j =
      (λ_ (B j)).hom ≫ chainMap B δ (Nat.le_add_left j (0 + 1)))
    (hur : ∀ i, (B i ◁ u) ≫ mu i 0 = (ρ_ (B i)).hom ≫ δ i)
    (hassoc : ∀ i j k, (mu i j ▷ B k) ≫ mu (i + 1 + j) k =
      (α_ (B i) (B j) (B k)).hom ≫ (B i ◁ mu j k) ≫
        mu i (j + 1 + k) ≫ chainCast B
          (by omega : i + 1 + (j + 1 + k) = i + 1 + j + 1 + k)) :
    MonObj (chainColimit B δ) where
  one := chainColimitUnit B δ u
  mul := chainColimitMul B δ mu hδl hδr
  one_mul := chainColimit_one_mul B δ mu hδl hδr u hul
  mul_one := chainColimit_mul_one B δ mu hδl hδr u hur
  mul_assoc := chainColimit_mul_assoc B δ mu hδl hδr hassoc

/-! ## Commutativity -/

section Braided

/-- Stagewise commutativity, pushed into the colimit: the index
transport is absorbed by the stage inclusion. -/
theorem mul_comm_ι [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j)) [BraidedCategory E]
    (hcomm : ∀ i j, (β_ (B i) (B j)).hom ≫ mu j i ≫
      chainCast B (by omega : j + 1 + i = i + 1 + j) = mu i j)
    (i j : ℕ) :
    (β_ (B i) (B j)).hom ≫ mu j i ≫
        chainColimitι B δ (j + 1 + i) =
      mu i j ≫ chainColimitι B δ (i + 1 + j) := by
  rw [← hcomm i j, Category.assoc, Category.assoc,
    chainCast_chainColimitι]

/-- **Commutativity** of the colimit multiplication, from stagewise
commutativity up to the index transport. -/
theorem chainColimitMul_comm
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [BraidedCategory E]
    (hcomm : ∀ i j, (β_ (B i) (B j)).hom ≫ mu j i ≫
      chainCast B (by omega : j + 1 + i = i + 1 + j) = mu i j) :
    (β_ (chainColimit B δ) (chainColimit B δ)).hom ≫
        chainColimitMul B δ mu hδl hδr =
      chainColimitMul B δ mu hδl hδr := by
  apply chainColimit_pair_hom_ext B δ
  intro i j
  rw [BraidedCategory.braiding_naturality_assoc,
    ι_tensorHom_chainColimitMul, ι_tensorHom_chainColimitMul]
  exact mul_comm_ι B δ mu hcomm i j

/-- **The chain colimit as a commutative monoid object**: stagewise
commutativity makes the packaged monoid structure commutative. -/
theorem chainColimit_isCommMonObj
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] [MonoidalCategory E]
    (mu : ∀ i j : ℕ, B i ⊗ B j ⟶ B (i + 1 + j))
    (hδl : ∀ i j, (δ i ▷ B j) ≫ mu (i + 1) j = mu i j ≫ δ (i + 1 + j) ≫
      chainCast B (Nat.add_right_comm (i + 1) j 1))
    (hδr : ∀ i j, (B i ◁ δ j) ≫ mu i (j + 1) = mu i j ≫ δ (i + 1 + j))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (u : 𝟙_ E ⟶ B 0) [BraidedCategory E]
    (hul : ∀ j, (u ▷ B j) ≫ mu 0 j =
      (λ_ (B j)).hom ≫ chainMap B δ (Nat.le_add_left j (0 + 1)))
    (hur : ∀ i, (B i ◁ u) ≫ mu i 0 = (ρ_ (B i)).hom ≫ δ i)
    (hassoc : ∀ i j k, (mu i j ▷ B k) ≫ mu (i + 1 + j) k =
      (α_ (B i) (B j) (B k)).hom ≫ (B i ◁ mu j k) ≫
        mu i (j + 1 + k) ≫ chainCast B
          (by omega : i + 1 + (j + 1 + k) = i + 1 + j + 1 + k))
    (hcomm : ∀ i j, (β_ (B i) (B j)).hom ≫ mu j i ≫
      chainCast B (by omega : j + 1 + i = i + 1 + j) = mu i j) :
    @IsCommMonObj E _ _ _ (chainColimit B δ)
      (chainColimitMonObj B δ mu hδl hδr u hul hur hassoc) :=
  letI := chainColimitMonObj B δ mu hδl hδr u hul hur hassoc
  ⟨chainColimitMul_comm B δ mu hδl hδr hcomm⟩

end Braided

/-! ## The ind-category instantiation

Over the ind-category of a small monoidal category the generic
development applies verbatim: the shape has colimits, tensoring
preserves them (`IndTensorExact`), and the generic chain diagram is
the chain functor of `ChainUnit`, so the nonvanishing criterion for
the colimit unit transfers to the packaged unit. -/

section Ind

/-- **Nonvanishing of the colimit unit**: over the ind-category, the
colimit unit built from a compatible family of stage units vanishes
exactly when the family dies at a finite stage. -/
theorem chainColimitUnit_eq_zero_iff
    {C : Type v} [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (B : ℕ → Ind C)
    (δ : ∀ n, B n ⟶ B (n + 1)) (u : ∀ n, 𝟙_ (Ind C) ⟶ B n)
    (hu : ∀ n, u n ≫ δ n = u (n + 1)) :
    chainColimitUnit B δ (u 0) = 0 ↔ ∃ n, u n = 0 :=
  unit_chain_colimit_eq_zero_iff B δ u hu 0

end Ind

end RS
