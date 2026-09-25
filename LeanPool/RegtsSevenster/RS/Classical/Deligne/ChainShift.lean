/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainAlgebra

/-!
# Shifting a chain colimit by one stage

Dropping the bottom stage of a chain does not change its colimit.
The stage inclusions of the full chain restrict to a cocone on the
shifted chain, giving the tail comparison; the transitions followed
by the shifted stage inclusions form a cocone on the full chain,
giving the comparison back.  Both composites are identified with the
identities by the stagewise extensionality lemma.  The
descent-from-legs helper `chainDesc` is factored out for reuse: any
family of legs absorbed by the transitions descends to the chain
colimit, with the stage computation exposed as a simp lemma.
-/

namespace RS

open CategoryTheory Limits

universe v u

variable {E : Type u}

/-- Legs absorbed by the transitions absorb all chain morphisms. -/
theorem chainMap_legs [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    {Z : E} (legs : ∀ n, B n ⟶ Z)
    (h : ∀ n, δ n ≫ legs (n + 1) = legs n) {a b : ℕ}
    (hab : a ≤ b) : chainMap B δ hab ≫ legs b = legs a := by
  induction b, hab using Nat.le_induction with
  | base => rw [chainMap_self, Category.id_comp]
  | succ b hab ih =>
    rw [chainMap_succ_of_le B δ hab, Category.assoc, h]
    exact ih

/-- The cocone on the chain diagram assembled from legs absorbed by
the transitions. -/
noncomputable def chainCocone
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    {Z : E} (legs : ∀ n, B n ⟶ Z)
    (h : ∀ n, δ n ≫ legs (n + 1) = legs n) :
    Cocone (chainDiagram B δ) where
  pt := Z
  ι :=
    { app := fun k => legs (smallNatEquiv.inverse.obj k)
      naturality := fun {k k'} f => by
        change chainMap B δ (leOfHom (smallNatEquiv.inverse.map f)) ≫
            legs (smallNatEquiv.inverse.obj k') =
          legs (smallNatEquiv.inverse.obj k) ≫ 𝟙 Z
        rw [Category.comp_id]
        exact chainMap_legs B δ legs h
          (leOfHom (smallNatEquiv.inverse.map f)) }

/-- The descent out of the chain colimit determined by legs absorbed
by the transitions. -/
noncomputable def chainDesc
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    {Z : E} (legs : ∀ n, B n ⟶ Z)
    (h : ∀ n, δ n ≫ legs (n + 1) = legs n) :
    chainColimit B δ ⟶ Z :=
  colimit.desc _ (chainCocone B δ legs h)

/-- On a stage, the descent is the corresponding leg. -/
@[reassoc (attr := simp)]
theorem ι_chainDesc [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    {Z : E} (legs : ∀ n, B n ⟶ Z)
    (h : ∀ n, δ n ≫ legs (n + 1) = legs n) (n : ℕ) :
    chainColimitι B δ n ≫ chainDesc B δ legs h = legs n :=
  colimit.ι_desc (chainCocone B δ legs h)
    (smallNatEquiv.functor.obj n)

/-- The comparison from the colimit of the shifted chain, whose leg
at a stage is the next stage inclusion of the full chain. -/
noncomputable def chainColimitTail
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] :
    chainColimit (fun k => B (k + 1)) (fun k => δ (k + 1)) ⟶
      chainColimit B δ :=
  chainDesc (fun k => B (k + 1)) (fun k => δ (k + 1))
    (fun k => chainColimitι B δ (k + 1))
    (fun k => delta_chainColimitι B δ (k + 1))

/-- On a stage, the tail comparison is the next stage inclusion. -/
@[reassoc (attr := simp)]
theorem ι_chainColimitTail
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    (k : ℕ) :
    chainColimitι (fun k => B (k + 1)) (fun k => δ (k + 1)) k ≫
        chainColimitTail B δ =
      chainColimitι B δ (k + 1) :=
  ι_chainDesc (fun k => B (k + 1)) (fun k => δ (k + 1))
    (fun k => chainColimitι B δ (k + 1))
    (fun k => delta_chainColimitι B δ (k + 1)) k

/-- The comparison to the colimit of the shifted chain, whose leg at
a stage is the transition followed by the shifted inclusion. -/
noncomputable def chainColimitUntail
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] :
    chainColimit B δ ⟶
      chainColimit (fun k => B (k + 1)) (fun k => δ (k + 1)) :=
  chainDesc B δ
    (fun k => δ k ≫
      chainColimitι (fun k => B (k + 1)) (fun k => δ (k + 1)) k)
    (fun k =>
      congrArg (fun t => δ k ≫ t)
        (delta_chainColimitι (fun k => B (k + 1))
          (fun k => δ (k + 1)) k))

/-- On a stage, the comparison to the shifted colimit is the
transition followed by the shifted inclusion. -/
@[reassoc (attr := simp)]
theorem ι_chainColimitUntail
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E]
    (k : ℕ) :
    chainColimitι B δ k ≫ chainColimitUntail B δ =
      δ k ≫
        chainColimitι (fun k => B (k + 1)) (fun k => δ (k + 1)) k :=
  ι_chainDesc B δ
    (fun k => δ k ≫
      chainColimitι (fun k => B (k + 1)) (fun k => δ (k + 1)) k)
    (fun k =>
      congrArg (fun t => δ k ≫ t)
        (delta_chainColimitι (fun k => B (k + 1))
          (fun k => δ (k + 1)) k)) k

/-- Dropping the bottom stage of a chain does not change the
colimit. -/
noncomputable def chainColimitTailIso
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] :
    chainColimit (fun k => B (k + 1)) (fun k => δ (k + 1)) ≅
      chainColimit B δ where
  hom := chainColimitTail B δ
  inv := chainColimitUntail B δ
  hom_inv_id := by
    apply chainColimit_hom_ext (fun k => B (k + 1))
      (fun k => δ (k + 1))
    intro n
    rw [Category.comp_id, ι_chainColimitTail_assoc,
      ι_chainColimitUntail]
    exact delta_chainColimitι (fun k => B (k + 1))
      (fun k => δ (k + 1)) n
  inv_hom_id := by
    apply chainColimit_hom_ext B δ
    intro n
    rw [Category.comp_id, ι_chainColimitUntail_assoc,
      ι_chainColimitTail]
    exact delta_chainColimitι B δ n

section MapIso

/-- **The chain colimit is invariant under stagewise
isomorphism**: compatible stage isomorphisms induce an
isomorphism of the chain colimits. -/
noncomputable def chainColimitMapIso
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] {C : ℕ → E}
    (δC : ∀ n, C n ⟶ C (n + 1))
    (φ : ∀ n, B n ≅ C n)
    (hφ : ∀ n, δ n ≫ (φ (n + 1)).hom = (φ n).hom ≫ δC n) :
    chainColimit B δ ≅ chainColimit C δC where
  hom := chainDesc B δ
    (fun n => (φ n).hom ≫ chainColimitι C δC n)
    (fun n => by
      rw [← Category.assoc, hφ n, Category.assoc,
        delta_chainColimitι])
  inv := chainDesc C δC
    (fun n => (φ n).inv ≫ chainColimitι B δ n)
    (fun n => by
      have h : δC n ≫ (φ (n + 1)).inv = (φ n).inv ≫ δ n := by
        rw [Iso.comp_inv_eq, Category.assoc, hφ n,
          Iso.inv_hom_id_assoc]
      rw [← Category.assoc, h, Category.assoc,
        delta_chainColimitι])
  hom_inv_id := by
    apply chainColimit_hom_ext B δ
    intro n
    rw [Category.comp_id, ← Category.assoc, ι_chainDesc,
      Category.assoc, ι_chainDesc, Iso.hom_inv_id_assoc]
  inv_hom_id := by
    apply chainColimit_hom_ext C δC
    intro n
    rw [Category.comp_id, ← Category.assoc, ι_chainDesc,
      Category.assoc, ι_chainDesc, Iso.inv_hom_id_assoc]

/-- The stage insertions under the stagewise isomorphism. -/
@[reassoc (attr := simp)]
theorem ι_chainColimitMapIso_hom
    [Category.{v} E] (B : ℕ → E) (δ : ∀ n, B n ⟶ B (n + 1))
    [HasColimitsOfShape SmallNat.{v} E] {C : ℕ → E}
    (δC : ∀ n, C n ⟶ C (n + 1))
    (φ : ∀ n, B n ≅ C n)
    (hφ : ∀ n, δ n ≫ (φ (n + 1)).hom = (φ n).hom ≫ δC n)
    (n : ℕ) :
    chainColimitι B δ n ≫ (chainColimitMapIso B δ δC φ hφ).hom =
      (φ n).hom ≫ chainColimitι C δC n :=
  ι_chainDesc B δ _ _ n

end MapIso

end RS
