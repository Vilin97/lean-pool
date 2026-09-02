/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Action
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Pi

/-!
# Irreducibility of permutation-wreath product actions

Let a group `H` act linearly on an `F`-module `V`, and let a group `Q` act
transitively on a nonempty finite type `ι`.  This file proves that the product
action of `H wr_ι Q` on `ι → V` is irreducible when the component action is
irreducible and nontrivial.

Here nontriviality of the action is recorded by `MovesNonzero H V`: every
nonzero component vector is moved by some element of `H`.  For an irreducible
module this follows as soon as the action itself is nontrivial; in particular,
it follows from faithfulness and `Nontrivial H`.

The proof is computation-free.  Starting with a nonzero vector in an invariant
subspace, subtracting a base-group translate isolates one coordinate.  The
component irreducibility fills that coordinate, top transitivity transports it
to every coordinate, and the finite sum of coordinate vectors fills the whole
product module.
-/

namespace Saxl

variable {F H Q ι V : Type*}
variable [Field F] [Group H] [Group Q] [MulAction Q ι]
variable [AddCommGroup V] [Module F V]
variable [DistribMulAction H V] [SMulCommClass H F V]

/-- The existing product action is additive whenever the component action is
additive. -/
instance permWreathDistribMulAction :
    DistribMulAction (PermWreath H Q ι) (ι → V) where
  toMulAction := permWreathMulAction H Q ι V
  smul_zero g := by
    funext i
    simp
  smul_add g x y := by
    funext i
    simp

/-- The existing product action commutes with the scalar action whenever the
component action does. -/
instance permWreathSMulCommClass :
    SMulCommClass (PermWreath H Q ι) F (ι → V) where
  smul_comm g a x := by
    funext i
    change g.left i • (a • x (g.right⁻¹ • i)) =
      a • (g.left i • x (g.right⁻¹ • i))
    exact smul_comm _ _ _

/-- Every nonzero vector is moved by some group element.  This is the exact
nontriviality condition used by the coordinate-isolation argument. -/
def MovesNonzero (H V : Type*) [Zero V] [SMul H V] : Prop :=
  ∀ v : V, v ≠ 0 → ∃ h : H, h • v ≠ v

/-- For an irreducible module, one moved vector implies that every nonzero
vector is moved. -/
theorem movesNonzero_of_irreducible
    (hirr : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V))
    (hnontrivial : ∃ h : H, ∃ v : V, h • v ≠ v) :
    MovesNonzero H V := by
  let _ : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V) := hirr
  intro v hv
  by_contra hmove
  have hfix : ∀ h : H, h • v = v := by
    intro h
    by_contra hh
    exact hmove ⟨h, hh⟩
  let fixed : Subrepresentation
      (Representation.ofDistribMulAction F H V) := {
    toSubmodule :=
      { carrier := {w | ∀ h : H, h • w = w}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy h
          simp [hx h, hy h]
        smul_mem' := by
          intro a x hx h
          rw [smul_comm, hx h] }
    apply_mem_toSubmodule := by
      intro g x hx h
      change h • (g • x) = g • x
      calc
        h • (g • x) = g • ((g⁻¹ * h * g) • x) := by simp [mul_smul]
        _ = g • x := by rw [hx] }
  have hvfixed : v ∈ fixed := hfix
  have hfixed_ne : fixed ≠ ⊥ := by
    intro hbot
    have hvbot : v ∈ (⊥ : Subrepresentation
        (Representation.ofDistribMulAction F H V)) := hbot ▸ hvfixed
    change v ∈ (⊥ : Submodule F V) at hvbot
    exact hv (by simpa using hvbot)
  have hfixed_top : fixed = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top fixed).resolve_left hfixed_ne
  obtain ⟨h, w, hhw⟩ := hnontrivial
  have hwfixed : w ∈ fixed := by
    rw [hfixed_top]
    exact Submodule.mem_top
  exact hhw (hwfixed h)

/-- A faithful irreducible action of a nontrivial group moves every nonzero
vector. -/
theorem movesNonzero_of_irreducible_faithful
    [Nontrivial H] [FaithfulSMul H V]
    (hirr : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V)) :
    MovesNonzero H V := by
  apply movesNonzero_of_irreducible hirr
  obtain ⟨h, hh⟩ : ∃ h : H, h ≠ 1 := exists_ne 1
  by_contra hmove
  apply hh
  apply (faithfulSMul_iff.mp (show FaithfulSMul H V from inferInstance)) h
  intro v
  by_contra hv
  exact hmove ⟨h, v, hv⟩

namespace PermWreath

private noncomputable def coordinate (i : ι) :
    H →* Saxl.PermWreath H Q ι := by
  classical
  exact (base H Q ι).comp (MonoidHom.mulSingle (fun _ : ι ↦ H) i)

private theorem coordinate_smul_apply [DecidableEq ι]
    (i : ι) (h : H) (x : ι → V) (j : ι) :
    (coordinate (Q := Q) i h • x) j = if j = i then h • x j else x j := by
  by_cases hji : j = i
  · subst j
    simp [coordinate]
  · simp [coordinate, hji]

private theorem coordinate_smul_single [DecidableEq ι]
    (i : ι) (h : H) (v : V) :
    coordinate (Q := Q) i h • (Pi.single i v : ι → V) =
      (Pi.single i (h • v) : ι → V) := by
  funext j
  rw [coordinate_smul_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private theorem top_smul_single [DecidableEq ι]
    (q : Q) (i : ι) (v : V) :
    top H Q ι q • (Pi.single i v : ι → V) =
      (Pi.single (q • i) v : ι → V) := by
  funext j
  by_cases hj : j = q • i
  · subst j
    simp
  · have hpre : q⁻¹ • j ≠ i := by
      intro heq
      apply hj
      rw [← heq]
      simp
    simp [hpre, hj]

/-- The coordinate-moving condition passes from a component action to its
permutation-wreath product action. -/
theorem movesNonzero (hmove : MovesNonzero H V) :
    MovesNonzero (Saxl.PermWreath H Q ι) (ι → V) := by
  classical
  intro x hx
  have hcoord : ∃ i : ι, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hxi⟩ := hcoord
  obtain ⟨h, hh⟩ := hmove (x i) hxi
  refine ⟨coordinate (Q := Q) i h, ?_⟩
  intro heq
  apply hh
  have hi := congrFun heq i
  rw [coordinate_smul_apply] at hi
  simpa using hi

/-- A finite transitive permutation wreath product of an irreducible component
that moves every nonzero vector is irreducible in its product action. -/
theorem isIrreducible_of_movesNonzero
    [Finite ι] [Nonempty ι] [Nontrivial V]
    (hcomponent : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V))
    (hmove : MovesNonzero H V)
    (htop : MulAction.IsPretransitive Q ι) :
    Representation.IsIrreducible
      (Representation.ofDistribMulAction F
        (Saxl.PermWreath H Q ι) (ι → V)) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V) := hcomponent
  let _ : MulAction.IsPretransitive Q ι := htop
  refine { toNontrivial := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule F (ι → V)) ≠ ⊤) h'
  · intro W
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    right
    have hWsub : W.toSubmodule ≠ ⊥ := by
      intro hbot
      apply hWbot
      exact Subrepresentation.ext hbot
    obtain ⟨x, hxW, hx⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hWsub
    have hcoord : ∃ i : ι, x i ≠ 0 := by
      by_contra h
      apply hx
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hxi⟩ := hcoord
    obtain ⟨h, hh⟩ := hmove (x i) hxi
    let g : Saxl.PermWreath H Q ι := coordinate (Q := Q) i h
    have hgxW : g • x ∈ W := by
      change (Representation.ofDistribMulAction F
        (Saxl.PermWreath H Q ι) (ι → V)) g x ∈ W
      exact W.apply_mem_toSubmodule g hxW
    have hdiffW : g • x - x ∈ W := W.toSubmodule.sub_mem hgxW hxW
    let d : V := h • x i - x i
    have hd : d ≠ 0 := sub_ne_zero.mpr hh
    have hdiff : g • x - x = (Pi.single i d : ι → V) := by
      funext j
      rw [Pi.sub_apply]
      change (coordinate (Q := Q) i h • x) j - x j = _
      rw [coordinate_smul_apply]
      by_cases hji : j = i
      · subst j
        simp [d]
      · simp [d, hji]
    have hsingle_d : (Pi.single i d : ι → V) ∈ W := by
      rw [← hdiff]
      exact hdiffW
    let U : Subrepresentation
        (Representation.ofDistribMulAction F H V) := {
      toSubmodule := Submodule.comap
        (LinearMap.single F (fun _ : ι ↦ V) i) W.toSubmodule
      apply_mem_toSubmodule := by
        intro k v hv
        change (Pi.single i v : ι → V) ∈ W at hv
        have hw := W.apply_mem_toSubmodule (coordinate (Q := Q) i k) hv
        change coordinate (Q := Q) i k •
          (Pi.single i v : ι → V) ∈ W at hw
        change (Pi.single i (k • v) : ι → V) ∈ W
        simpa only [coordinate_smul_single] using hw }
    have hdU : d ∈ U := hsingle_d
    have hUne : U ≠ ⊥ := by
      intro hbot
      have hdBot : d ∈ (⊥ : Subrepresentation
          (Representation.ofDistribMulAction F H V)) := hbot ▸ hdU
      change d ∈ (⊥ : Submodule F V) at hdBot
      exact hd (by simpa using hdBot)
    have hUtop : U = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hUne
    have hsingle_i : ∀ v : V, (Pi.single i v : ι → V) ∈ W := by
      intro v
      have hvU : v ∈ U := by
        rw [hUtop]
        exact Submodule.mem_top
      exact hvU
    have hsingle : ∀ (j : ι) (v : V),
        (Pi.single j v : ι → V) ∈ W := by
      intro j v
      obtain ⟨q, hqi⟩ := MulAction.exists_smul_eq Q i j
      have hw := W.apply_mem_toSubmodule (top H Q ι q) (hsingle_i v)
      change top H Q ι q • (Pi.single i v : ι → V) ∈ W at hw
      rw [top_smul_single, hqi] at hw
      exact hw
    apply top_unique
    intro y _hy
    have hsum : (∑ j : ι, Pi.single j (y j)) ∈ W :=
      Submodule.sum_mem W.toSubmodule (fun j _ ↦ hsingle j (y j))
    simpa only [LinearMap.sum_single_apply] using hsum

/-- Faithful-action form of `isIrreducible_of_movesNonzero`. -/
theorem isIrreducible_of_faithful
    [Finite ι] [Nonempty ι] [Nontrivial H] [Nontrivial V]
    [FaithfulSMul H V]
    (hcomponent : Representation.IsIrreducible
      (Representation.ofDistribMulAction F H V))
    (htop : MulAction.IsPretransitive Q ι) :
    Representation.IsIrreducible
      (Representation.ofDistribMulAction F
        (Saxl.PermWreath H Q ι) (ι → V)) := by
  classical
  let _ := Fintype.ofFinite ι
  exact isIrreducible_of_movesNonzero hcomponent
    (movesNonzero_of_irreducible_faithful hcomponent) htop

end PermWreath

end Saxl
