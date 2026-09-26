/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.Algebra.Group.ULift

/-!
# The free-product data used by Kurosh's theorem

This file starts the Bass--Serre extension of the finite Schreier development.
The ambient free product is Mathlib's `Monoid.CoprodI`; in particular, the
reduced-word normal form is not redefined here.  The definitions below keep
the two pieces of Kurosh data explicit:

* the canonical copy of each factor in the free product; and
* the subgroup obtained by intersecting a conjugate of that copy with a
  subgroup of the ambient free product.

The main decomposition theorem will use these definitions rather than an
unstructured existential statement.  This makes the double-coset indexing,
the factor embeddings, and the final free-product equivalence visible to the
kernel checker and to the Palomar statement surface.

The orbit type is Mathlib's `MulAction.orbitRel.Quotient`. Proof scaffolding
shared between this project's modules lives in `GraphCoveringTheory.Kurosh.Internal`.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

public section

open Set Function
open CategoryTheory
open scoped Pointwise

noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory

namespace Kurosh

open Monoid.CoprodI

/-- The indexed free product of a family of groups. -/
abbrev FreeProduct (G : ι → Type u) [∀ i, Group (G i)] := Monoid.CoprodI G

/-- The canonical inclusion of a factor into its free product. -/
@[expose] def factorInclusion (G : ι → Type u) [∀ i, Group (G i)] (i : ι) :
    G i →* FreeProduct G := Monoid.CoprodI.of

@[simp]
theorem factorInclusion_apply (G : ι → Type u) [∀ i, Group (G i)] (i : ι)
    (g : G i) : factorInclusion G i g = Monoid.CoprodI.of g := rfl

theorem factorInclusion_injective (G : ι → Type u) [∀ i, Group (G i)] (i : ι) :
    Function.Injective (factorInclusion G i) :=
  Monoid.CoprodI.of_injective i

/-!
## Conjugate intersections

The subgroup is deliberately defined inside the ambient group first.  A later
construction restricts it to the subgroup `H`, which gives the factors that
appear literally in the Kurosh decomposition.
-/

/-- Conjugation of a subgroup by an ambient-group element. -/
@[expose] def conjugateSubgroup {P : Type u} [Group P] (K : Subgroup P) (g : P) : Subgroup P :=
  K.map (MulAut.conj g)

@[simp]
theorem mem_conjugateSubgroup_iff {P : Type u} [Group P] (K : Subgroup P) (g x : P) :
    x ∈ conjugateSubgroup K g ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- The ambient subgroup obtained from a Kurosh factor. -/
@[expose] def intersectionFactor {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G) : Subgroup (FreeProduct G) :=
  H ⊓ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g

/-- The same factor regarded as a subgroup of `H`, so its inclusion into `H` is canonical. -/
@[expose] def intersectionFactorInH {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G) : Subgroup H :=
  (intersectionFactor H i g).comap H.subtype

theorem intersectionFactorInH_coe_mem {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G)
    (x : intersectionFactorInH H i g) :
    (x : FreeProduct G) ∈ intersectionFactor H i g :=
  x.property

/-!
## The double-coset indexing type

Mathlib's `DoubleCoset.Quotient` is exactly `H \ G / K`.  Defining the
factor index this way records the classical indexing without choosing
representatives prematurely.  Representatives are selected only when the
decomposition construction needs them.
-/

/-- Double cosets of `H` and the image of the indexed free factor. -/
abbrev DoubleCosetIndex {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) :=
  DoubleCoset.Quotient (H : Set (FreeProduct G))
    (MonoidHom.range (factorInclusion G i) : Set (FreeProduct G))

/-- A chosen representative of a double coset. -/
def doubleCosetRepresentative {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (q : DoubleCosetIndex H i) : FreeProduct G :=
  q.out

@[simp]
theorem doubleCosetRepresentative_mk {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G) :
    DoubleCoset.mk H (MonoidHom.range (factorInclusion G i))
        (doubleCosetRepresentative H i
          (DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) g)) =
      DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) g := by
  exact DoubleCoset.out_eq' _

theorem doubleCosetIndex_eq_iff {G : ι → Type u} [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (i : ι) (g h : FreeProduct G) :
    DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) g =
        DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) h ↔
      ∃ a ∈ H, ∃ b ∈ MonoidHom.range (factorInclusion G i), h = a * g * b := by
  exact DoubleCoset.eq

/-!
## Right-coset normal forms

The Bass--Serre action is a left action on right cosets.  The indexed
coproduct API exposes the first syllable directly, so right-coset normal
forms are obtained by applying the same operation to the inverse word.  The
small word reversal API here is useful independently of the later tree
construction.
-/

/-- Invert a reduced word by reversing its letters and inverting each letter. -/
def wordInv {G : ι → Type u} [∀ i, Group (G i)]
    (w : Word G) : Word G :=
  { toList := w.toList.reverse.map (fun x : Σ i, G i => ⟨x.1, x.2⁻¹⟩)
    ne_one := by
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      exact inv_ne_one.mpr (w.ne_one x (by simpa using hx))
    chain_ne := by
      apply (List.isChain_map _).2
      apply (List.isChain_reverse).2
      simpa only using w.chain_ne.imp (fun _ _ h => Ne.symm h) }

@[simp]
theorem wordInv_toList {G : ι → Type u} [∀ i, Group (G i)] (w : Word G) :
    (wordInv w).toList = w.toList.reverse.map (fun x : Σ i, G i => ⟨x.1, x.2⁻¹⟩) :=
  by rfl

theorem wordInv_prod {G : ι → Type u} [∀ i, Group (G i)] (w : Word G) :
    (wordInv w).prod = w.prod⁻¹ := by
  simp [wordInv, Word.prod, List.map_reverse, List.map_map,
    Function.comp_def, List.prod_reverse_noncomm]

@[simp]
theorem wordInv_wordInv {G : ι → Type u} [∀ i, Group (G i)] (w : Word G) :
    wordInv (wordInv w) = w := by
  apply Word.ext
  simp [wordInv, Function.comp_def, List.map_map]

/-- The factor index of the last letter, or `none` for the empty word. -/
@[expose] def wordLastIdx {G : ι → Type u} [∀ i, Group (G i)] (w : Word G) : Option ι :=
  (wordInv w).fstIdx

private lemma head_reverse_map {α β : Type*} (f : α → β) (l : List α) :
    (l.reverse.map f).head? = l.getLast?.map f := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl x ih => simp

theorem wordLastIdx_ne_iff {G : ι → Type u} [∀ i, Group (G i)]
    (w : Word G) (i : ι) :
    wordLastIdx w ≠ some i ↔
      ∀ l ∈ w.toList.getLast?, i ≠ l.1 := by
  rw [wordLastIdx, Word.fstIdx_ne_iff]
  rw [wordInv_toList, head_reverse_map, Option.forall_mem_map]

/-!
## Removing a rightmost syllable

This is the right-coset counterpart of `Word.equivPair`: the inverse word is
split at its first syllable and then inverted again.  It supplies the
canonical representative of a right coset of a factor.
-/

/-- Remove the terminal letter in factor `i`, if present. -/
noncomputable def rightTail {G : ι → Type u} [∀ i, Group (G i)] (i : ι) (w : Word G) : Word G := by
  classical
  exact wordInv ((Word.equivPair i (wordInv w)).tail)

/-- The terminal factor-`i` letter, or the identity if the word ends in another factor. -/
noncomputable def rightHead {G : ι → Type u} [∀ i, Group (G i)] (i : ι) (w : Word G) : G i := by
  classical
  exact (Word.equivPair i (wordInv w)).head⁻¹

theorem rightTail_lastIdx_ne {G : ι → Type u} [∀ i, Group (G i)] (i : ι) (w : Word G) :
    wordLastIdx (rightTail i w) ≠ some i := by
  classical
  rw [rightTail, wordLastIdx, wordInv_wordInv]
  exact (Word.equivPair i (wordInv w)).fstIdx_ne

/-- Reduced words representing cosets `g * Gᵢ`, obtained by removing the terminal
`i`-factor. -/
abbrev RightFactorWord {G : ι → Type u} [∀ i, Group (G i)] (i : ι) :=
  {w : Word G // wordLastIdx w ≠ some i}

/-- The right tail bundled with the fact that its last index differs from `i`. -/
@[expose] noncomputable def rightTailCanonical {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) : RightFactorWord (G := G) i :=
  ⟨rightTail i w, rightTail_lastIdx_ne i w⟩

theorem rightTail_of_lastIdx_ne {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (hw : wordLastIdx w ≠ some i) :
    rightTail i w = w := by
  classical
  rw [rightTail, Word.equivPair_eq_of_fstIdx_ne]
  · simp
  · exact hw

theorem equivPair_head_ne_one_of_fstIdx_eq {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (hwi : w.fstIdx = some i) :
    (Word.equivPair i w).head ≠ 1 := by
  intro hhead
  have htail : (Word.equivPair i w).tail = w := by
    simpa [hhead] using
      (Word.equivPair_head_smul_equivPair_tail (i := i) w)
  apply (Word.equivPair i w).fstIdx_ne
  rw [htail]
  exact hwi

theorem rightHead_ne_one_of_lastIdx_eq {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (hwi : wordLastIdx w = some i) : rightHead i w ≠ 1 := by
  intro hhead
  apply equivPair_head_ne_one_of_fstIdx_eq i (wordInv w)
  · simpa [wordLastIdx] using hwi
  · simpa [rightHead] using hhead

theorem right_syllable_decomposition {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) :
    w.prod = (rightTail i w).prod * Monoid.CoprodI.of (rightHead i w) := by
  classical
  let p := Word.equivPair i (wordInv w)
  have hp : Monoid.CoprodI.of p.head * p.tail.prod = (wordInv w).prod := by
    have hp' := congrArg Word.prod
      (Word.equivPair_head_smul_equivPair_tail (i := i) (wordInv w))
    simpa only [p, Word.prod_smul] using hp'
  have hw : w.prod = (wordInv w).prod⁻¹ := by
    simpa only [wordInv_wordInv] using (wordInv_prod (wordInv w))
  change w.prod = (wordInv p.tail).prod * Monoid.CoprodI.of p.head⁻¹
  rw [hw, ← hp, mul_inv_rev, wordInv_prod]
  simp

/-- Append a nonidentity factor-`i` letter to a word ending in a different factor. -/
@[expose] noncomputable def rightAppend {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (a : G i) (ha : a ≠ 1)
    (hw : wordLastIdx w ≠ some i) : Word G :=
  wordInv (Word.cons a⁻¹ (wordInv w)
    (by simpa [wordLastIdx] using hw) (inv_ne_one.mpr ha))

theorem wordInv_cons_rightAppend {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (a : G i) (w : Word G) (hw : w.fstIdx ≠ some i) (ha : a ≠ 1) :
    rightAppend i (⟨wordInv w, by simpa [wordLastIdx] using hw⟩ : RightFactorWord (G := G) i)
        a⁻¹ (inv_ne_one.mpr ha) (by simpa [wordLastIdx] using hw) =
      wordInv (Word.cons a w hw ha) := by
  simp only [rightAppend, inv_inv, wordInv_wordInv]

@[simp]
theorem rightAppend_prod {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (a : G i) (ha : a ≠ 1)
    (hw : wordLastIdx w ≠ some i) :
    (rightAppend i w a ha hw).prod =
      w.prod * Monoid.CoprodI.of a := by
  simp only [rightAppend, wordInv_prod, Word.prod_cons, map_inv, mul_inv_rev]
  simp

private theorem equivPair_cons_rightAppend {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (a : G i) (ha : a ≠ 1)
    (hw : wordLastIdx w ≠ some i) :
    Word.equivPair i
        (Word.cons a⁻¹ (wordInv w)
          (by simpa [wordLastIdx] using hw) (inv_ne_one.mpr ha)) =
      ⟨a⁻¹, wordInv w, by simpa [wordLastIdx] using hw⟩ := by
  classical
  rw [Word.cons_eq_smul]
  rw [Word.equivPair_smul_same, Word.equivPair_eq_of_fstIdx_ne]
  · simp
  · simpa [wordLastIdx] using hw

theorem rightAppend_rightTail {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (a : G i) (ha : a ≠ 1)
    (hw : wordLastIdx w ≠ some i) :
    rightTail i (rightAppend i w a ha hw) = w := by
  classical
  rw [rightTail, rightAppend, wordInv_wordInv,
    equivPair_cons_rightAppend i w a ha hw]
  simp

theorem rightAppend_rightHead {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (a : G i) (ha : a ≠ 1)
    (hw : wordLastIdx w ≠ some i) :
    rightHead i (rightAppend i w a ha hw) = a := by
  classical
  rw [rightHead, rightAppend, wordInv_wordInv,
    equivPair_cons_rightAppend i w a ha hw]
  simp

theorem word_equiv_mul_rightAppend {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : RightFactorWord (G := G) i) (a : G i) (ha : a ≠ 1) :
    Word.equiv (w.1.prod * Monoid.CoprodI.of a) =
      rightAppend i w.1 a ha w.2 := by
  apply (Word.equiv.symm).injective
  rw [(Word.equiv).symm_apply_apply]
  change w.1.prod * Monoid.CoprodI.of a =
    (rightAppend i w.1 a ha w.2).prod
  rw [rightAppend_prod]

theorem rightTail_equiv_mul_factor {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : RightFactorWord (G := G) i) (a : G i) :
    rightTail i (Word.equiv (w.1.prod * Monoid.CoprodI.of a)) = w.1 := by
  by_cases ha : a = 1
  · subst a
    simp only [map_one, mul_one]
    have hw : Word.equiv w.1.prod = w.1 :=
      (Word.equiv).apply_symm_apply w.1
    rw [hw]
    exact rightTail_of_lastIdx_ne i w.1 w.2
  · rw [word_equiv_mul_rightAppend i w a ha]
    exact rightAppend_rightTail i w.1 a ha w.2

theorem rightTail_eq_of_prod_eq_mul_factor {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w w' : RightFactorWord (G := G) i) (a a' : G i)
    (h : w.1.prod * Monoid.CoprodI.of a =
      w'.1.prod * Monoid.CoprodI.of a') : w.1 = w'.1 := by
  have hword : Word.equiv (w.1.prod * Monoid.CoprodI.of a) =
      Word.equiv (w'.1.prod * Monoid.CoprodI.of a') := by
    rw [h]
  have htail := congrArg (rightTail i) hword
  simpa [rightTail_equiv_mul_factor] using htail

/-- Append a nonidentity letter to a canonical representative for its factor coset. -/
@[expose] noncomputable def rightAppendCanonical {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : RightFactorWord (G := G) i) (a : G i) (ha : a ≠ 1) : Word G :=
  rightAppend i w.1 a ha w.2

theorem rightAppendCanonical_of_lastIdx_eq {G : ι → Type u} [∀ i, Group (G i)]
    (i : ι) (w : Word G) (hwi : wordLastIdx w = some i) :
    rightAppendCanonical i (rightTailCanonical i w) (rightHead i w)
        (rightHead_ne_one_of_lastIdx_eq i w hwi) = w := by
  classical
  let p := Word.equivPair i (wordInv w)
  have hp : Word.rcons p = wordInv w := by
    change (Word.equivPair i).symm (Word.equivPair i (wordInv w)) = wordInv w
    exact (Word.equivPair i).symm_apply_apply (wordInv w)
  have hpne : p.head ≠ 1 := by
    apply equivPair_head_ne_one_of_fstIdx_eq i (wordInv w)
    · simpa [wordLastIdx] using hwi
  have hpcons : Word.cons p.head p.tail p.fstIdx_ne hpne = wordInv w := by
    rw [← hp]
    simp [Word.rcons, hpne]
  unfold rightAppendCanonical rightTailCanonical rightAppend rightTail rightHead
  simp only [inv_inv, wordInv_wordInv]
  change wordInv (Word.cons p.head p.tail _ _) = w
  rw [hpcons, wordInv_wordInv]

/-!
## The explicit Bass--Serre tree

The central vertices are reduced words.  A factor vertex records a reduced
word which is already canonical on the right for one factor.  The two edge
families are the central-to-factor edge and the edge obtained by appending a
nontrivial factor syllable.  This is the usual normal-form model of the
Bass--Serre tree of an indexed free product.
-/

/-- The word model of Bass-Serre vertices: reduced words and canonical factor-coset words. -/
inductive BassSerreVertex {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    Type (max u v) where
  | central (w : Word G)
  | factor (i : ι) (w : RightFactorWord (G := G) i)

/-- The directed edges of the word model, oriented away from the empty word. -/
inductive BassSerreEdge {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    BassSerreVertex G → BassSerreVertex G → Type (max u v)
  | centralFactor (w : Word G) (i : ι) (hw : wordLastIdx w ≠ some i) :
      BassSerreEdge G (BassSerreVertex.central w)
        (BassSerreVertex.factor i ⟨w, hw⟩)
  | factorCentral (i : ι) (w : RightFactorWord (G := G) i) (a : G i) (ha : a ≠ 1) :
      BassSerreEdge G (BassSerreVertex.factor i w)
        (BassSerreVertex.central (rightAppendCanonical i w a ha))

instance bassSerreQuiver {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    Quiver (BassSerreVertex G) where
  Hom := BassSerreEdge G

theorem bassSerreWord_path {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (w : Word G) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (BassSerreVertex G)) _
      (BassSerreVertex.central Word.empty) (BassSerreVertex.central w)) := by
  let root : Quiver.Symmetrify (BassSerreVertex G) := BassSerreVertex.central Word.empty
  have hpath : ∀ q : Word G,
      Nonempty (@Quiver.Path (Quiver.Symmetrify (BassSerreVertex G)) _
        root (BassSerreVertex.central (wordInv q))) := by
    intro q
    induction q using Word.consRecOn with
    | empty =>
        exact ⟨Quiver.Path.nil⟩
    | @cons i a q hq ha ih =>
        rcases ih with ⟨p⟩
        let hw : wordLastIdx (wordInv q) ≠ some i := by
          simpa [wordLastIdx] using hq
        let e₁ : BassSerreVertex.central (wordInv q) ⟶
            BassSerreVertex.factor i ⟨wordInv q, hw⟩ :=
          BassSerreEdge.centralFactor (wordInv q) i hw
        let e₂ : BassSerreVertex.factor i ⟨wordInv q, hw⟩ ⟶
            BassSerreVertex.central
              (rightAppendCanonical i ⟨wordInv q, hw⟩ a⁻¹ (inv_ne_one.mpr ha)) :=
          BassSerreEdge.factorCentral i ⟨wordInv q, hw⟩ a⁻¹ (inv_ne_one.mpr ha)
        have he : rightAppendCanonical i ⟨wordInv q, hw⟩ a⁻¹
              (inv_ne_one.mpr ha) = wordInv (Word.cons a q hq ha) := by
          exact wordInv_cons_rightAppend i a q hq ha
        refine ⟨?_⟩
        rw [← he]
        exact p.cons (Quiver.Hom.toPos e₁) |>.cons (Quiver.Hom.toPos e₂)
  simpa [root] using hpath (wordInv w)

theorem bassSerreFactor_path {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (i : ι) (w : RightFactorWord (G := G) i) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (BassSerreVertex G)) _
      (BassSerreVertex.central Word.empty) (BassSerreVertex.factor i w)) := by
  rcases bassSerreWord_path G w.1 with ⟨p⟩
  exact ⟨p.cons (Quiver.Hom.toPos (BassSerreEdge.centralFactor w.1 i w.2))⟩

theorem bassSerre_rootedConnected {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Quiver.RootedConnected
      (show Quiver.Symmetrify (BassSerreVertex G) from BassSerreVertex.central Word.empty) := by
  constructor
  intro b
  cases b with
  | central w => exact bassSerreWord_path G w
  | factor i w => exact bassSerreFactor_path G i w

/-- A geodesic spanning tree of the symmetrified word model. -/
@[expose] noncomputable def bassSerreTree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    WideSubquiver (Quiver.Symmetrify (BassSerreVertex G)) :=
  @Quiver.geodesicSubtree (Quiver.Symmetrify (BassSerreVertex G))
    (Quiver.symmetrifyQuiver (BassSerreVertex G))
    (BassSerreVertex.central Word.empty)
    (bassSerre_rootedConnected G)

noncomputable instance bassSerreTreeArborescence {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Quiver.Arborescence (bassSerreTree G) :=
  @Quiver.geodesicArborescence (Quiver.Symmetrify (BassSerreVertex G))
    (Quiver.symmetrifyQuiver (BassSerreVertex G))
    (BassSerreVertex.central Word.empty)
    (bassSerre_rootedConnected G)

/-!
## Right cosets and the natural action

The canonical-word vertices above are convenient for connectivity proofs.  For
the group action it is cleaner to use the quotient of a group by right
multiplication by a subgroup.  The quotient is kept elementary here so that
the stabilizer calculation does not depend on a choice of representatives.
-/

/-- Equivalence under multiplication on the right by an element of `K`. -/
def rightCosetSetoid {P : Type w} [Group P] (K : Subgroup P) : Setoid P where
  r a b := ∃ k : K, a * k = b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by simp⟩
    · rintro a b ⟨k, hk⟩
      refine ⟨k⁻¹, ?_⟩
      calc
        b * (k⁻¹ : P) = (a * (k : P)) * (k⁻¹ : P) := by rw [hk]
        _ = a := by simp [mul_assoc]
    · rintro a b c ⟨k, hk⟩ ⟨l, hl⟩
      refine ⟨k * l, ?_⟩
      calc
        a * (k * l) = (a * k) * l := by rw [mul_assoc]
        _ = b * l := by rw [hk]
        _ = c := hl

/-- Cosets represented by `a * K`, using the right-multiplication equivalence relation. -/
abbrev RightCoset {P : Type w} [Group P] (K : Subgroup P) :=
  Quotient (rightCosetSetoid K)

/-- The coset represented by a group element. -/
@[expose] def rightCosetMk {P : Type w} [Group P] (K : Subgroup P) (a : P) : RightCoset K :=
  Quotient.mk (rightCosetSetoid K) a

theorem rightCosetMk_eq_iff {P : Type w} [Group P] (K : Subgroup P) (a b : P) :
    rightCosetMk K a = rightCosetMk K b ↔ ∃ k : K, a * k = b := by
  exact Quotient.eq''

instance rightCosetMulAction {P : Type w} [Group P] (K : Subgroup P) :
    MulAction P (RightCoset K) where
  smul g := Quotient.lift (fun a => rightCosetMk K (g * a)) (by
    intro a b hab
    rcases hab with ⟨k, hk⟩
    change Quotient.mk (rightCosetSetoid K) (g * a) =
      Quotient.mk (rightCosetSetoid K) (g * b)
    apply Quotient.sound
    refine ⟨k, ?_⟩
    rw [mul_assoc, hk])
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ a =>
        change rightCosetMk K (1 * a) = rightCosetMk K a
        simp
  mul_smul g h q := by
    induction q using Quotient.inductionOn with
    | _ a =>
        change rightCosetMk K ((g * h) * a) =
          rightCosetMk K (g * (h * a))
        rw [mul_assoc]

@[simp]
theorem rightCosetMk_smul {P : Type w} [Group P] (K : Subgroup P) (g a : P) :
    g • rightCosetMk K a = rightCosetMk K (g * a) := by
  change rightCosetMk K (g * a) = rightCosetMk K (g * a)
  rfl

theorem rightCoset_stabilizer_iff {P : Type w} [Group P] (K : Subgroup P)
    (g a : P) : g • rightCosetMk K a = rightCosetMk K a ↔
      a⁻¹ * g * a ∈ K := by
  rw [rightCosetMk_smul, rightCosetMk_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hconj : a⁻¹ * g * a = k⁻¹ := by
      apply (mul_right_cancel (b := (k : P)))
      calc
        (a⁻¹ * g * a) * k = a⁻¹ * (g * a * k) := by simp [mul_assoc]
        _ = a⁻¹ * a := by rw [hk]
        _ = 1 := by simp
        _ = k⁻¹ * k := by simp
    rw [hconj]
    exact K.inv_mem k.property
  · intro h
    refine ⟨⟨(a⁻¹ * g * a)⁻¹, K.inv_mem h⟩, ?_⟩
    simp [mul_assoc]

/-- Cosets of the image of a free factor in the ambient free product. -/
abbrev FactorCoset {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] (i : ι) :=
  RightCoset (MonoidHom.range (factorInclusion G i))

/-- The factor coset represented by an element of the free product. -/
@[expose] def factorCosetMk {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (i : ι) (g : FreeProduct G) : FactorCoset G i :=
  rightCosetMk (MonoidHom.range (factorInclusion G i)) g

theorem factorCoset_mul_factor {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (i : ι) (g : FreeProduct G) (a : G i) :
    factorCosetMk G i (g * Monoid.CoprodI.of a) = factorCosetMk G i g := by
  apply (rightCosetMk_eq_iff (MonoidHom.range (factorInclusion G i))
    (g * Monoid.CoprodI.of a) g).2
  refine ⟨⟨Monoid.CoprodI.of a⁻¹, ?_⟩, ?_⟩
  · exact ⟨a⁻¹, rfl⟩
  · simp [mul_assoc]

/-- Bass-Serre vertices represented by group elements and factor cosets. -/
inductive RawBassSerreVertex {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    Type (max u v) where
  | central (g : FreeProduct G)
  | factor (i : ι) (c : FactorCoset G i)

/-- An edge joins an ambient group element to its coset in a free factor. -/
inductive RawBassSerreEdge {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    RawBassSerreVertex G → RawBassSerreVertex G → Type (max u v)
  | centralFactor (g : FreeProduct G) (i : ι) :
      RawBassSerreEdge G (RawBassSerreVertex.central g)
        (RawBassSerreVertex.factor i (factorCosetMk G i g))

instance rawBassSerreQuiver {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    Quiver (RawBassSerreVertex G) where
  Hom := RawBassSerreEdge G

theorem rawBassSerreWord_path {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g : FreeProduct G) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _
      (RawBassSerreVertex.central 1) (RawBassSerreVertex.central g)) := by
  let root : Quiver.Symmetrify (RawBassSerreVertex G) :=
    RawBassSerreVertex.central 1
  have hpath : ∀ q : Word G,
      Nonempty (@Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _
        root (RawBassSerreVertex.central (wordInv q).prod)) := by
    intro q
    induction q using Word.consRecOn with
    | empty =>
        exact ⟨Quiver.Path.nil⟩
    | @cons i a q hq ha ih =>
        rcases ih with ⟨p⟩
        let old : FreeProduct G := (wordInv q).prod
        let new : FreeProduct G := (wordInv (Word.cons a q hq ha)).prod
        let e₁ : RawBassSerreVertex.central old ⟶
            RawBassSerreVertex.factor i (factorCosetMk G i old) :=
          RawBassSerreEdge.centralFactor old i
        have hnew : new = old * Monoid.CoprodI.of a⁻¹ := by
          dsimp [new, old]
          calc
            (wordInv (Word.cons a q hq ha)).prod =
                (rightAppend i (wordInv q) a⁻¹
                  (inv_ne_one.mpr ha) (by simpa [wordLastIdx] using hq)).prod := by
              rw [← wordInv_cons_rightAppend i a q hq ha]
            _ = (wordInv q).prod * Monoid.CoprodI.of a⁻¹ := by
              rw [rightAppend_prod]
        have hcoset : factorCosetMk G i new = factorCosetMk G i old := by
          rw [hnew]
          exact factorCoset_mul_factor G i old a⁻¹
        let e₂ : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
            (Quiver.symmetrifyQuiver (RawBassSerreVertex G))
            (RawBassSerreVertex.factor i (factorCosetMk G i old))
            (RawBassSerreVertex.central new) := by
          rw [← hcoset]
          exact Quiver.Hom.toNeg (RawBassSerreEdge.centralFactor new i)
        refine ⟨?_⟩
        change @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _
          root (RawBassSerreVertex.central new)
        exact p.cons (Quiver.Hom.toPos e₁) |>.cons e₂
  have hword : (Word.equiv g).prod = g := (Word.equiv).symm_apply_apply g
  rw [← hword]
  simpa [root] using hpath (wordInv (Word.equiv g))

theorem rawBassSerreFactor_path {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (c : FactorCoset G i) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _
      (RawBassSerreVertex.central 1) (RawBassSerreVertex.factor i c)) := by
  let g : FreeProduct G := Quotient.out c
  have hg : factorCosetMk G i g = c := by
    simp [g, factorCosetMk, rightCosetMk]
  rcases rawBassSerreWord_path G g with ⟨p⟩
  let e : RawBassSerreVertex.central g ⟶
      RawBassSerreVertex.factor i (factorCosetMk G i g) :=
    RawBassSerreEdge.centralFactor g i
  have pe := p.cons (Quiver.Hom.toPos e)
  exact ⟨by simpa only [hg] using pe⟩

theorem rawBassSerre_rootedConnected {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Quiver.RootedConnected
      (show Quiver.Symmetrify (RawBassSerreVertex G) from
        RawBassSerreVertex.central 1) := by
  constructor
  intro b
  cases b with
  | central g => exact rawBassSerreWord_path G g
  | factor i c => exact rawBassSerreFactor_path G i c

/-- A geodesic spanning tree of the symmetrified group-and-coset model. -/
@[expose] noncomputable def rawBassSerreTree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    WideSubquiver (Quiver.Symmetrify (RawBassSerreVertex G)) :=
  @Quiver.geodesicSubtree (Quiver.Symmetrify (RawBassSerreVertex G))
    (Quiver.symmetrifyQuiver (RawBassSerreVertex G))
    (RawBassSerreVertex.central 1) (rawBassSerre_rootedConnected G)

noncomputable instance rawBassSerreTreeArborescence {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] :
    Quiver.Arborescence (rawBassSerreTree G) :=
  @Quiver.geodesicArborescence (Quiver.Symmetrify (RawBassSerreVertex G))
    (Quiver.symmetrifyQuiver (RawBassSerreVertex G))
    (RawBassSerreVertex.central 1) (rawBassSerre_rootedConnected G)

instance rawBassSerreVertexMulAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : MulAction (FreeProduct G) (RawBassSerreVertex G) where
  smul g := fun x => match x with
    | RawBassSerreVertex.central h => RawBassSerreVertex.central (g * h)
    | RawBassSerreVertex.factor i c => RawBassSerreVertex.factor i (g • c)
  one_smul x := by
    cases x with
    | central h =>
        change RawBassSerreVertex.central (1 * h) = RawBassSerreVertex.central h
        simp
    | factor i c =>
        change RawBassSerreVertex.factor i (1 • c) = RawBassSerreVertex.factor i c
        simp
  mul_smul g h x := by
    cases x with
    | central k =>
        change RawBassSerreVertex.central ((g * h) * k) =
          RawBassSerreVertex.central (g * (h * k))
        rw [mul_assoc]
    | factor i c =>
        change RawBassSerreVertex.factor i ((g * h) • c) =
          RawBassSerreVertex.factor i (g • h • c)
        rw [mul_smul]

theorem rawBassSerre_factor_fixed_iff {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g : FreeProduct G) (h : H) :
    h.1 • RawBassSerreVertex.factor i (factorCosetMk G i g) =
        RawBassSerreVertex.factor i (factorCosetMk G i g) ↔
      (h : FreeProduct G) ∈ intersectionFactor H i g := by
  change RawBassSerreVertex.factor i (h.1 • factorCosetMk G i g) =
      RawBassSerreVertex.factor i (factorCosetMk G i g) ↔ _
  simp only [RawBassSerreVertex.factor.injEq, true_and, heq_eq_eq]
  change h.1 • rightCosetMk (MonoidHom.range (factorInclusion G i)) g =
      rightCosetMk (MonoidHom.range (factorInclusion G i)) g ↔ _
  rw [rightCoset_stabilizer_iff (MonoidHom.range (factorInclusion G i)) h.1 g]
  simp only [intersectionFactor, Subgroup.mem_inf, h.property, true_and,
    mem_conjugateSubgroup_iff]

theorem rawBassSerre_factor_orbit_iff {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g h : FreeProduct G) :
    (∃ k : H,
      k.1 • RawBassSerreVertex.factor i (factorCosetMk G i g) =
        RawBassSerreVertex.factor i (factorCosetMk G i h)) ↔
      DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) g =
        DoubleCoset.mk H (MonoidHom.range (factorInclusion G i)) h := by
  constructor
  · rintro ⟨k, hk⟩
    change RawBassSerreVertex.factor i
        (k.1 • factorCosetMk G i g) =
      RawBassSerreVertex.factor i (factorCosetMk G i h) at hk
    have hkcos : k.1 • factorCosetMk G i g = factorCosetMk G i h := by
      simpa only [RawBassSerreVertex.factor.injEq, true_and, heq_eq_eq] using hk
    change rightCosetMk (MonoidHom.range (factorInclusion G i))
        (k.1 * g) = rightCosetMk (MonoidHom.range (factorInclusion G i)) h at hkcos
    rw [rightCosetMk_eq_iff (MonoidHom.range (factorInclusion G i))
      (k.1 * g) h] at hkcos
    rcases hkcos with ⟨b, hb⟩
    apply (doubleCosetIndex_eq_iff H i g h).2
    refine ⟨k.1, k.property, b.1, b.property, ?_⟩
    exact hb.symm
  · intro hdouble
    rcases (doubleCosetIndex_eq_iff H i g h).1 hdouble with
      ⟨a, ha, b, hb, hab⟩
    let k : H := ⟨a, ha⟩
    refine ⟨k, ?_⟩
    change RawBassSerreVertex.factor i
        (a • factorCosetMk G i g) =
      RawBassSerreVertex.factor i (factorCosetMk G i h)
    apply congrArg (RawBassSerreVertex.factor i)
    change rightCosetMk (MonoidHom.range (factorInclusion G i))
        (a * g) = factorCosetMk G i h
    apply (rightCosetMk_eq_iff (MonoidHom.range (factorInclusion G i))
      (a * g) h).2
    refine ⟨⟨b, hb⟩, ?_⟩
    exact hab.symm

/-- Pairs of a free-factor index and a corresponding double coset. -/
abbrev KuroshFactorIndex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  Σ i, DoubleCosetIndex H i

/-- The chosen ambient group element for an indexed double coset. -/
noncomputable def kuroshFactorRepresentative {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : KuroshFactorIndex G H) : FreeProduct G :=
  doubleCosetRepresentative H q.1 q.2

/-- The intersection with a conjugate free factor, regarded as a subgroup of `H`. -/
def kuroshFactorSubgroup {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (q : KuroshFactorIndex G H) : Subgroup H :=
  intersectionFactorInH H q.1 (kuroshFactorRepresentative G H q)

/-- A central Bass–Serre vertex has trivial stabilizer. -/
theorem rawBassSerre_central_fixed_iff {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g h : FreeProduct G) :
    h • RawBassSerreVertex.central g = RawBassSerreVertex.central g ↔ h = 1 := by
  change RawBassSerreVertex.central (h * g) =
      RawBassSerreVertex.central g ↔ h = 1
  simp only [RawBassSerreVertex.central.injEq]
  constructor
  · intro heq
    apply (mul_right_cancel (b := g))
    simp [heq]
  · intro heq
    simp [heq]

theorem kurosh_factor_subgroup_is_stabilizer {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : KuroshFactorIndex G H) (h : H) :
    h ∈ kuroshFactorSubgroup G H q ↔
      h.1 • RawBassSerreVertex.factor q.1
          (factorCosetMk G q.1 (kuroshFactorRepresentative G H q)) =
        RawBassSerreVertex.factor q.1
          (factorCosetMk G q.1 (kuroshFactorRepresentative G H q)) := by
  exact (rawBassSerre_factor_fixed_iff G H q.1
    (kuroshFactorRepresentative G H q) h).symm

/-!
## The quotient graph seen by the subgroup

The raw tree is the universal Bass--Serre tree.  The next layer records the
quotient graph without choosing representatives of its vertices or edges.
This is the graph on which the free part of the Kurosh decomposition is the
fundamental-group contribution; the factor vertices retain the stabilizers
defined above.
-/

/-- The standard Mathlib quotient of an action by its orbit relation. -/
abbrev ActionOrbit (A : Type w) (X : Type w) [Group A] [MulAction A X] :=
  MulAction.orbitRel.Quotient A X

/-- Send a point to its group-action orbit. -/
@[expose] def actionOrbitMk (A : Type w) (X : Type w) [Group A] [MulAction A X]
    (x : X) : ActionOrbit A X := Quotient.mk (MulAction.orbitRel A X) x

/-- Orbit equality expressed by an element carrying the first point to the second.
Mathlib's orbit relation uses the reverse orientation. -/
@[simp]
theorem actionOrbitMk_eq_iff (A : Type w) (X : Type w) [Group A] [MulAction A X]
    (x y : X) : actionOrbitMk A X x = actionOrbitMk A X y ↔
      ∃ a : A, a • x = y := by
  constructor
  · intro h
    exact Quotient.exact h.symm
  · intro h
    exact (Quotient.sound h).symm

theorem actionOrbitMk_smul (A : Type w) (X : Type w) [Group A] [MulAction A X]
    (a : A) (x : X) : actionOrbitMk A X (a • x) = actionOrbitMk A X x := by
  apply (actionOrbitMk_eq_iff A X (a • x) x).2
  exact ⟨a⁻¹, by simp⟩

/-- An unbundled Bass-Serre edge is a group element paired with a factor index. -/
def rawBassSerreEdgeData {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :=
  FreeProduct G × ι

/-- The central vertex at the source of an unbundled edge. -/
def rawBassSerreEdgeDataSource {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (e : rawBassSerreEdgeData G) : RawBassSerreVertex G :=
  RawBassSerreVertex.central e.1

/-- The factor coset at the target of an unbundled edge. -/
def rawBassSerreEdgeDataTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (e : rawBassSerreEdgeData G) : RawBassSerreVertex G :=
  RawBassSerreVertex.factor e.2 (factorCosetMk G e.2 e.1)

/-- Translate an unbundled edge by left multiplication on its group coordinate. -/
def rawBassSerreEdgeDataAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (a : FreeProduct G) (e : rawBassSerreEdgeData G) :
    rawBassSerreEdgeData G :=
  (a * e.1, e.2)

instance rawBassSerreEdgeDataMulAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : MulAction (FreeProduct G) (rawBassSerreEdgeData G) where
  smul := rawBassSerreEdgeDataAction G
  one_smul e := by
    change (1 * e.1, e.2) = e
    rcases e with ⟨g, i⟩
    simp
  mul_smul a b e := by
    change ((a * b) * e.1, e.2) = (a * (b * e.1), e.2)
    rw [mul_assoc]

theorem rawBassSerreEdgeData_source_action {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (a : FreeProduct G) (e : rawBassSerreEdgeData G) :
    rawBassSerreEdgeDataSource G (a • e) = a • rawBassSerreEdgeDataSource G e := by
  rfl

theorem rawBassSerreEdgeData_target_action {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (a : FreeProduct G) (e : rawBassSerreEdgeData G) :
    rawBassSerreEdgeDataTarget G (a • e) = a • rawBassSerreEdgeDataTarget G e := by
  cases e using Prod.casesOn with
  | mk g i =>
      change RawBassSerreVertex.factor i (factorCosetMk G i (a * g)) =
        RawBassSerreVertex.factor i (a • factorCosetMk G i g)
      apply congrArg (RawBassSerreVertex.factor i)
      change rightCosetMk (MonoidHom.range (factorInclusion G i)) (a * g) =
        a • rightCosetMk (MonoidHom.range (factorInclusion G i)) g
      rw [rightCosetMk_smul]

instance rawBassSerreVertexSubgroupMulAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    MulAction H (RawBassSerreVertex G) where
  smul h x := h.1 • x
  one_smul x := by simp
  mul_smul a b x := by simp [mul_smul]

instance rawBassSerreEdgeDataSubgroupMulAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    MulAction H (rawBassSerreEdgeData G) where
  smul h e := h.1 • e
  one_smul e := by simp
  mul_smul a b e := by simp [mul_smul]

/-- Forget the endpoints of a bundled Bass-Serre edge. -/
def rawBassSerreEdgeDataOf {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : RawBassSerreVertex G} (e : a ⟶ b) :
    rawBassSerreEdgeData G := by
  cases e using RawBassSerreEdge.casesOn with
  | centralFactor g i => exact (g, i)

theorem rawBassSerreEdgeDataOf_source {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : RawBassSerreVertex G} (e : a ⟶ b) :
    rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G e) = a := by
  cases e using RawBassSerreEdge.casesOn; rfl

theorem rawBassSerreEdgeDataOf_target {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : RawBassSerreVertex G} (e : a ⟶ b) :
    rawBassSerreEdgeDataTarget G (rawBassSerreEdgeDataOf G e) = b := by
  cases e using RawBassSerreEdge.casesOn; rfl

/-- Translate a Bass-Serre edge and both endpoints by a group element. -/
def rawBassSerreEdgeAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g : FreeProduct G) {a b : RawBassSerreVertex G}
    (e : a ⟶ b) : g • a ⟶ g • b := by
  cases e using RawBassSerreEdge.casesOn with
  | centralFactor h i =>
      change RawBassSerreEdge G (RawBassSerreVertex.central (g * h))
        (RawBassSerreVertex.factor i (g • factorCosetMk G i h))
      exact RawBassSerreEdge.centralFactor (g * h) i

/-- Translate either orientation of a Bass-Serre edge. -/
def rawBassSerreSymmEdgeAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g : FreeProduct G) {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G)) _ a b) :
    @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G)) _ (g • a) (g • b) := by
  cases e using Sum.casesOn with
  | inl e => exact Quiver.Hom.toPos (rawBassSerreEdgeAction G g e)
  | inr e => exact Quiver.Hom.toNeg (rawBassSerreEdgeAction G g e)

/-- Translate every edge and endpoint of a symmetrified Bass-Serre path. -/
def rawBassSerrePathAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g : FreeProduct G) {a : RawBassSerreVertex G} :
    ∀ {b : RawBassSerreVertex G},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _ a b →
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _ (g • a) (g • b)
  | _, .nil => .nil
  | _, .cons p e =>
      .cons (rawBassSerrePathAction G g p)
        (rawBassSerreSymmEdgeAction G g e)

/-- Vertex orbits for the action of the subgroup `H` on the Bass-Serre graph. -/
abbrev RawBassSerreOrbitVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  ActionOrbit H (RawBassSerreVertex G)

/-- Edge orbits for the action of the subgroup `H` on the Bass-Serre graph. -/
abbrev RawBassSerreOrbitEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  ActionOrbit H (rawBassSerreEdgeData G)

/-- The factor vertex in the quotient graph represented by a Kurosh index. -/
def kuroshFactorOrbitVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : KuroshFactorIndex G H) : RawBassSerreOrbitVertex G H :=
  actionOrbitMk H (RawBassSerreVertex G)
    (RawBassSerreVertex.factor q.1
      (factorCosetMk G q.1 (kuroshFactorRepresentative G H q)))

theorem kuroshFactorOrbitVertex_eq_iff {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q r : KuroshFactorIndex G H) :
    kuroshFactorOrbitVertex G H q = kuroshFactorOrbitVertex G H r ↔ q = r := by
  constructor
  · intro h
    cases q with
    | mk i qi =>
        cases r with
        | mk j rj =>
            change actionOrbitMk H (RawBassSerreVertex G)
                (RawBassSerreVertex.factor i
                  (factorCosetMk G i (doubleCosetRepresentative H i qi))) =
              actionOrbitMk H (RawBassSerreVertex G)
                (RawBassSerreVertex.factor j
                  (factorCosetMk G j (doubleCosetRepresentative H j rj))) at h
            rw [actionOrbitMk_eq_iff H (RawBassSerreVertex G)] at h
            rcases h with ⟨a, ha⟩
            change RawBassSerreVertex.factor i
                (a.1 • factorCosetMk G i
                  (doubleCosetRepresentative H i qi)) =
              RawBassSerreVertex.factor j
                (factorCosetMk G j (doubleCosetRepresentative H j rj)) at ha
            have hij : i = j := by
              injection ha
            subst j
            have hcos : a.1 • factorCosetMk G i
                  (doubleCosetRepresentative H i qi) =
                factorCosetMk G i (doubleCosetRepresentative H i rj) := by
              injection ha
            change rightCosetMk (MonoidHom.range (factorInclusion G i))
                (a.1 * doubleCosetRepresentative H i qi) =
              rightCosetMk (MonoidHom.range (factorInclusion G i))
                (doubleCosetRepresentative H i rj) at hcos
            rw [rightCosetMk_eq_iff] at hcos
            rcases hcos with ⟨b, hb⟩
            have hdouble :
                DoubleCoset.mk H (MonoidHom.range (factorInclusion G i))
                    (doubleCosetRepresentative H i qi) =
                  DoubleCoset.mk H (MonoidHom.range (factorInclusion G i))
                    (doubleCosetRepresentative H i rj) :=
              (doubleCosetIndex_eq_iff H i
                (doubleCosetRepresentative H i qi)
                (doubleCosetRepresentative H i rj)).2
                ⟨a.1, a.property, b.1, b.property, hb.symm⟩
            exact congrArg (fun z => Sigma.mk i z) (calc
              qi = DoubleCoset.mk H (MonoidHom.range (factorInclusion G i))
                  (doubleCosetRepresentative H i qi) :=
                (DoubleCoset.out_eq' qi).symm
              _ = DoubleCoset.mk H (MonoidHom.range (factorInclusion G i))
                  (doubleCosetRepresentative H i rj) := hdouble
              _ = rj := DoubleCoset.out_eq' rj)
  · intro h
    cases h
    rfl

/-- The source vertex orbit of an edge orbit. -/
def rawBassSerreOrbitEdgeSource {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : RawBassSerreOrbitEdge G H) : RawBassSerreOrbitVertex G H :=
  Quotient.lift (fun x => actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataSource G x))
    (by
      intro x y hxy
      rcases hxy with ⟨a, hxy⟩
      change (a.1 : FreeProduct G) • y = x at hxy
      rw [← hxy, rawBassSerreEdgeData_source_action]
      exact actionOrbitMk_smul H (RawBassSerreVertex G) a
        (rawBassSerreEdgeDataSource G y)) e

/-- The target vertex orbit of an edge orbit. -/
def rawBassSerreOrbitEdgeTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : RawBassSerreOrbitEdge G H) : RawBassSerreOrbitVertex G H :=
  Quotient.lift (fun x => actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataTarget G x))
    (by
      intro x y hxy
      rcases hxy with ⟨a, hxy⟩
      change (a.1 : FreeProduct G) • y = x at hxy
      rw [← hxy, rawBassSerreEdgeData_target_action]
      exact actionOrbitMk_smul H (RawBassSerreVertex G) a
        (rawBassSerreEdgeDataTarget G y)) e

/-- The quotient quiver whose edges are subgroup orbits with prescribed endpoints. -/
@[expose, reducible]
def rawBassSerreOrbitQuiver {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver (RawBassSerreOrbitVertex G H) where
  Hom a b := {e : RawBassSerreOrbitEdge G H //
    rawBassSerreOrbitEdgeSource G H e = a ∧
      rawBassSerreOrbitEdgeTarget G H e = b}

instance rawBassSerreOrbitQuiver.inst {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver (RawBassSerreOrbitVertex G H) := rawBassSerreOrbitQuiver G H

/-- The subgroup orbit of an unbundled Bass-Serre edge. -/
@[expose] def rawBassSerreOrbitEdgeMk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : rawBassSerreEdgeData G) : RawBassSerreOrbitEdge G H :=
  actionOrbitMk H (rawBassSerreEdgeData G) e

/-- Bundle an edge orbit with its source and target vertex orbits. -/
@[expose] def rawBassSerreOrbitQuiverEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : rawBassSerreEdgeData G) :
    rawBassSerreOrbitEdgeSource G H (rawBassSerreOrbitEdgeMk G H e) ⟶
      rawBassSerreOrbitEdgeTarget G H (rawBassSerreOrbitEdgeMk G H e) :=
  ⟨rawBassSerreOrbitEdgeMk G H e, rfl, rfl⟩

theorem rawBassSerreOrbitEdgeSource_mk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : rawBassSerreEdgeData G) :
    rawBassSerreOrbitEdgeSource G H (rawBassSerreOrbitEdgeMk G H e) =
      actionOrbitMk H (RawBassSerreVertex G) (rawBassSerreEdgeDataSource G e) := by
  simp [rawBassSerreOrbitEdgeSource, rawBassSerreOrbitEdgeMk,
    actionOrbitMk]

theorem rawBassSerreOrbitEdgeTarget_mk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : rawBassSerreEdgeData G) :
    rawBassSerreOrbitEdgeTarget G H (rawBassSerreOrbitEdgeMk G H e) =
      actionOrbitMk H (RawBassSerreVertex G) (rawBassSerreEdgeDataTarget G e) := by
  simp [rawBassSerreOrbitEdgeTarget, rawBassSerreOrbitEdgeMk,
    actionOrbitMk]

/-- Project a Bass-Serre edge to the quotient quiver. -/
def rawBassSerreOrbitEdgeMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G} (e : a ⟶ b) :
    actionOrbitMk H (RawBassSerreVertex G) a ⟶
      actionOrbitMk H (RawBassSerreVertex G) b := by
  cases e using RawBassSerreEdge.casesOn with
  | centralFactor g i =>
      exact rawBassSerreOrbitQuiverEdge G H (g, i)

/-- The projection from the Bass-Serre quiver to its subgroup-orbit quiver. -/
def rawBassSerreOrbitPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreVertex G ⥤q RawBassSerreOrbitVertex G H where
  obj := actionOrbitMk H (RawBassSerreVertex G)
  map := rawBassSerreOrbitEdgeMap G H

/-- The orbit projection with values in the symmetrified quotient quiver. -/
def rawBassSerreOrbitPrefunctorToSymm {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreVertex G ⥤q Quiver.Symmetrify (RawBassSerreOrbitVertex G H) where
  obj := actionOrbitMk H (RawBassSerreVertex G)
  map e := Quiver.Hom.toPos (rawBassSerreOrbitEdgeMap G H e)

/-- Extend the orbit projection to both edge orientations. -/
def rawBassSerreOrbitSymmPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.Symmetrify (RawBassSerreVertex G) ⥤q
      Quiver.Symmetrify (RawBassSerreOrbitVertex G H) :=
  Quiver.Symmetrify.lift (rawBassSerreOrbitPrefunctorToSymm G H)

theorem rawBassSerreOrbitQuiver_rootedConnected {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.RootedConnected
      (show Quiver.Symmetrify (RawBassSerreOrbitVertex G H) from
        actionOrbitMk H (RawBassSerreVertex G) (RawBassSerreVertex.central 1)) := by
  constructor
  intro b
  induction b using Quotient.inductionOn' with
  | _ x =>
      cases x with
      | central g =>
          rcases rawBassSerreWord_path G g with ⟨p⟩
          simpa [rawBassSerreOrbitSymmPrefunctor,
            rawBassSerreOrbitPrefunctorToSymm, actionOrbitMk] using
            ⟨(rawBassSerreOrbitSymmPrefunctor G H).mapPath p⟩
      | factor i c =>
          rcases rawBassSerreFactor_path G i c with ⟨p⟩
          simpa [rawBassSerreOrbitSymmPrefunctor,
            rawBassSerreOrbitPrefunctorToSymm, actionOrbitMk] using
            ⟨(rawBassSerreOrbitSymmPrefunctor G H).mapPath p⟩

/-- A geodesic spanning tree of the symmetrified quotient graph. -/
@[expose] noncomputable def rawBassSerreOrbitTree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    WideSubquiver (Quiver.Symmetrify (RawBassSerreOrbitVertex G H)) :=
  @Quiver.geodesicSubtree (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
    (Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H))
    (actionOrbitMk H (RawBassSerreVertex G) (RawBassSerreVertex.central 1))
    (rawBassSerreOrbitQuiver_rootedConnected G H)

noncomputable instance rawBassSerreOrbitTreeArborescence {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.Arborescence (rawBassSerreOrbitTree G H) :=
  @Quiver.geodesicArborescence (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
    (Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H))
    (actionOrbitMk H (RawBassSerreVertex G) (RawBassSerreVertex.central 1))
    (rawBassSerreOrbitQuiver_rootedConnected G H)

/-- The unique path from the chosen root to a vertex of the quotient spanning tree. -/
@[instance_reducible] noncomputable def rawTreeUniquePath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (b : rawBassSerreOrbitTree G H) :
    Unique (@Quiver.Path (rawBassSerreOrbitTree G H)
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
      (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H)) b) :=
  @Quiver.Arborescence.uniquePath _ _ (rawBassSerreOrbitTreeArborescence G H) b

/- The distinguished quotient vertex corresponding to the identity of the subgroup. -/
/-- The subgroup orbit of the central vertex represented by the identity. -/
@[expose] def rawBassSerreOrbitRoot {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreOrbitVertex G H :=
  actionOrbitMk H (RawBassSerreVertex G) (RawBassSerreVertex.central 1)

/-- Choose an element of `H` carrying one representative of an orbit to another. -/
noncomputable def rawOrbitAlign {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y : RawBassSerreVertex G}
    (h : actionOrbitMk H (RawBassSerreVertex G) x =
      actionOrbitMk H (RawBassSerreVertex G) y) : H :=
  Classical.choose ((actionOrbitMk_eq_iff H (RawBassSerreVertex G) x y).1 h)

theorem rawOrbitAlign_spec {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y : RawBassSerreVertex G}
    (h : actionOrbitMk H (RawBassSerreVertex G) x =
      actionOrbitMk H (RawBassSerreVertex G) y) :
    (rawOrbitAlign G H h).1 • x = y :=
  Classical.choose_spec ((actionOrbitMk_eq_iff H (RawBassSerreVertex G) x y).1 h)

/-- The prefunctor forgetting membership in a wide subquiver. -/
@[expose] def wideSubquiverInclusion {V : Type u} [Quiver.{v} V]
    (W : WideSubquiver V) : W ⥤q V where
  obj := id
  map e := e.1

/-- Include the quotient spanning tree into the symmetrified quotient graph. -/
def rawTreeInclusion {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    rawBassSerreOrbitTree G H ⥤q
      Quiver.Symmetrify (RawBassSerreOrbitVertex G H) where
  obj := fun x => (show RawBassSerreOrbitVertex G H from x)
  map e := e.1

/-- Forget a quotient-tree edge's membership proof. -/
def rawTreeEdgeMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (e : @Quiver.Hom (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) a b) :
    @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (show RawBassSerreOrbitVertex G H from a)
      (show RawBassSerreOrbitVertex G H from b) :=
  (rawTreeInclusion G H).map e

/-- The quotient spanning tree expressed as a quiver on the ambient vertex type. -/
@[expose, reducible] def rawTreeQuiver {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver (RawBassSerreOrbitVertex G H) :=
  { Hom := fun a b =>
      { e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) a b //
        e ∈ rawBassSerreOrbitTree G H a b } }

noncomputable instance rawTreeQuiverArborescence {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @Quiver.Arborescence (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) := by
  change Quiver.Arborescence (rawBassSerreOrbitTree G H)
  exact rawBassSerreOrbitTreeArborescence G H

/-- Forget tree-membership proofs along a path in the quotient spanning tree. -/
@[expose] def rawTreePathMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ {a b : RawBassSerreOrbitVertex G H},
      @Quiver.Path (RawBassSerreOrbitVertex G H) (rawTreeQuiver G H) a b →
        @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) a b
  | _, _, @Quiver.Path.nil (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) _ =>
      (@Quiver.Path.nil (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _)
  | _, _, @Quiver.Path.cons (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) _ _ _ p e =>
      Quiver.Path.cons (rawTreePathMap G H p) e.1

/-- The root of the quotient spanning tree on the ambient vertex type. -/
@[expose] def rawTreeQuiverRoot {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreOrbitVertex G H :=
  @Quiver.Arborescence.root (RawBassSerreOrbitVertex G H)
    (rawTreeQuiver G H) (rawTreeQuiverArborescence G H)

theorem rawTreeQuiverRoot_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    rawTreeQuiverRoot G H = rawBassSerreOrbitRoot G H := by
  rfl

/-- The unique rooted tree path to a quotient vertex. -/
noncomputable def rawTreePath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    @Quiver.Path (RawBassSerreOrbitVertex G H) (rawTreeQuiver G H)
      (rawTreeQuiverRoot G H) a := by
  letI : Quiver (RawBassSerreOrbitVertex G H) := rawTreeQuiver G H
  letI : Quiver.Arborescence (RawBassSerreOrbitVertex G H) :=
    rawTreeQuiverArborescence G H
  letI : Unique (@Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawTreeQuiverRoot G H) a) :=
    @Quiver.Arborescence.uniquePath (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawTreeQuiverArborescence G H) a
  exact default

theorem rawTreePathMap_cons_raw {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) a b)
    (e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) b c) :
    rawTreePathMap G H
        (@Quiver.Path.cons (RawBassSerreOrbitVertex G H)
          (rawTreeQuiver G H) _ _ _ p e) =
      (@Quiver.Path.cons (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _
        (rawTreePathMap G H p)
        (show @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ from e.1)) := by
  simp [rawTreePathMap]

/-- Choose a representative of a path endpoint by successively lifting quotient edges. -/
@[expose] noncomputable def rawTreeLiftPath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {b : RawBassSerreOrbitVertex G H} :
    ∀ _p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H)) _
        (rawBassSerreOrbitRoot G H) b,
      {x : RawBassSerreVertex G //
        actionOrbitMk H (RawBassSerreVertex G) x = b}
  | Quiver.Path.nil =>
      ⟨RawBassSerreVertex.central 1, rfl⟩
  | @Quiver.Path.cons _ _ _ b c p e => by
      let x := rawTreeLiftPath G H p
      cases e using Sum.casesOn with
      | inl qe =>
          let d : rawBassSerreEdgeData G := Quotient.out qe.1
          have hsource : actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataSource G d) =
                actionOrbitMk H (RawBassSerreVertex G) x.1 := by
            have hd : actionOrbitMk H (rawBassSerreEdgeData G) d = qe.1 := by
              simp [d, actionOrbitMk]
            have hq : rawBassSerreOrbitEdgeSource G H
                (rawBassSerreOrbitEdgeMk G H d) =
                  (show RawBassSerreOrbitVertex G H from b) := by
              change rawBassSerreOrbitEdgeSource G H
                (actionOrbitMk H (rawBassSerreEdgeData G) d) = _
              rw [hd]
              exact qe.property.1
            rw [x.property]
            exact (rawBassSerreOrbitEdgeSource_mk G H d).symm.trans hq
          have halign : actionOrbitMk H (RawBassSerreVertex G)
                (rawBassSerreEdgeDataSource G d) =
              actionOrbitMk H (RawBassSerreVertex G) x.1 := hsource
          let a : H := rawOrbitAlign G H halign
          refine ⟨a • rawBassSerreEdgeDataTarget G d, ?_⟩
          rw [actionOrbitMk_smul H (RawBassSerreVertex G) a]
          have htarget : actionOrbitMk H (RawBassSerreVertex G)
                (rawBassSerreEdgeDataTarget G d) =
                  (show RawBassSerreOrbitVertex G H from c) := by
            have hd : actionOrbitMk H (rawBassSerreEdgeData G) d = qe.1 := by
              simp [d, actionOrbitMk]
            have hq : rawBassSerreOrbitEdgeTarget G H
                (rawBassSerreOrbitEdgeMk G H d) =
                  (show RawBassSerreOrbitVertex G H from c) := by
              change rawBassSerreOrbitEdgeTarget G H
                (actionOrbitMk H (rawBassSerreEdgeData G) d) = _
              rw [hd]
              exact qe.property.2
            exact (rawBassSerreOrbitEdgeTarget_mk G H d).symm.trans hq
          exact htarget
      | inr qe =>
          let d : rawBassSerreEdgeData G := Quotient.out qe.1
          have htarget : actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataTarget G d) =
                actionOrbitMk H (RawBassSerreVertex G) x.1 := by
            have hd : actionOrbitMk H (rawBassSerreEdgeData G) d = qe.1 := by
              simp [d, actionOrbitMk]
            have hq : rawBassSerreOrbitEdgeTarget G H
                (rawBassSerreOrbitEdgeMk G H d) =
                  (show RawBassSerreOrbitVertex G H from b) := by
              change rawBassSerreOrbitEdgeTarget G H
                (actionOrbitMk H (rawBassSerreEdgeData G) d) = _
              rw [hd]
              exact qe.property.2
            rw [x.property]
            exact (rawBassSerreOrbitEdgeTarget_mk G H d).symm.trans hq
          have halign : actionOrbitMk H (RawBassSerreVertex G)
                (rawBassSerreEdgeDataTarget G d) =
              actionOrbitMk H (RawBassSerreVertex G) x.1 := htarget
          let a : H := rawOrbitAlign G H halign
          refine ⟨a • rawBassSerreEdgeDataSource G d, ?_⟩
          rw [actionOrbitMk_smul H (RawBassSerreVertex G) a]
          have hsource : actionOrbitMk H (RawBassSerreVertex G)
                (rawBassSerreEdgeDataSource G d) =
                  (show RawBassSerreOrbitVertex G H from c) := by
            have hd : actionOrbitMk H (rawBassSerreEdgeData G) d = qe.1 := by
              simp [d, actionOrbitMk]
            have hq : rawBassSerreOrbitEdgeSource G H
                (rawBassSerreOrbitEdgeMk G H d) =
                  (show RawBassSerreOrbitVertex G H from c) := by
              change rawBassSerreOrbitEdgeSource G H
                (actionOrbitMk H (rawBassSerreEdgeData G) d) = _
              rw [hd]
              exact qe.property.1
            exact (rawBassSerreOrbitEdgeSource_mk G H d).symm.trans hq
          exact hsource

/-- The orbit representative obtained by lifting the chosen rooted tree path. -/
@[expose] noncomputable def rawTreeRepresentative {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (b : RawBassSerreOrbitVertex G H) : RawBassSerreVertex G :=
  (rawTreeLiftPath G H
    ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath
      ((rawTreeUniquePath G H b).default))).1

theorem rawTreeRepresentative_orbit {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (b : RawBassSerreOrbitVertex G H) :
    actionOrbitMk H (RawBassSerreVertex G) (rawTreeRepresentative G H b) = b := by
  exact (rawTreeLiftPath G H
    ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath
      ((rawTreeUniquePath G H b).default))).property

/-- Choose an unbundled representative of an edge in the quotient graph. -/
@[expose] noncomputable def quotientEdgeRawData {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) : rawBassSerreEdgeData G :=
  Quotient.out e.1

theorem quotientEdgeRawData_mk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    rawBassSerreOrbitEdgeMk G H (quotientEdgeRawData G H e) = e.1 := by
  simp [quotientEdgeRawData, rawBassSerreOrbitEdgeMk, actionOrbitMk]
theorem quotientEdgeSource_orbit {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataSource G (quotientEdgeRawData G H e)) = a := by
  have he : rawBassSerreOrbitEdgeSource G H
      (rawBassSerreOrbitEdgeMk G H (quotientEdgeRawData G H e)) = a := by
    rw [quotientEdgeRawData_mk G H e]
    exact e.property.1
  exact (rawBassSerreOrbitEdgeSource_mk G H
    (quotientEdgeRawData G H e)).symm.trans he

theorem quotientEdgeTarget_orbit {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H e)) = b := by
  have he : rawBassSerreOrbitEdgeTarget G H
      (rawBassSerreOrbitEdgeMk G H (quotientEdgeRawData G H e)) = b := by
    rw [quotientEdgeRawData_mk G H e]
    exact e.property.2
  exact (rawBassSerreOrbitEdgeTarget_mk G H
    (quotientEdgeRawData G H e)).symm.trans he

/-- Align an edge representative's source with the chosen orbit representative. -/
noncomputable def quotientEdgeSourceAlign {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) : H :=
  rawOrbitAlign G H ((quotientEdgeSource_orbit G H e).trans
    (rawTreeRepresentative_orbit G H a).symm)

theorem quotientEdgeSourceAlign_spec {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    (quotientEdgeSourceAlign G H e).1 •
        rawBassSerreEdgeDataSource G (quotientEdgeRawData G H e) =
      rawTreeRepresentative G H a :=
  rawOrbitAlign_spec G H _

/-- The target after translating an edge to align its source. -/
noncomputable def quotientEdgeAlignedTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) : RawBassSerreVertex G :=
  (quotientEdgeSourceAlign G H e).1 •
    rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H e)

theorem quotientEdgeAlignedTarget_orbit {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    actionOrbitMk H (RawBassSerreVertex G)
        (quotientEdgeAlignedTarget G H e) = b := by
  change actionOrbitMk H (RawBassSerreVertex G)
      ((quotientEdgeSourceAlign G H e) •
        rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H e)) = b
  rw [actionOrbitMk_smul H (RawBassSerreVertex G)
    (quotientEdgeSourceAlign G H e)]
  exact quotientEdgeTarget_orbit G H e

theorem rawTreeRepresentative_of_tree_edge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toPos e ∈ rawBassSerreOrbitTree G H a b) :
    rawTreeRepresentative G H b = quotientEdgeAlignedTarget G H e := by
  let te : @Quiver.Hom (rawBassSerreOrbitTree G H) _ a b :=
    ⟨Quiver.Hom.toPos e, he⟩
  have hp :
      ((rawTreeUniquePath G H b).default) =
        ((rawTreeUniquePath G H a).default).cons te := by
    exact ((rawTreeUniquePath G H b).uniq _).symm
  have hlift := congrArg
    (fun p : @Quiver.Path (rawBassSerreOrbitTree G H) (WideSubquiver.quiver
      (rawBassSerreOrbitTree G H)) (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H)) b =>
      (rawTreeLiftPath G H
        ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath p)).1) hp
  calc
    rawTreeRepresentative G H b =
        (rawTreeLiftPath G H
          ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath
            (((rawTreeUniquePath G H a).default).cons te))).1 := by
      exact hlift
    _ = quotientEdgeAlignedTarget G H e := by
      rfl

/-- Align the source-adjusted target with its chosen orbit representative. -/
noncomputable def quotientEdgeTargetAlign {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) : H :=
  rawOrbitAlign G H ((quotientEdgeAlignedTarget_orbit G H e).trans
    (rawTreeRepresentative_orbit G H b).symm)

theorem quotientEdgeTargetAlign_spec {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    (quotientEdgeTargetAlign G H e).1 • quotientEdgeAlignedTarget G H e =
      rawTreeRepresentative G H b :=
  rawOrbitAlign_spec G H _

/-- Align the raw target directly with its chosen orbit representative. -/
noncomputable def quotientEdgeDirectTargetAlign {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) : H :=
  rawOrbitAlign G H ((quotientEdgeTarget_orbit G H e).trans
    (rawTreeRepresentative_orbit G H b).symm)

theorem quotientEdgeDirectTargetAlign_spec {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    (quotientEdgeDirectTargetAlign G H e).1 •
        rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H e) =
      rawTreeRepresentative G H b :=
  rawOrbitAlign_spec G H _

theorem rawTreeRepresentative_of_tree_edge_neg {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a) :
    rawTreeRepresentative G H a =
      (quotientEdgeDirectTargetAlign G H e).1 •
        rawBassSerreEdgeDataSource G (quotientEdgeRawData G H e) := by
  let te : @Quiver.Hom (rawBassSerreOrbitTree G H) _ b a :=
    ⟨Quiver.Hom.toNeg e, he⟩
  have hp :
      ((rawTreeUniquePath G H a).default) =
        ((rawTreeUniquePath G H b).default).cons te := by
    exact ((rawTreeUniquePath G H a).uniq _).symm
  have hlift := congrArg
    (fun p : @Quiver.Path (rawBassSerreOrbitTree G H) (WideSubquiver.quiver
      (rawBassSerreOrbitTree G H)) (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H)) a =>
      (rawTreeLiftPath G H
        ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath p)).1) hp
  calc
    rawTreeRepresentative G H a =
        (rawTreeLiftPath G H
          ((wideSubquiverInclusion (rawBassSerreOrbitTree G H)).mapPath
            (((rawTreeUniquePath G H b).default).cons te))).1 := by
      exact hlift
    _ = (quotientEdgeDirectTargetAlign G H e).1 •
        rawBassSerreEdgeDataSource G (quotientEdgeRawData G H e) := by
      rfl

/-- The subgroup label of a quotient edge, normalized to the identity on tree edges. -/
noncomputable def quotientEdgeLabel {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) : H :=
  by
    classical
    exact if he : Quiver.Hom.toPos e ∈ rawBassSerreOrbitTree G H a b then
      1
    else if he' : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a then
      1
    else
      quotientEdgeTargetAlign G H e

/-- Choose a source alignment compatible with the normalized edge label. -/
noncomputable def quotientEdgeCoherentSourceAlign {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) : H := by
  classical
  exact if he : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a then
      quotientEdgeDirectTargetAlign G H e
    else
      quotientEdgeSourceAlign G H e

theorem quotientEdgeCoherentSourceAlign_spec {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    (quotientEdgeCoherentSourceAlign G H e).1 •
        rawBassSerreEdgeDataSource G (quotientEdgeRawData G H e) =
      rawTreeRepresentative G H a := by
  by_cases he : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a
  · rw [quotientEdgeCoherentSourceAlign, dite_eq_left he]
    exact (rawTreeRepresentative_of_tree_edge_neg G H e he).symm
  · rw [quotientEdgeCoherentSourceAlign, dite_eq_right he]
    exact quotientEdgeSourceAlign_spec G H e

theorem quotientEdgeLabel_transport_coherent {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    (quotientEdgeLabel G H e).1 •
        ((quotientEdgeCoherentSourceAlign G H e).1 •
          rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H e)) =
      rawTreeRepresentative G H b := by
  by_cases he : Quiver.Hom.toPos e ∈ rawBassSerreOrbitTree G H a b
  · rw [quotientEdgeLabel, dite_eq_left he, smul_smul]
    simp only [Subgroup.coe_one, one_mul]
    by_cases he' : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a
    · rw [quotientEdgeCoherentSourceAlign, dite_eq_left he']
      exact quotientEdgeDirectTargetAlign_spec G H e
    · rw [quotientEdgeCoherentSourceAlign, dite_eq_right he']
      exact (rawTreeRepresentative_of_tree_edge G H e he).symm
  · by_cases he' : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a
    · rw [quotientEdgeLabel, dite_eq_right he, dite_eq_left he', smul_smul]
      simp only [Subgroup.coe_one, one_mul]
      rw [quotientEdgeCoherentSourceAlign, dite_eq_left he']
      exact quotientEdgeDirectTargetAlign_spec G H e
    · rw [quotientEdgeLabel, dite_eq_right he, dite_eq_right he']
      rw [quotientEdgeCoherentSourceAlign, dite_eq_right he']
      exact quotientEdgeTargetAlign_spec G H e

/-- Label quotient edges by subgroup elements in the one-object groupoid. -/
def quotientGraphLabelPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreOrbitVertex G H ⥤q CategoryTheory.SingleObj H where
  obj := fun _ => ()
  map := fun e => quotientEdgeLabel G H e

/-- Interpret a symmetric quiver path as a morphism in its free groupoid. -/
def freeGroupoidPathHom {V : Type u} [q : Quiver.{v} V] {a : V} :
    ∀ {b : V},
      @Quiver.Path (Quiver.Symmetrify V) _ a b →
        @Quiver.Hom (Quiver.FreeGroupoid V)
          _
          ((Quiver.FreeGroupoid.of V).obj a)
          ((Quiver.FreeGroupoid.of V).obj b)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e =>
      freeGroupoidPathHom p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of V).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of V).map f))

private theorem freeGroupoidPathHom_nil {V : Type u} [q : Quiver.{v} V]
    {a : V} :
    @freeGroupoidPathHom V q a a
        (Quiver.Path.nil :
          @Quiver.Path (Quiver.Symmetrify V)
            (@Quiver.symmetrifyQuiver V q) a a) = 𝟙 _ := by
  unfold freeGroupoidPathHom
  rfl

theorem freeGroupoidPathHom_nil_public {V : Type u} [q : Quiver.{v} V]
    {a : V} :
    @freeGroupoidPathHom V q a a
        (Quiver.Path.nil :
          @Quiver.Path (Quiver.Symmetrify V)
            (@Quiver.symmetrifyQuiver V q) a a) = 𝟙 _ := by
  exact freeGroupoidPathHom_nil

private theorem freeGroupoidPathHom_cons {V : Type u} [q : Quiver.{v} V]
    {a b c : V}
    (p : @Quiver.Path (Quiver.Symmetrify V)
      (@Quiver.symmetrifyQuiver V q) a b)
    (e : @Quiver.Hom (Quiver.Symmetrify V)
      (@Quiver.symmetrifyQuiver V q) b c) :
    @freeGroupoidPathHom V q a c (p.cons e) =
      @freeGroupoidPathHom V q a b p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of V).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of V).map f)) := by
  cases p with
  | nil =>
      cases e using Sum.casesOn <;> simp [freeGroupoidPathHom]
  | cons p e' =>
      cases e using Sum.casesOn <;> cases e' using Sum.casesOn <;> simp [freeGroupoidPathHom,
        Category.assoc]

private theorem freeGroupoid_isConnected_of_rootedConnected
    {V : Type u} [q : Quiver.{v} V] (r : V)
    [Quiver.RootedConnected (show Quiver.Symmetrify V from r)] :
    IsConnected (Quiver.FreeGroupoid V) := by
  let : Nonempty (Quiver.FreeGroupoid V) :=
    ⟨(Quiver.FreeGroupoid.of V).obj r⟩
  apply zigzag_isConnected
  intro a b
  have ha : Nonempty (@Quiver.Path (Quiver.Symmetrify V) _ r a.as) :=
    @Quiver.RootedConnected.nonempty_path (Quiver.Symmetrify V)
      (Quiver.symmetrifyQuiver V) r _ a.as
  have hb : Nonempty (@Quiver.Path (Quiver.Symmetrify V) _ r b.as) :=
    @Quiver.RootedConnected.nonempty_path (Quiver.Symmetrify V)
      (Quiver.symmetrifyQuiver V) r _ b.as
  rcases ha with ⟨pa⟩
  rcases hb with ⟨pb⟩
  exact Zigzag.of_inv_hom (freeGroupoidPathHom pa) (freeGroupoidPathHom pb)

/-- Recover the original vertex from an object of the free groupoid. -/
def freeGroupoidBaseObj {V : Type u} [q : Quiver.{v} V]
    (a : Quiver.FreeGroupoid V) : V := by
  exact a.as

/-- The quiver underlying the category structure of the free groupoid. -/
@[instance_reducible] def freeGroupoidCategoryQuiver {V : Type u} [q : Quiver.{v} V] :
    Quiver (Quiver.FreeGroupoid V) := by
  letI : CategoryTheory.Category (Quiver.FreeGroupoid V) :=
    Quiver.FreeGroupoid.instCategory
  infer_instance

/-- Original quiver arrows, lifted to the universe of free groupoid morphisms. -/
@[instance_reducible] def freeGroupoidGeneratorQuiver {V : Type u} [q : Quiver.{v} V] :
    Quiver.{max u v} (Quiver.FreeGroupoid V) :=
  { Hom := fun a b => ULift.{u}
      (@Quiver.Hom V q (freeGroupoidBaseObj a) (freeGroupoidBaseObj b)) }

/-- Include a lifted generating arrow into the free groupoid. -/
def freeGroupoidGeneratorArrow {V : Type u} [q : Quiver.{v} V]
    {a b : Quiver.FreeGroupoid V}
    (e : ULift.{u}
      (@Quiver.Hom V q (freeGroupoidBaseObj a) (freeGroupoidBaseObj b))) :
    @Quiver.Hom (Quiver.FreeGroupoid V) (freeGroupoidCategoryQuiver (V := V)) a b := by
  cases a with
  | mk a =>
      cases b with
      | mk b =>
          exact (Quiver.FreeGroupoid.of V).map e.down

private theorem freeGroupoidGeneratorArrow_up {V : Type u} [q : Quiver.{v} V]
    {a b : V} (e : a ⟶ b) :
    freeGroupoidGeneratorArrow (ULift.up e) =
      (Quiver.FreeGroupoid.of V).map e := by
  rfl

instance freeGroupoidIsFreeGroupoid {V : Type u} [q : Quiver.{v} V] :
    IsFreeGroupoid (Quiver.FreeGroupoid V) where
  quiverGenerators := freeGroupoidGeneratorQuiver (V := V)
  of := freeGroupoidGeneratorArrow
  unique_lift := by
    intro X _ f
    change ∀ ⦃a b : Quiver.FreeGroupoid V⦄,
      ULift.{u} (@Quiver.Hom V q (freeGroupoidBaseObj a)
        (freeGroupoidBaseObj b)) → X at f
    let φ : V ⥤q CategoryTheory.SingleObj X :=
      { obj := fun _ => ()
        map := fun {a b} e => f (ULift.up e) }
    refine ⟨Quiver.FreeGroupoid.lift φ, ?_, ?_⟩
    · intro a b e
      cases a with
      | mk a =>
          cases b with
          | mk b =>
              change (Quiver.FreeGroupoid.lift φ).map
                (freeGroupoidGeneratorArrow e) = f e
              change (Quiver.FreeGroupoid.lift φ).map
                ((Quiver.FreeGroupoid.of V).map e.down) = f e
              change (Quiver.FreeGroupoid.of V ⋙q
                (Quiver.FreeGroupoid.lift φ).toPrefunctor).map e.down = f e
              rw [Quiver.FreeGroupoid.lift_spec]
              rfl
    · intro F hF
      apply Quiver.FreeGroupoid.lift_unique φ F
      refine Prefunctor.ext
        (F := Quiver.FreeGroupoid.of V ⋙q F.toPrefunctor) (G := φ)
        (fun _ => Subsingleton.elim _ _) ?_
      intro a b e
      convert hF _ _ (ULift.up e) using 1
      exact (congrArg (fun z => F.map z) (freeGroupoidGeneratorArrow_up e)).symm

/-- The free group contributed by loops in the quotient Bass--Serre graph. -/
abbrev KuroshFreePart {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  End ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj
    (rawBassSerreOrbitRoot G H))

/-- Evaluate loops in the quotient graph as elements of the subgroup `H`. -/
noncomputable def kuroshFreePartHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshFreePart G H →* H :=
  (SingleObj.toEnd H).symm.toMonoidHom.comp
    ((Quiver.FreeGroupoid.lift (quotientGraphLabelPrefunctor G H)).mapEnd
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj
        (rawBassSerreOrbitRoot G H)))

/-- The chosen tree path as a morphism in the quotient graph's free groupoid. -/
noncomputable def quotientTreePathHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj
        (rawBassSerreOrbitRoot G H) ⟶
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a :=
  by
    have hroot := rawTreeQuiverRoot_eq G H
    cases hroot
    exact @freeGroupoidPathHom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H)
      (rawBassSerreOrbitRoot G H) a
      (rawTreePathMap G H (rawTreePath G H a))

/-- Close a quotient edge to a based loop using the chosen tree paths. -/
noncomputable def quotientEdgeLoop {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    KuroshFreePart G H :=
  quotientTreePathHom G H a ≫
    (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e ≫
      Groupoid.inv (quotientTreePathHom G H b)

/-- Evaluate a morphism of the quotient free groupoid using subgroup edge labels. -/
noncomputable def quotientPathValue {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a ⟶
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b) : H :=
  (Quiver.FreeGroupoid.lift (quotientGraphLabelPrefunctor G H)).map p

/-- The subgroup label of an oriented quotient edge, inverted for reverse edges. -/
noncomputable def quotientSymmEdgeLabel {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) : H :=
  match e with
  | Sum.inl f => quotientEdgeLabel G H f
  | Sum.inr f => (quotientEdgeLabel G H f)⁻¹

/-- Multiply the labels along a symmetrified quotient path. -/
noncomputable def quotientRawPathValue {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) : H :=
  quotientPathValue G H
    (@freeGroupoidPathHom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b p)

theorem quotientPathValue_of {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : a ⟶ b) :
    quotientPathValue G H
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e) =
      quotientEdgeLabel G H e := by
  have hs := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (quotientGraphLabelPrefunctor G H)) e
  exact hs

theorem quotientPathValue_comp {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (p : (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a ⟶
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b)
    (q : (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b ⟶
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj c) :
    quotientPathValue G H (p ≫ q) =
      quotientPathValue G H q * quotientPathValue G H p := by
  unfold quotientPathValue
  rw [Functor.map_comp, SingleObj.comp_as_mul]

theorem quotientPathValue_inv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a ⟶
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b) :
    quotientPathValue G H (Groupoid.inv p) =
      (quotientPathValue G H p)⁻¹ := by
  simp only [quotientPathValue, Groupoid.inv_eq_inv, Functor.map_inv,
    SingleObj.inv_as_inv]

theorem quotientRawPathValue_nil {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    quotientRawPathValue G H
      (@Quiver.Path.nil (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a) = 1 := by
  simp [quotientRawPathValue, quotientPathValue, freeGroupoidPathHom,
    SingleObj.id_as_one]

theorem quotientRawPathValue_cons {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) b c) :
    quotientRawPathValue G H (p.cons e) =
      quotientSymmEdgeLabel G H e * quotientRawPathValue G H p := by
  cases e using Sum.casesOn with
  | inl e =>
      rw [quotientRawPathValue, freeGroupoidPathHom_cons,
        quotientPathValue_comp, quotientPathValue_of]
      rfl
  | inr e =>
      rw [quotientRawPathValue, freeGroupoidPathHom_cons,
        quotientPathValue_comp, quotientPathValue_inv,
        quotientPathValue_of]
      rfl

theorem quotientGraphFunctor_map_pos {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    (SingleObj.toEnd H).symm
        ((Quiver.FreeGroupoid.lift (quotientGraphLabelPrefunctor G H)).map
          ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e)) =
      quotientEdgeLabel G H e := by
  have hs := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (quotientGraphLabelPrefunctor G H)) e
  exact congrArg (fun z => (SingleObj.toEnd H).symm z) hs

theorem rawBassSerreOrbitTree_root_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (Quiver.root (rawBassSerreOrbitTree G H) : RawBassSerreOrbitVertex G H) =
      rawBassSerreOrbitRoot G H := by
  rfl

/-- The root of the quotient spanning tree as an ambient quotient vertex. -/
def rawBassSerreOrbitTreeRootVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreOrbitVertex G H :=
  Quiver.root (rawBassSerreOrbitTree G H)

/-- Map a tree path to the symmetrified quotient graph without bundled tree vertices. -/
def rawTreeInclusionMapPathAsRaw {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (p : @Quiver.Path (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) a b) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (show RawBassSerreOrbitVertex G H from a)
      (show RawBassSerreOrbitVertex G H from b) := by
  exact (rawTreeInclusion G H).mapPath p

@[simp] theorem rawTreeInclusion_mapPath_asRaw_nil {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)} :
    rawTreeInclusionMapPathAsRaw G H
      (Quiver.Path.nil : @Quiver.Path (WideSubquiver.toType
        (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (rawBassSerreOrbitTree G H))
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) a a) =
      (Quiver.Path.nil : @Quiver.Path (Quiver.Symmetrify
        (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))
        (show RawBassSerreOrbitVertex G H from a)
        (show RawBassSerreOrbitVertex G H from a)) := rfl

@[simp] theorem rawTreeInclusion_mapPath_asRaw_cons {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (p : @Quiver.Path (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) a b)
    (e : @Quiver.Hom (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) b c) :
    rawTreeInclusionMapPathAsRaw G H (p.cons e) =
      (rawTreeInclusionMapPathAsRaw G H p).cons
        ((rawTreeInclusion G H).map e) := rfl

/-- Include a rooted tree path and transport its source to the specified quotient root. -/
def rawTreeRootPath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (p : @Quiver.Path (rawBassSerreOrbitTree G H) (WideSubquiver.quiver (rawBassSerreOrbitTree G
      H)) (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H)) a) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H)
      (show RawBassSerreOrbitVertex G H from a) := by
  have hroot := rawBassSerreOrbitTree_root_eq G H
  cases hroot
  exact rawTreeInclusionMapPathAsRaw G H p

@[simp] theorem rawTreeRootPath_nil {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    rawTreeRootPath G H (Quiver.Path.nil :
      @Quiver.Path (rawBassSerreOrbitTree G H) (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H))
        (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H))) =
      (Quiver.Path.nil : @Quiver.Path (Quiver.Symmetrify
        (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))
        (rawBassSerreOrbitRoot G H) (rawBassSerreOrbitRoot G H)) := by
  rfl

@[simp] theorem rawTreeRootPath_cons {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {b c : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (p : @Quiver.Path (rawBassSerreOrbitTree G H) (WideSubquiver.quiver (rawBassSerreOrbitTree G
      H)) (@Quiver.root (rawBassSerreOrbitTree G H)
        (WideSubquiver.quiver (rawBassSerreOrbitTree G H))
        (rawBassSerreOrbitTreeArborescence G H)) b)
    (e : @Quiver.Hom (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) b c) :
    rawTreeRootPath G H (p.cons e) =
      (rawTreeRootPath G H p).cons (rawTreeEdgeMap G H e) := by
  have hroot := rawBassSerreOrbitTree_root_eq G H
  cases hroot
  rfl

/-- The chosen quotient-tree path with its source transported to the specified root. -/
noncomputable def rawTreePathAtRoot {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    @Quiver.Path (RawBassSerreOrbitVertex G H) (rawTreeQuiver G H)
      (rawBassSerreOrbitRoot G H) a := by
  have hroot := rawTreeQuiverRoot_eq G H
  cases hroot
  exact rawTreePath G H a

theorem rawTreePathAtRoot_eq_rawTreePath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    rawTreePathAtRoot G H a = rawTreePath G H a := by
  have hroot := rawTreeQuiverRoot_eq G H
  cases hroot
  rfl

theorem rawTreePathAtRoot_cons {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) a b)
    (e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) b c) :
    rawTreePathMap G H
        (@Quiver.Path.cons (RawBassSerreOrbitVertex G H)
          (rawTreeQuiver G H) _ _ _ p e) =
      (@Quiver.Path.cons (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _
        (rawTreePathMap G H p)
        (show @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ from e.1)) := by
  exact rawTreePathMap_cons_raw G H p e

theorem quotientTreePathHom_eq_rawTreePathAtRoot {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    quotientTreePathHom G H a =
      @freeGroupoidPathHom (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)
        (rawBassSerreOrbitRoot G H) a
        (rawTreePathMap G H (rawTreePathAtRoot G H a)) := by
  unfold quotientTreePathHom
  rfl

theorem quotientSymmEdgeLabel_tree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b)
    (he : e ∈ rawBassSerreOrbitTree G H a b) :
    quotientSymmEdgeLabel G H e = 1 := by
  cases e using Sum.casesOn with
  | inl e =>
      simp [quotientSymmEdgeLabel, quotientEdgeLabel, he]
  | inr e =>
      simp [quotientSymmEdgeLabel, quotientEdgeLabel, he]

theorem quotientRawPathValue_tree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) a b) :
    quotientRawPathValue G H (rawTreePathMap G H p) = 1 := by
  induction p with
  | nil =>
      simpa [rawTreePathMap] using quotientRawPathValue_nil G H a
  | cons p e ih =>
      rw [rawTreePathMap_cons_raw, quotientRawPathValue_cons, ih,
        quotientSymmEdgeLabel_tree G H e.1 e.2, mul_one]

theorem quotientTreePathValue_one {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    quotientPathValue G H (quotientTreePathHom G H a) = 1 := by
  rw [quotientTreePathHom_eq_rawTreePathAtRoot]
  exact quotientRawPathValue_tree G H (rawTreePathAtRoot G H a)

theorem kuroshFreePartHom_apply {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    kuroshFreePartHom G H x = quotientPathValue G H x := by
  rfl

theorem kuroshFreePartHom_quotientEdgeLoop {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    kuroshFreePartHom G H (quotientEdgeLoop G H e) =
      quotientEdgeLabel G H e := by
  rw [kuroshFreePartHom_apply, quotientEdgeLoop,
    quotientPathValue_comp, quotientPathValue_comp,
    quotientPathValue_inv, quotientTreePathValue_one,
    quotientTreePathValue_one, quotientPathValue_of]
  simp

theorem quotientEdgeLoop_tree_pos {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toPos e ∈ rawBassSerreOrbitTree G H a b) :
    quotientEdgeLoop G H e = 𝟙 _ := by
  let te : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) a b := ⟨Quiver.Hom.toPos e, he⟩
  let : Unique (@Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) b) := by
    have hroot := rawTreeQuiverRoot_eq G H
    cases hroot
    exact @Quiver.Arborescence.uniquePath (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawTreeQuiverArborescence G H) b
  have hp : rawTreePathAtRoot G H b =
      @Quiver.Path.cons (RawBassSerreOrbitVertex G H)
        (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) a b
        (rawTreePathAtRoot G H a) te := by
    exact Subsingleton.elim _ _
  rw [quotientEdgeLoop,
    quotientTreePathHom_eq_rawTreePathAtRoot G H a,
    quotientTreePathHom_eq_rawTreePathAtRoot G H b, hp,
    rawTreePathMap_cons_raw]
  have hpath := @freeGroupoidPathHom_cons
    (RawBassSerreOrbitVertex G H)
    (rawBassSerreOrbitQuiver.inst G H)
    (rawBassSerreOrbitRoot G H) _ _
    (rawTreePathMap G H (rawTreePathAtRoot G H a))
    (Quiver.Hom.toPos e)
  rw [hpath]
  simp

theorem quotientEdgeLoop_tree_neg {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a) :
    quotientEdgeLoop G H e = 𝟙 _ := by
  let te : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) b a := ⟨Quiver.Hom.toNeg e, he⟩
  let : Unique (@Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) a) := by
    have hroot := rawTreeQuiverRoot_eq G H
    cases hroot
    exact @Quiver.Arborescence.uniquePath (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawTreeQuiverArborescence G H) a
  have hp : rawTreePathAtRoot G H a =
      @Quiver.Path.cons (RawBassSerreOrbitVertex G H)
        (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) b a
        (rawTreePathAtRoot G H b) te := by
    exact Subsingleton.elim _ _
  rw [quotientEdgeLoop,
    quotientTreePathHom_eq_rawTreePathAtRoot G H a,
    quotientTreePathHom_eq_rawTreePathAtRoot G H b, hp,
    rawTreePathMap_cons_raw]
  have hpath := @freeGroupoidPathHom_cons
    (RawBassSerreOrbitVertex G H)
    (rawBassSerreOrbitQuiver.inst G H)
    (rawBassSerreOrbitRoot G H) _ _
    (rawTreePathMap G H (rawTreePathAtRoot G H b))
    (Quiver.Hom.toNeg e)
  rw [hpath]
  simp

theorem kuroshFreePartHom_quotientEdgeLoop_tree_pos {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toPos e ∈ rawBassSerreOrbitTree G H a b) :
    kuroshFreePartHom G H (quotientEdgeLoop G H e) = 1 := by
  rw [quotientEdgeLoop_tree_pos G H e he]
  exact (kuroshFreePartHom G H).map_one

theorem kuroshFreePartHom_quotientEdgeLoop_tree_neg {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (he : Quiver.Hom.toNeg e ∈ rawBassSerreOrbitTree G H b a) :
    kuroshFreePartHom G H (quotientEdgeLoop G H e) = 1 := by
  rw [quotientEdgeLoop_tree_neg G H e he]
  exact (kuroshFreePartHom G H).map_one

noncomputable instance kuroshFreePart_isFree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    IsFreeGroup (KuroshFreePart G H) := by
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (RawBassSerreOrbitVertex G H) from
        rawBassSerreOrbitRoot G H) :=
    rawBassSerreOrbitQuiver_rootedConnected G H
  let : IsConnected
      (Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H)) :=
    freeGroupoid_isConnected_of_rootedConnected
      (rawBassSerreOrbitRoot G H)
  exact IsFreeGroupoid.endIsFreeOfConnectedFree
    ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj
      (rawBassSerreOrbitRoot G H))

/-- Index set for the visible Kurosh factors together with the free part. -/
abbrev KuroshComponentIndex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  KuroshFactorIndex G H ⊕ PUnit

/-- The component group at a Kurosh factor or at the free quotient graph. -/
def KuroshComponent {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshComponentIndex G H → Type (max (u + 1) (v + 1)) :=
  Sum.elim
    (fun q => ULift.{max (u + 1) (v + 1)} (kuroshFactorSubgroup G H q))
    (fun _ => ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))

instance kuroshComponentGroup {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : KuroshComponentIndex G H) : Group (KuroshComponent G H q) := by
  cases q using Sum.casesOn with
  | inl q =>
      change Group
        (ULift.{max (u + 1) (v + 1)} (kuroshFactorSubgroup G H q))
      infer_instance
  | inr q =>
      change Group
        (ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))
      infer_instance

/-! The vertex-group version is the convenient graph-of-groups presentation.
It retains the (trivial) central vertex groups until the final reduction to
the usual factor-only Kurosh indexing. -/

/-- The stabilizer in `H` of the chosen representative of a quotient vertex. -/
abbrev treeVertexStabilizer {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) : Subgroup H :=
  MulAction.stabilizer H (rawTreeRepresentative G H a)

/-- All quotient vertices, together with one additional index for the free part. -/
abbrev TreeKuroshComponentIndex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  RawBassSerreOrbitVertex G H ⊕ PUnit

/-- The family of vertex stabilizers together with the quotient graph's loop group. -/
def TreeKuroshComponent {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshComponentIndex G H → Type (max (u + 1) (v + 1)) :=
  Sum.elim
    (fun a => ULift.{max (u + 1) (v + 1)} (treeVertexStabilizer G H a))
    (fun _ => ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))

instance treeKuroshComponentGroup {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : TreeKuroshComponentIndex G H) : Group (TreeKuroshComponent G H q) := by
  cases q using Sum.casesOn with
  | inl a =>
      change Group
        (ULift.{max (u + 1) (v + 1)} (treeVertexStabilizer G H a))
      infer_instance
  | inr q =>
      change Group
        (ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H))
      infer_instance

/-- The free product of all vertex stabilizers and the free part. -/
abbrev TreeKuroshProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  FreeProduct (TreeKuroshComponent G H)

/-- Map each stabilizer by inclusion and the free part by evaluation in `H`. -/
noncomputable def treeKuroshComponentHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : TreeKuroshComponentIndex G H) :
    TreeKuroshComponent G H q →* H := by
  cases q using Sum.casesOn with
  | inl a =>
      change ULift.{max (u + 1) (v + 1)} (treeVertexStabilizer G H a) →* H
      exact
        { toFun := fun x => x.down.1
          map_one' := by simp
          map_mul' := by intro x y; simp }
  | inr q =>
      change ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H) →* H
      exact
        { toFun := fun x => kuroshFreePartHom G H x.down
          map_one' := by
            exact (kuroshFreePartHom G H).map_one
          map_mul' := by
            intro x y
            exact (kuroshFreePartHom G H).map_mul x.down y.down }

/-- The homomorphism induced by the stabilizer inclusions and free-part evaluation. -/
noncomputable def treeKuroshProductToH {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshProduct G H →* H :=
  Monoid.CoprodI.lift (treeKuroshComponentHom G H)

/-- Include a vertex stabilizer as a factor in the tree Kurosh product. -/
noncomputable def treeKuroshVertexInclusion {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    treeVertexStabilizer G H a →* TreeKuroshProduct G H :=
  { toFun := fun x => Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)
    map_one' := by
      change Monoid.CoprodI.of (1 : TreeKuroshComponent G H (Sum.inl a)) = 1
      exact (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inl a) →* TreeKuroshProduct G H).map_one
    map_mul' := by
      intro x y
      change Monoid.CoprodI.of
          (show TreeKuroshComponent G H (Sum.inl a) from ULift.up (x * y)) =
        Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x) *
          Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inl a) from ULift.up y)
      rw [← (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inl a) →* TreeKuroshProduct G H).map_mul]
      rfl }

/-- Include the quotient graph's loop group as the free factor in the tree product. -/
noncomputable def treeKuroshFreeInclusion {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    KuroshFreePart G H →* TreeKuroshProduct G H :=
  { toFun := fun x => Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)
    map_one' := by
      change Monoid.CoprodI.of (1 : TreeKuroshComponent G H (Sum.inr PUnit.unit)) = 1
      exact (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inr PUnit.unit) →* TreeKuroshProduct G H).map_one
    map_mul' := by
      intro x y
      change Monoid.CoprodI.of
          (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up (x * y)) =
        Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x) *
          Monoid.CoprodI.of
            (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up y)
      rw [← (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inr PUnit.unit) →* TreeKuroshProduct G H).map_mul]
      rfl }

@[simp]
theorem treeKuroshProductToH_vertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) (x : treeVertexStabilizer G H a) :
    treeKuroshProductToH G H (treeKuroshVertexInclusion G H a x) = x := by
  change treeKuroshProductToH G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = x
  change (Monoid.CoprodI.lift (treeKuroshComponentHom G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = x
  rw [Monoid.CoprodI.lift_of]
  rfl

@[simp]
theorem treeKuroshProductToH_free {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    treeKuroshProductToH G H (treeKuroshFreeInclusion G H x) =
      kuroshFreePartHom G H x := by
  change treeKuroshProductToH G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) =
    kuroshFreePartHom G H x
  change (Monoid.CoprodI.lift (treeKuroshComponentHom G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) =
    kuroshFreePartHom G H x
  rw [Monoid.CoprodI.lift_of]
  rfl

/-- The explicit free product whose factors are the Kurosh stabilizers and free part. -/
abbrev KuroshProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  FreeProduct (KuroshComponent G H)

end Kurosh

end GraphCoveringTheory
