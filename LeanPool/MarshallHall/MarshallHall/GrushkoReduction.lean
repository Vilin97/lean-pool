/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoGeneral


/-!
## Reduced words for the binary free product

`Mathlib.GroupTheory.CoprodI` contains the normal-form theorem for an
indexed free product.  The binary coproduct has a separate implementation,
so this file supplies the small, explicit bridge needed by the Grushko
reduction argument.  In particular, the reduced-word object below is tied to
the actual inclusions `Monoid.Coprod.inl` and `Monoid.Coprod.inr`.
-/

@[expose] public section



open Function Monoid.Coprod

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

/-- The two group factors represented as a Boolean-indexed family. -/
abbrev binaryFamily (G H : Type u) : Bool → Type u
  | false => G
  | true => H

instance binaryFamilyGroup (G H : Type u) [Group G] [Group H] :
    ∀ b, Group (binaryFamily G H b) := by
  intro b
  cases b
  · change Group G
    exact inferInstance
  · change Group H
    exact inferInstance

noncomputable instance binaryFamilyDecidableEq (G H : Type u) :
    ∀ b, DecidableEq (binaryFamily G H b) := by
  intro b
  cases b <;> exact Classical.decEq _

/-- The free product of the two factors represented as a Boolean-indexed family. -/
abbrev binaryIndexedProduct :=
  Monoid.CoprodI (binaryFamily G H)

/-- The inclusion of the left factor in the Boolean-indexed free product. -/
def indexedLeft : G →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.CoprodI.of (M := binaryFamily G H) (i := false)

/-- The inclusion of the right factor in the Boolean-indexed free product. -/
def indexedRight : H →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.CoprodI.of (M := binaryFamily G H) (i := true)

/-- Converts the binary free product to the Boolean-indexed presentation. -/
def binaryToIndexed : G ∗ H →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.Coprod.lift (indexedLeft (G := G) (H := H))
    (indexedRight (G := G) (H := H))

/-- The factor inclusions defining a map from the Boolean-indexed presentation. -/
def indexedToBinaryFamily :
    (b : Bool) → binaryFamily G H b →* G ∗ H
  | false => Monoid.Coprod.inl
  | true => Monoid.Coprod.inr

/-- Converts the Boolean-indexed free product to the binary presentation. -/
def indexedToBinary : binaryIndexedProduct (G := G) (H := H) →* G ∗ H :=
  Monoid.CoprodI.lift (M := binaryFamily G H)
    (indexedToBinaryFamily (G := G) (H := H))

@[simp]
theorem binaryToIndexed_inl (g : G) :
    binaryToIndexed (G := G) (H := H) (Monoid.Coprod.inl g) = indexedLeft g := by
  rfl

@[simp]
theorem binaryToIndexed_inr (h : H) :
    binaryToIndexed (G := G) (H := H) (Monoid.Coprod.inr h) = indexedRight h := by
  rfl

@[simp]
theorem indexedToBinary_left (g : G) :
    indexedToBinary (G := G) (H := H) (indexedLeft g) = Monoid.Coprod.inl g := by
  change (Monoid.CoprodI.lift (M := binaryFamily G H)
      (indexedToBinaryFamily (G := G) (H := H)))
      (Monoid.CoprodI.of (M := binaryFamily G H) (i := false) g) =
        Monoid.Coprod.inl g
  rw [Monoid.CoprodI.lift_of]
  rfl

@[simp]
theorem indexedToBinary_right (h : H) :
    indexedToBinary (G := G) (H := H) (indexedRight h) = Monoid.Coprod.inr h := by
  change (Monoid.CoprodI.lift (M := binaryFamily G H)
      (indexedToBinaryFamily (G := G) (H := H)))
      (Monoid.CoprodI.of (M := binaryFamily G H) (i := true) h) =
        Monoid.Coprod.inr h
  rw [Monoid.CoprodI.lift_of]
  rfl

theorem indexedToBinary_comp_binaryToIndexed :
    (indexedToBinary (G := G) (H := H)).comp
        (binaryToIndexed (G := G) (H := H)) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext g
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inl g)) =
      Monoid.Coprod.inl g
    rw [binaryToIndexed_inl, indexedToBinary_left]
  · ext h
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inr h)) =
      Monoid.Coprod.inr h
    rw [binaryToIndexed_inr, indexedToBinary_right]

theorem binaryToIndexed_comp_indexedToBinary :
    (binaryToIndexed (G := G) (H := H)).comp
        (indexedToBinary (G := G) (H := H)) = MonoidHom.id _ := by
  classical
  apply Monoid.CoprodI.ext_hom
  intro b
  cases b
  · ext g
    change G at g
    change binaryToIndexed (indexedToBinary (indexedLeft g)) = indexedLeft g
    rw [indexedToBinary_left, binaryToIndexed_inl]
  · ext h
    change H at h
    change binaryToIndexed (indexedToBinary (indexedRight h)) = indexedRight h
    rw [indexedToBinary_right, binaryToIndexed_inr]

/-- The equivalence between binary and Boolean-indexed free-product presentations. -/
def binaryIndexedEquiv : (G ∗ H) ≃* binaryIndexedProduct (G := G) (H := H) :=
  { toFun := binaryToIndexed
    invFun := indexedToBinary
    left_inv := by
      intro x
      have h := congrArg (fun f : (G ∗ H) →* G ∗ H => f x)
        (indexedToBinary_comp_binaryToIndexed (G := G) (H := H))
      exact h
    right_inv := by
      intro x
      have h := congrArg (fun f : binaryIndexedProduct (G := G) (H := H) →*
          binaryIndexedProduct (G := G) (H := H) => f x)
        (binaryToIndexed_comp_indexedToBinary (G := G) (H := H))
      exact h
    map_mul' := map_mul binaryToIndexed }

/-- The reduced word representing an element of the binary free product. -/
def binaryReducedWord (x : G ∗ H) :
    Monoid.CoprodI.Word (binaryFamily G H) := by
  classical
  exact Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
    (binaryToIndexed x)

theorem binaryReducedWord_prod (x : G ∗ H) :
    Monoid.CoprodI.Word.prod (binaryReducedWord (G := G) (H := H) x) =
      binaryToIndexed x := by
  classical
  change (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm
      (binaryReducedWord (G := G) (H := H) x) = binaryToIndexed x
  rw [binaryReducedWord]
  exact (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm_apply_apply
    (binaryToIndexed x)

@[simp]
theorem binaryReducedWord_one :
    binaryReducedWord (G := G) (H := H) (1 : G ∗ H) =
      Monoid.CoprodI.Word.empty := by
  classical
  simp [binaryReducedWord, Monoid.CoprodI.Word.equiv]

/-- Includes a factor-tagged letter in the Boolean-indexed free product. -/
def binaryLetterToIndexed : Sum G H → binaryIndexedProduct (G := G) (H := H)
  | Sum.inl g => indexedLeft g
  | Sum.inr h => indexedRight h

theorem binaryToIndexed_factorWordProd (u : List (Sum G H)) :
    binaryToIndexed (G := G) (H := H) (factorWordProd u) =
      (u.map (binaryLetterToIndexed (G := G) (H := H))).prod := by
  induction u with
  | nil => simp [factorWordProd]
  | cons a u ih =>
      cases a <;>
        simp [factorWordProd, separatedMap, binaryLetterToIndexed, ih]

/-! Reversing an oriented labelled path reverses the order and inverts every
label.  This is the algebraic operation used by the graph-fold bookkeeping. -/
/-- Inverts a letter while retaining its factor tag. -/
def factorWordInv : Sum G H → Sum G H
  | Sum.inl g => Sum.inl g⁻¹
  | Sum.inr h => Sum.inr h⁻¹

@[simp]
theorem factorWordInv_factorWordInv (a : Sum G H) :
    factorWordInv (factorWordInv (G := G) (H := H) a) = a := by
  cases a <;> simp [factorWordInv]

@[simp]
theorem separatedMap_factorWordInv (a : Sum G H) :
    separatedMap (factorWordInv (G := G) (H := H) a) =
      (separatedMap (G := G) (H := H) a)⁻¹ := by
  cases a <;> rfl

theorem factorWordProd_reverse_inv (u : List (Sum G H)) :
    factorWordProd (G := G) (H := H)
        (u.reverse.map (factorWordInv (G := G) (H := H))) =
      (factorWordProd (G := G) (H := H) u)⁻¹ := by
  induction u with
  | nil => simp [factorWordProd]
  | cons a u ih =>
      rw [List.reverse_cons, List.map_append, factorWordProd_append, ih]
      simp [factorWordProd, separatedMap_factorWordInv, mul_inv_rev]

theorem word_length_rcons_le {b : Bool}
    (p : Monoid.CoprodI.Word.Pair (binaryFamily G H) b) :
    (Monoid.CoprodI.Word.rcons p).toList.length ≤ p.tail.toList.length + 1 := by
  classical
  by_cases hp : p.head = 1
  · simp [Monoid.CoprodI.Word.rcons, hp]
  · simp [Monoid.CoprodI.Word.rcons, hp, Monoid.CoprodI.Word.cons]

theorem word_pair_tail_length_le {b : Bool}
    (w : Monoid.CoprodI.Word (binaryFamily G H)) :
    (Monoid.CoprodI.Word.equivPair b w).tail.toList.length ≤ w.toList.length := by
  classical
  let p := Monoid.CoprodI.Word.equivPair b w
  have hrcons : Monoid.CoprodI.Word.rcons p = w := by
    rw [← Monoid.CoprodI.Word.equivPair_symm]
    exact (Monoid.CoprodI.Word.equivPair b).symm_apply_apply w
  change p.tail.toList.length ≤ w.toList.length
  by_cases hp : p.head = 1
  · rw [Monoid.CoprodI.Word.rcons, dite_eq_left hp] at hrcons
    simp [hrcons]
  · rw [Monoid.CoprodI.Word.rcons, dite_eq_right hp] at hrcons
    have hlen : w.toList.length = p.tail.toList.length + 1 := by
      calc
        w.toList.length =
            (Monoid.CoprodI.Word.cons p.head p.tail p.fstIdx_ne hp).toList.length := by
          rw [hrcons]
        _ = p.tail.toList.length + 1 := by
          simp [Monoid.CoprodI.Word.cons]
    omega

theorem word_length_mul_left_le {b : Bool} (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
      (Monoid.CoprodI.of a * x)).toList.length ≤
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).toList.length + 1 := by
  classical
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) = Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    calc
      e.symm (e (Monoid.CoprodI.of a * x)) = Monoid.CoprodI.of a * x :=
        e.symm_apply_apply _
      _ = Monoid.CoprodI.of a * e.symm (e x) := by
        rw [e.symm_apply_apply]
      _ = e.symm (Monoid.CoprodI.of a • e x) := by
        change Monoid.CoprodI.of a * Monoid.CoprodI.Word.prod (e x) =
          Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
        rw [Monoid.CoprodI.Word.prod_smul]
  rw [he]
  let q : Monoid.CoprodI.Word.Pair (binaryFamily G H) b :=
    { Monoid.CoprodI.Word.equivPair b (e x) with
      head := a * (Monoid.CoprodI.Word.equivPair b (e x)).head }
  have hq : Monoid.CoprodI.of a • e x = Monoid.CoprodI.Word.rcons q := by
    rw [← Monoid.CoprodI.Word.smul_eq_of_smul]
    simpa [q] using
      (Monoid.CoprodI.Word.smul_def (M := binaryFamily G H) a (e x))
  rw [hq]
  have htail := word_pair_tail_length_le (G := G) (H := H) (b := b) (e x)
  have htail' : q.tail.toList.length ≤ (e x).toList.length := by
    simpa [q] using htail
  exact (word_length_rcons_le (G := G) (H := H) q).trans
    (Nat.add_le_add_right htail' 1)

/-- The number of letters in the reduced free-product normal form. -/
def binaryReducedLength (x : G ∗ H) : ℕ :=
  (binaryReducedWord (G := G) (H := H) x).toList.length

@[simp]
theorem binaryToIndexed_separatedMap (a : Sum G H) :
    binaryToIndexed (G := G) (H := H) (separatedMap a) =
      binaryLetterToIndexed (G := G) (H := H) a := by
  cases a <;> simp [separatedMap, binaryLetterToIndexed]

theorem binaryReducedLength_factorWordProd_le (u : List (Sum G H)) :
    binaryReducedLength (G := G) (H := H) (factorWordProd u) ≤ u.length := by
  classical
  induction u with
  | nil =>
      change (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (binaryToIndexed (factorWordProd ([] : List (Sum G H))))).toList.length ≤ 0
      simp [factorWordProd, Monoid.CoprodI.Word.equiv]
  | cons a u ih =>
      have hword : binaryReducedWord (G := G) (H := H) (factorWordProd (a :: u)) =
          Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
            (binaryLetterToIndexed (G := G) (H := H) a *
              binaryToIndexed (G := G) (H := H) (factorWordProd u)) := by
        apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
        change Monoid.CoprodI.Word.prod
            (binaryReducedWord (G := G) (H := H) (factorWordProd (a :: u))) =
          Monoid.CoprodI.Word.prod
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
              (binaryLetterToIndexed (G := G) (H := H) a *
                binaryToIndexed (G := G) (H := H) (factorWordProd u)))
        rw [binaryReducedWord_prod]
        change binaryToIndexed (G := G) (H := H) (factorWordProd (a :: u)) =
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
              (binaryLetterToIndexed (G := G) (H := H) a *
                binaryToIndexed (G := G) (H := H) (factorWordProd u)))
        rw [(Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm_apply_apply]
        cases a <;>
          simp [factorWordProd, separatedMap, binaryLetterToIndexed]
      rw [binaryReducedLength, hword]
      cases a with
      | inl g =>
          exact (word_length_mul_left_le (G := G) (H := H) (b := false) g _).trans
            (Nat.succ_le_succ ih)
      | inr h =>
          exact (word_length_mul_left_le (G := G) (H := H) (b := true) h _).trans
            (Nat.succ_le_succ ih)

/-- Converts a Boolean-indexed factor element to a disjoint-union label. -/
def binarySigmaToSum : Sigma (binaryFamily G H) → Sum G H
  | ⟨false, g⟩ => Sum.inl g
  | ⟨true, h⟩ => Sum.inr h

@[simp]
theorem binaryLetterToIndexed_sigma (z : Sigma (binaryFamily G H)) :
    binaryLetterToIndexed (G := G) (H := H) (binarySigmaToSum z) =
      Monoid.CoprodI.of z.2 := by
  cases z with
  | mk b z =>
      cases b <;> rfl

/-- The reduced normal form as a list of factor-tagged letters. -/
def binaryReducedLetters (x : G ∗ H) : List (Sum G H) :=
  (binaryReducedWord (G := G) (H := H) x).toList.map binarySigmaToSum

theorem binaryLetterToIndexed_map_prod
    (l : List (Sigma (binaryFamily G H))) :
    ((l.map binarySigmaToSum).map (binaryLetterToIndexed (G := G) (H := H))).prod =
      (l.map (fun z => Monoid.CoprodI.of z.2)).prod := by
  induction l with
  | nil => rfl
  | cons z zs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [binaryLetterToIndexed_sigma, ih]

theorem factorWordProd_binaryReducedLetters (x : G ∗ H) :
    factorWordProd (binaryReducedLetters (G := G) (H := H) x) = x := by
  classical
  apply (binaryIndexedEquiv (G := G) (H := H)).injective
  calc
    binaryToIndexed (G := G) (H := H)
        (factorWordProd (binaryReducedLetters (G := G) (H := H) x)) =
        ((binaryReducedLetters (G := G) (H := H) x).map
          (binaryLetterToIndexed (G := G) (H := H))).prod :=
      binaryToIndexed_factorWordProd _
    _ = ((binaryReducedWord (G := G) (H := H) x).toList.map
          (fun z => Monoid.CoprodI.of z.2)).prod := by
      simpa [binaryReducedLetters, List.map_map] using
        (binaryLetterToIndexed_map_prod (G := G) (H := H)
          ((binaryReducedWord (G := G) (H := H) x).toList))
    _ = Monoid.CoprodI.Word.prod (binaryReducedWord (G := G) (H := H) x) := rfl
    _ = binaryToIndexed (G := G) (H := H) x :=
      binaryReducedWord_prod (G := G) (H := H) x

theorem binaryReducedLength_le_factorWordLength (x : G ∗ H) :
    binaryReducedLength (G := G) (H := H) x ≤ factorWordLength x := by
  obtain ⟨u, hu, hux⟩ := factorWordLength_spec x
  calc
    binaryReducedLength x = binaryReducedLength (factorWordProd u) :=
      (congrArg binaryReducedLength hux).symm
    _ ≤ u.length := binaryReducedLength_factorWordProd_le u
    _ = factorWordLength x := hu

theorem factorWordLength_le_binaryReducedLength (x : G ∗ H) :
    factorWordLength x ≤ binaryReducedLength x := by
  let u := binaryReducedLetters (G := G) (H := H) x
  have hu : factorWordProd u = x := by
    simpa [u] using factorWordProd_binaryReducedLetters (G := G) (H := H) x
  calc
    factorWordLength x = factorWordLength (factorWordProd u) := by rw [hu]
    _ ≤ u.length := factorWordLength_wordProd_le u
    _ = binaryReducedLength x := by
      simp [u, binaryReducedLength, binaryReducedLetters]

theorem factorWordLength_eq_binaryReducedLength (x : G ∗ H) :
    factorWordLength x = binaryReducedLength x :=
  le_antisymm (factorWordLength_le_binaryReducedLength x)
    (binaryReducedLength_le_factorWordLength x)

/-! ### The shape of a reduced binary word -/

/-- The factor index of a binary letter, expressed in the index type used by
the indexed free-product normal form. -/
def binarySumIndex : Sum G H → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

omit [Group G] [Group H] in
@[simp]
theorem binarySumIndex_inl (g : G) :
    binarySumIndex (G := G) (H := H) (Sum.inl g) = false := rfl

omit [Group G] [Group H] in
@[simp]
theorem binarySumIndex_inr (h : H) :
    binarySumIndex (G := G) (H := H) (Sum.inr h) = true := rfl

@[simp]
theorem binarySumIndex_factorWordInv (a : Sum G H) :
    binarySumIndex (factorWordInv (G := G) (H := H) a) =
      binarySumIndex a := by
  cases a <;> rfl

omit [Group G] [Group H] in
@[simp]
theorem binarySumIndex_sigma (z : Sigma (binaryFamily G H)) :
    binarySumIndex (G := G) (H := H) (binarySigmaToSum z) = z.1 := by
  cases z with
  | mk b z => cases b <;> rfl

theorem binaryReducedLetters_ne_one (x : G ∗ H) :
    ∀ a ∈ binaryReducedLetters (G := G) (H := H) x,
      a = Sum.inl 1 ∨ a = Sum.inr 1 → False := by
  intro a ha hbad
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  cases hbad with
  | inl h =>
      cases z with
      | mk b z =>
          cases b with
          | false =>
              change G at z
              have hz1 : z = 1 := by
                simpa [binarySigmaToSum] using h
              exact (binaryReducedWord (G := G) (H := H) x).ne_one
                ⟨false, z⟩ hz hz1
          | true => simp_all [binarySigmaToSum]
  | inr h =>
      cases z with
      | mk b z =>
          cases b with
          | false => simp_all [binarySigmaToSum]
          | true =>
              change H at z
              have hz1 : z = 1 := by
                simpa [binarySigmaToSum] using h
              exact (binaryReducedWord (G := G) (H := H) x).ne_one
                ⟨true, z⟩ hz hz1

theorem binaryReducedWord_chain_ne (x : G ∗ H) :
    (binaryReducedWord (G := G) (H := H) x).toList.IsChain
      (fun a b => a.1 ≠ b.1) :=
  (binaryReducedWord (G := G) (H := H) x).chain_ne

theorem binaryReducedLetters_chain_ne (x : G ∗ H) :
    (binaryReducedLetters (G := G) (H := H) x).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
  rw [binaryReducedLetters, List.isChain_map]
  exact (binaryReducedWord_chain_ne (G := G) (H := H) x).imp
    (by
      intro z z' h
      simpa only [binarySumIndex_sigma] using h)

theorem binaryReducedLetters_mem_ne_one (x : G ∗ H)
    {a : Sum G H} (ha : a ∈ binaryReducedLetters (G := G) (H := H) x) :
    a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
  constructor <;> intro h
  · exact binaryReducedLetters_ne_one (G := G) (H := H) x a ha (Or.inl h)
  · exact binaryReducedLetters_ne_one (G := G) (H := H) x a ha (Or.inr h)

/-! ### Exact multiplication in the different-factor case -/

theorem binaryReducedWord_inl_mul_of_fstIdx_ne (g : G) (x : G ∗ H)
    (hidx : (binaryReducedWord (G := G) (H := H) x).fstIdx ≠ some false)
    (hg : g ≠ 1) :
    binaryReducedWord (G := G) (H := H) (inl g * x) =
      Monoid.CoprodI.Word.cons g (binaryReducedWord x) hidx hg := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (binaryReducedWord (G := G) (H := H) (inl g * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.cons g (binaryReducedWord x) hidx hg)
  rw [binaryReducedWord_prod, Monoid.CoprodI.Word.prod_cons]
  rw [binaryReducedWord_prod]
  change binaryToIndexed (G := G) (H := H) (inl g * x) =
    Monoid.CoprodI.of (M := binaryFamily G H) (i := false) g *
      binaryToIndexed (G := G) (H := H) x
  simp [binaryToIndexed, indexedLeft]

theorem binaryReducedLength_inl_mul_of_fstIdx_ne (g : G) (x : G ∗ H)
    (hidx : (binaryReducedWord (G := G) (H := H) x).fstIdx ≠ some false)
    (hg : g ≠ 1) :
    binaryReducedLength (G := G) (H := H) (inl g * x) =
      binaryReducedLength x + 1 := by
  rw [binaryReducedLength,
    binaryReducedWord_inl_mul_of_fstIdx_ne (G := G) (H := H) g x hidx hg]
  simp [Monoid.CoprodI.Word.cons, binaryReducedLength]

theorem binaryReducedWord_inr_mul_of_fstIdx_ne (h : H) (x : G ∗ H)
    (hidx : (binaryReducedWord (G := G) (H := H) x).fstIdx ≠ some true)
    (hh : h ≠ 1) :
    binaryReducedWord (G := G) (H := H) (inr h * x) =
      Monoid.CoprodI.Word.cons h (binaryReducedWord x) hidx hh := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (binaryReducedWord (G := G) (H := H) (inr h * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.cons h (binaryReducedWord x) hidx hh)
  rw [binaryReducedWord_prod, Monoid.CoprodI.Word.prod_cons]
  rw [binaryReducedWord_prod]
  change binaryToIndexed (G := G) (H := H) (inr h * x) =
    Monoid.CoprodI.of (M := binaryFamily G H) (i := true) h *
      binaryToIndexed (G := G) (H := H) x
  simp [binaryToIndexed, indexedRight]

theorem binaryReducedLength_inr_mul_of_fstIdx_ne (h : H) (x : G ∗ H)
    (hidx : (binaryReducedWord (G := G) (H := H) x).fstIdx ≠ some true)
    (hh : h ≠ 1) :
    binaryReducedLength (G := G) (H := H) (inr h * x) =
      binaryReducedLength x + 1 := by
  rw [binaryReducedLength,
    binaryReducedWord_inr_mul_of_fstIdx_ne (G := G) (H := H) h x hidx hh]
  simp [Monoid.CoprodI.Word.cons, binaryReducedLength]

theorem word_cons_of_fstIdx_ne {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (hidx : (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).fstIdx ≠ some b)
    (ha : a ≠ 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.cons a
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) hidx ha := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.cons a
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) hidx ha)
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
    rw [Monoid.CoprodI.Word.prod_smul]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.of a * e.symm (e x)
    rw [e.symm_apply_apply]
  rw [he, Monoid.CoprodI.Word.prod_cons,
    Monoid.CoprodI.Word.prod_smul]

theorem word_length_cons_of_fstIdx_ne {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (hidx : (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).fstIdx ≠ some b)
    (ha : a ≠ 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).toList.length + 1 := by
  rw [word_cons_of_fstIdx_ne a x hidx ha]
  simp [Monoid.CoprodI.Word.cons]

theorem word_rcons_of_factor_mul {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.rcons
        { Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) with
          head := a * (Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head } := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.rcons
        { Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) with
          head := a * (Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head })
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
    rw [Monoid.CoprodI.Word.prod_smul]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.of a * e.symm (e x)
    rw [e.symm_apply_apply]
  rw [he, Monoid.CoprodI.Word.of_smul_def b (e x) a]

theorem word_length_factor_mul {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      if a * (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1 then
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length
      else
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length + 1 := by
  rw [word_rcons_of_factor_mul]
  by_cases h : a * (Monoid.CoprodI.Word.equivPair b
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1
  · simp [Monoid.CoprodI.Word.rcons, h]
  · simp [Monoid.CoprodI.Word.rcons, h, Monoid.CoprodI.Word.cons]

theorem word_tail_of_factor_mul_eq_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail := by
  rw [word_rcons_of_factor_mul]
  simp [Monoid.CoprodI.Word.rcons, h]

theorem word_cons_of_factor_mul_ne_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head ≠ 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.cons
        (a * (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head)
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).fstIdx_ne h := by
  rw [word_rcons_of_factor_mul]
  simp [Monoid.CoprodI.Word.rcons, h, Monoid.CoprodI.Word.cons]

theorem word_length_factor_mul_eq_tail_of_mul_eq_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length := by
  rw [word_tail_of_factor_mul_eq_one a x h]

theorem word_length_factor_mul_eq_tail_add_one_of_mul_ne_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head ≠ 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length + 1 := by
  rw [word_cons_of_factor_mul_ne_one a x h]
  simp [Monoid.CoprodI.Word.cons]

/-- Converts a disjoint-union label to a Boolean-indexed factor element. -/
def sumToSigma : Sum G H → Sigma (binaryFamily G H)
  | Sum.inl g => ⟨false, g⟩
  | Sum.inr h => ⟨true, h⟩

omit [Group G] [Group H] in
@[simp]
theorem binarySigmaToSum_sumToSigma (a : Sum G H) :
    binarySigmaToSum (G := G) (H := H) (sumToSigma (G := G) (H := H) a) = a := by
  cases a <;> rfl

omit [Group G] [Group H] in
@[simp]
theorem sumToSigma_snd_inl (g : G) :
    (sumToSigma (G := G) (H := H) (Sum.inl g)).2 = g := rfl

omit [Group G] [Group H] in
@[simp]
theorem sumToSigma_snd_inr (h : H) :
    (sumToSigma (G := G) (H := H) (Sum.inr h)).2 = h := rfl

omit [Group G] [Group H] in
@[simp]
theorem sumToSigma_fst (a : Sum G H) :
    (sumToSigma (G := G) (H := H) a).1 =
      binarySumIndex (G := G) (H := H) a := by
  cases a <;> rfl

theorem reducedWord_of_sumList {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    ∃ w : Monoid.CoprodI.Word (binaryFamily G H),
      w.toList = u.map (sumToSigma (G := G) (H := H)) := by
  let v : List (Sigma (binaryFamily G H)) :=
    u.map (sumToSigma (G := G) (H := H))
  have hv_ne : ∀ z ∈ v, z.2 ≠ 1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    cases a with
    | inl g =>
        change g ≠ (1 : G)
        intro hg
        apply (hne (Sum.inl g) ha).1
        exact congrArg (fun z : G => Sum.inl z) hg
    | inr h =>
        change h ≠ (1 : H)
        intro hh
        apply (hne (Sum.inr h) ha).2
        exact congrArg (fun z : H => Sum.inr z) hh
  have hv_chain : v.IsChain (fun a b => a.1 ≠ b.1) := by
    dsimp [v]
    rw [List.isChain_map]
    exact hchain.imp (by
      intro a b hab
      simpa only [sumToSigma_fst] using hab)
  exact ⟨{ toList := v, ne_one := hv_ne, chain_ne := hv_chain }, rfl⟩

theorem binaryReducedWord_factorWordProd_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    binaryReducedWord (G := G) (H := H) (factorWordProd u) =
      { toList := u.map (sumToSigma (G := G) (H := H)),
        ne_one := by
          intro z hz
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
          cases a with
          | inl g =>
              change g ≠ (1 : G)
              intro hg
              apply (hne (Sum.inl g) ha).1
              exact congrArg (fun z : G => Sum.inl z) hg
          | inr h =>
              change h ≠ (1 : H)
              intro hh
              apply (hne (Sum.inr h) ha).2
              exact congrArg (fun z : H => Sum.inr z) hh,
        chain_ne := by
          rw [List.isChain_map]
          exact hchain.imp (by
            intro a b hab
            simpa only [sumToSigma_fst] using hab) } := by
  let w : Monoid.CoprodI.Word (binaryFamily G H) :=
    { toList := u.map (sumToSigma (G := G) (H := H)),
      ne_one := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
        cases a with
        | inl g =>
            change g ≠ (1 : G)
            intro hg
            apply (hne (Sum.inl g) ha).1
            exact congrArg (fun z : G => Sum.inl z) hg
        | inr h =>
            change h ≠ (1 : H)
            intro hh
            apply (hne (Sum.inr h) ha).2
            exact congrArg (fun z : H => Sum.inr z) hh,
      chain_ne := by
        rw [List.isChain_map]
        exact hchain.imp (by
          intro a b hab
          simpa only [sumToSigma_fst] using hab) }
  have hprod : Monoid.CoprodI.Word.prod w =
      binaryToIndexed (G := G) (H := H) (factorWordProd u) := by
    rw [binaryToIndexed_factorWordProd]
    dsimp [w, Monoid.CoprodI.Word.prod]
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro a ha
    cases a <;> rfl
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (binaryReducedWord (G := G) (H := H) (factorWordProd u)) =
    Monoid.CoprodI.Word.prod w
  rw [binaryReducedWord_prod]
  exact hprod.symm

theorem factorWordLength_factorWordProd_eq_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    factorWordLength (factorWordProd u) = u.length := by
  rw [factorWordLength_eq_binaryReducedLength,
    binaryReducedLength,
    binaryReducedWord_factorWordProd_of_reduced (u := u) hne hchain]
  simp

theorem factorWordProd_ne_one_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b))
    (hpos : u ≠ []) :
    factorWordProd u ≠ 1 := by
  intro hprod
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  have hzero : factorWordLength (factorWordProd u) = 0 := by
    rw [hprod]
    simp
  have : u.length = 0 := by
    rw [← hlen, hzero]
  exact hpos (List.length_eq_zero_iff.mp this)

theorem factorWordProd_eq_one_iff_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    factorWordProd u = 1 ↔ u = [] := by
  constructor
  · intro hprod
    by_contra hne_nil
    exact factorWordProd_ne_one_of_reduced hne hchain hne_nil hprod
  · intro hu
    simp [hu, factorWordProd]

theorem factorWordLength_inl_mul_inr (g : G) (h : H)
    (hg : g ≠ 1) (hh : h ≠ 1) :
    factorWordLength (inl g * inr h) = 2 := by
  have hne : ∀ a ∈ ([Sum.inl g, Sum.inr h] : List (Sum G H)),
      a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by simp [hg], by simp⟩
    · exact ⟨by simp, by simp [hh]⟩
  have hchain : ([Sum.inl g, Sum.inr h] : List (Sum G H)).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
    simp
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  simpa [factorWordProd, separatedMap] using hlen

theorem factorWordLength_inr_mul_inl (h : H) (g : G)
    (hh : h ≠ 1) (hg : g ≠ 1) :
    factorWordLength (inr h * inl g) = 2 := by
  have hne : ∀ a ∈ ([Sum.inr h, Sum.inl g] : List (Sum G H)),
      a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by simp, by simp [hh]⟩
    · exact ⟨by simp [hg], by simp⟩
  have hchain : ([Sum.inr h, Sum.inl g] : List (Sum G H)).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
    simp
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  simpa [factorWordProd, separatedMap] using hlen

/-! ### Nielsen-minimal tuples and the certified descent measure -/

/-- The total canonical syllable length of a finite tuple in the binary free
product. -/
def tupleFactorLength {n : ℕ} (x : Fin n → G ∗ H) : ℕ :=
  ∑ i, factorWordLength (x i)

/-- A tuple is minimal when its total canonical syllable length is least in its
Nielsen-equivalence class. -/
def NielsenMinimal {n : ℕ} (x : Fin n → G ∗ H) : Prop :=
  ∀ y, NielsenEquivalent x y → tupleFactorLength x ≤ tupleFactorLength y

/-- A tuple is Nielsen-reduced when no elementary multiplication or inverse
  multiplication strictly shortens one of its entries.  This is the local
  normal-form condition extracted from a globally minimal tuple. -/
def NielsenReduced {n : ℕ} (x : Fin n → G ∗ H) : Prop :=
  ∀ i j, i ≠ j →
    factorWordLength (x i) ≤ factorWordLength (x i * x j) ∧
      factorWordLength (x i) ≤ factorWordLength (x i * (x j)⁻¹) ∧
      factorWordLength (x i) ≤ factorWordLength (x j * x i)

/-- A Nielsen-equivalent tuple realizes the specified total factor-word length. -/
def NielsenLengthRepresented {n : ℕ} (x : Fin n → G ∗ H) (k : ℕ) : Prop :=
  ∃ y, NielsenEquivalent x y ∧ tupleFactorLength y = k

/-- The least total factor-word length among Nielsen-equivalent tuples. -/
noncomputable def nielsenMinLength {n : ℕ} (x : Fin n → G ∗ H) : ℕ := by
  classical
  exact Nat.find (show ∃ k, NielsenLengthRepresented x k from
    ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)

theorem nielsenMinLength_spec {n : ℕ} (x : Fin n → G ∗ H) :
    NielsenLengthRepresented x (nielsenMinLength x) := by
  classical
  exact Nat.find_spec (show ∃ k, NielsenLengthRepresented x k from
    ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)

theorem exists_nielsen_minimal {n : ℕ} (x : Fin n → G ∗ H) :
    ∃ y, NielsenEquivalent x y ∧ NielsenMinimal y ∧
      tupleFactorLength y = nielsenMinLength x := by
  classical
  obtain ⟨y, hy, hlen⟩ := nielsenMinLength_spec x
  refine ⟨y, hy, ?_, hlen⟩
  intro z hyz
  have hxz : NielsenEquivalent x z :=
    Relation.ReflTransGen.trans hy hyz
  have hmin := Nat.find_min'
    (show ∃ k, NielsenLengthRepresented x k from
      ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)
    (show NielsenLengthRepresented x (tupleFactorLength z) from
      ⟨z, hxz, rfl⟩)
  rw [hlen]
  exact hmin

theorem tupleFactorLength_update {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) (a : G ∗ H) :
    tupleFactorLength (Function.update x i a) =
      factorWordLength a +
        ∑ k ∈ (Finset.univ.erase i), factorWordLength (x k) := by
  rw [tupleFactorLength]
  have hfun :
      (fun k => factorWordLength (Function.update x i a k)) =
        Function.update (fun k => factorWordLength (x k)) i
          (factorWordLength a) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.erase_eq]

theorem tupleFactorLength_split {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) :
    tupleFactorLength x =
      factorWordLength (x i) +
        ∑ k ∈ (Finset.univ.erase i), factorWordLength (x k) := by
  rw [tupleFactorLength]
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => factorWordLength (x k)) (Finset.mem_univ i)
  simpa [Finset.erase_eq, Nat.add_comm] using h.symm

theorem tupleFactorLength_update_lt {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) (a : G ∗ H)
    (ha : factorWordLength a < factorWordLength (x i)) :
    tupleFactorLength (Function.update x i a) < tupleFactorLength x := by
  rw [tupleFactorLength_update, tupleFactorLength_split]
  exact Nat.add_lt_add_right ha _

theorem nielsenMinimal_tupleFactorLength_le_mulRight {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x i * x j)) := by
  apply hmin
  exact Relation.ReflTransGen.single
    (NielsenStep.mulRight i j hij rfl)

theorem nielsenMinimal_no_strict_mulRight_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x i * x j) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulRight hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x i * x j) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

/-! ### Inverse Nielsen moves -/

theorem nielsenEquivalent_mulRight_inv {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x (Function.update x i (x i * (x j)⁻¹)) := by
  let y : Fin n → A := Function.update x j (x j)⁻¹
  let z : Fin n → A := Function.update y i (y i * y j)
  let w : Fin n → A := Function.update z j (z j)⁻¹
  have hxy : NielsenStep x y := NielsenStep.invert j rfl
  have hyz : NielsenStep y z := NielsenStep.mulRight i j hij rfl
  have hzw : NielsenStep z w := NielsenStep.invert j rfl
  have hxyz : NielsenEquivalent x z :=
    Relation.ReflTransGen.trans (Relation.ReflTransGen.single hxy)
      (Relation.ReflTransGen.single hyz)
  have hxyzw : NielsenEquivalent x w :=
    Relation.ReflTransGen.trans hxyz (Relation.ReflTransGen.single hzw)
  have hw : w = Function.update x i (x i * (x j)⁻¹) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [w, z, y, hij]
    · by_cases hkj : k = j
      · subst k
        simp [w, z, y, hki, hij]
      · simp [w, z, y, hki, hkj, hij]
  rw [← hw]
  exact hxyzw

theorem nielsenEquivalent_symm {A : Type*} [Group A] {n : ℕ}
    {x y : Fin n → A} (h : NielsenEquivalent x y) :
    NielsenEquivalent y x := by
  have step_symm : ∀ {u v : Fin n → A}, NielsenStep u v →
      NielsenEquivalent v u := by
    intro u v hstep
    cases hstep with
    | perm e hEq =>
        subst v
        apply Relation.ReflTransGen.single
        apply NielsenStep.perm e.symm
        funext i
        simp [Function.comp_apply]
    | invert i hEq =>
        subst v
        apply Relation.ReflTransGen.single
        apply NielsenStep.invert i
        funext k
        by_cases hki : k = i
        · subst k
          simp
        · simp [hki]
    | mulRight i j hij hEq =>
        have hback := nielsenEquivalent_mulRight_inv v i j hij
        have hEqBack : Function.update v i (v i * (v j)⁻¹) = u := by
          rw [hEq]
          funext k
          by_cases hki : k = i
          · subst k
            simp [hij.symm]
          · by_cases hkj : k = j
            · subst k
              simp [hki]
            · simp [hki]
        rw [hEqBack] at hback
        exact hback
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hstep => exact step_symm hstep
  | trans h₁ h₂ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₂ ih₁

theorem nielsenEquivalent_refl {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) : NielsenEquivalent x x :=
  Relation.ReflTransGen.refl

theorem nielsenEquivalent_trans {A : Type*} [Group A] {n : ℕ}
    {x y z : Fin n → A} (hxy : NielsenEquivalent x y)
    (hyz : NielsenEquivalent y z) : NielsenEquivalent x z :=
  Relation.ReflTransGen.trans hxy hyz

theorem nielsenEquivalent_mulLeft {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x (Function.update x i (x j * x i)) := by
  let y : Fin n → A := Function.update x i (x i)⁻¹
  let z : Fin n → A := Function.update y j (y j)⁻¹
  let w : Fin n → A := Function.update z i (z i * z j)
  let q : Fin n → A := Function.update w i (w i)⁻¹
  let r : Fin n → A := Function.update q j (q j)⁻¹
  have hxy : NielsenStep x y := NielsenStep.invert i rfl
  have hyz : NielsenStep y z := NielsenStep.invert j rfl
  have hzw : NielsenStep z w := NielsenStep.mulRight i j hij rfl
  have hwq : NielsenStep w q := NielsenStep.invert i rfl
  have hqr : NielsenStep q r := NielsenStep.invert j rfl
  have hxyzw : NielsenEquivalent x w :=
    Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hxy)
        (Relation.ReflTransGen.single hyz))
      (Relation.ReflTransGen.single hzw)
  have hxyzwq : NielsenEquivalent x q :=
    Relation.ReflTransGen.trans hxyzw (Relation.ReflTransGen.single hwq)
  have hxyzwqr : NielsenEquivalent x r :=
    Relation.ReflTransGen.trans hxyzwq (Relation.ReflTransGen.single hqr)
  have hr : r = Function.update x i (x j * x i) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [r, q, w, z, y, hij, hij.symm]
    · by_cases hkj : k = j
      · subst k
        simp [r, q, w, z, y, hki, hij]
      · simp [r, q, w, z, y, hki, hkj, hij]
  rw [← hr]
  exact hxyzwqr

/-! A conjugation of one entry by another is a composite of elementary moves.
This is the tuple operation used when changing the base point of a folded
graph. -/
theorem nielsenEquivalent_conjugate {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x
      (Function.update x i (x j * x i * (x j)⁻¹)) := by
  let y := Function.update x i (x j * x i)
  have hxy : NielsenEquivalent x y := nielsenEquivalent_mulLeft x i j hij
  have hyz : NielsenEquivalent y
      (Function.update y i (y i * (y j)⁻¹)) :=
    nielsenEquivalent_mulRight_inv y i j hij
  have hxyz := nielsenEquivalent_trans hxy hyz
  have hEq : Function.update y i (y i * (y j)⁻¹) =
      Function.update x i (x j * x i * (x j)⁻¹) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [y, hij.symm, mul_assoc]
    · simp [y, hki]
  rw [hEq] at hxyz
  exact hxyz

theorem nielsenMinimal_tupleFactorLength_le_mulRight_inv {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x i * (x j)⁻¹)) := by
  apply hmin
  exact nielsenEquivalent_mulRight_inv x i j hij

theorem nielsenMinimal_tupleFactorLength_le_mulLeft {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x j * x i)) := by
  exact hmin _ (nielsenEquivalent_mulLeft x i j hij)

theorem nielsenMinimal_no_strict_mulRight_inv_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x i * (x j)⁻¹) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulRight_inv hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x i * (x j)⁻¹) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

theorem nielsenMinimal_no_strict_mulLeft_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x j * x i) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulLeft hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x j * x i) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

theorem nielsenMinimal_nielsenReduced {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x) :
    NielsenReduced x := by
  intro i j hij
  exact ⟨Nat.le_of_not_gt (nielsenMinimal_no_strict_mulRight_descent hmin i j hij),
    Nat.le_of_not_gt (nielsenMinimal_no_strict_mulRight_inv_descent hmin i j hij),
    Nat.le_of_not_gt (nielsenMinimal_no_strict_mulLeft_descent hmin i j hij)⟩

theorem exists_nielsen_reduced {n : ℕ} (x : Fin n → G ∗ H) :
    ∃ y, NielsenEquivalent x y ∧ NielsenReduced y ∧
      tupleFactorLength y = nielsenMinLength x := by
  obtain ⟨y, hy, hmin, hlen⟩ := exists_nielsen_minimal x
  exact ⟨y, hy, nielsenMinimal_nielsenReduced hmin, hlen⟩


end GeneralGrushko
end MarshallHall
