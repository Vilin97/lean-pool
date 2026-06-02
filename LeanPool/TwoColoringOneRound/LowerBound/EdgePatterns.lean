/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.TwoColoringOneRound.LowerBound.Defs

/-!
Reusable lemmas for counting edges with coordinate-wise constraints relative to a threshold `two`.

These are used in auxiliary “sanity check” and “upper bound” files to avoid repeating large
case-bashy equivalence proofs.
-/

namespace Distributed2Coloring.LowerBound


namespace EdgePatterns

variable {n : Nat} (two : Sym n)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small : Type := Set.Iio two
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big : Type := Set.Ici two

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Pat0000 (e : Edge n) : Prop :=
  e.1 0 < two ∧ e.1 1 < two ∧ e.1 2 < two ∧ e.1 3 < two

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Pat1111 (e : Edge n) : Prop :=
  two ≤ e.1 0 ∧ two ≤ e.1 1 ∧ two ≤ e.1 2 ∧ two ≤ e.1 3

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Pat1001 (e : Edge n) : Prop :=
  two ≤ e.1 0 ∧ e.1 1 < two ∧ e.1 2 < two ∧ two ≤ e.1 3

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Pat0110 (e : Edge n) : Prop :=
  e.1 0 < two ∧ two ≤ e.1 1 ∧ two ≤ e.1 2 ∧ e.1 3 < two

instance : DecidablePred (Pat0000 (two := two)) := by
  intro e
  dsimp [Pat0000]
  infer_instance

instance : DecidablePred (Pat1111 (two := two)) := by
  intro e
  dsimp [Pat1111]
  infer_instance

instance : DecidablePred (Pat1001 (two := two)) := by
  intro e
  dsimp [Pat1001]
  infer_instance

instance : DecidablePred (Pat0110 (two := two)) := by
  intro e
  dsimp [Pat0110]
  infer_instance

private lemma big_ne_small {n : Nat} {two : Sym n} (x : Big (two := two)) (y : Small (two := two)) :
    (x.1 : Sym n) ≠ y.1 := by
  intro hxy
  have hx : two ≤ (y.1 : Sym n) := hxy ▸ x.2
  exact (not_lt_of_ge hx) y.2

private lemma small_ne_big {n : Nat} {two : Sym n} (x : Small (two := two)) (y : Big (two := two)) :
    (x.1 : Sym n) ≠ y.1 := by
  intro hxy
  exact big_ne_small (two := two) (x := y) (y := x) hxy.symm

private def bigValEmbedding {n : Nat} {two : Sym n} : Big (two := two) ↪ Sym n :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def smallValEmbedding {n : Nat} {two : Sym n} : Small (two := two) ↪ Sym n :=
  ⟨Subtype.val, Subtype.val_injective⟩

private lemma disjoint_range_big_small {n : Nat} {two : Sym n}
    (ad : Fin 2 ↪ Big (two := two)) (bc : Fin 2 ↪ Small (two := two)) :
    Disjoint (Set.range (ad.trans bigValEmbedding)) (Set.range (bc.trans smallValEmbedding)) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, h⟩
  have h' : (ad i).1 = (bc j).1 := by
    simpa [bigValEmbedding, smallValEmbedding] using h.symm
  exact (big_ne_small (two := two) (x := ad i) (y := bc j) h').elim

private lemma disjoint_range_small_big {n : Nat} {two : Sym n}
    (bc : Fin 2 ↪ Small (two := two)) (ad : Fin 2 ↪ Big (two := two)) :
    Disjoint (Set.range (bc.trans smallValEmbedding)) (Set.range (ad.trans bigValEmbedding)) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, h⟩
  have h' : (bc i).1 = (ad j).1 := by
    simpa [bigValEmbedding, smallValEmbedding] using h.symm
  exact (small_ne_big (two := two) (x := bc i) (y := ad j) h').elim

private def outerPos : Fin 2 ↪ Fin 4 where
  toFun
    | 0 => 0
    | _ => 3
  inj' := by decide

private def innerPos : Fin 2 ↪ Fin 4 where
  toFun
    | 0 => 1
    | _ => 2
  inj' := by decide

private def interleavePos : Fin 4 ↪ Fin 4 where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | _ => 1
  inj' := by decide

@[simp] private lemma outerPos_zero : outerPos 0 = (0 : Fin 4) := rfl
@[simp] private lemma outerPos_one : outerPos 1 = (3 : Fin 4) := rfl
@[simp] private lemma innerPos_zero : innerPos 0 = (1 : Fin 4) := rfl
@[simp] private lemma innerPos_one : innerPos 1 = (2 : Fin 4) := rfl
@[simp] private lemma interleavePos_zero : interleavePos 0 = (0 : Fin 4) := rfl
@[simp] private lemma interleavePos_one : interleavePos 1 = (2 : Fin 4) := rfl
@[simp] private lemma interleavePos_two : interleavePos 2 = (3 : Fin 4) := rfl
@[simp] private lemma interleavePos_three : interleavePos 3 = (1 : Fin 4) := rfl

private def embedding1001 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Fin 4 ↪ Sym n := by
  let ad' : Fin 2 ↪ Sym n := ad.trans bigValEmbedding
  let bc' : Fin 2 ↪ Sym n := bc.trans smallValEmbedding
  exact interleavePos.trans
    (Fin.Embedding.append (x := ad') (y := bc')
      (disjoint_range_big_small (two := two) ad bc))

private def embedding0110 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Fin 4 ↪ Sym n := by
  let bc' : Fin 2 ↪ Sym n := bc.trans smallValEmbedding
  let ad' : Fin 2 ↪ Sym n := ad.trans bigValEmbedding
  exact interleavePos.trans
    (Fin.Embedding.append (x := bc') (y := ad')
      (disjoint_range_small_big (two := two) bc ad))

private def tuple1001 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => (ad 0).1
    | 1 => (bc 0).1
    | 2 => (bc 1).1
    | _ => (ad 1).1

private def tuple0110 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => (bc 0).1
    | 1 => (ad 0).1
    | 2 => (ad 1).1
    | _ => (bc 1).1

private lemma tuple1001_eq_embedding1001 {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) :
    tuple1001 two ad bc = embedding1001 two ad bc := by
  funext i
  fin_cases i <;> rfl

private lemma tuple0110_eq_embedding0110 {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) :
    tuple0110 two ad bc = embedding0110 two ad bc := by
  funext i
  fin_cases i <;> rfl

private lemma tuple1001_injective {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Function.Injective (tuple1001 two ad bc) := by
  simpa [tuple1001_eq_embedding1001 (two := two) ad bc] using
    (embedding1001 two ad bc).injective

private lemma tuple0110_injective {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Function.Injective (tuple0110 two ad bc) := by
  simpa [tuple0110_eq_embedding0110 (two := two) ad bc] using
    (embedding0110 two ad bc).injective

theorem card_pat0000 :
    Fintype.card {e : Edge n // Pat0000 (two := two) e}
      = (Fintype.card (Small (two := two))).descFactorial 4 := by
  classical
  let toEmb : {e : Edge n // Pat0000 (two := two) e} → (Fin 4 ↪ Small (two := two)) :=
    fun e =>
      (⟨e.1.1, e.1.2⟩ : Fin 4 ↪ Sym n).codRestrict (Set.Iio two) (by
        intro i
        fin_cases i
        · simpa [Pat0000] using e.2.1
        · simpa [Pat0000] using e.2.2.1
        · simpa [Pat0000] using e.2.2.2.1
        · simpa [Pat0000] using e.2.2.2.2)
  let ofEmb : (Fin 4 ↪ Small (two := two)) → {e : Edge n // Pat0000 (two := two) e} :=
    fun x =>
      ⟨⟨fun i => (x i).1, by
          intro i j hij
          exact x.injective (Subtype.ext hij)⟩,
        ⟨(x 0).2, (x 1).2, (x 2).2, (x 3).2⟩⟩
  have hEquiv : {e : Edge n // Pat0000 (two := two) e} ≃ (Fin 4 ↪ Small (two := two)) :=
    { toFun := toEmb
      invFun := ofEmb
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rfl
      right_inv := by
        intro x
        ext i
        rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat0000 (two := two) e}
        = Fintype.card (Fin 4 ↪ Small (two := two)) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq]

theorem card_pat1111 :
    Fintype.card {e : Edge n // Pat1111 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 4 := by
  classical
  let toEmb : {e : Edge n // Pat1111 (two := two) e} → (Fin 4 ↪ Big (two := two)) :=
    fun e =>
      (⟨e.1.1, e.1.2⟩ : Fin 4 ↪ Sym n).codRestrict (Set.Ici two) (by
        intro i
        fin_cases i
        · simpa [Pat1111] using e.2.1
        · simpa [Pat1111] using e.2.2.1
        · simpa [Pat1111] using e.2.2.2.1
        · simpa [Pat1111] using e.2.2.2.2)
  let ofEmb : (Fin 4 ↪ Big (two := two)) → {e : Edge n // Pat1111 (two := two) e} :=
    fun x =>
      ⟨⟨fun i => (x i).1, by
          intro i j hij
          exact x.injective (Subtype.ext hij)⟩,
        ⟨(x 0).2, (x 1).2, (x 2).2, (x 3).2⟩⟩
  have hEquiv : {e : Edge n // Pat1111 (two := two) e} ≃ (Fin 4 ↪ Big (two := two)) :=
    { toFun := toEmb
      invFun := ofEmb
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rfl
      right_inv := by
        intro x
        ext i
        rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat1111 (two := two) e}
        = Fintype.card (Fin 4 ↪ Big (two := two)) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq]

theorem card_pat1001 :
    Fintype.card {e : Edge n // Pat1001 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 2
          * (Fintype.card (Small (two := two))).descFactorial 2 := by
  classical
  let toProd : {e : Edge n // Pat1001 (two := two) e} →
      (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    fun e =>
      let emb : Fin 4 ↪ Sym n := ⟨e.1.1, e.1.2⟩
      ( (outerPos.trans emb).codRestrict (Set.Ici two) (by
            intro i
            fin_cases i
            · simpa [emb, Pat1001] using e.2.1
            · simpa [emb, Pat1001] using e.2.2.2.2)
      , (innerPos.trans emb).codRestrict (Set.Iio two) (by
            intro i
            fin_cases i
            · simpa [emb, Pat1001] using e.2.2.1
            · simpa [emb, Pat1001] using e.2.2.2.1) )
  let ofProd : (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) →
      {e : Edge n // Pat1001 (two := two) e} :=
    fun p =>
      let ad := p.1
      let bc := p.2
      ⟨⟨tuple1001 two ad bc, tuple1001_injective (two := two) ad bc⟩,
        ⟨(ad 0).2, (bc 0).2, (bc 1).2, (ad 1).2⟩⟩
  have hEquiv : {e : Edge n // Pat1001 (two := two) e}
      ≃ (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    { toFun := toProd
      invFun := ofProd
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        cases p with
        | mk ad bc =>
            apply Prod.ext <;> ext i <;> fin_cases i <;> rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat1001 (two := two) e}
        = Fintype.card ((Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two))) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq, Fintype.card_prod]

theorem card_pat0110 :
    Fintype.card {e : Edge n // Pat0110 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 2
          * (Fintype.card (Small (two := two))).descFactorial 2 := by
  classical
  let toProd : {e : Edge n // Pat0110 (two := two) e} →
      (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    fun e =>
      let emb : Fin 4 ↪ Sym n := ⟨e.1.1, e.1.2⟩
      ( (innerPos.trans emb).codRestrict (Set.Ici two) (by
            intro i
            fin_cases i
            · simpa [emb, Pat0110] using e.2.2.1
            · simpa [emb, Pat0110] using e.2.2.2.1)
      , (outerPos.trans emb).codRestrict (Set.Iio two) (by
            intro i
            fin_cases i
            · simpa [emb, Pat0110] using e.2.1
            · simpa [emb, Pat0110] using e.2.2.2.2) )
  let ofProd : (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) →
      {e : Edge n // Pat0110 (two := two) e} :=
    fun p =>
      let ad := p.1
      let bc := p.2
      ⟨⟨tuple0110 two ad bc, tuple0110_injective (two := two) ad bc⟩,
        ⟨(bc 0).2, (ad 0).2, (ad 1).2, (bc 1).2⟩⟩
  have hEquiv : {e : Edge n // Pat0110 (two := two) e}
      ≃ (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    { toFun := toProd
      invFun := ofProd
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        cases p with
        | mk ad bc =>
            apply Prod.ext <;> ext i <;> fin_cases i <;> rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat0110 (two := two) e}
        = Fintype.card ((Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two))) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq, Fintype.card_prod]

end EdgePatterns

end Distributed2Coloring.LowerBound
