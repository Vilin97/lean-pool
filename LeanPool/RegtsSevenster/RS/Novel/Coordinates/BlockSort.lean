/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarPeel

/-!
# Sorting a multi-star into blocks

An arbitrary vertex assignment of a multi-star is sorted into
block form: the degree list records the fibre sizes in vertex
order, and the sort equivalence regroups the slots fibre by
fibre.  Relabelling along the sort turns the multi-star into the
block-assigned form, ready for the block factorization.
-/

namespace RS

section Sorting

variable {n m : ℕ} (assign : Fin n → Fin m)

/-- The degree list of an assignment: fibre sizes in vertex
order. -/
noncomputable def degList : List ℕ :=
  List.ofFn (fun v : Fin m => Fintype.card {i // assign i = v})

/-- The degree list has one entry per vertex. -/
theorem degList_length : (degList assign).length = m := by
  simp [degList]

/-- Each entry is that vertex's fibre size. -/
theorem degList_get (w : Fin (degList assign).length) :
    (degList assign).get w =
      Fintype.card {i // assign i =
        finCongr (degList_length assign) w} := by
  rw [List.get_eq_getElem]
  simp only [degList]
  rw [List.getElem_ofFn]
  exact congrArg (fun v => Fintype.card {i // assign i = v})
    (Fin.ext rfl)

/-- The fibre sizes sum to the total. -/
theorem sum_card_fibres :
    ∑ v : Fin m, Fintype.card {i // assign i = v} = n := by
  rw [← Fintype.card_sigma,
    Fintype.card_congr (_root_.Equiv.sigmaFiberEquiv assign),
    Fintype.card_fin]

/-- The degrees sum to the slot count: the fibres partition the
slots. -/
theorem degList_sum : (degList assign).sum = n := by
  rw [degList, List.sum_ofFn]
  exact sum_card_fibres assign

/-- The block-form index space has the right cardinality. -/
theorem degList_card_sigma :
    Fintype.card
      (Σ w : Fin (degList assign).length,
        Fin ((degList assign).get w)) = n := by
  rw [Fintype.card_sigma]
  rw [show ∑ w : Fin (degList assign).length,
      Fintype.card (Fin ((degList assign).get w)) =
      ∑ v : Fin m, Fintype.card {i // assign i = v} from
    Fintype.sum_equiv (finCongr (degList_length assign)) _ _
      (fun w => by
        rw [Fintype.card_fin, degList_get assign w])]
  exact sum_card_fibres assign

/-- The sort map: a slot goes to its vertex block at its
enumerated offset within the fibre. -/
noncomputable def sortFun (i : Fin n) :
    Σ w : Fin (degList assign).length,
      Fin ((degList assign).get w) :=
  ⟨finCongr (degList_length assign).symm (assign i),
    finCongr (degList_get assign _).symm
      (Fintype.equivFin _
        ⟨i, (Fin.ext rfl :
          assign i = finCongr (degList_length assign)
            (finCongr (degList_length assign).symm
              (assign i)))⟩)⟩

/-- The unsort map: read the fibre element back off. -/
noncomputable def unsortFun
    (p : Σ w : Fin (degList assign).length,
      Fin ((degList assign).get w)) : Fin n :=
  ((Fintype.equivFin
      {i // assign i = finCongr (degList_length assign)
        p.1}).symm
    (finCongr (degList_get assign p.1) p.2)).val

/-- Unsorting undoes sorting. -/
theorem unsort_sort (i : Fin n) :
    unsortFun assign (sortFun assign i) = i :=
  congrArg Subtype.val
    ((Fintype.equivFin
      {j // assign j = finCongr (degList_length assign)
        (sortFun assign i).1}).symm_apply_apply
      ⟨i, Fin.ext rfl⟩)

/-- So the sort is a bijection of slots. -/
theorem sortFun_bijective : Function.Bijective (sortFun assign) := by
  have hinj : Function.Injective (sortFun assign) :=
    Function.LeftInverse.injective (unsort_sort assign)
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by rw [Fintype.card_fin, degList_card_sigma]⟩

/-- **The sort equivalence** onto the block index space. -/
noncomputable def sortSigma :
    Fin n ≃ Σ w : Fin (degList assign).length,
      Fin ((degList assign).get w) :=
  _root_.Equiv.ofBijective _ (sortFun_bijective assign)

/-- The sorted slot's block index is its vertex. -/
theorem sortSigma_fst (i : Fin n) :
    (sortSigma assign i).1 =
      finCongr (degList_length assign).symm (assign i) := rfl

end Sorting

section Relabel

/-- **Sorting a multi-star**: a slot equivalence intertwining the
assignments (through a vertex identification) relabels one
multi-star onto the other. -/
noncomputable def multiStarCompRelabel {V V' : Type}
    [Fintype V] [Fintype V'] {n N : ℕ}
    (assign : Fin n → V) (c : ℕ) (σ : Fin n ≃ Fin N)
    (b : Fin N → V') (e : V ≃ V')
    (hb : ∀ i, b (σ i) = e (assign i)) :
    (multiStar assign c).Equiv
      ((multiStar b c).relabel σ.symm) where
  flagEquiv := _root_.Equiv.sumCongr σ σ
  vertexEquiv := e
  attach_comm := fun g => by
    rcases g with i | i
    · show Sum.inl (b (σ i)) =
        (Sum.inl (assign i) : V ⊕ Fin n).map e id
      rw [hb i]
      rfl
    · show Sum.inr (σ.symm (σ i)) =
        (Sum.inr i : V ⊕ Fin n).map e id
      rw [σ.symm_apply_apply]
      rfl
  pairing_comm := fun g => by
    rcases g with i | i <;> rfl
  circles_eq := rfl

end Relabel

end RS
