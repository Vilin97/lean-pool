/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.FibreCard

/-!
# Mixed fixed-point decomposition

Decomposes the subtype of colourings fixed by a lifted permutation
`viaEmbeddingHom (castLEEmb h) σ` into a product of the fixed colourings
on the first `m` coordinates and free colourings on the tail.
-/

@[expose] public section

namespace RS

open Finset Equiv.Perm Fin

variable {m n N : ℕ}

/-- The tail has the expected size. -/
theorem card_tail (h : m ≤ n) :
    Fintype.card {i : Fin n // m ≤ (i : ℕ)} = n - m := by
  have : Fintype.card {i : Fin n // m ≤ (i : ℕ)} =
      Fintype.card {i : Fin n // ¬ (i : ℕ) < m} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Nat.not_lt.symm))
  rw [this, Fintype.card_subtype_compl (p := fun i : Fin n => (i : ℕ) < m),
    Fintype.card_fin, Fintype.card_fin_lt_of_le h]

private theorem lift_castLE (h : m ≤ n) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) (Fin.castLE h j) =
      Fin.castLE h (σ j) := by
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  exact Equiv.Perm.viaEmbedding_apply σ (Fin.castLEEmb h) j

private theorem castLEEmb_range_subset (h : m ≤ n) (i : Fin n)
    (hi : i ∈ Set.range (Fin.castLEEmb h)) : (i : ℕ) < m := by
  obtain ⟨j, rfl⟩ := hi
  exact j.2

open scoped Classical in
/-- **The fixed-point decomposition**: a colouring fixed by a lifted
permutation is a fixed colouring on the head together with a free
one on the tail, which the lift does not move. -/
noncomputable def mixedFixedEquiv (h : m ≤ n) (σ : Equiv.Perm (Fin m)) :
    {f : Fin n → Fin N //
      f ∘ ⇑(Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) = f} ≃
    {g : Fin m → Fin N // g ∘ ⇑σ = g} ×
      ({i : Fin n // m ≤ (i : ℕ)} → Fin N) where
  toFun f :=
    (⟨f.1 ∘ Fin.castLE h, by
        funext j
        simp only [Function.comp_apply]
        have hf := congr_fun f.2 (Fin.castLE h j)
        simp only [Function.comp_apply] at hf
        rw [lift_castLE h σ j] at hf
        exact hf⟩,
      fun i => f.1 i.1)
  invFun p :=
    ⟨fun i => if hi : (i : ℕ) < m then p.1.1 ⟨i, hi⟩ else p.2 ⟨i, by omega⟩, by
      funext i
      simp only [Function.comp_apply]
      by_cases hi : (i : ℕ) < m
      · have heq : (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) i =
            Fin.castLE h (σ ⟨i, hi⟩) := by
          conv_lhs => rw [show i = Fin.castLE h ⟨i, hi⟩ from Fin.ext (by simp)]
          exact lift_castLE h σ ⟨i, hi⟩
        rw [heq]
        have hσval : (Fin.castLE h (σ ⟨i, hi⟩) : ℕ) < m := (σ ⟨i, hi⟩).2
        rw [dite_eq_left hσval, dite_eq_left hi]
        have hfix := congr_fun p.1.2 ⟨i, hi⟩
        simp only [Function.comp_apply] at hfix
        rw [show (⟨↑(Fin.castLE h (σ ⟨↑i, hi⟩)), hσval⟩ : Fin m) = σ ⟨i, hi⟩
          from Fin.ext rfl]
        exact hfix
      · have hmem : i ∉ Set.range (Fin.castLEEmb h) := by
          intro hmem; exact hi (castLEEmb_range_subset h i hmem)
        rw [Equiv.Perm.viaEmbeddingHom_apply,
          Equiv.Perm.viaEmbedding_apply_of_notMem σ (Fin.castLEEmb h) i hmem]⟩
  left_inv f := by
    apply Subtype.ext; funext i; simp only
    by_cases hi : (i : ℕ) < m
    · rw [dite_eq_left hi]; simp only [Function.comp_apply]; congr 1
    · rw [dite_eq_right hi]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; funext j; simp only [Function.comp_apply]
      rw [dite_eq_left (show (Fin.castLE h j : ℕ) < m from j.2)]; congr 1
    · funext ⟨i, hi⟩; simp only
      rw [dite_eq_right (show ¬ (i : ℕ) < m by omega)]

/-- The colour counts add across the split. -/
theorem mixedFixedEquiv_symm_fibreCard (h : m ≤ n)
    (σ : Equiv.Perm (Fin m))
    (g : {g : Fin m → Fin N // g ∘ ⇑σ = g})
    (t : {i : Fin n // m ≤ (i : ℕ)} → Fin N) (c : Fin N) :
    fibreCard ((mixedFixedEquiv h σ).symm (g, t)).1 c =
      fibreCard g.1 c +
      (Finset.univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} =>
        t i = c)).card := by
  classical
  simp only [fibreCard]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype,
    ← Fintype.card_subtype (fun i : {i : Fin n // m ≤ (i : ℕ)} => t i = c),
    ← Fintype.card_sum]
  apply Fintype.card_congr
  -- {i : Fin n // F i = c} ≃ {j : Fin m // g j = c} ⊕ {s : tail // t s = c}
  -- F = ((mixedFixedEquiv h σ).symm (g, t)).1, definitionally the dite function
  have glue_eq : ∀ (i : Fin n),
      ((mixedFixedEquiv h σ).symm (g, t)).1 i =
        if hi : (i : ℕ) < m then g.1 ⟨i, hi⟩
        else t ⟨i, by omega⟩ := fun _ => rfl
  refine {
    toFun := fun ⟨i, hi⟩ =>
      if him : (i : ℕ) < m then
        Sum.inl ⟨⟨i, him⟩, by rw [glue_eq, dite_eq_left him] at hi; exact hi⟩
      else
        Sum.inr
          ⟨⟨i, Nat.not_lt.mp him⟩, by rw [glue_eq, dite_eq_right him] at hi; exact hi⟩
    invFun := fun x => x.elim
      (fun ⟨j, hj⟩ => ⟨Fin.castLE h j, by
        have : (Fin.castLE h j : ℕ) < m := j.2
        rw [glue_eq, dite_eq_left this]; convert hj using 1; exact Fin.ext rfl⟩)
      (fun ⟨s, hs⟩ => ⟨s.1, by
        have : ¬ (s.1 : ℕ) < m := Nat.not_lt.mpr s.2
        rw [glue_eq, dite_eq_right this]
        exact (congr_arg t (Subtype.ext rfl)).trans hs⟩)
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨i, hi⟩
    simp only
    split_ifs with him
    · exact Subtype.ext rfl
    · exact Subtype.ext rfl
  · rintro (⟨j, hj⟩ | ⟨s, hs⟩)
    · dsimp only [Sum.elim_inl]
      rw [dite_eq_left (show (Fin.castLE h j : ℕ) < m from j.2)]
      exact congr_arg Sum.inl (Subtype.ext (Fin.ext rfl))
    · dsimp only [Sum.elim_inr]
      simp only [dite_eq_right (show ¬ (s.1 : ℕ) < m from Nat.not_lt.mpr s.2)]

end RS
