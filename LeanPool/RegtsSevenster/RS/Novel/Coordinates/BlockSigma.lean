/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarPeel

/-!
# The block sigma equivalence

The block enumeration pairs a block index with an offset within the
block to enumerate the concatenated total.
-/

namespace RS

/-- Split the sigma over a cons list into head + tail. -/
private def blockSigmaSplitFun (d : ℕ) (ds : List ℕ) :
    (Σ v : Fin (ds.length + 1), Fin ((d :: ds).get v)) →
      Fin d ⊕ (Σ w : Fin ds.length, Fin (ds.get w))
  | ⟨⟨0, _⟩, j⟩ => Sum.inl j
  | ⟨⟨v + 1, hv⟩, j⟩ => Sum.inr ⟨⟨v, by omega⟩, j⟩

/-- Inverse of the split. -/
private def blockSigmaSplitInv (d : ℕ) (ds : List ℕ) :
    Fin d ⊕ (Σ w : Fin ds.length, Fin (ds.get w)) →
      (Σ v : Fin (ds.length + 1), Fin ((d :: ds).get v))
  | Sum.inl j => ⟨⟨0, by omega⟩, j⟩
  | Sum.inr ⟨w, j⟩ => ⟨w.succ, j⟩

/-- The sigma over a cons list splits as head + tail. -/
private def blockSigmaSplit (d : ℕ) (ds : List ℕ) :
    (Σ v : Fin (ds.length + 1), Fin ((d :: ds).get v)) ≃
      Fin d ⊕ (Σ w : Fin ds.length, Fin (ds.get w)) where
  toFun := blockSigmaSplitFun d ds
  invFun := blockSigmaSplitInv d ds
  left_inv := by
    rintro ⟨⟨v, hv⟩, j⟩
    match v with
    | 0 => rfl
    | v + 1 => rfl
  right_inv := by
    rintro (j | ⟨w, j⟩)
    · rfl
    · rfl

/-- The block enumeration: a block index and an offset within the
block enumerate the concatenated total. -/
noncomputable def blockSigmaEquiv : (ds : List ℕ) →
    (Σ v : Fin ds.length, Fin (ds.get v)) ≃ Fin ds.sum
  | [] =>
    haveI : IsEmpty (Σ v : Fin ([] : List ℕ).length,
        Fin (([] : List ℕ).get v)) :=
      ⟨fun p => p.1.elim0⟩
    haveI : IsEmpty (Fin ([] : List ℕ).sum) :=
      ⟨fun i => i.elim0⟩
    Equiv.equivOfIsEmpty _ _
  | d :: ds =>
    (blockSigmaSplit d ds).trans
      ((Equiv.sumCongr (Equiv.refl (Fin d)) (blockSigmaEquiv ds)).trans
        (finSumFinEquiv.trans (finCongr (by simp [List.sum_cons]))))

/-- The block enumeration lands in its own block. -/
theorem blockAssign_blockSigmaEquiv (ds : List ℕ)
    (p : Σ v : Fin ds.length, Fin (ds.get v)) :
    blockAssign ds (blockSigmaEquiv ds p) = p.1 := by
  induction ds with
  | nil => exact p.1.elim0
  | cons d ds ih =>
    obtain ⟨⟨v, hv⟩, j⟩ := p
    match v with
    | 0 =>
      -- p = ⟨⟨0, _⟩, j⟩ where j : Fin d
      -- blockSigmaEquiv (d :: ds) ⟨⟨0, _⟩, j⟩ goes through:
      --   split → inl j
      --   sumCongr → inl j
      --   finSumFinEquiv → castAdd ds.sum j
      --   finCongr → same val
      show blockAssign (d :: ds) (blockSigmaEquiv (d :: ds) ⟨⟨0, hv⟩, j⟩) =
        ⟨0, hv⟩
      -- The equiv value has val = j.val < d
      have hval : (blockSigmaEquiv (d :: ds) ⟨⟨0, hv⟩, j⟩).val = j.val := rfl
      have hlt : (blockSigmaEquiv (d :: ds) ⟨⟨0, hv⟩, j⟩).val < d := by
        rw [hval]; exact j.isLt
      unfold blockAssign
      rw [dif_pos hlt]
    | v + 1 =>
      -- p = ⟨⟨v+1, hv⟩, j⟩ where j : Fin (ds.get ⟨v, _⟩)
      show blockAssign (d :: ds) (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩) =
        ⟨v + 1, hv⟩
      -- The equiv value has val = d + (blockSigmaEquiv ds ⟨⟨v, _⟩, j⟩).val
      have hlc : (d :: ds).length = ds.length + 1 := rfl
      have hw : v < ds.length := by omega
      have hval : (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨v, hw⟩, j⟩).val := rfl
      have hnlt : ¬ (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val < d := by
        rw [hval]; omega
      unfold blockAssign
      rw [dif_neg hnlt]
      -- Goal: (blockAssign ds ⟨val - d, _⟩).succ = ⟨v + 1, hv⟩
      have hisLt : (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val - d < ds.sum
        := by
        have := (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).isLt
        simp only [List.sum_cons] at this
        omega
      suffices hsuff : blockAssign ds
          (⟨(blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val - d,
            hisLt⟩ : Fin ds.sum) = ⟨v, hw⟩ by
        exact congrArg Fin.succ hsuff
      have hsub : (blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val - d =
          (blockSigmaEquiv ds ⟨⟨v, hw⟩, j⟩).val := by
        rw [hval]; omega
      have harg : (⟨(blockSigmaEquiv (d :: ds) ⟨⟨v + 1, hv⟩, j⟩).val - d,
          hisLt⟩ : Fin ds.sum) =
          blockSigmaEquiv ds ⟨⟨v, hw⟩, j⟩ :=
        Fin.ext hsub
      rw [congrArg (blockAssign ds) harg]
      exact ih ⟨⟨v, hw⟩, j⟩

end RS
