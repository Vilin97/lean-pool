/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConj

/-!
# Extension commutes with an adjacent colour swap

Extending a mixed colouring by one slot and swapping two adjacent
colours are independent operations when the swapped pair lies below
the new slot: the swap acts on the tail, the extension prepends, and
the two commute on the nose (`colourExtend_colourSwap`).

The proof is the corresponding statement for the adjacency sign
(`adjSign_eq_tail`) carried through the word and its permutation.
-/

namespace RS

open CategoryTheory MonoidalCategory
open scoped TensorProduct

variable {k ℓ : ℕ}

private theorem adjSign_eq_tail {n : ℕ} (c : MixedColouring k ℓ (n + 2)) (i : ℕ)
    (h : i + 2 ≤ n + 1) :
    adjSign c ⟨i, by omega⟩ ⟨i + 1, by omega⟩ =
    adjSign (MixedColouring.tail c) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
  unfold adjSign MixedColouring.tail; rfl

private theorem swap_last_eq {n i : ℕ} (h : i + 2 ≤ n + 1) :
    Equiv.swap (⟨i, by omega⟩ : Fin (n + 2)) ⟨i + 1, by omega⟩
      (Fin.last (n + 1)) = Fin.last (n + 1) := by
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2 <;> simp_all [Fin.ext_iff, Fin.val_last] <;> omega

private theorem swap_castSucc_eq {n i : ℕ} (h : i + 2 ≤ n + 1)
    (j : Fin (n + 1)) :
    Equiv.swap (⟨i, by omega⟩ : Fin (n + 2)) ⟨i + 1, by omega⟩
      (j.castSucc) =
    (Equiv.swap (⟨i, by omega⟩ : Fin (n + 1)) ⟨i + 1, by omega⟩ j).castSucc
      := by
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 <;> simp_all [Fin.ext_iff]

/-- Composition of `funTensorFun`, `TensorProduct.map f id`, for
general tensor elements. -/
private theorem funTensorFun_map_id {ι κ : Type} [Fintype ι]
    [Fintype κ]
    (f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (t : (ι → ℂ) ⊗[ℂ] (κ → ℂ)) (x : ι) (y : κ) :
    funTensorFun ι κ (TensorProduct.map f LinearMap.id t) (x, y) =
    f (fun x' => funTensorFun ι κ t (x', y)) x := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, funTensorFun_tmul]
    have : (fun x' => a x' * b y) = b y • a := by
      ext x'; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [map_add, Pi.add_apply, ih₁, ih₂]
    have : (fun x' => funTensorFun ι κ t₁ (x', y) +
      funTensorFun ι κ t₂ (x', y)) =
      (fun x' => funTensorFun ι κ t₁ (x', y)) +
      (fun x' => funTensorFun ι κ t₂ (x', y)) := rfl
    rw [this, map_add, Pi.add_apply]

/-! ### Computation lemmas for `colourPowerStep` applied at a point -/

-- Raised budget: the tensor step equivalence is applied to a
-- `tensorHom` and split over the four graded blocks.
private theorem step_tensorHom_even_apply (d : ℕ)
    (T : colourPower k ℓ d ⟶ colourPower k ℓ d)
    (P : (SuperVect.tensorObj (colourPower k ℓ d) (stdSuperPair k ℓ)).even)
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven}) :
    (colourPowerStep k ℓ d).evenEquiv
      ((SuperVect.tensorHom T (SuperVect.Hom.id (stdSuperPair k ℓ)) :
        SuperVect.Hom _ _).evenMap P) c =
    Sum.elim
      (fun p => funTensorFun _ _ (TensorProduct.map
        (T : SuperVect.Hom _ _).evenMap LinearMap.id P.1) p)
      (fun p => funTensorFun _ _ (TensorProduct.map
        (T : SuperVect.Hom _ _).oddMap LinearMap.id P.2) p)
      (evenSplitEquiv k ℓ d c) := by
  unfold colourPowerStep SuperVect.tensorHom SuperVect.Hom.id
  rfl

/-- The even step equivalence applied at a point. -/
private theorem step_even_apply (d : ℕ)
    (P : (SuperVect.tensorObj (colourPower k ℓ d) (stdSuperPair k ℓ)).even)
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven}) :
    (colourPowerStep k ℓ d).evenEquiv P c =
    Sum.elim (fun p => funTensorFun _ _ P.1 p)
      (fun p => funTensorFun _ _ P.2 p)
      (evenSplitEquiv k ℓ d c) := by
  unfold colourPowerStep
  rfl

-- As for the even component, on the odd half.
private theorem step_tensorHom_odd_apply (d : ℕ)
    (T : colourPower k ℓ d ⟶ colourPower k ℓ d)
    (P : (SuperVect.tensorObj (colourPower k ℓ d) (stdSuperPair k ℓ)).odd)
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven}) :
    (colourPowerStep k ℓ d).oddEquiv
      ((SuperVect.tensorHom T (SuperVect.Hom.id (stdSuperPair k ℓ)) :
        SuperVect.Hom _ _).oddMap P) c =
    Sum.elim
      (fun p => funTensorFun _ _ (TensorProduct.map
        (T : SuperVect.Hom _ _).evenMap LinearMap.id P.1) p)
      (fun p => funTensorFun _ _ (TensorProduct.map
        (T : SuperVect.Hom _ _).oddMap LinearMap.id P.2) p)
      (Equiv.sumComm _ _ (oddSplitEquiv k ℓ d c)) := by
  unfold colourPowerStep SuperVect.tensorHom SuperVect.Hom.id
  rfl

/-- The odd step equivalence applied at a point. -/
private theorem step_odd_apply (d : ℕ)
    (P : (SuperVect.tensorObj (colourPower k ℓ d) (stdSuperPair k ℓ)).odd)
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven}) :
    (colourPowerStep k ℓ d).oddEquiv P c =
    Sum.elim (fun p => funTensorFun _ _ P.1 p)
      (fun p => funTensorFun _ _ P.2 p)
      (Equiv.sumComm _ _ (oddSplitEquiv k ℓ d c)) := by
  unfold colourPowerStep
  rfl

/-! ### How `evenSplitEquiv` interacts with swaps -/

private theorem tail_of_evenSplitEquiv_inl {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven}) (α : Fin k)
    (heq : evenSplitEquiv k ℓ d c = Sum.inl (c₀, α)) :
    MixedColouring.tail c.val = c₀.val := by
  have h1 : c = (evenSplitEquiv k ℓ d).symm (Sum.inl (c₀, α)) := by
    rw [← heq, Equiv.symm_apply_apply]
  ext i
  have h2 := congr_arg (fun x => x.val i.castSucc) h1
  simp only [evenSplitEquiv_symm_inl, colouringSplit_symm_castSucc] at h2
  exact h2

private theorem last_of_evenSplitEquiv_inl {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven}) (α : Fin k)
    (heq : evenSplitEquiv k ℓ d c = Sum.inl (c₀, α)) :
    c.val (Fin.last d) = Sum.inl α := by
  have h1 : c = (evenSplitEquiv k ℓ d).symm (Sum.inl (c₀, α)) := by
    rw [← heq, Equiv.symm_apply_apply]
  have h2 := congr_arg (fun x => x.val (Fin.last d)) h1
  simp only [evenSplitEquiv_symm_inl, colouringSplit_symm_last] at h2
  exact h2

private theorem tail_of_evenSplitEquiv_inr {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven}) (β : Fin (2 * ℓ))
    (heq : evenSplitEquiv k ℓ d c = Sum.inr (c₀, β)) :
    MixedColouring.tail c.val = c₀.val := by
  have h1 : c = (evenSplitEquiv k ℓ d).symm (Sum.inr (c₀, β)) := by
    rw [← heq, Equiv.symm_apply_apply]
  ext i
  have h2 := congr_arg (fun x => x.val i.castSucc) h1
  simp only [evenSplitEquiv_symm_inr, colouringSplit_symm_castSucc] at h2
  exact h2

private theorem last_of_evenSplitEquiv_inr {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven}) (β : Fin (2 * ℓ))
    (heq : evenSplitEquiv k ℓ d c = Sum.inr (c₀, β)) :
    c.val (Fin.last d) = Sum.inr β := by
  have h1 : c = (evenSplitEquiv k ℓ d).symm (Sum.inr (c₀, β)) := by
    rw [← heq, Equiv.symm_apply_apply]
  have h2 := congr_arg (fun x => x.val (Fin.last d)) h1
  simp only [evenSplitEquiv_symm_inr, colouringSplit_symm_last] at h2
  exact h2

/-- `evenSplitEquiv` applied to a swapped colouring, inl case. -/
private theorem evenSplitEquiv_swap_inl {n i : ℕ} (h : i + 2 ≤ n + 1)
    (c : {c : MixedColouring k ℓ (n + 2) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ (n + 1) // c.IsEven}) (α : Fin k)
    (heq : evenSplitEquiv k ℓ (n + 1) c = Sum.inl (c₀, α)) :
    evenSplitEquiv k ℓ (n + 1)
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩, c.prop.comp _⟩ =
    Sum.inl (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      c₀.prop.comp _⟩, α) := by
  suffices hsuff : (evenSplitEquiv k ℓ (n + 1)).symm
      (Sum.inl (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        c₀.prop.comp _⟩, α)) =
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩, c.prop.comp _⟩ by
    rw [← hsuff, Equiv.apply_symm_apply]
  have htail := tail_of_evenSplitEquiv_inl c c₀ α heq
  have hlast := last_of_evenSplitEquiv_inl c c₀ α heq
  ext j
  simp only [evenSplitEquiv_symm_inl]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [colouringSplit_symm_last, Function.comp_apply, swap_last_eq h,
    hlast]
  · simp only [colouringSplit_symm_castSucc, Function.comp_apply,
    swap_castSucc_eq h]
    show c₀.val ((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j') =
      c.val (((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j').castSucc)
    rw [← htail]; rfl

/-- `evenSplitEquiv` applied to a swapped colouring, inr case. -/
private theorem evenSplitEquiv_swap_inr {n i : ℕ} (h : i + 2 ≤ n + 1)
    (c : {c : MixedColouring k ℓ (n + 2) // c.IsEven})
    (c₀ : {c : MixedColouring k ℓ (n + 1) // ¬ c.IsEven}) (β : Fin (2 * ℓ))
    (heq : evenSplitEquiv k ℓ (n + 1) c = Sum.inr (c₀, β)) :
    evenSplitEquiv k ℓ (n + 1)
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩, c.prop.comp _⟩ =
    Sum.inr (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      MixedColouring.not_isEven_comp c₀.prop _⟩, β) := by
  suffices hsuff : (evenSplitEquiv k ℓ (n + 1)).symm
      (Sum.inr (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c₀.prop _⟩, β)) =
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩, c.prop.comp _⟩ by
    rw [← hsuff, Equiv.apply_symm_apply]
  have htail := tail_of_evenSplitEquiv_inr c c₀ β heq
  have hlast := last_of_evenSplitEquiv_inr c c₀ β heq
  ext j
  simp only [evenSplitEquiv_symm_inr]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [colouringSplit_symm_last, Function.comp_apply, swap_last_eq h,
    hlast]
  · simp only [colouringSplit_symm_castSucc, Function.comp_apply,
    swap_castSucc_eq h]
    show c₀.val ((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j') =
      c.val (((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j').castSucc)
    rw [← htail]; rfl

/-! ### Analogous lemmas for `oddSplitEquiv` -/

private theorem tail_of_oddSplitEquiv_inl {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven}) (α : Fin k)
    (heq : oddSplitEquiv k ℓ d c = Sum.inl (c₀, α)) :
    MixedColouring.tail c.val = c₀.val := by
  have h1 : c = (oddSplitEquiv k ℓ d).symm (Sum.inl (c₀, α)) := by
    rw [← heq, Equiv.symm_apply_apply]
  ext i
  have h2 := congr_arg (fun x => x.val i.castSucc) h1
  simp only [oddSplitEquiv_symm_inl, colouringSplit_symm_castSucc] at h2
  exact h2

private theorem last_of_oddSplitEquiv_inl {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven}) (α : Fin k)
    (heq : oddSplitEquiv k ℓ d c = Sum.inl (c₀, α)) :
    c.val (Fin.last d) = Sum.inl α := by
  have h1 : c = (oddSplitEquiv k ℓ d).symm (Sum.inl (c₀, α)) := by
    rw [← heq, Equiv.symm_apply_apply]
  have h2 := congr_arg (fun x => x.val (Fin.last d)) h1
  simp only [oddSplitEquiv_symm_inl, colouringSplit_symm_last] at h2
  exact h2

private theorem tail_of_oddSplitEquiv_inr {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven}) (β : Fin (2 * ℓ))
    (heq : oddSplitEquiv k ℓ d c = Sum.inr (c₀, β)) :
    MixedColouring.tail c.val = c₀.val := by
  have h1 : c = (oddSplitEquiv k ℓ d).symm (Sum.inr (c₀, β)) := by
    rw [← heq, Equiv.symm_apply_apply]
  ext i
  have h2 := congr_arg (fun x => x.val i.castSucc) h1
  simp only [oddSplitEquiv_symm_inr, colouringSplit_symm_castSucc] at h2
  exact h2

private theorem last_of_oddSplitEquiv_inr {d : ℕ}
    (c : {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven}) (β : Fin (2 * ℓ))
    (heq : oddSplitEquiv k ℓ d c = Sum.inr (c₀, β)) :
    c.val (Fin.last d) = Sum.inr β := by
  have h1 : c = (oddSplitEquiv k ℓ d).symm (Sum.inr (c₀, β)) := by
    rw [← heq, Equiv.symm_apply_apply]
  have h2 := congr_arg (fun x => x.val (Fin.last d)) h1
  simp only [oddSplitEquiv_symm_inr, colouringSplit_symm_last] at h2
  exact h2

private theorem oddSplitEquiv_swap_inl {n i : ℕ} (h : i + 2 ≤ n + 1)
    (c : {c : MixedColouring k ℓ (n + 2) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ (n + 1) // ¬ c.IsEven}) (α : Fin k)
    (heq : oddSplitEquiv k ℓ (n + 1) c = Sum.inl (c₀, α)) :
    oddSplitEquiv k ℓ (n + 1)
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c.prop _⟩ =
    Sum.inl (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      MixedColouring.not_isEven_comp c₀.prop _⟩, α) := by
  suffices hsuff : (oddSplitEquiv k ℓ (n + 1)).symm
      (Sum.inl (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c₀.prop _⟩, α)) =
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c.prop _⟩ by
    rw [← hsuff, Equiv.apply_symm_apply]
  have htail := tail_of_oddSplitEquiv_inl c c₀ α heq
  have hlast := last_of_oddSplitEquiv_inl c c₀ α heq
  ext j
  simp only [oddSplitEquiv_symm_inl]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [colouringSplit_symm_last, Function.comp_apply, swap_last_eq h,
    hlast]
  · simp only [colouringSplit_symm_castSucc, Function.comp_apply,
    swap_castSucc_eq h]
    show c₀.val ((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j') =
      c.val (((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j').castSucc)
    rw [← htail]; rfl

private theorem oddSplitEquiv_swap_inr {n i : ℕ} (h : i + 2 ≤ n + 1)
    (c : {c : MixedColouring k ℓ (n + 2) // ¬ c.IsEven})
    (c₀ : {c : MixedColouring k ℓ (n + 1) // c.IsEven}) (β : Fin (2 * ℓ))
    (heq : oddSplitEquiv k ℓ (n + 1) c = Sum.inr (c₀, β)) :
    oddSplitEquiv k ℓ (n + 1)
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c.prop _⟩ =
    Sum.inr (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      c₀.prop.comp _⟩, β) := by
  suffices hsuff : (oddSplitEquiv k ℓ (n + 1)).symm
      (Sum.inr (⟨c₀.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        c₀.prop.comp _⟩, β)) =
      ⟨c.val ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
        MixedColouring.not_isEven_comp c.prop _⟩ by
    rw [← hsuff, Equiv.apply_symm_apply]
  have htail := tail_of_oddSplitEquiv_inr c c₀ β heq
  have hlast := last_of_oddSplitEquiv_inr c c₀ β heq
  ext j
  simp only [oddSplitEquiv_symm_inr]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [colouringSplit_symm_last, Function.comp_apply, swap_last_eq h,
    hlast]
  · simp only [colouringSplit_symm_castSucc, Function.comp_apply,
    swap_castSucc_eq h]
    show c₀.val ((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j') =
      c.val (((Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) j').castSucc)
    rw [← htail]; rfl

/-! ### Main theorem -/

-- Raised budget: both components unfold the step equivalence and
-- the swap at two arities to compare them position by position.
/-- **Extension compatibility of the signed swap**: extending the
adjacent Koszul swap by one position is the adjacent Koszul swap
of the extended power. -/
theorem colourExtend_colourSwap {k ℓ : ℕ} (n i : ℕ)
    (h : i + 2 ≤ n + 1) :
    colourExtend (n + 1) (colourSwap k ℓ (n + 1) i h) =
      colourSwap k ℓ (n + 2) i (by omega) := by
  refine SuperVect.Hom.ext ?_ ?_
  · -- Even component: reduce to step ∘ tensorHom = colourSwap ∘ step
    suffices key : ∀ P,
        (colourPowerStep k ℓ (n + 1)).evenEquiv
          ((SuperVect.tensorHom (colourSwap k ℓ (n + 1) i h)
            (SuperVect.Hom.id (stdSuperPair k ℓ)) :
            SuperVect.Hom _ _).evenMap P) =
        (colourSwap k ℓ (n + 2) i (by omega) :
          SuperVect.Hom _ _).evenMap
          ((colourPowerStep k ℓ (n + 1)).evenEquiv P) by
      ext F
      change (colourPowerStep k ℓ (n + 1)).evenEquiv
        (((SuperVect.tensorHom (colourSwap k ℓ (n + 1) i h)
          (SuperVect.Hom.id (stdSuperPair k ℓ)) :
          SuperVect.Hom _ _).evenMap)
          ((colourPowerStep k ℓ (n + 1)).evenEquiv.symm F)) =
        (colourSwap k ℓ (n + 2) i (by omega) :
          SuperVect.Hom _ _).evenMap F
      rw [key, (colourPowerStep k ℓ (n + 1)).evenEquiv.apply_symm_apply]
    -- Prove key pointwise
    intro P
    funext ⟨c, hc⟩
    rw [step_tensorHom_even_apply]
    change Sum.elim
        (fun p => funTensorFun _ _ (TensorProduct.map
          (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).evenMap
          LinearMap.id P.1) p)
        (fun p => funTensorFun _ _ (TensorProduct.map
          (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).oddMap
          LinearMap.id P.2) p)
        (evenSplitEquiv k ℓ (n + 1) ⟨c, hc⟩) =
      adjSign c ⟨i, by omega⟩ ⟨i + 1, by omega⟩ *
        (colourPowerStep k ℓ (n + 1)).evenEquiv P
          ⟨c ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩, hc.comp _⟩
    rcases heq : evenSplitEquiv k ℓ (n + 1) ⟨c, hc⟩ with ⟨c₀, α⟩ | ⟨c₀, β⟩
    · -- Case inl: last colour even
      simp only [Sum.elim_inl]
      erw [funTensorFun_map_id
        (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).evenMap
        P.1 c₀ α,
        adjSign_eq_tail c (i := i) h,
        tail_of_evenSplitEquiv_inl ⟨c, hc⟩ c₀ α heq,
        step_even_apply,
        evenSplitEquiv_swap_inl h ⟨c, hc⟩ c₀ α heq,
        Sum.elim_inl]; rfl
    · -- Case inr: last colour odd
      simp only [Sum.elim_inr]
      erw [funTensorFun_map_id
        (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).oddMap
        P.2 c₀ β,
        adjSign_eq_tail c (i := i) h,
        tail_of_evenSplitEquiv_inr ⟨c, hc⟩ c₀ β heq,
        step_even_apply,
        evenSplitEquiv_swap_inr h ⟨c, hc⟩ c₀ β heq,
        Sum.elim_inr]; rfl
  · -- Odd component: analogous
    suffices key : ∀ P,
        (colourPowerStep k ℓ (n + 1)).oddEquiv
          ((SuperVect.tensorHom (colourSwap k ℓ (n + 1) i h)
            (SuperVect.Hom.id (stdSuperPair k ℓ)) :
            SuperVect.Hom _ _).oddMap P) =
        (colourSwap k ℓ (n + 2) i (by omega) :
          SuperVect.Hom _ _).oddMap
          ((colourPowerStep k ℓ (n + 1)).oddEquiv P) by
      ext F
      change (colourPowerStep k ℓ (n + 1)).oddEquiv
        (((SuperVect.tensorHom (colourSwap k ℓ (n + 1) i h)
          (SuperVect.Hom.id (stdSuperPair k ℓ)) :
          SuperVect.Hom _ _).oddMap)
          ((colourPowerStep k ℓ (n + 1)).oddEquiv.symm F)) =
        (colourSwap k ℓ (n + 2) i (by omega) :
          SuperVect.Hom _ _).oddMap F
      rw [key, (colourPowerStep k ℓ (n + 1)).oddEquiv.apply_symm_apply]
    intro P
    funext ⟨c, hc⟩
    rw [step_tensorHom_odd_apply]
    change Sum.elim
        (fun p => funTensorFun _ _ (TensorProduct.map
          (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).evenMap
          LinearMap.id P.1) p)
        (fun p => funTensorFun _ _ (TensorProduct.map
          (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).oddMap
          LinearMap.id P.2) p)
        (Equiv.sumComm _ _ (oddSplitEquiv k ℓ (n + 1) ⟨c, hc⟩)) =
      adjSign c ⟨i, by omega⟩ ⟨i + 1, by omega⟩ *
        (colourPowerStep k ℓ (n + 1)).oddEquiv P
          ⟨c ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
            MixedColouring.not_isEven_comp hc _⟩
    rcases heq : oddSplitEquiv k ℓ (n + 1) ⟨c, hc⟩ with ⟨c₀, α⟩ | ⟨c₀, β⟩
    · -- oddSplitEquiv c = inl(c₀, α): c₀ odd, α even colour
      simp only [Equiv.sumComm_apply, Sum.swap_inl, Sum.elim_inr]
      erw [funTensorFun_map_id
        (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).oddMap
        P.2 c₀ α,
        adjSign_eq_tail c (i := i) h,
        tail_of_oddSplitEquiv_inl ⟨c, hc⟩ c₀ α heq,
        step_odd_apply,
        oddSplitEquiv_swap_inl h ⟨c, hc⟩ c₀ α heq,
        Equiv.sumComm_apply, Sum.swap_inl, Sum.elim_inr]; rfl
    · -- oddSplitEquiv c = inr(c₀, β): c₀ even, β odd colour
      simp only [Equiv.sumComm_apply, Sum.swap_inr, Sum.elim_inl]
      erw [funTensorFun_map_id
        (colourSwap k ℓ (n + 1) i h : SuperVect.Hom _ _).evenMap
        P.1 c₀ β,
        adjSign_eq_tail c (i := i) h,
        tail_of_oddSplitEquiv_inr ⟨c, hc⟩ c₀ β heq,
        step_odd_apply,
        oddSplitEquiv_swap_inr h ⟨c, hc⟩ c₀ β heq,
        Equiv.sumComm_apply, Sum.swap_inr, Sum.elim_inl]; rfl

end RS
