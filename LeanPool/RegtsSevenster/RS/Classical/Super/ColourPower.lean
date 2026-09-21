/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdSuper

/-!
# The colouring model of tensor powers

The `d`-th tensor power of the standard super space
`stdSuperPair k ℓ` in the pair-component model is an exponentially
nested product.  The colouring model flattens it: a basis vector
of the power is a *mixed colouring* — each of the `d` positions
carries an even colour in `Fin k` or an odd colour in
`Fin (2ℓ)` — and the power is the space of functions on
colourings, graded by the parity of the odd support.  All the
§5–6 network maps become colouring combinatorics in this model,
meshing directly with the mixed partition function's
Definition-5 sum.
-/

open scoped TensorProduct

namespace RS

/-- A mixed colouring of `d` tensor positions: each position an
even colour or an odd colour. -/
abbrev MixedColouring (k ℓ d : ℕ) : Type :=
  Fin d → (Fin k ⊕ Fin (2 * ℓ))

namespace MixedColouring

/-- Colourings of finitely many slots by finitely many colours are
finite in number. -/
instance (k ℓ d : ℕ) : Fintype (MixedColouring k ℓ d) :=
  inferInstanceAs (Fintype (Fin d → Fin k ⊕ Fin (2 * ℓ)))

/-- And can be compared. -/
instance (k ℓ d : ℕ) : DecidableEq (MixedColouring k ℓ d) :=
  inferInstanceAs (DecidableEq (Fin d → Fin k ⊕ Fin (2 * ℓ)))

/-- The odd positions of a colouring. -/
def oddSet {k ℓ d : ℕ} (c : MixedColouring k ℓ d) :
    Finset (Fin d) :=
  Finset.univ.filter (fun i => (c i).isRight)

/-- A colouring is even when its odd support has even size. -/
def IsEven {k ℓ d : ℕ} (c : MixedColouring k ℓ d) : Prop :=
  Even c.oddSet.card

/-- Whether a colouring is even is decidable. -/
instance {k ℓ d : ℕ} (c : MixedColouring k ℓ d) :
    Decidable c.IsEven :=
  inferInstanceAs (Decidable (Even c.oddSet.card))

end MixedColouring

/-- **The colouring model** of the `d`-th tensor power of the
standard super space: functions on mixed colourings, graded by
the parity of the odd support. -/
noncomputable def colourPower (k ℓ d : ℕ) : SuperVect where
  even := {c : MixedColouring k ℓ d // c.IsEven} → ℂ
  odd := {c : MixedColouring k ℓ d // ¬ c.IsEven} → ℂ

/-- A grading-preserving linear equivalence of super vector
spaces. -/
structure SuperLinearEquiv (V W : SuperVect) where
  /-- The even component. -/
  evenEquiv : V.even ≃ₗ[ℂ] W.even
  /-- The odd component. -/
  oddEquiv : V.odd ≃ₗ[ℂ] W.odd

/-- The tensor product of function spaces on finite types is the
function space on the product. -/
noncomputable def funTensorFun (ι κ : Type) [Fintype ι]
    [Fintype κ] :
    ((ι → ℂ) ⊗[ℂ] (κ → ℂ)) ≃ₗ[ℂ] (ι × κ → ℂ) :=
  (TensorProduct.congr
      (Finsupp.linearEquivFunOnFinite ℂ ℂ ι).symm
      (Finsupp.linearEquivFunOnFinite ℂ ℂ κ).symm).trans
    ((finsuppTensorFinsupp' ℂ ι κ).trans
      (Finsupp.linearEquivFunOnFinite ℂ ℂ (ι × κ)))

/-- The iterated monoidal power of a super vector space, new
factors on the right. -/
noncomputable def superPow (V : SuperVect) : ℕ → SuperVect
  | 0 => SuperVect.tensorUnit
  | d + 1 => SuperVect.tensorObj (superPow V d) V

/-! ### Splitting a colouring at its last position -/

namespace MixedColouring

/-- The tail of a colouring: the first `d` positions. -/
def tail {k ℓ d : ℕ} (c : MixedColouring k ℓ (d + 1)) :
    MixedColouring k ℓ d :=
  fun i => c i.castSucc

/-- The odd support splits at the last position. -/
theorem oddSet_card_succ {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) :
    c.oddSet.card = c.tail.oddSet.card +
      (if (c (Fin.last d)).isRight then 1 else 0) := by
  unfold oddSet tail
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_castSucc]

/-- Parity of the extension, last position even. -/
theorem isEven_succ_left {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (a : Fin k)
    (h : c (Fin.last d) = Sum.inl a) :
    (c.IsEven ↔ c.tail.IsEven) := by
  unfold IsEven
  rw [oddSet_card_succ, h]
  simp

/-- Parity of the extension, last position odd. -/
theorem isEven_succ_right {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (b : Fin (2 * ℓ))
    (h : c (Fin.last d) = Sum.inr b) :
    (c.IsEven ↔ ¬ c.tail.IsEven) := by
  unfold IsEven
  rw [oddSet_card_succ, h]
  simp [Nat.even_add_one]

end MixedColouring

/-- Splitting a colouring at its last position. -/
noncomputable def colouringSplit (k ℓ d : ℕ) :
    MixedColouring k ℓ (d + 1) ≃
      MixedColouring k ℓ d × (Fin k ⊕ Fin (2 * ℓ)) where
  toFun c := (MixedColouring.tail c, c (Fin.last d))
  invFun p :=
    Fin.snoc (α := fun _ => Fin k ⊕ Fin (2 * ℓ)) p.1 p.2
  left_inv c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [MixedColouring.tail]
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) ?_ <;>
      simp [MixedColouring.tail]

/-- Parity through the split. -/
theorem MixedColouring.isEven_split {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) :
    c.IsEven ↔ Sum.elim
      (fun _ : Fin k => c.tail.IsEven)
      (fun _ : Fin (2 * ℓ) => ¬ c.tail.IsEven)
      (c (Fin.last d)) := by
  rcases h : c (Fin.last d) with a | b
  · simp only [Sum.elim_inl]
    exact c.isEven_succ_left a h
  · simp only [Sum.elim_inr]
    exact c.isEven_succ_right b h

/-- A subtype of a product by a condition on the first factor. -/
def subtypeProdFst {A X : Type} (Q : A → Prop) :
    {p : A × X // Q p.1} ≃ {a : A // Q a} × X where
  toFun p := (⟨p.val.1, p.prop⟩, p.val.2)
  invFun q := ⟨(q.1.val, q.2), q.1.prop⟩
  left_inv _p := rfl
  right_inv _q := rfl

/-- The even colourings of `d + 1` positions split by the last
colour: an even colour on an even tail, or an odd colour on an
odd tail. -/
noncomputable def evenSplitEquiv (k ℓ d : ℕ) :
    {c : MixedColouring k ℓ (d + 1) // c.IsEven} ≃
      ({c : MixedColouring k ℓ d // c.IsEven} × Fin k) ⊕
        ({c : MixedColouring k ℓ d // ¬ c.IsEven} ×
          Fin (2 * ℓ)) :=
  (((colouringSplit k ℓ d).subtypeEquiv
      (q := fun p => Sum.elim
        (fun _ : Fin k => p.1.IsEven)
        (fun _ : Fin (2 * ℓ) => ¬ p.1.IsEven) p.2)
      (fun c => by
        rw [MixedColouring.isEven_split c]
        exact Iff.rfl)).trans
    (((Equiv.prodSumDistrib (MixedColouring k ℓ d)
        (Fin k) (Fin (2 * ℓ))).subtypeEquiv
      (q := Sum.elim
        (fun ta : MixedColouring k ℓ d × Fin k => ta.1.IsEven)
        (fun tb : MixedColouring k ℓ d × Fin (2 * ℓ) =>
          ¬ tb.1.IsEven))
      (fun p => by
        rcases p with ⟨t, a | b⟩ <;> exact Iff.rfl)).trans
      ((Equiv.subtypeSum).trans
        (Equiv.sumCongr
          (subtypeProdFst (fun t : MixedColouring k ℓ d =>
            t.IsEven))
          (subtypeProdFst (fun t : MixedColouring k ℓ d =>
            ¬ t.IsEven))))))

/-- The odd colourings of `d + 1` positions split by the last
colour: an even colour on an odd tail, or an odd colour on an
even tail. -/
noncomputable def oddSplitEquiv (k ℓ d : ℕ) :
    {c : MixedColouring k ℓ (d + 1) // ¬ c.IsEven} ≃
      ({c : MixedColouring k ℓ d // ¬ c.IsEven} × Fin k) ⊕
        ({c : MixedColouring k ℓ d // c.IsEven} ×
          Fin (2 * ℓ)) :=
  (((colouringSplit k ℓ d).subtypeEquiv
      (q := fun p => Sum.elim
        (fun _ : Fin k => ¬ p.1.IsEven)
        (fun _ : Fin (2 * ℓ) => p.1.IsEven) p.2)
      (fun c => by
        rw [show (¬ c.IsEven) ↔ _ from
          not_iff_not.mpr (MixedColouring.isEven_split c)]
        rw [show ((colouringSplit k ℓ d) c).2 =
          c (Fin.last d) from rfl]
        rcases c (Fin.last d) with a | b <;>
          simp only [Sum.elim_inl, Sum.elim_inr, not_not] <;>
          exact Iff.rfl)).trans
    (((Equiv.prodSumDistrib (MixedColouring k ℓ d)
        (Fin k) (Fin (2 * ℓ))).subtypeEquiv
      (q := Sum.elim
        (fun ta : MixedColouring k ℓ d × Fin k =>
          ¬ ta.1.IsEven)
        (fun tb : MixedColouring k ℓ d × Fin (2 * ℓ) =>
          tb.1.IsEven))
      (fun p => by
        rcases p with ⟨t, a | b⟩ <;> exact Iff.rfl)).trans
      ((Equiv.subtypeSum).trans
        (Equiv.sumCongr
          (subtypeProdFst (fun t : MixedColouring k ℓ d =>
            ¬ t.IsEven))
          (subtypeProdFst (fun t : MixedColouring k ℓ d =>
            t.IsEven))))))

/-! ### The equivalence with the iterated power -/

namespace SuperLinearEquiv

/-- The identity super linear equivalence. -/
noncomputable def refl (V : SuperVect) : SuperLinearEquiv V V :=
  ⟨LinearEquiv.refl ℂ _, LinearEquiv.refl ℂ _⟩

/-- Composition of super linear equivalences. -/
noncomputable def trans {U V W : SuperVect}
    (e : SuperLinearEquiv U V) (e' : SuperLinearEquiv V W) :
    SuperLinearEquiv U W :=
  ⟨e.evenEquiv.trans e'.evenEquiv, e.oddEquiv.trans e'.oddEquiv⟩

/-- The tensor of super linear equivalences. -/
noncomputable def tensorCongr {V V' W W' : SuperVect}
    (e : SuperLinearEquiv V V') (e' : SuperLinearEquiv W W') :
    SuperLinearEquiv (SuperVect.tensorObj V W)
      (SuperVect.tensorObj V' W') :=
  ⟨LinearEquiv.prodCongr
      (TensorProduct.congr e.evenEquiv e'.evenEquiv)
      (TensorProduct.congr e.oddEquiv e'.oddEquiv),
   LinearEquiv.prodCongr
      (TensorProduct.congr e.evenEquiv e'.oddEquiv)
      (TensorProduct.congr e.oddEquiv e'.evenEquiv)⟩

end SuperLinearEquiv

/-- At `d = 0` there is exactly one even colouring, the empty
one. -/
instance colourZeroEvenUnique (k ℓ : ℕ) :
    Unique {c : MixedColouring k ℓ 0 // c.IsEven} where
  default := ⟨(default : Fin 0 → Fin k ⊕ Fin (2 * ℓ)),
    ⟨0, by simp [MixedColouring.oddSet]⟩⟩
  uniq x := Subtype.ext (Subsingleton.elim _ _)

/-- And no odd one: the zeroth power is purely even. -/
instance colourZeroOddEmpty (k ℓ : ℕ) :
    IsEmpty {c : MixedColouring k ℓ 0 // ¬ c.IsEven} :=
  ⟨fun x => x.prop (by
    have h : x.val = (default : Fin 0 → Fin k ⊕ Fin (2 * ℓ)) :=
      Subsingleton.elim _ _
    rw [MixedColouring.IsEven, h]
    exact ⟨0, by simp [MixedColouring.oddSet]⟩)⟩

/-- The base of the recursion: the zeroth power is the colouring
model of zero positions. -/
noncomputable def colourPowerZero (k ℓ : ℕ) :
    SuperLinearEquiv SuperVect.tensorUnit (colourPower k ℓ 0) :=
  ⟨(LinearEquiv.funUnique
      {c : MixedColouring k ℓ 0 // c.IsEven} ℂ ℂ).symm,
   show SuperVect.tensorUnit.odd ≃ₗ[ℂ]
      ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ) from
    LinearEquiv.ofSubsingleton _ _⟩

/-- The step of the recursion: tensoring the colouring model with
the standard space extends the colourings by one position. -/
noncomputable def colourPowerStep (k ℓ d : ℕ) :
    SuperLinearEquiv
      (SuperVect.tensorObj (colourPower k ℓ d) (stdSuperPair k ℓ))
      (colourPower k ℓ (d + 1)) :=
  ⟨(LinearEquiv.prodCongr
      (funTensorFun {c : MixedColouring k ℓ d // c.IsEven}
        (Fin k))
      (funTensorFun {c : MixedColouring k ℓ d // ¬ c.IsEven}
        (Fin (2 * ℓ)))).trans
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ)
        (evenSplitEquiv k ℓ d).symm)),
   (LinearEquiv.prodCongr
      (funTensorFun {c : MixedColouring k ℓ d // c.IsEven}
        (Fin (2 * ℓ)))
      (funTensorFun {c : MixedColouring k ℓ d // ¬ c.IsEven}
        (Fin k))).trans
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm.trans
      ((LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ)
        (Equiv.sumComm _ _)).trans
        (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ)
          (oddSplitEquiv k ℓ d).symm)))⟩

/-- **The colouring model of the iterated power**: the `d`-th
monoidal power of the standard super space is the colouring
model. -/
noncomputable def colourPowerEquiv (k ℓ : ℕ) : (d : ℕ) →
    SuperLinearEquiv (superPow (stdSuperPair k ℓ) d)
      (colourPower k ℓ d)
  | 0 => colourPowerZero k ℓ
  | d + 1 =>
      (SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ d)
        (SuperLinearEquiv.refl (stdSuperPair k ℓ))).trans
        (colourPowerStep k ℓ d)

end RS
