/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapMatch

/-!
# Peeling the bundle cap

The strand-bundle cap on `m + 1` strands factors as the cap on
`m` strands tensored with a single evaluation, composed with the
rotation that moves the last strand's two ends to the end of the
boundary word.  This is the recursion that computes the cap
functional in coordinates.
-/

@[expose] public section

namespace RS

/-- The peel rotation, on values. -/
def capPeelFun (m j : ℕ) : ℕ :=
  if j < m then j
  else if j = m then m + m
  else if j ≤ m + m then j - 1 else j

/-- The inverse peel rotation, on values. -/
def capPeelInv (m j : ℕ) : ℕ :=
  if j < m then j
  else if j = m + m then m
  else if j < m + m then j + 1 else j

/-- The peel rotation: move the last strand's ends to the end. -/
def capPeelRotation (m : ℕ) :
    Fin ((m + 1) + (m + 1)) ≃ Fin ((m + m) + 2) where
  toFun i := ⟨capPeelFun m i.val, by
    have := i.isLt
    unfold capPeelFun
    split_ifs <;> omega⟩
  invFun j := ⟨capPeelInv m j.val, by
    have := j.isLt
    unfold capPeelInv
    split_ifs <;> omega⟩
  left_inv i := Fin.ext (by
    have := i.isLt
    change capPeelInv m (capPeelFun m i.val) = i.val
    unfold capPeelFun capPeelInv
    split_ifs <;> omega)
  right_inv j := Fin.ext (by
    have := j.isLt
    change capPeelFun m (capPeelInv m j.val) = j.val
    unfold capPeelFun capPeelInv
    split_ifs <;> omega)

/-- The incoming transport of the peel evaluates by the inverse
rotation. -/
theorem capPeel_inTransport_val (m : ℕ)
    (ℓ : Fin (((m + m) + 2) + 0)) :
    ((finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (capPeelRotation m).symm
        (_root_.Equiv.refl (Fin 0))).trans
        finSumFinEquiv)) ℓ).val = capPeelInv m ℓ.val := by
  rw [show ℓ = Fin.castAdd 0 ⟨ℓ.val, by
      have := ℓ.isLt; omega⟩ from Fin.ext rfl]
  rw [_root_.Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The peel flag map. -/
def capPeelFlagFun (m : ℕ) :
    Fin (m + 1) × Bool → ((Fin m × Bool) ⊕ Fin 2) := fun g =>
  if h : g.1.val < m then Sum.inl (⟨g.1.val, h⟩, g.2)
  else Sum.inr (if g.2 then 1 else 0)

/-- The inverse peel flag map. -/
def capPeelFlagInv (m : ℕ) :
    ((Fin m × Bool) ⊕ Fin 2) → Fin (m + 1) × Bool
  | Sum.inl (j, b) => (⟨j.val, by omega⟩, b)
  | Sum.inr t => (⟨m, by omega⟩, decide (t.val = 1))

/-- The peel flag equivalence. -/
def capPeelFlagEquiv (m : ℕ) :
    (Fin (m + 1) × Bool) ≃ ((Fin m × Bool) ⊕ Fin 2) where
  toFun := capPeelFlagFun m
  invFun := capPeelFlagInv m
  left_inv g := by
    -- ═══════ ATTACHMENT ═══════
    -- A strand below `m` lands in the smaller bundle; the top strand
    -- lands in the two-element strand.
    obtain ⟨i, b⟩ := g
    unfold capPeelFlagFun
    by_cases h : i.val < m
    · rw [dite_eq_left h]
      change (⟨i.val, _⟩, b) = (i, b)
      exact Prod.ext (Fin.ext rfl) rfl
    · rw [dite_eq_right h]
      have hi : i.val = m := by
        have := i.isLt
        omega
      cases b
      · change ((⟨m, _⟩ : Fin (m + 1)),
          decide ((0 : Fin 2).val = 1)) = (i, false)
        exact Prod.ext (Fin.ext (show m = i.val by omega)) rfl
      · change ((⟨m, _⟩ : Fin (m + 1)),
          decide ((1 : Fin 2).val = 1)) = (i, true)
        exact Prod.ext (Fin.ext (show m = i.val by omega)) rfl
  right_inv g := by
    rcases g with ⟨j, b⟩ | t
    · change capPeelFlagFun m (⟨j.val, _⟩, b) = _
      unfold capPeelFlagFun
      rw [dite_eq_left (show (⟨j.val, by omega⟩ :
        Fin (m + 1)).val < m from j.isLt)]
    · change capPeelFlagFun m (⟨m, _⟩, decide (t.val = 1)) = _
      unfold capPeelFlagFun
      rw [dite_eq_right (show ¬ ((⟨m, by omega⟩ :
        Fin (m + 1)).val < m) from by
          change ¬ (m < m); omega)]
      refine congrArg Sum.inr ?_
      have ht := t.isLt
      rcases (show t.val = 0 ∨ t.val = 1 by omega)
        with hv | hv
      · rw [show t = (0 : Fin 2) from Fin.ext hv]
        rfl
      · rw [show t = (1 : Fin 2) from Fin.ext hv]
        rfl

/-- Interleave value on the cap side. -/
theorem capPeel_interleave_left_val (m X : ℕ)
    (h : X < (m + m) + 0) :
    ((interleaveEquiv (m + m) 0 2 0)
      (Sum.inl ⟨X, h⟩)).val = X := by
  rw [show (⟨X, h⟩ : Fin ((m + m) + 0)) =
    Fin.castAdd 0 ⟨X, by omega⟩ from Fin.ext rfl,
    interleaveEquiv_inl_low]
  rfl

/-- Interleave value on the evaluation side. -/
theorem capPeel_interleave_right_val (m X : ℕ)
    (h : X < 2 + 0) :
    ((interleaveEquiv (m + m) 0 2 0)
      (Sum.inr ⟨X, h⟩)).val = (m + m) + X := by
  rw [show (⟨X, h⟩ : Fin (2 + 0)) =
    Fin.castAdd 0 ⟨X, by omega⟩ from Fin.ext rfl,
    interleaveEquiv_inr_low]
  rfl

private theorem capPeelEquiv_attach_comm (m : ℕ)
    (g : (((strandBundle (m + 1)).relabel (finCongr
      (by omega : (m + 1) + (m + 1) =
        ((m + 1) + (m + 1)) + 0)))).Flag) :
    (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv)))).attach (capPeelFlagEquiv m g) =
      ((((strandBundle (m + 1)).relabel (finCongr
      (by omega : (m + 1) + (m + 1) =
        ((m + 1) + (m + 1)) + 0)))).attach g).map (_root_.Equiv.equivOfIsEmpty Empty (Empty
            ⊕ Empty)) id := by
  -- ═══════ PAIRING ═══════
  -- The flag map sends a strand's two ends to the same factor, so
  -- the pairing is the factor's own.
  obtain ⟨i, b⟩ := g
  by_cases h : i.val < m
  · have hflag : capPeelFlagEquiv m (i, b) =
        Sum.inl (⟨i.val, h⟩, b) := dite_eq_left h
    refine Eq.trans (congrArg
      (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
        ((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).attach z) hflag) ?_
    cases b
    · change Sum.inr ((finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))
        ((interleaveEquiv (m + m) 0 2 0)
          (Sum.inl ⟨i.val, by omega⟩))) =
        Sum.inr (finCongr
          (by omega : (m + 1) + (m + 1) =
            ((m + 1) + (m + 1)) + 0) ⟨i.val, by omega⟩)
      refine congrArg Sum.inr (Fin.ext ?_)
      rw [capPeel_inTransport_val,
        capPeel_interleave_left_val]
      change capPeelInv m i.val = i.val
      unfold capPeelInv
      rw [ite_eq_left h]
    · change Sum.inr ((finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))
        ((interleaveEquiv (m + m) 0 2 0)
          (Sum.inl ⟨m + i.val, by omega⟩))) =
        Sum.inr (finCongr
          (by omega : (m + 1) + (m + 1) =
            ((m + 1) + (m + 1)) + 0)
          ⟨(m + 1) + i.val, by omega⟩)
      refine congrArg Sum.inr (Fin.ext ?_)
      rw [capPeel_inTransport_val,
        capPeel_interleave_left_val]
      change capPeelInv m (m + i.val) = (m + 1) + i.val
      unfold capPeelInv
      split_ifs <;> omega
  -- ─────── the top strand ───────
  · have hi : i.val = m := by
      have := i.isLt
      omega
    cases b
    · have hflag : capPeelFlagEquiv m (i, false) =
          Sum.inr 0 := by
        change capPeelFlagFun m (i, false) = _
        unfold capPeelFlagFun
        rw [dite_eq_right h]
        rfl
      refine Eq.trans (congrArg
        (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
          ((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).attach z) hflag) ?_
      change Sum.inr ((finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))
        ((interleaveEquiv (m + m) 0 2 0)
          (Sum.inr ⟨0, by omega⟩))) =
        Sum.inr (finCongr
          (by omega : (m + 1) + (m + 1) =
            ((m + 1) + (m + 1)) + 0) ⟨i.val, by omega⟩)
      refine congrArg Sum.inr (Fin.ext ?_)
      rw [capPeel_inTransport_val,
        capPeel_interleave_right_val]
      change capPeelInv m ((m + m) + 0) = i.val
      unfold capPeelInv
      split_ifs <;> omega
    · have hflag : capPeelFlagEquiv m (i, true) =
          Sum.inr 1 := by
        change capPeelFlagFun m (i, true) = _
        unfold capPeelFlagFun
        rw [dite_eq_right h]
        rfl
      refine Eq.trans (congrArg
        (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
          ((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).attach z) hflag) ?_
      change Sum.inr ((finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))
        ((interleaveEquiv (m + m) 0 2 0)
          (Sum.inr ⟨1, by omega⟩))) =
        Sum.inr (finCongr
          (by omega : (m + 1) + (m + 1) =
            ((m + 1) + (m + 1)) + 0)
          ⟨(m + 1) + i.val, by omega⟩)
      refine congrArg Sum.inr (Fin.ext ?_)
      rw [capPeel_inTransport_val,
        capPeel_interleave_right_val]
      change capPeelInv m ((m + m) + 1) = (m + 1) + i.val
      unfold capPeelInv
      split_ifs <;> omega
-- ═══════ PAIRING ═══════

private theorem capPeelEquiv_pairing_comm (m : ℕ)
    (g : (((strandBundle (m + 1)).relabel (finCongr
      (by omega : (m + 1) + (m + 1) =
        ((m + 1) + (m + 1)) + 0)))).Flag) :
    capPeelFlagEquiv m ((((strandBundle (m + 1)).relabel (finCongr
      (by omega : (m + 1) + (m + 1) =
        ((m + 1) + (m + 1)) + 0)))).pairing g) =
      (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv)))).pairing (capPeelFlagEquiv m g) := by
  obtain ⟨i, b⟩ := g
  change capPeelFlagEquiv m (i, !b) =
    ((((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing
      (capPeelFlagEquiv m (i, b)) :
      ((Fin m × Bool) ⊕ Fin 2)))
  by_cases h : i.val < m
  · exact ((dite_eq_left h : capPeelFlagEquiv m (i, !b) =
        Sum.inl (⟨i.val, h⟩, !b))).trans
      (((rfl : (Sum.inl (⟨i.val, h⟩, !b) :
          ((Fin m × Bool) ⊕ Fin 2)) =
        (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing
          (Sum.inl (⟨i.val, h⟩, b)) :
          ((Fin m × Bool) ⊕ Fin 2)))).trans
      ((congrArg (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
        (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing z : ((Fin m × Bool) ⊕ Fin 2)))
        (dite_eq_left h : capPeelFlagEquiv m (i, b) =
          Sum.inl (⟨i.val, h⟩, b))).symm))
  -- ─────── the top strand ───────
  · have hf : capPeelFlagEquiv m (i, false) =
        Sum.inr (0 : Fin 2) := by
      change capPeelFlagFun m (i, false) = _
      unfold capPeelFlagFun
      rw [dite_eq_right h]
      rfl
    have ht : capPeelFlagEquiv m (i, true) =
        Sum.inr (1 : Fin 2) := by
      change capPeelFlagFun m (i, true) = _
      unfold capPeelFlagFun
      rw [dite_eq_right h]
      rfl
    cases b
    · exact ht.trans
        (((show (Sum.inr (1 : Fin 2) :
            ((Fin m × Bool) ⊕ Fin 2)) =
          (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing
            (Sum.inr (0 : Fin 2)) :
            ((Fin m × Bool) ⊕ Fin 2)) from
          congrArg Sum.inr (Fin.ext rfl))).trans
        ((congrArg (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
          (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing z : ((Fin m × Bool) ⊕ Fin 2))) hf).symm))
    · exact hf.trans
        (((show (Sum.inr (0 : Fin 2) :
            ((Fin m × Bool) ⊕ Fin 2)) =
          (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing
            (Sum.inr (1 : Fin 2)) :
            ((Fin m × Bool) ⊕ Fin 2)) from
          congrArg Sum.inr (Fin.ext rfl))).trans
        ((congrArg (fun z : ((Fin m × Bool) ⊕ Fin 2) =>
          (((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))).pairing z : ((Fin m × Bool) ⊕ Fin 2))) ht).symm))

/-- **The cap peel equivalence**: the padded bundle cap on
`m + 1` strands is the tensor of the cap on `m` strands with one
evaluation, relabelled along the peel rotation. -/
noncomputable def capPeelEquiv (m : ℕ) :
    ((strandBundle (m + 1)).relabel (finCongr
      (by omega : (m + 1) + (m + 1) =
        ((m + 1) + (m + 1)) + 0))).Equiv
    ((tensorFragment
        ((strandBundle m).relabel (finCongr
          (by omega : m + m = (m + m) + 0)))
        (Fragment.strand.relabel (finCongr
          (by omega : 2 = 2 + 0)))).relabel
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (capPeelRotation m).symm
          (_root_.Equiv.refl (Fin 0))).trans
          finSumFinEquiv))) where
  flagEquiv := capPeelFlagEquiv m
  vertexEquiv :=
    show Empty ≃ (Empty ⊕ Empty) from
      _root_.Equiv.equivOfIsEmpty _ _
  -- ═══════ ATTACHMENT ═══════
  attach_comm := capPeelEquiv_attach_comm m
  pairing_comm := capPeelEquiv_pairing_comm m
  circles_eq := rfl

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **The cap peel**: the bundle cap on `m + 1` strands is the
peel rotation composed with the cap on `m` strands tensored with
one evaluation. -/
theorem bundleCapClass_peel (m : ℕ) :
    bundleCapClass f (m + 1) =
      HomSpace.comp f ((m + 1) + (m + 1)) ((m + m) + 2) 0
        (bundleMapClass f (capPeelRotation m))
        (HomSpace.tensor f (m + m) 0 2 0
          (bundleCapClass f m) (evClass f)) := by
  rw [show HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f) =
    HomSpace.ofFragment f.val (tensorFragment
      ((strandBundle m).relabel (finCongr
        (by omega : m + m = (m + m) + 0)))
      (Fragment.strand.relabel (finCongr
        (by omega : 2 = 2 + 0)))) from
    HomSpace.tensor_ofFragment f (m + m) 0 2 0 _ _]
  rw [bundleMapClass_comp_left]
  exact HomSpace.ofFragment_congr f (capPeelEquiv m)

end RS
