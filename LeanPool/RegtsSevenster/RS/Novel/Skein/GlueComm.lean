/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.FragmentEquiv

/-!
# Commutation of disjoint single-pair glues

Two single-pair glues at disjoint label pairs commute up to fragment
equivalence: gluing `{i, j}` then `{k, l}` yields an equivalent
fragment to gluing `{k, l}` then `{i, j}`, provided the four labels
are pairwise distinct.  This is the engine of associativity for the
skein category.

The proof proceeds by classifying the involution structure of
`W.pairing` on the four boundary flags: whether the pairs `{i, j}`
and `{k, l}` are edges determines the open/closed status of each
glue and thus the circle count and rewiring behaviour.
-/

namespace RS

namespace Fragment

variable {α : Type}

/-! ### Label plumbing -/

/-- The swap equivalence between nested surviving-label subtypes:
removing `{i, j}` then `{k, l}` is the same as removing `{k, l}`
then `{i, j}`. -/
def swapLabelEquiv {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    SurvivingLabel (SurvivingLabel α i j) ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm,
      hjl.symm⟩ ≃
    SurvivingLabel (SurvivingLabel α k l) ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩ where
  toFun x :=
    let val := x.val.val
    have hxk : val ≠ k := fun h => x.prop.1 (Subtype.ext h)
    have hxl : val ≠ l := fun h => x.prop.2 (Subtype.ext h)
    have hxi : val ≠ i := x.val.prop.1
    have hxj : val ≠ j := x.val.prop.2
    ⟨⟨val, hxk, hxl⟩, fun h => hxi (congrArg Subtype.val h),
      fun h => hxj (congrArg Subtype.val h)⟩
  invFun x :=
    let val := x.val.val
    have hxi : val ≠ i := fun h => x.prop.1 (Subtype.ext h)
    have hxj : val ≠ j := fun h => x.prop.2 (Subtype.ext h)
    have hxk : val ≠ k := x.val.prop.1
    have hxl : val ≠ l := x.val.prop.2
    ⟨⟨val, hxi, hxj⟩, fun h => hxk (congrArg Subtype.val h),
      fun h => hxl (congrArg Subtype.val h)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-! ### What the two orders share

Neither the surviving flags nor the attachment map of a double glue
depends on the order the two pairs are glued in: either order leaves
the flags of `W` that are none of the four glued boundary flags, and
either order reads attachment off `W.attach`.  Only the pairing and
the circle count tell the configurations below apart, so the pairing
is all each of them has to compute.
-/

/-- The flags surviving both glues, read in either order: removing
`{i, j}` and then `{k, l}` nests the four exclusions one way, and
removing `{k, l}` first nests them the other way.  The swap is the
identity on the underlying flag of `W`. -/
private def doubleSurvivingSwap (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    {f : SurvivingFlag W i j //
        f ≠ glueBoundaryFlag W i j ⟨k, hik.symm, hjk.symm⟩ ∧
        f ≠ glueBoundaryFlag W i j ⟨l, hil.symm, hjl.symm⟩} ≃
      {f : SurvivingFlag W k l //
        f ≠ glueBoundaryFlag W k l ⟨i, hik, hil⟩ ∧
        f ≠ glueBoundaryFlag W k l ⟨j, hjk, hjl⟩} where
  toFun f :=
    ⟨⟨f.val.val, fun h => f.prop.1 (Subtype.ext h),
        fun h => f.prop.2 (Subtype.ext h)⟩,
      fun h => f.val.prop.1 (congrArg Subtype.val h),
      fun h => f.val.prop.2 (congrArg Subtype.val h)⟩
  invFun f :=
    ⟨⟨f.val.val, fun h => f.prop.1 (Subtype.ext h),
        fun h => f.prop.2 (Subtype.ext h)⟩,
      fun h => f.val.prop.1 (congrArg Subtype.val h),
      fun h => f.val.prop.2 (congrArg Subtype.val h)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- The partner of a flag can be the boundary flag of at most one
label, so testing four labels in turn gives five cases: a match at
one of them, carrying the failures before it, or no match at all. -/
private theorem partner_cases (W : Fragment α) (f : W.Flag) (a b c d : α) :
    W.pairing f = W.boundaryFlag a ∨
      (W.pairing f ≠ W.boundaryFlag a ∧ W.pairing f = W.boundaryFlag b) ∨
      (W.pairing f ≠ W.boundaryFlag a ∧ W.pairing f ≠ W.boundaryFlag b ∧
        W.pairing f = W.boundaryFlag c) ∨
      (W.pairing f ≠ W.boundaryFlag a ∧ W.pairing f ≠ W.boundaryFlag b ∧
        W.pairing f ≠ W.boundaryFlag c ∧ W.pairing f = W.boundaryFlag d) ∨
      (W.pairing f ≠ W.boundaryFlag a ∧ W.pairing f ≠ W.boundaryFlag b ∧
        W.pairing f ≠ W.boundaryFlag c ∧ W.pairing f ≠ W.boundaryFlag d) := by
  classical
  by_cases ha : W.pairing f = W.boundaryFlag a
  · exact Or.inl ha
  by_cases hb : W.pairing f = W.boundaryFlag b
  · exact Or.inr (Or.inl ⟨ha, hb⟩)
  by_cases hc : W.pairing f = W.boundaryFlag c
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc⟩))
  by_cases hd : W.pairing f = W.boundaryFlag d
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, hd⟩)))

/-- The swap intertwines the two attachment maps.  Both sides trace
the same flag of `W` down to `W.attach`: outer glue to inner glue to
`W`, and back up the other order.  The vertex types are all `W.Vertex`
and are spelled out so the chain of rewrites stays at one type. -/
private theorem doubleGlueAttach_comm (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    {p : SurvivingFlag W i j → SurvivingFlag W i j}
    {hp : ∀ f, p (p f) = f} {hp' : ∀ f, p f ≠ f} {c : ℕ}
    {q : SurvivingFlag W k l → SurvivingFlag W k l}
    {hq : ∀ f, q (q f) = f} {hq' : ∀ f, q f ≠ f} {d : ℕ}
    (f : SurvivingFlag (W.glueWith i j p hp hp' c)
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩) :
    Sum.map (id : W.Vertex → W.Vertex)
        ((swapLabelEquiv hik hil hjk hjl).symm)
        (glueAttach (W.glueWith k l q hq hq' d)
          ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
          (doubleSurvivingSwap W hik hil hjk hjl f)) =
      Sum.map (id : W.Vertex → W.Vertex) id
        (glueAttach (W.glueWith i j p hp hp' c)
          ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩ f) := by
  set g := doubleSurvivingSwap W hik hil hjk hjl f
  rcases h_r : glueAttach (W.glueWith i j p hp hp' c)
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩ f with v_r | ℓ_r
  · -- An internal vertex: the same one at every stage.
    have h_ir : glueAttach W i j f.val = Sum.inl v_r :=
      (glueAttach_inl_iff f v_r).mp h_r
    have h_base : W.attach f.val.val = Sum.inl v_r :=
      (glueAttach_inl_iff f.val v_r).mp h_ir
    have h_il : glueAttach W k l g.val = Sum.inl v_r :=
      (glueAttach_inl_iff g.val v_r).mpr h_base
    have h_l : glueAttach (W.glueWith k l q hq hq' d)
        ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩ g = Sum.inl v_r :=
      (glueAttach_inl_iff (W := W.glueWith k l q hq hq' d)
        (i := ⟨i, hik, hil⟩) (j := ⟨j, hjk, hjl⟩) g v_r).mpr h_il
    exact congrArg (Sum.map (id : W.Vertex → W.Vertex)
      ((swapLabelEquiv hik hil hjk hjl).symm)) h_l
  · -- A surviving label: the same one, carried across the swap.
    have h_ir : glueAttach W i j f.val = Sum.inr ℓ_r.val :=
      (glueAttach_inr_iff f ℓ_r).mp h_r
    have h_base : W.attach f.val.val = Sum.inr ℓ_r.val.val :=
      (glueAttach_inr_iff f.val ℓ_r.val).mp h_ir
    have hℓk : ℓ_r.val.val ≠ k := fun h =>
      (survivingFlag_attach_ne g.val).1 (h_base.trans (congrArg Sum.inr h))
    have hℓl : ℓ_r.val.val ≠ l := fun h =>
      (survivingFlag_attach_ne g.val).2 (h_base.trans (congrArg Sum.inr h))
    have h_il : glueAttach W k l g.val = Sum.inr ⟨ℓ_r.val.val, hℓk, hℓl⟩ :=
      (glueAttach_inr_iff g.val ⟨ℓ_r.val.val, hℓk, hℓl⟩).mpr h_base
    have hℓi : (⟨ℓ_r.val.val, hℓk, hℓl⟩ : SurvivingLabel α k l) ≠
        ⟨i, hik, hil⟩ := fun h => ℓ_r.val.prop.1 (congrArg Subtype.val h)
    have hℓj : (⟨ℓ_r.val.val, hℓk, hℓl⟩ : SurvivingLabel α k l) ≠
        ⟨j, hjk, hjl⟩ := fun h => ℓ_r.val.prop.2 (congrArg Subtype.val h)
    have h_l : glueAttach (W.glueWith k l q hq hq' d)
        ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩ g =
        Sum.inr ⟨⟨ℓ_r.val.val, hℓk, hℓl⟩, hℓi, hℓj⟩ :=
      (glueAttach_inr_iff (W := W.glueWith k l q hq hq' d)
        (i := ⟨i, hik, hil⟩) (j := ⟨j, hjk, hjl⟩) g
        ⟨⟨ℓ_r.val.val, hℓk, hℓl⟩, hℓi, hℓj⟩).mpr h_il
    exact (congrArg (Sum.map (id : W.Vertex → W.Vertex)
      ((swapLabelEquiv hik hil hjk hjl).symm)) h_l).trans
      (congrArg Sum.inr (Subtype.ext (Subtype.ext rfl)))

/-! ### Configuration (4): both pairs are edges (closed-closed) -/

-- The restricted pairing sends k's boundary flag to l's in the
-- closed ij fragment.
private theorem closedClosed_second_ij
    (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    (W.gluePairClosed i j hclosed_ij).pairing
      (glueBoundaryFlag W i j ⟨k, hik.symm, hjk.symm⟩) =
    glueBoundaryFlag W i j ⟨l, hil.symm, hjl.symm⟩ :=
  Subtype.ext hclosed_kl

-- The restricted pairing sends i's boundary flag to j's in the
-- closed kl fragment.
private theorem closedClosed_second_kl
    (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    (W.gluePairClosed k l hclosed_kl).pairing
      (glueBoundaryFlag W k l ⟨i, hik, hil⟩) =
    glueBoundaryFlag W k l ⟨j, hjk, hjl⟩ :=
  Subtype.ext hclosed_ij

/-- Configuration (4): commutativity when both `{i, j}` and
`{k, l}` are edges of `W`.  Both glues are closed in both orders,
giving circles `W.circles + 2` with the pairing restricted. -/
private def closedClosed_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    ((W.gluePairClosed i j hclosed_ij).gluePairClosed
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (closedClosed_second_ij W hik hil hjk hjl hclosed_ij hclosed_kl)).Equiv
    (((W.gluePairClosed k l hclosed_kl).gluePairClosed
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (closedClosed_second_kl W hik hil hjk hjl hclosed_ij hclosed_kl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    -- The pairing in gluePairClosed is just W.pairing restricted
    -- Both sides apply W.pairing to the underlying flag value
    apply Subtype.ext
    apply Subtype.ext
    -- Goal: W.pairing f.val.val = W.pairing f.val.val
    rfl
  circles_eq := rfl

/-! ### Configuration (0): both pairs are open and disjoint (open-open) -/

/-- Local helper: value of rewire in the "else" branch. -/
private theorem rewire_val_ne' {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val ≠ W.boundaryFlag i)
    (hfj : W.pairing f.val ≠ W.boundaryFlag j) :
    (rewire hopen f).val = W.pairing f.val := by
  unfold rewire; simp [dite_eq_right hfi, dite_eq_right hfj]

/-- Local helper: value of rewire in the first branch (partner is bFi). -/
private theorem rewire_val_left' {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val = W.boundaryFlag i) :
    (rewire hopen f).val = W.pairing (W.boundaryFlag j) := by
  unfold rewire; simp [dite_eq_left hfi]

/-- Local helper: value of rewire in the second branch (partner is bFj). -/
private theorem rewire_val_right' {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val ≠ W.boundaryFlag i)
    (hfj : W.pairing f.val = W.boundaryFlag j) :
    (rewire hopen f).val = W.pairing (W.boundaryFlag i) := by
  unfold rewire; simp [dite_eq_right hfi, dite_eq_left hfj]

-- The kl glue is open in the ij-first fragment.
private theorem openOpen_second_open_ij
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  change (W.gluePairOpen i j hij hopen_ij).pairing
      (glueBoundaryFlag W i j ⟨k, hik.symm, hjk.symm⟩) ≠
    glueBoundaryFlag W i j ⟨l, hil.symm, hjl.symm⟩
  intro heq
  have h_ne_i : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
    hfar_ik (W.pairing_boundaryFlag_comm h)
  have h_ne_j : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hfar_jk (W.pairing_boundaryFlag_comm h)
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j
      ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag k) :=
    rewire_val_ne' h_ne_i h_ne_j
  exact hopen_kl (hval.symm ▸ congrArg Subtype.val heq)

-- The ij glue is open in the kl-first fragment.
private theorem openOpen_second_open_kl
    (W : Fragment α) {i j k l : α}
    (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  change (W.gluePairOpen k l hkl hopen_kl).pairing
      (glueBoundaryFlag W k l ⟨i, hik, hil⟩) ≠
    glueBoundaryFlag W k l ⟨j, hjk, hjl⟩
  intro heq
  have h_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := hfar_ik
  have h_ne_l : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l := hfar_il
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l
      ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag i) :=
    rewire_val_ne' h_ne_k h_ne_l
  exact hopen_ij (hval.symm ▸ congrArg Subtype.val heq)

private theorem openOpen_disjoint_equiv_pairing_first
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).Flag)
    (hpi : W.pairing f.val.val = W.boundaryFlag i) :
    ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).pairing f).val.val =
      (((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (openOpen_second_open_kl W hkl hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_il)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).pairing (doubleSurvivingSwap W hik hil hjk
            hjl f)).val.val := by
  classical
  -- Reduce to equality of underlying W.Flag values
  -- Name the two single glues; every transport below is
  -- read at one of them.
  let Wij := W.gluePairOpen i j hij hopen_ij
  let Wkl := W.gluePairOpen k l hkl hopen_kl
  -- Two `Subtype.ext` steps put both sides at the underlying
  -- `W.Flag` value, where each is a nested `rewire` of `f.val.val`;
  -- `show` spells that goal out.
  let g := doubleSurvivingSwap W hik hil hjk hjl f
  change (rewire (openOpen_second_open_ij W hij hik hil hjk hjl
          hopen_ij hopen_kl hfar_ik hfar_jk) f).val.val =
       (rewire (openOpen_second_open_kl W hkl hik hil hjk hjl
          hopen_ij hopen_kl hfar_ik hfar_il) g).val.val
  -- Key "far by involution" facts
  -- Abbreviation for the hopen_second arguments
  let hopen_ij_kl := openOpen_second_open_ij W hij hik hil hjk hjl
      hopen_ij hopen_kl hfar_ik hfar_jk
  let hopen_kl_ij := openOpen_second_open_kl W hkl hik hil hjk hjl
      hopen_ij hopen_kl hfar_ik hfar_il
  -- 5-way case split on W.pairing f.val.val
  -- LHS: rewire(ij) takes its first branch, giving W.pairing bFj;
  --   rewire(kl) then takes its else branch, leaving it there.
  have lhs_inner : (rewire hopen_ij f.val).val =
      W.pairing (W.boundaryFlag j) :=
    rewire_val_left' hpi
  have lhs_inner_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
    rw [lhs_inner]; exact hfar_jk
  have lhs_inner_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
    rw [lhs_inner]; exact hfar_jl
  have lhs_outer_ne_k : Wij.pairing f.val ≠
      Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
    lhs_inner_ne_k (congrArg Subtype.val h)
  have lhs_outer_ne_l : Wij.pairing f.val ≠
      Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
    lhs_inner_ne_l (congrArg Subtype.val h)
  have lhs_val : (rewire hopen_ij_kl f).val.val =
      W.pairing (W.boundaryFlag j) := by
    have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
      lhs_outer_ne_l
    exact congrArg Subtype.val h ▸ lhs_inner
  -- RHS: rewire(kl) takes its else branch, bFi being neither bFk
  --   nor bFl, leaving bFi; rewire(ij) then takes its first
  --   branch, giving rewire(kl) at bFj, which is W.pairing bFj.
  have rhs_inner_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
    change W.pairing f.val.val ≠ W.boundaryFlag k
    rw [hpi]; exact fun h => hik (W.boundaryFlag_injective h)
  have rhs_inner_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
    change W.pairing f.val.val ≠ W.boundaryFlag l
    rw [hpi]; exact fun h => hil (W.boundaryFlag_injective h)
  have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag i := by
    have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_inner_ne_k
      rhs_inner_ne_l
    rw [h]; exact hpi
  have rhs_outer_eq_i : Wkl.pairing g.val =
      Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
    Subtype.ext rhs_inner
  have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
      ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag j) :=
    rewire_val_ne' hfar_jk hfar_jl
  have rhs_val : (rewire hopen_kl_ij g).val.val =
      W.pairing (W.boundaryFlag j) := by
    have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
    exact congrArg Subtype.val h ▸ rhs_j_rewire
  rw [lhs_val, rhs_val]

private theorem openOpen_disjoint_equiv_pairing_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).Flag) :
    doubleSurvivingSwap W hik hil hjk hjl ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).pairing f) =
      ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (openOpen_second_open_kl W hkl hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_il)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).pairing (doubleSurvivingSwap W hik hil hjk
            hjl f) := by
  classical
  -- Reduce to equality of underlying W.Flag values
  apply Subtype.ext
  apply Subtype.ext
  -- Name the two single glues; every transport below is
  -- read at one of them.
  let Wij := W.gluePairOpen i j hij hopen_ij
  let Wkl := W.gluePairOpen k l hkl hopen_kl
  -- Two `Subtype.ext` steps put both sides at the underlying
  -- `W.Flag` value, where each is a nested `rewire` of `f.val.val`;
  -- `show` spells that goal out.
  let g := doubleSurvivingSwap W hik hil hjk hjl f
  change (rewire (openOpen_second_open_ij W hij hik hil hjk hjl
          hopen_ij hopen_kl hfar_ik hfar_jk) f).val.val =
       (rewire (openOpen_second_open_kl W hkl hik hil hjk hjl
          hopen_ij hopen_kl hfar_ik hfar_il) g).val.val
  -- Key "far by involution" facts
  have hfar_ki : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
    hfar_ik (W.pairing_boundaryFlag_comm h)
  have hfar_kj : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hfar_jk (W.pairing_boundaryFlag_comm h)
  have hfar_li : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag i := fun h =>
    hfar_il (W.pairing_boundaryFlag_comm h)
  have hfar_lj : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag j := fun h =>
    hfar_jl (W.pairing_boundaryFlag_comm h)
  -- g.val.val = f.val.val by definition of the swap
  have hgval : g.val.val = f.val.val := rfl
  -- Abbreviation for the hopen_second arguments
  let hopen_ij_kl := openOpen_second_open_ij W hij hik hil hjk hjl
      hopen_ij hopen_kl hfar_ik hfar_jk
  let hopen_kl_ij := openOpen_second_open_kl W hkl hik hil hjk hjl
      hopen_ij hopen_kl hfar_ik hfar_il
  -- 5-way case split on W.pairing f.val.val
  rcases partner_cases W f.val.val i j k l with
      hpi | ⟨hpi, hpj⟩ | ⟨hpi, hpj, hpk⟩ | ⟨hpi, hpj, hpk, hpl⟩ |
      ⟨hpi, hpj, hpk, hpl⟩
  · exact openOpen_disjoint_equiv_pairing_first W hij hkl hik hil hjk hjl hopen_ij hopen_kl
      hfar_ik hfar_il hfar_jk hfar_jl f hpi
  · -- ═══════ PARTNER IS bF j ═══════
    have lhs_inner : (rewire hopen_ij f.val).val =
        W.pairing (W.boundaryFlag i) :=
      rewire_val_right' hpi hpj
    have lhs_inner_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
      rw [lhs_inner]; exact hfar_ik
    have lhs_inner_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
      rw [lhs_inner]; exact hfar_il
    have lhs_outer_ne_k : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
      lhs_inner_ne_k (congrArg Subtype.val h)
    have lhs_outer_ne_l : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
      lhs_inner_ne_l (congrArg Subtype.val h)
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag i) := by
      have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
        lhs_outer_ne_l
      exact congrArg Subtype.val h ▸ lhs_inner
    -- RHS: rewire(kl) takes its else branch, leaving bFj; rewire(ij)
    --   then takes its second branch, giving rewire(kl) at bFi,
    --   which is W.pairing bFi.
    have rhs_inner_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ W.boundaryFlag k
      rw [hpj]; exact fun h => hjk (W.boundaryFlag_injective h)
    have rhs_inner_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
      change W.pairing f.val.val ≠ W.boundaryFlag l
      rw [hpj]; exact fun h => hjl (W.boundaryFlag_injective h)
    have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
      have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_inner_ne_k
        rhs_inner_ne_l
      rw [h]; exact hpj
    have rhs_inner_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact fun h => hij.symm (W.boundaryFlag_injective h)
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_inner_ne_i (congrArg Subtype.val h)
    have rhs_outer_eq_j : Wkl.pairing g.val =
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
      Subtype.ext rhs_inner
    have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
        ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag i) :=
      rewire_val_ne' hfar_ik hfar_il
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag i) := by
      have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_eq_j
      exact congrArg Subtype.val h ▸ rhs_i_rewire
    rw [lhs_val, rhs_val]
  · -- ═══════ PARTNER IS bF k ═══════
    have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
      rw [lhs_inner, hpk]
    have lhs_outer_eq_k : Wij.pairing f.val =
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
      Subtype.ext lhs_inner_eq_k
    have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
        ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag l) :=
      rewire_val_ne' hfar_li hfar_lj
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag l) := by
      have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
      exact congrArg Subtype.val h ▸ lhs_l_rewire
    -- RHS: rewire(kl) takes its first branch, giving W.pairing bFl;
    --   rewire(ij) then takes its else branch, leaving it there.
    have rhs_inner_eq_k : W.pairing g.val.val = W.boundaryFlag k := by
      change W.pairing f.val.val = W.boundaryFlag k; exact hpk
    have rhs_inner : (rewire hopen_kl g.val).val =
        W.pairing (W.boundaryFlag l) :=
      @rewire_val_left' _ W k l hopen_kl g.val rhs_inner_eq_k
    have rhs_inner_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact hfar_li
    have rhs_inner_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
      rw [rhs_inner]; exact hfar_lj
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_inner_ne_i (congrArg Subtype.val h)
    have rhs_outer_ne_j : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
      rhs_inner_ne_j (congrArg Subtype.val h)
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag l) := by
      have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_ne_j
      exact congrArg Subtype.val h ▸ rhs_inner
    rw [lhs_val, rhs_val]
  · -- ═══════ PARTNER IS bF l ═══════
    have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have lhs_inner_eq_l : (rewire hopen_ij f.val).val = W.boundaryFlag l := by
      rw [lhs_inner, hpl]
    have lhs_inner_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
      rw [lhs_inner_eq_l]
      exact fun h => hkl.symm (W.boundaryFlag_injective h)
    have lhs_outer_ne_k : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
      fun h => lhs_inner_ne_k (congrArg Subtype.val h)
    have lhs_outer_eq_l : Wij.pairing f.val =
        Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
      Subtype.ext lhs_inner_eq_l
    have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
        ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag k) :=
      rewire_val_ne' hfar_ki hfar_kj
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag k) := by
      have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
        lhs_outer_eq_l
      exact congrArg Subtype.val h ▸ lhs_k_rewire
    -- RHS: rewire(kl) takes its second branch, giving W.pairing bFk;
    --   rewire(ij) then takes its else branch, leaving it there.
    have rhs_inner_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ W.boundaryFlag k; exact hpk
    have rhs_inner_eq_l : W.pairing g.val.val = W.boundaryFlag l := by
      change W.pairing f.val.val = W.boundaryFlag l; exact hpl
    have rhs_inner : (rewire hopen_kl g.val).val =
        W.pairing (W.boundaryFlag k) :=
      @rewire_val_right' _ W k l hopen_kl g.val rhs_inner_ne_k rhs_inner_eq_l
    have rhs_inner_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact hfar_ki
    have rhs_inner_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
      rw [rhs_inner]; exact hfar_kj
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_inner_ne_i (congrArg Subtype.val h)
    have rhs_outer_ne_j : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
      rhs_inner_ne_j (congrArg Subtype.val h)
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag k) := by
      have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_ne_j
      exact congrArg Subtype.val h ▸ rhs_inner
    rw [lhs_val, rhs_val]
  · -- ═══════ PARTNER IS NONE OF THE FOUR ═══════
    have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have lhs_inner_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
      rw [lhs_inner]; exact hpk
    have lhs_inner_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
      rw [lhs_inner]; exact hpl
    have lhs_outer_ne_k : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
      fun h => lhs_inner_ne_k (congrArg Subtype.val h)
    have lhs_outer_ne_l : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
      fun h => lhs_inner_ne_l (congrArg Subtype.val h)
    have lhs_val : (rewire hopen_ij_kl f).val.val = W.pairing f.val.val := by
      have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
        lhs_outer_ne_l
      exact congrArg Subtype.val h ▸ lhs_inner
    -- RHS: inner rewire(kl) else → W.pairing f.val.val
    --       outer rewire(ij) else → W.pairing f.val.val
    have rhs_inner_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ W.boundaryFlag k; exact hpk
    have rhs_inner_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
      change W.pairing f.val.val ≠ W.boundaryFlag l; exact hpl
    have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
      have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_inner_ne_k
        rhs_inner_ne_l
      exact h
    have rhs_inner_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact hpi
    have rhs_inner_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
      rw [rhs_inner]; exact hpj
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_inner_ne_i (congrArg Subtype.val h)
    have rhs_outer_ne_j : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
      rhs_inner_ne_j (congrArg Subtype.val h)
    have rhs_val : (rewire hopen_kl_ij g).val.val = W.pairing f.val.val := by
      have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_ne_j
      exact congrArg Subtype.val h ▸ rhs_inner
    rw [lhs_val, rhs_val]

private theorem openOpen_disjoint_equiv_attach_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).Flag) :
    ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (openOpen_second_open_kl W hkl hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_il)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).attach (doubleSurvivingSwap W hik hil hjk hjl f) =
      ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk))).attach f).map (_root_.Equiv.refl W.Vertex) id := by
  classical
  exact doubleGlueAttach_comm W hik hil hjk hjl f

/-- Configuration (0): commutativity when both `{i, j}` and `{k, l}`
are open (not edges) and disjoint (no cross-edges between the two
pairs). Both glues are open in both orders, giving circles `W.circles`
with a double-rewire that commutes. -/
private def openOpen_disjoint_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (openOpen_second_open_ij W hij hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_jk)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (openOpen_second_open_kl W hkl hik hil hjk hjl
        hopen_ij hopen_kl hfar_ik hfar_il)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm := openOpen_disjoint_equiv_attach_comm W hij hkl hik hil hjk hjl hopen_ij
      hopen_kl hfar_ik hfar_il hfar_jk
  pairing_comm := openOpen_disjoint_equiv_pairing_comm W hij hkl hik hil hjk hjl hopen_ij
      hopen_kl hfar_ik hfar_il hfar_jk hfar_jl
  circles_eq := rfl

/-! ### Configuration (1): {i,j} closed, {k,l} open (closed-open mixed) -/

-- The kl glue is open after a closed ij glue.
private theorem closedOpen_second_open
    (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l) :
    (W.gluePairClosed i j hclosed_ij).pairing
      ((W.gluePairClosed i j hclosed_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairClosed i j hclosed_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  intro heq
  exact hopen_kl (congrArg Subtype.val heq)

-- The ij glue is closed after an open kl glue.
private theorem closedOpen_second_closed
    (W : Fragment α) {i j k l : α}
    (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) =
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  -- Need to show: rewire hopen_kl (glueBF i') = glueBF j'
  -- W.pairing(bFi) = bFj, and bFj ≠ bFk (j≠k), bFj ≠ bFl (j≠l)
  -- So rewire hits else branch: val = W.pairing(bFi) = bFj = (glueBF j').val
  apply Subtype.ext
  have hne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := by
    rw [hclosed_ij]; exact fun h => hjk (W.boundaryFlag_injective h)
  have hne_l : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l := by
    rw [hclosed_ij]; exact fun h => hjl (W.boundaryFlag_injective h)
  have hval := @rewire_val_ne' _ W k l hopen_kl
    (glueBoundaryFlag W k l ⟨i, hik, hil⟩) hne_k hne_l
  exact hval.trans hclosed_ij

/-- Configuration (1): commutativity when `{i, j}` is an edge and
`{k, l}` is not.  The ij-first order is closed then open; the kl-first
order is open then closed; both give circles `W.circles + 1`. -/
private def closedOpen_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hclosed_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l) :
    ((W.gluePairClosed i j hclosed_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (closedOpen_second_open W hik hil hjk hjl hclosed_ij hopen_kl)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairClosed
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (closedOpen_second_closed W hkl hik hil hjk hjl hclosed_ij
        hopen_kl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    -- Both sides compute the same underlying W.Flag value.
    -- LHS: rewire on gluePairClosed(ij) checking partner vs bFk/bFl
    -- RHS: restricted (rewire on W checking partner vs bFk/bFl)
    apply Subtype.ext
    apply Subtype.ext
    -- Name the two single glues; every transport below is
    -- read at one of them.
    let Wij := W.gluePairClosed i j hclosed_ij
    let g := doubleSurvivingSwap W hik hil hjk hjl f
    let hopen_ij_kl := closedOpen_second_open W hik hil hjk hjl
        hclosed_ij hopen_kl
    -- Both sides test the partner of `f.val.val` against `bFk` and
    -- `bFl`: on the left after the ij-glue, on the right before it.
    change (rewire hopen_ij_kl f).val.val =
         (rewire hopen_kl g.val).val
    have hgval : g.val.val = f.val.val := rfl
    by_cases hpk : W.pairing f.val.val = W.boundaryFlag k
    · -- Partner is bFk: both sides give W.pairing(bFl)
      -- LHS: the ij-glue's pairing of f has underlying value bFk, so
      --   it is the glued flag at k' and rewire takes its first
      --   branch, giving the glued flag at l', that is W.pairing bFl.
      have lhs_eq_k : Wij.pairing f.val =
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
        Subtype.ext hpk
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag l) := by
        have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_eq_k
        exact congrArg Subtype.val h
      -- RHS: W.pairing g.val.val = bFk → rewire first branch → W.pairing(bFl)
      have rhs_eq_k : W.pairing g.val.val = W.boundaryFlag k := by
        change W.pairing f.val.val = W.boundaryFlag k; exact hpk
      have rhs_val : (rewire hopen_kl g.val).val =
          W.pairing (W.boundaryFlag l) :=
        @rewire_val_left' _ W k l hopen_kl g.val rhs_eq_k
      rw [lhs_val, rhs_val]
    · by_cases hpl : W.pairing f.val.val = W.boundaryFlag l
      · -- Partner is bFl: both sides give W.pairing(bFk)
        have lhs_ne_k : Wij.pairing f.val ≠
            Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
          fun h => hpk (congrArg Subtype.val h)
        have lhs_eq_l : Wij.pairing f.val =
            Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
          Subtype.ext hpl
        have lhs_val : (rewire hopen_ij_kl f).val.val =
            W.pairing (W.boundaryFlag k) := by
          have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_ne_k lhs_eq_l
          exact congrArg Subtype.val h
        have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
          change W.pairing f.val.val ≠ W.boundaryFlag k; exact hpk
        have rhs_eq_l : W.pairing g.val.val = W.boundaryFlag l := by
          change W.pairing f.val.val = W.boundaryFlag l; exact hpl
        have rhs_val : (rewire hopen_kl g.val).val =
            W.pairing (W.boundaryFlag k) :=
          @rewire_val_right' _ W k l hopen_kl g.val rhs_ne_k rhs_eq_l
        rw [lhs_val, rhs_val]
      · -- Partner is neither bFk nor bFl: both sides give W.pairing f.val.val
        have lhs_ne_k : Wij.pairing f.val ≠
            Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
          fun h => hpk (congrArg Subtype.val h)
        have lhs_ne_l : Wij.pairing f.val ≠
            Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
          fun h => hpl (congrArg Subtype.val h)
        have lhs_val : (rewire hopen_ij_kl f).val.val =
            W.pairing f.val.val := by
          have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_ne_k lhs_ne_l
          exact congrArg Subtype.val h
        have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
          change W.pairing f.val.val ≠ W.boundaryFlag k; exact hpk
        have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
          change W.pairing f.val.val ≠ W.boundaryFlag l; exact hpl
        have rhs_val : (rewire hopen_kl g.val).val = W.pairing f.val.val :=
          @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
        rw [lhs_val, rhs_val]
  circles_eq := rfl

/-! ### Configuration (1'): {k,l} closed, {i,j} open (open-closed mixed) -/

-- The ij glue is open after a closed kl glue.
private theorem openClosed_second_open
    (W : Fragment α) {i j k l : α}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    (W.gluePairClosed k l hclosed_kl).pairing
      ((W.gluePairClosed k l hclosed_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairClosed k l hclosed_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  intro heq
  exact hopen_ij (congrArg Subtype.val heq)

-- The kl glue is closed after an open ij glue.
private theorem openClosed_second_closed
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) =
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  apply Subtype.ext
  have hne_i : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := by
    rw [hclosed_kl]; exact fun h => hil.symm (W.boundaryFlag_injective h)
  have hne_j : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := by
    rw [hclosed_kl]; exact fun h => hjl.symm (W.boundaryFlag_injective h)
  have hval := @rewire_val_ne' _ W i j hopen_ij
    (glueBoundaryFlag W i j ⟨k, hik.symm, hjk.symm⟩)
    hne_i hne_j
  exact hval.trans hclosed_kl

/-- Configuration (1'): commutativity when `{k, l}` is an edge and
`{i, j}` is not.  The ij-first order is open then closed; the kl-first
order is closed then open; both give circles `W.circles + 1`. -/
private def openClosed_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hclosed_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairClosed
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (openClosed_second_closed W hij hik hil hjk hjl hopen_ij
        hclosed_kl)).Equiv
    (((W.gluePairClosed k l hclosed_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (openClosed_second_open W hik hil hjk hjl hopen_ij hclosed_kl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    -- LHS: restricted pairing of gluePairOpen(ij) = rewire(ij) restricted
    -- RHS: rewire on gluePairClosed(kl) checking partner vs bFi/bFj
    -- Both reduce to the same 3-case split on W.pairing f.val.val vs bFi/bFj
    apply Subtype.ext
    apply Subtype.ext
    -- Name the two single glues; every transport below is
    -- read at one of them.
    let Wkl := W.gluePairClosed k l hclosed_kl
    let g := doubleSurvivingSwap W hik hil hjk hjl f
    let hopen_kl_ij := openClosed_second_open W hik hil hjk hjl
        hopen_ij hclosed_kl
    -- Both sides test the partner of `f.val.val` against `bFi` and
    -- `bFj`: on the left before the kl-glue, on the right after it.
    change (rewire hopen_ij f.val).val =
         (rewire hopen_kl_ij g).val.val
    have hgval : g.val.val = f.val.val := rfl
    by_cases hpi : W.pairing f.val.val = W.boundaryFlag i
    · -- Partner is bFi: both sides give W.pairing(bFj)
      -- LHS: rewire(ij) first branch → W.pairing(bFj)
      have lhs_val : (rewire hopen_ij f.val).val =
          W.pairing (W.boundaryFlag j) :=
        rewire_val_left' hpi
      -- RHS: inner pairing is ⟨W.pairing g.val.val,...⟩ = ⟨bFi,...⟩ = glueBF i'
      have rhs_eq_i : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
        Subtype.ext (show W.pairing g.val.val = W.boundaryFlag i from hpi)
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_eq_i
        exact congrArg Subtype.val h
      rw [lhs_val, rhs_val]
    · by_cases hpj : W.pairing f.val.val = W.boundaryFlag j
      · -- Partner is bFj: both sides give W.pairing(bFi)
        have lhs_val : (rewire hopen_ij f.val).val =
            W.pairing (W.boundaryFlag i) :=
          rewire_val_right' hpi hpj
        have rhs_ne_i : Wkl.pairing g.val ≠
            Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
          fun h => hpi (congrArg Subtype.val h)
        have rhs_eq_j : Wkl.pairing g.val =
            Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
          Subtype.ext (show W.pairing g.val.val = W.boundaryFlag j from hpj)
        have rhs_val : (rewire hopen_kl_ij g).val.val =
            W.pairing (W.boundaryFlag i) := by
          have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_ne_i rhs_eq_j
          exact congrArg Subtype.val h
        rw [lhs_val, rhs_val]
      · -- Partner is neither bFi nor bFj: both sides give W.pairing f.val.val
        have lhs_val : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
          rewire_val_ne' hpi hpj
        have rhs_ne_i : Wkl.pairing g.val ≠
            Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
          fun h => hpi (congrArg Subtype.val h)
        have rhs_ne_j : Wkl.pairing g.val ≠
            Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
          fun h => hpj (congrArg Subtype.val h)
        have rhs_val : (rewire hopen_kl_ij g).val.val =
            W.pairing f.val.val := by
          have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_ne_i rhs_ne_j
          exact congrArg Subtype.val h
        rw [lhs_val, rhs_val]
  circles_eq := rfl

/-! ### Configuration (2): one cross-edge, variant {ik} -/

-- Second kl-glue is open after ij-glue (cross ik variant).
private theorem oneCross_ik_second_open_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  intro heq
  have hki : W.pairing (W.boundaryFlag k) = W.boundaryFlag i :=
    W.pairing_boundaryFlag_comm hcross
  have lhs_val : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag j) := rewire_val_left' hki
  exact hfar_jl (lhs_val.symm ▸ congrArg Subtype.val heq)

-- Second ij-glue is open after kl-glue (cross ik variant).
private theorem oneCross_ik_second_open_ij
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  intro heq
  have lhs_val : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag l) := rewire_val_left' hcross
  have hfar_lj : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag j :=
    fun h => hfar_jl (W.pairing_boundaryFlag_comm h)
  exact hfar_lj (lhs_val.symm ▸ congrArg Subtype.val heq)

private theorem oneCross_ik_equiv_pairing_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij hcross
        hfar_jl))).Flag) :
    doubleSurvivingSwap W hik hil hjk hjl ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij hcross
        hfar_jl))).pairing f) =
      ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_ik_second_open_ij W hij hkl hik hil hjk hjl hopen_kl hcross
        hfar_jl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).pairing (doubleSurvivingSwap W hik hil hjk
            hjl f) := by
  classical
  apply Subtype.ext; apply Subtype.ext
  -- Name the two single glues; every transport below is
  -- read at one of them.
  let Wij := W.gluePairOpen i j hij hopen_ij
  let Wkl := W.gluePairOpen k l hkl hopen_kl
  let g := doubleSurvivingSwap W hik hil hjk hjl f
  change (rewire (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij
    hcross hfar_jl)
         f).val.val =
       (rewire (oneCross_ik_second_open_ij W hij hkl hik hil hjk hjl hopen_kl
         hcross hfar_jl)
         g).val.val
  have hgval : g.val.val = f.val.val := rfl
  have hki : W.pairing (W.boundaryFlag k) = W.boundaryFlag i :=
    W.pairing_boundaryFlag_comm hcross
  have hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k := fun h =>
    hij (W.boundaryFlag_injective (hki.symm.trans (W.pairing_boundaryFlag_comm
      h)))
  have hfar_lj : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag j :=
    fun h => hfar_jl (W.pairing_boundaryFlag_comm h)
  have hfar_li : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag i := fun h =>
    hkl (W.boundaryFlag_injective (hcross.symm.trans
      (W.pairing_boundaryFlag_comm h)))
  let hopen_ij_kl := oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl
    hopen_ij hcross hfar_jl
  let hopen_kl_ij := oneCross_ik_second_open_ij W hij hkl hik hil hjk hjl
    hopen_kl hcross hfar_jl
  -- Case split: partner = bFj, bFl, or none (bFi and bFk are impossible)
  by_cases hpj : W.pairing f.val.val = W.boundaryFlag j
  · -- ═══════ PARTNER IS bF j: BOTH ORDERS GIVE W.pairing (bF l) ═══════
    have hpi : W.pairing f.val.val ≠ W.boundaryFlag i := by
      intro h
      have hfk : f.val.val = W.boundaryFlag k := by
        have := congrArg W.pairing h
        rw [W.pairing_invol, hcross] at this
        exact this
      exact absurd (Subtype.ext hfk) f.prop.1
    -- LHS: inner ij right branch → val = W.pairing(bFi) = bFk
    have lhs_inner : (rewire hopen_ij f.val).val =
        W.pairing (W.boundaryFlag i) :=
      rewire_val_right' hpi hpj
    have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
      rw [lhs_inner, hcross]
    have lhs_outer_eq_k : Wij.pairing f.val =
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
      Subtype.ext lhs_inner_eq_k
    -- Outer: first branch, giving the ij-glue's pairing at l'; and
    --   rewire(ij) at bFl takes its else branch, so that is
    --   W.pairing bFl.
    have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
        ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag l) :=
      rewire_val_ne' hfar_li hfar_lj
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag l) := by
      have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
      exact congrArg Subtype.val h ▸ lhs_l_rewire
    -- RHS: inner kl else (bFj ≠ bFk, ≠ bFl) → val = bFj
    have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ _; rw [hpj]
      exact fun h => hjk (W.boundaryFlag_injective h)
    have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
      change W.pairing f.val.val ≠ _; rw [hpj]
      exact fun h => hjl (W.boundaryFlag_injective h)
    have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
      have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      rw [h]; exact hpj
    -- outer ij: = bFj → second branch → (gluePairOpen kl).pairing(bFi')
    have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact fun h => hij.symm (W.boundaryFlag_injective h)
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_ne_i (congrArg Subtype.val h)
    have rhs_outer_eq_j : Wkl.pairing g.val =
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
      Subtype.ext rhs_inner
    -- rewire(kl) at bFi takes its first branch, W.pairing bFi being
    --   bFk, giving W.pairing bFl.
    have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
        ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag l) :=
      rewire_val_left' hcross
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag l) := by
      have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_eq_j
      exact congrArg Subtype.val h ▸ rhs_i_rewire
    rw [lhs_val, rhs_val]
  · by_cases hpl : W.pairing f.val.val = W.boundaryFlag l
    · -- Case D: partner = bFl → both give W.pairing(bFj)
      have hpi : W.pairing f.val.val ≠ W.boundaryFlag i := by
        intro h
        have hfk : f.val.val = W.boundaryFlag k := by
          have := congrArg W.pairing h
          rw [W.pairing_invol, hcross] at this
          exact this
        exact absurd (Subtype.ext hfk) f.prop.1
      -- LHS: inner ij else (≠bFi, ≠bFj) → val = bFl
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_inner_eq_l : (rewire hopen_ij f.val).val =
          W.boundaryFlag l := by
        rw [lhs_inner, hpl]
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner_eq_l]
        exact fun h => hkl.symm (W.boundaryFlag_injective h)
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
        fun h => lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_eq_l : Wij.pairing f.val =
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
        Subtype.ext lhs_inner_eq_l
      -- Outer: second branch, giving the ij-glue's pairing at k';
      --   and rewire(ij) at bFk takes its first branch, W.pairing
      --   bFk being bFi, giving W.pairing bFj.
      have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_left' hki
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_eq_l
        exact congrArg Subtype.val h ▸ lhs_k_rewire
      -- RHS: inner kl second branch (≠bFk, =bFl) → val = W.pairing(bFk) = bFi
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        intro h
        change W.pairing f.val.val = _ at h
        have hfi : f.val.val = W.boundaryFlag i := by
          have := congrArg W.pairing h
          rw [W.pairing_invol, hki] at this
          exact this
        exact f.val.prop.1 hfi
      have rhs_eq_l : W.pairing g.val.val = W.boundaryFlag l := by
        change W.pairing f.val.val = _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val =
          W.pairing (W.boundaryFlag k) :=
        @rewire_val_right' _ W k l hopen_kl g.val rhs_ne_k rhs_eq_l
      have rhs_inner_eq_i : (rewire hopen_kl g.val).val =
          W.boundaryFlag i := by
        rw [rhs_inner, hki]
      -- outer ij: = bFi → first branch → (gluePairOpen kl).pairing(bFj')
      have rhs_outer_eq_i : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
        Subtype.ext rhs_inner_eq_i
      -- rewire(kl) at bFj takes its else branch, W.pairing bFj being
      --   neither bFk nor bFl, leaving W.pairing bFj.
      have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_ne' hfar_jk hfar_jl
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
        exact congrArg Subtype.val h ▸ rhs_j_rewire
      rw [lhs_val, rhs_val]
    · -- Case E: none of bFi,bFj,bFk,bFl → both give W.pairing(f.val.val)
      have hpi : W.pairing f.val.val ≠ W.boundaryFlag i := by
        intro h
        have hfk : f.val.val = W.boundaryFlag k := by
          have := congrArg W.pairing h
          rw [W.pairing_invol, hcross] at this
          exact this
        exact absurd (Subtype.ext hfk) f.prop.1
      have hpk : W.pairing f.val.val ≠ W.boundaryFlag k := by
        intro h
        have hfi : f.val.val = W.boundaryFlag i := by
          have := congrArg W.pairing h
          rw [W.pairing_invol, hki] at this
          exact this
        exact f.val.prop.1 hfi
      -- LHS: inner ij else → val = W.pairing(f.val.val); outer kl else
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner]; exact hpk
      have lhs_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
        rw [lhs_inner]; exact hpl
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_ne_l : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
        lhs_ne_l (congrArg Subtype.val h)
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_ne_l
        exact congrArg Subtype.val h ▸ lhs_inner
      -- RHS: inner kl else → val = W.pairing(f.val.val); outer ij else
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; exact hpk
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
        exact @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact hpi
      have rhs_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
        rw [rhs_inner]; exact hpj
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_ne_j : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
        rhs_ne_j (congrArg Subtype.val h)
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_ne_j
        exact congrArg Subtype.val h ▸ rhs_inner
      rw [lhs_val, rhs_val]

private theorem oneCross_ik_equiv_attach_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij hcross
        hfar_jl))).Flag) :
    ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_ik_second_open_ij W hij hkl hik hil hjk hjl hopen_kl hcross
        hfar_jl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).attach (doubleSurvivingSwap W hik hil hjk hjl f) =
      ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij hcross
        hfar_jl))).attach f).map (_root_.Equiv.refl W.Vertex) id := by
  classical
  exact doubleGlueAttach_comm W hik hil hjk hjl f

/-- Configuration (2), variant {ik}: one cross-edge `W.pairing(bFi) = bFk`.
Both glues are open in both orders; circles = `W.circles`. -/
private def oneCross_ik_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_ik_second_open_kl W hij hkl hik hil hjk hjl hopen_ij hcross
        hfar_jl)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_ik_second_open_ij W hij hkl hik hil hjk hjl hopen_kl hcross
        hfar_jl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm := oneCross_ik_equiv_attach_comm W hij hkl hik hil hjk hjl hopen_ij hopen_kl
      hcross hfar_jl
  pairing_comm := oneCross_ik_equiv_pairing_comm W hij hkl hik hil hjk hjl hopen_ij
      hopen_kl hcross hfar_jl
  circles_eq := rfl

/-! ### Configuration (2): one cross-edge, variant {il} -/

-- Second kl-glue is open after ij-glue (cross il variant).
private theorem oneCross_il_second_open_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  intro heq
  have h_ne_i : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
    hkl (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hcross))
  have h_ne_j : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hfar_jk (W.pairing_boundaryFlag_comm h)
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag k) := rewire_val_ne' h_ne_i h_ne_j
  exact hopen_kl (hval.symm ▸ congrArg Subtype.val heq)

-- Second ij-glue is open after kl-glue (cross il variant).
private theorem oneCross_il_second_open_ij
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (_hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  intro heq
  have h_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h =>
    hkl (W.boundaryFlag_injective (h.symm.trans hcross))
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag k) :=
    rewire_val_right' h_ne_k hcross
  have hfar_kj : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hfar_jk (W.pairing_boundaryFlag_comm h)
  exact hfar_kj (hval.symm ▸ congrArg Subtype.val heq)

/-- Configuration (2), variant {il}: one cross-edge `W.pairing(bFi) = bFl`.
Both glues are open in both orders; circles = `W.circles`. -/
private def oneCross_il_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    apply Subtype.ext; apply Subtype.ext
    -- ═══════ THE ATTACHMENT AND FLAG SIDES ARE SHARED ═══════
    -- Only the pairing distinguishes this configuration, so what
    -- follows is the five-way case analysis on the partner of the
    -- flag, at the cross-edge this configuration carries.
    -- Name the two single glues; every transport below is
    -- read at one of them.
    let Wij := W.gluePairOpen i j hij hopen_ij
    let Wkl := W.gluePairOpen k l hkl hopen_kl
    let g := doubleSurvivingSwap W hik hil hjk hjl f
    change (rewire (oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
            hopen_ij hopen_kl hcross hfar_jk) f).val.val =
         (rewire (oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
            hopen_ij hopen_kl hcross hfar_jk) g).val.val
    have hli : W.pairing (W.boundaryFlag l) = W.boundaryFlag i :=
      W.pairing_boundaryFlag_comm hcross
    have hfar_kj : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
      hfar_jk (W.pairing_boundaryFlag_comm h)
    have hfar_ki : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
      hkl (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
        hcross))
    have hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l := fun h =>
      hij (W.boundaryFlag_injective (hli.symm.trans (W.pairing_boundaryFlag_comm
        h)))
    let hopen_ij_kl := oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk
    let hopen_kl_ij := oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk
    rcases partner_cases W f.val.val i l j k with
        hpi | ⟨hpi, hpl⟩ | ⟨hpi, hpl, hpj⟩ | ⟨hpi, hpl, hpj, hpk⟩ |
        ⟨hpi, hpl, hpj, hpk⟩
    · -- Impossible: f.val.val = bFl
      have hfl : f.val.val = W.boundaryFlag l := by
        have h := congrArg W.pairing hpi
        rw [W.pairing_invol] at h
        exact h.trans hcross
      exact absurd (Subtype.ext hfl) f.prop.2
    · -- Impossible: f.val.val = bFi
      have hfi : f.val.val = W.boundaryFlag i := by
        have h := congrArg W.pairing hpl
        rw [W.pairing_invol] at h
        exact h.trans hli
      exact absurd hfi f.val.prop.1
    · -- Case: partner = bFj → both give W.pairing(bFk)
      have lhs_inner : (rewire hopen_ij f.val).val =
          W.pairing (W.boundaryFlag i) :=
        rewire_val_right' hpi hpj
      have lhs_inner_eq_l : (rewire hopen_ij f.val).val = W.boundaryFlag l := by
        rw [lhs_inner, hcross]
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        (fun h' => hkl.symm (W.boundaryFlag_injective h'))
          (lhs_inner_eq_l ▸ congrArg Subtype.val h)
      have lhs_outer_eq_l : Wij.pairing f.val =
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
        Subtype.ext lhs_inner_eq_l
      have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag k) :=
        rewire_val_ne' hfar_ki hfar_kj
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag k) := by
        have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_eq_l
        exact congrArg Subtype.val h ▸ lhs_k_rewire
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; rw [hpj]
        exact fun h => hjk (W.boundaryFlag_injective h)
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; rw [hpj]
        exact fun h => hjl (W.boundaryFlag_injective h)
      have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
        have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
        rw [h]; exact hpj
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact fun h => hij.symm (W.boundaryFlag_injective h)
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_eq_j : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
        Subtype.ext rhs_inner
      have rhs_i_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h
        =>
        hkl (W.boundaryFlag_injective (h.symm.trans hcross))
      have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag k) :=
        rewire_val_right' rhs_i_ne_k hcross
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag k) := by
        have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_eq_j
        exact congrArg Subtype.val h ▸ rhs_i_rewire
      rw [lhs_val, rhs_val]
    · -- Case: partner = bFk → both give W.pairing(bFj)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
        rw [lhs_inner, hpk]
      have lhs_outer_eq_k : Wij.pairing f.val =
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
        Subtype.ext lhs_inner_eq_k
      have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_left' hli
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
        exact congrArg Subtype.val h ▸ lhs_l_rewire
      have rhs_eq_k : W.pairing g.val.val = W.boundaryFlag k := by
        change W.pairing f.val.val = _; exact hpk
      have rhs_inner : (rewire hopen_kl g.val).val =
          W.pairing (W.boundaryFlag l) :=
        @rewire_val_left' _ W k l hopen_kl g.val rhs_eq_k
      have rhs_inner_eq_i : (rewire hopen_kl g.val).val = W.boundaryFlag i := by
        rw [rhs_inner, hli]
      have rhs_outer_eq_i : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
        Subtype.ext rhs_inner_eq_i
      have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_ne' hfar_jk hfar_jl
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
        exact congrArg Subtype.val h ▸ rhs_j_rewire
      rw [lhs_val, rhs_val]
    · -- Case: none → both give W.pairing(f.val.val)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner]; exact hpk
      have lhs_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
        rw [lhs_inner]; exact hpl
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_ne_l : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
        lhs_ne_l (congrArg Subtype.val h)
      have lhs_val : (rewire hopen_ij_kl f).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_ne_l
        exact congrArg Subtype.val h ▸ lhs_inner
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; exact hpk
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
        exact @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact hpi
      have rhs_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
        rw [rhs_inner]; exact hpj
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_ne_j : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
        rhs_ne_j (congrArg Subtype.val h)
      have rhs_val : (rewire hopen_kl_ij g).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_ne_j
        exact congrArg Subtype.val h ▸ rhs_inner
      rw [lhs_val, rhs_val]
  circles_eq := rfl

/-! ### Configuration (2): one cross-edge, variant {jk} -/

-- Second kl-glue is open after ij-glue (cross jk variant).
private theorem oneCross_jk_second_open_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  intro heq
  have hkj : W.pairing (W.boundaryFlag k) = W.boundaryFlag j :=
    W.pairing_boundaryFlag_comm hcross
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag i) := rewire_val_right'
        (fun h => hij.symm (W.boundaryFlag_injective (hkj ▸ h))) hkj
  exact hfar_il (hval.symm ▸ congrArg Subtype.val heq)

-- Second ij-glue is open after kl-glue (cross jk variant).
private theorem oneCross_jk_second_open_ij
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  intro heq
  have h_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h =>
    hij (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      (W.pairing_boundaryFlag_comm hcross)))
  have h_ne_l : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l := hfar_il
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag i) := rewire_val_ne' h_ne_k h_ne_l
  have hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j := fun h =>
    hik (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hcross))
  exact hopen_ij (hval.symm ▸ congrArg Subtype.val heq)

/-- Configuration (2), variant {jk}: one cross-edge `W.pairing(bFj) = bFk`.
Both glues are open in both orders; circles = `W.circles`. -/
private def oneCross_jk_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag k)
    (hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jk_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hcross hfar_il)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_jk_second_open_ij W hij hkl hik hil hjk hjl
        hopen_kl hcross hfar_il)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    apply Subtype.ext; apply Subtype.ext
    -- ═══════ THE ATTACHMENT AND FLAG SIDES ARE SHARED ═══════
    -- Only the pairing distinguishes this configuration, so what
    -- follows is the five-way case analysis on the partner of the
    -- flag, at the cross-edge this configuration carries.
    -- Name the two single glues; every transport below is
    -- read at one of them.
    let Wij := W.gluePairOpen i j hij hopen_ij
    let Wkl := W.gluePairOpen k l hkl hopen_kl
    let g := doubleSurvivingSwap W hik hil hjk hjl f
    change (rewire (oneCross_jk_second_open_kl W hij hkl hik hil hjk hjl
            hopen_ij hcross hfar_il) f).val.val =
         (rewire (oneCross_jk_second_open_ij W hij hkl hik hil hjk hjl
            hopen_kl hcross hfar_il) g).val.val
    have hkj : W.pairing (W.boundaryFlag k) = W.boundaryFlag j :=
      W.pairing_boundaryFlag_comm hcross
    have hfar_li : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag i := fun h =>
      hfar_il (W.pairing_boundaryFlag_comm h)
    have hfar_lj : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag j := fun h =>
      hkl.symm (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm
        h).symm.trans hcross))
    have hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h =>
      hij (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
        hkj))
    let hopen_ij_kl := oneCross_jk_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hcross hfar_il
    let hopen_kl_ij := oneCross_jk_second_open_ij W hij hkl hik hil hjk hjl
        hopen_kl hcross hfar_il
    rcases partner_cases W f.val.val j k i l with
        hpj | ⟨hpj, hpk⟩ | ⟨hpj, hpk, hpi⟩ | ⟨hpj, hpk, hpi, hpl⟩ |
        ⟨hpj, hpk, hpi, hpl⟩
    · -- Impossible: f.val.val = bFk
      have hfk : f.val.val = W.boundaryFlag k := by
        have h := congrArg W.pairing hpj
        rw [W.pairing_invol] at h
        exact h.trans hcross
      exact absurd (Subtype.ext hfk) f.prop.1
    · -- Impossible: f.val.val = bFj
      have hfj : f.val.val = W.boundaryFlag j := by
        have h := congrArg W.pairing hpk
        rw [W.pairing_invol] at h
        exact h.trans hkj
      exact absurd hfj f.val.prop.2
    · -- Case: partner = bFi → both give W.pairing(bFl)
      have lhs_inner : (rewire hopen_ij f.val).val =
          W.pairing (W.boundaryFlag j) :=
        rewire_val_left' hpi
      have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
        rw [lhs_inner, hcross]
      have lhs_outer_eq_k : Wij.pairing f.val =
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
        Subtype.ext lhs_inner_eq_k
      have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag l) :=
        rewire_val_ne' hfar_li hfar_lj
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag l) := by
        have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
        exact congrArg Subtype.val h ▸ lhs_l_rewire
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; rw [hpi]
        exact fun h => hik (W.boundaryFlag_injective h)
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; rw [hpi]
        exact fun h => hil (W.boundaryFlag_injective h)
      have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag i := by
        have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
        rw [h]; exact hpi
      have rhs_outer_eq_i : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
        Subtype.ext rhs_inner
      have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag l) :=
        rewire_val_left' hcross
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag l) := by
        have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
        exact congrArg Subtype.val h ▸ rhs_j_rewire
      rw [lhs_val, rhs_val]
    · -- Case: partner = bFl → both give W.pairing(bFi)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_inner_eq_l : (rewire hopen_ij f.val).val = W.boundaryFlag l := by
        rw [lhs_inner, hpl]
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner_eq_l]
        exact fun h => hkl.symm (W.boundaryFlag_injective h)
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_eq_l : Wij.pairing f.val =
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
        Subtype.ext lhs_inner_eq_l
      have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag i) :=
        rewire_val_right' (fun h => hij.symm (W.boundaryFlag_injective (hkj ▸
          h))) hkj
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag i) := by
        have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_eq_l
        exact congrArg Subtype.val h ▸ lhs_k_rewire
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; exact hpk
      have rhs_eq_l : W.pairing g.val.val = W.boundaryFlag l := by
        change W.pairing f.val.val = _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val =
          W.pairing (W.boundaryFlag k) :=
        @rewire_val_right' _ W k l hopen_kl g.val rhs_ne_k rhs_eq_l
      have rhs_inner_eq_j : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
        rw [rhs_inner, hkj]
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner_eq_j]
        exact fun h => hij.symm (W.boundaryFlag_injective h)
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_eq_j : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
        Subtype.ext rhs_inner_eq_j
      have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag i) :=
        rewire_val_ne' hfar_ik hfar_il
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag i) := by
        have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_eq_j
        exact congrArg Subtype.val h ▸ rhs_i_rewire
      rw [lhs_val, rhs_val]
    · -- Case: none → both give W.pairing(f.val.val)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner]; exact hpk
      have lhs_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
        rw [lhs_inner]; exact hpl
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_ne_l : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
        lhs_ne_l (congrArg Subtype.val h)
      have lhs_val : (rewire hopen_ij_kl f).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_ne_l
        exact congrArg Subtype.val h ▸ lhs_inner
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; exact hpk
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
        exact @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact hpi
      have rhs_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
        rw [rhs_inner]; exact hpj
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_ne_j : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
        rhs_ne_j (congrArg Subtype.val h)
      have rhs_val : (rewire hopen_kl_ij g).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_ne_j
        exact congrArg Subtype.val h ▸ rhs_inner
      rw [lhs_val, rhs_val]
  circles_eq := rfl

/-! ### Configuration (2): one cross-edge, variant {jl} -/

-- Second kl-glue is open after ij-glue (cross jl variant).
private theorem oneCross_jl_second_open_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) ≠
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  intro heq
  have h_ne_i : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
    hfar_ik (W.pairing_boundaryFlag_comm h)
  have h_ne_j : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hkl (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hcross))
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag k) := rewire_val_ne' h_ne_i h_ne_j
  exact hopen_kl (hval.symm ▸ congrArg Subtype.val heq)

-- Second ij-glue is open after kl-glue (cross jl variant).
private theorem oneCross_jl_second_open_ij
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (_hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) ≠
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  intro heq
  have h_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := hfar_ik
  have h_ne_l : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l := fun h =>
    hij (W.boundaryFlag_injective
      ((W.pairing_boundaryFlag_comm h).symm.trans (W.pairing_boundaryFlag_comm
        hcross)))
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag i) := rewire_val_ne' h_ne_k h_ne_l
  have hopen_ij' : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j := fun h =>
    hil (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hcross))
  exact hopen_ij' (hval.symm ▸ congrArg Subtype.val heq)

private theorem oneCross_jl_equiv_pairing_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik))).Flag) :
    doubleSurvivingSwap W hik hil hjk hjl ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik))).pairing f) =
      ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_jl_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).pairing (doubleSurvivingSwap W hik hil hjk
            hjl f) := by
  classical
  apply Subtype.ext; apply Subtype.ext
  -- ═══════ THE ATTACHMENT AND FLAG SIDES ARE SHARED ═══════
  -- Only the pairing distinguishes this configuration, so what
  -- follows is the five-way case analysis on the partner of the
  -- flag, at the cross-edge this configuration carries.
  -- Name the two single glues; every transport below is
  -- read at one of them.
  let Wij := W.gluePairOpen i j hij hopen_ij
  let Wkl := W.gluePairOpen k l hkl hopen_kl
  let g := doubleSurvivingSwap W hik hil hjk hjl f
  change (rewire (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
          hopen_ij hopen_kl hcross hfar_ik) f).val.val =
       (rewire (oneCross_jl_second_open_ij W hij hkl hik hil hjk hjl
          hopen_ij hopen_kl hcross hfar_ik) g).val.val
  have hlj : W.pairing (W.boundaryFlag l) = W.boundaryFlag j :=
    W.pairing_boundaryFlag_comm hcross
  have hfar_ki : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
    hfar_ik (W.pairing_boundaryFlag_comm h)
  have hfar_kj : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
    hkl (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hcross))
  have hfar_il : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag l := fun h =>
    hij (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
      hlj))
  let hopen_ij_kl := oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
      hopen_ij hopen_kl hcross hfar_ik
  let hopen_kl_ij := oneCross_jl_second_open_ij W hij hkl hik hil hjk hjl
      hopen_ij hopen_kl hcross hfar_ik
  rcases partner_cases W f.val.val j l i k with
      hpj | ⟨hpj, hpl⟩ | ⟨hpj, hpl, hpi⟩ | ⟨hpj, hpl, hpi, hpk⟩ |
      ⟨hpj, hpl, hpi, hpk⟩
  · -- Impossible: f.val.val = bFl
    have hfl : f.val.val = W.boundaryFlag l := by
      have h := congrArg W.pairing hpj
      rw [W.pairing_invol] at h
      exact h.trans hcross
    exact absurd (Subtype.ext hfl) f.prop.2
  · -- Impossible: f.val.val = bFj
    have hfj : f.val.val = W.boundaryFlag j := by
      have h := congrArg W.pairing hpl
      rw [W.pairing_invol] at h
      exact h.trans hlj
    exact absurd hfj f.val.prop.2
  · -- Case: partner = bFi → both give W.pairing(bFk)
    have lhs_inner : (rewire hopen_ij f.val).val =
        W.pairing (W.boundaryFlag j) :=
      rewire_val_left' hpi
    have lhs_inner_eq_l : (rewire hopen_ij f.val).val = W.boundaryFlag l := by
      rw [lhs_inner, hcross]
    have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
      rw [lhs_inner_eq_l]
      exact fun h => hkl.symm (W.boundaryFlag_injective h)
    have lhs_outer_ne_k : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
      lhs_ne_k (congrArg Subtype.val h)
    have lhs_outer_eq_l : Wij.pairing f.val =
        Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
      Subtype.ext lhs_inner_eq_l
    have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
        ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag k) :=
      rewire_val_ne' hfar_ki hfar_kj
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag k) := by
      have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
        lhs_outer_eq_l
      exact congrArg Subtype.val h ▸ lhs_k_rewire
    have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ _; rw [hpi]
      exact fun h => hik (W.boundaryFlag_injective h)
    have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
      change W.pairing f.val.val ≠ _; rw [hpi]
      exact fun h => hil (W.boundaryFlag_injective h)
    have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag i := by
      have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      rw [h]; exact hpi
    have rhs_outer_eq_i : Wkl.pairing g.val =
        Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
      Subtype.ext rhs_inner
    have rhs_j_ne_k : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k := fun h
      =>
      hkl (W.boundaryFlag_injective (h.symm.trans hcross))
    have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
        ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag k) :=
      rewire_val_right' rhs_j_ne_k hcross
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag k) := by
      have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
      exact congrArg Subtype.val h ▸ rhs_j_rewire
    rw [lhs_val, rhs_val]
  · -- Case: partner = bFk → both give W.pairing(bFi)
    have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
      rw [lhs_inner, hpk]
    have lhs_outer_eq_k : Wij.pairing f.val =
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
      Subtype.ext lhs_inner_eq_k
    have lhs_l_ne_i : W.pairing (W.boundaryFlag l) ≠ W.boundaryFlag i := fun h
      =>
      hfar_il (W.pairing_boundaryFlag_comm h)
    have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
        ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag i) :=
      rewire_val_right' lhs_l_ne_i hlj
    have lhs_val : (rewire hopen_ij_kl f).val.val =
        W.pairing (W.boundaryFlag i) := by
      have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
      exact congrArg Subtype.val h ▸ lhs_l_rewire
    have rhs_eq_k : W.pairing g.val.val = W.boundaryFlag k := by
      change W.pairing f.val.val = _; exact hpk
    have rhs_inner : (rewire hopen_kl g.val).val =
        W.pairing (W.boundaryFlag l) :=
      @rewire_val_left' _ W k l hopen_kl g.val rhs_eq_k
    have rhs_inner_eq_j : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
      rw [rhs_inner, hlj]
    have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner_eq_j]
      exact fun h => hij.symm (W.boundaryFlag_injective h)
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_ne_i (congrArg Subtype.val h)
    have rhs_outer_eq_j : Wkl.pairing g.val =
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
      Subtype.ext rhs_inner_eq_j
    have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
        ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag i) :=
      rewire_val_ne' hfar_ik hfar_il
    have rhs_val : (rewire hopen_kl_ij g).val.val =
        W.pairing (W.boundaryFlag i) := by
      have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_eq_j
      exact congrArg Subtype.val h ▸ rhs_i_rewire
    rw [lhs_val, rhs_val]
  · -- Case: none → both give W.pairing(f.val.val)
    have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
      rw [lhs_inner]; exact hpk
    have lhs_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
      rw [lhs_inner]; exact hpl
    have lhs_outer_ne_k : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
      lhs_ne_k (congrArg Subtype.val h)
    have lhs_outer_ne_l : Wij.pairing f.val ≠
        Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
      lhs_ne_l (congrArg Subtype.val h)
    have lhs_val : (rewire hopen_ij_kl f).val.val = W.pairing f.val.val := by
      have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
        lhs_outer_ne_l
      exact congrArg Subtype.val h ▸ lhs_inner
    have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
      change W.pairing f.val.val ≠ _; exact hpk
    have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
      change W.pairing f.val.val ≠ _; exact hpl
    have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
      exact @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
    have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
      rw [rhs_inner]; exact hpi
    have rhs_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
      rw [rhs_inner]; exact hpj
    have rhs_outer_ne_i : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
      rhs_ne_i (congrArg Subtype.val h)
    have rhs_outer_ne_j : Wkl.pairing g.val ≠
        Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
      rhs_ne_j (congrArg Subtype.val h)
    have rhs_val : (rewire hopen_kl_ij g).val.val = W.pairing f.val.val := by
      have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
        rhs_outer_ne_j
      exact congrArg Subtype.val h ▸ rhs_inner
    rw [lhs_val, rhs_val]

private theorem oneCross_jl_equiv_attach_comm
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k)
    (f : (((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik))).Flag) :
    ((((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_jl_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm)).attach (doubleSurvivingSwap W hik hil hjk hjl f) =
      ((((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik))).attach f).map (_root_.Equiv.refl W.Vertex) id := by
  classical
  exact doubleGlueAttach_comm W hik hil hjk hjl f

/-- Configuration (2), variant {jl}: one cross-edge `W.pairing(bFj) = bFl`.
Both glues are open in both orders; circles = `W.circles`. -/
private def oneCross_jl_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag j) = W.boundaryFlag l)
    (hfar_ik : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (oneCross_jl_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (oneCross_jl_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_ik)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm := oneCross_jl_equiv_attach_comm W hij hkl hik hil hjk hjl hopen_ij hopen_kl
      hcross hfar_ik
  pairing_comm := oneCross_jl_equiv_pairing_comm W hij hkl hik hil hjk hjl hopen_ij
      hopen_kl hcross hfar_ik
  circles_eq := rfl

/-! ### Configuration (3): two cross-edges (open then closed) -/

-- Second kl-glue is CLOSED after ij-glue (two crosses, ik+jl variant).
private theorem twoCross_ikjl_second_closed_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hcross_ik : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hcross_jl : W.pairing (W.boundaryFlag j) = W.boundaryFlag l) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) =
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  apply Subtype.ext
  have hki : W.pairing (W.boundaryFlag k) = W.boundaryFlag i :=
    W.pairing_boundaryFlag_comm hcross_ik
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag j) := rewire_val_left' hki
  exact hval.trans hcross_jl

-- Second ij-glue is CLOSED after kl-glue (two crosses, ik+jl variant).
private theorem twoCross_ikjl_second_closed_ij
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross_ik : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hcross_jl : W.pairing (W.boundaryFlag j) = W.boundaryFlag l) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) =
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  apply Subtype.ext
  have hlj : W.pairing (W.boundaryFlag l) = W.boundaryFlag j :=
    W.pairing_boundaryFlag_comm hcross_jl
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag l) := rewire_val_left' hcross_ik
  exact hval.trans hlj

/-- Configuration (3), variant {ik,jl}: two cross-edges.
First glue is open, second is closed; circles = `W.circles + 1`. -/
private def twoCross_ikjl_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross_ik : W.pairing (W.boundaryFlag i) = W.boundaryFlag k)
    (hcross_jl : W.pairing (W.boundaryFlag j) = W.boundaryFlag l) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairClosed
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (twoCross_ikjl_second_closed_kl W hij hkl hik hil hjk hjl
        hopen_ij hcross_ik hcross_jl)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairClosed
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (twoCross_ikjl_second_closed_ij W hij hkl hik hil hjk hjl
        hopen_kl hcross_ik hcross_jl)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    apply Subtype.ext; apply Subtype.ext
    change (rewire hopen_ij f.val).val = (rewire hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val).val
    have hki : W.pairing (W.boundaryFlag k) = W.boundaryFlag i :=
      W.pairing_boundaryFlag_comm hcross_ik
    have hlj : W.pairing (W.boundaryFlag l) = W.boundaryFlag j :=
      W.pairing_boundaryFlag_comm hcross_jl
    have hpi : W.pairing f.val.val ≠ W.boundaryFlag i := fun h =>
      (fun hfk : f.val.val = W.boundaryFlag k => f.prop.1 (Subtype.ext hfk))
        (by have := congrArg W.pairing h; rw [W.pairing_invol] at this; exact
          this.trans hcross_ik)
    have hpj : W.pairing f.val.val ≠ W.boundaryFlag j := fun h =>
      (fun hfl : f.val.val = W.boundaryFlag l => f.prop.2 (Subtype.ext hfl))
        (by have := congrArg W.pairing h; rw [W.pairing_invol] at this; exact
          this.trans hcross_jl)
    have hpk : W.pairing f.val.val ≠ W.boundaryFlag k := fun h =>
      f.val.prop.1 (by
        have := congrArg W.pairing h
        rw [W.pairing_invol] at this
        exact this.trans hki)
    have hpl : W.pairing f.val.val ≠ W.boundaryFlag l := fun h =>
      f.val.prop.2 (by
        have := congrArg W.pairing h
        rw [W.pairing_invol] at this
        exact this.trans hlj)
    have lhs_val : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have rhs_val : (rewire hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val).val =
        W.pairing f.val.val :=
      @rewire_val_ne' _ W k l hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val hpk hpl
    rw [lhs_val, rhs_val]
  circles_eq := rfl

-- Second kl-glue is CLOSED after ij-glue (two crosses, il+jk variant).
private theorem twoCross_iljk_second_closed_kl
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (_hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hcross_il : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hcross_jk : W.pairing (W.boundaryFlag j) = W.boundaryFlag k) :
    (W.gluePairOpen i j hij hopen_ij).pairing
      ((W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨k, hik.symm, hjk.symm⟩) =
    (W.gluePairOpen i j hij hopen_ij).boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := by
  apply Subtype.ext
  have hkj : W.pairing (W.boundaryFlag k) = W.boundaryFlag j :=
    W.pairing_boundaryFlag_comm hcross_jk
  have hval : (rewire hopen_ij (glueBoundaryFlag W i j ⟨k, hik.symm,
    hjk.symm⟩)).val =
      W.pairing (W.boundaryFlag i) :=
    rewire_val_right' (fun h => hij.symm (W.boundaryFlag_injective (hkj ▸ h)))
      hkj
  exact hval.trans hcross_il

-- Second ij-glue is CLOSED after kl-glue (two crosses, il+jk variant).
private theorem twoCross_iljk_second_closed_ij
    (W : Fragment α) {i j k l : α}
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross_il : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hcross_jk : W.pairing (W.boundaryFlag j) = W.boundaryFlag k) :
    (W.gluePairOpen k l hkl hopen_kl).pairing
      ((W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨i, hik, hil⟩) =
    (W.gluePairOpen k l hkl hopen_kl).boundaryFlag ⟨j, hjk, hjl⟩ := by
  apply Subtype.ext
  have hkj : W.pairing (W.boundaryFlag k) = W.boundaryFlag j :=
    W.pairing_boundaryFlag_comm hcross_jk
  have h_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h =>
    hkl (W.boundaryFlag_injective (h.symm.trans hcross_il))
  have hval : (rewire hopen_kl (glueBoundaryFlag W k l ⟨i, hik, hil⟩)).val =
      W.pairing (W.boundaryFlag k) :=
    rewire_val_right' h_ne_k hcross_il
  exact hval.trans hkj

/-- Configuration (3), variant {il,jk}: two cross-edges.
First glue is open, second is closed; circles = `W.circles + 1`. -/
private def twoCross_iljk_equiv [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross_il : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hcross_jk : W.pairing (W.boundaryFlag j) = W.boundaryFlag k) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairClosed
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (twoCross_iljk_second_closed_kl W hij hkl hik hil hjk hjl
        hopen_ij hcross_il hcross_jk)).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairClosed
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (twoCross_iljk_second_closed_ij W hij hkl hik hil hjk hjl
        hopen_kl hcross_il hcross_jk)).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    apply Subtype.ext; apply Subtype.ext
    change (rewire hopen_ij f.val).val = (rewire hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val).val
    have hli : W.pairing (W.boundaryFlag l) = W.boundaryFlag i :=
      W.pairing_boundaryFlag_comm hcross_il
    have hkj : W.pairing (W.boundaryFlag k) = W.boundaryFlag j :=
      W.pairing_boundaryFlag_comm hcross_jk
    have hpi : W.pairing f.val.val ≠ W.boundaryFlag i := fun h =>
      (fun hfl : f.val.val = W.boundaryFlag l => f.prop.2 (Subtype.ext hfl))
        (by have := congrArg W.pairing h; rw [W.pairing_invol] at this; exact
          this.trans hcross_il)
    have hpj : W.pairing f.val.val ≠ W.boundaryFlag j := fun h =>
      (fun hfk : f.val.val = W.boundaryFlag k => f.prop.1 (Subtype.ext hfk))
        (by have := congrArg W.pairing h; rw [W.pairing_invol] at this; exact
          this.trans hcross_jk)
    have hpk : W.pairing f.val.val ≠ W.boundaryFlag k := fun h =>
      f.val.prop.2 (by
        have := congrArg W.pairing h
        rw [W.pairing_invol] at this
        exact this.trans hkj)
    have hpl : W.pairing f.val.val ≠ W.boundaryFlag l := fun h =>
      f.val.prop.1 (by
        have := congrArg W.pairing h
        rw [W.pairing_invol] at this
        exact this.trans hli)
    have lhs_val : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
      rewire_val_ne' hpi hpj
    have rhs_val : (rewire hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val).val =
        W.pairing f.val.val :=
      @rewire_val_ne' _ W k l hopen_kl
        (doubleSurvivingSwap W hik hil hjk hjl f).val hpk hpl
    rw [lhs_val, rhs_val]
  circles_eq := rfl

/-! ### Main dispatch: `gluePairComm` -/

/-- Two single-pair glues at disjoint label pairs commute up to
fragment equivalence. -/
def gluePairComm [DecidableEq α]
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ((W.gluePair i j hij).gluePair
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))).Equiv
    (((W.gluePair k l hkl).gluePair
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) := by
  by_cases h_ij : W.pairing (W.boundaryFlag i) = W.boundaryFlag j
  · -- {i,j} is a closed pair
    rw [gluePair_eq_closed hij h_ij]
    by_cases h_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l
    · -- Config (4): both closed
      rw [gluePair_eq_closed hkl h_kl]
      rw [gluePair_eq_closed _ (closedClosed_second_ij W hik hil hjk hjl h_ij
        h_kl)]
      rw [gluePair_eq_closed _ (closedClosed_second_kl W hik hil hjk hjl h_ij
        h_kl)]
      exact closedClosed_equiv W hij hkl hik hil hjk hjl h_ij h_kl
    · -- Config (1): ij closed, kl open
      rw [gluePair_eq_open hkl h_kl]
      rw [gluePair_eq_open _ (closedOpen_second_open W hik hil hjk hjl h_ij
        h_kl)]
      rw [gluePair_eq_closed _ (closedOpen_second_closed W hkl hik hil hjk hjl
        h_ij h_kl)]
      exact closedOpen_equiv W hij hkl hik hil hjk hjl h_ij h_kl
  · -- {i,j} is an open pair
    rw [gluePair_eq_open hij h_ij]
    by_cases h_kl : W.pairing (W.boundaryFlag k) = W.boundaryFlag l
    · -- Config (1'): ij open, kl closed
      rw [gluePair_eq_closed hkl h_kl]
      rw [gluePair_eq_closed _ (openClosed_second_closed W hij hik hil hjk hjl
        h_ij h_kl)]
      rw [gluePair_eq_open _ (openClosed_second_open W hik hil hjk hjl h_ij
        h_kl)]
      exact openClosed_equiv W hij hkl hik hil hjk hjl h_ij h_kl
    · -- Both open: dispatch on cross-edges
      rw [gluePair_eq_open hkl h_kl]
      by_cases hcross_ik : W.pairing (W.boundaryFlag i) = W.boundaryFlag k
      · by_cases hcross_jl : W.pairing (W.boundaryFlag j) = W.boundaryFlag l
        · -- Config (3): two crosses {ik, jl}
          rw [gluePair_eq_closed _ (twoCross_ikjl_second_closed_kl W hij hkl hik
            hil hjk hjl
            h_ij hcross_ik hcross_jl)]
          rw [gluePair_eq_closed _ (twoCross_ikjl_second_closed_ij W hij hkl hik
            hil hjk hjl
            h_kl hcross_ik hcross_jl)]
          exact twoCross_ikjl_equiv W hij hkl hik hil hjk hjl h_ij h_kl
            hcross_ik hcross_jl
        · -- Config (2) variant {ik}
          rw [gluePair_eq_open _ (oneCross_ik_second_open_kl W hij hkl hik hil
            hjk hjl
            h_ij hcross_ik hcross_jl)]
          rw [gluePair_eq_open _ (oneCross_ik_second_open_ij W hij hkl hik hil
            hjk hjl
            h_kl hcross_ik hcross_jl)]
          exact oneCross_ik_equiv W hij hkl hik hil hjk hjl h_ij h_kl
            hcross_ik hcross_jl
      · by_cases hcross_il : W.pairing (W.boundaryFlag i) = W.boundaryFlag l
        · by_cases hcross_jk : W.pairing (W.boundaryFlag j) = W.boundaryFlag k
          · -- Config (3): two crosses {il, jk}
            rw [gluePair_eq_closed _ (twoCross_iljk_second_closed_kl W hij hkl
              hik hil hjk hjl
              h_ij hcross_il hcross_jk)]
            rw [gluePair_eq_closed _ (twoCross_iljk_second_closed_ij W hij hkl
              hik hil hjk hjl
              h_kl hcross_il hcross_jk)]
            exact twoCross_iljk_equiv W hij hkl hik hil hjk hjl h_ij h_kl
              hcross_il hcross_jk
          · -- Config (2) variant {il}
            rw [gluePair_eq_open _ (oneCross_il_second_open_kl W hij hkl hik hil
              hjk hjl
              h_ij h_kl hcross_il hcross_jk)]
            rw [gluePair_eq_open _ (oneCross_il_second_open_ij W hij hkl hik hil
              hjk hjl
              h_ij h_kl hcross_il hcross_jk)]
            exact oneCross_il_equiv W hij hkl hik hil hjk hjl h_ij h_kl
              hcross_il hcross_jk
        · by_cases hcross_jk : W.pairing (W.boundaryFlag j) = W.boundaryFlag k
          · -- Config (2) variant {jk}
            rw [gluePair_eq_open _ (oneCross_jk_second_open_kl W hij hkl hik hil
              hjk hjl
              h_ij hcross_jk hcross_il)]
            rw [gluePair_eq_open _ (oneCross_jk_second_open_ij W hij hkl hik hil
              hjk hjl
              h_kl hcross_jk hcross_il)]
            exact oneCross_jk_equiv W hij hkl hik hil hjk hjl h_ij h_kl
              hcross_jk hcross_il
          · by_cases hcross_jl : W.pairing (W.boundaryFlag j) = W.boundaryFlag l
            · -- Config (2) variant {jl}
              rw [gluePair_eq_open _ (oneCross_jl_second_open_kl W hij hkl hik
                hil hjk hjl
                h_ij h_kl hcross_jl hcross_ik)]
              rw [gluePair_eq_open _ (oneCross_jl_second_open_ij W hij hkl hik
                hil hjk hjl
                h_ij h_kl hcross_jl hcross_ik)]
              exact oneCross_jl_equiv W hij hkl hik hil hjk hjl h_ij h_kl
                hcross_jl hcross_ik
            · -- Config (0): all boundary pairs disjoint
              rw [gluePair_eq_open _ (openOpen_second_open_ij W hij hik hil hjk
                hjl
                h_ij h_kl hcross_ik hcross_jk)]
              rw [gluePair_eq_open _ (openOpen_second_open_kl W hkl hik hil hjk
                hjl
                h_ij h_kl hcross_ik hcross_il)]
              exact openOpen_disjoint_equiv W hij hkl hik hil hjk hjl h_ij h_kl
                hcross_ik hcross_il hcross_jk hcross_jl

end Fragment

end RS
