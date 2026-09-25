/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueComm

/-!
# Gluing in an ambient union

The two normalization equivalences behind associativity of
composition: disjoint union of fragments is associative up to
equivalence (with the label re-bracketing), and a single-pair glue
commutes with extending the ambient fragment by a disjoint union.
-/

@[expose] public section

namespace RS

variable {α β γ : Type}

/-! ### Glue-in-ambient equivalence -/

namespace Fragment

variable {α β : Type}

/-- The label equivalence for gluing inside an ambient union:
surviving labels of the sum at an inl-pair decompose as
the surviving labels of the left factor plus the right labels. -/
def ambientLabelEquiv (i j : α) :
    SurvivingLabel (α ⊕ β) (Sum.inl i) (Sum.inl j) ≃
      (SurvivingLabel α i j ⊕ β) where
  toFun x :=
    match hx : x.val with
    | Sum.inl a => Sum.inl ⟨a,
        fun h => x.prop.1 (hx ▸ congrArg Sum.inl h),
        fun h => x.prop.2 (hx ▸ congrArg Sum.inl h)⟩
    | Sum.inr b => Sum.inr b
  invFun y :=
    match y with
    | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a,
        fun h => ha.1 (Sum.inl.inj h),
        fun h => ha.2 (Sum.inl.inj h)⟩
    | Sum.inr b => ⟨Sum.inr b,
        Sum.inr_ne_inl, Sum.inr_ne_inl⟩
  left_inv x := by
    rcases x with ⟨a | b, hx⟩ <;> simp
  right_inv y := by
    rcases y with ⟨a, ha⟩ | b <;> simp

/-- The flag equivalence for gluing inside an ambient union:
surviving flags of the union at the inl-pair are the surviving
flags of the left factor plus the right flags. -/
def ambientFlagEquiv (W : Fragment α) (V : Fragment β) (i j : α) :
    SurvivingFlag W i j ⊕ V.Flag ≃
      SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j) where
  toFun f :=
    match f with
    | Sum.inl ⟨g, hg⟩ => ⟨Sum.inl g,
        fun h => hg.1 (Sum.inl.inj h),
        fun h => hg.2 (Sum.inl.inj h)⟩
    | Sum.inr g => ⟨Sum.inr g,
        fun (h : Sum.inr g = Sum.inl (W.boundaryFlag i)) =>
          absurd h Sum.inr_ne_inl,
        fun (h : Sum.inr g = Sum.inl (W.boundaryFlag j)) =>
          absurd h Sum.inr_ne_inl⟩
  invFun f :=
    match hf : f.val with
    | Sum.inl g => Sum.inl ⟨g,
        fun h => f.prop.1 (show f.val = Sum.inl (W.boundaryFlag i)
          from hf ▸ congrArg Sum.inl h),
        fun h => f.prop.2 (show f.val = Sum.inl (W.boundaryFlag j)
          from hf ▸ congrArg Sum.inl h)⟩
    | Sum.inr g => Sum.inr g
  left_inv f := by
    rcases f with ⟨g, hg⟩ | g <;> simp
  right_inv f := by
    rcases f with ⟨g | g, hf⟩ <;> simp

/-- `glueAttach` at a flag attached to a vertex. -/
private theorem glueAttach_of_vertex {W : Fragment α} {i j : α}
    (f : SurvivingFlag W i j) {v : W.Vertex}
    (ha : W.attach f.val = Sum.inl v) :
    glueAttach W i j f = Sum.inl v :=
  (glueAttach_inl_iff f v).mpr ha

/-- `glueAttach` at a flag attached to a label. -/
private theorem glueAttach_of_label {W : Fragment α} {i j : α}
    (f : SurvivingFlag W i j) {ℓ : α}
    (ha : W.attach f.val = Sum.inr ℓ)
    (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) :
    glueAttach W i j f = Sum.inr ⟨ℓ, hℓi, hℓj⟩ :=
  (glueAttach_inr_iff f ⟨ℓ, hℓi, hℓj⟩).mpr ha

private theorem gluePairClosed_disjUnion_attach_comm (W : Fragment α) (V :
  Fragment β)
    {i j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (f : (((W.gluePairClosed i j hclosed).disjUnion V)).Flag) :
    ((((W.disjUnion V).gluePairClosed (Sum.inl i) (Sum.inl j)
          (congrArg Sum.inl hclosed)).relabel
        (ambientLabelEquiv i j))).attach (ambientFlagEquiv W V i j f) =
      ((((W.gluePairClosed i j hclosed).disjUnion V)).attach f).map (_root_.Equiv.refl
          (W.Vertex ⊕ V.Vertex)) id := by
  rcases f with ⟨g, hg⟩ | g
  · -- W-side survivor: flagEquiv maps Sum.inl ⟨g, hg⟩ to ⟨Sum.inl g, ...⟩
    -- The union's attach at Sum.inl g = (W.attach g).map Sum.inl Sum.inl
    have hunion : (W.disjUnion V).attach (Sum.inl g) =
        (W.attach g).map Sum.inl Sum.inl := rfl
    set f' : SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j) :=
      ⟨Sum.inl g, fun h => hg.1 (Sum.inl.inj h),
        fun h => hg.2 (Sum.inl.inj h)⟩
    -- Change the goal to an explicit form
    change (glueAttach (W.disjUnion V) (Sum.inl i) (Sum.inl j) f').map id
          (ambientLabelEquiv i j) =
        Sum.map (⇑(_root_.Equiv.refl (W.Vertex ⊕ V.Vertex))) id
          ((glueAttach W i j ⟨g, hg⟩).map Sum.inl Sum.inl)
    rcases ha : W.attach g with v | ℓ
    · -- vertex case
      have hf' : (W.disjUnion V).attach f'.val = Sum.inl (Sum.inl v) := by
        change (W.attach g).map Sum.inl Sum.inl = _; rw [ha]; rfl
      rw [glueAttach_of_vertex f' hf',
          glueAttach_of_vertex ⟨g, hg⟩ ha]
      rfl
    · -- label case
      have hℓi : ℓ ≠ i := fun h => hg.1 (W.eq_boundaryFlag i g (h ▸ ha))
      have hℓj : ℓ ≠ j := fun h => hg.2 (W.eq_boundaryFlag j g (h ▸ ha))
      have hf' : (W.disjUnion V).attach f'.val = Sum.inr (Sum.inl ℓ) := by
        change (W.attach g).map Sum.inl Sum.inl = _; rw [ha]; rfl
      have hℓi' : (Sum.inl ℓ : α ⊕ β) ≠ Sum.inl i :=
        fun h => hℓi (Sum.inl.inj h)
      have hℓj' : (Sum.inl ℓ : α ⊕ β) ≠ Sum.inl j :=
        fun h => hℓj (Sum.inl.inj h)
      rw [glueAttach_of_label f' hf' hℓi' hℓj',
          glueAttach_of_label ⟨g, hg⟩ ha hℓi hℓj]
      rfl
  · -- V-side flag
    set f' : SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j) :=
      ⟨Sum.inr g, fun (h : Sum.inr g = Sum.inl (W.boundaryFlag i)) =>
        absurd h Sum.inr_ne_inl,
        fun (h : Sum.inr g = Sum.inl (W.boundaryFlag j)) =>
        absurd h Sum.inr_ne_inl⟩
    change (glueAttach (W.disjUnion V) (Sum.inl i) (Sum.inl j) f').map id
          (ambientLabelEquiv i j) =
        Sum.map (⇑(_root_.Equiv.refl (W.Vertex ⊕ V.Vertex))) id
          ((V.attach g).map Sum.inr Sum.inr)
    rcases ha : V.attach g with v | ℓ
    · have hf' : (W.disjUnion V).attach f'.val = Sum.inl (Sum.inr v) := by
        change (V.attach g).map Sum.inr Sum.inr = _; rw [ha]; rfl
      rw [glueAttach_of_vertex f' hf']
      rfl
    · have hf' : (W.disjUnion V).attach f'.val = Sum.inr (Sum.inr ℓ) := by
        change (V.attach g).map Sum.inr Sum.inr = _; rw [ha]; rfl
      have hℓi : (Sum.inr ℓ : α ⊕ β) ≠ Sum.inl i := Sum.inr_ne_inl
      have hℓj : (Sum.inr ℓ : α ⊕ β) ≠ Sum.inl j := Sum.inr_ne_inl
      rw [glueAttach_of_label f' hf' hℓi hℓj]
      rfl

private theorem gluePairClosed_disjUnion_pairing_comm (W : Fragment α) (V :
  Fragment β)
    {i j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (f : (((W.gluePairClosed i j hclosed).disjUnion V)).Flag) :
    ambientFlagEquiv W V i j ((((W.gluePairClosed i j hclosed).disjUnion V)).pairing f) =
      ((((W.disjUnion V).gluePairClosed (Sum.inl i) (Sum.inl j)
          (congrArg Sum.inl hclosed)).relabel
        (ambientLabelEquiv i j))).pairing (ambientFlagEquiv W V i j f) := by
  rcases f with ⟨g, hg⟩ | g
  · apply Subtype.ext
    change Sum.inl (W.pairing g) = (W.disjUnion V).pairing (Sum.inl g)
    rfl
  · apply Subtype.ext
    change Sum.inr (V.pairing g) = (W.disjUnion V).pairing (Sum.inr g)
    rfl

/-- The closed case of glue-in-ambient: when the two boundary flags
bound a common edge in W, the LHS and RHS produce equivalent
fragments. -/
noncomputable def gluePairClosedDisjUnion (W : Fragment α) (V :
  Fragment β)
    {i j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    ((W.gluePairClosed i j hclosed).disjUnion V).Equiv
      (((W.disjUnion V).gluePairClosed (Sum.inl i) (Sum.inl j)
          (congrArg Sum.inl hclosed)).relabel
        (ambientLabelEquiv i j)) where
  flagEquiv := ambientFlagEquiv W V i j
  vertexEquiv := _root_.Equiv.refl (W.Vertex ⊕ V.Vertex)
  attach_comm := by exact gluePairClosed_disjUnion_attach_comm W V hclosed
  pairing_comm := by exact gluePairClosed_disjUnion_pairing_comm W V hclosed
  circles_eq := by
    change (W.circles + 1) + V.circles = (W.circles + V.circles) + 1
    omega

private theorem gluePairOpen_disjUnion_attach_comm (W : Fragment α) (V : Fragment
  β)
    {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : (((W.gluePairOpen i j hij hopen).disjUnion V)).Flag) :
    ((((W.disjUnion V).gluePairOpen (Sum.inl i) (Sum.inl j)
          (fun h => hij (Sum.inl.inj h))
          (fun h => hopen (Sum.inl.inj h))).relabel
        (ambientLabelEquiv i j))).attach (ambientFlagEquiv W V i j f) =
      ((((W.gluePairOpen i j hij hopen).disjUnion V)).attach f).map (_root_.Equiv.refl
          (W.Vertex ⊕ V.Vertex)) id := by
  -- The attach proof is identical to the closed case: glueAttach is
  -- the same function in both gluePairClosed and gluePairOpen.
  rcases f with ⟨g, hg⟩ | g
  · set f' : SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j) :=
      ⟨Sum.inl g, fun h => hg.1 (Sum.inl.inj h),
        fun h => hg.2 (Sum.inl.inj h)⟩
    change (glueAttach (W.disjUnion V) (Sum.inl i) (Sum.inl j) f').map id
          (ambientLabelEquiv i j) =
        Sum.map (⇑(_root_.Equiv.refl (W.Vertex ⊕ V.Vertex))) id
          ((glueAttach W i j ⟨g, hg⟩).map Sum.inl Sum.inl)
    rcases ha : W.attach g with v | ℓ
    · have hf' : (W.disjUnion V).attach f'.val = Sum.inl (Sum.inl v) := by
        change (W.attach g).map Sum.inl Sum.inl = _; rw [ha]; rfl
      rw [glueAttach_of_vertex f' hf',
          glueAttach_of_vertex ⟨g, hg⟩ ha]
      rfl
    · have hℓi : ℓ ≠ i := fun h => hg.1 (W.eq_boundaryFlag i g (h ▸ ha))
      have hℓj : ℓ ≠ j := fun h => hg.2 (W.eq_boundaryFlag j g (h ▸ ha))
      have hf' : (W.disjUnion V).attach f'.val = Sum.inr (Sum.inl ℓ) := by
        change (W.attach g).map Sum.inl Sum.inl = _; rw [ha]; rfl
      rw [glueAttach_of_label f' hf'
            (fun h => hℓi (Sum.inl.inj h)) (fun h => hℓj (Sum.inl.inj h)),
          glueAttach_of_label ⟨g, hg⟩ ha hℓi hℓj]
      rfl
  · set f' : SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j) :=
      ⟨Sum.inr g, fun (h : Sum.inr g = Sum.inl (W.boundaryFlag i)) =>
        absurd h Sum.inr_ne_inl,
        fun (h : Sum.inr g = Sum.inl (W.boundaryFlag j)) =>
        absurd h Sum.inr_ne_inl⟩
    change (glueAttach (W.disjUnion V) (Sum.inl i) (Sum.inl j) f').map id
          (ambientLabelEquiv i j) =
        Sum.map (⇑(_root_.Equiv.refl (W.Vertex ⊕ V.Vertex))) id
          ((V.attach g).map Sum.inr Sum.inr)
    rcases ha : V.attach g with v | ℓ
    · have hf' : (W.disjUnion V).attach f'.val = Sum.inl (Sum.inr v) := by
        change (V.attach g).map Sum.inr Sum.inr = _; rw [ha]; rfl
      rw [glueAttach_of_vertex f' hf']
      rfl
    · have hf' : (W.disjUnion V).attach f'.val = Sum.inr (Sum.inr ℓ) := by
        change (V.attach g).map Sum.inr Sum.inr = _; rw [ha]; rfl
      rw [glueAttach_of_label f' hf' Sum.inr_ne_inl Sum.inr_ne_inl]
      rfl

private theorem gluePairOpen_disjUnion_pairing_comm (W : Fragment α) (V : Fragment
  β)
    {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : (((W.gluePairOpen i j hij hopen).disjUnion V)).Flag) :
    ambientFlagEquiv W V i j ((((W.gluePairOpen i j hij hopen).disjUnion V)).pairing f) =
      ((((W.disjUnion V).gluePairOpen (Sum.inl i) (Sum.inl j)
          (fun h => hij (Sum.inl.inj h))
          (fun h => hopen (Sum.inl.inj h))).relabel
        (ambientLabelEquiv i j))).pairing (ambientFlagEquiv W V i j f) := by
  -- ═══════ REWIRE COMMUTATION ═══════
  rcases f with ⟨g, hg⟩ | g
  · -- W-side survivor: three dite branches of rewire align
    apply Subtype.ext
    -- After Subtype.ext, goal is about .val in W.Flag ⊕ V.Flag
    -- LHS: Sum.inl (rewire hopen ⟨g, hg⟩).val
    -- RHS: (rewire hopen_union ⟨Sum.inl g, ...⟩).val
    change Sum.inl (rewire hopen ⟨g, hg⟩).val =
      (rewire (show (W.disjUnion V).pairing
            ((W.disjUnion V).boundaryFlag (Sum.inl i)) ≠
          (W.disjUnion V).boundaryFlag (Sum.inl j) from
          fun h => hopen (Sum.inl.inj h))
        (⟨Sum.inl g, fun h => hg.1 (Sum.inl.inj h),
          fun h => hg.2 (Sum.inl.inj h)⟩ :
          SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j))).val
    unfold rewire
    split
    · rename_i hfi
      rw [dite_eq_left (show (W.disjUnion V).pairing (Sum.inl g) =
          (W.disjUnion V).boundaryFlag (Sum.inl i) from
          congrArg Sum.inl hfi)]
      rfl
    · split
      · rename_i hfi hfj
        rw [dite_eq_right (show (W.disjUnion V).pairing (Sum.inl g) ≠
            (W.disjUnion V).boundaryFlag (Sum.inl i) from
            fun h => hfi (Sum.inl.inj h)),
          dite_eq_left (show (W.disjUnion V).pairing (Sum.inl g) =
            (W.disjUnion V).boundaryFlag (Sum.inl j) from
            congrArg Sum.inl hfj)]
        rfl
      · rename_i hfi hfj
        rw [dite_eq_right (show (W.disjUnion V).pairing (Sum.inl g) ≠
            (W.disjUnion V).boundaryFlag (Sum.inl i) from
            fun h => hfi (Sum.inl.inj h)),
          dite_eq_right (show (W.disjUnion V).pairing (Sum.inl g) ≠
            (W.disjUnion V).boundaryFlag (Sum.inl j) from
            fun h => hfj (Sum.inl.inj h))]
        rfl
  · -- V-side flag: both dite conditions false since Sum.inr ≠ Sum.inl
    apply Subtype.ext
    change Sum.inr (V.pairing g) =
      (rewire (show (W.disjUnion V).pairing
            ((W.disjUnion V).boundaryFlag (Sum.inl i)) ≠
          (W.disjUnion V).boundaryFlag (Sum.inl j) from
          fun h => hopen (Sum.inl.inj h))
        (⟨Sum.inr g, fun (h : Sum.inr g =
            (W.disjUnion V).boundaryFlag (Sum.inl i)) =>
          absurd h Sum.inr_ne_inl,
          fun (h : Sum.inr g =
            (W.disjUnion V).boundaryFlag (Sum.inl j)) =>
          absurd h Sum.inr_ne_inl⟩ :
          SurvivingFlag (W.disjUnion V) (Sum.inl i) (Sum.inl j))).val
    unfold rewire
    rw [dite_eq_right (show (W.disjUnion V).pairing (Sum.inr g) ≠
          (W.disjUnion V).boundaryFlag (Sum.inl i) from
          Sum.inr_ne_inl),
        dite_eq_right (show (W.disjUnion V).pairing (Sum.inr g) ≠
          (W.disjUnion V).boundaryFlag (Sum.inl j) from
          Sum.inr_ne_inl)]
    rfl

/-- The open case of glue-in-ambient: when the two boundary flags
bound distinct edges in W, the LHS and RHS produce equivalent
fragments. -/
noncomputable def gluePairOpenDisjUnion (W : Fragment α) (V : Fragment
  β)
    {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    ((W.gluePairOpen i j hij hopen).disjUnion V).Equiv
      (((W.disjUnion V).gluePairOpen (Sum.inl i) (Sum.inl j)
          (fun h => hij (Sum.inl.inj h))
          (fun h => hopen (Sum.inl.inj h))).relabel
        (ambientLabelEquiv i j)) where
  flagEquiv := ambientFlagEquiv W V i j
  vertexEquiv := _root_.Equiv.refl (W.Vertex ⊕ V.Vertex)
  attach_comm := by exact gluePairOpen_disjUnion_attach_comm W V hij hopen
  pairing_comm := by exact gluePairOpen_disjUnion_pairing_comm W V hij hopen
  circles_eq := by
    change W.circles + V.circles = (W.circles + V.circles)
    rfl

/-- A single-pair glue commutes with extending the ambient
fragment by a disjoint union: gluing `{i, j}` in `W` and then
forming the union with `V` is equivalent to forming the union first
and gluing the inl-wrapped pair. -/
noncomputable def gluePairDisjUnion (W : Fragment α) (V : Fragment β)
    {i j : α} (hij : i ≠ j) :
    ((W.gluePair i j hij).disjUnion V).Equiv
      (((W.disjUnion V).gluePair (Sum.inl i) (Sum.inl j)
          (fun h => hij (Sum.inl.inj h))).relabel
        (ambientLabelEquiv i j)) := by
  unfold gluePair
  split
  · -- closed case: W's pair is closed, so union's pair is closed
    rename_i hclosed
    have hunion : (W.disjUnion V).pairing
        ((W.disjUnion V).boundaryFlag (Sum.inl i)) =
        (W.disjUnion V).boundaryFlag (Sum.inl j) :=
      congrArg Sum.inl hclosed
    rw [dite_eq_left hunion]
    exact gluePairClosedDisjUnion W V hclosed
  · -- open case: W's pair is open, so union's pair is open
    rename_i hopen
    have hunion : (W.disjUnion V).pairing
        ((W.disjUnion V).boundaryFlag (Sum.inl i)) ≠
        (W.disjUnion V).boundaryFlag (Sum.inl j) :=
      fun h => hopen (Sum.inl.inj h)
    rw [dite_eq_right hunion]
    exact gluePairOpenDisjUnion W V hij hopen

/-- The label condition transported along a relabelling. -/
private theorem relabelSurvIff (e : α ≃ β) (i j : β) (x : α) :
    (x ≠ e.symm i ∧ x ≠ e.symm j) ↔ (e x ≠ i ∧ e x ≠ j) := by
  constructor
  · intro hx
    exact ⟨fun h => hx.1 (by rw [← h, e.symm_apply_apply]),
      fun h => hx.2 (by rw [← h, e.symm_apply_apply])⟩
  · intro hx
    exact ⟨fun h => hx.1 (by rw [h, e.apply_symm_apply]),
      fun h => hx.2 (by rw [h, e.apply_symm_apply])⟩

private theorem relabelGlueAttach_aux (W : Fragment α) (e : α ≃ β)
    {i j : β} (f : SurvivingFlag (W.relabel e) i j) :
    (glueAttach W (e.symm i) (e.symm j) f).map id
        (e.subtypeEquiv (relabelSurvIff e i j)) =
      Sum.map id id (glueAttach (W.relabel e) i j f) := by
  rcases ha : W.attach f.val with v | ℓ
  · rw [glueAttach_of_vertex (W := W) (i := e.symm i) (j := e.symm j) f ha,
      glueAttach_of_vertex f
        (show (W.relabel e).attach f.val = Sum.inl v from by
          change (W.attach f.val).map id e = _
          rw [ha]; rfl)]
    rfl
  · have h1 : ℓ ≠ e.symm i :=
      fun h => (survivingFlag_attach_ne
        (W := W) (i := e.symm i) (j := e.symm j) f).1 (by rw [ha, h])
    have h2 : ℓ ≠ e.symm j :=
      fun h => (survivingFlag_attach_ne
        (W := W) (i := e.symm i) (j := e.symm j) f).2 (by rw [ha, h])
    have h1' : e ℓ ≠ i := fun h => h1 (by rw [← h, e.symm_apply_apply])
    have h2' : e ℓ ≠ j := fun h => h2 (by rw [← h, e.symm_apply_apply])
    rw [glueAttach_of_label (W := W) (i := e.symm i) (j := e.symm j)
        f ha h1 h2,
      glueAttach_of_label f
        (show (W.relabel e).attach f.val = Sum.inr (e ℓ) from by
          change (W.attach f.val).map id e = _
          rw [ha]; rfl) h1' h2']
    rfl

/-- Gluing commutes with relabelling: gluing two labels of a
relabelled fragment is the relabelled gluing of their preimages. -/
noncomputable def gluePairRelabel (W : Fragment α) (e : α ≃ β)
    {i j : β} (hij : i ≠ j) :
    ((W.relabel e).gluePair i j hij).Equiv
      ((W.gluePair (e.symm i) (e.symm j)
          (fun h => hij (by rw [← e.apply_symm_apply i,
            ← e.apply_symm_apply j, h]))).relabel
        (e.subtypeEquiv (by exact relabelSurvIff e i j)))
    := by
  by_cases hclosed :
      W.pairing (W.boundaryFlag (e.symm i)) = W.boundaryFlag (e.symm j)
  · have hc' : (W.relabel e).pairing ((W.relabel e).boundaryFlag i) =
        (W.relabel e).boundaryFlag j := hclosed
    rw [gluePair_eq_closed hij hc', gluePair_eq_closed _ hclosed]
    exact
      { flagEquiv := by
          exact _root_.Equiv.refl (((W.relabel e).gluePairClosed i j hc').Flag)
        vertexEquiv := by
          exact _root_.Equiv.refl (((W.relabel e).gluePairClosed i j
            hc').Vertex)
        attach_comm := fun f => by exact relabelGlueAttach_aux W e f
        pairing_comm := fun f => rfl
        circles_eq := rfl }
  · have ho' : ¬ ((W.relabel e).pairing ((W.relabel e).boundaryFlag i) =
        (W.relabel e).boundaryFlag j) := hclosed
    rw [gluePair_eq_open hij ho', gluePair_eq_open _ hclosed]
    exact
      { flagEquiv := by
          exact _root_.Equiv.refl (((W.relabel e).gluePairOpen i j hij
            ho').Flag)
        vertexEquiv := by
          exact _root_.Equiv.refl (((W.relabel e).gluePairOpen i j hij
            ho').Vertex)
        attach_comm := fun f => by exact relabelGlueAttach_aux W e f
        pairing_comm := fun f => rfl
        circles_eq := rfl }

/-! ### Component swap of a single glue -/

/-- Swapping the two removed labels. -/
def survLabelSwapEquiv (α : Type) (i j : α) :
    SurvivingLabel α j i ≃ SurvivingLabel α i j where
  toFun x := ⟨x.val, x.prop.2, x.prop.1⟩
  invFun x := ⟨x.val, x.prop.2, x.prop.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Gluing a pair is symmetric in its two labels, up to the swap
relabelling. -/
noncomputable def gluePairSwap (W : Fragment α) {i j : α}
    (hij : i ≠ j) :
    (W.gluePair i j hij).Equiv
      ((W.gluePair j i (Ne.symm hij)).relabel
        (survLabelSwapEquiv α i j)) := by
  have hbne : W.boundaryFlag i ≠ W.boundaryFlag j :=
    fun h => hij (W.boundaryFlag_injective h)
  set flagE : SurvivingFlag W j i ≃ SurvivingFlag W i j :=
    ⟨fun f => ⟨f.val, f.prop.2, f.prop.1⟩,
     fun f => ⟨f.val, f.prop.2, f.prop.1⟩,
     fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
  by_cases hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j
  · have hclosed' : W.pairing (W.boundaryFlag j) = W.boundaryFlag i := by
      rw [← hclosed, W.pairing_invol]
    rw [gluePair_eq_closed hij hclosed,
      gluePair_eq_closed (Ne.symm hij) hclosed']
    refine ⟨flagE.symm, _root_.Equiv.refl _, fun f => ?_, fun f => ?_,
      rfl⟩
    · change (glueAttach W j i (flagE.symm f)).map id
          (survLabelSwapEquiv α i j) =
        (glueAttach W i j f).map (_root_.Equiv.refl _) id
      rcases ha : W.attach f.val with v | ℓ
      · have h1 : glueAttach W j i (flagE.symm f) = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        have h2 : glueAttach W i j f = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        rw [h1, h2]
        rfl
      · have h1 : ∃ p : SurvivingLabel α j i,
            glueAttach W j i (flagE.symm f) = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        have h2 : ∃ p : SurvivingLabel α i j,
            glueAttach W i j f = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        obtain ⟨p1, hp1, hv1⟩ := h1
        obtain ⟨p2, hp2, hv2⟩ := h2
        rw [hp1, hp2]
        exact congrArg Sum.inr (Subtype.ext (hv1.trans hv2.symm))
    · exact Subtype.ext rfl
  · have hopen' : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag i := by
      intro h
      exact hclosed (by rw [← h, W.pairing_invol])
    rw [gluePair_eq_open hij hclosed,
      gluePair_eq_open (Ne.symm hij) hopen']
    refine ⟨flagE.symm, _root_.Equiv.refl _, fun f => ?_, fun f => ?_,
      rfl⟩
    · change (glueAttach W j i (flagE.symm f)).map id
          (survLabelSwapEquiv α i j) =
        (glueAttach W i j f).map (_root_.Equiv.refl _) id
      rcases ha : W.attach f.val with v | ℓ
      · have h1 : glueAttach W j i (flagE.symm f) = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        have h2 : glueAttach W i j f = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        rw [h1, h2]
        rfl
      · have h1 : ∃ p : SurvivingLabel α j i,
            glueAttach W j i (flagE.symm f) = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        have h2 : ∃ p : SurvivingLabel α i j,
            glueAttach W i j f = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        obtain ⟨p1, hp1, hv1⟩ := h1
        obtain ⟨p2, hp2, hv2⟩ := h2
        rw [hp1, hp2]
        exact congrArg Sum.inr (Subtype.ext (hv1.trans hv2.symm))
    · change flagE.symm (rewire hclosed f) = rewire hopen' (flagE.symm f)
      unfold rewire
      by_cases hfi : W.pairing f.val = W.boundaryFlag i
      · have hfj : ¬ W.pairing f.val = W.boundaryFlag j :=
          fun h => hbne (hfi.symm.trans h)
        rw [dite_eq_left hfi,
          dite_eq_right (show ¬ W.pairing ((flagE.symm f).val) =
            W.boundaryFlag j from hfj),
          dite_eq_left (show W.pairing ((flagE.symm f).val) =
            W.boundaryFlag i from hfi)]
        exact Subtype.ext rfl
      · by_cases hfj : W.pairing f.val = W.boundaryFlag j
        · rw [dite_eq_right hfi, dite_eq_left hfj,
            dite_eq_left (show W.pairing ((flagE.symm f).val) =
              W.boundaryFlag j from hfj)]
          exact Subtype.ext rfl
        · rw [dite_eq_right hfi, dite_eq_right hfj,
            dite_eq_right (show ¬ W.pairing ((flagE.symm f).val) =
              W.boundaryFlag j from hfj),
            dite_eq_right (show ¬ W.pairing ((flagE.symm f).val) =
              W.boundaryFlag i from hfi)]
          exact Subtype.ext rfl

/-- Disjoint union is commutative, up to the sum-swap
relabelling. -/
noncomputable def disjUnionComm (W₁ : Fragment α) (W₂ : Fragment β) :
    (W₁.disjUnion W₂).Equiv
      ((W₂.disjUnion W₁).relabel (Equiv.sumComm β α)) where
  flagEquiv := Equiv.sumComm W₁.Flag W₂.Flag
  vertexEquiv := Equiv.sumComm W₁.Vertex W₂.Vertex
  attach_comm := fun f => by
    rcases f with f | f
    · change ((W₁.attach f).map Sum.inr Sum.inr).map id
          (Equiv.sumComm β α) =
        ((W₁.attach f).map Sum.inl Sum.inl).map
          (Equiv.sumComm W₁.Vertex W₂.Vertex) id
      rcases W₁.attach f with v | ℓ <;> rfl
    · change ((W₂.attach f).map Sum.inl Sum.inl).map id
          (Equiv.sumComm β α) =
        ((W₂.attach f).map Sum.inr Sum.inr).map
          (Equiv.sumComm W₁.Vertex W₂.Vertex) id
      rcases W₂.attach f with v | ℓ <;> rfl
  pairing_comm := fun f => by
    rcases f with f | f <;> rfl
  circles_eq := by
    change W₁.circles + W₂.circles = W₂.circles + W₁.circles
    omega

end Fragment

end RS
