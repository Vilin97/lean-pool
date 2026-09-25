/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.DirMatching
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonicalFrame
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordCount
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SuperSpace
public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelChords

/-!
# The directed matching a transition system induces on the used labels

An Eulerian subset with a compatible local pairing decomposes into
circuits and directed trails between labelled ends.  The trails
give a directed perfect matching on the labels the subset uses:
partners are the two ends of a trail, and the direction is the one
the trail runs in.

Two kinds of trail occur.  Most have at least one internal step,
and there the orientation's chain direction reads the trail's sense
off the entry edge; the two ends carry opposite values by
chain-direction rigidity.  A trail of a single edge — both of whose
ends are labelled — has no internal step, and the orientation's
laws say nothing about it, so its sense is taken from the label
order.  That is the same orientation the mixed partition function's
own through-edge product uses.
-/

@[expose] public section

namespace RS

open EdgeSubset

variable {α : Type}

/-- A used label whose trail is a single edge: its entry edge is
another used label's flag. -/
def IsThroughLabel {W : Fragment α}
    (F : EdgeSubset W) (i : α) : Prop :=
  W.pairing (W.boundaryFlag i) ∈ F.boundaryFlags

/-- Off the single-edge trails the entry edge is internal. -/
theorem pairing_internal_of_not_through {W : Fragment α}
    (F : EdgeSubset W) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hnt : ¬ IsThroughLabel F i) :
    W.pairing (W.boundaryFlag i) ∈ F.internalFlags :=
  (mem_internalFlags_or_boundaryFlags F
    (F.pairing_mem _ (mem_flags_of_boundaryFlags F hb))).resolve_right hnt

/-- The single-edge trails come in pairs. -/
theorem isThroughLabel_chordInv [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (ht : IsThroughLabel F i) :
    IsThroughLabel F (chordInv F κ i) := by
  unfold IsThroughLabel at ht ⊢
  rw [boundaryFlag_chordInv F κ hb,
    pathMatch_eq_pairing_of_boundary κ hb ht, W.pairing_invol]
  exact hb

/-- Comparing two distinct labels the other way negates. -/
theorem decide_lt_flip [LinearOrder α]
    {i j : α} (h : i ≠ j) :
    decide (j < i) = !decide (i < j) := by
  rcases lt_trichotomy i j with h1 | h1 | h1
  · rw [decide_eq_false (asymm h1), decide_eq_true h1]
    rfl
  · exact absurd h1 h
  · rw [decide_eq_true h1, decide_eq_false (asymm h1)]
    rfl

open scoped Classical in
/-- **The directed matching a transition system induces on the used
labels** — RS21's `M(ω,κ)`.  Partners are the two ends of a trail;
the direction is the trail's own, read from the orientation where
the trail has an internal step and from the label order where it is
a single edge. -/
noncomputable def cutMatching [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation) :
    DirMatching {i : α // W.boundaryFlag i ∈ F.boundaryFlags} where
  edge i := ⟨chordInv F κ i.val, chordInv_mem F κ i.prop⟩
  edge_invol i := Subtype.ext (chordInv_invol F κ i.val)
  edge_ne i := fun h =>
    chordInv_ne F κ i.prop (congrArg Subtype.val h)
  tail i :=
    if IsThroughLabel F i.val then
      decide (i.val < chordInv F κ i.val)
    else !chainDir o (W.boundaryFlag i.val)
  tail_flip i := by
    by_cases ht : IsThroughLabel F i.val
    · have ht' : IsThroughLabel F (chordInv F κ i.val) :=
        isThroughLabel_chordInv F κ i.prop ht
      change (if IsThroughLabel F (chordInv F κ i.val) then
          decide (chordInv F κ i.val
            < chordInv F κ (chordInv F κ i.val))
        else _) = !(if IsThroughLabel F i.val then _ else _)
      rw [ite_eq_left ht', ite_eq_left ht, chordInv_invol]
      exact decide_lt_flip (fun hx =>
        chordInv_ne F κ i.prop hx.symm)
    · have hint := pairing_internal_of_not_through F i.prop ht
      have hfar : W.pairing (W.boundaryFlag (chordInv F κ i.val))
          ∈ F.internalFlags := by
        rw [boundaryFlag_chordInv F κ i.prop]
        exact pathMatch_pairing_internal i.prop hint
      have ht' : ¬ IsThroughLabel F (chordInv F κ i.val) := fun hx =>
        Finset.disjoint_left.mp F.internalFlags_disjoint_boundaryFlags
          hfar hx
      change (if IsThroughLabel F (chordInv F κ i.val) then _
        else !chainDir o (W.boundaryFlag (chordInv F κ i.val)))
        = !(if IsThroughLabel F i.val then _
          else !chainDir o (W.boundaryFlag i.val))
      rw [ite_eq_right ht', ite_eq_right ht, boundaryFlag_chordInv F κ i.prop,
        chainDir_pathMatch o i.prop hint]

/-! ### Undoing the dual basis

RS21's boundary vector at a used leg is `f_{χ₁(i)}` where the arc
enters and `g_{χ₁(i)}` where it leaves.  Written in the basis of
the `f`'s, the leaving legs carry the partner colour and the
partner sign.  So a basis coordinate `x` of the tensor determines
`χ₁` by undoing the partner at the legs the trail leaves, and
contributes the product of those legs' signs.

The two operations below are that change of basis and its weight.
-/

section ChordRelabel

/-- **The chord involution shifts through the relabel.** -/
theorem chordInv_relabelUp [LinearOrder α] {W : Fragment α}
    {β : Type} [LinearOrder β] (e : α ≃o β)
    (F : EdgeSubset W) (κ : F.RelTransitionSystem) (b : β) :
    chordInv (F.relabelUp e.toEquiv) (relabelTransUp e.toEquiv F κ) b
      = e (chordInv F κ (e.symm b)) := by
  have hbf : (W.relabel e.toEquiv).boundaryFlag b
      = W.boundaryFlag (e.symm b) := rfl
  unfold chordInv
  by_cases hb : W.boundaryFlag (e.symm b) ∈ F.boundaryFlags
  · have hb' : (W.relabel e.toEquiv).boundaryFlag b
        ∈ (F.relabelUp e.toEquiv).boundaryFlags := by
      rw [hbf, relabelUp_boundaryFlags e F]
      exact hb
    rw [dite_eq_left hb', dite_eq_left hb]
    have hpm := relabel_pathMatch e F κ hb' hb
    have hmem' : κ.pathMatch (W.boundaryFlag (e.symm b)) hb
        ∈ (F.relabelUp e.toEquiv).boundaryFlags := by
      rw [relabelUp_boundaryFlags e F]
      exact κ.pathMatch_mem hb
    calc (F.relabelUp e.toEquiv).boundaryLabel
          ((relabelTransUp e.toEquiv F κ).pathMatch_mem hb')
        = (F.relabelUp e.toEquiv).boundaryLabel hmem' := by
          congr 1
      _ = e (F.boundaryLabel (κ.pathMatch_mem hb)) :=
          relabel_boundaryLabel e F hmem' (κ.pathMatch_mem hb)
  · have hb' : ¬ ((W.relabel e.toEquiv).boundaryFlag b
        ∈ (F.relabelUp e.toEquiv).boundaryFlags) := by
      rw [hbf, relabelUp_boundaryFlags e F]
      exact hb
    rw [dite_eq_right hb', dite_eq_right hb]
    exact (e.apply_symm_apply b).symm

/-- **The used labels shift through the relabel.** -/
noncomputable def usedLabRelabelEquiv [LinearOrder α] {W : Fragment α}
    {β : Type} [LinearOrder β]
    (e : α ≃o β) (F : EdgeSubset W) :
    {b : β // (W.relabel e.toEquiv).boundaryFlag b
        ∈ (F.relabelUp e.toEquiv).boundaryFlags}
      ≃ {a : α // W.boundaryFlag a ∈ F.boundaryFlags} where
  toFun b := ⟨e.symm b.val,
    (relabelUp_boundaryFlags e F) ▸ b.prop⟩
  invFun a := ⟨e a.val,
    (relabelUp_boundaryFlags e F).symm ▸
      (show W.boundaryFlag (e.symm (e a.val)) ∈ F.boundaryFlags from
        (e.symm_apply_apply a.val).symm ▸ a.prop)⟩
  left_inv b := Subtype.ext (e.apply_symm_apply b.val)
  right_inv a := Subtype.ext (e.symm_apply_apply a.val)

/-- **The chord matching shifts through the relabel**, on
pairings. -/
theorem cutMatching_relabelUp_edge [LinearOrder α] {W : Fragment α}
    {β : Type} [LinearOrder β]
    (e : α ≃o β) (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (o' : (relabelTransUp e.toEquiv F κ).Orientation)
    (a : {a : α // W.boundaryFlag a ∈ F.boundaryFlags}) :
    ((((cutMatching (F.relabelUp e.toEquiv)
          (relabelTransUp e.toEquiv F κ) o').map
        (usedLabRelabelEquiv e F)).edge a).val)
      = chordInv F κ a.val := by
  change e.symm (chordInv (F.relabelUp e.toEquiv)
      (relabelTransUp e.toEquiv F κ) (e a.val))
    = chordInv F κ a.val
  rw [chordInv_relabelUp e F κ (e a.val), e.symm_apply_apply,
    e.symm_apply_apply]

end ChordRelabel

/-! ### The arcs' directions, as data

RS21's Eulerian orientation directs every edge of the subset,
including one whose two ends are both labelled.  The chain
orientation of a relative transition system directs only the
internal flags, so it fixes the direction of a chain but says
nothing about such an edge.  The missing freedom is recorded here:
the directions of the chord matching's arcs are taken as data — any
directed matching on the used labels whose partner map is the chord
involution — and the chain orientation supplies one choice among
them.

Only the directions enter the change of basis and its weight, so
both are stated against a bare direction function.
-/

/-- The used labels of a subset. -/
abbrev UsedLab {W : Fragment α}
    (F : EdgeSubset W) : Type :=
  {i : α // W.boundaryFlag i ∈ F.boundaryFlags}

open Classical in
/-- Undo the dual basis against a given set of arc directions. -/
noncomputable def untwistD {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (tl : UsedLab F → Bool) (x : GenBoundaryState k ℓ α) :
    GenBoundaryState k ℓ α :=
  fun i =>
    if h : W.boundaryFlag i ∈ F.boundaryFlags then
      if tl ⟨i, h⟩ then
        match x i with
        | Sum.inl a => Sum.inl a
        | Sum.inr c => Sum.inr (oddPartner ℓ c)
      else x i
    else x i

open Classical in
/-- The dual basis's weight against a given set of arc
directions. -/
noncomputable def dualWeightD {W : Fragment α}
    [Fintype α] {k ℓ : ℕ}
    (F : EdgeSubset W) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α) : ℂ :=
  ∏ i : α,
    if h : W.boundaryFlag i ∈ F.boundaryFlags then
      if tl ⟨i, h⟩ then
        match x i with
        | Sum.inl _ => 1
        | Sum.inr c => dualSign ℓ c
      else 1
    else 1

open Classical in
/-- Undo the dual basis: partner the colour at each leg the trail
leaves. -/
noncomputable def untwist [LinearOrder α] {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α) : GenBoundaryState k ℓ α :=
  fun i =>
    if h : W.boundaryFlag i ∈ F.boundaryFlags then
      if (cutMatching F κ o).tail ⟨i, h⟩ then
        match x i with
        | Sum.inl a => Sum.inl a
        | Sum.inr c => Sum.inr (oddPartner ℓ c)
      else x i
    else x i

open Classical in
/-- **The dual basis's weight**: the partner signs at the legs the
trail leaves. -/
noncomputable def dualWeight [LinearOrder α] {W : Fragment α}
    [Fintype α] {k ℓ : ℕ}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α) : ℂ :=
  ∏ i : α,
    if h : W.boundaryFlag i ∈ F.boundaryFlags then
      if (cutMatching F κ o).tail ⟨i, h⟩ then
        match x i with
        | Sum.inl _ => 1
        | Sum.inr c => dualSign ℓ c
      else 1
    else 1

/-! ### A chain flip touches only its own two labels

The flip set of a ported chain consists of internal flags, and its
only exits are the two ports, whose partners are the chain's two
boundary flags.  So a used label whose entry flag lies in the flip
set is one of those two.
-/

/-- **Only the chain's own two labels have their entry flag in the
flip set.** -/
theorem label_of_pairing_mem_flipSet {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hmem : W.pairing (W.boundaryFlag i) ∈ S) : i = i₁ ∨ i = i₂ := by
  by_cases h1 : W.pairing (W.boundaryFlag i) = p₁
  · refine Or.inl (W.boundaryFlag_injective ?_)
    have hp := h.hσ₁
    rw [← h1, W.pairing_invol] at hp
    exact hp
  · by_cases h2 : W.pairing (W.boundaryFlag i) = p₂
    · refine Or.inr (W.boundaryFlag_injective ?_)
      have hp := h.hσ₂
      rw [← h2, W.pairing_invol] at hp
      exact hp
    · exfalso
      have hx := h.pairing_mem _ hmem h1 h2
      rw [W.pairing_invol] at hx
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags (h.int_of_mem _ hx) hb

/-- The chain's near port is the entry flag of its first label. -/
theorem pairing_boundaryFlag_eq_port {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.pairing (W.boundaryFlag i₁) = p₁ := by
  rw [← h.hσ₁, W.pairing_invol]

/-- And of its second. -/
theorem pairing_boundaryFlag_eq_port' {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.pairing (W.boundaryFlag i₂) = p₂ := by
  rw [← h.hσ₂, W.pairing_invol]

/-- A chain's own labels are not through-labels: their entry flags
are internal. -/
theorem not_isThroughLabel_port {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    ¬ IsThroughLabel F i₁ := by
  intro hx
  unfold IsThroughLabel at hx
  rw [pairing_boundaryFlag_eq_port h] at hx
  exact Finset.disjoint_left.mp F.internalFlags_disjoint_boundaryFlags
    (h.int_of_mem _ h.hp₁S) hx

/-- And the second. -/
theorem not_isThroughLabel_port' {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    ¬ IsThroughLabel F i₂ := by
  intro hx
  unfold IsThroughLabel at hx
  rw [pairing_boundaryFlag_eq_port' h] at hx
  exact Finset.disjoint_left.mp F.internalFlags_disjoint_boundaryFlags
    (h.int_of_mem _ h.hp₂S) hx

/-! ### A chain flip reverses one arc

RS21's `M(ω′,κ′)` differs from `M(ω,κ)` by inverting one arc.  In
the flag model that is exactly what a chain flip does: the tail
function changes at the chain's two labels and nowhere else, and
those two labels are the ends of one arc.
-/

open Classical in
/-- **A chain flip reverses exactly the chain's own arc.** -/
theorem cutMatching_portFlip [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    {S : Finset W.Flag} {p₁ p₂ : W.Flag} {i₁ i₂ : α}
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂) :
    cutMatching F κ (o.portFlip h)
      = (cutMatching F κ o).reverseArc ⟨i₁, hb₁⟩ := by
  refine DirMatching.ext rfl (funext fun j => ?_)
  have hcond : (j = (⟨i₁, hb₁⟩ : {i : α // W.boundaryFlag i ∈
        F.boundaryFlags}) ∨
      j = (cutMatching F κ o).edge ⟨i₁, hb₁⟩)
      ↔ (j.val = i₁ ∨ j.val = i₂) := by
    constructor
    · rintro (rfl | hx)
      · exact Or.inl rfl
      · exact Or.inr (by rw [hx]; exact hchord)
    · rintro (hx | hx)
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext (by rw [hx]; exact hchord.symm))
  change (if IsThroughLabel F j.val then
        decide (j.val < chordInv F κ j.val)
      else !chainDir (o.portFlip h) (W.boundaryFlag j.val))
    = (if j = ⟨i₁, hb₁⟩ ∨ j = (cutMatching F κ o).edge ⟨i₁, hb₁⟩
       then !(cutMatching F κ o).tail j
       else (cutMatching F κ o).tail j)
  by_cases hnt : IsThroughLabel F j.val
  · have hj : ¬ (j.val = i₁ ∨ j.val = i₂) := by
      rintro (hx | hx)
      · exact (not_isThroughLabel_port h) (hx ▸ hnt)
      · exact (not_isThroughLabel_port' h) (hx ▸ hnt)
    rw [ite_eq_left hnt, ite_eq_right (fun hx => hj (hcond.mp hx))]
    change _ = if IsThroughLabel F j.val then
        decide (j.val < chordInv F κ j.val) else _
    rw [ite_eq_left hnt]
  · have htail : (cutMatching F κ o).tail j
        = !chainDir o (W.boundaryFlag j.val) := by
      change (if IsThroughLabel F j.val then
          decide (j.val < chordInv F κ j.val) else _) = _
      rw [ite_eq_right hnt]
    rw [ite_eq_right hnt, htail, chainDir_eq, chainDir_eq]
    by_cases hj : j.val = i₁ ∨ j.val = i₂
    · have hmem : W.pairing (W.boundaryFlag j.val) ∈ S := by
        rcases hj with hx | hx <;> rw [hx]
        · rw [pairing_boundaryFlag_eq_port h]; exact h.hp₁S
        · rw [pairing_boundaryFlag_eq_port' h]; exact h.hp₂S
      rw [ite_eq_left (hcond.mpr hj), portFlip_isOut_of_mem o h hmem]
    · have hnm : W.pairing (W.boundaryFlag j.val) ∉ S := fun hx =>
        hj (label_of_pairing_mem_flipSet h j.prop hx)
      rw [ite_eq_right (fun hx => hj (hcond.mp hx)),
        portFlip_isOut_of_notMem o h hnm]

open Classical in
/-- **A used label whose chain has an interior admits a chain
flip.**  This is the half of RS21's step 1 the chain orientation
provides: the trail through the interior can be inverted, and doing
so reverses exactly that label's arc. -/
theorem exists_chainFlip [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (o : κ.Orientation) {i₁ : α}
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hnt : ¬ IsThroughLabel F i₁) :
    ∃ (S : Finset W.Flag) (p₁ p₂ : W.Flag)
      (hp : PortedFlipSet κ S p₁ p₂ i₁ (chordInv F κ i₁)),
      cutMatching F κ (o.portFlip hp)
        = (cutMatching F κ o).reverseArc ⟨i₁, hb₁⟩ := by
  obtain ⟨k, -, hcont, hpm⟩ := pathMatch_chain_length κ hb₁
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    refine hnt ?_
    have hmem := κ.pathMatch_mem hb₁
    rwa [hpm, iterWalk_zero] at hmem
  have hterm : W.pairing (iterWalk κ (W.boundaryFlag i₁) k)
      ∈ F.boundaryFlags := by
    rw [← hpm]
    exact κ.pathMatch_mem hb₁
  have hiγ : W.attach (W.pairing (iterWalk κ (W.boundaryFlag i₁) k))
      = Sum.inr (chordInv F κ i₁) := by
    rw [← hpm, ← boundaryFlag_chordInv F κ hb₁]
    exact W.attach_boundaryFlag _
  obtain ⟨S, hp, -, -⟩ := exists_chainPortedFlipSet κ hb₁ hcont hterm
    hk (W.attach_boundaryFlag i₁) hiγ
  exact ⟨S, _, _, hp, cutMatching_portFlip o hp hb₁ rfl⟩

/-! ### Evaluating the change of basis

Undoing the dual basis acts pointwise: at a used label it partners
the colour exactly when the trail leaves that label, and elsewhere
it does nothing.
-/

open Classical in
/-- The change of basis at a used label. -/
theorem untwist_apply_of_mem [LinearOrder α] {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags) :
    untwist F κ o x i
      = if (cutMatching F κ o).tail ⟨i, hb⟩ then
          (match x i with
            | Sum.inl a => Sum.inl a
            | Sum.inr c => Sum.inr (oddPartner ℓ c))
        else x i :=
  dite_eq_left hb

open Classical in
/-- The change of basis is trivial off the used labels. -/
theorem untwist_apply_of_not_mem [LinearOrder α] {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α) {i : α}
    (hb : W.boundaryFlag i ∉ F.boundaryFlags) :
    untwist F κ o x i = x i :=
  dite_eq_right hb

/-! ### The chain flip's effect on the dual basis

Reversing a chain exchanges which of its two ends is the tail, so
undoing the dual basis after the flip is undoing it before with the
two ends' colours partnered — which is the state flip the summand's
own chain-flip ledger produces.
-/

/-- The dual basis's per-label weight squares to one. -/
theorem dualFactor_sq {k ℓ : ℕ} (v : Fin k ⊕ Fin (2 * ℓ)) :
    (match v with
      | Sum.inl _ => (1 : ℂ)
      | Sum.inr c => dualSign ℓ c) *
      (match v with
        | Sum.inl _ => (1 : ℂ)
        | Sum.inr c => dualSign ℓ c) = 1 := by
  rcases v with a | c
  · norm_num
  · exact oddPartnerSign_cast_sq ℓ c

section ChainFlip

open Classical in
/-- The direction flips at the chain's two labels. -/
theorem tail_portFlip_of_mem [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation) {S : Finset W.Flag}
    {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hj : i = i₁ ∨ i = i₂) :
    (cutMatching F κ (o.portFlip h)).tail ⟨i, hb⟩
      = !(cutMatching F κ o).tail ⟨i, hb⟩ := by
  rw [show (cutMatching F κ (o.portFlip h)).tail ⟨i, hb⟩
        = ((cutMatching F κ o).reverseArc ⟨i₁, hb₁⟩).tail ⟨i, hb⟩
      from by rw [cutMatching_portFlip o h hb₁ hchord],
    DirMatching.reverseArc_tail, ite_eq_left]
  rcases hj with hx | hx
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr (Subtype.ext (hx.trans hchord.symm))

open Classical in
/-- And nowhere else. -/
theorem tail_portFlip_of_not_mem
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation) {S : Finset W.Flag}
    {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hj : ¬ (i = i₁ ∨ i = i₂)) :
    (cutMatching F κ (o.portFlip h)).tail ⟨i, hb⟩
      = (cutMatching F κ o).tail ⟨i, hb⟩ := by
  rw [show (cutMatching F κ (o.portFlip h)).tail ⟨i, hb⟩
        = ((cutMatching F κ o).reverseArc ⟨i₁, hb₁⟩).tail ⟨i, hb⟩
      from by rw [cutMatching_portFlip o h hb₁ hchord],
    DirMatching.reverseArc_tail, ite_eq_right]
  rintro (hx | hx)
  · exact hj (Or.inl (congrArg Subtype.val hx))
  · refine hj (Or.inr ?_)
    exact (congrArg Subtype.val hx).trans hchord

open Classical in
/-- **A chain flip partners the two chain ends.** -/
theorem untwist_portFlip [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation) {S : Finset W.Flag}
    {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    {k ℓ : ℕ} (x : GenBoundaryState k ℓ α) :
    untwist F κ (o.portFlip h) x
      = stateOddFlip (untwist F κ o x) i₁ i₂ := by
  have hb₂ : W.boundaryFlag i₂ ∈ F.boundaryFlags := by
    rw [← hchord]; exact chordInv_mem F κ hb₁
  have hflip : ∀ (i : α) (hb : W.boundaryFlag i ∈ F.boundaryFlags),
      i = i₁ ∨ i = i₂ →
      untwist F κ (o.portFlip h) x i
        = Sum.map id (oddPartner ℓ) (untwist F κ o x i) := by
    intro i hb hj
    rw [untwist_apply_of_mem F κ (o.portFlip h) x hb,
      untwist_apply_of_mem F κ o x hb,
      tail_portFlip_of_mem o h hb₁ hchord hb hj]
    by_cases ht : (cutMatching F κ o).tail ⟨i, hb⟩ = true
    · rw [ht, Bool.not_true, ite_eq_right (by simp), ite_eq_left rfl]
      rcases hx : x i with a | c
      · rfl
      · change Sum.inr c
          = Sum.map id (oddPartner ℓ) (Sum.inr (oddPartner ℓ c))
        rw [Sum.map_inr, oddPartner_invol]
    · rw [Bool.eq_false_iff.mpr ht, Bool.not_false, ite_eq_left rfl,
        ite_eq_right (by simp)]
      rcases hx : x i with a | c <;> rfl
  funext i
  by_cases h1 : i = i₁
  · subst h1
    rw [stateOddFlip_left]
    exact hflip i hb₁ (Or.inl rfl)
  · by_cases h2 : i = i₂
    · subst h2
      rw [stateOddFlip_right]
      exact hflip i hb₂ (Or.inr rfl)
    · rw [stateOddFlip_of_ne h1 h2]
      by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
      · rw [untwist_apply_of_mem F κ (o.portFlip h) x hb,
          untwist_apply_of_mem F κ o x hb,
          tail_portFlip_of_not_mem o h hb₁ hchord hb
            (fun hx => hx.elim h1 h2)]
      · rw [untwist_apply_of_not_mem F κ (o.portFlip h) x hb,
          untwist_apply_of_not_mem F κ o x hb]

open Classical in
/-- **The chain flip's weight**: the dual basis's weights before and
after a chain flip multiply to the two chain ends' signs, since they
differ exactly at those two labels and every factor squares to
one. -/
theorem dualWeight_portFlip_mul
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation) {S : Finset W.Flag}
    {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    [Fintype α] {k ℓ : ℕ}
    (x : GenBoundaryState k ℓ α) {c₁ c₂ : Fin (2 * ℓ)}
    (hc₁ : x i₁ = Sum.inr c₁) (hc₂ : x i₂ = Sum.inr c₂) :
    dualWeight F κ (o.portFlip h) x * dualWeight F κ o x
      = dualSign ℓ c₁ * dualSign ℓ c₂ := by
  have hb₂ : W.boundaryFlag i₂ ∈ F.boundaryFlags := by
    rw [← hchord]; exact chordInv_mem F κ hb₁
  have hne : i₁ ≠ i₂ := h.hlab
  unfold dualWeight
  rw [← Finset.prod_mul_distrib]
  have hpair : ∀ i ∈ (Finset.univ : Finset α), i ∉ ({i₁, i₂} :
      Finset α) →
      ((if hb : W.boundaryFlag i ∈ F.boundaryFlags then
          (if (cutMatching F κ (o.portFlip h)).tail ⟨i, hb⟩ then
            (match x i with
              | Sum.inl _ => 1
              | Sum.inr c => dualSign ℓ c)
          else 1) else 1) *
        (if hb : W.boundaryFlag i ∈ F.boundaryFlags then
          (if (cutMatching F κ o).tail ⟨i, hb⟩ then
            (match x i with
              | Sum.inl _ => 1
              | Sum.inr c => dualSign ℓ c)
          else 1) else 1)) = 1 := by
    intro i _ hi
    have hj : ¬ (i = i₁ ∨ i = i₂) := by
      rintro (rfl | rfl) <;> exact hi (by simp)
    by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
    · rw [dite_eq_left hb, dite_eq_left hb,
        tail_portFlip_of_not_mem o h hb₁ hchord hb hj]
      by_cases ht : (cutMatching F κ o).tail ⟨i, hb⟩ = true
      · rw [ite_eq_left ht]
        exact dualFactor_sq (x i)
      · rw [ite_eq_right ht]
        norm_num
    · rw [dite_eq_right hb, dite_eq_right hb]
      norm_num
  rw [← Finset.prod_subset (Finset.subset_univ ({i₁, i₂} :
      Finset α)) hpair, Finset.prod_pair hne,
    dite_eq_left hb₁, dite_eq_left hb₂, dite_eq_left hb₁, dite_eq_left hb₂,
    tail_portFlip_of_mem o h hb₁ hchord hb₁ (Or.inl rfl),
    tail_portFlip_of_mem o h hb₁ hchord hb₂ (Or.inr rfl), hc₁, hc₂]
  by_cases t₁ : (cutMatching F κ o).tail ⟨i₁, hb₁⟩ = true <;>
    by_cases t₂ : (cutMatching F κ o).tail ⟨i₂, hb₂⟩ = true <;>
    simp [t₁, t₂, Bool.eq_false_iff.mpr]

end ChainFlip

open Classical in
/-- The change of basis at an odd used label. -/
theorem untwist_apply_odd [LinearOrder α] {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags) {c : Fin (2 * ℓ)}
    (hc : x i = Sum.inr c) :
    untwist F κ o x i
      = Sum.inr (if (cutMatching F κ o).tail ⟨i, hb⟩ then
          oddPartner ℓ c else c) := by
  rw [untwist_apply_of_mem F κ o x hb, hc]
  by_cases ht : (cutMatching F κ o).tail ⟨i, hb⟩ = true
  · rw [ite_eq_left ht, ite_eq_left ht]
  · rw [ite_eq_right ht, ite_eq_right ht]

/-! ### Reversing one arc's direction

RS21's (12) inverts a directed trail.  When the trail is a single
edge joining two labelled ends there is nothing inside to invert, so
the whole effect is on the dual basis: the leg that carried `g`
carries `f` and the other way about.  The two legs' weights are
therefore exchanged, and since the two ends of an arc carry partner
colours, the exchange costs a sign.
-/

section OrderFreeArc

open Classical in
/-- **Reversing an arc exchanges the two legs' weights**, at a cost
of one sign.  The hypothesis is the support condition: the two ends
of an arc carry partner colours. -/
theorem dualWeightD_reverseArc_mul {W : Fragment α}
    [Fintype α] [DecidableEq α]
    {k ℓ : ℕ} (F : EdgeSubset W) (M : DirMatching (UsedLab F))
    (a : UsedLab F) (x : GenBoundaryState k ℓ α)
    {c : Fin (2 * ℓ)} (hta : M.tail a = true)
    (hca : x a.val = Sum.inr c)
    (hca' : x (M.edge a).val = Sum.inr (oddPartner ℓ c)) :
    dualWeightD F (M.reverseArc a).tail x
        * dualWeightD F M.tail x = -1 := by
  have hane : (M.edge a).val ≠ a.val := fun hx =>
    M.edge_ne a (Subtype.ext hx)
  unfold dualWeightD
  rw [← Finset.prod_mul_distrib]
  have hfac : ∀ i : α, i ≠ a.val → i ≠ (M.edge a).val →
      ((if h : W.boundaryFlag i ∈ F.boundaryFlags then
          if (M.reverseArc a).tail ⟨i, h⟩ then
            match x i with
            | Sum.inl _ => 1
            | Sum.inr d => dualSign ℓ d
          else 1
        else 1) *
      (if h : W.boundaryFlag i ∈ F.boundaryFlags then
          if M.tail ⟨i, h⟩ then
            match x i with
            | Sum.inl _ => 1
            | Sum.inr d => dualSign ℓ d
          else 1
        else 1)) = 1 := by
    intro i h1 h2
    by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
    · rw [dite_eq_left hb, dite_eq_left hb,
        show (M.reverseArc a).tail ⟨i, hb⟩ = M.tail ⟨i, hb⟩ from by
          rw [DirMatching.reverseArc_tail]
          exact ite_eq_right (by
            rintro (hx | hx)
            · exact h1 (congrArg Subtype.val hx)
            · exact h2 (congrArg Subtype.val hx))]
      by_cases ht : M.tail ⟨i, hb⟩ = true
      · rw [ite_eq_left ht]
        exact dualFactor_sq (x i)
      · rw [ite_eq_right ht]
        norm_num
    · rw [dite_eq_right hb, dite_eq_right hb]
      norm_num
  have hpair : ∀ f : α → ℂ, (∀ i, i ≠ a.val → i ≠ (M.edge a).val →
      f i = 1) → (∏ i : α, f i) = f a.val * f (M.edge a).val := by
    intro f hf
    rw [← Finset.prod_subset
      (Finset.subset_univ ({a.val, (M.edge a).val} : Finset α))
      (fun i _ hi => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        push Not at hi
        exact hf i hi.1 hi.2),
      Finset.prod_pair (Ne.symm hane)]
  rw [hpair _ hfac]
  have ha : (⟨a.val, a.prop⟩ : UsedLab F) = a := Subtype.ext rfl
  have ha' : (⟨(M.edge a).val, (M.edge a).prop⟩ : UsedLab F)
      = M.edge a := Subtype.ext rfl
  have htb : M.tail (M.edge a) = false := by
    rw [M.tail_flip a, hta]
    rfl
  rw [dite_eq_left a.prop, dite_eq_left a.prop, dite_eq_left (M.edge a).prop,
    dite_eq_left (M.edge a).prop]
  rw [show (M.reverseArc a).tail ⟨a.val, a.prop⟩ = false from by
      rw [ha, DirMatching.reverseArc_tail, ite_eq_left (Or.inl rfl), hta]
      rfl,
    show M.tail ⟨a.val, a.prop⟩ = true from by rw [ha]; exact hta,
    show (M.reverseArc a).tail ⟨(M.edge a).val, (M.edge a).prop⟩
        = true from by
      rw [ha', DirMatching.reverseArc_tail, ite_eq_left (Or.inr rfl), htb]
      rfl,
    show M.tail ⟨(M.edge a).val, (M.edge a).prop⟩ = false from by
      rw [ha']; exact htb]
  rw [ite_eq_right (by simp), ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by simp),
    hca, hca']
  change (1 * dualSign ℓ c) * (dualSign ℓ (oddPartner ℓ c) * 1) = -1
  rw [dualSign_oddPartner]
  have hsq := dualSign_sq ℓ c
  linear_combination -hsq

open Classical in
/-- The change of basis at a used leg. -/
theorem untwistD_apply_mem {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (tl : UsedLab F → Bool) (x : GenBoundaryState k ℓ α) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags) :
    untwistD F tl x i
      = if tl ⟨i, hb⟩ then Sum.map id (oddPartner ℓ) (x i)
        else x i := by
  unfold untwistD
  rw [dite_eq_left hb]
  by_cases ht : tl ⟨i, hb⟩ = true
  · rw [ite_eq_left ht, ite_eq_left ht]
    rcases x i with a | c <;> rfl
  · rw [ite_eq_right ht, ite_eq_right ht]

open Classical in
/-- The change of basis away from the used legs. -/
theorem untwistD_apply_not_mem {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (tl : UsedLab F → Bool) (x : GenBoundaryState k ℓ α) {i : α}
    (hb : W.boundaryFlag i ∉ F.boundaryFlags) :
    untwistD F tl x i = x i := dite_eq_right hb

open Classical in
/-- **Reversing an arc partners the colour at its two legs.** -/
theorem untwistD_reverseArc {W : Fragment α}
    [DecidableEq α] {k ℓ : ℕ}
    (F : EdgeSubset W) (M : DirMatching (UsedLab F)) (a : UsedLab F)
    (x : GenBoundaryState k ℓ α) :
    untwistD F (M.reverseArc a).tail x
      = stateOddFlip (untwistD F M.tail x) a.val (M.edge a).val := by
  have hinv : ∀ v : Fin k ⊕ Fin (2 * ℓ),
      Sum.map id (oddPartner ℓ) (Sum.map id (oddPartner ℓ) v) = v := by
    rintro (b | d)
    · rfl
    · change Sum.inr (oddPartner ℓ (oddPartner ℓ d)) = Sum.inr d
      rw [oddPartner_invol]
  funext i
  by_cases hi₁ : i = a.val
  · rw [hi₁, stateOddFlip_left, untwistD_apply_mem F _ x a.prop,
      untwistD_apply_mem F _ x a.prop,
      show (M.reverseArc a).tail ⟨a.val, a.prop⟩
          = !M.tail ⟨a.val, a.prop⟩ from by
        rw [DirMatching.reverseArc_tail]
        exact ite_eq_left (Or.inl (Subtype.ext rfl))]
    by_cases ht : M.tail ⟨a.val, a.prop⟩ = true
    · rw [ht, Bool.not_true, ite_eq_right (by simp), ite_eq_left rfl, hinv]
    · have htf : M.tail ⟨a.val, a.prop⟩ = false := by
        cases hbb : M.tail ⟨a.val, a.prop⟩
        · rfl
        · exact absurd hbb ht
      rw [htf, Bool.not_false, ite_eq_left rfl, ite_eq_right (by simp)]
  · by_cases hi₂ : i = (M.edge a).val
    · rw [hi₂, stateOddFlip_right,
        untwistD_apply_mem F _ x (M.edge a).prop,
        untwistD_apply_mem F _ x (M.edge a).prop,
        show (M.reverseArc a).tail ⟨(M.edge a).val, (M.edge a).prop⟩
            = !M.tail ⟨(M.edge a).val, (M.edge a).prop⟩ from by
          rw [DirMatching.reverseArc_tail]
          exact ite_eq_left (Or.inr (Subtype.ext rfl))]
      by_cases ht : M.tail ⟨(M.edge a).val, (M.edge a).prop⟩ = true
      · rw [ht, Bool.not_true, ite_eq_right (by simp), ite_eq_left rfl, hinv]
      · have htf : M.tail ⟨(M.edge a).val, (M.edge a).prop⟩
            = false := by
          cases hbb : M.tail ⟨(M.edge a).val, (M.edge a).prop⟩
          · rfl
          · exact absurd hbb ht
        rw [htf, Bool.not_false, ite_eq_left rfl, ite_eq_right (by simp)]
    · rw [stateOddFlip_of_ne hi₁ hi₂]
      by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
      · rw [untwistD_apply_mem F _ x hb, untwistD_apply_mem F _ x hb,
          show (M.reverseArc a).tail ⟨i, hb⟩ = M.tail ⟨i, hb⟩ from by
            rw [DirMatching.reverseArc_tail]
            exact ite_eq_right (by
              rintro (hx | hx)
              · exact hi₁ (congrArg Subtype.val hx)
              · exact hi₂ (congrArg Subtype.val hx))]
      · rw [untwistD_apply_not_mem F _ x hb,
          untwistD_apply_not_mem F _ x hb]

open Classical in
/-- The dual basis's weight at given arc directions squares to
one. -/
theorem dualWeightD_mul_self {W : Fragment α}
    [Fintype α] {k ℓ : ℕ}
    (F : EdgeSubset W) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α) :
    dualWeightD F tl x * dualWeightD F tl x = 1 := by
  unfold dualWeightD
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun i _ => ?_)
  by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
  · rw [dite_eq_left hb]
    by_cases ht : tl ⟨i, hb⟩ = true
    · rw [ite_eq_left ht]
      exact dualFactor_sq (x i)
    · rw [ite_eq_right ht]
      norm_num
  · rw [dite_eq_right hb]
    norm_num

open Classical in
/-- **The change of basis preserves which legs are odd**, so the
subset-matching condition does not see the arc directions. -/
theorem genBoundarySubsetMatches_untwistD {W : Fragment α}
    {k ℓ : ℕ}
    (F : EdgeSubset W) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α) :
    genBoundarySubsetMatches W F.flags (untwistD F tl x)
      ↔ genBoundarySubsetMatches W F.flags x := by
  have hodd : ∀ i : α, (∃ c, untwistD F tl x i = Sum.inr c)
      ↔ (∃ c, x i = Sum.inr c) := by
    intro i
    by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
    · rw [untwistD_apply_mem F tl x hb]
      by_cases ht : tl ⟨i, hb⟩ = true
      · rw [ite_eq_left ht]
        rcases hx : x i with a | c
        · exact ⟨fun ⟨d, hd⟩ => absurd hd (by simp), fun ⟨d, hd⟩ =>
            absurd hd (by simp)⟩
        · exact ⟨fun _ => ⟨c, rfl⟩,
            fun _ => ⟨oddPartner ℓ c, rfl⟩⟩
      · rw [ite_eq_right ht]
    · rw [untwistD_apply_not_mem F tl x hb]
  constructor
  · intro hm i
    exact (hm i).trans (hodd i)
  · intro hm i
    exact (hm i).trans (hodd i).symm

end OrderFreeArc

open Classical in
/-- The dual basis's weight squares to one. -/
theorem dualWeight_mul_self [LinearOrder α] {W : Fragment α}
    [Fintype α] {k ℓ : ℕ}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α) :
    dualWeight F κ o x * dualWeight F κ o x = 1 := by
  unfold dualWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun i _ => ?_)
  by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
  · rw [dite_eq_left hb]
    by_cases ht : (cutMatching F κ o).tail ⟨i, hb⟩ = true
    · rw [ite_eq_left ht]
      exact dualFactor_sq (x i)
    · rw [ite_eq_right ht]
      norm_num
  · rw [dite_eq_right hb]
    norm_num

/-! ### The through-edge product ignores a chain flip

A chain's two labels are not through-labels, so flipping the state
there leaves every through-edge's two colours alone.
-/

open Classical in
/-- A through-flag's own label is a through-label. -/
theorem isThroughLabel_of_mem_throughFlags {W : Fragment α}
    {F : EdgeSubset W}
    {f : W.Flag} (hf : f ∈ F.throughFlags) {i : α}
    (hi : W.attach f = Sum.inr i) : IsThroughLabel F i := by
  obtain ⟨hmem, -, ⟨j, hj⟩⟩ := mem_throughFlags_iff.mp hf
  have hfe : f = W.boundaryFlag i := W.eq_boundaryFlag i f hi
  unfold IsThroughLabel
  rw [← hfe]
  exact Finset.mem_filter.mpr ⟨F.pairing_mem f hmem, ⟨j, hj⟩⟩

open Classical in
/-- A used through-label's flag is a through-flag. -/
theorem mem_throughFlags_of_isThroughLabel {W : Fragment α}
    {F : EdgeSubset W} {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hit : IsThroughLabel F i) :
    W.boundaryFlag i ∈ F.throughFlags :=
  mem_throughFlags_iff.mpr ⟨mem_flags_of_boundaryFlags F hb,
    ⟨i, W.attach_boundaryFlag i⟩, (Finset.mem_filter.mp hit).2⟩

end RS
