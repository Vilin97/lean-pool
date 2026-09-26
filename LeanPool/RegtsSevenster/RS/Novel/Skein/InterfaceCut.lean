/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueLedger
public import LeanPool.RegtsSevenster.RS.Novel.Skein.VertexSum
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SuperGram
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceOrderIso
public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor

/-!
# The interface matching on a fragment's used labels

RS21 pairs the chord matching `M(ω,κ)` with the matching that
identifies the two fragments' labels, and counts the components of
their union.  In the flag model that second matching lives on the
labels of a single fragment whose boundary index is a sum: the left
half is one side's labels, the right half the other's, and an
identification of the two halves says which label is glued to which.

Only the labels the subset uses carry chords, so the interface
matching has to be read there — which asks that the subset use the
two halves of every interface pair together.  That is exactly the
condition under which a glued edge is in the Eulerian subset or out
of it, and it is what the boundary state pins.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment Equiv
section InterfaceCut

variable {γ δ : Type}

/-- **The subset uses the two halves of every interface pair
together.** -/
def InterfacePaired
    {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ) : Prop :=
  ∀ a : γ, V.boundaryFlag (Sum.inl a) ∈ F.boundaryFlags
    ↔ V.boundaryFlag (Sum.inr (e a)) ∈ F.boundaryFlags

/-- The used labels, split by side. -/
def usedSideEquiv {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) :
    UsedLab F
      ≃ {a : γ // V.boundaryFlag (Sum.inl a) ∈ F.boundaryFlags}
        ⊕ {b : δ // V.boundaryFlag (Sum.inr b) ∈ F.boundaryFlags} where
  toFun x :=
    match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, h⟩
  invFun := fun
    | Sum.inl a => ⟨Sum.inl a.val, a.prop⟩
    | Sum.inr b => ⟨Sum.inr b.val, b.prop⟩
  left_inv := fun x => by
    obtain ⟨y, hy⟩ := x
    cases y <;> rfl
  right_inv := fun x => by cases x <;> rfl

/-- The identification of the two sides' used labels. -/
def interfaceSideEquiv {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ)
    (hp : InterfacePaired F e) :
    {a : γ // V.boundaryFlag (Sum.inl a) ∈ F.boundaryFlags}
      ≃ {b : δ // V.boundaryFlag (Sum.inr b) ∈ F.boundaryFlags} :=
  e.subtypeEquiv (fun a => hp a)

/-- **The interface matching on the used labels**: each used label of
one side paired with the label it is glued to. -/
noncomputable def interfaceCut
    {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ)
    (hp : InterfacePaired F e) :
    DirMatching (UsedLab F) :=
  (DirMatching.interfaceEquivMatching
    (interfaceSideEquiv F e hp)).map (usedSideEquiv F).symm

/-- **The label involution the interface matching realises**: swap
sides along the identification. -/
def interfaceSwap (e : γ ≃ δ) : γ ⊕ δ → γ ⊕ δ :=
  Sum.elim (fun a => Sum.inr (e a)) (fun b => Sum.inl (e.symm b))

/-- **The interface matching pairs by the swap.** -/
theorem interfaceCut_edge_val
    {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ)
    (hp : InterfacePaired F e)
    (x : UsedLab F) :
    ((interfaceCut F e hp).edge x).val = interfaceSwap e x.val := by
  obtain ⟨y, hy⟩ := x
  cases y <;> rfl

end InterfaceCut

/-! ## Pairing, read on the swap

`InterfacePaired` is about the two halves of a sum; the constructions
the recursion applies — a glue, then a relabel — do not preserve that
shape, the glued fragment's labels being a subtype rather than a sum.
Reading the condition on the swap instead removes the shape from it,
and then both constructions transport it by a single equation between
label maps.
-/

section SwapPaired

variable {L : Type} {V : Fragment L} (F : EdgeSubset V) (ι : L → L)

/-- **The subset uses a label exactly when it uses its partner.** -/
def SwapPaired : Prop :=
  ∀ x : L, V.boundaryFlag x ∈ F.boundaryFlags
    ↔ V.boundaryFlag (ι x) ∈ F.boundaryFlags

end SwapPaired

section SwapPairedSum

variable {γ δ : Type}

/-- **Pairing on the swap is pairing across the interface.** -/
theorem swapPaired_iff_interfacePaired
    {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ) :
    SwapPaired F (interfaceSwap e) ↔ InterfacePaired F e := by
  constructor
  · exact fun h a => h (Sum.inl a)
  · intro h x
    cases x with
    | inl a => exact h a
    | inr b =>
      have := (h (e.symm b)).symm
      rwa [e.apply_symm_apply] at this

end SwapPairedSum

section SwapPairedTransport

/-- **Pairing transports along any reading of one subset's used
labels in another's.**  Both constructions the recursion applies are
of this shape: a glue reads a surviving label as a label, a relabel
reads a new index as an old one. -/
theorem swapPaired_of_mem_iff {L L' : Type} {V : Fragment L}
    {V' : Fragment L'} (F : EdgeSubset V) (F' : EdgeSubset V')
    (ι : L → L) (ι' : L' → L') (φ : L' → L)
    (hmem : ∀ x : L', V'.boundaryFlag x ∈ F'.boundaryFlags
      ↔ V.boundaryFlag (φ x) ∈ F.boundaryFlags)
    (hcomp : ∀ x : L', φ (ι' x) = ι (φ x))
    (h : SwapPaired F ι) : SwapPaired F' ι' := by
  intro x
  rw [hmem x, hmem (ι' x), hcomp x]
  exact h (φ x)

variable {α β : Type}

/-- **Pairing shifts through a relabel.** -/
theorem swapPaired_relabelUp [LinearOrder α] [LinearOrder β] {W : Fragment α}
    (E : α ≃o β) (F : EdgeSubset W)
    (ι : α → α) (ι' : β → β)
    (hcomp : ∀ x : α, E.symm (ι' (E x)) = ι x)
    (h : SwapPaired F ι) :
    SwapPaired (F.relabelUp E.toEquiv) ι' :=
  swapPaired_of_mem_iff F (F.relabelUp E.toEquiv) ι ι'
    (fun b => E.symm b)
    (fun b => by rw [relabelUp_boundaryFlags E F]; exact Iff.rfl)
    (fun b => by
      have := hcomp (E.symm b)
      rwa [E.apply_symm_apply] at this)
    h

section SwapPairedCut

/-- **A paired subset reaches the glue.**  The glue only sees the
base's subsets that use its two labels together, and a subset paired
by the swap uses them together whenever the swap pairs them. -/
theorem agreeingSubset_of_swapPaired
    {L : Type} {V : Fragment L} (F : EdgeSubset V) (ι : L → L)
    (h : SwapPaired F ι) {i j : L}
    (hij : ι i = j) : AgreeingSubset i j F.flags := by
  refine ⟨F.pairing_mem, ⟨fun hi => ?_, fun hj => ?_⟩⟩
  · have hb := (h i).mp (boundaryFlag_mem_boundaryFlags hi)
    rw [hij] at hb
    exact mem_flags_of_boundaryFlags F hb
  · refine mem_flags_of_boundaryFlags F ((h i).mpr ?_)
    rw [hij]
    exact boundaryFlag_mem_boundaryFlags hj

/-- **The glued pair are partners of the interface matching**, which
is what makes the glue contract it. -/
theorem edge_eq_of_swap
    {L : Type} {V : Fragment L} (F : EdgeSubset V) (ι : L → L)
    {N : DirMatching (UsedLab F)}
    (hN : ∀ x : UsedLab F, ((N.edge x).val : L) = ι x.val) {i j : L}
    (hbi : V.boundaryFlag i ∈ F.boundaryFlags)
    (hbj : V.boundaryFlag j ∈ F.boundaryFlags) (hij : ι i = j) :
    N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ :=
  Subtype.ext ((hN ⟨i, hbi⟩).trans hij)

end SwapPairedCut

end SwapPairedTransport

/-! ## The interface matching through a relabel

The interface recursion relabels after every glue, and the relabel
carries the interface identification with it.  Since the matching's
pairing is the swap, all the transport has to check is that the swap
commutes with the relabel — one equation between label maps, with no
subsets, systems or orientations in it.
-/

section InterfaceRelabel

variable {α γ' δ' : Type}

/-- **The relabelled interface matching pairs by the transported
swap.** -/
theorem interfaceCut_relabelUp_edge
    [LinearOrder α] [LinearOrder (γ' ⊕ δ')] {W : Fragment α}
    (F : EdgeSubset W) (E : α ≃o (γ' ⊕ δ')) (e' : γ' ≃ δ')
    (hp' : InterfacePaired (F.relabelUp E.toEquiv) e')
    (x : UsedLab F) :
    (((interfaceCut (F.relabelUp E.toEquiv) e' hp').map
        (usedLabRelabelEquiv E F)).edge x).val
      = E.symm (interfaceSwap e' (E x.val)) := by
  change E.symm ((interfaceCut (F.relabelUp E.toEquiv) e' hp').edge
      ⟨E x.val, _⟩).val = _
  rw [interfaceCut_edge_val]

end InterfaceRelabel

/-! ## One stage of the interface matching

At a stage the fragment is glued and then relabelled, and the
interface matching of the result has to be the base's, contracted at
the glued pair.  All four kinds of cut read a surviving label as a
label, so the whole comparison is one equation between label maps:
the transported swap on surviving labels is the base's swap.
-/

section InterfaceStage

variable {L Lg γ' δ' : Type}

/-- **A glue restricts a matching that pairs by an involution of the
labels.**  Both sides pair by the same involution, so reading the
glued fragment's matching on the base's used labels gives the base's,
restricted at the glued pair. -/
theorem restrict_edge_of_swap
    {V : Fragment L} {Vg : Fragment Lg} (Fl : EdgeSubset V)
    (Fg : EdgeSubset Vg) (φ : Lg → L) (ι : L → L)
    {N : DirMatching (UsedLab Fl)}
    (hN : ∀ x : UsedLab Fl, ((N.edge x).val : L) = ι x.val)
    {Ng : DirMatching (UsedLab Fg)}
    (hNg : ∀ z : UsedLab Fg, φ ((Ng.edge z).val) = ι (φ z.val))
    {i j : UsedLab Fl} (hNij : N.edge i = j)
    (G : UsedLab Fg ≃ DirMatching.Surviving i j)
    (hG : ∀ w : UsedLab Fg, ((G w).val.val : L) = φ w.val) :
    (Ng.map G).edge = (N.restrict hNij).edge := by
  funext y
  have hGs : ∀ z : DirMatching.Surviving i j,
      φ ((G.symm z).val) = z.val.val := by
    intro z
    have := hG (G.symm z)
    rw [G.apply_symm_apply] at this
    exact this.symm
  refine Subtype.ext (Subtype.ext ?_)
  rw [DirMatching.map_edge G, hG, hNg, hGs y]
  exact (hN y.val).symm

end InterfaceStage

/-! ## The swap through the interface step

The recursion's relabel is `interfaceStepEquiv`, which deletes the
glued label from each half and re-indexes.  The interface swap
commutes with it: on either side the deletion is at the top of the
half, so it leaves every surviving label's index alone, and the swap
is the identity on indices.
-/

section InterfaceStep

/-- The identification of the two halves at interface size `n`. -/
def stepIdent (n : ℕ) : Fin (0 + n) ≃ Fin (n + 0) :=
  finCongr (by omega)

/-- The interface identification keeps a label's index. -/
theorem stepIdent_val {n : ℕ} (v : Fin (0 + n)) :
    ((stepIdent n v : Fin (n + 0)) : ℕ) = (v : ℕ) := rfl

/-- **The interface swap commutes with the recursion's relabel.** -/
theorem interfaceSwap_interfaceStep (n : ℕ)
    (x : {x : Fin (0 + n + 1) ⊕ Fin (n + 1 + 0) //
        x ≠ Sum.inl ⟨0 + n, Nat.lt_succ_self _⟩ ∧
        x ≠ Sum.inr ⟨n, by omega⟩}) :
    ((interfaceStepEquiv 0 n 0).symm
        (interfaceSwap (stepIdent n)
          (interfaceStepEquiv 0 n 0 x))).val
      = interfaceSwap (stepIdent (n + 1)) x.val := by
  obtain ⟨y, hy⟩ := x
  cases y with
  | inl v =>
    have hv : (v : ℕ) < n := by
      have h1 : (v : ℕ) ≠ 0 + n := fun hh =>
        hy.1 (congrArg Sum.inl (Fin.ext hh))
      have h2 : (v : ℕ) < 0 + n + 1 := v.isLt
      omega
    change Sum.inr (((rightRemoveEquiv n 0).symm
        (stepIdent n (finRemoveEquiv ⟨0 + n, Nat.lt_succ_self _⟩
          ⟨v, fun he => hy.1 (congrArg Sum.inl he)⟩))).val)
      = Sum.inr (stepIdent (n + 1) v)
    refine congrArg Sum.inr (Fin.ext ?_)
    set d : Fin (n + 0) := stepIdent n
      (finRemoveEquiv ⟨0 + n, Nat.lt_succ_self _⟩
        ⟨v, fun he => hy.1 (congrArg Sum.inl he)⟩) with hd
    have hdv : (d : ℕ) = (v : ℕ) := by
      rw [hd, stepIdent_val]
      exact finRemoveEquiv_top_val (n := 0 + n) _
    set z := (rightRemoveEquiv n 0).symm d with hz
    have hzd : (rightRemoveEquiv n 0 z : ℕ) = (d : ℕ) := by
      rw [hz, Equiv.apply_symm_apply]
    have hzne : (z.val : ℕ) ≠ n := fun hh => z.prop (Fin.ext hh)
    have hval := rightRemoveEquiv_val n 0 z
    rw [hzd] at hval
    have : ((stepIdent (n + 1) v : Fin (n + 1 + 0)) : ℕ) = (v : ℕ) := rfl
    rw [this]
    split_ifs at hval with hlt
    · omega
    · omega
  | inr w =>
    have hw : (w : ℕ) < n := by
      have h1 : (w : ℕ) ≠ n := fun hh =>
        hy.2 (congrArg Sum.inr (Fin.ext hh))
      have h2 : (w : ℕ) < n + 1 + 0 := w.isLt
      omega
    change Sum.inl (((finRemoveEquiv ⟨0 + n, Nat.lt_succ_self _⟩).symm
        ((stepIdent n).symm (rightRemoveEquiv n 0
          ⟨w, fun he => hy.2 (congrArg Sum.inr he)⟩))).val)
      = Sum.inl ((stepIdent (n + 1)).symm w)
    refine congrArg Sum.inl (Fin.ext ?_)
    set c : Fin (0 + n) := (stepIdent n).symm (rightRemoveEquiv n 0
      ⟨w, fun he => hy.2 (congrArg Sum.inr he)⟩) with hc
    have hcw : (c : ℕ) = (w : ℕ) := by
      have h := rightRemoveEquiv_val n 0
        ⟨w, fun he => hy.2 (congrArg Sum.inr he)⟩
      rw [ite_eq_left hw] at h
      change ((rightRemoveEquiv n 0
        ⟨w, fun he => hy.2 (congrArg Sum.inr he)⟩ : Fin (n + 0)) : ℕ)
        = (w : ℕ)
      exact h
    set z := (finRemoveEquiv
      (⟨0 + n, Nat.lt_succ_self _⟩ : Fin (0 + n + 1))).symm c with hz
    have hzc : (finRemoveEquiv
        (⟨0 + n, Nat.lt_succ_self _⟩ : Fin (0 + n + 1)) z : ℕ)
        = (c : ℕ) := by rw [hz, Equiv.apply_symm_apply]
    have hval := finRemoveEquiv_top_val (n := 0 + n) z
    rw [hzc] at hval
    have : (((stepIdent (n + 1)).symm w : Fin (0 + n + 1)) : ℕ)
        = (w : ℕ) := rfl
    rw [this]
    omega

/-- **The recursion's cut pair are interface partners**, which is
what makes the glue contract the interface matching rather than
merge two of its arcs. -/
theorem interfaceSwap_cut (n : ℕ) :
    interfaceSwap (stepIdent (n + 1))
        (Sum.inl ⟨0 + n, Nat.lt_succ_self _⟩)
      = Sum.inr (⟨n, by omega⟩ : Fin (n + 1 + 0)) := by
  refine congrArg Sum.inr (Fin.ext ?_)
  change (0 + n : ℕ) = n
  omega

end InterfaceStep

/-! ## The closed top

At the empty interface there are no labels, hence no through edges,
and the through-edge product the flag model carries is one.  That is
where RS21's `s_h(G,H)` and the flag model's summand meet.
-/

section ClosedTop

variable {L : Type}

/-- A closed fragment has no through flags: every flag meets a
vertex. -/
theorem throughFlags_isEmpty [IsEmpty L] {V : Fragment L}
    (F : EdgeSubset V) :
    F.throughFlags = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun f hf => ?_)
  obtain ⟨-, ⟨i, -⟩, -⟩ := mem_throughFlags_iff.mp hf
  exact isEmptyElim i

/-- At the closed top every flag is internal: there are no labels to
attach to. -/
theorem allInternal_isEmpty [IsEmpty L] {V : Fragment L}
    (F : EdgeSubset V) : F.allInternal := by
  classical
  refine Finset.eq_empty_of_forall_notMem (fun f hf => ?_)
  obtain ⟨-, i, -⟩ := Finset.mem_filter.mp hf
  exact isEmptyElim i

/-- **The chord sign is trivial at the closed top.**  There are no
labels, hence no chords to cross. -/
theorem pathSign_isEmpty [LinearOrder L] [IsEmpty L] {V : Fragment L}
    (F : EdgeSubset V)
    (κ : F.RelTransitionSystem) : pathSign κ = 1 :=
  pathSign_of_allInternal (allInternal_isEmpty F) κ

open Classical in
/-- **The closed top's value is RS21's `s_h(G,H)`**: the circuit sign
times the colouring sum, with no chord sign and no through-edge
product. -/
theorem throughValueC_isEmpty [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ} (F : EdgeSubset V)
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st)
    (hne : Nonempty F.CanonData) :
    F.throughValueC h st hbnd
      = F.throughSummand h st hbnd (Classical.choice hne).2.val
          ((Classical.choice hne).1.openCircuitCount) := by
  unfold EdgeSubset.throughValueC
  rw [dite_eq_left hne, pathSign_isEmpty, one_mul]

open Classical in
/-- **The closed top's partition value is a sum of RS21's
summands.**  With no labels the chord sign is one and the
through-edge product is one, so each Eulerian subset contributes its
circuit sign times its colouring sum — RS21's `s_h(G,H)`. -/
theorem throughMixedPartitionC_isEmpty
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L) :
    throughMixedPartitionC h V st
      = ((k : ℂ) - 2 * ℓ) ^ V.circles *
        ∑ s : Finset V.Flag,
          if hc : ∀ f ∈ s, V.pairing f ∈ s then
            if hbnd : genBoundarySubsetMatches V s st then
              if (EdgeSubset.mk s hc).Eulerian then
                if hne : Nonempty (EdgeSubset.mk s hc).CanonData then
                  (EdgeSubset.mk s hc).throughSummand h st hbnd
                    (Classical.choice hne).2.val
                    ((Classical.choice hne).1.openCircuitCount)
                else 0
              else 0
            else 0
          else 0 := by
  unfold throughMixedPartitionC
  refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl (fun s _ => ?_))
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · rw [dite_eq_left hc, dite_eq_left hc]
    by_cases hbnd : genBoundarySubsetMatches V s st
    · rw [dite_eq_left hbnd, dite_eq_left hbnd]
      by_cases hE : (EdgeSubset.mk s hc).Eulerian
      · rw [ite_eq_left hE, ite_eq_left hE]
        by_cases hne : Nonempty (EdgeSubset.mk s hc).CanonData
        · rw [dite_eq_left hne]
          exact throughValueC_isEmpty _ h st hbnd hne
        · rw [dite_eq_right hne]
          unfold EdgeSubset.throughValueC
          rw [dite_eq_right hne]
      · rw [ite_eq_right hE, ite_eq_right hE]
    · rw [dite_eq_right hbnd, dite_eq_right hbnd]
  · rw [dite_eq_right hc, dite_eq_right hc]

/-- **The through-edge product is one at the closed top.** -/
theorem throughProduct_isEmpty [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ} (F : EdgeSubset V)
    (st : GenBoundaryState k ℓ L) : F.throughProduct st = 1 := by
  unfold EdgeSubset.throughProduct
  rw [throughFlags_isEmpty F]
  rfl

end ClosedTop

/-! ## The union at a disjoint union

At the start of the interface recursion the fragment is a disjoint
union, its two boundary halves are the two fragments' own labels, and
its chord matching is the two fragments' chord matchings side by
side.  So the union of the chord matching with the interface matching
is RS21's own union `M(ω₁,κ₁) ∪ M(ω₂,κ₂)`, read on one copy of the
label set through the interface identification — which is the form
Lemma 11 for a composition consumes.
-/

section DisjUnionCut

variable {α β : Type}

/-- The used labels of the left half. -/
def usedLeftEquiv
    {W₁ : Fragment α} {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂)) :
    {a : α //
        (W₁.disjUnion W₂).boundaryFlag (Sum.inl a) ∈ F.boundaryFlags}
      ≃ UsedLab (leftSub F) :=
  Equiv.subtypeEquivRight (fun _ => inl_mem_boundary)

/-- The used labels of the right half. -/
def usedRightEquiv
    {W₁ : Fragment α} {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂)) :
    {b : β //
        (W₁.disjUnion W₂).boundaryFlag (Sum.inr b) ∈ F.boundaryFlags}
      ≃ UsedLab (rightSub F) :=
  Equiv.subtypeEquivRight (fun _ => inr_mem_boundary)

/-- The used labels of a disjoint union, split into the two sides'
own. -/
def usedDisjUnionEquiv
    {W₁ : Fragment α} {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂)) :
    UsedLab F ≃ UsedLab (leftSub F) ⊕ UsedLab (rightSub F) :=
  (usedSideEquiv F).trans
    (Equiv.sumCongr (usedLeftEquiv F) (usedRightEquiv F))

/-- **The chord of a left label is the left side's chord.** -/
theorem chordInv_prodRel_inl
    [LinearOrder α] [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    (F : EdgeSubset (W₁.disjUnion W₂))
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) {a : α}
    (hb : (W₁.disjUnion W₂).boundaryFlag (Sum.inl a)
      ∈ F.boundaryFlags) :
    chordInv F (prodRel κ₁ κ₂) (Sum.inl a)
      = Sum.inl (chordInv (leftSub F) κ₁ a) := by
  have hb' : W₁.boundaryFlag a ∈ (leftSub F).boundaryFlags :=
    inl_mem_boundary.mp hb
  refine (W₁.disjUnion W₂).boundaryFlag_injective ?_
  rw [boundaryFlag_chordInv F (prodRel κ₁ κ₂) hb]
  change (prodRel κ₁ κ₂).pathMatch (Sum.inl (W₁.boundaryFlag a)) hb
    = Sum.inl (W₁.boundaryFlag (chordInv (leftSub F) κ₁ a))
  rw [pathMatch_prodRel_inl κ₁ κ₂ hb hb',
    boundaryFlag_chordInv (leftSub F) κ₁ hb']

/-- **The chord of a right label is the right side's chord.** -/
theorem chordInv_prodRel_inr
    [LinearOrder α] [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    (F : EdgeSubset (W₁.disjUnion W₂))
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) {b : β}
    (hb : (W₁.disjUnion W₂).boundaryFlag (Sum.inr b)
      ∈ F.boundaryFlags) :
    chordInv F (prodRel κ₁ κ₂) (Sum.inr b)
      = Sum.inr (chordInv (rightSub F) κ₂ b) := by
  have hb' : W₂.boundaryFlag b ∈ (rightSub F).boundaryFlags :=
    inr_mem_boundary.mp hb
  refine (W₁.disjUnion W₂).boundaryFlag_injective ?_
  rw [boundaryFlag_chordInv F (prodRel κ₁ κ₂) hb]
  change (prodRel κ₁ κ₂).pathMatch (Sum.inr (W₂.boundaryFlag b)) hb
    = Sum.inr (W₂.boundaryFlag (chordInv (rightSub F) κ₂ b))
  rw [pathMatch_prodRel_inr κ₁ κ₂ hb hb',
    boundaryFlag_chordInv (rightSub F) κ₂ hb']

/-- **The chord matching of a disjoint union is the two sides' chord
matchings, side by side.** -/
theorem cutMatching_disjUnion_edge
    [LinearOrder α] [LinearOrder β] [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    ((cutMatching F (prodRel κ₁ κ₂) (prodOrient o₁ o₂)).map
        (usedDisjUnionEquiv F)).edge
      = (DirMatching.sumMatching (cutMatching (leftSub F) κ₁ o₁)
          (cutMatching (rightSub F) κ₂ o₂)).edge := by
  funext x
  rcases x with a | b
  · have hb : (W₁.disjUnion W₂).boundaryFlag (Sum.inl a.val)
        ∈ F.boundaryFlags := inl_mem_boundary.mpr a.prop
    have hy : (cutMatching F (prodRel κ₁ κ₂)
          (prodOrient o₁ o₂)).edge
          ((usedDisjUnionEquiv F).symm (Sum.inl a))
        = ⟨Sum.inl (chordInv (leftSub F) κ₁ a.val), by
            rw [← chordInv_prodRel_inl F κ₁ κ₂ hb]
            exact chordInv_mem F (prodRel κ₁ κ₂) hb⟩ :=
      Subtype.ext (chordInv_prodRel_inl F κ₁ κ₂ hb)
    change usedDisjUnionEquiv F ((cutMatching F (prodRel κ₁ κ₂)
        (prodOrient o₁ o₂)).edge
        ((usedDisjUnionEquiv F).symm (Sum.inl a))) = _
    rw [hy]
    rfl
  · have hb : (W₁.disjUnion W₂).boundaryFlag (Sum.inr b.val)
        ∈ F.boundaryFlags := inr_mem_boundary.mpr b.prop
    have hy : (cutMatching F (prodRel κ₁ κ₂)
          (prodOrient o₁ o₂)).edge
          ((usedDisjUnionEquiv F).symm (Sum.inr b))
        = ⟨Sum.inr (chordInv (rightSub F) κ₂ b.val), by
            rw [← chordInv_prodRel_inr F κ₁ κ₂ hb]
            exact chordInv_mem F (prodRel κ₁ κ₂) hb⟩ :=
      Subtype.ext (chordInv_prodRel_inr F κ₁ κ₂ hb)
    change usedDisjUnionEquiv F ((cutMatching F (prodRel κ₁ κ₂)
        (prodOrient o₁ o₂)).edge
        ((usedDisjUnionEquiv F).symm (Sum.inr b))) = _
    rw [hy]
    rfl

/-- The interface identification, read on the two sides' own used
labels. -/
def interfaceSideDisjEquiv
    {W₁ : Fragment α} {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    (e : α ≃ β)
    (hp : InterfacePaired F e) :
    UsedLab (leftSub F) ≃ UsedLab (rightSub F) :=
  (usedLeftEquiv F).symm.trans
    ((interfaceSideEquiv F e hp).trans (usedRightEquiv F))

/-- The interface identification on the two sides' used labels, as
an order isomorphism when the identification is one. -/
def interfaceSideDisjOrderIso
    [LinearOrder α] [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    (F : EdgeSubset (W₁.disjUnion W₂))
    (E : α ≃o β)
    (hp : InterfacePaired F E.toEquiv) :
    UsedLab (leftSub F) ≃o UsedLab (rightSub F) where
  toEquiv := interfaceSideDisjEquiv F E.toEquiv hp
  map_rel_iff' := E.map_rel_iff

/-- **The interface matching of a disjoint union is the interface
identification, read on the two sides' used labels.** -/
theorem interfaceCut_disjUnion_edge
    {W₁ : Fragment α} {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    (e : α ≃ β)
    (hp : InterfacePaired F e) :
    ((interfaceCut F e hp).map (usedDisjUnionEquiv F)).edge
      = (DirMatching.interfaceEquivMatching
          (interfaceSideDisjEquiv F e hp)).edge := by
  funext x
  rcases x with a | b
  · rfl
  · rfl

/-- **The colouring sum splits over a disjoint union.**  RS21's
`∏_{v ∈ V′(F₁∗F₂)}` is `∏_{v ∈ V′(F₁)} ∏_{v ∈ V′(F₂)}`, and at a
fixed interface colouring the two sides' sums are independent. -/
theorem vertexSum_disjUnion {W₁ : Fragment α} {W₂ : Fragment β}
    (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    F.vertexSum h st hbnd (prodOrient o₁ o₂)
      = (leftSub F).vertexSum h (fun a => st (Sum.inl a)) hbnd₁ o₁
        * (rightSub F).vertexSum h (fun b => st (Sum.inr b)) hbnd₂
          o₂ :=
  colouringSum_split h st hbnd hbnd₁ hbnd₂ o₁ o₂

/-- **RS21's union, at the start of the recursion.**  The union of a
disjoint union's chord matching with its interface matching counts
what the two fragments' own chord matchings count, identified along
the interface. -/
theorem unionCount_cutMatching_disjUnion
    [LinearOrder α] [LinearOrder β] [Fintype α] [Fintype β]
    [LinearOrder (α ⊕ β)] {W₁ : Fragment α} {W₂ : Fragment β}
    (F : EdgeSubset (W₁.disjUnion W₂)) (e : α ≃ β)
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (hp : InterfacePaired F e) :
    DirMatching.unionCount
        (cutMatching F (prodRel κ₁ κ₂) (prodOrient o₁ o₂))
        (interfaceCut F e hp)
      = DirMatching.unionCount (cutMatching (leftSub F) κ₁ o₁)
          ((cutMatching (rightSub F) κ₂ o₂).map
            (interfaceSideDisjEquiv F e hp).symm) := by
  classical
  rw [← DirMatching.unionCount_map (usedDisjUnionEquiv F)
      (cutMatching F (prodRel κ₁ κ₂) (prodOrient o₁ o₂))
      (interfaceCut F e hp),
    DirMatching.unionCount_congr
      (cutMatching_disjUnion_edge F κ₁ κ₂ o₁ o₂)
      (interfaceCut_disjUnion_edge F e hp),
    DirMatching.unionCount_sumMatching (interfaceSideDisjEquiv F e hp)]

end DisjUnionCut

end EdgeSubset

end RS
