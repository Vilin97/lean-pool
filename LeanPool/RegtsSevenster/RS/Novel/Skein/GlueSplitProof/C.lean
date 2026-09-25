/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSplitProof.A

/-!
# The closed and open masters

The per-subset ledgers and the open-cut engine, assembled into the
master splitting identities.
-/

namespace RS



namespace EdgeSubset

open Fragment

/-! ### The open engine: non-participating correspondences -/

section OpenEngine

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')
  (hni : partnerSurvI hopen ∉ s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc : EdgeSubset W)

include hc' hc hni in
omit hc in
/-- The far end of the `j`-edge is also absent. -/
theorem hnj_of : partnerSurvJ hopen ∉ s' :=
  partnerSurvJ_notMem_of hij hopen s' hc' hni

include hij hni in
private theorem bfi_not_mem_lift :
    W.boundaryFlag i ∉ liftSubsetOpen hopen s' := fun hmem =>
  hni ((boundaryFlagI_mem_liftOpen_iff hij hopen s').mp hmem)

include hc' hc hni in
omit hc in
private theorem bfj_not_mem_lift :
    W.boundaryFlag j ∉ liftSubsetOpen hopen s' := fun hmem =>
  hnj_of hij hopen s' hc' hni
    ((boundaryFlagJ_mem_liftOpen_iff hij hopen s').mp hmem)

/-- Eulerian transport across the open lift. -/
theorem eulerian_lift_open_iff :
    (Fl).Eulerian ↔ (Fg).Eulerian := by
  have hdeg : ∀ v : W.Vertex, (Fl).deg v = (Fg).deg v := by
    intro v
    exact deg_liftSubsetOpen_eq hopen s' v
  constructor <;> intro hE v
  · rw [← hdeg v]; exact hE v
  · rw [hdeg v]; exact hE v

/-- The glued boundary-state constraint follows from the lifted
one (open case). -/
theorem genBoundarySubsetMatches_glued_of_liftOpen {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ))
    (hbndW : genBoundarySubsetMatches W
      (liftSubsetOpen hopen s')
      (GenBoundaryState.extendPair i j st c c')) :
    genBoundarySubsetMatches (W.gluePairOpen i j hij hopen) s' st
    := by
  intro a
  have h := hbndW a.val
  rw [GenBoundaryState.extendPair_surviving st c c' a] at h
  exact Iff.trans
    (surviving_val_mem_liftOpen_iff hopen s'
      (glueBoundaryFlag W i j a)).symm h

/-! #### Through product (open, non-participating) -/

variable
  (κ' : (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "κW" =>
  RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ'

local notation "oW" =>
  unglueOrientationOpen hij hopen s' hc' hc κ' o'

/-! #### In-flag lists (open) -/

/-- The lifted in-flag list is a permutation of the projected
glued in-flag list (open case). -/
theorem relInFlagsAt_perm_open (v : W.Vertex) :
    ((Fl).relInFlagsAt (oW) v).Perm
      (((Fg).relInFlagsAt o' v).map Subtype.val) := by
  refine List.perm_of_nodup_nodup_toFinset_eq
    (relInFlagsAt_nodup _ _)
    (List.Nodup.map (fun x y hxy => Subtype.ext hxy)
      (relInFlagsAt_nodup _ _)) ?_
  ext f
  simp only [List.mem_toFinset]
  constructor
  · intro hf
    obtain ⟨hmem, hv, hout⟩ := mem_relInFlagsAt_iff.mp hf
    have hsurv := vertex_flag_surviving (i := i) (j := j) f v hv
    refine List.mem_map.mpr ⟨⟨f, hsurv.1, hsurv.2⟩,
      mem_relInFlagsAt_iff.mpr ⟨?_, ?_, ?_⟩, rfl⟩
    · exact (surviving_val_mem_liftOpen_iff hopen s'
        ⟨f, hsurv.1, hsurv.2⟩).mp hmem
    · exact (glueAttach_inl_iff ⟨f, hsurv.1, hsurv.2⟩ v).mpr hv
    · exact (unglueIsOut_val o'.isOut
        ⟨f, hsurv.1, hsurv.2⟩).symm.trans hout
  · intro hf
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
    obtain ⟨hmem, hv, hout⟩ := mem_relInFlagsAt_iff.mp hf₀
    refine mem_relInFlagsAt_iff.mpr
      ⟨(surviving_val_mem_liftOpen_iff hopen s' f₀).mpr hmem,
        (glueAttach_inl_iff f₀ v).mp hv,
        (unglueIsOut_val o'.isOut f₀).trans hout⟩

/-- Members of the projected glued in-flag list are internal in
the open lift. -/
theorem mem_map_relInFlagsAt_internal_open {v : W.Vertex} :
    ∀ f ∈ ((Fg).relInFlagsAt o' v).map Subtype.val,
      f ∈ (Fl).internalFlags := by
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
  exact internal_val_of_glueOpen hij hopen s' hc' hc
    (mem_internal_of_mem_relInFlagsAt hf₀)

/-! #### Pointwise core data agreement (open) -/

/-- The core-colour entry at the matched flag agrees (open). -/
private theorem coreOdd_match_entry_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (_hint : f' ∈ (Fg).internalFlags)
    (h1 : (κW).match_ f'.val ∈ (Fl).coreFlags)
    (h2 : κ'.match_ f' ∈ (Fg).coreFlags) :
    φW.val ⟨(κW).match_ f'.val, h1⟩ =
      φ'.val ⟨κ'.match_ f', h2⟩ := by
  have hmv : (κW).match_ f'.val = (κ'.match_ f').val :=
    unglueOpen_match_val hij hopen s' hc' hc κ' f'
  have hmcoreW : (κ'.match_ f').val ∈ (Fl).coreFlags := by
    rw [← hmv]; exact h1
  exact (congrArg φW.val (Subtype.ext hmv)).trans
    (hφ (κ'.match_ f') hmcoreW h2)

/-- The core odd pair function agrees (open). -/
private theorem coreOddPairFn_lift_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (hint : f' ∈ (Fg).internalFlags)
    (hintW : f'.val ∈ (Fl).internalFlags) :
    (Fl).coreOddPairFn (κW) φW ⟨f'.val, hintW⟩ =
      (Fg).coreOddPairFn κ' φ' ⟨f', hint⟩ := by
  unfold EdgeSubset.coreOddPairFn
  refine congrArg₂ (fun x y => [x, oddPartner ℓ y]) ?_ ?_
  · exact hφ f'
      (internalFlags_subset_coreFlags _ hintW)
      (internalFlags_subset_coreFlags _ hint)
  · exact coreOdd_match_entry_open hij hopen s' hc' hc κ' φW φ'
      hφ f' hint
      (internalFlags_subset_coreFlags _ ((κW).match_mem _ hintW))
      (internalFlags_subset_coreFlags _ (κ'.match_mem _ hint))

/-- The core odd sign function agrees (open). -/
private theorem coreOddSignFn_lift_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (hint : f' ∈ (Fg).internalFlags)
    (hintW : f'.val ∈ (Fl).internalFlags) :
    (Fl).coreOddSignFn (κW) φW ⟨f'.val, hintW⟩ =
      (Fg).coreOddSignFn κ' φ' ⟨f', hint⟩ := by
  unfold EdgeSubset.coreOddSignFn
  refine congrArg (oddPartnerSign ℓ) ?_
  exact coreOdd_match_entry_open hij hopen s' hc' hc κ' φW φ'
    hφ f' hint
    (internalFlags_subset_coreFlags _ ((κW).match_mem _ hintW))
    (internalFlags_subset_coreFlags _ (κ'.match_mem _ hint))

/-! #### List conversions (open) -/

private theorem flatMap_pair_map_val_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (l : List (SurvivingFlag W i j)) :
    ∀ (H1 : ∀ f ∈ l.map Subtype.val, f ∈ (Fl).internalFlags)
      (H2 : ∀ f' ∈ l, f' ∈ (Fg).internalFlags),
      ((l.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).flatMap
          ((Fl).coreOddPairFn (κW) φW) =
      (l.attachWith (· ∈ (Fg).internalFlags) H2).flatMap
        ((Fg).coreOddPairFn κ' φ') := by
  induction l with
  | nil => intro _ _; rfl
  | cons f' t ih =>
    intro H1 H2
    change ((f'.val :: t.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).flatMap
          ((Fl).coreOddPairFn (κW) φW) =
      ((f' :: t).attachWith (· ∈ (Fg).internalFlags) H2).flatMap
        ((Fg).coreOddPairFn κ' φ')
    rw [List.attachWith_cons, List.attachWith_cons]
    refine congrArg₂ (· ++ ·) ?_ (ih _ _)
    exact coreOddPairFn_lift_open hij hopen s' hc' hc κ' φW φ'
      hφ f' (H2 f' (List.mem_cons_self))
      (H1 f'.val (List.mem_map.mpr
        ⟨f', List.mem_cons_self, rfl⟩))

private theorem map_sign_map_val_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (l : List (SurvivingFlag W i j)) :
    ∀ (H1 : ∀ f ∈ l.map Subtype.val, f ∈ (Fl).internalFlags)
      (H2 : ∀ f' ∈ l, f' ∈ (Fg).internalFlags),
      ((l.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).map
          ((Fl).coreOddSignFn (κW) φW) =
      (l.attachWith (· ∈ (Fg).internalFlags) H2).map
        ((Fg).coreOddSignFn κ' φ') := by
  induction l with
  | nil => intro _ _; rfl
  | cons f' t ih =>
    intro H1 H2
    change ((f'.val :: t.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).map
          ((Fl).coreOddSignFn (κW) φW) =
      ((f' :: t).attachWith (· ∈ (Fg).internalFlags) H2).map
        ((Fg).coreOddSignFn κ' φ')
    rw [List.attachWith_cons, List.attachWith_cons]
    refine congrArg₂ (· :: ·) ?_ (ih _ _)
    exact coreOddSignFn_lift_open hij hopen s' hc' hc κ' φW φ'
      hφ f' (H2 f' (List.mem_cons_self))
      (H1 f'.val (List.mem_map.mpr
        ⟨f', List.mem_cons_self, rfl⟩))

/-! #### Vertex data transports (open) -/

/-- The core odd sign at a vertex agrees (open). -/
theorem coreOddSignAt_transport_open {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    (Fl).coreOddSignAt (oW) φW v = (Fg).coreOddSignAt o' φ' v
    := by
  unfold EdgeSubset.coreOddSignAt
  have hperm := perm_attachWith
    (relInFlagsAt_perm_open hij hopen s' hc' hc κ' o' v)
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)
    (mem_map_relInFlagsAt_internal_open hij hopen s' hc' hc κ' o'
      (v := v))
  rw [List.Perm.prod_eq (hperm.map ((Fl).coreOddSignFn (κW) φW))]
  rw [map_sign_map_val_open hij hopen s' hc' hc κ' φW φ' hφ
    ((Fg).relInFlagsAt o' v) _
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)]
  rfl

/-- The evaluated core odd list at a vertex agrees (open). -/
theorem evalOdd_coreOddListAt_transport_open {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (μ : Multiset (Fin k)) (v : W.Vertex) :
    h.evalOdd μ ((Fl).coreOddListAt (oW) φW v) =
      h.evalOdd μ ((Fg).coreOddListAt o' φ' v) := by
  unfold EdgeSubset.coreOddListAt
  have hperm := perm_attachWith
    (relInFlagsAt_perm_open hij hopen s' hc' hc κ' o' v)
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)
    (mem_map_relInFlagsAt_internal_open hij hopen s' hc' hc κ' o'
      (v := v))
  have hstep := h.evalOdd_flatMap_perm μ
    ((Fl).coreOddPairFn (κW) φW) (fun _ => rfl) hperm []
  simp only [List.nil_append] at hstep
  rw [hstep,
    flatMap_pair_map_val_open hij hopen s' hc' hc κ' φW φ' hφ
      ((Fg).relInFlagsAt o' v) _
      (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)]
  rfl

/-! #### The even colouring correspondence (open) -/

/-- Push a glued even colouring to the open lift: the two glued
half-edges inherit the merged edge's colour. -/
noncomputable def evenPushOpen {k : ℕ}
    (ψ' : (Fg).EvenColouring k) : (Fl).EvenColouring k :=
  ⟨fun f =>
    if hfi : f.val = W.boundaryFlag i then
      ψ'.val ⟨partnerSurvI hopen, hni⟩
    else if hfj : f.val = W.boundaryFlag j then
      ψ'.val ⟨partnerSurvJ hopen,
        hnj_of hij hopen s' hc' hni⟩
    else ψ'.val ⟨⟨f.val, hfi, hfj⟩,
      fun hmem => f.prop ((surviving_val_mem_liftOpen_iff
        hopen s' ⟨f.val, hfi, hfj⟩).mpr hmem)⟩, by
    intro f
    dsimp only []
    by_cases hfi : f.val = W.boundaryFlag i
    · -- pairing f.val = partnerI.val
      have hpv : W.pairing f.val =
          (partnerSurvI hopen).val := by
        rw [hfi]; rfl
      have hp1 : W.pairing f.val ≠ W.boundaryFlag i := by
        rw [hpv]; exact (partnerSurvI hopen).prop.1
      have hp2 : W.pairing f.val ≠ W.boundaryFlag j := by
        rw [hpv]; exact (partnerSurvI hopen).prop.2
      rw [dite_eq_right hp1, dite_eq_right hp2, dite_eq_left hfi]
      refine congrArg ψ'.val (Subtype.ext (Subtype.ext ?_))
      exact hpv
    · by_cases hfj : f.val = W.boundaryFlag j
      · have hpv : W.pairing f.val =
            (partnerSurvJ hopen).val := by
          rw [hfj]; rfl
        have hp1 : W.pairing f.val ≠ W.boundaryFlag i := by
          rw [hpv]; exact (partnerSurvJ hopen).prop.1
        have hp2 : W.pairing f.val ≠ W.boundaryFlag j := by
          rw [hpv]; exact (partnerSurvJ hopen).prop.2
        rw [dite_eq_right hp1, dite_eq_right hp2, dite_eq_right hfi, dite_eq_left hfj]
        refine congrArg ψ'.val (Subtype.ext (Subtype.ext ?_))
        exact hpv
      · by_cases hpi' : W.pairing f.val = W.boundaryFlag i
        · -- f is the far end of the i-edge
          have hfeq : (⟨f.val, hfi, hfj⟩ : SurvivingFlag W i j) =
              partnerSurvI hopen :=
            eq_partnerSurvI_of_pairing hopen ⟨f.val, hfi, hfj⟩
              hpi'
          rw [dite_eq_left hpi', dite_eq_right hfi, dite_eq_right hfj]
          exact congrArg ψ'.val (Subtype.ext hfeq).symm
        · by_cases hpj' : W.pairing f.val = W.boundaryFlag j
          · have hfeq : (⟨f.val, hfi, hfj⟩ :
                SurvivingFlag W i j) = partnerSurvJ hopen :=
              eq_partnerSurvJ_of_pairing hopen
                ⟨f.val, hfi, hfj⟩ hpj'
            rw [dite_eq_right hpi', dite_eq_left hpj', dite_eq_right hfi,
              dite_eq_right hfj]
            exact congrArg ψ'.val (Subtype.ext hfeq).symm
          · rw [dite_eq_right hpi', dite_eq_right hpj', dite_eq_right hfi,
              dite_eq_right hfj]
            have hnotmem : (⟨f.val, hfi, hfj⟩ :
                SurvivingFlag W i j) ∉ s' := fun hmem =>
              f.prop ((surviving_val_mem_liftOpen_iff hopen
                s' ⟨f.val, hfi, hfj⟩).mpr hmem)
            have hrw : (W.gluePairOpen i j hij hopen).pairing
                ⟨f.val, hfi, hfj⟩ =
                (⟨W.pairing f.val, hpi', hpj'⟩ :
                  SurvivingFlag W i j) :=
              Subtype.ext (rewire_val_of_ne hopen
                ⟨f.val, hfi, hfj⟩ hpi' hpj')
            have hp := ψ'.prop ⟨⟨f.val, hfi, hfj⟩, hnotmem⟩
            refine Eq.trans ?_ hp
            refine congrArg ψ'.val (Subtype.ext ?_)
            exact hrw.symm⟩

/-- Pointwise agreement of the open even push at subset-avoiding
surviving flags. -/
theorem evenPushOpen_agrees {k : ℕ}
    (ψ' : (Fg).EvenColouring k) :
    ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetOpen hopen s') (h2 : g ∉ s'),
      (evenPushOpen hij hopen s' hc' hc hni ψ').val ⟨g.val, h1⟩ =
        ψ'.val ⟨g, h2⟩ := by
  intro g h1 h2
  change (if hfi : g.val = W.boundaryFlag i then _
      else if hfj : g.val = W.boundaryFlag j then _
      else ψ'.val ⟨⟨g.val, hfi, hfj⟩, _⟩) = ψ'.val ⟨g, h2⟩
  rw [dite_eq_right g.prop.1, dite_eq_right g.prop.2]

/-- The open even push at the two glued boundary flags. -/
theorem evenPushOpen_at_i {k : ℕ}
    (ψ' : (Fg).EvenColouring k)
    (hP : W.boundaryFlag i ∉ liftSubsetOpen hopen s') :
    (evenPushOpen hij hopen s' hc' hc hni ψ').val
      ⟨W.boundaryFlag i, hP⟩ =
      ψ'.val ⟨partnerSurvI hopen, hni⟩ := dite_eq_left rfl

/-- The pushed even colouring at the second glued boundary flag. -/
theorem evenPushOpen_at_j {k : ℕ}
    (ψ' : (Fg).EvenColouring k)
    (hP : W.boundaryFlag j ∉ liftSubsetOpen hopen s') :
    (evenPushOpen hij hopen s' hc' hc hni ψ').val
      ⟨W.boundaryFlag j, hP⟩ =
      ψ'.val ⟨partnerSurvJ hopen,
        hnj_of hij hopen s' hc' hni⟩ := by
  change (if hfi : W.boundaryFlag j = W.boundaryFlag i then _
      else if hfj : W.boundaryFlag j = W.boundaryFlag j then _
      else _) = _
  rw [dite_eq_right (fun hEq =>
    hij (W.boundaryFlag_injective hEq).symm), dite_eq_left rfl]

/-- The open even push is injective. -/
theorem evenPushOpen_injective {k : ℕ} :
    Function.Injective
      (evenPushOpen hij hopen s' hc' hc hni (k := k)) := by
  intro ψ₁ ψ₂ hEq
  refine Subtype.ext (funext fun x => ?_)
  have h1 : x.val.val ∉ liftSubsetOpen hopen s' := fun hmem =>
    x.prop ((surviving_val_mem_liftOpen_iff hopen s'
      x.val).mp hmem)
  have hv := congrArg (fun ψ : (Fl).EvenColouring k =>
    ψ.val ⟨x.val.val, h1⟩) hEq
  simp only [] at hv
  rw [evenPushOpen_agrees hij hopen s' hc' hc hni ψ₁ x.val h1
      x.prop,
    evenPushOpen_agrees hij hopen s' hc' hc hni ψ₂ x.val h1
      x.prop] at hv
  exact (congrArg ψ₁.val (Subtype.ext rfl)).symm.trans
    (hv.trans (congrArg ψ₂.val (Subtype.ext rfl)))

/-- The glued constancy across the merged edge. -/
theorem glued_even_merged {k : ℕ}
    (ψ' : (Fg).EvenColouring k) :
    ψ'.val ⟨partnerSurvJ hopen,
        hnj_of hij hopen s' hc' hni⟩ =
      ψ'.val ⟨partnerSurvI hopen, hni⟩ := by
  have hp := ψ'.prop ⟨partnerSurvI hopen, hni⟩
  refine Eq.trans ?_ hp
  refine congrArg ψ'.val (Subtype.ext ?_)
  exact (gluePairOpen_pairing_interface_i hij hopen
    (partnerSurvI hopen)
    (by rw [partnerSurvI_val hopen, W.pairing_invol])).symm

/-! #### The even boundary match across the open glue -/

include hc' hc in
/-- Even boundary matching transfers across an open cut: matching
the extended state upstairs is matching the state downstairs. -/
theorem genEvenBoundaryMatch_open_iff [LinearOrder α] {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (a₀ : Fin k)
    (hbndW : genBoundarySubsetMatches W
      (liftSubsetOpen hopen s')
      (GenBoundaryState.extendPair i j st (Sum.inl a₀)
        (Sum.inl a₀)))
    (hbnd' : genBoundarySubsetMatches
      (W.gluePairOpen i j hij hopen) s' st)
    (ψ' : (Fg).EvenColouring k) :
    genEvenBoundaryMatch (Fl)
        (GenBoundaryState.extendPair i j st (Sum.inl a₀)
          (Sum.inl a₀)) hbndW
        (evenPushOpen hij hopen s' hc' hc hni ψ') ↔
      (ψ'.val ⟨partnerSurvI hopen, hni⟩ = a₀ ∧
        genEvenBoundaryMatch (Fg) st hbnd' ψ') := by
  constructor
  · intro hW
    constructor
    · have hsti : GenBoundaryState.extendPair i j st (Sum.inl a₀)
          (Sum.inl a₀) i = Sum.inl a₀ :=
        GenBoundaryState.extendPair_left st _ _
      have hval := hW i a₀ hsti
      exact (evenPushOpen_at_i hij hopen s' hc' hc hni ψ'
        _).symm.trans hval
    · intro a y hst
      have hstW : GenBoundaryState.extendPair i j st (Sum.inl a₀)
          (Sum.inl a₀) a.val = Sum.inl y := by
        rw [GenBoundaryState.extendPair_surviving]
        exact hst
      have hval := hW a.val y hstW
      exact (evenPushOpen_agrees hij hopen s' hc' hc hni ψ'
        (glueBoundaryFlag W i j a) _ _).symm.trans hval
  · rintro ⟨hx, hG⟩
    intro a₀' y hst
    by_cases hai : a₀' = i
    · subst hai
      rw [GenBoundaryState.extendPair_left] at hst
      have hy : y = a₀ := (Sum.inl.inj hst).symm
      rw [evenPushOpen_at_i hij hopen s' hc' hc hni ψ', hx, hy]
    · by_cases haj : a₀' = j
      · subst haj
        rw [GenBoundaryState.extendPair_right hij] at hst
        have hy : y = a₀ := (Sum.inl.inj hst).symm
        rw [evenPushOpen_at_j hij hopen s' hc' hc hni ψ',
          glued_even_merged hij hopen s' hc' hni ψ', hx, hy]
      · have hst' : st ⟨a₀', hai, haj⟩ = Sum.inl y := by
          rw [← GenBoundaryState.extendPair_surviving st
            (Sum.inl a₀) (Sum.inl a₀) ⟨a₀', hai, haj⟩]
          exact hst
        have hval := hG ⟨a₀', hai, haj⟩ y hst'
        exact (evenPushOpen_agrees hij hopen s' hc' hc hni ψ'
          (glueBoundaryFlag W i j ⟨a₀', hai, haj⟩) _ _).trans hval

include hij hc' hc hni in
/-- Every colouring satisfying the diagonal lifted match lies in
the image of the open push. -/
theorem evenPushOpen_covers {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (a₀ : Fin k)
    (hbndW : genBoundarySubsetMatches W
      (liftSubsetOpen hopen s')
      (GenBoundaryState.extendPair i j st (Sum.inl a₀)
        (Sum.inl a₀)))
    (ψW : (Fl).EvenColouring k)
    (hmatch : genEvenBoundaryMatch (Fl)
      (GenBoundaryState.extendPair i j st (Sum.inl a₀)
        (Sum.inl a₀)) hbndW ψW) :
    ∃ ψ' : (Fg).EvenColouring k,
      evenPushOpen hij hopen s' hc' hc hni ψ' = ψW := by
  have hnl : ∀ g : SurvivingFlag W i j, g ∉ s' →
      g.val ∉ liftSubsetOpen hopen s' := fun g hg hmem =>
    hg ((surviving_val_mem_liftOpen_iff hopen s' g).mp hmem)
  -- boundary values of ψW are pinned to a₀
  have hbi : ∀ hP : W.boundaryFlag i ∉ liftSubsetOpen hopen
      s', ψW.val ⟨W.boundaryFlag i, hP⟩ = a₀ := by
    intro hP
    have := hmatch i a₀ (GenBoundaryState.extendPair_left st _ _)
    exact (congrArg ψW.val (Subtype.ext rfl)).trans this
  have hbj : ∀ hP : W.boundaryFlag j ∉ liftSubsetOpen hopen
      s', ψW.val ⟨W.boundaryFlag j, hP⟩ = a₀ := by
    intro hP
    have := hmatch j a₀
      (GenBoundaryState.extendPair_right hij st _ _)
    exact (congrArg ψW.val (Subtype.ext rfl)).trans this
  have hbfiP : W.boundaryFlag i ∉ liftSubsetOpen hopen s' :=
    bfi_not_mem_lift hij hopen s' hni
  have hbfjP : W.boundaryFlag j ∉ liftSubsetOpen hopen s' :=
    bfj_not_mem_lift hij hopen s' hc' hni
  have hpI : ∀ (hP : (partnerSurvI hopen).val ∉ liftSubsetOpen hopen s'),
      ψW.val ⟨(partnerSurvI hopen).val, hP⟩ = a₀
      := by
    intro hP
    have hp := ψW.prop ⟨W.boundaryFlag i, hbfiP⟩
    exact ((congrArg ψW.val (Subtype.ext rfl)).trans hp).trans
      (hbi hbfiP)
  have hpJ : ∀ (hP : (partnerSurvJ hopen).val ∉
      liftSubsetOpen hopen s'),
      ψW.val ⟨(partnerSurvJ hopen).val, hP⟩ = a₀ := by
    intro hP
    have hp := ψW.prop ⟨W.boundaryFlag j, hbfjP⟩
    exact ((congrArg ψW.val (Subtype.ext rfl)).trans hp).trans
      (hbj hbfjP)
  have hrwI : ((W.gluePairOpen i j hij hopen).pairing
      (partnerSurvI hopen)).val = (partnerSurvJ hopen).val :=
    congrArg Subtype.val (gluePairOpen_pairing_interface_i hij
      hopen (partnerSurvI hopen)
      (by rw [partnerSurvI_val hopen, W.pairing_invol]))
  have hrwJ : ((W.gluePairOpen i j hij hopen).pairing
      (partnerSurvJ hopen)).val = (partnerSurvI hopen).val :=
    congrArg Subtype.val (gluePairOpen_pairing_interface_j hij
      hopen (partnerSurvJ hopen)
      (by
        rw [partnerSurvJ_val hopen, W.pairing_invol]
        exact fun hh => hij (W.boundaryFlag_injective hh).symm)
      (by rw [partnerSurvJ_val hopen, W.pairing_invol]))
  refine ⟨⟨fun x => ψW.val ⟨x.val.val, hnl x.val x.prop⟩, ?_⟩, ?_⟩
  · intro x
    by_cases hxi : x.val = partnerSurvI hopen
    · have h₁ : ((W.gluePairOpen i j hij hopen).pairing
          x.val).val = (partnerSurvJ hopen).val := by
        rw [hxi]; exact hrwI
      refine ((congrArg ψW.val (Subtype.ext h₁)).trans
        (hpJ (hnl _ (hnj_of hij hopen s' hc' hni)))).trans ?_
      refine ((hpI (hnl _ hni)).symm.trans
        (congrArg ψW.val (Subtype.ext ?_)))
      change (partnerSurvI hopen).val = x.val.val
      rw [hxi]
    · by_cases hxj : x.val = partnerSurvJ hopen
      · have h₁ : ((W.gluePairOpen i j hij hopen).pairing
            x.val).val = (partnerSurvI hopen).val := by
          rw [hxj]; exact hrwJ
        refine ((congrArg ψW.val (Subtype.ext h₁)).trans
          (hpI (hnl _ hni))).trans ?_
        refine ((hpJ (hnl _
          (hnj_of hij hopen s' hc' hni))).symm.trans
          (congrArg ψW.val (Subtype.ext ?_)))
        change (partnerSurvJ hopen).val = x.val.val
        rw [hxj]
      · have hp1 : W.pairing x.val.val ≠ W.boundaryFlag i :=
          fun hh => hxi (eq_partnerSurvI_of_pairing hopen x.val hh)
        have hp2 : W.pairing x.val.val ≠ W.boundaryFlag j :=
          fun hh => hxj
            (eq_partnerSurvJ_of_pairing hopen x.val hh)
        have h₁ : ((W.gluePairOpen i j hij hopen).pairing
            x.val).val = W.pairing x.val.val :=
          rewire_val_of_ne hopen x.val hp1 hp2
        have hp := ψW.prop ⟨x.val.val, hnl x.val x.prop⟩
        exact ((congrArg ψW.val (Subtype.ext h₁)).trans hp)
  · refine Subtype.ext (funext fun f => ?_)
    change (if hfi : f.val = W.boundaryFlag i then _
        else if hfj : f.val = W.boundaryFlag j then _
        else _) = ψW.val f
    by_cases hfi : f.val = W.boundaryFlag i
    · rw [dite_eq_left hfi]
      refine (hpI (hnl _ hni)).trans ?_
      refine ((hbi hbfiP).symm.trans
        (congrArg ψW.val (Subtype.ext ?_)))
      exact hfi.symm
    · by_cases hfj : f.val = W.boundaryFlag j
      · rw [dite_eq_right hfi, dite_eq_left hfj]
        refine (hpJ (hnl _
          (hnj_of hij hopen s' hc' hni))).trans ?_
        refine ((hbj hbfjP).symm.trans
          (congrArg ψW.val (Subtype.ext ?_)))
        exact hfj.symm
      · rw [dite_eq_right hfi, dite_eq_right hfj]

include hij hc' hc hni in
/-- The constrained lifted even sum reindexes along the open
push. -/
theorem sum_even_open {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (a₀ : Fin k)
    (hbndW : genBoundarySubsetMatches W
      (liftSubsetOpen hopen s')
      (GenBoundaryState.extendPair i j st (Sum.inl a₀)
        (Sum.inl a₀)))
    (G : (Fl).EvenColouring k → ℂ) :
    (∑ ψW : (Fl).EvenColouring k,
      if genEvenBoundaryMatch (Fl)
          (GenBoundaryState.extendPair i j st (Sum.inl a₀)
            (Sum.inl a₀)) hbndW ψW then G ψW else 0) =
    ∑ ψ' : (Fg).EvenColouring k,
      if genEvenBoundaryMatch (Fl)
          (GenBoundaryState.extendPair i j st (Sum.inl a₀)
            (Sum.inl a₀)) hbndW
          (evenPushOpen hij hopen s' hc' hc hni ψ') then
        G (evenPushOpen hij hopen s' hc' hc hni ψ') else 0 := by
  calc (∑ ψW : (Fl).EvenColouring k,
      if genEvenBoundaryMatch (Fl)
          (GenBoundaryState.extendPair i j st (Sum.inl a₀)
            (Sum.inl a₀)) hbndW ψW then G ψW else 0)
      = ∑ ψW ∈ Finset.univ.image
          (evenPushOpen hij hopen s' hc' hc hni (k := k)),
          (if genEvenBoundaryMatch (Fl)
              (GenBoundaryState.extendPair i j st (Sum.inl a₀)
                (Sum.inl a₀)) hbndW ψW then G ψW else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro ψW _ hnotim
        rw [ite_eq_right (fun hmatch => hnotim ?_)]
        obtain ⟨ψ', hψ'⟩ := evenPushOpen_covers hij hopen s' hc'
          hc hni st a₀ hbndW ψW hmatch
        exact Finset.mem_image.mpr ⟨ψ', Finset.mem_univ _, hψ'⟩
    _ = ∑ ψ' : (Fg).EvenColouring k,
          (if genEvenBoundaryMatch (Fl)
              (GenBoundaryState.extendPair i j st (Sum.inl a₀)
                (Sum.inl a₀)) hbndW
              (evenPushOpen hij hopen s' hc' hc hni ψ') then
            G (evenPushOpen hij hopen s' hc' hc hni ψ') else 0)
        := Finset.sum_image (fun x _ y _ hxy =>
            evenPushOpen_injective hij hopen s' hc' hc hni hxy)

end OpenEngine

/-! ### The open per-subset master -/

section OpenMaster

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))

end OpenMaster

end EdgeSubset

end RS
