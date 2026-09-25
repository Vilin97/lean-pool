/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StarExplode
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc

/-!
# The star decomposition

Regluing the explosion along the matching restores the fragment
(`explode_reglue`): an induction over a list of orbit
representatives, each step being `explodeAtGluePair`, threaded
through `glueList_cons`.  Taking the representatives to be the
canonical ones gives `starDecomposition`, the accompanying paper's
"stars and closed graphs" (§3.2): every closed fragment is its star
union glued along the edge matching.
-/

namespace RS

section Decomposition

variable (W : ClosedFragment)

/-- The matching pairs of a representative list, as labels of the
explosion at `C`. -/
def repPairs (C : Finset W.Flag) (hC : CutClosed W C) :
    (l : List W.Flag) → (∀ x ∈ l, x ∈ C) →
      List ({f : W.Flag // f ∈ C} × {f : W.Flag // f ∈ C})
  | [], _ => []
  | x :: l, h =>
      (⟨x, h x List.mem_cons_self⟩,
       ⟨W.pairing x, hC x (h x List.mem_cons_self)⟩) ::
        repPairs C hC l
          (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

/-- Coverage: the orbits of the list exhaust the cut set. -/
def Covers (C : Finset W.Flag) (l : List W.Flag) : Prop :=
  ∀ g ∈ C, ∃ x ∈ l, g = x ∨ g = W.pairing x

/-- The tail of a representative list covers the shrunken cut
set, provided the head's orbit is disjoint from the tail's
pairs (from well-formedness). -/
theorem covers_tail {C : Finset W.Flag} {x : W.Flag}
    {l : List W.Flag} (hcov : Covers W C (x :: l))
    (hdisj : ∀ y ∈ l, y ≠ x ∧ y ≠ W.pairing x ∧
      W.pairing y ≠ x ∧ W.pairing y ≠ W.pairing x) :
    Covers W (cutErase W C x) l := by
  intro g hg
  rw [mem_cutErase] at hg
  obtain ⟨hgC, hgx, hgpx⟩ := hg
  obtain ⟨y, hy, hcase⟩ := hcov g hgC
  rcases List.mem_cons.mp hy with rfl | hyl
  · rcases hcase with rfl | rfl
    · exact absurd rfl hgx
    · exact absurd rfl hgpx
  · exact ⟨y, hyl, hcase⟩

/-- Membership in the flattened matching pairs: the orbits of the
list. -/
theorem mem_repPairs_flat (C : Finset W.Flag)
    (hC : CutClosed W C) :
    ∀ (l : List W.Flag) (h : ∀ x ∈ l, x ∈ C)
      (z : {f : W.Flag // f ∈ C}),
      z ∈ (repPairs W C hC l h).flatMap
          (fun p => [p.1, p.2]) ↔
        ∃ y ∈ l, z.val = y ∨ z.val = W.pairing y
  | [], _, z => by
    simp [repPairs]
  | x :: l, h, z => by
    simp only [repPairs, List.flatMap_cons, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rw [mem_repPairs_flat C hC l _ z]
    constructor
    · rintro ((rfl | rfl) | ⟨y, hy, hcase⟩)
      · exact ⟨x, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨x, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨y, Or.inr hy, hcase⟩
    · rintro ⟨y, rfl | hyl, hcase⟩
      · rcases hcase with hv | hv
        · exact Or.inl (Or.inl (Subtype.ext hv))
        · exact Or.inl (Or.inr (Subtype.ext hv))
      · exact Or.inr ⟨y, hyl, hcase⟩

/-- No label survives a covering matching. -/
theorem repPairs_surv_isEmpty (C : Finset W.Flag)
    (hC : CutClosed W C) (l : List W.Flag)
    (h : ∀ x ∈ l, x ∈ C) (hcov : Covers W C l) :
    IsEmpty (Fragment.FoldSurviving {f : W.Flag // f ∈ C}
      (repPairs W C hC l h)) := by
  refine ⟨fun s => ?_⟩
  obtain ⟨⟨g, hgC⟩, hprop⟩ := s
  have hmem := (forall_ne_iff_not_mem_flat _ _).mp hprop
  refine hmem ?_
  rw [mem_repPairs_flat]
  exact hcov g hgC

/-- The coerced matching tail is the matching of the shrunken cut
set, through the step label equivalence. -/
theorem coerce_repPairs (C : Finset W.Flag)
    (hC : CutClosed W C) (x : W.Flag) (hx : x ∈ C) :
    ∀ (l : List W.Flag) (h : ∀ y ∈ l, y ∈ C)
      (h' : ∀ y ∈ l, y ∈ cutErase W C x)
      (hsep : Fragment.PairsSep (stepLabelI W C x hx)
        (stepLabelJ W C hC x hx) (repPairs W C hC l h)),
      Fragment.coercePairsList (stepLabelI W C x hx)
          (stepLabelJ W C hC x hx) (repPairs W C hC l h) hsep =
        Fragment.mapPairs (stepLabelEquiv W C hC x hx)
          (repPairs W (cutErase W C x)
            (cutErase_closed W C hC x) l h')
  | [], _, _, _ => rfl
  | y :: l, h, h', hsep => by
    simp only [repPairs, Fragment.coercePairsList,
      Fragment.mapPairs, List.map_cons]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (coerce_repPairs C hC x hx l _ _ _)
    · exact Subtype.ext (Subtype.ext rfl)
    · exact Subtype.ext (Subtype.ext rfl)

/-- The pair of a list member is in the matching. -/
theorem repPairs_mem (C : Finset W.Flag) (hC : CutClosed W C) :
    ∀ (l : List W.Flag) (h : ∀ x ∈ l, x ∈ C) {y : W.Flag}
      (hy : y ∈ l),
      (⟨y, h y hy⟩,
        (⟨W.pairing y, hC y (h y hy)⟩ :
          {f : W.Flag // f ∈ C})) ∈ repPairs W C hC l h
  | [], _, _, hy => absurd hy (List.not_mem_nil)
  | a :: l, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hyl
    · exact List.mem_cons_self
    · exact List.mem_cons.mpr
        (Or.inr (repPairs_mem C hC l _ hyl))

/-- The head-orbit disjointness facts, from well-formedness. -/
theorem repPairs_head_disj {C : Finset W.Flag}
    {hC : CutClosed W C} {x : W.Flag} {l : List W.Flag}
    {h : ∀ y ∈ x :: l, y ∈ C}
    (wf : Fragment.PairsWF (repPairs W C hC (x :: l) h)) :
    ∀ y ∈ l, y ≠ x ∧ y ≠ W.pairing x ∧
      W.pairing y ≠ x ∧ W.pairing y ≠ W.pairing x := by
  intro y hy
  have hmem := repPairs_mem W C hC l
    (fun z hz => h z (List.mem_cons.mpr (Or.inr hz))) hy
  have hy1 := wf.sep _ hmem
  obtain ⟨h1, h2, h3, h4⟩ := hy1
  exact ⟨fun he => h1 (Subtype.ext he),
    fun he => h2 (Subtype.ext he),
    fun he => h3 (Subtype.ext he),
    fun he => h4 (Subtype.ext he)⟩

/-- Well-formedness transports along mapped pairs. -/
theorem mapPairs_wf_of {α β : Type} (e : α ≃ β)
    {ps : List (α × α)}
    (h : Fragment.PairsWF (Fragment.mapPairs e ps)) :
    Fragment.PairsWF ps := by
  have h2 := Fragment.mapPairs_wf e.symm _ h
  have h3 : Fragment.mapPairs e.symm (Fragment.mapPairs e ps) =
      ps := by
    rw [show Fragment.mapPairs e ps =
      Fragment.mapPairs e.symm.symm ps by
        rw [_root_.Equiv.symm_symm]]
    exact mapPairs_symm_cancel e.symm ps
  rwa [h3] at h2

/-- The explosion at a memberless cut set is the fragment,
generalized over the cut set. -/
noncomputable def explodeAtNotMem (C : Finset W.Flag)
    (hC : CutClosed W C) (hne : ∀ f, f ∉ C)
    (e0 : Fin 0 ≃ {f : W.Flag // f ∈ C}) :
    (W.relabel e0).Equiv (explodeAt W C hC) :=
  haveI : IsEmpty {f : W.Flag // f ∈ C} :=
    ⟨fun s => hne s.val s.prop⟩
  { flagEquiv := (_root_.Equiv.sumEmpty W.Flag
      {f : W.Flag // f ∈ C}).symm
    vertexEquiv := _root_.Equiv.refl W.Vertex
    attach_comm := fun f => by
      change (explodeAt W C hC).attach (Sum.inl f) =
        ((W.attach f).map id _).map (_root_.Equiv.refl _) id
      rw [ClosedFragment.attach_eq_vertexOf W f]
      rfl
    pairing_comm := fun f => by
      change (Sum.inl (W.pairing f) :
        W.Flag ⊕ {f : W.Flag // f ∈ C}) =
        (explodeAt W C hC).pairing (Sum.inl f)
      have hp : ∀ g : W.Flag, (explodeAt W C hC).pairing
          (Sum.inl g) = Sum.inl (W.pairing g) := fun g => by
        change (if h : g ∈ C then
          (Sum.inr ⟨g, h⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
          else Sum.inl (W.pairing g)) = Sum.inl (W.pairing g)
        exact dite_eq_right (hne g)
      rw [hp f]
    circles_eq := rfl }

/-- **The regluing induction**: gluing the covering matching in
the explosion restores the fragment. -/
theorem explode_reglue :
    ∀ (l : List W.Flag) (C : Finset W.Flag)
      (hC : CutClosed W C) (h : ∀ x ∈ l, x ∈ C)
      (_hcov : Covers W C l)
      (wf : Fragment.PairsWF (repPairs W C hC l h))
      (e : Fin 0 ≃ Fragment.FoldSurviving
        {f : W.Flag // f ∈ C} (repPairs W C hC l h)),
      Nonempty ((Fragment.glueList (explodeAt W C hC)
          (repPairs W C hC l h) wf).Equiv (W.relabel e))
  | [], C, hC, h, hcov, wf, e => by
    have hne : ∀ f, f ∉ C := fun f hf => by
      obtain ⟨x, hx, _⟩ := hcov f hf
      exact absurd hx (List.not_mem_nil)
    have : IsEmpty {f : W.Flag // f ∈ C} :=
      ⟨fun s => hne s.val s.prop⟩
    refine ⟨?_⟩
    change ((explodeAt W C hC).relabel
      Fragment.foldSurvivingNilEquiv.symm).Equiv (W.relabel e)
    refine (Fragment.Equiv.relabelCongr
      (explodeAtNotMem W C hC hne
        (_root_.Equiv.equivOfIsEmpty (Fin 0) _)).symm
      Fragment.foldSurvivingNilEquiv.symm).trans ?_
    refine (Fragment.Equiv.relabelTrans W _ _).trans ?_
    exact Fragment.Equiv.relabelEq W
      (_root_.Equiv.ext (fun i => i.elim0))
  | x :: l, C, hC, h, hcov, wf, e => by
    have hx : x ∈ C := h x List.mem_cons_self
    have hdisj := repPairs_head_disj W wf
    have htail : ∀ y ∈ l, y ∈ C :=
      fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
    have h' : ∀ y ∈ l, y ∈ cutErase W C x := fun y hy =>
      (mem_cutErase W C x).mpr
        ⟨htail y hy, (hdisj y hy).1, (hdisj y hy).2.1⟩
    have hcov' : Covers W (cutErase W C x) l :=
      covers_tail W hcov hdisj
    -- the coerced tail is the shrunken matching
    have hco := coerce_repPairs W C hC x hx l htail h' wf.sep
    have wfco : Fragment.PairsWF
        (Fragment.coercePairsList (stepLabelI W C x hx)
          (stepLabelJ W C hC x hx)
          (repPairs W C hC l htail) wf.sep) :=
      Fragment.coercePairsList_wf _ _ _ wf.tail wf.sep
    have wf' : Fragment.PairsWF
        (repPairs W (cutErase W C x)
          (cutErase_closed W C hC x) l h') :=
      mapPairs_wf_of (stepLabelEquiv W C hC x hx)
        (hco ▸ wfco)
    have : IsEmpty (Fragment.FoldSurviving
        {f : W.Flag // f ∈ cutErase W C x}
        (repPairs W (cutErase W C x)
          (cutErase_closed W C hC x) l h')) :=
      repPairs_surv_isEmpty W (cutErase W C x)
        (cutErase_closed W C hC x) l h' hcov'
    obtain ⟨IH⟩ := explode_reglue l (cutErase W C x)
      (cutErase_closed W C hC x) h' hcov' wf'
      (_root_.Equiv.equivOfIsEmpty (Fin 0) _)
    refine ⟨?_⟩
    change (Fragment.glueList (explodeAt W C hC)
      ((⟨x, hx⟩, ⟨W.pairing x, hC x hx⟩) ::
        repPairs W C hC l htail)
      wf).Equiv (W.relabel e)
    rw [Fragment.glueList_cons (explodeAt W C hC)
      (⟨x, hx⟩, ⟨W.pairing x, hC x hx⟩)
      (repPairs W C hC l htail) wf]
    -- transport the inner fold across the one-step equivalence
    have C1 := Fragment.glueListCongr
      (explodeAtGluePair W C hC x hx) _ wfco
    -- bridge the coerced pairs to the mapped shrunken matching
    have C2 := Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv
        ((explodeAt W (cutErase W C x)
          (cutErase_closed W C hC x)).relabel
            (stepLabelEquiv W C hC x hx))
        hco wfco
        (Fragment.mapPairs_wf (stepLabelEquiv W C hC x hx) _
          wf')
        (List.Perm.of_eq hco))
    -- pull the step relabel out
    have C3 := Fragment.glueListRelabel
      (explodeAt W (cutErase W C x)
        (cutErase_closed W C hC x))
      (stepLabelEquiv W C hC x hx)
      (repPairs W (cutErase W C x)
        (cutErase_closed W C hC x) l h') wf'
    -- assemble: the inner chain, fully spelled
    have K : (Fragment.glueList
        ((explodeAt W C hC).gluePair (stepLabelI W C x hx)
          (stepLabelJ W C hC x hx)
          (stepLabel_ne W C hC x hx))
        (Fragment.coercePairsList (stepLabelI W C x hx)
          (stepLabelJ W C hC x hx)
          (repPairs W C hC l htail) wf.sep) wfco).Equiv
        (W.relabel
          (((_root_.Equiv.equivOfIsEmpty (Fin 0)
              (Fragment.FoldSurviving
                {f : W.Flag // f ∈ cutErase W C x}
                (repPairs W (cutErase W C x)
                  (cutErase_closed W C hC x) l h'))).trans
            (Fragment.foldSurvivingMapEquiv
              (stepLabelEquiv W C hC x hx)
              (repPairs W (cutErase W C x)
                (cutErase_closed W C hC x) l h'))).trans
            (Fragment.foldSurvivingPermEquiv
              (List.Perm.of_eq hco)).symm)) :=
      C1.trans (C2.trans
        ((Fragment.Equiv.relabelCongr
          (C3.trans
            ((Fragment.Equiv.relabelCongr IH
              (Fragment.foldSurvivingMapEquiv
                (stepLabelEquiv W C hC x hx)
                (repPairs W (cutErase W C x)
                  (cutErase_closed W C hC x) l h'))).trans
            (Fragment.Equiv.relabelTrans W _ _)))
          (Fragment.foldSurvivingPermEquiv
            (List.Perm.of_eq hco)).symm).trans
        (Fragment.Equiv.relabelTrans W _ _)))
    exact (Fragment.Equiv.relabelCongr K
      (Fragment.foldFlatten _ _ _ _)).trans
      ((Fragment.Equiv.relabelTrans W _ _).trans
        (Fragment.Equiv.relabelEq W
          (_root_.Equiv.ext (fun i => i.elim0))))

/-- Well-formedness of the matching from list distinctness and
orbit disjointness. -/
theorem repPairs_wf_of (C : Finset W.Flag) (hC : CutClosed W C) :
    ∀ (l : List W.Flag) (h : ∀ x ∈ l, x ∈ C)
      (_ : l.Nodup)
      (_ : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → x ≠ W.pairing y),
      Fragment.PairsWF (repPairs W C hC l h)
  | [], _, _, _ => List.nodup_nil
  | x :: l, h, hnodup, hdisj => by
    have htail : ∀ y ∈ l, y ∈ C :=
      fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
    change ((⟨x, _⟩, ⟨W.pairing x, _⟩) ::
      repPairs W C hC l htail).flatMap
        (fun p => [p.1, p.2]) |>.Nodup
    rw [List.flatMap_cons]
    refine List.Nodup.append ?_ ?_ ?_
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      exact fun he => W.pairing_ne x
        (congrArg Subtype.val he).symm
    · exact repPairs_wf_of C hC l htail
        (List.nodup_cons.mp hnodup).2
        (fun a ha b hb hab => hdisj a
          (List.mem_cons.mpr (Or.inr ha)) b
          (List.mem_cons.mpr (Or.inr hb)) hab)
    · intro z hz hz2
      have hz3 := (mem_repPairs_flat W C hC l htail z).mp hz2
      obtain ⟨y, hy, hcase⟩ := hz3
      have hxy : x ≠ y := fun he =>
        (List.nodup_cons.mp hnodup).1 (he ▸ hy)
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hz
      rcases hz with rfl | rfl
      · rcases hcase with hv | hv
        · exact hxy hv
        · exact hdisj x List.mem_cons_self y
            (List.mem_cons.mpr (Or.inr hy)) hxy hv
      · rcases hcase with hv | hv
        · exact hdisj y (List.mem_cons.mpr (Or.inr hy)) x
            List.mem_cons_self (fun he => hxy he.symm) hv.symm
        · exact hxy (by
            have h5 : W.pairing x = W.pairing y := hv
            have := congrArg W.pairing h5
            rwa [W.pairing_invol, W.pairing_invol] at this)

/-- The canonical orbit representatives: flags enumerated below
their partners. -/
noncomputable def canonicalReps : List W.Flag :=
  (Finset.univ.filter (fun f =>
    (Fintype.equivFin W.Flag f : ℕ) <
      Fintype.equivFin W.Flag (W.pairing f))).toList

/-- A flag represents its edge exactly when it is the lower of the
two under the enumeration. -/
theorem mem_canonicalReps {f : W.Flag} :
    f ∈ canonicalReps W ↔
      (Fintype.equivFin W.Flag f : ℕ) <
        Fintype.equivFin W.Flag (W.pairing f) := by
  unfold canonicalReps
  rw [Finset.mem_toList, Finset.mem_filter]
  simp

/-- The canonical representatives cover everything. -/
theorem canonicalReps_covers :
    Covers W Finset.univ (canonicalReps W) := by
  intro g _
  have hne : (Fintype.equivFin W.Flag g : ℕ) ≠
      Fintype.equivFin W.Flag (W.pairing g) := fun he =>
    W.pairing_ne g (((Fintype.equivFin W.Flag).injective
      (Fin.ext he)).symm)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨g, (mem_canonicalReps W).mpr hlt, Or.inl rfl⟩
  · refine ⟨W.pairing g, (mem_canonicalReps W).mpr ?_,
      Or.inr (W.pairing_invol g).symm⟩
    rw [W.pairing_invol]
    exact hgt

/-- The canonical representatives are orbit-disjoint. -/
theorem canonicalReps_disj :
    ∀ x ∈ canonicalReps W, ∀ y ∈ canonicalReps W,
      x ≠ y → x ≠ W.pairing y := by
  intro x hx y hy _ he
  have h1 := (mem_canonicalReps W).mp hx
  have h2 := (mem_canonicalReps W).mp hy
  rw [he] at h1
  rw [W.pairing_invol] at h1
  omega

/-- The full cut is pairing-closed. -/
theorem fullCut_closed : CutClosed W Finset.univ :=
  fun _ _ => Finset.mem_univ _

/-- The canonical matching is well-formed. -/
theorem canonicalReps_wf :
    Fragment.PairsWF (repPairs W Finset.univ (fullCut_closed W)
      (canonicalReps W) (fun _ _ => Finset.mem_univ _)) :=
  repPairs_wf_of W Finset.univ (fullCut_closed W)
    (canonicalReps W) _ (Finset.nodup_toList _)
    (canonicalReps_disj W)

/-- Regluing the whole matching leaves no surviving label: the
decomposition closes the fragment. -/
instance canonical_surv_isEmpty :
    IsEmpty (Fragment.FoldSurviving
      {f : W.Flag // f ∈ (Finset.univ : Finset W.Flag)}
      (repPairs W Finset.univ (fullCut_closed W)
        (canonicalReps W) (fun _ _ => Finset.mem_univ _))) :=
  repPairs_surv_isEmpty W Finset.univ (fullCut_closed W)
    (canonicalReps W) _ (canonicalReps_covers W)

/-- **The star decomposition** (accompanying paper §3.2, "stars and closed
graphs"): every closed fragment is its star union, reglued along
the canonical edge matching. -/
theorem starDecomposition (W : ClosedFragment) :
    Nonempty ((Fragment.glueList
        (explodeAt W Finset.univ (fullCut_closed W))
        (repPairs W Finset.univ (fullCut_closed W)
          (canonicalReps W) (fun _ _ => Finset.mem_univ _))
        (canonicalReps_wf W)).Equiv
      (W.relabel (_root_.Equiv.equivOfIsEmpty (Fin 0) _))) :=
  explode_reglue W (canonicalReps W) Finset.univ
    (fullCut_closed W) (fun _ _ => Finset.mem_univ _)
    (canonicalReps_covers W) (canonicalReps_wf W) _

end Decomposition

end RS
