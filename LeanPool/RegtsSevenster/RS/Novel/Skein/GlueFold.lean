/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.PairDisjoint
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueAmbient

/-!
# Fold-and-reorder theory for iterated single-pair gluing

Iterated single-pair gluing over a list of pairs, with a
well-formedness predicate (all 2n components pairwise distinct) and
a reorder theorem: the result is invariant under permutation of the
pair list, up to fragment equivalence composed with the canonical
relabelling.
-/

namespace RS

namespace Fragment

variable {α : Type}

/-! ### Well-formedness of pair lists -/

/-- All 2n components of a list of pairs are pairwise distinct. -/
def PairsWF (ps : List (α × α)) : Prop :=
  (ps.flatMap (fun p => [p.1, p.2])).Nodup

/-- The empty list is trivially well-formed. -/
theorem PairsWF.nil : PairsWF (α := α) [] := List.nodup_nil

/-- The components of the head pair are distinct. -/
theorem PairsWF.head_ne {p : α × α} {ps : List (α × α)}
    (h : PairsWF (p :: ps)) : p.1 ≠ p.2 := by
  unfold PairsWF at h
  rw [List.flatMap_cons] at h
  have h1 := (List.nodup_append.mp h).1
  rw [List.nodup_cons] at h1
  intro heq
  exact h1.1 (heq ▸ List.mem_cons_self)

/-- The tail of a well-formed pair list is well-formed. -/
theorem PairsWF.tail {p : α × α} {ps : List (α × α)}
    (h : PairsWF (p :: ps)) : PairsWF ps := by
  unfold PairsWF at h ⊢
  rw [List.flatMap_cons] at h
  exact (List.nodup_append.mp h).2.1

/-- The head pair of a well-formed list shares no label with any
pair of the tail. -/
theorem PairsWF.head_disjoint_of {i j : α} {ps : List (α × α)}
    (h : PairsWF ((i, j) :: ps)) (q : α × α) (hq : q ∈ ps) :
    PairDisjoint q (i, j) := by
  unfold PairsWF at h
  rw [List.flatMap_cons] at h
  have hnd := List.nodup_append.mp h
  have hmem1 : q.1 ∈ ps.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨q, hq, List.mem_cons_self⟩
  have hmem2 : q.2 ∈ ps.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨q, hq, List.mem_cons.mpr (Or.inr List.mem_cons_self)⟩
  refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
  · exact (hnd.2.2 i List.mem_cons_self q.1 (heq ▸ hmem1)).symm heq
  · exact (hnd.2.2 j (List.mem_cons.mpr (Or.inr List.mem_cons_self)) q.1 (heq ▸
    hmem1)).symm heq
  · exact (hnd.2.2 i List.mem_cons_self q.2 (heq ▸ hmem2)).symm heq
  · exact (hnd.2.2 j (List.mem_cons.mpr (Or.inr List.mem_cons_self)) q.2 (heq ▸
    hmem2)).symm heq

/-- Well-formedness is preserved by permutation of the pair list. -/
theorem PairsWF.perm {ps qs : List (α × α)} (h : PairsWF ps)
    (hperm : ps.Perm qs) : PairsWF qs := by
  unfold PairsWF at h ⊢
  exact (hperm.flatMap (fun _ _ => List.Perm.refl _)).nodup_iff.mp h

/-! ### The flat surviving subtype -/

/-- The labels surviving all glues in a pair list: those not
appearing as any component of any pair. -/
def FoldSurviving (α : Type) (ps : List (α × α)) : Type :=
  {x : α // ∀ p ∈ ps, x ≠ p.1 ∧ x ≠ p.2}

/-- The vacuous surviving equivalence for the empty list. -/
def foldSurvivingNilEquiv : FoldSurviving α [] ≃ α where
  toFun x := x.val
  invFun x := ⟨x, fun _ h => absurd h List.not_mem_nil⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The surviving-set equivalence induced by a permutation of pairs:
the membership condition is ∀-quantified over ∈, so a permutation
preserving membership gives an equivalence. -/
def foldSurvivingPermEquiv {ps qs : List (α × α)}
    (hperm : ps.Perm qs) :
    FoldSurviving α ps ≃ FoldSurviving α qs where
  toFun x := ⟨x.val, fun p hp => x.prop p (hperm.mem_iff.mpr hp)⟩
  invFun x := ⟨x.val, fun p hp => x.prop p (hperm.mem_iff.mp hp)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-! ### Coercing tail pairs into the surviving-label subtype -/

/-- The separation hypothesis for coercing pairs. -/
abbrev PairsSep (i j : α) (ps : List (α × α)) : Prop :=
  ∀ q ∈ ps, PairDisjoint q (i, j)

/-- Extract the separation hypothesis from PairsWF. -/
theorem PairsWF.sep {i j : α} {ps : List (α × α)}
    (h : PairsWF ((i, j) :: ps)) : PairsSep i j ps :=
  h.head_disjoint_of

/-- Coerce a well-formed tail into pairs of surviving labels. -/
def coercePairsList (i j : α) :
    (ps : List (α × α)) →
    PairsSep i j ps →
    List (SurvivingLabel α i j × SurvivingLabel α i j)
  | [], _ => []
  | q :: ps, h =>
    let hq := h q List.mem_cons_self
    (⟨q.1, hq.fst_ne_fst, hq.fst_ne_snd⟩,
      ⟨q.2, hq.snd_ne_fst, hq.snd_ne_snd⟩) ::
      coercePairsList i j ps (fun r hr => h r (List.mem_cons.mpr (Or.inr hr)))

/-- Length of `coercePairsList` equals the original list length. -/
theorem coercePairsList_length (i j : α) :
    ∀ (ps : List (α × α)) (h : PairsSep i j ps),
    (coercePairsList i j ps h).length = ps.length
  | [], _ => rfl
  | _ :: ps, _ => congrArg Nat.succ (coercePairsList_length i j ps _)

/-- The val-projection of the flattened coerced list equals the
original flattened list. -/
theorem coercePairsList_flatMap_map_val (i j : α) :
    ∀ (ps : List (α × α)) (h : PairsSep i j ps),
    ((coercePairsList i j ps h).flatMap (fun r => [r.1, r.2])).map Subtype.val =
      ps.flatMap (fun q => [q.1, q.2])
  | [], _ => rfl
  | _ :: ps, h => by
    simp only [coercePairsList, List.flatMap_cons, List.map_append]
    exact congrArg ([_, _] ++ ·) (coercePairsList_flatMap_map_val i j ps _)

/-- Well-formedness of the coerced pairs. -/
theorem coercePairsList_wf (i j : α) (ps : List (α × α))
    (hwf : PairsWF ps) (h : PairsSep i j ps) :
    PairsWF (coercePairsList i j ps h) := by
  unfold PairsWF
  apply List.Nodup.of_map Subtype.val
  unfold PairsWF at hwf
  rw [coercePairsList_flatMap_map_val]
  exact hwf

/-- Each element of coercePairsList comes from an element of ps. -/
theorem coercePairsList_mem_of (i j : α) :
    ∀ (ps : List (α × α)) (h : PairsSep i j ps)
    (r : SurvivingLabel α i j × SurvivingLabel α i j)
    (_ : r ∈ coercePairsList i j ps h),
    ∃ q ∈ ps, r.1.val = q.1 ∧ r.2.val = q.2
  | q :: ps, h, r, hr => by
    simp only [coercePairsList] at hr
    rcases List.mem_cons.mp hr with heq | htail
    · subst heq
      exact ⟨q, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨q', hq', h1, h2⟩ := coercePairsList_mem_of i j ps _ r htail
      exact ⟨q', List.mem_cons.mpr (Or.inr hq'), h1, h2⟩

/-- Membership in coercePairsList: if q ∈ ps then the coerced version
is in coercePairsList. -/
theorem coercePairsList_mem (i j : α) :
    ∀ (ps : List (α × α)) (h : PairsSep i j ps)
    (q : α × α) (_ : q ∈ ps),
    ∃ r ∈ coercePairsList i j ps h, r.1.val = q.1 ∧ r.2.val = q.2
  | q' :: ps, h, q, hq => by
    rcases List.mem_cons.mp hq with rfl | htail
    · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨r, hr, h1, h2⟩ := coercePairsList_mem i j ps _ q htail
      exact ⟨r, List.mem_cons.mpr (Or.inr hr), h1, h2⟩

/-! ### The flattening equivalence -/

/-- The canonical equivalence between the nested surviving type
(first remove i, j from α to get SurvivingLabel; then remove
the coerced tail pairs) and the flat surviving type (remove
(i, j) :: ps at once). -/
def foldFlatten (i j : α) (ps : List (α × α))
    (h : PairsSep i j ps) :
    FoldSurviving (SurvivingLabel α i j) (coercePairsList i j ps h) ≃
      FoldSurviving α ((i, j) :: ps) where
  toFun x :=
    ⟨x.val.val, fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact ⟨x.val.prop.1, x.val.prop.2⟩
      · obtain ⟨r, hr, h1, h2⟩ := coercePairsList_mem i j ps h p hmem
        have hxr := x.prop r hr
        exact ⟨fun heq => hxr.1 (Subtype.ext (h1 ▸ heq)),
               fun heq => hxr.2 (Subtype.ext (h2 ▸ heq))⟩⟩
  invFun x :=
    ⟨⟨x.val, by
        have := x.prop (i, j) List.mem_cons_self
        exact ⟨this.1, this.2⟩⟩,
      fun r hr => by
        obtain ⟨q, hq, h1, h2⟩ := coercePairsList_mem_of i j ps h r hr
        have hxq := x.prop q (List.mem_cons.mpr (Or.inr hq))
        exact ⟨fun heq => hxq.1 (h1 ▸ congrArg Subtype.val heq),
               fun heq => hxq.2 (h2 ▸ congrArg Subtype.val heq)⟩⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-! ### The fold: iterated single-pair gluing -/

private noncomputable def glueListAux :
    (n : ℕ) → {α : Type} → (W : Fragment α) →
    (ps : List (α × α)) → PairsWF ps →
    ps.length ≤ n → Fragment (FoldSurviving α ps)
  | _, _, W, [], _, _ => W.relabel foldSurvivingNilEquiv.symm
  | n + 1, _, W, (i, j) :: ps, h, hlen =>
    have hlen' : (coercePairsList i j ps h.sep).length ≤ n := by
      rw [coercePairsList_length]
      simp only [List.length_cons] at hlen
      omega
    (glueListAux n (W.gluePair i j h.head_ne)
      (coercePairsList i j ps h.sep)
      (coercePairsList_wf i j ps h.tail h.sep)
      hlen').relabel
    (foldFlatten i j ps h.sep)

/-- Iterated single-pair gluing along a list of distinct pairs.
Glues each pair in order; the result is labelled by the elements of
α not appearing in any pair. -/
noncomputable def glueList {α : Type} (W : Fragment α)
    (ps : List (α × α)) (h : PairsWF ps) :
    Fragment (FoldSurviving α ps) :=
  glueListAux ps.length W ps h le_rfl

private theorem glueListAux_irrel :
    ∀ (n m : ℕ) {α : Type} (W : Fragment α)
    (ps : List (α × α)) (h : PairsWF ps)
    (hn : ps.length ≤ n) (hm : ps.length ≤ m),
    glueListAux n W ps h hn = glueListAux m W ps h hm
  | 0, 0, _, _, [], _, _, _ => rfl
  | 0, _ + 1, _, _, [], _, _, _ => rfl
  | _ + 1, 0, _, _, [], _, _, _ => rfl
  | _ + 1, _ + 1, _, _, [], _, _, _ => rfl
  | n + 1, m + 1, _, W, (i, j) :: ps, h, hn, hm => by
    simp only [glueListAux]
    congr 1
    exact glueListAux_irrel n m _ _ _ _ _

/-- Unfolding `glueList` at the empty list. -/
theorem glueList_nil {α : Type} (W : Fragment α) (h : PairsWF (α := α) []) :
    glueList W [] h = W.relabel foldSurvivingNilEquiv.symm := rfl

/-- Unfolding `glueList` at a cons. -/
theorem glueList_cons {α : Type} (W : Fragment α)
    (p : α × α) (ps : List (α × α)) (hp : PairsWF (p :: ps)) :
    glueList W (p :: ps) hp =
      (glueList (W.gluePair p.1 p.2 hp.head_ne)
        (coercePairsList p.1 p.2 ps hp.sep)
        (coercePairsList_wf p.1 p.2 ps hp.tail hp.sep)).relabel
      (foldFlatten p.1 p.2 ps hp.sep) := by
  change glueListAux ((p :: ps).length) W (p :: ps) hp le_rfl =
    (glueListAux ((coercePairsList p.1 p.2 ps hp.sep).length)
      (W.gluePair p.1 p.2 hp.head_ne)
      (coercePairsList p.1 p.2 ps hp.sep)
      (coercePairsList_wf p.1 p.2 ps hp.tail hp.sep) le_rfl).relabel _
  simp only [List.length_cons, glueListAux]
  congr 1
  exact glueListAux_irrel _ _ _ _ _ _ _

/-! ### Congruence: glueList respects fragment equivalence -/

private noncomputable def glueListCongr_aux
    (n : ℕ) {α : Type} {W₁ W₂ : Fragment α}
    (he : W₁.Equiv W₂)
    (ps : List (α × α)) (h : PairsWF ps)
    (hn : ps.length ≤ n) :
    (glueListAux n W₁ ps h hn).Equiv (glueListAux n W₂ ps h hn) := by
  induction n generalizing α with
  | zero =>
    match ps, h, hn with
    | [], _, _ => exact Equiv.relabelCongr he _
  | succ n ih =>
    match ps, h, hn with
    | [], _, _ => exact Equiv.relabelCongr he _
    | (i, j) :: ps, h, hlen =>
      change ((glueListAux n _ _ _ _).relabel _).Equiv
        ((glueListAux n _ _ _ _).relabel _)
      exact Equiv.relabelCongr
        (ih (Equiv.gluePairCongr he h.head_ne)
          (coercePairsList i j ps h.sep)
          (coercePairsList_wf i j ps h.tail h.sep) _)
        (foldFlatten i j ps h.sep)

/-- `glueList` respects fragment equivalence: equivalent inputs
produce equivalent outputs. -/
noncomputable def glueListCongr {α : Type}
    {W₁ W₂ : Fragment α}
    (he : W₁.Equiv W₂)
    (ps : List (α × α)) (h : PairsWF ps) :
    (glueList W₁ ps h).Equiv (glueList W₂ ps h) :=
  glueListCongr_aux ps.length he ps h le_rfl

/-! ### Relabelling commutes with the fold -/

/-- Map a pair list through an equivalence. -/
def mapPairs (e : α ≃ β) (ps : List (α × α)) : List (β × β) :=
  ps.map (Prod.map e e)

private theorem mapPairs_flatMap (e : α ≃ β) :
    ∀ (ps : List (α × α)),
    (mapPairs e ps).flatMap (fun p => [p.1, p.2]) =
      (ps.flatMap (fun q => [q.1, q.2])).map e
  | [] => rfl
  | _ :: ps => by
    simp only [mapPairs, List.map_cons, List.flatMap_cons, List.map_append,
      Prod.map, List.map_cons, List.map_nil]
    exact congrArg _ (mapPairs_flatMap e ps)

/-- Well-formedness is preserved by mapping through an equivalence. -/
theorem mapPairs_wf (e : α ≃ β) (ps : List (α × α))
    (hp : PairsWF ps) : PairsWF (mapPairs e ps) := by
  unfold PairsWF
  rw [mapPairs_flatMap]
  exact hp.map e.injective

/-- The canonical equivalence on FoldSurviving induced by a
label equivalence. -/
def foldSurvivingMapEquiv (e : α ≃ β) (ps : List (α × α)) :
    FoldSurviving α ps ≃ FoldSurviving β (mapPairs e ps) where
  toFun x := ⟨e x.val, fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨fun h => (x.prop q hq).1 (e.injective (show e x.val = e q.1 from h)),
           fun h => (x.prop q hq).2 (e.injective (show e x.val = e q.2
             from h))⟩⟩
  invFun y := ⟨e.symm y.val, fun p hp => by
    have h := y.prop (Prod.map e e p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simp only [Prod.map] at h
    exact ⟨fun heq => h.1 ((e.apply_symm_apply y.val).symm.trans (congrArg e
      heq)),
           fun heq => h.2 ((e.apply_symm_apply y.val).symm.trans (congrArg e
             heq))⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

/-- PairsSep is preserved by mapping. -/
private theorem mapPairs_sep (e : α ≃ β) (i j : α) (ps : List (α × α))
    (h : PairsSep i j ps) : PairsSep (e i) (e j) (mapPairs e ps) := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  simp only [Prod.map]
  have := h r hr
  exact ⟨fun h' => this.fst_ne_fst (e.injective h'),
    fun h' => this.fst_ne_snd (e.injective h'),
    fun h' => this.snd_ne_fst (e.injective h'),
    fun h' => this.snd_ne_snd (e.injective h')⟩

/-- The surviving-label equivalence induced by a label equiv. -/
def survLabelMapEquiv (e : α ≃ β) (i j : α) :
    SurvivingLabel α i j ≃ SurvivingLabel β (e i) (e j) where
  toFun x := ⟨e x.val, fun h => x.prop.1 (e.injective h),
                         fun h => x.prop.2 (e.injective h)⟩
  invFun y := ⟨e.symm y.val,
    fun h => y.prop.1 ((e.apply_symm_apply y.val).symm.trans (congrArg e h)),
    fun h => y.prop.2 ((e.apply_symm_apply y.val).symm.trans (congrArg e h))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

/-- The coerced mapped pairs equal the mapped coerced pairs. -/
private theorem coercePairsList_mapPairs_comm (e : α ≃ β) (i j : α) :
    ∀ (ps : List (α × α)) (hsep : PairsSep i j ps)
    (hsep' : PairsSep (e i) (e j) (mapPairs e ps)),
    coercePairsList (e i) (e j) (mapPairs e ps) hsep' =
      mapPairs (survLabelMapEquiv e i j) (coercePairsList i j ps hsep)
  | [], _, _ => rfl
  | _ :: ps, _, _ =>
    congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
      (coercePairsList_mapPairs_comm e i j ps _ _)

/-- The cast equivalence between surviving-label types differing only
by propositionally-equal indices. Identity on the underlying value. -/
private def survLabelCastEquiv (e : α ≃ β) (i j : α) :
    SurvivingLabel α (e.symm (e i)) (e.symm (e j)) ≃ SurvivingLabel α i j where
  toFun x := ⟨x.val,
    fun h => x.prop.1 (h.trans (e.symm_apply_apply i).symm),
    fun h => x.prop.2 (h.trans (e.symm_apply_apply j).symm)⟩
  invFun x := ⟨x.val,
    fun h => x.prop.1 (h.trans (e.symm_apply_apply i)),
    fun h => x.prop.2 (h.trans (e.symm_apply_apply j))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The coerced pairs after casting equal the directly coerced pairs. -/
private theorem coercePairsList_cast_eq (e : α ≃ β) (i j : α) :
    ∀ (ps : List (α × α))
    (hsep : PairsSep (e.symm (e i)) (e.symm (e j)) ps) (hsep' : PairsSep i j
      ps),
    mapPairs (survLabelCastEquiv e i j)
      (coercePairsList (e.symm (e i)) (e.symm (e j)) ps hsep) =
      coercePairsList i j ps hsep'
  | [], _, _ => rfl
  | _ :: ps, _, _ =>
    congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
      (coercePairsList_cast_eq e i j ps _ _)

/-- Composition of mapPairs. -/
private theorem mapPairs_mapPairs (f : β ≃ γ) (g : α ≃ β) :
    ∀ (xs : List (α × α)),
    mapPairs f (mapPairs g xs) = mapPairs (g.trans f) xs
  | [] => rfl
  | _ :: xs => congrArg₂ List.cons rfl (mapPairs_mapPairs f g xs)

/-- Two equivs that agree pointwise give the same mapPairs result. -/
private theorem mapPairs_congr {f g : α ≃ β}
    (h : ∀ x, f x = g x) :
    ∀ (xs : List (α × α)),
    mapPairs f xs = mapPairs g xs
  | [] => rfl
  | _ :: xs => congrArg₂ List.cons (Prod.ext (h _) (h _)) (mapPairs_congr h xs)

/-- Gluing at propositionally-equal indices and then relabelling by the
cast equivalence yields an equivalent fragment. -/
private noncomputable def gluePair_cast_equiv (W : Fragment α) (e : α ≃ β)
    (i j : α) (hij : i ≠ j) :
    let hij' : e.symm (e i) ≠ e.symm (e j) := fun h =>
      hij (e.injective (by rw [← e.apply_symm_apply (e i),
        ← e.apply_symm_apply (e j), h]))
    ((W.gluePair (e.symm (e i)) (e.symm (e j)) hij').relabel
      (survLabelCastEquiv e i j)).Equiv (W.gluePair i j hij) := by
  intro hij'
  have hbi : W.boundaryFlag (e.symm (e i)) = W.boundaryFlag i :=
    congrArg W.boundaryFlag (e.symm_apply_apply i)
  have hbj : W.boundaryFlag (e.symm (e j)) = W.boundaryFlag j :=
    congrArg W.boundaryFlag (e.symm_apply_apply j)
  -- The flag types are SurvivingFlag W (e.symm(ei))(e.symm(ej)) on both sides
  -- (relabel does not change Flag). We bridge to SurvivingFlag W i j.
  set flagE : SurvivingFlag W (e.symm (e i)) (e.symm (e j)) ≃ SurvivingFlag W i
    j :=
    ⟨fun f => ⟨f.val,
        fun h => f.prop.1 (h.trans hbi.symm),
        fun h => f.prop.2 (h.trans hbj.symm)⟩,
     fun f => ⟨f.val,
        fun h => f.prop.1 (h.trans hbi),
        fun h => f.prop.2 (h.trans hbj)⟩,
     fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
  -- Build the Equiv by cases on closed/open
  by_cases hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j
  · -- ═══════ THE PAIR IS CLOSED ═══════
    have hclosed' : W.pairing (W.boundaryFlag (e.symm (e i))) =
        W.boundaryFlag (e.symm (e j)) :=
      (congrArg W.pairing hbi).trans (hclosed.trans hbj.symm)
    -- After gluePair_eq_closed, both sides are gluePairClosed
    -- LHS fragment = (gluePairClosed W (e.symm(ei)) (e.symm(ej))
    --   hclosed').relabel castE
    -- RHS fragment = gluePairClosed W i j hclosed
    -- Both have Flag = SurvivingFlag W ... and Vertex = W.Vertex
    have hlhs_eq := gluePair_eq_closed hij' hclosed'
    have hrhs_eq := gluePair_eq_closed hij hclosed
    rw [hlhs_eq, hrhs_eq]
    refine ⟨flagE, _root_.Equiv.refl _, fun f => ?_, fun f => ?_, rfl⟩
    · -- attach_comm: both sides depend on W.attach f.val
      change glueAttach W i j (flagE f) =
        ((glueAttach W (e.symm (e i)) (e.symm (e j)) f).map id
          (survLabelCastEquiv e i j)).map (_root_.Equiv.refl _) id
      rcases ha : W.attach f.val with v | ℓ
      · have h1 : glueAttach W i j (flagE f) = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        have h2 : glueAttach W (e.symm (e i)) (e.symm (e j)) f = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        rw [h1, h2]; rfl
      · have h1 : ∃ p : SurvivingLabel α i j,
            glueAttach W i j (flagE f) = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        have h2 : ∃ p : SurvivingLabel α (e.symm (e i)) (e.symm (e j)),
            glueAttach W (e.symm (e i)) (e.symm (e j)) f = Sum.inr p ∧ p.val = ℓ
              := by
          exact exists_glueAttach_inr _ ha
        obtain ⟨p1, hp1, hv1⟩ := h1
        obtain ⟨p2, hp2, hv2⟩ := h2
        rw [hp1, hp2]
        exact congrArg Sum.inr (Subtype.ext (hv1.trans hv2.symm))
    · -- pairing_comm
      exact Subtype.ext rfl
  · -- ═══════ THE PAIR IS OPEN ═══════
    have hopen' : W.pairing (W.boundaryFlag (e.symm (e i))) ≠
        W.boundaryFlag (e.symm (e j)) :=
      fun h => hclosed ((congrArg W.pairing hbi).symm.trans (h.trans hbj))
    have hlhs_eq := gluePair_eq_open hij' hopen'
    have hrhs_eq := gluePair_eq_open hij hclosed
    rw [hlhs_eq, hrhs_eq]
    refine ⟨flagE, _root_.Equiv.refl _, fun f => ?_, fun f => ?_, rfl⟩
    · -- attach_comm (same as closed case)
      change glueAttach W i j (flagE f) =
        ((glueAttach W (e.symm (e i)) (e.symm (e j)) f).map id
          (survLabelCastEquiv e i j)).map (_root_.Equiv.refl _) id
      rcases ha : W.attach f.val with v | ℓ
      · have h1 : glueAttach W i j (flagE f) = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        have h2 : glueAttach W (e.symm (e i)) (e.symm (e j)) f = Sum.inl v := by
          exact (glueAttach_inl_iff _ v).mpr ha
        rw [h1, h2]; rfl
      · have h1 : ∃ p : SurvivingLabel α i j,
            glueAttach W i j (flagE f) = Sum.inr p ∧ p.val = ℓ := by
          exact exists_glueAttach_inr _ ha
        have h2 : ∃ p : SurvivingLabel α (e.symm (e i)) (e.symm (e j)),
            glueAttach W (e.symm (e i)) (e.symm (e j)) f = Sum.inr p ∧ p.val = ℓ
              := by
          exact exists_glueAttach_inr _ ha
        obtain ⟨p1, hp1, hv1⟩ := h1
        obtain ⟨p2, hp2, hv2⟩ := h2
        rw [hp1, hp2]
        exact congrArg Sum.inr (Subtype.ext (hv1.trans hv2.symm))
    · -- pairing_comm for open case (rewire)
      change flagE (rewire hopen' f) = rewire hclosed (flagE f)
      unfold rewire
      split
      · rename_i hfi
        have hfi' : W.pairing (flagE f).val = W.boundaryFlag i := by
          change W.pairing f.val = W.boundaryFlag i; rw [← hbi]; exact hfi
        rw [dite_eq_left hfi']
        exact Subtype.ext (congrArg W.pairing hbj)
      · rename_i hfi
        have hfi' : ¬(W.pairing (flagE f).val = W.boundaryFlag i) := by
          change ¬(W.pairing f.val = W.boundaryFlag i); rw [← hbi]; exact hfi
        rw [dite_eq_right hfi']
        split
        · rename_i hfj
          have hfj' : W.pairing (flagE f).val = W.boundaryFlag j := by
            change W.pairing f.val = W.boundaryFlag j; rw [← hbj]; exact hfj
          rw [dite_eq_left hfj']
          exact Subtype.ext (congrArg W.pairing hbi)
        · rename_i hfj
          have hfj' : ¬(W.pairing (flagE f).val = W.boundaryFlag j) := by
            change ¬(W.pairing f.val = W.boundaryFlag j); rw [← hbj]; exact hfj
          rw [dite_eq_right hfj']
          exact Subtype.ext rfl

/-- Casting a `glueList` result along a list equality: relabelling
by the induced `foldSurvivingPermEquiv` bridges the type change. -/
noncomputable def glueListEqEquiv {α : Type} (W : Fragment α)
    {ps qs : List (α × α)} (h : ps = qs) (hp : PairsWF ps) (hq : PairsWF qs)
    (hperm : ps.Perm qs) :
    ((glueList W ps hp).relabel (foldSurvivingPermEquiv hperm)).Equiv
      (glueList W qs hq) := by
  subst h; exact Equiv.relabelRefl _

/-- Iterated gluing commutes with relabelling (existence). -/
private theorem nonempty_glueList_relabel_aux (n : ℕ) :
    ∀ {α β : Type} (W : Fragment α) (e : α ≃ β)
    (ps : List (α × α)) (hp : PairsWF ps)
    (_ : ps.length ≤ n),
    Nonempty ((glueList (W.relabel e) (mapPairs e ps) (mapPairs_wf e ps
      hp)).Equiv
      ((glueList W ps hp).relabel (foldSurvivingMapEquiv e ps))) := by
  induction n with
  -- ═══════ n = 0: NO PAIRS LEFT TO GLUE ═══════
  | zero =>
    intro α β W e ps hp hlen
    have hnil : ps = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    change Nonempty (((W.relabel e).relabel (foldSurvivingNilEquiv (α
      := β)).symm).Equiv
      ((W.relabel (foldSurvivingNilEquiv (α := α)).symm).relabel
        (foldSurvivingMapEquiv e [])))
    have heq : e.trans (foldSurvivingNilEquiv (α := β)).symm =
        (foldSurvivingNilEquiv (α := α)).symm.trans (foldSurvivingMapEquiv e [])
          :=
      _root_.Equiv.ext (fun _ => Subtype.ext rfl)
    exact ⟨(Equiv.relabelTrans W e (foldSurvivingNilEquiv (α := β)).symm).trans
      (heq ▸ (Equiv.relabelTrans W (foldSurvivingNilEquiv (α := α)).symm
        (foldSurvivingMapEquiv e [])).symm)⟩
  -- ═══════ n + 1: PEEL THE HEAD PAIR ═══════
  | succ n ih =>
    intro α β W e ps hp hlen
    match ps, hp, hlen with
    -- ═══════ The list is empty anyway ═══════
    | [], _, _ =>
      change Nonempty (((W.relabel e).relabel (foldSurvivingNilEquiv (α
        := β)).symm).Equiv
        ((W.relabel (foldSurvivingNilEquiv (α := α)).symm).relabel
          (foldSurvivingMapEquiv e [])))
      have heq : e.trans (foldSurvivingNilEquiv (α := β)).symm =
          (foldSurvivingNilEquiv (α := α)).symm.trans (foldSurvivingMapEquiv e
            []) :=
        _root_.Equiv.ext (fun _ => Subtype.ext rfl)
      exact ⟨(Equiv.relabelTrans W e (foldSurvivingNilEquiv (α
        := β)).symm).trans
        (heq ▸ (Equiv.relabelTrans W (foldSurvivingNilEquiv (α := α)).symm
          (foldSurvivingMapEquiv e [])).symm)⟩
    -- ═══════ Glue the head, recurse on the tail at the
    -- surviving-label type ═══════
    | (i, j) :: ps, hp, hlen =>
      have hij' := hp.head_ne
      -- Inner type bookkeeping
      have hij_inner : e.symm (e i) ≠ e.symm (e j) := fun h =>
        hij' (e.injective (by rw [← e.apply_symm_apply (e i),
          ← e.apply_symm_apply (e j), h]))
      have hsep' : PairsSep (e.symm (e i)) (e.symm (e j)) ps := by
        intro q hq; have := hp.sep q hq
        exact ⟨fun h => this.fst_ne_fst (h.trans (e.symm_apply_apply i)),
               fun h => this.fst_ne_snd (h.trans (e.symm_apply_apply j)),
               fun h => this.snd_ne_fst (h.trans (e.symm_apply_apply i)),
               fun h => this.snd_ne_snd (h.trans (e.symm_apply_apply j))⟩
      set L' := coercePairsList (e.symm (e i)) (e.symm (e j)) ps hsep'
      set L₂ := coercePairsList i j ps hp.sep
      have hlen' : L'.length ≤ n := by
        simp only [L']; rw [coercePairsList_length]
        simp only [List.length_cons] at hlen; omega
      have hwf' : PairsWF L' := coercePairsList_wf _ _ ps hp.tail hsep'
      have hwf₂ : PairsWF L₂ := coercePairsList_wf _ _ ps hp.tail hp.sep
      -- The inner relabelling (sends val x to e x)
      set σ : SurvivingLabel α (e.symm (e i)) (e.symm (e j)) ≃
          SurvivingLabel β (e i) (e j) :=
        _root_.Equiv.subtypeEquiv e (fun x => ⟨
          fun ⟨h1, h2⟩ => ⟨fun h => h1 (e.injective
            (show e x = e (e.symm (e i)) from by
              rw [e.apply_symm_apply]; exact h)),
            fun h => h2 (e.injective
            (show e x = e (e.symm (e j)) from by
              rw [e.apply_symm_apply]; exact h))⟩,
          fun ⟨h1, h2⟩ => ⟨fun h => h1
            (show e x = e i from by
              rw [← e.apply_symm_apply (e i)]; exact congrArg e h),
            fun h => h2
            (show e x = e j from by
              rw [← e.apply_symm_apply (e j)]; exact congrArg e h)⟩⟩)
      set castE := survLabelCastEquiv e i j
      -- First IH: main relabelling at the inner type
      obtain ⟨e_ih⟩ := ih (W.gluePair (e.symm (e i)) (e.symm (e j)) hij_inner)
        σ L' hwf' hlen'
      -- Second IH: cast relabelling
      have hlen₂ : L'.length ≤ n := hlen'
      obtain ⟨e_cast⟩ := ih (W.gluePair (e.symm (e i)) (e.symm (e j)) hij_inner)
        castE L' hwf' hlen₂
      -- Pair list equalities
      have hL_eq : coercePairsList (e i) (e j) (mapPairs e ps)
          (mapPairs_sep e i j ps hp.sep) =
          mapPairs σ L' := by
        -- Use coercePairsList_mapPairs_comm + coercePairsList_cast_eq +
        --   composition
        have h1 := coercePairsList_mapPairs_comm e i j ps hp.sep
          (mapPairs_sep e i j ps hp.sep)
        have h2 := (coercePairsList_cast_eq e i j ps hsep' hp.sep).symm
        rw [h1, h2, mapPairs_mapPairs]
        exact mapPairs_congr (fun x => Subtype.ext rfl) L'
      have hL_cast : mapPairs castE L' = L₂ :=
        coercePairsList_cast_eq e i j ps hsep' hp.sep
      -- Core equiv bridges
      have hgpr := gluePairRelabel W e
        (show e i ≠ e j from e.injective.ne hij')
      have hgpc := gluePair_cast_equiv W e i j hij'
      have hwf₁ := coercePairsList_wf (e i) (e j) (mapPairs e ps)
        (mapPairs_wf e ps hp.tail) (mapPairs_sep e i j ps hp.sep)
      -- Perm bridges for the list equalities
      have list_perm_fwd : (coercePairsList (e i) (e j) (mapPairs e ps)
          (mapPairs_sep e i j ps hp.sep)).Perm (mapPairs σ L') := by rw [hL_eq]
      have list_perm_cast : (mapPairs castE L').Perm L₂ := by rw [hL_cast]
      -- Key relabelling equivs to the final type
      let flattenMapEquiv : FoldSurviving (SurvivingLabel β (e i) (e j))
        (mapPairs σ L') ≃
          FoldSurviving β ((e i, e j) :: mapPairs e ps) :=
        (foldSurvivingPermEquiv list_perm_fwd).symm.trans
          (foldFlatten (e i) (e j) (mapPairs e ps) (mapPairs_sep e i j ps
            hp.sep))
      let castFlatten : FoldSurviving (SurvivingLabel α i j) (mapPairs castE L')
        ≃
          FoldSurviving β ((e i, e j) :: mapPairs e ps) :=
        (foldSurvivingPermEquiv list_perm_cast).trans
          ((foldFlatten i j ps hp.sep).trans (foldSurvivingMapEquiv e ((i, j) ::
            ps)))
      -- All composed relabellings agree on values (send ⟨⟨x,_⟩,_⟩ ↦ ⟨e x,_⟩)
      have hequivs : (foldSurvivingMapEquiv σ L').trans flattenMapEquiv =
          (foldSurvivingMapEquiv castE L').trans castFlatten :=
        _root_.Equiv.ext (fun ⟨⟨_, _⟩, _⟩ => by
          simp only [foldSurvivingMapEquiv, flattenMapEquiv,
            castFlatten, foldSurvivingPermEquiv, foldFlatten]
          exact Subtype.ext rfl)
      -- Compose the first IH + congruence at the mapPairs σ L' type
      have composed₂ := (glueListCongr hgpr (mapPairs σ L')
        (mapPairs_wf σ L' hwf')).trans e_ih
      -- Bridge from cPL label type to mapPairs σ L' label type (via
      --   glueListEqEquiv)
      have bridge_lhs := glueListEqEquiv
        ((W.relabel e).gluePair (e i) (e j) (show e i ≠ e j from e.injective.ne
          hij'))
        hL_eq hwf₁ (mapPairs_wf σ L' hwf') list_perm_fwd
      -- Bridge from mapPairs castE L' to L₂ label type
      have bridge_cast := glueListEqEquiv
        ((W.gluePair (e.symm (e i)) (e.symm (e j)) hij_inner).relabel castE)
        hL_cast (mapPairs_wf castE L' hwf') hwf₂ list_perm_cast
      -- Assemble the full equiv at the final type
      have hlhs := glueList_cons (W.relabel e) (e i, e j) (mapPairs e ps)
        (mapPairs_wf e ((i, j) :: ps) hp)
      have hrhs := glueList_cons W (i, j) ps hp
      -- The key equalities on composed equivs
      have ff_eq : (foldSurvivingPermEquiv list_perm_fwd).trans flattenMapEquiv
        =
          foldFlatten (e i) (e j) (mapPairs e ps) (mapPairs_sep e i j ps hp.sep)
            :=
        _root_.Equiv.ext (fun _ => by
          simp only [flattenMapEquiv, _root_.Equiv.trans_apply,
            _root_.Equiv.symm_apply_apply])
      -- Build the chain from the composed LHS form to the RHS
      have final :
        ((glueList ((W.relabel e).gluePair (e i) (e j) (e.injective.ne hij'))
            (coercePairsList (e i) (e j) (mapPairs e ps)
              (mapPairs_sep e i j ps hp.sep)) hwf₁).relabel
          (foldFlatten (e i) (e j) (mapPairs e ps) (mapPairs_sep e i j ps
            hp.sep))).Equiv
        ((glueList (W.gluePair i j hij') L₂ hwf₂).relabel
          ((foldFlatten i j ps hp.sep).trans
            (foldSurvivingMapEquiv e ((i, j) :: ps)))) := by
        -- Rewrite the LHS relabelling to its composed form
        suffices h :
          ((glueList ((W.relabel e).gluePair (e i) (e j) (e.injective.ne hij'))
              (coercePairsList (e i) (e j) (mapPairs e ps)
              (mapPairs_sep e i j ps hp.sep)) hwf₁).relabel
            ((foldSurvivingPermEquiv list_perm_fwd).trans
              flattenMapEquiv)).Equiv
          ((glueList (W.gluePair i j hij') L₂ hwf₂).relabel
            ((foldFlatten i j ps hp.sep).trans
              (foldSurvivingMapEquiv e ((i, j) :: ps)))) by
          exact ff_eq ▸ h
        -- Bridge via hequivs at the inner glueList level
        have mid_equiv :
            ((glueList (W.gluePair (e.symm (e i)) (e.symm (e j)) hij_inner) L'
              hwf').relabel
              ((foldSurvivingMapEquiv σ L').trans flattenMapEquiv)).Equiv
            ((glueList (W.gluePair (e.symm (e i)) (e.symm (e j)) hij_inner) L'
              hwf').relabel
              ((foldSurvivingMapEquiv castE L').trans castFlatten)) := by
          rw [hequivs]; exact Equiv.refl _
        -- LHS chain: decompose relabelling, apply bridges and IH
        have lhs_chain :=
          ((Equiv.relabelTrans (glueList _ _ hwf₁)
            (foldSurvivingPermEquiv list_perm_fwd) flattenMapEquiv).symm.trans
            (Equiv.relabelCongr (bridge_lhs.trans composed₂)
              flattenMapEquiv)).trans
            (Equiv.relabelTrans (glueList _ L' hwf')
              (foldSurvivingMapEquiv σ L') flattenMapEquiv)
        -- RHS chain: decompose through e_cast, bridge, and gluePair_cast_equiv
        have rhs_chain :=
          ((Equiv.relabelTrans (glueList _ L' hwf')
            (foldSurvivingMapEquiv castE L') castFlatten).symm.trans
            (Equiv.relabelCongr e_cast.symm castFlatten)).trans
            (((Equiv.relabelTrans (glueList _ (mapPairs castE L') (mapPairs_wf
              castE L' hwf'))
                (foldSurvivingPermEquiv list_perm_cast)
                ((foldFlatten i j ps hp.sep).trans
                  (foldSurvivingMapEquiv e ((i, j) :: ps)))).symm.trans
              (Equiv.relabelCongr bridge_cast
                ((foldFlatten i j ps hp.sep).trans
                  (foldSurvivingMapEquiv e ((i, j) :: ps))))).trans
              (Equiv.relabelCongr (glueListCongr hgpc L₂ hwf₂)
                ((foldFlatten i j ps hp.sep).trans
                  (foldSurvivingMapEquiv e ((i, j) :: ps)))))
        exact lhs_chain.trans (mid_equiv.trans rhs_chain)
      -- Fold back using glueList_cons
      have rhs_fold := (Equiv.relabelTrans
        (glueList (W.gluePair i j hij') L₂ hwf₂)
        (foldFlatten i j ps hp.sep) (foldSurvivingMapEquiv e ((i, j) ::
          ps))).symm
      exact ⟨(hlhs ▸ final).trans (rhs_fold.trans (hrhs ▸ Equiv.refl _))⟩

/-- Iterated gluing commutes with relabelling: gluing the mapped
pairs in the relabelled fragment is the original fold, relabelled
by the induced surviving-label equivalence. -/
noncomputable def glueListRelabel {α β : Type} (W : Fragment α)
    (e : α ≃ β) (ps : List (α × α)) (hp : PairsWF ps) :
    (glueList (W.relabel e) (mapPairs e ps) (mapPairs_wf e ps hp)).Equiv
      ((glueList W ps hp).relabel (foldSurvivingMapEquiv e ps)) :=
  (nonempty_glueList_relabel_aux ps.length W e ps hp le_rfl).some

/-! ### Concatenation: folding in two stages -/

/-- The separation of the second block from the first. -/
abbrev PairsSepAll (ps qs : List (α × α)) : Prop :=
  ∀ q ∈ qs, ∀ p ∈ ps, PairDisjoint q p

/-- Pairs avoiding an earlier pair list lift into its surviving
labels. -/
def liftPairs (ps : List (α × α)) :
    (qs : List (α × α)) → PairsSepAll ps qs →
    List (FoldSurviving α ps × FoldSurviving α ps)
  | [], _ => []
  | q :: qs, h =>
    (⟨q.1, fun p hp => ⟨(h q List.mem_cons_self p hp).fst_ne_fst,
        (h q List.mem_cons_self p hp).fst_ne_snd⟩⟩,
     ⟨q.2, fun p hp => ⟨(h q List.mem_cons_self p hp).snd_ne_fst,
        (h q List.mem_cons_self p hp).snd_ne_snd⟩⟩) ::
      liftPairs ps qs
        (fun r hr => h r (List.mem_cons.mpr (Or.inr hr)))

/-- The separation hypothesis of a well-formed concatenation. -/
theorem PairsWF.append_sep {ps qs : List (α × α)}
    (h : PairsWF (ps ++ qs)) : PairsSepAll ps qs := by
  intro q hq p hp
  unfold PairsWF at h
  rw [List.flatMap_append] at h
  have hd := List.disjoint_of_nodup_append h
  have hq1 : q.1 ∈ qs.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨q, hq, List.mem_cons_self⟩
  have hq2 : q.2 ∈ qs.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨q, hq,
      List.mem_cons.mpr (Or.inr List.mem_cons_self)⟩
  have hp1 : p.1 ∈ ps.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩
  have hp2 : p.2 ∈ ps.flatMap (fun r => [r.1, r.2]) :=
    List.mem_flatMap.mpr ⟨p, hp,
      List.mem_cons.mpr (Or.inr List.mem_cons_self)⟩
  exact ⟨fun he => hd hp1 (he ▸ hq1), fun he => hd hp2 (he ▸ hq1),
         fun he => hd hp1 (he ▸ hq2), fun he => hd hp2 (he ▸ hq2)⟩

/-- The first block of a well-formed concatenation. -/
theorem PairsWF.append_left {ps qs : List (α × α)}
    (h : PairsWF (ps ++ qs)) : PairsWF ps := by
  unfold PairsWF at h ⊢
  rw [List.flatMap_append] at h
  exact (List.nodup_append.mp h).1

/-- The second block of a well-formed concatenation. -/
theorem PairsWF.append_right {ps qs : List (α × α)}
    (h : PairsWF (ps ++ qs)) : PairsWF qs := by
  unfold PairsWF at h ⊢
  rw [List.flatMap_append] at h
  exact (List.nodup_append.mp h).2.1

/-- The val-projection of the flattened lifted list is the original
flattened list. -/
theorem liftPairs_flatMap_map_val (ps : List (α × α)) :
    ∀ (qs : List (α × α)) (h : PairsSepAll ps qs),
    ((liftPairs ps qs h).flatMap (fun r => [r.1, r.2])).map
        Subtype.val =
      qs.flatMap (fun q => [q.1, q.2])
  | [], _ => rfl
  | _ :: qs, h => by
    simp only [liftPairs, List.flatMap_cons, List.map_append]
    exact congrArg ([_, _] ++ ·) (liftPairs_flatMap_map_val ps qs _)

/-- The lifted second block is well-formed. -/
theorem liftPairs_wf (ps qs : List (α × α))
    (hwf : PairsWF qs) (h : PairsSepAll ps qs) :
    PairsWF (liftPairs ps qs h) := by
  have hnodup : (((liftPairs ps qs h).flatMap
      (fun r => [r.1, r.2])).map Subtype.val).Nodup := by
    rw [liftPairs_flatMap_map_val]
    exact hwf
  exact List.Nodup.of_map Subtype.val hnodup

/-- Each lifted pair comes from an original pair. -/
theorem liftPairs_mem_of (ps : List (α × α)) :
    ∀ (qs : List (α × α)) (h : PairsSepAll ps qs)
    (r : FoldSurviving α ps × FoldSurviving α ps)
    (_ : r ∈ liftPairs ps qs h),
    ∃ q ∈ qs, r.1.val = q.1 ∧ r.2.val = q.2
  | q :: qs, h, r, hr => by
    simp only [liftPairs] at hr
    rcases List.mem_cons.mp hr with heq | htail
    · subst heq
      exact ⟨q, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨q', hq', h1, h2⟩ := liftPairs_mem_of ps qs _ r htail
      exact ⟨q', List.mem_cons.mpr (Or.inr hq'), h1, h2⟩

/-- Each original pair lifts to a member. -/
theorem liftPairs_mem (ps : List (α × α)) :
    ∀ (qs : List (α × α)) (h : PairsSepAll ps qs)
    (q : α × α) (_ : q ∈ qs),
    ∃ r ∈ liftPairs ps qs h, r.1.val = q.1 ∧ r.2.val = q.2
  | q' :: qs, h, q, hq => by
    rcases List.mem_cons.mp hq with rfl | htail
    · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨r, hr, h1, h2⟩ := liftPairs_mem ps qs _ q htail
      exact ⟨r, List.mem_cons.mpr (Or.inr hr), h1, h2⟩

/-- The two-stage surviving labels flatten to the concatenation's
surviving labels. -/
def appendFlatten (ps qs : List (α × α)) (h : PairsSepAll ps qs) :
    FoldSurviving (FoldSurviving α ps) (liftPairs ps qs h) ≃
      FoldSurviving α (ps ++ qs) where
  toFun x := ⟨x.val.val, fun p hp => by
    rcases List.mem_append.mp hp with hps | hqs
    · exact x.val.prop p hps
    · obtain ⟨r, hr, h1, h2⟩ := liftPairs_mem ps qs h p hqs
      have hxr := x.prop r hr
      exact ⟨fun he => hxr.1 (Subtype.ext (h1 ▸ he)),
             fun he => hxr.2 (Subtype.ext (h2 ▸ he))⟩⟩
  invFun x := ⟨⟨x.val, fun p hp =>
      x.prop p (List.mem_append.mpr (Or.inl hp))⟩,
    fun r hr => by
      obtain ⟨q, hq, h1, h2⟩ := liftPairs_mem_of ps qs h r hr
      have hx := x.prop q (List.mem_append.mpr (Or.inr hq))
      exact ⟨fun he => hx.1 (h1 ▸ congrArg Subtype.val he),
             fun he => hx.2 (h2 ▸ congrArg Subtype.val he)⟩⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- Coercing a concatenation coerces blockwise. -/
theorem coercePairsList_append (i j : α) :
    ∀ (ps qs : List (α × α)) (h : PairsSep i j (ps ++ qs)),
    coercePairsList i j (ps ++ qs) h =
      coercePairsList i j ps
        (fun r hr => h r (List.mem_append.mpr (Or.inl hr))) ++
      coercePairsList i j qs
        (fun r hr => h r (List.mem_append.mpr (Or.inr hr)))
  | [], _, _ => rfl
  | p :: ps, qs, h => by
    simp only [List.cons_append, coercePairsList]
    exact congrArg₂ List.cons rfl (coercePairsList_append i j ps qs _)

/-- Lifting over the empty first block is mapping through the nil
equivalence. -/
private theorem liftPairs_nil_eq :
    ∀ (qs : List (α × α)) (h : PairsSepAll [] qs),
    liftPairs [] qs h = mapPairs foldSurvivingNilEquiv.symm qs
  | [], _ => rfl
  | _ :: qs, _h =>
    congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
      (liftPairs_nil_eq qs _)

/-- Lifting over a cons factors through the flattening of the
head glue. -/
private theorem liftPairs_cons_eq (i j : α) (ps : List (α × α))
    (hsep : PairsSep i j ps) :
    ∀ (qs : List (α × α)) (h : PairsSepAll ((i, j) :: ps) qs)
    (hq : PairsSep i j qs)
    (h'' : PairsSepAll (coercePairsList i j ps hsep)
      (coercePairsList i j qs hq)),
    mapPairs (foldFlatten i j ps hsep).symm
        (liftPairs ((i, j) :: ps) qs h) =
      liftPairs (coercePairsList i j ps hsep)
        (coercePairsList i j qs hq) h''
  | [], _, _, _ => rfl
  | q :: qs, _, hq, h'' => by
    simp only [liftPairs, coercePairsList, mapPairs, List.map_cons,
      Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (Subtype.ext (Subtype.ext rfl))
        (Subtype.ext (Subtype.ext rfl)))
      (liftPairs_cons_eq i j ps hsep qs _ _ _)

/-- Mapping back and forth through an equivalence cancels. -/
private theorem mapPairs_cancel {α β : Type} (e : α ≃ β) :
    ∀ ps : List (β × β), mapPairs e (mapPairs e.symm ps) = ps
  | [] => rfl
  | p :: ps => by
    simp only [mapPairs, List.map_cons, Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (e.apply_symm_apply p.1) (e.apply_symm_apply p.2))
      (mapPairs_cancel e ps)

/-- The nil case of two-stage folding. -/
private theorem nonempty_glueList_append_nil {α : Type}
    (W : Fragment α) (qs : List (α × α))
    (h : PairsWF (([] : List (α × α)) ++ qs)) :
    Nonempty ((glueList W ([] ++ qs) h).Equiv
      ((glueList (glueList W [] h.append_left)
        (liftPairs [] qs h.append_sep)
        (liftPairs_wf [] qs h.append_right h.append_sep)).relabel
        (appendFlatten [] qs h.append_sep))) := by
  have hperm : (liftPairs [] qs h.append_sep).Perm
      (mapPairs foldSurvivingNilEquiv.symm qs) := by
    rw [liftPairs_nil_eq]
  have b1 := glueListEqEquiv (glueList W [] h.append_left)
    (liftPairs_nil_eq qs h.append_sep)
    (liftPairs_wf [] qs h.append_right h.append_sep)
    (mapPairs_wf _ qs h.append_right) hperm
  have hEq : glueList (glueList W [] h.append_left)
      (mapPairs foldSurvivingNilEquiv.symm qs)
      (mapPairs_wf _ qs h.append_right) =
      glueList (W.relabel foldSurvivingNilEquiv.symm)
        (mapPairs foldSurvivingNilEquiv.symm qs)
        (mapPairs_wf _ qs h.append_right) := by
    rw [glueList_nil]
  have b3 := glueListRelabel W foldSurvivingNilEquiv.symm qs
    h.append_right
  -- assemble
  have hcomp : (foldSurvivingPermEquiv hperm).trans
      ((foldSurvivingPermEquiv hperm).symm.trans
        (appendFlatten [] qs h.append_sep)) =
      appendFlatten [] qs h.append_sep :=
    _root_.Equiv.ext (fun x =>
      congrArg _ ((foldSurvivingPermEquiv hperm).symm_apply_apply x))
  refine ⟨Fragment.Equiv.symm ?_⟩
  refine Fragment.Equiv.trans
    (hcomp ▸ (Equiv.relabelTrans _
      (foldSurvivingPermEquiv hperm)
      ((foldSurvivingPermEquiv hperm).symm.trans
        (appendFlatten [] qs h.append_sep))).symm) ?_
  refine Fragment.Equiv.trans
    (Equiv.relabelCongr (hEq ▸ b1) _) ?_
  refine Fragment.Equiv.trans
    (Equiv.relabelCongr b3 _) ?_
  refine Fragment.Equiv.trans (Equiv.relabelTrans _ _ _) ?_
  have hfinal : (foldSurvivingMapEquiv foldSurvivingNilEquiv.symm
        qs).trans
      ((foldSurvivingPermEquiv hperm).symm.trans
        (appendFlatten [] qs h.append_sep)) =
      _root_.Equiv.refl _ :=
    _root_.Equiv.ext (fun _ => Subtype.ext rfl)
  rw [hfinal]
  exact Equiv.relabelRefl _

/-- Two-stage folding (existence): gluing a concatenation is
gluing the first block, then the lifted second block. -/
private theorem nonempty_glueList_append_aux (n : ℕ) :
    ∀ {α : Type} (W : Fragment α) (ps qs : List (α × α))
    (h : PairsWF (ps ++ qs)) (_ : ps.length ≤ n),
    Nonempty ((glueList W (ps ++ qs) h).Equiv
      ((glueList (glueList W ps h.append_left)
        (liftPairs ps qs h.append_sep)
        (liftPairs_wf ps qs h.append_right h.append_sep)).relabel
        (appendFlatten ps qs h.append_sep))) := by
  induction n with
  | zero =>
    intro α W ps qs h hlen
    obtain rfl : ps = [] :=
      List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    exact nonempty_glueList_append_nil W qs h
  | succ n ih =>
    intro α W ps qs h hlen
    match ps, h, hlen with
    | [], h, _ =>
      exact nonempty_glueList_append_nil W qs h
    | (i, j) :: ps, h, hlen =>
      have hne : i ≠ j := h.append_left.head_ne
      have hsep : PairsSep i j (ps ++ qs) := h.sep
      have happend := coercePairsList_append i j ps qs hsep
      have hwf_c : PairsWF
          (coercePairsList i j ps
            (fun r hr => hsep r (List.mem_append.mpr (Or.inl hr))) ++
           coercePairsList i j qs
            (fun r hr => hsep r (List.mem_append.mpr (Or.inr hr)))) :=
        happend ▸ coercePairsList_wf i j (ps ++ qs) h.tail hsep
      have hlen' : (coercePairsList i j ps
          (fun r hr => hsep r (List.mem_append.mpr (Or.inl hr)))).length
          ≤ n := by
        rw [coercePairsList_length]
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨e_ih⟩ := ih (W.gluePair i j hne) _ _ hwf_c hlen'
      -- list bridge on the left
      have b1 := glueListEqEquiv (W.gluePair i j hne) happend
        (coercePairsList_wf i j (ps ++ qs) h.tail hsep) hwf_c
        (by rw [happend])
      -- lifted-pairs bridge on the right
      have hlift : mapPairs (foldFlatten i j ps h.append_left.sep)
          (liftPairs
            (coercePairsList i j ps h.append_left.sep)
            (coercePairsList i j qs
              (fun r hr => hsep r (List.mem_append.mpr (Or.inr hr))))
            (hwf_c.append_sep)) =
          liftPairs ((i, j) :: ps) qs h.append_sep := by
        rw [← liftPairs_cons_eq i j ps h.append_left.sep qs
          h.append_sep
          (fun r hr => hsep r (List.mem_append.mpr (Or.inr hr)))
          hwf_c.append_sep]
        exact mapPairs_cancel _ _
      -- outer-relabel commutation on the right
      have e_rel := glueListRelabel
        (glueList (W.gluePair i j hne)
          (coercePairsList i j ps h.append_left.sep)
          (coercePairsList_wf i j ps h.append_left.tail
            h.append_left.sep))
        (foldFlatten i j ps h.append_left.sep)
        (liftPairs _ _ hwf_c.append_sep)
        (liftPairs_wf _ _ hwf_c.append_right hwf_c.append_sep)
      have b2 := glueListEqEquiv
        ((glueList (W.gluePair i j hne)
          (coercePairsList i j ps h.append_left.sep)
          (coercePairsList_wf i j ps h.append_left.tail
            h.append_left.sep)).relabel
          (foldFlatten i j ps h.append_left.sep))
        hlift
        (mapPairs_wf _ _
          (liftPairs_wf _ _ hwf_c.append_right hwf_c.append_sep))
        (liftPairs_wf _ _ h.append_right h.append_sep)
        (by rw [hlift])
      refine ⟨?_⟩
      change ((glueList W ((i, j) :: (ps ++ qs)) h).Equiv _)
      rw [glueList_cons W (i, j) (ps ++ qs) h]
      -- move the left side to the two-stage form
      have hcompL : (foldSurvivingPermEquiv (by rw [happend] :
            (coercePairsList i j (ps ++ qs) h.sep).Perm _)).trans
          ((foldSurvivingPermEquiv (by rw [happend])).symm.trans
            (foldFlatten i j (ps ++ qs) h.sep)) =
          foldFlatten i j (ps ++ qs) h.sep :=
        _root_.Equiv.ext (fun x => by simp)
      refine Fragment.Equiv.trans
        (hcompL ▸ (Equiv.relabelTrans _
          (foldSurvivingPermEquiv (by rw [happend]))
          ((foldSurvivingPermEquiv (by rw [happend])).symm.trans
            (foldFlatten i j (ps ++ qs) h.sep))).symm) ?_
      refine Fragment.Equiv.trans
        (Equiv.relabelCongr (b1.trans e_ih) _) ?_
      refine Fragment.Equiv.trans (Equiv.relabelTrans _ _ _) ?_
      -- move the right side to the two-stage form
      refine Fragment.Equiv.symm ?_
      have hconsR := glueList_cons W (i, j) ps h.append_left
      rw [hconsR]
      refine Fragment.Equiv.trans
        (Equiv.relabelCongr b2.symm _) ?_
      refine Fragment.Equiv.trans (Equiv.relabelTrans _ _ _) ?_
      refine Fragment.Equiv.trans
        (Equiv.relabelCongr e_rel _) ?_
      refine Fragment.Equiv.trans (Equiv.relabelTrans _ _ _) ?_
      have heqF : (foldSurvivingMapEquiv
            (foldFlatten i j ps h.append_left.sep)
            (liftPairs _ _ hwf_c.append_sep)).trans
          ((foldSurvivingPermEquiv (by rw [hlift])).trans
            (appendFlatten ((i, j) :: ps) qs h.append_sep)) =
          (appendFlatten _ _ hwf_c.append_sep).trans
            ((foldSurvivingPermEquiv (by rw [happend])).symm.trans
              (foldFlatten i j (ps ++ qs) h.sep)) :=
        _root_.Equiv.ext (fun _ => Subtype.ext rfl)
      exact heqF ▸ Fragment.Equiv.refl _

/-- **Two-stage folding**: gluing a concatenation of pair lists is
gluing the first block, then the lifted second block, up to the
flattening of survivors. -/
noncomputable def glueListAppend (W : Fragment α)
    (ps qs : List (α × α)) (h : PairsWF (ps ++ qs)) :
    (glueList W (ps ++ qs) h).Equiv
      ((glueList (glueList W ps h.append_left)
        (liftPairs ps qs h.append_sep)
        (liftPairs_wf ps qs h.append_right h.append_sep)).relabel
        (appendFlatten ps qs h.append_sep)) :=
  (nonempty_glueList_append_aux ps.length W ps qs h le_rfl).some

/-! ### Disjoint-union embedding: left -/

/-- Embed a pair list into the left summand of a disjoint
union. -/
def inlPairs (ps : List (α × α)) :
    List ((α ⊕ β) × (α ⊕ β)) :=
  ps.map (Prod.map Sum.inl Sum.inl)

private theorem inlPairs_flatMap :
    ∀ (ps : List (α × α)),
    (inlPairs (β := β) ps).flatMap
      (fun p => [p.1, p.2]) =
      (ps.flatMap (fun q => [q.1, q.2])).map Sum.inl
  | [] => rfl
  | _ :: ps => by
    simp only [inlPairs, List.map_cons,
      List.flatMap_cons, List.map_append, Prod.map,
      List.map_cons, List.map_nil]
    exact congrArg _ (inlPairs_flatMap ps)

/-- `inlPairs` preserves well-formedness. -/
theorem inlPairs_wf (ps : List (α × α))
    (hp : PairsWF ps) :
    PairsWF (inlPairs (β := β) ps) := by
  unfold PairsWF; rw [inlPairs_flatMap]
  exact hp.map Sum.inl_injective

/-- The surviving-label equivalence for left-embedded
pairs: inl-labels survive iff they survive the original
list; all inr-labels survive. -/
def inlFoldEquiv (ps : List (α × α)) :
    FoldSurviving (α ⊕ β)
      (inlPairs (β := β) ps) ≃
      (FoldSurviving α ps) ⊕ β where
  toFun := fun ⟨x, hx⟩ =>
    match x, hx with
    | Sum.inl a, hx => Sum.inl ⟨a,
        fun p hp => by
        have := hx
          (Prod.map Sum.inl Sum.inl p)
          (List.mem_map.mpr ⟨p, hp, rfl⟩)
        simp only [Prod.map] at this
        exact
          ⟨fun h => this.1
              (congrArg Sum.inl h),
           fun h => this.2
              (congrArg Sum.inl h)⟩⟩
    | Sum.inr b, _ => Sum.inr b
  invFun := fun y =>
    match y with
    | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a,
        fun p hp => by
        obtain ⟨q, hq, rfl⟩ :=
          List.mem_map.mp hp
        simp only [Prod.map]
        exact
          ⟨fun h => (ha q hq).1
              (Sum.inl.inj h),
           fun h => (ha q hq).2
              (Sum.inl.inj h)⟩⟩
    | Sum.inr b => ⟨Sum.inr b,
        fun p hp => by
        obtain ⟨_, _, rfl⟩ :=
          List.mem_map.mp hp
        exact ⟨Sum.inr_ne_inl,
          Sum.inr_ne_inl⟩⟩
  left_inv := fun ⟨x, _⟩ => by
    cases x with
    | inl => exact Subtype.ext rfl
    | inr => exact Subtype.ext rfl
  right_inv := fun y => by
    cases y with
    | inl a =>
      exact congrArg Sum.inl (Subtype.ext rfl)
    | inr => rfl

/-! ### Disjoint-union embedding: right -/

/-- Embed a pair list into the right summand of a disjoint
union. -/
def inrPairs (qs : List (β × β)) :
    List ((α ⊕ β) × (α ⊕ β)) :=
  qs.map (Prod.map Sum.inr Sum.inr)

private theorem inrPairs_flatMap :
    ∀ (qs : List (β × β)),
    (inrPairs (α := α) qs).flatMap
      (fun p => [p.1, p.2]) =
      (qs.flatMap (fun q => [q.1, q.2])).map Sum.inr
  | [] => rfl
  | _ :: qs => by
    simp only [inrPairs, List.map_cons,
      List.flatMap_cons, List.map_append, Prod.map,
      List.map_cons, List.map_nil]
    exact congrArg _ (inrPairs_flatMap qs)

/-- `inrPairs` preserves well-formedness. -/
theorem inrPairs_wf (qs : List (β × β))
    (hq : PairsWF qs) :
    PairsWF (inrPairs (α := α) qs) := by
  unfold PairsWF; rw [inrPairs_flatMap]
  exact hq.map Sum.inr_injective

/-- The surviving-label equivalence for right-embedded
pairs: inr-labels survive iff they survive the original
list; all inl-labels survive. -/
def inrFoldEquiv (qs : List (β × β)) :
    FoldSurviving (α ⊕ β)
      (inrPairs (α := α) qs) ≃
      α ⊕ (FoldSurviving β qs) where
  toFun := fun ⟨x, hx⟩ =>
    match x, hx with
    | Sum.inl a, _ => Sum.inl a
    | Sum.inr b, hx => Sum.inr ⟨b,
        fun p hp => by
        have := hx
          (Prod.map Sum.inr Sum.inr p)
          (List.mem_map.mpr ⟨p, hp, rfl⟩)
        simp only [Prod.map] at this
        exact
          ⟨fun h => this.1
              (congrArg Sum.inr h),
           fun h => this.2
              (congrArg Sum.inr h)⟩⟩
  invFun := fun y =>
    match y with
    | Sum.inl a => ⟨Sum.inl a,
        fun p hp => by
        obtain ⟨_, _, rfl⟩ :=
          List.mem_map.mp hp
        exact ⟨Sum.inl_ne_inr,
          Sum.inl_ne_inr⟩⟩
    | Sum.inr ⟨b, hb⟩ => ⟨Sum.inr b,
        fun p hp => by
        obtain ⟨q, hq, rfl⟩ :=
          List.mem_map.mp hp
        simp only [Prod.map]
        exact
          ⟨fun h => (hb q hq).1
              (Sum.inr.inj h),
           fun h => (hb q hq).2
              (Sum.inr.inj h)⟩⟩
  left_inv := fun ⟨x, _⟩ => by
    cases x with
    | inl => exact Subtype.ext rfl
    | inr => exact Subtype.ext rfl
  right_inv := fun y => by
    cases y with
    | inl => rfl
    | inr b =>
      exact congrArg Sum.inr (Subtype.ext rfl)

/-! ### Helpers for disjoint-union embedding proofs -/

/-- Relabelling the left factor of a disjoint union equals
relabelling the whole union by `Equiv.sumCongr`. -/
private noncomputable def relabelDisjUnionLeft
    {α' : Type}
    (W : Fragment α) (W' : Fragment β)
    (e : α ≃ α') :
    ((W.relabel e).disjUnion W').Equiv
      ((W.disjUnion W').relabel
        (_root_.Equiv.sumCongr e
          (_root_.Equiv.refl β))) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := by
    rcases f with f | f
    · change ((W.attach f).map Sum.inl Sum.inl).map
            id (_root_.Equiv.sumCongr e
              (_root_.Equiv.refl β)) =
          (((W.attach f).map id e).map Sum.inl
            Sum.inl).map (_root_.Equiv.refl _) id
      rcases W.attach f with v | ℓ <;> rfl
    · change ((W'.attach f).map Sum.inr Sum.inr).map
            id (_root_.Equiv.sumCongr e
              (_root_.Equiv.refl β)) =
          ((W'.attach f).map Sum.inr Sum.inr).map
            (_root_.Equiv.refl _) id
      rcases W'.attach f with v | ℓ <;> rfl
  pairing_comm f := by rcases f with f | f <;> rfl
  circles_eq := rfl

/-- Relabelling the right factor of a disjoint union equals
relabelling the whole union by `Equiv.sumCongr`. -/
private noncomputable def relabelDisjUnionRight
    {β' : Type}
    (W : Fragment α) (W' : Fragment β)
    (e : β ≃ β') :
    (W.disjUnion (W'.relabel e)).Equiv
      ((W.disjUnion W').relabel
        (_root_.Equiv.sumCongr (_root_.Equiv.refl α)
          e)) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := by
    rcases f with f | f
    · change ((W.attach f).map Sum.inl Sum.inl).map
            id (_root_.Equiv.sumCongr
              (_root_.Equiv.refl α) e) =
          ((W.attach f).map Sum.inl Sum.inl).map
            (_root_.Equiv.refl _) id
      rcases W.attach f with v | ℓ <;> rfl
    · change ((W'.attach f).map Sum.inr Sum.inr).map
            id (_root_.Equiv.sumCongr
              (_root_.Equiv.refl α) e) =
          (((W'.attach f).map id e).map Sum.inr
            Sum.inr).map (_root_.Equiv.refl _) id
      rcases W'.attach f with v | ℓ <;> rfl
  pairing_comm f := by rcases f with f | f <;> rfl
  circles_eq := rfl

/-- The coerced inl-pairs equal the mapped inl-pairs of the
coerced original pairs. -/
private theorem coercePairsList_inlPairs_comm
    (i j : α) (hij : i ≠ j) :
    ∀ (ps : List (α × α))
    (hsep : PairsSep (Sum.inl i : α ⊕ β)
      (Sum.inl j) (inlPairs (β := β) ps))
    (hsep' : PairsSep i j ps),
    coercePairsList (Sum.inl i : α ⊕ β)
        (Sum.inl j) (inlPairs (β := β) ps) hsep =
      mapPairs (ambientLabelEquiv i j).symm
        (inlPairs (β := β)
          (coercePairsList i j ps hsep'))
  | [], _, _ => rfl
  | _ :: ps, _, _ =>
    congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl)
        (Subtype.ext rfl))
      (coercePairsList_inlPairs_comm
        i j hij ps _ _)

/-! ### Disjoint-union left: main induction -/

private theorem nonempty_glueList_disjUnion_left_cons
    (n : ℕ)
    (ih : ∀ {α β : Type} (W₁ : Fragment α)
    (W₂ : Fragment β)
    (ps : List (α × α)) (hp : PairsWF ps)
    (_ : ps.length ≤ n),
    Nonempty
      ((glueList (W₁.disjUnion W₂)
          (inlPairs ps) (inlPairs_wf ps hp)).Equiv
        (((glueList W₁ ps hp).disjUnion
            W₂).relabel
          (inlFoldEquiv ps).symm)))
    {α β : Type} (W₁ : Fragment α) (W₂ : Fragment β)
    (i j : α) (ps : List (α × α)) (hp : PairsWF ((i, j) :: ps))
    (hlen : ((i, j) :: ps).length ≤ n + 1) :
    Nonempty
      ((glueList (W₁.disjUnion W₂)
          (inlPairs ((i, j) :: ps)) (inlPairs_wf ((i, j) :: ps) hp)).Equiv
        (((glueList W₁ ((i, j) :: ps) hp).disjUnion W₂).relabel
          (inlFoldEquiv ((i, j) :: ps)).symm)) := by
  have hij := hp.head_ne
  have hij' : (Sum.inl i : α ⊕ β) ≠
      Sum.inl j :=
    fun h => hij (Sum.inl.inj h)
  have hp_inl :=
    inlPairs_wf (β := β)
      ((i, j) :: ps) hp
  have hwf_cp :=
    coercePairsList_wf i j ps
      hp.tail hp.sep
  have hwf_scp :=
    coercePairsList_wf (Sum.inl i)
      (Sum.inl j) (inlPairs (β := β) ps)
      hp_inl.tail hp_inl.sep
  have hlen' :
      (coercePairsList i j ps
        hp.sep).length ≤ n := by
    rw [coercePairsList_length]
    simp only [List.length_cons] at hlen
    omega
  -- Abbreviations
  let amb :=
    ambientLabelEquiv (β := β) i j
  let cp :=
    coercePairsList i j ps hp.sep
  let scp :=
    coercePairsList (Sum.inl i)
      (Sum.inl j)
      (inlPairs (β := β) ps)
      hp_inl.sep
  -- Tail list bridge
  have h_cpc :=
    coercePairsList_inlPairs_comm
      i j hij ps hp_inl.sep hp.sep
  -- mapPairs cancellation
  have h_mp :
      mapPairs amb scp =
        inlPairs (β := β) cp := by
    change mapPairs
      (ambientLabelEquiv i j)
      (coercePairsList (Sum.inl i)
        (Sum.inl j)
        (inlPairs (β := β) ps)
        hp_inl.sep) =
      inlPairs (β := β)
        (coercePairsList i j ps hp.sep)
    rw [h_cpc, mapPairs_mapPairs,
      show (ambientLabelEquiv
          (β := β) i j).symm.trans
        (ambientLabelEquiv i j) =
        _root_.Equiv.refl _ from
        _root_.Equiv.ext
          (ambientLabelEquiv i j).apply_symm_apply]
    exact List.map_id _
  -- IH
  obtain ⟨e_ih⟩ := ih
    (W₁.gluePair i j hij) W₂
    cp hwf_cp hlen'
  -- gluePairDisjUnion
  have e_gp :=
    gluePairDisjUnion W₁ W₂ hij
  -- glueListRelabel
  have e_rel := glueListRelabel
    ((W₁.disjUnion W₂).gluePair
      (Sum.inl i) (Sum.inl j) hij')
    amb scp hwf_scp
  -- glueListEqEquiv
  have e_eq := glueListEqEquiv
    (((W₁.disjUnion W₂).gluePair
      (Sum.inl i) (Sum.inl j)
      hij').relabel amb)
    h_mp
    (mapPairs_wf amb scp hwf_scp)
    (inlPairs_wf cp hwf_cp)
    (h_mp ▸ List.Perm.refl _)
  -- glueListCongr
  have e_congr := glueListCongr
    (Fragment.Equiv.symm e_gp)
    (inlPairs (β := β) cp)
    (inlPairs_wf cp hwf_cp)
  -- Inner chain
  have inner :=
    ((Equiv.relabelCongr e_rel.symm
      (foldSurvivingPermEquiv
        (h_mp ▸ List.Perm.refl
          _))).trans
      e_eq).trans
    (e_congr.trans e_ih)
  -- Outer relabelling bridge
  let σ :=
    (inlFoldEquiv (β := β) cp).trans
      ((_root_.Equiv.sumCongr
        (foldFlatten i j ps hp.sep)
        (_root_.Equiv.refl β)).trans
      (inlFoldEquiv (β := β)
        ((i, j) :: ps)).symm)
  -- LHS equiv equality
  have hLHS :
      (foldSurvivingMapEquiv amb
        scp).trans
        ((foldSurvivingPermEquiv
          (h_mp ▸ List.Perm.refl
            _)).trans σ) =
      foldFlatten (Sum.inl i)
        (Sum.inl j)
        (inlPairs (β := β) ps)
        hp_inl.sep :=
    _root_.Equiv.ext (fun x => by
      obtain ⟨⟨a | b, -, -⟩, -⟩ := x
      · exact Subtype.ext rfl
      · exact Subtype.ext rfl)
  -- RHS equiv equality
  have hRHS :
      (inlFoldEquiv (β := β)
        cp).symm.trans σ =
      (_root_.Equiv.sumCongr
        (foldFlatten i j ps hp.sep)
        (_root_.Equiv.refl β)).trans
      (inlFoldEquiv (β := β)
        ((i, j) :: ps)).symm :=
    _root_.Equiv.ext (fun y => by
      rcases y with ⟨⟨a, -⟩, -⟩ | b
      · exact Subtype.ext rfl
      · exact Subtype.ext rfl)
  -- RHS chain
  have rhs_chain :
    (((glueList
        (W₁.gluePair i j hij)
        cp hwf_cp).disjUnion
      W₂).relabel
      ((inlFoldEquiv (β := β)
        cp).symm.trans σ)).Equiv
    ((((glueList
        (W₁.gluePair i j hij)
        cp hwf_cp).relabel
      (foldFlatten i j ps
        hp.sep)).disjUnion
      W₂).relabel
      (inlFoldEquiv (β := β)
        ((i, j) :: ps)).symm) := by
    rw [hRHS]
    exact
      (Equiv.relabelTrans _ _ _).symm.trans
      (Equiv.relabelCongr
        (relabelDisjUnionLeft _ W₂
          _).symm _)
  -- Main proof
  refine ⟨?_⟩
  change ((W₁.disjUnion W₂).glueList
      ((Sum.inl i, Sum.inl j) ::
        inlPairs (β := β) ps)
      hp_inl).Equiv
    (((W₁.glueList ((i, j) :: ps)
        hp).disjUnion
      W₂).relabel
      (inlFoldEquiv (β := β)
        ((i, j) :: ps)).symm)
  rw [glueList_cons (W₁.disjUnion W₂)
        (Sum.inl i, Sum.inl j)
        (inlPairs (β := β) ps) hp_inl,
      glueList_cons W₁ (i, j) ps hp]
  rw [← hLHS]
  exact
    ((Equiv.relabelTrans _
      (foldSurvivingMapEquiv amb scp)
      ((foldSurvivingPermEquiv
        _).trans σ)).symm.trans
    ((Equiv.relabelTrans _
      (foldSurvivingPermEquiv _)
      σ).symm.trans
    (Equiv.relabelCongr inner
      σ))).trans
    ((Equiv.relabelTrans _
      (inlFoldEquiv (β := β)
        cp).symm σ).trans
      rhs_chain)

private theorem nonempty_glueList_disjUnion_left_aux
    (n : ℕ) :
    ∀ {α β : Type} (W₁ : Fragment α)
    (W₂ : Fragment β)
    (ps : List (α × α)) (hp : PairsWF ps)
    (_ : ps.length ≤ n),
    Nonempty
      ((glueList (W₁.disjUnion W₂)
          (inlPairs ps) (inlPairs_wf ps hp)).Equiv
        (((glueList W₁ ps hp).disjUnion
            W₂).relabel
          (inlFoldEquiv ps).symm)) := by
  induction n with
  -- ═══════ n = 0: NO PAIRS LEFT TO GLUE ═══════
  | zero =>
    intro α β W₁ W₂ ps hp hlen
    have hnil : ps = [] :=
      List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp hlen)
    subst hnil
    have heq :
        (foldSurvivingNilEquiv
            (α := α ⊕ β)).symm =
          (_root_.Equiv.sumCongr
            (foldSurvivingNilEquiv
              (α := α)).symm
            (_root_.Equiv.refl β)).trans
          (inlFoldEquiv (β := β) []).symm :=
      _root_.Equiv.ext (fun x => by
        cases x <;> exact Subtype.ext rfl)
    exact ⟨(heq ▸ (Equiv.relabelTrans
        (W₁.disjUnion W₂)
        (_root_.Equiv.sumCongr
          (foldSurvivingNilEquiv
            (α := α)).symm
          (_root_.Equiv.refl β))
        (inlFoldEquiv (β := β)
          []).symm).symm).trans
      (Equiv.relabelCongr
        (relabelDisjUnionLeft W₁ W₂
          (foldSurvivingNilEquiv
            (α := α)).symm).symm
        (inlFoldEquiv (β := β) []).symm)⟩
  -- ═══════ n + 1: PEEL THE HEAD PAIR ═══════
  | succ n ih =>
    intro α β W₁ W₂ ps hp hlen
    match ps, hp, hlen with
    -- ═══════ The list is empty anyway ═══════
    | [], _, _ =>
      have heq :
          (foldSurvivingNilEquiv
              (α := α ⊕ β)).symm =
            (_root_.Equiv.sumCongr
              (foldSurvivingNilEquiv
                (α := α)).symm
              (_root_.Equiv.refl β)).trans
            (inlFoldEquiv (β := β) []).symm :=
        _root_.Equiv.ext (fun x => by
          cases x <;> exact Subtype.ext rfl)
      exact ⟨(heq ▸ (Equiv.relabelTrans
          (W₁.disjUnion W₂)
          (_root_.Equiv.sumCongr
            (foldSurvivingNilEquiv
              (α := α)).symm
            (_root_.Equiv.refl β))
          (inlFoldEquiv (β := β)
            []).symm).symm).trans
        (Equiv.relabelCongr
          (relabelDisjUnionLeft W₁ W₂
            (foldSurvivingNilEquiv
              (α := α)).symm).symm
          (inlFoldEquiv (β := β) []).symm)⟩
    -- ═══════ Glue the head on the left component, recurse ═══════
    | (i, j) :: ps, hp, hlen =>
      exact nonempty_glueList_disjUnion_left_cons n ih W₁ W₂ i j ps hp hlen

/-- Iterated left-side gluing commutes with disjoint
union: gluing the `inlPairs`-embedded pair list in the
disjoint union is equivalent to gluing `W₁` alone and
then taking the disjoint union with `W₂`, up to the
canonical label isomorphism `inlFoldEquiv`. -/
noncomputable def glueListDisjUnionLeft
    {α β : Type}
    (W₁ : Fragment α) (W₂ : Fragment β)
    (ps : List (α × α)) (hp : PairsWF ps) :
    (glueList (W₁.disjUnion W₂)
        (inlPairs ps)
        (inlPairs_wf ps hp)).Equiv
      (((glueList W₁ ps hp).disjUnion
          W₂).relabel
        (inlFoldEquiv ps).symm) :=
  (nonempty_glueList_disjUnion_left_aux
    ps.length W₁ W₂ ps hp le_rfl).some

/-- Iterated right-side gluing commutes with disjoint
union: gluing the `inrPairs`-embedded pair list in the
disjoint union is equivalent to gluing `W₂` alone and
then taking the disjoint union with `W₁`, up to the
canonical label isomorphism `inrFoldEquiv`. -/
noncomputable def glueListDisjUnionRight
    {α β : Type}
    (W₁ : Fragment α) (W₂ : Fragment β)
    (qs : List (β × β)) (hq : PairsWF qs) :
    (glueList (W₁.disjUnion W₂)
        (inrPairs qs)
        (inrPairs_wf qs hq)).Equiv
      (((W₁.disjUnion
          (glueList W₂ qs hq)).relabel
        (inrFoldEquiv qs).symm)) := by
  -- Derive from glueListDisjUnionLeft via
  -- disjUnionComm and glueListRelabel
  let sc := _root_.Equiv.sumComm β α
  -- mapPairs sc (inlPairs qs) = inrPairs qs
  have h_mp :
      mapPairs sc
        (inlPairs (α := β) (β := α) qs) =
      inrPairs (α := α) (β := β) qs := by
    simp only [mapPairs, inlPairs, inrPairs,
      List.map_map]; rfl
  -- Abbreviations
  have h_perm :
      (mapPairs sc
        (inlPairs (α := β) (β := α) qs)).Perm
      (inrPairs (α := α) (β := β) qs) :=
    h_mp ▸ List.Perm.refl _
  let fSPE_e :=
    foldSurvivingPermEquiv h_perm
  let fSME_e :=
    foldSurvivingMapEquiv sc
      (inlPairs (α := β) (β := α) qs)
  let ife :=
    inlFoldEquiv (α := β) (β := α) qs
  let sc' := _root_.Equiv.sumComm α
    (FoldSurviving β qs)
  -- Step 1: swap W₁, W₂
  have e1 :=
    glueListCongr
      (disjUnionComm W₁ W₂)
      (inrPairs qs) (inrPairs_wf qs hq)
  -- Step 2: bridge pair lists
  have e2 :=
    (glueListEqEquiv
      ((W₂.disjUnion W₁).relabel sc)
      h_mp
      (mapPairs_wf sc _
        (inlPairs_wf (β := α) qs hq))
      (inrPairs_wf qs hq)
      (h_mp ▸ List.Perm.refl _)).symm
  -- Step 3: pull relabel through glueList
  have e3 :=
    glueListRelabel (W₂.disjUnion W₁) sc
      (inlPairs (β := α) qs)
      (inlPairs_wf (β := α) qs hq)
  -- Step 4: left embedding theorem
  have e4 :=
    glueListDisjUnionLeft W₂ W₁ qs hq
  -- Step 5: swap result back
  have e5 :=
    disjUnionComm (glueList W₂ qs hq) W₁
  -- Composed equiv equation
  have h_eq :
      sc'.trans (ife.symm.trans
        (fSME_e.trans fSPE_e)) =
      (inrFoldEquiv (α := α) qs).symm :=
    _root_.Equiv.ext (fun x => by
      rcases x with a | ⟨b, -⟩
      · exact Subtype.ext rfl
      · exact Subtype.ext rfl)
  -- Chain the equivalences
  exact
    (e1.trans e2).trans
    ((Equiv.relabelCongr e3 fSPE_e).trans
    ((Equiv.relabelTrans _ fSME_e
      fSPE_e).trans
    ((Equiv.relabelCongr e4
      (fSME_e.trans fSPE_e)).trans
    ((Equiv.relabelTrans _
      ife.symm
      (fSME_e.trans fSPE_e)).trans
    ((Equiv.relabelCongr e5
      (ife.symm.trans
        (fSME_e.trans fSPE_e))).trans
    ((Equiv.relabelTrans _
      sc'
      (ife.symm.trans
        (fSME_e.trans fSPE_e))).trans
    (h_eq ▸ Equiv.refl _)))))))

/-! ### The swap-components fold lemma -/

/-- The flatMap of a pair-swapped list is a permutation
of the original flatMap. -/
private theorem swap_flatMap_perm :
    ∀ (ps : List (α × α)),
    ((ps.map Prod.swap).flatMap
      (fun p => [p.1, p.2])).Perm
    (ps.flatMap (fun p => [p.1, p.2]))
  | [] => List.Perm.refl []
  | (a, b) :: ps => by
    simp only [List.map_cons, Prod.swap,
      List.flatMap_cons]
    exact (List.Perm.append_left [b, a]
      (swap_flatMap_perm ps)).trans
      (List.Perm.swap a b _)

/-- Swapping every pair preserves well-formedness. -/
theorem swapPairs_wf (ps : List (α × α))
    (hp : PairsWF ps) :
    PairsWF (ps.map Prod.swap) :=
  (swap_flatMap_perm ps).nodup_iff.mpr hp

/-- Surviving labels are invariant under swapping pair
components: `x ≠ p.1 ∧ x ≠ p.2` iff
`x ≠ p.2 ∧ x ≠ p.1`. -/
def swapFoldEquiv (ps : List (α × α)) :
    FoldSurviving α (ps.map Prod.swap) ≃
      FoldSurviving α ps where
  toFun x :=
    ⟨x.val, fun p hp => by
      have := x.prop p.swap
        (List.mem_map.mpr ⟨p, hp, rfl⟩)
      exact ⟨this.2, this.1⟩⟩
  invFun x :=
    ⟨x.val, fun p hp => by
      obtain ⟨q, hq, rfl⟩ :=
        List.mem_map.mp hp
      exact ⟨(x.prop q hq).2,
        (x.prop q hq).1⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- PairsSep is symmetric in the removed labels and
invariant under swapping pair components. -/
private theorem pairsSep_swap (i j : α)
    (ps : List (α × α))
    (h : PairsSep i j ps) :
    PairsSep j i (ps.map Prod.swap) := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have := h r hr
  exact this.swap_left.swap_right

/-- Coercing a swapped pair list relates to
mapping `survLabelSwapEquiv` over the swap of the
original coerced list. -/
private theorem coercePairsList_swap
    (i j : α) :
    ∀ (ps : List (α × α))
    (h : PairsSep i j ps)
    (h' : PairsSep j i (ps.map Prod.swap)),
    coercePairsList j i
      (ps.map Prod.swap) h' =
    mapPairs (survLabelSwapEquiv α i j).symm
      ((coercePairsList i j ps h).map
        Prod.swap)
  | [], _, _ => rfl
  | _ :: ps, h, h' => by
    simp only [List.map_cons, Prod.swap,
      coercePairsList, mapPairs, Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl)
        (Subtype.ext rfl))
      (coercePairsList_swap i j ps _ _)

private theorem nonempty_glueList_swap_aux
    (n : ℕ) :
    ∀ {α : Type} (W : Fragment α)
    (ps : List (α × α)) (hp : PairsWF ps)
    (_ : ps.length ≤ n),
    Nonempty
      ((glueList W (ps.map Prod.swap)
          (swapPairs_wf ps hp)).Equiv
        ((glueList W ps hp).relabel
          (swapFoldEquiv ps).symm)) := by
  induction n with
  -- ═══════ n = 0: NO PAIRS LEFT TO GLUE ═══════
  | zero =>
    intro α W ps hp hlen
    have hnil : ps = [] :=
      List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp hlen)
    subst hnil
    change Nonempty
      ((W.relabel
        foldSurvivingNilEquiv.symm).Equiv
       ((W.relabel
        foldSurvivingNilEquiv.symm).relabel
         (swapFoldEquiv []).symm))
    have heq :
        foldSurvivingNilEquiv (α := α).symm =
        foldSurvivingNilEquiv.symm.trans
          (swapFoldEquiv (α := α) []).symm :=
      _root_.Equiv.ext
        (fun _ => Subtype.ext rfl)
    exact ⟨(Equiv.relabelTrans W
      foldSurvivingNilEquiv.symm
      (swapFoldEquiv []).symm).symm.trans
      (heq ▸ Equiv.refl _)⟩
  -- ═══════ n + 1: PEEL THE HEAD PAIR ═══════
  | succ n ih =>
    intro α W ps hp hlen
    match ps, hp, hlen with
    -- ═══════ The list is empty anyway ═══════
    | [], _, _ =>
      change Nonempty
        ((W.relabel
          foldSurvivingNilEquiv.symm).Equiv
         ((W.relabel
          foldSurvivingNilEquiv.symm).relabel
           (swapFoldEquiv []).symm))
      have heq :
          foldSurvivingNilEquiv
            (α := α).symm =
          foldSurvivingNilEquiv.symm.trans
            (swapFoldEquiv (α := α) []).symm :=
        _root_.Equiv.ext
          (fun _ => Subtype.ext rfl)
      exact ⟨(Equiv.relabelTrans W
        foldSurvivingNilEquiv.symm
        (swapFoldEquiv []).symm).symm.trans
        (heq ▸ Equiv.refl _)⟩
    -- ═══════ Glue the head with its ends swapped, recurse ═══════
    | (i, j) :: ps, hp, hlen =>
      have hij := hp.head_ne
      have hji : j ≠ i := Ne.symm hij
      -- Swapped well-formedness
      have hp_swap :=
        swapPairs_wf ((i, j) :: ps) hp
      have sep_ij := hp.sep
      have sep_ji_swap :=
        pairsSep_swap i j ps sep_ij
      -- Coerced pair lists
      let cpl_ij :=
        coercePairsList i j ps sep_ij
      let cpl_swap :=
        coercePairsList j i
          (ps.map Prod.swap)
          sep_ji_swap
      have hwf_ij :=
        coercePairsList_wf i j ps
          hp.tail sep_ij
      have hwf_swap :=
        coercePairsList_wf j i
          (ps.map Prod.swap)
          (swapPairs_wf ps hp.tail)
          sep_ji_swap
      -- Length bound for IH
      have hlen' : cpl_ij.length ≤ n := by
        simp only [cpl_ij]
        rw [coercePairsList_length]
        simp only [List.length_cons]
          at hlen
        omega
      -- Swap equiv abbreviations
      let sle_ij :=
        survLabelSwapEquiv α i j
      let sle_ji := sle_ij.symm
      -- Commutation: cpl_swap relates to
      -- mapPairs sle_ji (cpl_ij.map swap)
      have h_cps :=
        coercePairsList_swap i j ps
          sep_ij sep_ji_swap
      have h_mp :
          mapPairs sle_ji
            (cpl_ij.map Prod.swap) =
          cpl_swap :=
        h_cps.symm
      -- Perm witness (shared between
      -- e_eq and fSPE)
      have hperm :
          (mapPairs sle_ji
            (cpl_ij.map Prod.swap)).Perm
          cpl_swap :=
        h_mp ▸ List.Perm.refl _
      -- Step 1: gluePairSwap
      have e_swap :=
        gluePairSwap W hji
      -- Step 2: glueListCongr
      have e_congr :=
        glueListCongr e_swap
          cpl_swap hwf_swap
      -- Step 3: glueListRelabel
      have hwf_swap_ij :=
        swapPairs_wf cpl_ij hwf_ij
      have e_rel :=
        glueListRelabel
          (W.gluePair i j hij) sle_ji
          (cpl_ij.map Prod.swap)
          hwf_swap_ij
      -- Step 4: glueListEqEquiv bridge
      have e_eq :=
        glueListEqEquiv
          ((W.gluePair i j hij).relabel
            sle_ji)
          h_mp
          (mapPairs_wf sle_ji _
            hwf_swap_ij)
          hwf_swap hperm
      -- Step 5: IH
      obtain ⟨e_ih⟩ :=
        ih (W.gluePair i j hij)
          cpl_ij hwf_ij hlen'
      -- Abbreviations for equivs
      let fSPE :=
        foldSurvivingPermEquiv hperm
      let fSME :=
        foldSurvivingMapEquiv sle_ji
          (cpl_ij.map Prod.swap)
      let ff_ji :=
        foldFlatten j i
          (ps.map Prod.swap)
          sep_ji_swap
      let ff_ij :=
        foldFlatten i j ps sep_ij
      -- Inner chain:
      -- glueList (gp j i) cpl_swap
      -- ≡ glueList (gp i j) cpl_ij
      --     |>.relabel composed
      have inner :=
        (e_congr.trans
          (e_eq.symm.trans
            (Equiv.relabelCongr e_rel
              fSPE))).trans
        ((Equiv.relabelTrans _
          fSME fSPE).trans
        (Equiv.relabelCongr e_ih
          (fSME.trans fSPE)))
      -- Composed equiv equation
      have h_eq :
          (((swapFoldEquiv cpl_ij).symm.trans
            (fSME.trans fSPE)).trans
            ff_ji) =
          ff_ij.trans
            (swapFoldEquiv
              ((i, j) :: ps)).symm :=
        _root_.Equiv.ext
          (fun _ => Subtype.ext rfl)
      -- Bridge: h_eq lifts to fragment equiv
      let glW :=
        glueList (W.gluePair i j hij)
          cpl_ij hwf_ij
      have bridge :
          (glW.relabel
            (((swapFoldEquiv
                cpl_ij).symm.trans
              (fSME.trans fSPE)).trans
              ff_ji)).Equiv
          (glW.relabel
            (ff_ij.trans
              (swapFoldEquiv
                ((i, j) :: ps)).symm))
          := by rw [h_eq]; exact Equiv.refl _
      -- Assemble via glueList_cons
      refine ⟨?_⟩
      change (glueList W
          ((j, i) :: ps.map Prod.swap)
          hp_swap).Equiv
        ((glueList W ((i, j) :: ps)
            hp).relabel
          (swapFoldEquiv
            ((i, j) :: ps)).symm)
      rw [glueList_cons W (j, i)
            (ps.map Prod.swap) hp_swap,
          glueList_cons W (i, j) ps hp]
      let sfe_cons :=
        (swapFoldEquiv
          ((i, j) :: ps)).symm
      exact
        (Equiv.relabelCongr inner
          ff_ji).trans
        ((Equiv.relabelTrans
          (glW.relabel
            (swapFoldEquiv cpl_ij).symm)
          (fSME.trans fSPE) ff_ji).trans
        ((Equiv.relabelTrans glW
          (swapFoldEquiv cpl_ij).symm
          ((fSME.trans fSPE).trans
            ff_ji)).trans
        (bridge.trans
        (Equiv.relabelTrans glW
          ff_ij sfe_cons).symm)))

/-- Gluing a pair list is symmetric in each pair's
components: swapping every `(i,j)` to `(j,i)` yields
an equivalent fold, up to the canonical
`swapFoldEquiv`. -/
noncomputable def glueListSwap
    {α : Type}
    (W : Fragment α)
    (ps : List (α × α))
    (hp : PairsWF ps) :
    (glueList W (ps.map Prod.swap)
        (swapPairs_wf ps hp)).Equiv
      ((glueList W ps hp).relabel
        (swapFoldEquiv ps).symm) :=
  (nonempty_glueList_swap_aux ps.length
    W ps hp le_rfl).some

/-! ### The reorder theorem -/

/-- The doubly-coerced tail list in q-then-p order equals
`mapPairs swapLabelEquiv.symm` of the doubly-coerced tail in p-then-q order. -/
private theorem doubly_coerced_swap_eq
    {i j k l : α} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ∀ (ps : List (α × α))
    (hsep_ij : PairsSep i j ps) (hsep_kl : PairsSep k l ps)
    (hsep_inner_ij : PairsSep (⟨k, hik.symm, hjk.symm⟩ : SurvivingLabel α i j)
      ⟨l, hil.symm, hjl.symm⟩ (coercePairsList i j ps hsep_ij))
    (hsep_inner_kl : PairsSep (⟨i, hik, hil⟩ : SurvivingLabel α k l)
      ⟨j, hjk, hjl⟩ (coercePairsList k l ps hsep_kl)),
    coercePairsList ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
        (coercePairsList i j ps hsep_ij) hsep_inner_ij =
      mapPairs (swapLabelEquiv hik hil hjk hjl).symm
        (coercePairsList ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
          (coercePairsList k l ps hsep_kl) hsep_inner_kl)
  | [], _, _, _, _ => rfl
  | _ :: ps, hsep_ij, hsep_kl, hsep_inner_ij, hsep_inner_kl => by
    simp only [coercePairsList, mapPairs, List.map_cons, Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (Subtype.ext (Subtype.ext rfl)) (Subtype.ext (Subtype.ext rfl)))
      (doubly_coerced_swap_eq hik hil hjk hjl ps _ _ _ _)

/-- The coerced pair list permutes when the original does. -/
private theorem coercePairsList_perm (i j : α)
    {ps qs : List (α × α)} (hperm : ps.Perm qs)
    (hp : PairsSep i j ps) (hq : PairsSep i j qs) :
    (coercePairsList i j ps hp).Perm (coercePairsList i j qs hq) := by
  classical
  induction hperm with
  | nil => exact List.Perm.nil
  | @cons x _ _ _ ih =>
    exact List.Perm.cons _ (ih _ _)
  | @swap x y _ =>
    exact List.Perm.swap _ _ _
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    have hmid : PairsSep i j l₂ :=
      fun q hq => hp q (h₁.mem_iff.mpr hq)
    exact (ih₁ _ hmid).trans (ih₂ hmid _)

/-- Auxiliary: the reorder theorem by induction on list length
(needed because the cons case recurses at a different type). -/
private theorem nonempty_glueList_perm_aux (n : ℕ) :
    ∀ {α : Type} (W : Fragment α)
    {ps qs : List (α × α)}
    (hperm : ps.Perm qs) (hp : PairsWF ps)
    (_ : ps.length ≤ n),
    Nonempty ((glueList W ps hp).Equiv
      ((glueList W qs (hp.perm hperm)).relabel
        (foldSurvivingPermEquiv hperm).symm)) := by
  induction n with
  -- ═══════ n = 0: BOTH LISTS ARE EMPTY ═══════
  | zero =>
    intro α W ps qs hperm hp hlen
    have hnil : ps = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    have hqs : qs = [] := hperm.symm.eq_nil
    subst hqs
    have hid : (foldSurvivingPermEquiv hperm).symm =
      _root_.Equiv.refl _ :=
      _root_.Equiv.ext (fun ⟨_, _⟩ => Subtype.ext rfl)
    exact ⟨hid ▸ (Equiv.relabelRefl _).symm⟩
  -- ═══════ n + 1: INDUCT ON THE PERMUTATION ═══════
  | succ n ih =>
    intro α W ps qs hperm hp hlen
    induction hperm generalizing W with
    -- ═══════ nil: nothing to reorder ═══════
    | nil =>
      have hid : (foldSurvivingPermEquiv
          (List.Perm.nil (α := α × α))).symm =
        _root_.Equiv.refl _ :=
        _root_.Equiv.ext (fun ⟨_, _⟩ => Subtype.ext rfl)
      exact ⟨hid ▸ (Equiv.relabelRefl _).symm⟩
    -- ═══════ cons: a shared head, reorder the tails ═══════
    | @cons p ps' qs' hperm _ih_unused =>
      -- Both sides glue p first; use the outer IH on the coerced tails.
      have hlen_tail : (coercePairsList p.1 p.2 ps' hp.sep).length ≤ n := by
        rw [coercePairsList_length]; simp only [List.length_cons] at hlen; omega
      have hp' : PairsWF (p :: qs') := hp.perm (List.Perm.cons p hperm)
      have hwf_cps := coercePairsList_wf p.1 p.2 ps' hp.tail hp.sep
      have hwf_cqs := coercePairsList_wf p.1 p.2 qs' hp'.tail hp'.sep
      have hperm_c := coercePairsList_perm p.1 p.2 hperm hp.sep hp'.sep
      -- Apply the outer IH at type SurvivingLabel α p.1 p.2
      obtain ⟨e_sub⟩ := ih (W.gluePair p.1 p.2 hp.head_ne) hperm_c hwf_cps
        hlen_tail
      -- e_sub relates the inner glues; now compose relabellings
      set B := glueList (W.gluePair p.1 p.2 hp.head_ne)
        (coercePairsList p.1 p.2 qs' hp'.sep) hwf_cqs
      have step₁ := (Equiv.relabelCongr e_sub (foldFlatten p.1 p.2 ps' hp.sep))
      have step₂ := step₁.trans (Equiv.relabelTrans B _ _)
      have step₃ := (Equiv.relabelTrans B (foldFlatten p.1 p.2 qs' hp'.sep)
        (foldSurvivingPermEquiv (List.Perm.cons p hperm)).symm).symm
      have hequivs :
          (foldSurvivingPermEquiv hperm_c).symm.trans (foldFlatten p.1 p.2 ps'
            hp.sep) =
          (foldFlatten p.1 p.2 qs' hp'.sep).trans
            (foldSurvivingPermEquiv (List.Perm.cons p hperm)).symm :=
        _root_.Equiv.ext (fun ⟨⟨_, _⟩, _⟩ => Subtype.ext rfl)
      exact ⟨(glueList_cons W p ps' hp ▸ (glueList_cons W p qs' hp' ▸
        (hequivs ▸ step₂).trans step₃))⟩
    -- ═══════ swap: the two heads exchange ═══════
    | @swap p q ps' =>
      -- swap p q ps' : (q :: p :: ps').Perm (p :: q :: ps')
      -- hp : PairsWF (q :: p :: ps')
      let := Classical.typeDecidableEq α
      have hp' : PairsWF (p :: q :: ps') := hp.perm (List.Perm.swap p q ps')
      have hq12 := hp.head_ne
      have hp12 := hp.tail.head_ne
      have h_pq := hp.head_disjoint_of p List.mem_cons_self
      have hik : q.1 ≠ p.1 := h_pq.fst_ne_fst.symm
      have hil : q.1 ≠ p.2 := h_pq.snd_ne_fst.symm
      have hjk : q.2 ≠ p.1 := h_pq.fst_ne_snd.symm
      have hjl : q.2 ≠ p.2 := h_pq.snd_ne_snd.symm
      have hsep_q_ps' : PairsSep q.1 q.2 ps' :=
        fun r hr => hp.sep r (List.mem_cons.mpr (Or.inr hr))
      have hsep_p_ps' : PairsSep p.1 p.2 ps' :=
        fun r hr => hp'.sep r (List.mem_cons.mpr (Or.inr hr))
      have hwf_q := coercePairsList_wf q.1 q.2 (p :: ps') hp.tail hp.sep
      have hwf_p := coercePairsList_wf p.1 p.2 (q :: ps') hp'.tail hp'.sep
      have hwf_dbl_qp := coercePairsList_wf _ _ _ hwf_q.tail hwf_q.sep
      have hwf_dbl_pq := coercePairsList_wf _ _ _ hwf_p.tail hwf_p.sep
      -- List equality: doubly-coerced in q-then-p order = mapPairs swapLE.symm
      --   of p-then-q order
      have hlist_eq := doubly_coerced_swap_eq hik hil hjk hjl ps'
        hsep_q_ps' hsep_p_ps' hwf_q.sep hwf_p.sep
      -- gluePairComm: (W.gp q).gp p' ≃ ((W.gp p).gp q').relabel swapLE.symm
      have hcomm := gluePairComm W hq12 hp12 hik hil hjk hjl
      -- Relabelling theorem for the tail
      have hlen_dbl : (coercePairsList (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1
        p.2)
          ⟨q.2, hjk, hjl⟩ (coercePairsList p.1 p.2 ps' hsep_p_ps')
            hwf_p.sep).length ≤ n := by
        rw [coercePairsList_length, coercePairsList_length]
        simp only [List.length_cons] at hlen; omega
      obtain ⟨e_relabel⟩ := nonempty_glueList_relabel_aux n
        ((W.gluePair p.1 p.2 hp12).gluePair
          (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1 p.2) ⟨q.2, hjk, hjl⟩
          (fun h => hq12 (congrArg Subtype.val h)))
        (swapLabelEquiv hik hil hjk hjl).symm _ hwf_dbl_pq hlen_dbl
      -- Core equivalence at the doubly-coerced level
      have core := (glueListCongr hcomm _
        (mapPairs_wf (swapLabelEquiv hik hil hjk hjl).symm _ hwf_dbl_pq)).trans
          e_relabel
      -- Bridge: use glueListEqEquiv to relate dbl_qp and mapPairs forms
      have list_perm : (coercePairsList (⟨p.1, hik.symm, hjk.symm⟩ :
        SurvivingLabel α q.1 q.2)
          ⟨p.2, hil.symm, hjl.symm⟩ (coercePairsList q.1 q.2 ps' hsep_q_ps')
          hwf_q.sep).Perm
          (mapPairs (swapLabelEquiv hik hil hjk hjl).symm
            (coercePairsList (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1 p.2)
              ⟨q.2, hjk, hjl⟩ (coercePairsList p.1 p.2 ps' hsep_p_ps')
                hwf_p.sep)) := by
        rw [hlist_eq]
      let inner_qp := (W.gluePair q.1 q.2 hq12).gluePair
            ⟨p.1, hik.symm, hjk.symm⟩ ⟨p.2, hil.symm, hjl.symm⟩
            (fun h => hp12 (congrArg Subtype.val h))
      have bridge := glueListEqEquiv inner_qp hlist_eq hwf_dbl_qp
        (mapPairs_wf (swapLabelEquiv hik hil hjk hjl).symm _ hwf_dbl_pq)
          list_perm
      -- bridge : (glueList inner_qp dbl_qp _).relabel (fSPE list_perm) ≃
      --          glueList inner_qp (mapPairs swapLE.symm dbl_pq) _
      -- core : glueList inner_qp (mapPairs..) _ ≃ (glueList inner_pq dbl_pq
      --   _).relabel (fSME..)
      -- Compose to get: (glueList inner_qp dbl_qp _).relabel (fSPE list_perm) ≃
      --   RHS
      have bridged := bridge.trans core
      -- Composed foldFlattens
      let ff_qp := (foldFlatten (⟨p.1, hik.symm, hjk.symm⟩ : SurvivingLabel α
        q.1 q.2)
        ⟨p.2, hil.symm, hjl.symm⟩ (coercePairsList q.1 q.2 ps' hsep_q_ps')
          hwf_q.sep).trans
        (foldFlatten q.1 q.2 (p :: ps') hp.sep)
      let ff_pq := (foldFlatten (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1 p.2)
        ⟨q.2, hjk, hjl⟩ (coercePairsList p.1 p.2 ps' hsep_p_ps')
          hwf_p.sep).trans
        (foldFlatten p.1 p.2 (q :: ps') hp'.sep)
      -- toTarget maps from FS..(mapPairs..) to FS α (q::p::ps')
      let toTarget := (foldSurvivingPermEquiv list_perm).symm.trans ff_qp
      -- Relabel both sides of bridged by toTarget
      have lifted := Equiv.relabelCongr bridged toTarget
      -- Merge both relabellings using relabelTrans
      have combined :=
        (Equiv.relabelTrans _ (foldSurvivingPermEquiv list_perm)
          toTarget).symm.trans
        (lifted.trans
          (Equiv.relabelTrans _
            (foldSurvivingMapEquiv (swapLabelEquiv hik hil hjk hjl).symm _)
            toTarget))
      -- combined : (glueList inner_qp dbl_qp _).relabel ((fSPE list_perm).trans
      --   toTarget) ≃
      -- (glueList inner_pq dbl_pq _).relabel ((fSME..).trans toTarget)
      -- Show the composed relabellings simplify
      have lhs_eq : (foldSurvivingPermEquiv list_perm).trans toTarget = ff_qp :=
        _root_.Equiv.ext (fun _ => Subtype.ext rfl)
      have rhs_eq :
          (foldSurvivingMapEquiv (swapLabelEquiv hik hil hjk hjl).symm _).trans
            toTarget =
          ff_pq.trans (foldSurvivingPermEquiv (List.Perm.swap p q ps')).symm :=
        _root_.Equiv.ext (fun _ => Subtype.ext rfl)
      -- Rewrite to get the desired relabellings
      have step := rhs_eq ▸ lhs_eq ▸ combined
      -- step : (glueList inner_qp dbl_qp _).relabel ff_qp ≃
      -- (glueList inner_pq dbl_pq _).relabel (ff_pq.trans (fSPE swap).symm)
      -- Decompose the RHS double relabelling
      have decomposed := step.trans (Equiv.relabelTrans _ ff_pq
        (foldSurvivingPermEquiv (List.Perm.swap p q ps')).symm).symm
      -- Fold back using glueList_cons
      have hlhs₁ := glueList_cons W q (p :: ps') hp
      have hlhs₂ := glueList_cons (W.gluePair q.1 q.2 hq12)
        (⟨p.1, hik.symm, hjk.symm⟩, ⟨p.2, hil.symm, hjl.symm⟩)
        (coercePairsList q.1 q.2 ps' hsep_q_ps') hwf_q
      have hrhs₁ := glueList_cons W p (q :: ps') hp'
      have hrhs₂ := glueList_cons (W.gluePair p.1 p.2 hp12)
        (⟨q.1, hik, hil⟩, ⟨q.2, hjk, hjl⟩)
        (coercePairsList p.1 p.2 ps' hsep_p_ps') hwf_p
      -- LHS: fold back two levels
      let ff_inner_qp := foldFlatten
        (⟨p.1, hik.symm, hjk.symm⟩ : SurvivingLabel α q.1 q.2)
        ⟨p.2, hil.symm, hjl.symm⟩ (coercePairsList q.1 q.2 ps' hsep_q_ps')
          hwf_q.sep
      let ff_outer_q := foldFlatten q.1 q.2 (p :: ps') hp.sep
      have lhs_fold := (Equiv.relabelTrans
        (glueList inner_qp _ hwf_dbl_qp) ff_inner_qp ff_outer_q).symm
      -- RHS: fold back two levels
      let inner_pq := (W.gluePair p.1 p.2 hp12).gluePair
            (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1 p.2) ⟨q.2, hjk, hjl⟩
            (fun h => hq12 (congrArg Subtype.val h))
      let ff_inner_pq := foldFlatten
        (⟨q.1, hik, hil⟩ : SurvivingLabel α p.1 p.2)
        ⟨q.2, hjk, hjl⟩ (coercePairsList p.1 p.2 ps' hsep_p_ps') hwf_p.sep
      let ff_outer_p := foldFlatten p.1 p.2 (q :: ps') hp'.sep
      have rhs_fold := (Equiv.relabelTrans
        (glueList inner_pq _ hwf_dbl_pq) ff_inner_pq ff_outer_p).symm
      exact ⟨(hlhs₁ ▸ hlhs₂ ▸ lhs_fold.symm).trans
        (decomposed.trans (Equiv.relabelCongr (hrhs₁ ▸ hrhs₂ ▸ rhs_fold)
          (foldSurvivingPermEquiv (List.Perm.swap p q ps')).symm))⟩
    -- ═══════ trans: compose two reorderings ═══════
    | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      have hlen₂ : l₂.length ≤ n + 1 := h₁.length_eq ▸ hlen
      have e₁ := (ih₁ W hp hlen).some
      have e₂ := (ih₂ W (hp.perm h₁) hlen₂).some
      have step₁ := e₁.trans
        (Equiv.relabelCongr e₂ (foldSurvivingPermEquiv h₁).symm)
      have step₂ := step₁.trans (Equiv.relabelTrans _ _ _)
      have hcomp : (foldSurvivingPermEquiv h₂).symm.trans
        (foldSurvivingPermEquiv h₁).symm =
          (foldSurvivingPermEquiv (h₁.trans h₂)).symm :=
        _root_.Equiv.ext (fun ⟨_, _⟩ => Subtype.ext rfl)
      exact ⟨hcomp ▸ step₂⟩

private theorem nonempty_glueList_perm {α : Type} (W : Fragment α)
    {ps qs : List (α × α)}
    (hperm : ps.Perm qs) (hp : PairsWF ps) :
    Nonempty ((glueList W ps hp).Equiv
      ((glueList W qs (hp.perm hperm)).relabel
        (foldSurvivingPermEquiv hperm).symm)) :=
  nonempty_glueList_perm_aux ps.length W hperm hp le_rfl

/-- The reorder theorem: gluing along a permuted pair list yields an
equivalent fragment (up to the canonical relabelling of survivors).
-/
noncomputable def glueListPerm (W : Fragment α) {ps qs : List (α × α)}
    (hperm : ps.Perm qs) (hp : PairsWF ps) :
    (glueList W ps hp).Equiv
      ((glueList W qs (hp.perm hperm)).relabel
        (foldSurvivingPermEquiv hperm).symm) :=
  (nonempty_glueList_perm W hperm hp).some

end Fragment

end RS
