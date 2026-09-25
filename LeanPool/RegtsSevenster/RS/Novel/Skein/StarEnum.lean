/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StarDecomposition

/-!
# The star union with a `Fin`-boundary

The explosion at the full cut, enumerated representatives-first:
each edge orbit contributes its canonical representative among the
first `m` boundary labels and its partner among the last `m`.
Under this enumeration the canonical matching becomes the straight
matching `i ↔ m + i`, so the star decomposition says that gluing
the straight matching in the star union restores the fragment —
the shape the trace calculus closes against the strand bundle.
-/

namespace RS

section StarEnum

variable (W : ClosedFragment)

/-- The number of edges: one canonical representative per orbit. -/
noncomputable abbrev edgeCount : ℕ := (canonicalReps W).length

/-- The representatives are pairwise distinct: one per edge orbit. -/
theorem canonicalReps_nodup : (canonicalReps W).Nodup :=
  Finset.nodup_toList _

/-- The partner of a representative is not a representative. -/
theorem pairing_notMem_canonicalReps {f : W.Flag}
    (h : f ∈ canonicalReps W) :
    W.pairing f ∉ canonicalReps W := by
  intro h2
  have h1 := (mem_canonicalReps W).mp h
  have h3 := (mem_canonicalReps W).mp h2
  rw [W.pairing_invol] at h3
  omega

/-- Every flag is a representative or the partner of one. -/
theorem mem_or_pairing_mem (f : W.Flag) :
    f ∈ canonicalReps W ∨ W.pairing f ∈ canonicalReps W := by
  have hne : (Fintype.equivFin W.Flag f : ℕ) ≠
      Fintype.equivFin W.Flag (W.pairing f) := fun he =>
    W.pairing_ne f (((Fintype.equivFin W.Flag).injective
      (Fin.ext he)).symm)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ((mem_canonicalReps W).mpr hlt)
  · refine Or.inr ((mem_canonicalReps W).mpr ?_)
    rw [W.pairing_invol]
    exact hgt

/-- The splitting map: a flag to its orbit representative, tagged
by which side of the orbit it sits on. -/
noncomputable def repSplitFun (f : W.Flag) :
    {x // x ∈ canonicalReps W} ⊕ {x // x ∈ canonicalReps W} :=
  if h : f ∈ canonicalReps W then Sum.inl ⟨f, h⟩
  else Sum.inr ⟨W.pairing f, (mem_or_pairing_mem W f).resolve_left h⟩

/-- The inverse splitting map. -/
def repSplitInv :
    ({x // x ∈ canonicalReps W} ⊕ {x // x ∈ canonicalReps W}) →
      W.Flag
  | Sum.inl x => x.val
  | Sum.inr x => W.pairing x.val

/-- The orbit split: a flag is a representative or a partner. -/
noncomputable def repSplitEquiv :
    W.Flag ≃
      {x // x ∈ canonicalReps W} ⊕ {x // x ∈ canonicalReps W} where
  toFun := repSplitFun W
  invFun := repSplitInv W
  left_inv f := by
    by_cases h : f ∈ canonicalReps W
    · have h1 : repSplitFun W f = Sum.inl ⟨f, h⟩ := dite_eq_left h
      rw [h1]
      rfl
    · have h1 : repSplitFun W f =
          Sum.inr ⟨W.pairing f,
            (mem_or_pairing_mem W f).resolve_left h⟩ := dite_eq_right h
      rw [h1]
      exact W.pairing_invol f
  right_inv s := by
    rcases s with x | x
    · change repSplitFun W x.val = Sum.inl x
      exact dite_eq_left x.prop
    · change repSplitFun W (W.pairing x.val) = Sum.inr x
      exact (dite_eq_right (pairing_notMem_canonicalReps W x.prop)).trans
        (congrArg Sum.inr (Subtype.ext (W.pairing_invol x.val)))

/-- The list-position equivalence of the representatives. -/
noncomputable def repIndexEquiv :
    {x // x ∈ canonicalReps W} ≃ Fin (edgeCount W) :=
  (List.Nodup.getEquiv (canonicalReps W) (canonicalReps_nodup W)).symm

/-- **The star enumeration**: representatives on the low labels,
partners on the high labels, in list order. -/
noncomputable def starEnum :
    {f : W.Flag // f ∈ (Finset.univ : Finset W.Flag)} ≃
      Fin (edgeCount W + edgeCount W) :=
  ((Equiv.subtypeUnivEquiv (fun f => Finset.mem_univ f)).trans
    (repSplitEquiv W)).trans
    ((Equiv.sumCongr (repIndexEquiv W) (repIndexEquiv W)).trans
      finSumFinEquiv)

/-- **The star union**: the explosion at the full cut with the
representatives-first boundary enumeration. -/
noncomputable def starUnion :
    Fragment (Fin (edgeCount W + edgeCount W)) :=
  (explodeAt W Finset.univ (fullCut_closed W)).relabel (starEnum W)

/-- The straight matching pairs `i ↔ m + i`. -/
def matchPairs (m : ℕ) : List (Fin (m + m) × Fin (m + m)) :=
  (List.finRange m).map (fun j => (Fin.castAdd m j, Fin.natAdd m j))

/-- The straight matching has one pair per edge. -/
theorem matchPairs_length (m : ℕ) : (matchPairs m).length = m := by
  simp [matchPairs]

/-- Its `j`th pair is `(j, m + j)`. -/
theorem matchPairs_getElem (m j : ℕ)
    (hj : j < (matchPairs m).length) (hj' : j < m) :
    (matchPairs m)[j]'hj =
      (Fin.castAdd m ⟨j, hj'⟩, Fin.natAdd m ⟨j, hj'⟩) := by
  simp [matchPairs]

/-- Transporting a pair list along an equivalence keeps its
length. -/
theorem mapPairs_length {α β : Type} (e : α ≃ β)
    (ps : List (α × α)) :
    (Fragment.mapPairs e ps).length = ps.length := by
  simp [Fragment.mapPairs]

/-- And moves each pair componentwise. -/
theorem mapPairs_getElem {α β : Type} (e : α ≃ β)
    (ps : List (α × α)) (j : ℕ)
    (hj : j < (Fragment.mapPairs e ps).length)
    (hj' : j < ps.length) :
    (Fragment.mapPairs e ps)[j]'hj =
      (e (ps[j]'hj').1, e (ps[j]'hj').2) := by
  simp [Fragment.mapPairs, Prod.map]

/-! ### The enumeration sends the canonical matching to the
straight matching -/

/-- **The `j`th representative gets the low label `j`.** -/
theorem starEnum_rep (j : ℕ) (hj : j < (canonicalReps W).length) :
    starEnum W ⟨(canonicalReps W)[j]'hj, Finset.mem_univ _⟩ =
      Fin.castAdd (edgeCount W) ⟨j, hj⟩ := by
  have hmem : (canonicalReps W)[j]'hj ∈ canonicalReps W :=
    List.getElem_mem hj
  change finSumFinEquiv
    ((Equiv.sumCongr (repIndexEquiv W) (repIndexEquiv W))
      (repSplitEquiv W ((canonicalReps W)[j]'hj))) = _
  have h1 : repSplitEquiv W ((canonicalReps W)[j]'hj) =
      Sum.inl ⟨(canonicalReps W)[j]'hj, hmem⟩ := dite_eq_left hmem
  rw [h1, Equiv.sumCongr_apply, Sum.map_inl]
  have h2 : repIndexEquiv W ⟨(canonicalReps W)[j]'hj, hmem⟩ =
      ⟨j, hj⟩ := by
    rw [show (⟨(canonicalReps W)[j]'hj, hmem⟩ :
        {x // x ∈ canonicalReps W}) =
        List.Nodup.getEquiv (canonicalReps W)
          (canonicalReps_nodup W) ⟨j, hj⟩ from Subtype.ext rfl]
    exact Equiv.symm_apply_apply _ _
  rw [h2]
  exact finSumFinEquiv_apply_left ⟨j, hj⟩

/-- **Its partner gets the high label `m + j`** — so the canonical
matching becomes the straight one. -/
theorem starEnum_partner (j : ℕ)
    (hj : j < (canonicalReps W).length) :
    starEnum W ⟨W.pairing ((canonicalReps W)[j]'hj),
        Finset.mem_univ _⟩ =
      Fin.natAdd (edgeCount W) ⟨j, hj⟩ := by
  have hmem : (canonicalReps W)[j]'hj ∈ canonicalReps W :=
    List.getElem_mem hj
  have hnot : W.pairing ((canonicalReps W)[j]'hj) ∉
      canonicalReps W :=
    pairing_notMem_canonicalReps W hmem
  change finSumFinEquiv
    ((Equiv.sumCongr (repIndexEquiv W) (repIndexEquiv W))
      (repSplitEquiv W (W.pairing ((canonicalReps W)[j]'hj)))) = _
  have h1 : repSplitEquiv W (W.pairing ((canonicalReps W)[j]'hj)) =
      Sum.inr ⟨W.pairing (W.pairing ((canonicalReps W)[j]'hj)),
        (mem_or_pairing_mem W _).resolve_left hnot⟩ :=
    dite_eq_right hnot
  rw [h1, Equiv.sumCongr_apply, Sum.map_inr]
  have h2 : repIndexEquiv W
      ⟨W.pairing (W.pairing ((canonicalReps W)[j]'hj)),
        (mem_or_pairing_mem W _).resolve_left hnot⟩ = ⟨j, hj⟩ := by
    rw [show (⟨W.pairing (W.pairing ((canonicalReps W)[j]'hj)),
        (mem_or_pairing_mem W _).resolve_left hnot⟩ :
        {x // x ∈ canonicalReps W}) =
        List.Nodup.getEquiv (canonicalReps W)
          (canonicalReps_nodup W) ⟨j, hj⟩ from
      Subtype.ext (by
        change W.pairing (W.pairing ((canonicalReps W)[j]'hj)) = _
        rw [W.pairing_invol]
        rfl)]
    exact Equiv.symm_apply_apply _ _
  rw [h2]
  exact finSumFinEquiv_apply_right ⟨j, hj⟩

/-- The representative pair list has one pair per listed flag. -/
theorem repPairs_length (C : Finset W.Flag) (hC : CutClosed W C) :
    ∀ (l : List W.Flag) (h : ∀ x ∈ l, x ∈ C),
      (repPairs W C hC l h).length = l.length
  | [], _ => rfl
  | _ :: l, _ => congrArg Nat.succ (repPairs_length C hC l _)

/-- And its `j`th pair is that flag with its partner. -/
theorem repPairs_getElem (C : Finset W.Flag) (hC : CutClosed W C) :
    ∀ (l : List W.Flag) (h : ∀ x ∈ l, x ∈ C) (j : ℕ)
      (hj : j < (repPairs W C hC l h).length)
      (hj' : j < l.length),
      (repPairs W C hC l h)[j]'hj =
        (⟨l[j]'hj', h _ (List.getElem_mem hj')⟩,
         ⟨W.pairing (l[j]'hj'),
           hC _ (h _ (List.getElem_mem hj'))⟩)
  | [], _, j, hj, _ => absurd hj (by simp [repPairs])
  | x :: l, h, 0, _, _ => rfl
  | x :: l, h, j + 1, hj, hj' => by
    change (repPairs W C hC l _)[j]'_ = _
    exact repPairs_getElem C hC l _ j _ (by simpa using hj')

/-- The enumerated canonical matching is the straight matching. -/
theorem mapPairs_repPairs :
    Fragment.mapPairs (starEnum W)
      (repPairs W Finset.univ (fullCut_closed W) (canonicalReps W)
        (fun _ _ => Finset.mem_univ _)) =
      matchPairs (edgeCount W) := by
  have hlen : (Fragment.mapPairs (starEnum W)
      (repPairs W Finset.univ (fullCut_closed W) (canonicalReps W)
        (fun _ _ => Finset.mem_univ _))).length =
      (matchPairs (edgeCount W)).length := by
    rw [mapPairs_length,
      repPairs_length W Finset.univ (fullCut_closed W),
      matchPairs_length]
  apply List.ext_getElem hlen
  intro j hj hj'
  have hjr : j < (canonicalReps W).length := by
    rw [mapPairs_length,
      repPairs_length W Finset.univ (fullCut_closed W)] at hj
    exact hj
  have hjp : j < (repPairs W Finset.univ (fullCut_closed W)
      (canonicalReps W) (fun _ _ => Finset.mem_univ _)).length := by
    rw [repPairs_length W Finset.univ (fullCut_closed W)]
    exact hjr
  rw [mapPairs_getElem (starEnum W) _ j hj hjp,
    repPairs_getElem W Finset.univ (fullCut_closed W)
      (canonicalReps W) _ j hjp hjr,
    matchPairs_getElem (edgeCount W) j hj' hjr]
  exact Prod.ext (starEnum_rep W j hjr) (starEnum_partner W j hjr)

/-! ### The transported star decomposition -/

/-- The straight matching is a well-formed gluing list on the star
union: it is the transported canonical list. -/
theorem matchPairs_wf_star :
    Fragment.PairsWF (matchPairs (edgeCount W)) :=
  mapPairs_repPairs W ▸
    Fragment.mapPairs_wf (starEnum W) _ (canonicalReps_wf W)

/-- Gluing the straight matching in the star union leaves no
surviving label: the fold consumes the whole boundary, which is
what makes the decomposition restore the fragment. -/
theorem starUnion_surv_isEmpty :
    IsEmpty (Fragment.FoldSurviving
      (Fin (edgeCount W + edgeCount W)) (matchPairs (edgeCount W))) := by
  have e := Fragment.foldSurvivingMapEquiv (starEnum W)
    (repPairs W Finset.univ (fullCut_closed W) (canonicalReps W)
      (fun _ _ => Finset.mem_univ _))
  rw [mapPairs_repPairs W] at e
  have := canonical_surv_isEmpty W
  exact Function.isEmpty e.symm

/-- **The star union self-glue**: gluing the straight matching in
the star union restores the fragment. -/
theorem starUnion_reglue :
    Nonempty ((Fragment.glueList (starUnion W)
        (matchPairs (edgeCount W)) (matchPairs_wf_star W)).Equiv
      (W.relabel
        (haveI := starUnion_surv_isEmpty W
         Equiv.equivOfIsEmpty (Fin 0) _))) := by
  have := starUnion_surv_isEmpty W
  obtain ⟨D⟩ := starDecomposition W
  have G := Fragment.glueListRelabel
    (explodeAt W Finset.univ (fullCut_closed W)) (starEnum W)
    (repPairs W Finset.univ (fullCut_closed W) (canonicalReps W)
      (fun _ _ => Finset.mem_univ _))
    (canonicalReps_wf W)
  have E := Fragment.glueListEqEquiv (starUnion W)
    (mapPairs_repPairs W)
    (Fragment.mapPairs_wf (starEnum W) _ (canonicalReps_wf W))
    (matchPairs_wf_star W)
    (List.Perm.of_eq (mapPairs_repPairs W))
  refine ⟨?_⟩
  refine (E.symm.trans ?_)
  refine (Fragment.Equiv.relabelCongr G _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelCongr D _) _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelTrans W _ _) _).trans ?_
  refine (Fragment.Equiv.relabelTrans W _ _).trans ?_
  exact Fragment.Equiv.relabelEq W
    (_root_.Equiv.ext (fun i => i.elim0))

end StarEnum

end RS
