/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereClosePair

/-!
# HardSphereForkPackingCoordinates

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

namespace HsVirial

open Set
open Metric
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

lemma hardSphereReindexedBlockCoordinateEquiv_fst_apply
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n)
    (x : Fin n → HSPosition 3) (i : Fin m) :
    ((hardSphereReindexedBlockCoordinateEquiv e x).1 i).1 =
      x (e (Fin.castAdd q (@finProdFinEquiv m 2 (i, 0)))) := by
  rfl

lemma hardSphereReindexedBlockCoordinateEquiv_snd_apply
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n)
    (x : Fin n → HSPosition 3) (i : Fin m) :
    ((hardSphereReindexedBlockCoordinateEquiv e x).1 i).2 =
      x (e (Fin.castAdd q (@finProdFinEquiv m 2 (i, 1)))) := by
  rfl

lemma hardSphereBlockCoordinateEquiv_fst_apply
    (m q : Nat) (x : Fin (m * 2 + q) → HSPosition 3) (i : Fin m) :
    ((hardSphereBlockCoordinateEquiv m q x).1 i).1 =
      x (Fin.castAdd q (@finProdFinEquiv m 2 (i, 0))) := by
  rfl

lemma hardSphereBlockCoordinateEquiv_snd_apply
    (m q : Nat) (x : Fin (m * 2 + q) → HSPosition 3) (i : Fin m) :
    ((hardSphereBlockCoordinateEquiv m q x).1 i).2 =
      x (Fin.castAdd q (@finProdFinEquiv m 2 (i, 1))) := by
  rfl

lemma hardSphereBlockCoordinateEquiv_complement_apply
    (m q : Nat) (x : Fin (m * 2 + q) → HSPosition 3) (i : Fin q) :
    (hardSphereBlockCoordinateEquiv m q x).2 i =
      x (Fin.natAdd (m * 2) i) := by
  rfl

lemma hardSphereReindexedBlockCoordinateEquiv_symm_apply
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n)
    (x : Fin n → HSPosition 3) (i : Fin (m * 2 + q)) :
      (hardSphereBlockCoordinateEquiv m q).symm
        (hardSphereReindexedBlockCoordinateEquiv e x) i =
      x (e i) := by
  simp [hardSphereReindexedBlockCoordinateEquiv, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply]

/-- The rooted tree-difference coordinate carrying a fixed tree edge. -/
noncomputable def hardSphereTreeEdgeIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (e : Sym2 (Fin k)) (he : e ∈ T) : Fin (k - 1) := by
  classical
  have he' : e ∈ hardSphereTreeParentEdgeFinset hT := by
    rw [hardSphereTreeParentEdgeFinset_eq hT]
    exact he
  exact (Finset.mem_image.mp he').choose

lemma hardSphereTreeParentEdge_hardSphereTreeEdgeIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (e : Sym2 (Fin k)) (he : e ∈ T) :
    hardSphereTreeParentEdge hT (hardSphereTreeEdgeIndex hT e he) = e := by
  classical
  unfold hardSphereTreeEdgeIndex
  have he' : e ∈ hardSphereTreeParentEdgeFinset hT := by
    rw [hardSphereTreeParentEdgeFinset_eq hT]
    exact he
  exact (Finset.mem_image.mp he').choose_spec.2

/-- The two tree edges used by an order-compatible fork. -/
def hardSphereForkMemberVertex {k : Nat}
    (f : HardSphereForkTriple k) (j : Fin 2) : Fin k :=
  if j = 0 then f.2.1 else f.2.2

/-- Choose one of the two center-to-leaf edges of a fork. -/
def hardSphereForkMemberEdge {k : Nat}
    (f : HardSphereForkTriple k) (j : Fin 2) : Sym2 (Fin k) :=
  if j = 0 then s(f.1, f.2.1) else s(f.1, f.2.2)

lemma hardSphereForkMemberEdge_eq {k : Nat}
    (f : HardSphereForkTriple k) (j : Fin 2) :
    hardSphereForkMemberEdge f j =
      s(f.1, hardSphereForkMemberVertex f j) := by
  fin_cases j <;> rfl

lemma hardSphereForkMemberEdge_mem {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P)
    {f : HardSphereForkTriple k} (hf : f ∈ P) (j : Fin 2) :
    hardSphereForkMemberEdge f j ∈ T := by
  fin_cases j
  · simpa [hardSphereForkMemberEdge] using (hP.1 f hf).2.2.1
  · simpa [hardSphereForkMemberEdge] using (hP.1 f hf).2.2.2

/-- The tree-difference coordinate corresponding to a fork edge. -/
noncomputable def hardSphereForkMemberIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (f : HardSphereForkTriple k) (j : Fin 2)
    (he : hardSphereForkMemberEdge f j ∈ T) : Fin (k - 1) :=
  hardSphereTreeEdgeIndex hT _ he

lemma hardSphereTreeParentEdge_hardSphereForkMemberIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (f : HardSphereForkTriple k) (j : Fin 2)
    (he : hardSphereForkMemberEdge f j ∈ T) :
    hardSphereTreeParentEdge hT
        (hardSphereForkMemberIndex hT f j he) =
      hardSphereForkMemberEdge f j := by
  exact hardSphereTreeParentEdge_hardSphereTreeEdgeIndex hT _ he

/-- Whether the tree orientation of a fork edge opposes its center-to-leaf orientation. -/
noncomputable def hardSphereForkMemberReversed {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (f : HardSphereForkTriple k) (j : Fin 2)
    (he : hardSphereForkMemberEdge f j ∈ T) : Bool :=
  decide (hardSphereTreeParent hT
      (hardSphereForkMemberIndex hT f j he) ≠ f.1)

lemma hardSphereForkMember_oriented_difference {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P)
    {f : HardSphereForkTriple k} (hf : f ∈ P) (j : Fin 2)
    (he : hardSphereForkMemberEdge f j ∈ T)
    (r : HardSphereConfiguration k 3) :
    (if hardSphereForkMemberReversed hT f j he then
        -hardSphereTreeDifference hT r
          (hardSphereForkMemberIndex hT f j he)
      else
        hardSphereTreeDifference hT r
          (hardSphereForkMemberIndex hT f j he)) =
      hardSpherePosition r (hardSphereForkMemberVertex f j) -
        hardSpherePosition r f.1 := by
  have hfork := hP.1 f hf
  have hedge := hardSphereTreeParentEdge_hardSphereForkMemberIndex hT f j he
  rw [hardSphereForkMemberEdge_eq] at hedge
  rcases Sym2.eq_iff.mp hedge with hsame | hcross
  · have hparent : hardSphereTreeParent hT
        (hardSphereForkMemberIndex hT f j he) = f.1 := hsame.1
    have hchild : hardSphereFreeParticleIndex
        (hardSphereForkMemberIndex hT f j he) =
      hardSphereForkMemberVertex f j := hsame.2
    simp [hardSphereForkMemberReversed, hparent,
      hardSphereTreeDifference, hchild]
  · have hparent : hardSphereTreeParent hT
        (hardSphereForkMemberIndex hT f j he) =
      hardSphereForkMemberVertex f j := hcross.1
    have hchild : hardSphereFreeParticleIndex
        (hardSphereForkMemberIndex hT f j he) = f.1 := hcross.2
    have hne : hardSphereForkMemberVertex f j ≠ f.1 := by
      fin_cases j
      · exact ne_of_gt hfork.1
      · exact ne_of_gt (lt_trans hfork.1 hfork.2.1)
    simp [hardSphereForkMemberReversed, hparent, hne,
      hardSphereTreeDifference, hchild]

/-- Assign tree-difference coordinates to the two members of each packed fork. -/
noncomputable def hardSphereForkPackingMemberIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    P × Fin 2 → Fin (k - 1) :=
  fun z => hardSphereForkMemberIndex hT z.1.1 z.2
    (hardSphereForkMemberEdge_mem hP z.1.2 z.2)

lemma hardSphereForkPackingMemberIndex_injective {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P) :
    Function.Injective (hardSphereForkPackingMemberIndex hT hP) := by
  classical
  rintro ⟨⟨f, hf⟩, j⟩ ⟨⟨g, hg⟩, l⟩ hidx
  have hedge : hardSphereForkMemberEdge f j =
      hardSphereForkMemberEdge g l := by
    have h := congrArg (hardSphereTreeParentEdge hT) hidx
    dsimp [hardSphereForkPackingMemberIndex] at h
    rw [hardSphereTreeParentEdge_hardSphereForkMemberIndex,
      hardSphereTreeParentEdge_hardSphereForkMemberIndex] at h
    exact h
  by_cases hfg : f = g
  · subst g
    have hfork := hP.1 f hf
    apply Prod.ext
    · rfl
    · fin_cases j <;> fin_cases l
      · rfl
      · exfalso
        rcases (Sym2.eq_iff.mp hedge) with h | h
        · exact (ne_of_lt hfork.2.1) h.2
        · exact (ne_of_gt hfork.1) h.2
      · exfalso
        rcases (Sym2.eq_iff.mp hedge) with h | h
        · exact (ne_of_gt hfork.2.1) h.2
        · exact (ne_of_lt hfork.1) h.1
      · rfl
  · exfalso
    have hnot : f.1 ∉ (hardSphereForkSupport g : Set (Fin k)) := by
      intro hmem
      exact hP.2 f hf g hg hfg f.1
        (by simp [hardSphereForkSupport]) hmem
    fin_cases j <;> fin_cases l
    all_goals
      rcases (Sym2.eq_iff.mp hedge) with h | h
      · exact hnot (by simp [hardSphereForkSupport, h.1])
      · exact hnot (by simp [hardSphereForkSupport, h.1])

/-- Index packed fork members using the finite enumeration of the packing. -/
noncomputable def hardSphereForkPackingMemberIndexFin {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
  (hP : hardSphereForkPacking T P) :
    (Fin P.card × Fin 2) → Fin (k - 1) :=
  fun z => hardSphereForkPackingMemberIndex hT hP
    (P.equivFin.symm z.1, z.2)

/-- The orientation correction for an enumerated packed fork edge. -/
noncomputable def hardSphereForkPackingMemberReversed {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin P.card) (j : Fin 2) : Bool :=
  hardSphereForkMemberReversed hT (P.equivFin.symm i) j
    (hardSphereForkMemberEdge_mem hP (P.equivFin.symm i).property j)

lemma hardSphereForkPackingMember_oriented_difference {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P)
    (i : Fin P.card) (j : Fin 2) (r : HardSphereConfiguration k 3) :
    (if hardSphereForkPackingMemberReversed hT hP i j then
        -hardSphereTreeDifference hT r
          (hardSphereForkPackingMemberIndexFin hT hP (i, j))
      else
        hardSphereTreeDifference hT r
          (hardSphereForkPackingMemberIndexFin hT hP (i, j))) =
      hardSpherePosition r
          (hardSphereForkMemberVertex (P.equivFin.symm i).val j) -
        hardSpherePosition r (P.equivFin.symm i).val.1 := by
  convert (hardSphereForkMember_oriented_difference (hT := hT) hP
      (P.equivFin.symm i).property j
      (hardSphereForkMemberEdge_mem hP (P.equivFin.symm i).property j) r) using 1
  rfl

lemma hardSphereForkPackingMemberIndexFin_injective {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P) :
    Function.Injective (hardSphereForkPackingMemberIndexFin hT hP) := by
  intro z w h
  change hardSphereForkPackingMemberIndex hT hP
      (P.equivFin.symm z.1, z.2) =
    hardSphereForkPackingMemberIndex hT hP
      (P.equivFin.symm w.1, w.2) at h
  have h' := hardSphereForkPackingMemberIndex_injective (hT := hT) hP h
  apply Prod.ext
  · simpa using congrArg P.equivFin (congrArg Prod.fst h')
  · simpa using congrArg Prod.snd h'

/-- Flatten the two coordinate indices per packed fork into one finite index. -/
noncomputable def hardSphereForkPackingFlatMemberIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    Fin (P.card * 2) → Fin (k - 1) :=
  fun z => hardSphereForkPackingMemberIndexFin hT hP
    ((@finProdFinEquiv P.card 2).symm z)

lemma hardSphereForkPackingFlatMemberIndex_injective {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P) :
    Function.Injective (hardSphereForkPackingFlatMemberIndex hT hP) := by
  intro z w h
  change hardSphereForkPackingMemberIndexFin hT hP
      ((@finProdFinEquiv P.card 2).symm z) =
    hardSphereForkPackingMemberIndexFin hT hP
      ((@finProdFinEquiv P.card 2).symm w) at h
  have h' := hardSphereForkPackingMemberIndexFin_injective (hT := hT) hP h
  exact (@finProdFinEquiv P.card 2).symm.injective h'

/-- The set of tree coordinates used by the fork packing. -/
noncomputable def hardSphereForkPackingSelectedIndices {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) : Finset (Fin (k - 1)) :=
  (Finset.univ : Finset (Fin (P.card * 2))).image
    (hardSphereForkPackingFlatMemberIndex hT hP)

lemma hardSphereForkPackingSelectedIndices_card {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P) :
    (hardSphereForkPackingSelectedIndices hT hP).card = P.card * 2 := by
  unfold hardSphereForkPackingSelectedIndices
  rw [Finset.card_image_of_injective _
    (hardSphereForkPackingFlatMemberIndex_injective (hT := hT) hP)]
  simp

/-- The bijection from packed edge indices to their selected tree coordinates. -/
noncomputable def hardSphereForkPackingSelectedEquiv {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    Fin (P.card * 2) ≃ hardSphereForkPackingSelectedIndices hT hP := by
  let g := hardSphereForkPackingFlatMemberIndex hT hP
  apply Equiv.ofBijective
    (fun i => ⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  constructor
  · intro i j hij
    apply hardSphereForkPackingFlatMemberIndex_injective (hT := hT) hP
    exact congrArg Subtype.val hij
  · intro x
    rcases Finset.mem_image.mp x.property with ⟨i, hi, hix⟩
    refine ⟨i, ?_⟩
    exact Subtype.ext hix

/-- The number of tree coordinates not used by the fork packing. -/
noncomputable def hardSphereForkPackingComplementCard {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) : Nat :=
  Fintype.card {i : Fin (k - 1) //
    i ∉ hardSphereForkPackingSelectedIndices hT hP}

lemma hardSphereForkPackingComplementCard_eq {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    {hT : T ∈ treeUniverse (V := Fin k)}
    (hP : hardSphereForkPacking T P) :
    hardSphereForkPackingComplementCard hT hP =
      (k - 1) - P.card * 2 := by
  unfold hardSphereForkPackingComplementCard
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin]
  rw [show Fintype.card {i : Fin (k - 1) //
      i ∈ hardSphereForkPackingSelectedIndices hT hP} =
      (hardSphereForkPackingSelectedIndices hT hP).card by simp,
    hardSphereForkPackingSelectedIndices_card (hT := hT) hP]

/-- Reindex tree coordinates with packed fork edges first and unused edges last. -/
noncomputable def hardSphereForkPackingIndexEquiv {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) ≃
      Fin (k - 1) := by
  let S := hardSphereForkPackingSelectedIndices hT hP
  let C := {i : Fin (k - 1) // i ∉ S}
  let eSelected : Fin (P.card * 2) ≃ S :=
    hardSphereForkPackingSelectedEquiv hT hP
  let eComplement : Fin (hardSphereForkPackingComplementCard hT hP) ≃ C :=
    (Fintype.equivFin C).symm
  let eSum : Fin (P.card * 2) ⊕
      Fin (hardSphereForkPackingComplementCard hT hP) ≃ Fin (k - 1) :=
    (eSelected.sumCongr eComplement).trans
      (Equiv.sumCompl (fun i : Fin (k - 1) => i ∈ S))
  exact (@finSumFinEquiv (P.card * 2)
      (hardSphereForkPackingComplementCard hT hP)).symm.trans eSum

lemma hardSphereForkPackingIndexEquiv_member {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin P.card) (j : Fin 2) :
    hardSphereForkPackingIndexEquiv hT hP
        (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
          (@finProdFinEquiv P.card 2 (i, j))) =
    hardSphereForkPackingMemberIndexFin hT hP (i, j) := by
  have hfin := (@finProdFinEquiv P.card 2).symm_apply_apply (i, j)
  have hfirst := congrArg Prod.fst hfin
  have hsecond := congrArg Prod.snd hfin
  have hdiv : (@finProdFinEquiv P.card 2 (i, j)).divNat = i := by
    change (@finProdFinEquiv P.card 2 (i, j)).divNat = i at hfirst
    exact hfirst
  have hmod : (@finProdFinEquiv P.card 2 (i, j)).modNat = j := by
    change (@finProdFinEquiv P.card 2 (i, j)).modNat = j at hsecond
    exact hsecond
  simp only [hardSphereForkPackingIndexEquiv, hardSphereForkPackingSelectedIndices,
    Equiv.sumCongr, hardSphereForkPackingSelectedEquiv, Equiv.ofBijective,
    hardSphereForkPackingFlatMemberIndex, hardSphereForkPackingMemberIndexFin,
    finProdFinEquiv_symm_apply, Equiv.symm_mk, Equiv.sumCompl, Finset.mem_image, Finset.mem_univ,
    true_and, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.coe_fn_mk, Sum.map_inl,
    Sum.elim_inl]
  change hardSphereForkPackingMemberIndex hT hP
      (P.equivFin.symm (@finProdFinEquiv P.card 2 (i, j)).divNat,
        (@finProdFinEquiv P.card 2 (i, j)).modNat) = _
  rw [hdiv, hmod]

lemma hardSphereForkPackingIndexEquiv_selected_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin (P.card * 2)) :
    hardSphereForkPackingIndexEquiv hT hP
        (Fin.castAdd (hardSphereForkPackingComplementCard hT hP) i) =
      hardSphereForkPackingFlatMemberIndex hT hP i := by
  simp [hardSphereForkPackingIndexEquiv, hardSphereForkPackingSelectedEquiv,
    hardSphereForkPackingSelectedIndices, Equiv.sumCongr, Equiv.sumCompl, Equiv.ofBijective]
  rfl

lemma hardSphereForkPackingIndexEquiv_complement_not_mem {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin (hardSphereForkPackingComplementCard hT hP)) :
    hardSphereForkPackingIndexEquiv hT hP
        (Fin.natAdd (P.card * 2) i) ∉
      hardSphereForkPackingSelectedIndices hT hP := by
  simp only [hardSphereForkPackingSelectedIndices, hardSphereForkPackingIndexEquiv,
    Equiv.sumCongr, hardSphereForkPackingSelectedEquiv, Equiv.ofBijective, Equiv.symm_mk,
    Equiv.sumCompl, Finset.mem_image, Finset.mem_univ, true_and, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.coe_fn_mk, Sum.map_inr, Sum.elim_inr, not_exists]
  intro x hx
  have hnot := ((Fintype.equivFin {x : Fin (k - 1) //
      x ∉ hardSphereForkPackingSelectedIndices hT hP}).symm i).property
  apply hnot
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩

/-- Group tree-difference coordinates into packed pairs and remaining single coordinates. -/
noncomputable def hardSphereForkPackingRawBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    HardSphereConfiguration k 3 →
      ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3)) :=
  (hardSphereReindexedBlockCoordinateEquiv
    (hardSphereForkPackingIndexEquiv hT hP)) ∘
    (hardSphereTreeDifferencePositionMap hT)

lemma measurePreserving_hardSphereForkPackingRawBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    MeasurePreserving (hardSphereForkPackingRawBlockMap hT hP)
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))) := by
  change MeasurePreserving
    ((hardSphereReindexedBlockCoordinateEquiv
      (hardSphereForkPackingIndexEquiv hT hP)) ∘
      (hardSphereTreeDifferencePositionMap hT)) volume volume
  exact (measurePreserving_hardSphereReindexedBlockCoordinateEquiv
    (hardSphereForkPackingIndexEquiv hT hP)).comp
    (measurePreserving_hardSphereTreeDifferencePositionMap hT)

lemma hardSphereForkPackingRawBlockMap_flat_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (r : HardSphereConfiguration k 3)
    (i : Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP)) :
    (hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)).symm
        (hardSphereForkPackingRawBlockMap hT hP r) i =
      hardSphereTreeDifferencePositionMap hT r
        (hardSphereForkPackingIndexEquiv hT hP i) := by
  change (hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)).symm
        (hardSphereReindexedBlockCoordinateEquiv (hardSphereForkPackingIndexEquiv hT hP)
          (hardSphereTreeDifferencePositionMap hT r)) i = _
  rw [hardSphereReindexedBlockCoordinateEquiv_symm_apply]

/-- Negate a position exactly when the orientation flag requests reversal. -/
def hardSphereApplyReversal (reverse : Bool) (x : HSPosition 3) : HSPosition 3 :=
  if reverse then -x else x

lemma measurePreserving_hardSphereApplyReversal (reverse : Bool) :
    MeasurePreserving (hardSphereApplyReversal reverse)
      (volume : Measure (HSPosition 3))
      (volume : Measure (HSPosition 3)) := by
  cases reverse
  · change MeasurePreserving (fun x : HSPosition 3 => x) volume volume
    exact MeasurePreserving.id volume
  · change MeasurePreserving (fun x : HSPosition 3 => -x) volume volume
    exact Measure.measurePreserving_neg volume

/-- The orientation reversal flag for a flattened packed coordinate. -/
noncomputable def hardSphereForkPackingFlatReversed {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
  (i : Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP)) : Bool :=
  if hi : i.val < P.card * 2 then
    let ij := (@finProdFinEquiv P.card 2).symm ⟨i.val, hi⟩
    hardSphereForkPackingMemberReversed hT hP ij.1 ij.2
  else
    false

/-- Apply all orientation corrections to the flattened tree coordinates. -/
noncomputable def hardSphereForkPackingFlatSignMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    (Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) → HSPosition 3) →
      (Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) → HSPosition 3) :=
  fun x i => hardSphereApplyReversal (hardSphereForkPackingFlatReversed hT hP i) (x i)

lemma hardSphereForkPackingFlatReversed_member {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin P.card) (j : Fin 2) :
    hardSphereForkPackingFlatReversed hT hP
        (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
          (@finProdFinEquiv P.card 2 (i, j))) =
      hardSphereForkPackingMemberReversed hT hP i j := by
  unfold hardSphereForkPackingFlatReversed
  have hi :
      (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
          (@finProdFinEquiv P.card 2 (i, j))).val < P.card * 2 := by
    exact (@finProdFinEquiv P.card 2 (i, j)).isLt
  rw [dite_eq_left hi]
  dsimp
  rw [(@finProdFinEquiv P.card 2).symm_apply_apply]

lemma hardSphereForkPackingFlatReversed_complement {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (i : Fin (hardSphereForkPackingComplementCard hT hP)) :
    hardSphereForkPackingFlatReversed hT hP
        (Fin.natAdd (P.card * 2) i) = false := by
  unfold hardSphereForkPackingFlatReversed
  rw [dite_eq_right]
  simp [Fin.natAdd]

lemma measurePreserving_hardSphereForkPackingFlatSignMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    MeasurePreserving (hardSphereForkPackingFlatSignMap hT hP)
      (volume : Measure (Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) →
        HSPosition 3))
      (volume : Measure (Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) →
        HSPosition 3)) := by
  change MeasurePreserving
    (fun (x : Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP) → HSPosition 3)
        (i : Fin (P.card * 2 + hardSphereForkPackingComplementCard hT hP)) =>
      hardSphereApplyReversal (hardSphereForkPackingFlatReversed hT hP i) (x i)) volume volume
  exact volume_preserving_pi (fun i =>
    measurePreserving_hardSphereApplyReversal
      (hardSphereForkPackingFlatReversed hT hP i))

/-- Group the orientation-corrected coordinates into fork pairs and single positions. -/
noncomputable def hardSphereForkPackingSignedBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3)) →
      ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3)) :=
  (hardSphereBlockCoordinateEquiv P.card
    (hardSphereForkPackingComplementCard hT hP)) ∘
    (hardSphereForkPackingFlatSignMap hT hP) ∘
    (hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)).symm

lemma measurePreserving_hardSphereForkPackingSignedBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    MeasurePreserving (hardSphereForkPackingSignedBlockMap hT hP)
      (volume : Measure ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3)))
      (volume : Measure ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))) := by
  let e := hardSphereBlockCoordinateEquiv P.card
    (hardSphereForkPackingComplementCard hT hP)
  have he := measurePreserving_hardSphereBlockCoordinateEquiv P.card
    (hardSphereForkPackingComplementCard hT hP)
  have he' := MeasurePreserving.symm e he
  have hflat := measurePreserving_hardSphereForkPackingFlatSignMap hT hP
  change MeasurePreserving (e ∘ hardSphereForkPackingFlatSignMap hT hP ∘ e.symm)
    volume volume
  simpa [Function.comp_def] using he.comp (hflat.comp he')

lemma hardSphereForkPackingSignedBlockMap_fst_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (z : (Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))
    (i : Fin P.card) :
    ((hardSphereForkPackingSignedBlockMap hT hP z).1 i).1 =
      hardSphereApplyReversal
        (hardSphereForkPackingFlatReversed hT hP
          (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
            (@finProdFinEquiv P.card 2 (i, 0))))
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z
          (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
            (@finProdFinEquiv P.card 2 (i, 0)))) := by
  change ((hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)
      (hardSphereForkPackingFlatSignMap hT hP
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z))).1 i).1 = _
  rw [hardSphereBlockCoordinateEquiv_fst_apply]
  rfl

lemma hardSphereForkPackingSignedBlockMap_snd_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (z : (Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))
    (i : Fin P.card) :
    ((hardSphereForkPackingSignedBlockMap hT hP z).1 i).2 =
      hardSphereApplyReversal
        (hardSphereForkPackingFlatReversed hT hP
          (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
            (@finProdFinEquiv P.card 2 (i, 1))))
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z
          (Fin.castAdd (hardSphereForkPackingComplementCard hT hP)
            (@finProdFinEquiv P.card 2 (i, 1)))) := by
  change ((hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)
      (hardSphereForkPackingFlatSignMap hT hP
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z))).1 i).2 = _
  rw [hardSphereBlockCoordinateEquiv_snd_apply]
  rfl

lemma hardSphereForkPackingSignedBlockMap_complement_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (z : (Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))
    (i : Fin (hardSphereForkPackingComplementCard hT hP)) :
    (hardSphereForkPackingSignedBlockMap hT hP z).2 i =
      hardSphereApplyReversal
        (hardSphereForkPackingFlatReversed hT hP
          (Fin.natAdd (P.card * 2) i))
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z
          (Fin.natAdd (P.card * 2) i)) := by
  change (hardSphereBlockCoordinateEquiv P.card
      (hardSphereForkPackingComplementCard hT hP)
      (hardSphereForkPackingFlatSignMap hT hP
        ((hardSphereBlockCoordinateEquiv P.card
          (hardSphereForkPackingComplementCard hT hP)).symm z))).2 i = _
  rw [hardSphereBlockCoordinateEquiv_complement_apply]
  rfl

/-- The configuration-to-block map used for the simultaneous fork volume estimate. -/
noncomputable def hardSphereForkPackingBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    HardSphereConfiguration k 3 →
      ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3)) :=
  (hardSphereForkPackingSignedBlockMap hT hP) ∘
    (hardSphereForkPackingRawBlockMap hT hP)

lemma hardSphereForkPackingBlockMap_fst_member_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (r : HardSphereConfiguration k 3) (i : Fin P.card) :
    ((hardSphereForkPackingBlockMap hT hP r).1 i).1 =
      hardSpherePosition r
          (hardSphereForkMemberVertex (P.equivFin.symm i).val 0) -
        hardSpherePosition r (P.equivFin.symm i).val.1 := by
  change ((hardSphereForkPackingSignedBlockMap hT hP
    (hardSphereForkPackingRawBlockMap hT hP r)).1 i).1 = _
  rw [hardSphereForkPackingSignedBlockMap_fst_apply,
    hardSphereForkPackingFlatReversed_member,
    hardSphereForkPackingRawBlockMap_flat_apply,
    hardSphereForkPackingIndexEquiv_member,
    hardSphereTreeDifferencePositionMap_apply]
  simpa [hardSphereApplyReversal] using
    (hardSphereForkPackingMember_oriented_difference hP i 0 r)

lemma hardSphereForkPackingBlockMap_snd_member_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (r : HardSphereConfiguration k 3) (i : Fin P.card) :
    ((hardSphereForkPackingBlockMap hT hP r).1 i).2 =
      hardSpherePosition r
          (hardSphereForkMemberVertex (P.equivFin.symm i).val 1) -
        hardSpherePosition r (P.equivFin.symm i).val.1 := by
  change ((hardSphereForkPackingSignedBlockMap hT hP
    (hardSphereForkPackingRawBlockMap hT hP r)).1 i).2 = _
  rw [hardSphereForkPackingSignedBlockMap_snd_apply,
    hardSphereForkPackingFlatReversed_member,
    hardSphereForkPackingRawBlockMap_flat_apply,
    hardSphereForkPackingIndexEquiv_member,
    hardSphereTreeDifferencePositionMap_apply]
  simpa [hardSphereApplyReversal] using
    (hardSphereForkPackingMember_oriented_difference hP i 1 r)

lemma hardSphereForkPackingBlockMap_complement_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    (r : HardSphereConfiguration k 3)
    (i : Fin (hardSphereForkPackingComplementCard hT hP)) :
    (hardSphereForkPackingBlockMap hT hP r).2 i =
      hardSphereTreeDifferencePositionMap hT r
        (hardSphereForkPackingIndexEquiv hT hP
          (Fin.natAdd (P.card * 2) i)) := by
  change (hardSphereForkPackingSignedBlockMap hT hP
    (hardSphereForkPackingRawBlockMap hT hP r)).2 i = _
  rw [hardSphereForkPackingSignedBlockMap_complement_apply,
    hardSphereForkPackingFlatReversed_complement,
    hardSphereForkPackingRawBlockMap_flat_apply,
    hardSphereTreeDifferencePositionMap_apply]
  rfl

lemma hardSphereForkPackingBlockMap_mem_separatedBlockProductRegion {k : Nat}
    [NeZero k] {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P)
    {r : HardSphereConfiguration k 3}
    (hr : r ∈ hardSphereTreeRegion T)
    (hrAvoid : r ∈ hardSphereForkAvoidanceRegion T P) :
    hardSphereForkPackingBlockMap hT hP r ∈
      hardSphereSeparatedBlockProductRegion P.card
        (hardSphereForkPackingComplementCard hT hP) := by
  rw [hardSphereSeparatedBlockProductRegion]
  constructor
  · rw [hardSphereSeparatedPairProductRegion]
    intro i
    rw [hardSphereSeparatedPairRegion]
    simp only [Set.mem_ofPred_eq]
    rw [hardSphereForkPackingBlockMap_fst_member_apply,
      hardSphereForkPackingBlockMap_snd_member_apply]
    simpa [hardSphereForkRelativePair, hardSphereSeparatedPairRegion,
      hardSphereForkMemberVertex, mem_ball_iff_norm, sub_zero] using
      (hardSphere_treeRegion_mem_separatedPair_of_mem_forkAvoidance hP hr hrAvoid
        (P.equivFin.symm i).property)
  · rw [hardSphereProductBallRegion]
    intro i
    rw [hardSphereForkPackingBlockMap_complement_apply]
    rw [hardSphereTreeDifferencePositionMap_apply]
    rw [mem_ball_iff_norm]
    simpa [sub_zero] using
      (hardSphereTreeDifference_norm_lt_one hT hr
        (hardSphereForkPackingIndexEquiv hT hP
          (Fin.natAdd (P.card * 2) i)))

lemma measurePreserving_hardSphereForkPackingBlockMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    MeasurePreserving (hardSphereForkPackingBlockMap hT hP)
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure ((Fin P.card → (HSPosition 3 × HSPosition 3)) ×
        (Fin (hardSphereForkPackingComplementCard hT hP) → HSPosition 3))) := by
  change MeasurePreserving
    ((hardSphereForkPackingSignedBlockMap hT hP) ∘
      (hardSphereForkPackingRawBlockMap hT hP)) volume volume
  exact (measurePreserving_hardSphereForkPackingSignedBlockMap hT hP).comp
    (measurePreserving_hardSphereForkPackingRawBlockMap hT hP)

lemma hardSphere_nbc_region_real_volume_le_of_forkPacking {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hT : T ∈ treeUniverse (V := Fin k))
    (hP : hardSphereForkPacking T P) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ P.card *
        hardSphereKappa ^ hardSphereForkPackingComplementCard hT hP := by
  apply hardSphere_nbc_region_real_volume_le_of_separatedBlockMap
    (φ := hardSphereForkPackingBlockMap hT hP)
    (measurePreserving_hardSphereForkPackingBlockMap hT hP)
  intro r hr
  exact hardSphereForkPackingBlockMap_mem_separatedBlockProductRegion hT hP
    (hardSphere_nbc_region_subset_tree_region hr)
    (hardSphere_nbc_region_subset_forkAvoidance hP hr)

theorem hardSphereNBCRegion_real_volume_le_forkFactor {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      (17 / 32 : ℝ) ^ hardSphereNu T * hardSphereKappa ^ (k - 1) := by
  obtain ⟨P, hP, hcard⟩ := hardSphere_exists_forkPacking_card_eq_nu T
  have hbound := hardSphere_nbc_region_real_volume_le_of_forkPacking hT hP
  rw [hardSphereSeparatedPairRegion_real_volume_ratio,
    hardSphereForkPackingComplementCard_eq hP] at hbound
  have htwo := hardSphereForkPacking_two_mul_card_le_pred hP
  have hpow : 2 * P.card + ((k - 1) - P.card * 2) = k - 1 := by
    omega
  calc
    (volume : Measure (HardSphereConfiguration k 3)).real
          (nbcRegion (V := Fin k)
            (hardSphereActiveExact (k := k) (d := 3)) T) ≤
        ((17 / 32 : ℝ) * hardSphereKappa ^ 2) ^ P.card *
          hardSphereKappa ^ ((k - 1) - P.card * 2) := hbound
    _ = (17 / 32 : ℝ) ^ P.card *
          (hardSphereKappa ^ 2) ^ P.card *
          hardSphereKappa ^ ((k - 1) - P.card * 2) := by
      rw [mul_pow]
    _ = (17 / 32 : ℝ) ^ P.card *
          hardSphereKappa ^ (2 * P.card) *
          hardSphereKappa ^ ((k - 1) - P.card * 2) := by
      rw [pow_mul]
    _ = (17 / 32 : ℝ) ^ P.card *
          hardSphereKappa ^ (2 * P.card + ((k - 1) - P.card * 2)) := by
      rw [mul_assoc, ← pow_add]
    _ = (17 / 32 : ℝ) ^ P.card * hardSphereKappa ^ (k - 1) := by
      rw [hpow]
    _ = (17 / 32 : ℝ) ^ hardSphereNu T * hardSphereKappa ^ (k - 1) := by
      rw [← hcard]

end

end HsVirial
