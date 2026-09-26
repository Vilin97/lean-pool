/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarEnum
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic

/-!
# Preparations for the bundle closure

Three ingredients for identifying the strand-bundle closure with
the straight-matching self-glue: the straight matching is
well-formed and leaves no survivors (generically, for any `m`);
the strand bundle is invariant under transposing its two boundary
blocks; and the interface pairs of a full closure split into the
high-block pairs followed by the low-block pairs.
-/

@[expose] public section

namespace RS

/-! ### The straight matching, generically -/

/-- The straight matching's flags, listed. -/
theorem matchPairs_flat (m : ℕ) :
    (matchPairs m).flatMap (fun p => [p.1, p.2]) =
      (List.finRange m).flatMap
        (fun j => [Fin.castAdd m j, Fin.natAdd m j]) := by
  unfold matchPairs
  rw [List.flatMap_map]

/-- It uses every label: the matching is perfect. -/
theorem mem_matchPairs_flat (m : ℕ) (z : Fin (m + m)) :
    z ∈ (matchPairs m).flatMap (fun p => [p.1, p.2]) := by
  rw [matchPairs_flat]
  refine List.mem_flatMap.mpr ?_
  by_cases h : z.val < m
  · exact ⟨⟨z.val, h⟩, List.mem_finRange _,
      List.mem_cons.mpr (Or.inl (Fin.ext rfl))⟩
  · refine ⟨⟨z.val - m, by have := z.isLt; omega⟩,
      List.mem_finRange _, List.mem_cons.mpr (Or.inr
        (List.mem_cons.mpr (Or.inl (Fin.ext ?_))))⟩
    change z.val = m + (z.val - m)
    have := z.isLt
    omega

/-- It is a well-formed gluing list. -/
theorem matchPairs_wf (m : ℕ) :
    Fragment.PairsWF (matchPairs m) := by
  change ((matchPairs m).flatMap (fun p => [p.1, p.2])).Nodup
  rw [matchPairs_flat]
  refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
  · intro j _
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro he
    have hv := congrArg Fin.val he
    have h1 : (Fin.castAdd m j).val = j.val := rfl
    have h2 : (Fin.natAdd m j).val = m + j.val := rfl
    rw [h1, h2] at hv
    have := j.isLt
    omega
  · refine List.Nodup.pairwise_of_forall_ne
      (List.nodup_finRange m) ?_
    intro a _ b _ hab
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    intro z hza hzb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hza hzb
    rcases hza with rfl | rfl
    · rcases hzb with h | h
      · have hv := congrArg Fin.val h
        have h1 : (Fin.castAdd m a).val = a.val := rfl
        have h2 : (Fin.castAdd m b).val = b.val := rfl
        rw [h1, h2] at hv
        exact hne hv
      · have hv := congrArg Fin.val h
        have h1 : (Fin.castAdd m a).val = a.val := rfl
        have h2 : (Fin.natAdd m b).val = m + b.val := rfl
        rw [h1, h2] at hv
        have := a.isLt
        omega
    · rcases hzb with h | h
      · have hv := congrArg Fin.val h
        have h1 : (Fin.natAdd m a).val = m + a.val := rfl
        have h2 : (Fin.castAdd m b).val = b.val := rfl
        rw [h1, h2] at hv
        have := b.isLt
        omega
      · have hv := congrArg Fin.val h
        have h1 : (Fin.natAdd m a).val = m + a.val := rfl
        have h2 : (Fin.natAdd m b).val = m + b.val := rfl
        rw [h1, h2] at hv
        omega

/-- And leaves no survivor, so gluing it closes the fragment. -/
theorem matchPairs_surv_isEmpty (m : ℕ) :
    IsEmpty (Fragment.FoldSurviving (Fin (m + m))
      (matchPairs m)) := by
  refine ⟨fun s => ?_⟩
  obtain ⟨z, hprop⟩ := s
  exact (forall_ne_iff_not_mem_flat _ _).mp hprop
    (mem_matchPairs_flat m z)

/-! ### Block-swap invariance of the strand bundle -/

/-- Transposing the two boundary blocks of the strand bundle
returns the strand bundle: each strand just swaps its two ends. -/
noncomputable def strandBundleTranspose (m : ℕ) :
    ((strandBundle m).relabel (transposeEquiv m m)).Equiv
      (strandBundle m) where
  flagEquiv := ⟨fun f => (f.1, !f.2), fun f => (f.1, !f.2),
    fun f => by obtain ⟨i, b⟩ := f; cases b <;> rfl,
    fun f => by obtain ⟨i, b⟩ := f; cases b <;> rfl⟩
  vertexEquiv := _root_.Equiv.refl Empty
  attach_comm := fun f => by
    obtain ⟨i, b⟩ := f
    change (strandBundle m).attach (i, !b) =
      (((strandBundle m).attach (i, b)).map id
        (transposeEquiv m m)).map (_root_.Equiv.refl Empty) id
    cases b
    · change (Sum.inr ⟨m + i.val, by omega⟩ :
          Empty ⊕ Fin (m + m)) =
        Sum.inr (transposeEquiv m m ⟨i.val, by omega⟩)
      refine congrArg Sum.inr ?_
      rw [transposeEquiv_low m m i.val i.isLt]
    · change (Sum.inr ⟨i.val, by omega⟩ :
          Empty ⊕ Fin (m + m)) =
        Sum.inr (transposeEquiv m m ⟨m + i.val, by omega⟩)
      refine congrArg Sum.inr ?_
      rw [transposeEquiv_high m m i.val i.isLt]
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-! ### The interface split of a full closure -/

/-- The high-block interface pairs of a full `(m + m)`-closure. -/
def highCross (m : ℕ) :
    List ((Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) ×
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0))) :=
  (List.finRange m).reverse.map (fun k =>
    (Sum.inl ⟨m + k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨m + k.val, by have := k.isLt; omega⟩))

/-- The low-block interface pairs of a full `(m + m)`-closure. -/
def lowCross (m : ℕ) :
    List ((Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) ×
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0))) :=
  (List.finRange m).reverse.map (fun k =>
    (Sum.inl ⟨k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨k.val, by have := k.isLt; omega⟩))

/-- A full closure's interface pairs split into the high block
followed by the low block. -/
theorem interfacePairs_split (m : ℕ) :
    interfacePairs 0 (m + m) 0 = highCross m ++ lowCross m := by
  apply List.ext_getElem
  · simp [interfacePairs, highCross, lowCross]
  intro i hi hi'
  have hi2 : i < m + m := by
    have h0 : (interfacePairs 0 (m + m) 0).length = m + m := by
      simp [interfacePairs]
    omega
  have hL : (interfacePairs 0 (m + m) 0)[i]'hi =
      (Sum.inl ⟨0 + (m + m - 1 - i), by omega⟩,
       Sum.inr ⟨m + m - 1 - i, by omega⟩) := by
    simp only [interfacePairs, List.getElem_map,
      List.getElem_reverse, List.length_finRange,
      List.getElem_finRange]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> simp
  rw [hL]
  rcases Nat.lt_or_ge i m with him | him
  · have hml : i < (highCross m).length := by
      simp only [highCross, List.length_map, List.length_reverse,
        List.length_finRange]
      omega
    rw [List.getElem_append_left hml]
    have hR : (highCross m)[i]'hml =
        (Sum.inl ⟨m + (m - 1 - i), by omega⟩,
         Sum.inr ⟨m + (m - 1 - i), by omega⟩) := by
      simp only [highCross, List.getElem_map,
        List.getElem_reverse, List.length_finRange,
        List.getElem_finRange]
      refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
        (congrArg Sum.inr (Fin.ext ?_)) <;> simp
    rw [hR]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · change 0 + (m + m - 1 - i) = m + (m - 1 - i)
      omega
    · change m + m - 1 - i = m + (m - 1 - i)
      omega
  · have hml : (highCross m).length ≤ i := by
      simp only [highCross, List.length_map, List.length_reverse,
        List.length_finRange]
      omega
    rw [List.getElem_append_right hml]
    have hcl : (highCross m).length = m := by
      simp only [highCross, List.length_map, List.length_reverse,
        List.length_finRange]
    have hlow : i - (highCross m).length <
        (lowCross m).length := by
      simp only [highCross, lowCross, List.length_map,
        List.length_reverse, List.length_finRange]
      omega
    have hR : (lowCross m)[i - (highCross m).length]'hlow =
        (Sum.inl ⟨m - 1 - (i - m), by omega⟩,
         Sum.inr ⟨m - 1 - (i - m), by omega⟩) := by
      simp only [lowCross, List.getElem_map,
        List.getElem_reverse, List.length_finRange,
        List.getElem_finRange, hcl]
      refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
        (congrArg Sum.inr (Fin.ext ?_)) <;> simp
    rw [hR]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · change 0 + (m + m - 1 - i) = m - 1 - (i - m)
      omega
    · change m + m - 1 - i = m - 1 - (i - m)
      omega

end RS
