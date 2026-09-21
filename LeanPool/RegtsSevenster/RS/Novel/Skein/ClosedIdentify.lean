/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceCut
import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionProduct

/-!
# The closed identification at an arbitrary empty label type

The composition of two fragments is built at the label type
`Fin 0 ⊕ Fin 0` and then relabelled to `Fin 0`.  The Definition 5
value lives at the latter, the colouring recursion at the former, so
the two have to be matched across the relabel.

Both sides are the same sum of RS21 summands.  At an empty label type
the chord sign is one and the label chords are empty, so any two
canonical data give the same summand; and the summand itself is
carried across a relabel by `relabel_throughSummand`.  Together these
identify the relabelled fragment's Definition 5 value with the
constrained value downstairs, with no independence input.
-/

namespace RS

namespace EdgeSubset

open Fragment Classical

section Indep

variable {L : Type}

/-- **At an empty label type the summand does not depend on the
canonical data.**  The chord sign is one and the label chords are
empty, so Proposition 3 equates the two signed values. -/
theorem throughSummand_canon_indep [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ} (F : EdgeSubset V)
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st)
    (d₁ d₂ : F.CanonData) :
    F.throughSummand h st hbnd d₁.2.val d₁.1.openCircuitCount
      = F.throughSummand h st hbnd d₂.2.val d₂.1.openCircuitCount := by
  have h1 := signedValueAt_eq (F := F) h st hbnd d₁.2.val d₁.2.prop
  have h2 := signedValueAt_eq (F := F) h st hbnd d₂.2.val d₂.2.prop
  rw [pathSign_isEmpty F d₁.1, one_mul] at h1
  rw [pathSign_isEmpty F d₂.1, one_mul] at h2
  rw [← h1, ← h2]
  exact signedValueAt_of_labelChords_eq_pairing h st hbnd
    (by rw [labelChords_of_allInternal (allInternal_isEmpty F) d₁.1,
      labelChords_of_allInternal (allInternal_isEmpty F) d₂.1])

end Indep

section Relabel

variable {L : Type}

/-- Every flag of a subset at an empty label type is internally
attached. -/
theorem attach_inl_isEmpty [IsEmpty L] {V : Fragment L}
    (F : EdgeSubset V) :
    ∀ f ∈ F.flags, ∃ v : V.Vertex, V.attach f = Sum.inl v := by
  intro f _
  rcases hv : V.attach f with v | i
  · exact ⟨v, rfl⟩
  · exact isEmptyElim i

open Classical in
/-- **The relabelled fragment's Definition 5 value is the summand
downstairs.**  Both are RS21's `s_h(G,H)` for the same subset. -/
theorem mixedValue_relabelUp_closed [LinearOrder L] {V : Fragment L}
    (e : L ≃o Fin 0)
    (F : EdgeSubset V) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st)
    (hE : F.Eulerian) (d : F.CanonData) :
    (F.relabelUp e.toEquiv).mixedValue h
      = F.throughSummand h st hbnd d.2.val d.1.openCircuitCount := by
  have hst : (fun a => st (e.symm (e.toEquiv a))) = st :=
    funext fun a => congrArg st (e.symm_apply_apply a)
  have hst2 : (fun a => st (e.symm (e a))) = st :=
    funext fun a => congrArg st (e.symm_apply_apply a)
  have hbnd' : genBoundarySubsetMatches (V.relabel e.toEquiv)
      (F.relabelUp e.toEquiv).flags (fun b => st (e.symm b)) := by
    refine (relabel_genBoundarySubsetMatches_iff e.toEquiv F.flags
      (fun b => st (e.symm b))).mpr ?_
    rw [hst]
    exact hbnd
  have hE' : (F.relabelUp e.toEquiv).Eulerian :=
    (relabelUp_eulerian e.toEquiv F).mpr hE
  have hcan := pathCanonical_relabelUp e F d.2.prop
  have hne' : Nonempty (F.relabelUp e.toEquiv).CanonData :=
    ⟨⟨relabelTransUp e.toEquiv F d.1,
      ⟨relabelOrientUp e.toEquiv F d.2.val, hcan⟩⟩⟩
  rw [← throughValueC_eq_mixedValue (F.relabelUp e.toEquiv) h
      (fun b => st (e.symm b)) hbnd' hE'
      (attach_inl_isEmpty (F.relabelUp e.toEquiv)),
    throughValueC_isEmpty (F.relabelUp e.toEquiv) h _ hbnd' hne',
    throughSummand_canon_indep (F.relabelUp e.toEquiv) h _ hbnd'
      (Classical.choice hne')
      ⟨relabelTransUp e.toEquiv F d.1,
        ⟨relabelOrientUp e.toEquiv F d.2.val, hcan⟩⟩]
  show (F.relabelUp e.toEquiv).throughSummand h _ hbnd'
      (relabelOrientUp e.toEquiv F d.2.val)
      (relabelTransUp e.toEquiv F d.1).openCircuitCount = _
  rw [relabel_openCircuitCount e.toEquiv F d.1]
  refine Eq.trans (relabel_throughSummand e F h
    (fun b => st (e.symm b)) hbnd' ?_ d.2.val
    d.1.openCircuitCount) ?_
  · rw [hst2]; exact hbnd
  · congr 1

/-- At an empty label type every subset matches every state. -/
theorem genBoundarySubsetMatches_isEmpty [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ}
    (s : Finset V.Flag) (st : GenBoundaryState k ℓ L) :
    genBoundarySubsetMatches V s st :=
  fun i => isEmptyElim i

/-- At an empty label type every bijection to `Fin 0` is monotone. -/
def emptyOrderIso [LinearOrder L] [IsEmpty L]
    (ee : L ≃ Fin 0) : L ≃o Fin 0 where
  toEquiv := ee
  map_rel_iff' {a} := isEmptyElim a

open Classical in
/-- **The relabelled fragment's Definition 5 partition value is the
constrained value downstairs**, at a monotone relabel. -/
theorem mixedPartition_relabel_orderIso
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    (e : L ≃o Fin 0)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ L) :
    mixedPartition h (V.relabel e.toEquiv)
      = throughMixedPartitionC h V st := by
  rw [throughMixedPartitionC_isEmpty h st]
  unfold mixedPartition
  refine congrArg (fun z => ((k : ℂ) - 2 * ℓ) ^ V.circles * z)
    (Finset.sum_congr rfl (fun s _ => ?_))
  simp only [relabel_pairing_eq]
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · have hbnd := genBoundarySubsetMatches_isEmpty (V := V) s st
    refine Eq.trans (dif_pos hc) (Eq.trans ?_ (dif_pos hc).symm)
    refine Eq.trans ?_ (dif_pos hbnd).symm
    by_cases hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian
    · have hE' : (EdgeSubset.mk s hc :
          EdgeSubset (V.relabel e.toEquiv)).Eulerian :=
        (relabelUp_eulerian e.toEquiv (EdgeSubset.mk s hc)).mpr hE
      obtain ⟨⟨κ, o⟩⟩ := (EdgeSubset.mk s hc :
        EdgeSubset V).exists_transition_orientation hE
        (attach_inl_isEmpty (V := V) (EdgeSubset.mk s hc))
      have hcan := pathCanonical_of_allInternal
        (allInternal_isEmpty (V := V) (EdgeSubset.mk s hc))
        o.toRel
      have hne : Nonempty (EdgeSubset.mk s hc :
          EdgeSubset V).CanonData :=
        ⟨⟨κ.toRelTransitionSystem, o.toRel, hcan⟩⟩
      refine Eq.trans (if_pos hE') (Eq.trans ?_ (if_pos hE).symm)
      refine Eq.trans ?_ (dif_pos hne).symm
      rw [throughSummand_canon_indep (V := V) (EdgeSubset.mk s hc) h
        st hbnd
        (Classical.choice hne)
        ⟨κ.toRelTransitionSystem, o.toRel, hcan⟩]
      exact mixedValue_relabelUp_closed e (V := V)
        (EdgeSubset.mk s hc) h st hbnd hE
        ⟨κ.toRelTransitionSystem, o.toRel, hcan⟩
    · have hE' : ¬ (EdgeSubset.mk s hc :
          EdgeSubset (V.relabel e.toEquiv)).Eulerian :=
        fun hx => hE
          ((relabelUp_eulerian e.toEquiv (EdgeSubset.mk s hc)).mp hx)
      refine Eq.trans (if_neg hE') ?_
      exact (if_neg hE).symm
  · refine Eq.trans (dif_neg hc) ?_
    symm
    exact dif_neg hc

open Classical in
/-- **The relabelled fragment's Definition 5 partition value is the
constrained value downstairs.**  Monotonicity is automatic: there is
nothing to compare. -/
theorem mixedPartition_relabel_closed
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    (ee : L ≃ Fin 0)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ L) :
    mixedPartition h (V.relabel ee)
      = throughMixedPartitionC h V st := by
  rw [show ee = (emptyOrderIso ee).toEquiv from rfl]
  exact mixedPartition_relabel_orderIso (emptyOrderIso ee) h st

open Classical in
/-- The same identification, for a fragment presented as a relabel.
Naming the relabelled fragment keeps the elaborator from having to
solve for it under the relabel. -/
theorem mixedPartition_relabel_closed_of_eq [LinearOrder L] [IsEmpty L]
    (V₀ : Fragment L)
    (ee : L ≃ Fin 0) {V' : ClosedFragment}
    (hV : V' = V₀.relabel ee) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ L) :
    mixedPartition h V' = throughMixedPartitionC h V₀ st := by
  subst hV
  exact mixedPartition_relabel_closed ee h st

end Relabel

end EdgeSubset

end RS
