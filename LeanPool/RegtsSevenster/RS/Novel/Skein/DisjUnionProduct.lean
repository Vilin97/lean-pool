/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.TheoremQuant
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceOrderIso
public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor
public import LeanPool.RegtsSevenster.RS.StatementConverse
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughEdgeCut
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedCutDispatch
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedAgreement

/-!
# The final chain: assembling the factorization

The closing assembly of the converse, built entirely from
unconditional inputs: the **closed identification**.  On a closed
fragment every subset is all-internal, so its chord diagram is
empty (`labelChords_of_allInternal`) — one fibre — and the
canonical choice value agrees with the choice-free Definition 5
value (`EdgeSubset.throughValueC_eq_mixedValue`).  Independence
across boundary pairings is not needed, there being no boundary.
-/

@[expose] public section

namespace RS



/-! ## The closed identification, unconditional -/

/-- The canonical constrained value agrees with the Definition 5
value on closed Eulerian subsets — unconditionally: closed chord
diagrams are empty, so all canonical data share one fibre. -/
theorem EdgeSubset.throughValueC_eq_mixedValue {W : ClosedFragment}
    (F : EdgeSubset W) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (Fin 0))
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hE : F.Eulerian)
    (hint : ∀ f ∈ F.flags,
      ∃ v : W.Vertex, W.attach f = Sum.inl v) :
    F.throughValueC h st hbnd = F.mixedValue h := by
  obtain ⟨⟨κ, o⟩⟩ := F.exists_transition_orientation hE hint
  have hcanon : EdgeSubset.PathCanonical o.toRel :=
    EdgeSubset.pathCanonical_of_allInternal
      (F.allInternal_of_closed) _
  have hne : Nonempty F.CanonData :=
    ⟨⟨κ.toRelTransitionSystem, o.toRel, hcanon⟩⟩
  calc F.throughValueC h st hbnd
      = F.signedValueAt h st hbnd (Classical.choice hne).1 :=
        F.throughValueC_eq_signedValueAt h st hbnd hne
    _ = F.signedValueAt h st hbnd κ.toRelTransitionSystem :=
        F.signedValueAt_of_labelChords_eq_pairing h st hbnd
          (by rw [EdgeSubset.labelChords_of_allInternal
              (F.allInternal_of_closed),
            EdgeSubset.labelChords_of_allInternal
              (F.allInternal_of_closed)])
    _ = EdgeSubset.pathSign κ.toRelTransitionSystem *
          F.throughSummand h st hbnd o.toRel
            κ.toRelTransitionSystem.openCircuitCount :=
        EdgeSubset.signedValueAt_eq h st hbnd o.toRel hcanon
    _ = F.mixedSummand h o := by
        rw [EdgeSubset.pathSign_of_allInternal
            (F.allInternal_of_closed), one_mul]
        exact F.throughSummand_eq_mixedSummand h st hbnd o
    _ = F.mixedValue h :=
        (EdgeSubset.mixedValue_eq_summand_open F h o).symm

/-! ## Membership characterizations (any fragment) -/

/-- Membership in the internal flags, unfolded: a participating flag
attached to a vertex. -/
theorem mem_internalFlags_iff {γ : Type} {W : Fragment γ}
    {F : EdgeSubset W} {f : W.Flag} :
    f ∈ F.internalFlags ↔ f ∈ F.flags ∧
      ∃ v : W.Vertex, W.attach f = Sum.inl v :=
  Finset.mem_filter

/-! ## The canonical-value migration

The corrected (canonical) constrained value pins a path-canonical
orientation and weights it by the Pfaffian chord-diagram sign.  The
factorization migrates: the product of two path-canonical component
orientations is path-canonical for the union (chains stay
componentwise), and cross-component chords never interleave under
any order placing every left label below every right label, so the
crossing count — hence the path sign — is additive. -/

section CanonMigration

open EdgeSubset

variable {α β : Type}

/-! ### The product system's chain matching -/

/-- The boundary label of a left-summand boundary flag. -/
theorem boundaryLabel_inl
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag}
    (hb : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (leftSub F).boundaryFlags) :
    F.boundaryLabel hb = Sum.inl ((leftSub F).boundaryLabel hb') := by
  refine EdgeSubset.boundaryLabel_eq_of_attach hb ?_
  change ((W₁.attach g).map Sum.inl Sum.inl) =
    Sum.inr (Sum.inl ((leftSub F).boundaryLabel hb'))
  rw [EdgeSubset.attach_boundaryLabel hb']
  rfl

/-- The boundary label of a right-summand boundary flag. -/
theorem boundaryLabel_inr
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag}
    (hb : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (rightSub F).boundaryFlags) :
    F.boundaryLabel hb = Sum.inr ((rightSub F).boundaryLabel hb') := by
  refine EdgeSubset.boundaryLabel_eq_of_attach hb ?_
  change ((W₂.attach g).map Sum.inr Sum.inr) =
    Sum.inr (Sum.inr ((rightSub F).boundaryLabel hb'))
  rw [EdgeSubset.attach_boundaryLabel hb']
  rfl

end CanonMigration

end RS
