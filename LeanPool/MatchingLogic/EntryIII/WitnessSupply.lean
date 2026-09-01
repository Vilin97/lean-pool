/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

import LeanPool.MatchingLogic.EntryIII.Witnessed
import LeanPool.MatchingLogic.EntryIII.WitnessedCollapse
import Mathlib.Data.Set.Finite.Basic

/-!
# MatchingLogic.EntryIII.WitnessSupply
-/

/-!
The variable-supply hypothesis separating ordinary and fresh witnessedness.

An infinite supply of Henkin implications for each existential must contain a
witness outside the finite raw-variable support of its body.  Maximality and
ordinary witnessedness are retained in the theorem interface to make the
comparison with the canonical-model hypotheses explicit; the supply condition
itself is what does the work.
-/

namespace MatchingLogic

open Set

variable {S : Signature}

/-- Every existential in `Gamma` has infinitely many Henkin names whose
capture-avoiding instances are already licensed by implications in `Gamma`. -/
def InfiniteWitnessSupply (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    Set.Infinite
      {y : Nat |
        .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma}

/-- The source-style variable supply for a starting theory: infinitely many
names occur free in none of its patterns. -/
def InfiniteFreshVariableSupply (Gamma : Set (Pattern S Nat)) : Prop :=
  Set.Infinite {y : Nat | ∀ q ∈ Gamma, y ∉ FV q}

/-- An infinite supply of usable witnesses upgrades ordinary witnessedness to
raw-fresh witnessedness.  The proof is short: `p.allVars` is finite. -/
theorem freshWitnessed_of_witnessed_of_supply
    {Gamma : Set (Pattern S Nat)} (hSupply : InfiniteWitnessSupply Gamma) :
    FreshWitnessed Gamma := by
  intro x p hex
  obtain ⟨y, hySupply, hyFresh⟩ :=
    (hSupply hex).exists_notMem_finset p.allVars
  exact ⟨y, hyFresh, hySupply⟩

/-! ### Henkin extension of a set with a fresh variable supply -/

noncomputable section

/-- Local decidable equality used by the fresh-variable supply construction. -/
local instance witnessSupplyDecidableEqPattern : DecidableEq (Pattern S Nat) :=
  Classical.decEq _

/-- The starting set together with the finite list of witnesses adjoined so
far. -/
private def supplyStageTheory (Gamma : Set (Pattern S Nat))
    (l : List (Pattern S Nat)) : Set (Pattern S Nat) :=
  Gamma ∪ {q | q ∈ l}

/-- Choose outside both the finite current support and the body support, from
the infinite reserve unused freely by the starting theory. -/
private noncomputable def Pattern.supplyFresh
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) : Nat :=
  Classical.choose
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))

private theorem Pattern.supplyFresh_mem_reserve
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∈ {y : Nat | ∀ q ∈ Gamma, y ∉ FV q} :=
  (Classical.choose_spec
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))).1

private theorem Pattern.supplyFresh_not_mem_blocked
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∉
      (listSupport l).allVars ∪ p.allVars :=
  (Classical.choose_spec
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))).2

private theorem Pattern.supplyFresh_not_mem_body
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∉ p.allVars := by
  intro hp
  exact supplyFresh_not_mem_blocked Gamma hSupply l p
    (Finset.mem_union_right _ hp)

private theorem Pattern.supplyFresh_not_mem_stage_FV
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    ∀ q ∈ supplyStageTheory Gamma l, supplyFresh Gamma hSupply l p ∉ FV q := by
  intro q hq
  rcases hq with hqGamma | hqList
  · exact supplyFresh_mem_reserve Gamma hSupply l p q hqGamma
  · intro hfree
    apply supplyFresh_not_mem_blocked Gamma hSupply l p
    apply Finset.mem_union_left
    exact allVars_subset_listSupport hqList (q.FV_subset_allVars hfree)

private def supplyAddWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) : Pattern S Nat → List (Pattern S Nat)
  | .ex x p =>
      let y := Pattern.supplyFresh Gamma hSupply l p
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) :: l
  | _ => l

private theorem supplyStageTheory_subset_addWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (phi : Pattern S Nat) :
    supplyStageTheory Gamma l ⊆
      supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l phi) := by
  intro q hq
  rcases hq with hq | hq
  · exact Set.mem_union_left _ hq
  · exact Set.mem_union_right _ (by
      cases phi <;> simp_all [supplyAddWitness])

private theorem locConsistent_supplyAddWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (phi : Pattern S Nat)
    (hl : LocConsistent (supplyStageTheory Gamma l)) :
    LocConsistent
      (supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l phi)) := by
  cases phi with
  | var x => simpa [supplyAddWitness] using hl
  | bot => simpa [supplyAddWitness] using hl
  | app sigma args => simpa [supplyAddWitness] using hl
  | imp p q => simpa [supplyAddWitness] using hl
  | ex x p =>
      let y := Pattern.supplyFresh Gamma hSupply l p
      have hcons := locConsistent_insert_captureAvoidingWitness
        (Gamma := supplyStageTheory Gamma l) (x := x) (y := y) (p := p) hl
        (Pattern.supplyFresh_not_mem_stage_FV Gamma hSupply l p)
        (Pattern.supplyFresh_not_mem_body Gamma hSupply l p)
      rw [show
        supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l (.ex x p)) =
          insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
            (supplyStageTheory Gamma l) by
          ext q
          simp [supplyStageTheory, supplyAddWitness, y]
          tauto]
      exact hcons

private abbrev supplyWitnessStages
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) : Nat → List (Pattern S Nat) :=
  henkinStages (supplyAddWitness Gamma hSupply) enum []

private theorem supplyWitnessStages_locConsistent
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (hGamma : LocConsistent Gamma) :
    ∀ n, LocConsistent
      (supplyStageTheory Gamma (supplyWitnessStages Gamma hSupply enum n)) := by
  intro n
  induction n with
  | zero => simpa [henkinStages, supplyStageTheory] using hGamma
  | succ n ih =>
      simpa [henkinStages] using
        locConsistent_supplyAddWitness Gamma hSupply
          (supplyWitnessStages Gamma hSupply enum n) (enum n) ih

private def suppliedHenkinTheory
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) : Set (Pattern S Nat) :=
  henkinLimit (supplyStageTheory Gamma) (supplyAddWitness Gamma hSupply) enum []

private theorem suppliedHenkinTheory_locConsistent
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (hGamma : LocConsistent Gamma) :
    LocConsistent (suppliedHenkinTheory Gamma hSupply enum) := by
  exact henkinLimit_locConsistent (supplyStageTheory Gamma)
    (supplyAddWitness Gamma hSupply) enum []
    (supplyStageTheory_subset_addWitness Gamma hSupply)
    (supplyWitnessStages_locConsistent Gamma hSupply enum hGamma)

private theorem Gamma_subset_suppliedHenkinTheory
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) :
    Gamma ⊆ suppliedHenkinTheory Gamma hSupply enum := by
  intro q hq
  exact ⟨0, Set.mem_union_left _ hq⟩

private theorem suppliedHenkinTheory_has_freshWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (x : Nat) (p : Pattern S Nat) :
    ∃ y, y ∉ p.allVars ∧
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈
        suppliedHenkinTheory Gamma hSupply enum := by
  obtain ⟨n, hn⟩ := henum (.ex x p)
  let l := supplyWitnessStages Gamma hSupply enum n
  let y := Pattern.supplyFresh Gamma hSupply l p
  refine ⟨y, Pattern.supplyFresh_not_mem_body Gamma hSupply l p, n + 1, ?_⟩
  apply Set.mem_union_right
  simp [henkinStages, hn, supplyAddWitness, l, y]

/-- A locally consistent set extends to a fresh-witnessed MCS provided the
starting syntax leaves an infinite reserve of variables free in none of its
members.  This is the additional hypothesis that the raw-`Nat` formulation
needs in place of the source's extension from `V` to `V⁺`. -/
theorem locConsistent_extend_freshWitnessed_isMCS
    [Countable (Pattern S Nat)] {Gamma : Set (Pattern S Nat)}
    (hGamma : LocConsistent Gamma)
    (hSupply : InfiniteFreshVariableSupply Gamma) :
    ∃ Delta : Set (Pattern S Nat),
      Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta := by
  let _ : Nonempty (Pattern S Nat) := ⟨.bot⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Pattern S Nat)
  obtain ⟨Delta, hHenkinDelta, hM⟩ :=
    locConsistent_extend_isMCS
      (suppliedHenkinTheory_locConsistent Gamma hSupply enum hGamma)
  refine ⟨Delta,
    (Gamma_subset_suppliedHenkinTheory Gamma hSupply enum).trans hHenkinDelta,
    hM, ?_⟩
  intro x p _hex
  obtain ⟨y, hyFresh, hyWitness⟩ :=
    suppliedHenkinTheory_has_freshWitness Gamma hSupply enum henum x p
  exact ⟨y, hyFresh, hHenkinDelta hyWitness⟩

/-- The same extension statement without a variable-supply hypothesis is
false.  Taking the existing witnessed-but-not-fresh MCS as the starting set
leaves no locally consistent proper extension in which freshness could be
repaired. -/
theorem locConsistent_extend_freshWitnessed_isMCS_unrestricted_refuted :
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      LocConsistent Gamma →
        ∃ Delta : Set (Pattern WitnessCollapseSig Nat),
          Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta) := by
  intro hExtension
  obtain ⟨Delta, hsub, hDeltaMCS, hDeltaFresh⟩ :=
    hExtension witnessCollapseTheory_isMCS.1
  have hEq : Delta = witnessCollapseTheory := by
    apply Set.Subset.antisymm _ hsub
    by_contra hnotSubset
    obtain ⟨p, hpDelta, hpNotTheory⟩ := Set.not_subset.mp hnotSubset
    have hstrict : witnessCollapseTheory ⊂ Delta :=
      (Set.ssubset_iff_of_subset hsub).mpr ⟨p, hpDelta, hpNotTheory⟩
    exact (witnessCollapseTheory_isMCS.2 hstrict) hDeltaMCS.1
  rw [hEq] at hDeltaFresh
  exact witnessCollapseTheory_not_freshWitnessed hDeltaFresh

end

end MatchingLogic
