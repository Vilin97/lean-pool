/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The ordinary witnessed condition does not collapse to fresh witnessedness on
raw named syntax, even for maximal locally consistent sets.
-/
import LeanPool.MatchingLogic.EntryIII.MCSAlpha
import LeanPool.MatchingLogic.EntryIII.Witnessed

/-!
# MatchingLogic.EntryIII.WitnessedCollapse
-/

namespace MatchingLogic

open Set

noncomputable section

/-- The countermodel needs no symbols: variables and existential quantification
already separate ordinary witnesses from fresh witnesses. -/
abbrev WitnessCollapseSig : Signature where
  Sym := Empty
  arity e := Empty.elim e

/-- The two-point empty-signature model used for the witness-collapse example. -/
abbrev witnessCollapseModel : Model WitnessCollapseSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp e := Empty.elim e

/-- Variable `0` names `true`; every other variable names `false`. -/
def witnessCollapseRho : Nat → witnessCollapseModel.carrier := fun n => n = 0

/-- The complete pointed theory at `true`. -/
def witnessCollapseTheory : Set (Pattern WitnessCollapseSig Nat) :=
  {p | true ∈ witnessCollapseModel.denote witnessCollapseRho p}

private theorem witnessCollapseRho_surjective : Function.Surjective witnessCollapseRho := by
  intro b
  cases b with
  | false => exact ⟨1, by simp [witnessCollapseRho]⟩
  | true => exact ⟨0, by simp [witnessCollapseRho]⟩

private theorem mem_denote_conj
    (l : List (Pattern WitnessCollapseSig Nat))
    (hl : ∀ p ∈ l, true ∈ witnessCollapseModel.denote witnessCollapseRho p) :
    true ∈ witnessCollapseModel.denote witnessCollapseRho (conj l) := by
  induction l with
  | nil => simp [conj]
  | cons p l ih =>
      have hp := hl p (by simp)
      have htail := ih (by
        intro q hq
        exact hl q (by simp [hq]))
      simpa [conj, Pattern.and, Pattern.nt] using And.intro hp htail

/-- The pointed theory is a genuine maximal locally consistent set. -/
theorem witnessCollapseTheory_isMCS : IsMCS witnessCollapseTheory := by
  constructor
  · rintro ⟨l, hl, hp⟩
    have hconj : true ∈ witnessCollapseModel.denote witnessCollapseRho (conj l) :=
      mem_denote_conj l (by
        intro p hp
        exact hl p hp)
    have htotal := soundness
      (∅ : Set (Pattern WitnessCollapseSig Nat))
      (.imp (conj l) .bot) hp witnessCollapseModel (by simp [Model.SatSet])
      witnessCollapseRho
    have himp : true ∈ witnessCollapseModel.denote witnessCollapseRho
        (.imp (conj l) .bot) := by
      rw [htotal]
      exact Set.mem_univ true
    simp only [denote_imp, denote_bot, Set.union_empty, Set.mem_compl_iff] at himp
    exact himp hconj
  · intro Delta hstrict hDeltaConsistent
    obtain ⟨p, hpDelta, hpNotGamma⟩ := Set.exists_of_ssubset hstrict
    have hnotpGamma : Pattern.nt p ∈ witnessCollapseTheory := by
      change true ∈ witnessCollapseModel.denote witnessCollapseRho (Pattern.nt p)
      change true ∉ witnessCollapseModel.denote witnessCollapseRho p at hpNotGamma
      simpa only [denote_nt, Set.mem_compl_iff] using hpNotGamma
    have hpLoc : LocProvable Delta p := LocProvable.of_mem hpDelta
    have hnotpLoc : LocProvable Delta (Pattern.nt p) :=
      LocProvable.of_mem (hstrict.1 hnotpGamma)
    exact hDeltaConsistent (hpLoc.mp hnotpLoc)

/-- Surjectivity of the valuation supplies an ordinary name for every semantic
existential witness. -/
theorem witnessCollapseTheory_witnessed : Witnessed witnessCollapseTheory := by
  intro x p hex
  change true ∈ witnessCollapseModel.denote witnessCollapseRho (.ex x p) at hex
  simp only [denote_ex, Set.mem_iUnion] at hex
  obtain ⟨a, ha⟩ := hex
  obtain ⟨y, hy⟩ := witnessCollapseRho_surjective a
  refine ⟨y, ?_⟩
  change true ∈ witnessCollapseModel.denote witnessCollapseRho
    (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
  apply Set.mem_union_right
  rw [witnessCollapseModel.denote_captureAvoidingSubst]
  simpa [hy] using ha

/-- The existential `∃ 0. var 0` belongs to the pointed theory, but every
fresh name denotes `false`, so no fresh Henkin implication belongs to it. -/
theorem witnessCollapseTheory_not_freshWitnessed :
    ¬ FreshWitnessed witnessCollapseTheory := by
  intro hFresh
  let e : Pattern WitnessCollapseSig Nat := .ex 0 (.var 0)
  have he : e ∈ witnessCollapseTheory := by
    change true ∈ witnessCollapseModel.denote witnessCollapseRho e
    simp [e]
  obtain ⟨y, hyFresh, hyImp⟩ := hFresh he
  have hyNe : y ≠ 0 := by
    simpa [Pattern.allVars] using hyFresh
  change true ∈ witnessCollapseModel.denote witnessCollapseRho
    (.imp e (Pattern.captureAvoidingSubst 0 y (.var 0))) at hyImp
  have hePoint : true ∈ witnessCollapseModel.denote witnessCollapseRho e := he
  have hinstance :
      true ∉ witnessCollapseModel.denote witnessCollapseRho
        (Pattern.captureAvoidingSubst 0 y (.var 0)) := by
    rw [witnessCollapseModel.denote_captureAvoidingSubst]
    simp [witnessCollapseRho, hyNe]
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  exact hyImp.elim (fun hnot => hnot hePoint) (fun hmem => hinstance hmem)

/-- A concrete counterexample to the proposed collapse theorem, including the
maximality obligation. -/
theorem witnessed_freshWitnessed_of_isMCS_counterexample :
    ∃ Gamma : Set (Pattern WitnessCollapseSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ FreshWitnessed Gamma := by
  exact ⟨witnessCollapseTheory, witnessCollapseTheory_isMCS,
    witnessCollapseTheory_witnessed, witnessCollapseTheory_not_freshWitnessed⟩

/-- Direct negation of the proposed implication at the counterexample
signature. -/
theorem witnessed_freshWitnessed_of_isMCS_refuted :
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      IsMCS Gamma → Witnessed Gamma → FreshWitnessed Gamma) := by
  intro hCollapse
  exact witnessCollapseTheory_not_freshWitnessed
    (hCollapse witnessCollapseTheory_isMCS witnessCollapseTheory_witnessed)

/-- **The failure is not stable under α-renaming.**

`∃0. var 0` has no fresh witness above: the only variable naming the witnessing
element is `0`, and `0` occurs in the body, so freshness over `allVars` rules it
out.  Its α-variant `∃1. var 1` is a different raw pattern with the same
meaning, and for it the name `0` *is* fresh — so a fresh witness exists.

This locates ONE cause of the phenomenon: on raw named syntax the choice of
bound name can exhaust the supply of usable witnesses, and choosing another
representative of the same α-class restores it.

It does NOT show that α is the whole story, and an earlier version of this
docstring said it was.  `AlphaFreshWitnessed.lean` refutes that: there is an MCS
that is `Witnessed` and fails the α-RELAXED condition too, so quotienting by α
would not remove the need for the stronger invariant.  What does remove it is an
infinite supply of usable witnesses — see `WitnessSupply.lean`. -/
theorem alpha_variant_has_a_fresh_witness :
    ∃ y : Nat, y ∉ (Pattern.var 1 : Pattern WitnessCollapseSig Nat).allVars ∧
      (Pattern.imp (.ex 1 (.var 1))
        (Pattern.captureAvoidingSubst 1 y (.var 1))) ∈ witnessCollapseTheory := by
  refine ⟨0, by simp [Pattern.allVars], ?_⟩
  change true ∈ witnessCollapseModel.denote witnessCollapseRho _
  apply Set.mem_union_right
  rw [witnessCollapseModel.denote_captureAvoidingSubst]
  simp [witnessCollapseRho]

end

end MatchingLogic
