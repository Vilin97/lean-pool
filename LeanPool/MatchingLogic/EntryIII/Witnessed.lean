/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The witnessed Lindenbaum extension used by entry point (iii).

The source works modulo alpha equivalence and adds, for each existential,
a fresh Henkin implication.  Here the implication uses the total
capture-avoiding substitution from `CaptureAvoiding`; freshness is required
only for the conservative-extension proof, not for the public operation.
-/
import LeanPool.MatchingLogic.EntryIII.CaptureAvoiding
import LeanPool.MatchingLogic.EntryIII.Lindenbaum
import Mathlib.Data.Countable.Defs

/-!
# MatchingLogic.EntryIII.Witnessed
-/

namespace MatchingLogic

open Set

variable {S : Signature}

noncomputable section

/-- Local decidable equality used by the witnessed-extension construction. -/
local instance instDecidableEqPatternNatWitnessed : DecidableEq (Pattern S Nat) :=
  Classical.decEq _

/-- A theory is witnessed when every existential it contains has a Henkin
implication to one of its capture-avoiding variable instances. -/
def Witnessed (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    ∃ y : Nat, .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma

/-- A witnessed theory whose Henkin name is fresh for every raw occurrence in
the existential body.  This is the source construction's actual stronger
invariant; `Witnessed` is its interface needed by the basic Truth Lemma. -/
def FreshWitnessed (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    ∃ y : Nat, y ∉ p.allVars ∧
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma

theorem FreshWitnessed.toWitnessed {Gamma : Set (Pattern S Nat)}
    (h : FreshWitnessed Gamma) : Witnessed Gamma := by
  intro x p hex
  obtain ⟨y, _hyfresh, hy⟩ := h hex
  exact ⟨y, hy⟩

private theorem swap_not_taut :
    PForm.Taut
      (.imp (.imp (.atom 0) (.imp (.atom 1) .bot))
        (.imp (.atom 1) (.imp (.atom 0) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Propositional contraposition in the shape used by quantifier
generalisation below. -/
theorem Provable.swap_not {Gamma : Set (Pattern S Nat)}
    {p q : Pattern S Nat} (h : Provable Gamma (.imp p (Pattern.nt q))) :
    Provable Gamma (.imp q (Pattern.nt p)) := by
  have ht : Provable Gamma
      (.imp (.imp p (Pattern.nt q)) (.imp q (Pattern.nt p))) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then p else q)
        swap_not_taut)
  exact .mp h ht

private theorem not_imp_left_taut :
    PForm.Taut
      (.imp (.imp (.imp (.atom 0) (.atom 1)) .bot) (.atom 0)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem not_imp_right_taut :
    PForm.Taut
      (.imp (.imp (.imp (.atom 0) (.atom 1)) .bot)
        (.imp (.atom 1) .bot)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem Provable.not_imp_left (Gamma : Set (Pattern S Nat))
    (p q : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.nt (.imp p q)) p) := by
  simpa [PForm.subst, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then p else q)
      not_imp_left_taut)

private theorem Provable.not_imp_right (Gamma : Set (Pattern S Nat))
    (p q : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.nt (.imp p q)) (Pattern.nt q)) := by
  simpa [PForm.subst, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then p else q)
      not_imp_right_taut)

private theorem not_mem_FV_conj {y : Nat} {l : List (Pattern S Nat)}
    (h : ∀ p ∈ l, y ∉ FV p) : y ∉ FV (conj l) := by
  induction l with
  | nil => simp [conj, Pattern.tp]
  | cons p l ih =>
      simp only [conj]
      simp [Pattern.and, Pattern.nt, h p (by simp), ih (by
        intro q hq
        exact h q (by simp [hq]))]

/-- Local universal generalisation of a negation.  The side condition is the
source condition that the generalised name is absent from every premise. -/
theorem LocProvable.not_ex_of_not_fresh {Gamma : Set (Pattern S Nat)}
    {y : Nat} {q : Pattern S Nat}
    (hfresh : ∀ p ∈ Gamma, y ∉ FV p)
    (hnot : LocProvable Gamma (Pattern.nt q)) :
    LocProvable Gamma (Pattern.nt (.ex y q)) := by
  rcases hnot with ⟨l, hl, hp⟩
  have hswap : Provable (∅ : Set (Pattern S Nat))
      (.imp q (Pattern.nt (conj l))) := hp.swap_not
  have hfree : y ∉ FV (Pattern.nt (conj l)) := by
    simpa [Pattern.nt] using not_mem_FV_conj (y := y) (l := l) (by
      intro p hp
      exact hfresh p (hl p hp))
  have hgen : Provable (∅ : Set (Pattern S Nat))
      (.imp (.ex y q) (Pattern.nt (conj l))) := .exGen hswap hfree
  exact ⟨l, hl, hgen.swap_not⟩

/-- Adding one fresh Henkin implication is conservative for local
consistency.  This is the proof-theoretic heart of the witnessed extension. -/
theorem locConsistent_insert_captureAvoidingWitness
    {Gamma : Set (Pattern S Nat)} {x y : Nat} {p : Pattern S Nat}
    (hGamma : LocConsistent Gamma)
    (hyGamma : ∀ q ∈ Gamma, y ∉ FV q)
    (hyp : y ∉ p.allVars) :
    LocConsistent
      (insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p)) Gamma) := by
  intro hbad
  let q := Pattern.captureAvoidingSubst x y p
  let e : Pattern S Nat := .ex x p
  have hnimp : LocProvable Gamma (Pattern.nt (.imp e q)) := by
    simpa [e, q] using LocProvable.deduction_insert hbad
  have he : LocProvable Gamma e :=
    hnimp.mp (LocProvable.of_provable (Provable.not_imp_left ∅ e q))
  have hnq : LocProvable Gamma (Pattern.nt q) :=
    hnimp.mp (LocProvable.of_provable (Provable.not_imp_right ∅ e q))
  have hnex : LocProvable Gamma (Pattern.nt (.ex y q)) :=
    hnq.not_ex_of_not_fresh hyGamma
  have halpha : Provable (∅ : Set (Pattern S Nat)) (.imp e (.ex y q)) := by
    have hraw := Provable.alphaEx_forward (Gamma := (∅ : Set (Pattern S Nat)))
      (x := x) (p := p) hyp
    simpa [e, q, Pattern.captureAvoidingSubst_eq_substVar_of_fresh hyp] using hraw
  have hex : LocProvable Gamma (.ex y q) :=
    he.mp (LocProvable.of_provable halpha)
  exact hGamma (hex.mp hnex)

/-! ### Shared Henkin-stage infrastructure -/

/-- Iterate a witness-adjunction operation along an enumeration. -/
def henkinStages {α : Type} (step : List α → α → List α)
    (enum : Nat → α) (base : List α) : Nat → List α
  | 0 => base
  | n + 1 => step (henkinStages step enum base n) (enum n)

/-- The union of the theories represented by all finite Henkin stages. -/
def henkinLimit {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base : List α) : Set α :=
  {q | ∃ n, q ∈ stageTheory (henkinStages step enum base n)}

/-- A stage operation that only enlarges represented theories gives a monotone
sequence of finite Henkin stages. -/
theorem henkinStages_mono {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base : List α)
    (hstep : ∀ l phi, stageTheory l ⊆ stageTheory (step l phi)) :
    Monotone (fun n => stageTheory (henkinStages step enum base n)) :=
  monotone_nat_of_le_succ fun n => by
    simpa [henkinStages] using hstep (henkinStages step enum base n) (enum n)

/-- Every finite list drawn from a Henkin limit already appears at one common
finite stage. -/
theorem henkinLimit_covers_list {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base l : List α)
    (hstep : ∀ stage phi, stageTheory stage ⊆ stageTheory (step stage phi))
    (hl : ∀ q ∈ l, q ∈ henkinLimit stageTheory step enum base) :
    ∃ n, ∀ q ∈ l, q ∈ stageTheory (henkinStages step enum base n) := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
      rcases hl q (by simp) with ⟨n, hn⟩
      obtain ⟨m, hm⟩ := ih (by
        intro r hr
        exact hl r (by simp [hr]))
      refine ⟨max n m, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact henkinStages_mono stageTheory step enum base hstep
          (Nat.le_max_left n m) hn
      · exact henkinStages_mono stageTheory step enum base hstep
          (Nat.le_max_right n m) (hm r hr)

/-- Local consistency at every finite stage passes to the shared Henkin limit. -/
theorem henkinLimit_locConsistent
    (stageTheory : List (Pattern S Nat) → Set (Pattern S Nat))
    (step : List (Pattern S Nat) → Pattern S Nat → List (Pattern S Nat))
    (enum : Nat → Pattern S Nat) (base : List (Pattern S Nat))
    (hstep : ∀ stage phi, stageTheory stage ⊆ stageTheory (step stage phi))
    (hconsistent : ∀ n,
      LocConsistent (stageTheory (henkinStages step enum base n))) :
    LocConsistent (henkinLimit stageTheory step enum base) := by
  intro hbad
  rcases hbad with ⟨l, hl, hp⟩
  obtain ⟨n, hn⟩ :=
    henkinLimit_covers_list stageTheory step enum base l hstep hl
  exact hconsistent n ⟨l, hn, hp⟩

/-! ### Finite fresh-support stages -/

/-- A binder-free pattern whose `allVars` contains the variables of every
pattern in the list. -/
def Pattern.listSupport : List (Pattern S Nat) → Pattern S Nat
  | [] => .bot
  | p :: l => .imp p (listSupport l)

/-- Every member's raw-variable support lies in the list support. -/
theorem Pattern.allVars_subset_listSupport {l : List (Pattern S Nat)}
    {p : Pattern S Nat} (hp : p ∈ l) : p.allVars ⊆ (listSupport l).allVars := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · intro y hy
        exact Finset.mem_union_left _ hy
      · intro y hy
        exact Finset.mem_union_right _ (ih hp hy)

/-- The fresh name chosen when the current finite stage is `l` and the
enumerated existential body is `p`. -/
private def Pattern.henkinFresh (l : List (Pattern S Nat)) (p : Pattern S Nat) : Nat :=
  (Pattern.imp (listSupport l) p).fresh

private theorem Pattern.henkinFresh_not_mem_body
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    henkinFresh l p ∉ p.allVars := by
  intro hmem
  exact (Pattern.imp (listSupport l) p).fresh_not_mem_allVars
    (Finset.mem_union_right _ hmem)

private theorem Pattern.henkinFresh_not_mem_stage_FV
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    ∀ q ∈ ({q | q ∈ l} : Set (Pattern S Nat)), henkinFresh l p ∉ FV q := by
  intro q hq hfree
  apply (Pattern.imp (listSupport l) p).fresh_not_mem_allVars
  apply Finset.mem_union_left
  exact allVars_subset_listSupport hq (q.FV_subset_allVars hfree)

/-- Add the fresh Henkin implication associated to an existential pattern;
leave a non-existential enumeration entry unchanged. -/
private def addWitness (l : List (Pattern S Nat)) : Pattern S Nat → List (Pattern S Nat)
  | .ex x p =>
      let y := Pattern.henkinFresh l p
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) :: l
  | _ => l

private theorem listTheory_subset_addWitness (l : List (Pattern S Nat))
    (phi : Pattern S Nat) :
    ({q | q ∈ l} : Set (Pattern S Nat)) ⊆ {q | q ∈ addWitness l phi} := by
  intro q hq
  cases phi <;> simp_all [addWitness]

private theorem locConsistent_addWitness (l : List (Pattern S Nat))
    (phi : Pattern S Nat) (hl : LocConsistent ({q | q ∈ l} : Set (Pattern S Nat))) :
    LocConsistent ({q | q ∈ addWitness l phi} : Set (Pattern S Nat)) := by
  cases phi with
  | var x => simpa [addWitness] using hl
  | bot => simpa [addWitness] using hl
  | app sigma args => simpa [addWitness] using hl
  | imp p q => simpa [addWitness] using hl
  | ex x p =>
      let y := Pattern.henkinFresh l p
      have hcons := locConsistent_insert_captureAvoidingWitness
        (Gamma := ({q | q ∈ l} : Set (Pattern S Nat))) (x := x) (y := y) (p := p)
        hl (Pattern.henkinFresh_not_mem_stage_FV l p)
        (Pattern.henkinFresh_not_mem_body l p)
      rw [show
        ({q | q ∈ addWitness l (.ex x p)} : Set (Pattern S Nat)) =
          insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
            ({q | q ∈ l} : Set (Pattern S Nat)) by
          ext q
          simp [addWitness, y]]
      exact hcons

/-- The finite Henkin stages.  Stage `n+1` handles enumeration entry `n`. -/
private abbrev witnessStages (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) : Nat → List (Pattern S Nat) :=
  henkinStages addWitness enum base

private theorem witnessStages_locConsistent (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∀ n, LocConsistent ({q | q ∈ witnessStages enum base n} : Set (Pattern S Nat)) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      simpa [henkinStages] using
        locConsistent_addWitness (witnessStages enum base n) (enum n) ih

/-- Union of all finite witness-adjunction stages. -/
private def henkinTheory (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) : Set (Pattern S Nat) :=
  henkinLimit (fun l => {q | q ∈ l}) addWitness enum base

private theorem henkinTheory_locConsistent (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    LocConsistent (henkinTheory enum base) := by
  exact henkinLimit_locConsistent (fun l => {q | q ∈ l}) addWitness enum base
    listTheory_subset_addWitness
    (witnessStages_locConsistent enum base hbase)

private theorem base_subset_henkinTheory (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) :
    ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ henkinTheory enum base := by
  intro q hq
  exact ⟨0, hq⟩

private theorem henkinTheory_has_freshWitness
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat)) (x : Nat) (p : Pattern S Nat) :
    ∃ y, y ∉ p.allVars ∧ .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈
      henkinTheory enum base := by
  obtain ⟨n, hn⟩ := henum (.ex x p)
  let y := Pattern.henkinFresh (witnessStages enum base n) p
  refine ⟨y, Pattern.henkinFresh_not_mem_body _ _, n + 1, ?_⟩
  simp [henkinStages, hn, addWitness, y]

/-! ### Witnessed Lindenbaum extension -/

/-- The finite Henkin construction preserves the raw freshness of the
adjoined witness name, not merely the ordinary witnessed property. -/
theorem finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ FreshWitnessed Delta := by
  obtain ⟨Delta, hHDelta, hM⟩ :=
    locConsistent_extend_isMCS (henkinTheory_locConsistent enum base hbase)
  refine ⟨Delta, (base_subset_henkinTheory enum base).trans hHDelta, hM, ?_⟩
  intro x p _hex
  obtain ⟨y, hyfresh, hy⟩ := henkinTheory_has_freshWitness enum henum base x p
  exact ⟨y, hyfresh, hHDelta hy⟩

/-- Enumeration-parametric ordinary witnessedness follows by forgetting the
freshness evidence from the stronger construction. -/
theorem finite_locConsistent_extend_witnessed_isMCS_of_surjective
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by
  obtain ⟨Delta, hbaseDelta, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
      enum henum base hbase
  exact ⟨Delta, hbaseDelta, hM, hW.toWitnessed⟩

/-- Every locally consistent finite-list theory over a countable pattern
language extends to a maximal locally consistent theory with fresh Henkin
witnesses. -/
theorem finite_locConsistent_extend_freshWitnessed_isMCS
    [Countable (Pattern S Nat)] (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ FreshWitnessed Delta := by
  let _ : Nonempty (Pattern S Nat) := ⟨.bot⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Pattern S Nat)
  exact finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
    enum henum base hbase

/-- Every locally consistent finite-list theory over a countable pattern
language extends to a witnessed maximal locally consistent set. -/
theorem finite_locConsistent_extend_witnessed_isMCS
    [Countable (Pattern S Nat)] (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by
  obtain ⟨Delta, hbaseDelta, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS base hbase
  exact ⟨Delta, hbaseDelta, hM, hW.toWitnessed⟩

end

end MatchingLogic
