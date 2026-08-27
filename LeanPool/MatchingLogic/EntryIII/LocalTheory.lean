/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The propositional/local-theory layer of the canonical-model proof.

This file deliberately contains no alpha-conversion, fresh-variable, or
substitution-normalisation argument.  It transcribes Definitions 67--68 and
Proposition 69 of Chen--Rosu's technical report using the repository's pinned
right-associated finite-list conjunction `conj`.
-/
import LeanPool.MatchingLogic.ProofSystem

/-!
# MatchingLogic.EntryIII.LocalTheory
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

noncomputable section

/-- Local decidable equality used for finite local theories. -/
local instance instDecidableEqPatternLocalTheory : DecidableEq (Pattern S Var) :=
  Classical.decEq _

/-! ### Small public Hilbert toolkit -/

/-- Provability is monotone in its hypotheses. -/
theorem Provable.weaken {Gamma Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGD : Gamma ⊆ Delta) (h : Provable Gamma phi) : Provable Delta phi := by
  induction h with
  | hyp hphi => exact .hyp (hGD hphi)
  | taut hp => exact .taut hp
  | mp _ _ ihphi himp => exact .mp ihphi himp
  | exQuant hfree => exact .exQuant hfree
  | exGen _ hfree ih => exact .exGen ih hfree
  | propBot => exact .propBot
  | propOr => exact .propOr
  | propEx hfree => exact .propEx hfree
  | framing _ ih => exact .framing ih
  | existence => exact .existence
  | singleton C1 C2 => exact .singleton C1 C2

/-- A theorem is usable under arbitrary hypotheses. -/
theorem Provable.weaken_empty {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable (∅ : Set (Pattern S Var)) phi) : Provable Gamma phi :=
  h.weaken (by simp)

private theorem taut_imp_refl : PForm.Taut (.imp (.atom 0) (.atom 0)) := by
  intro v
  cases h : v 0 <;> simp [PForm.eval, h]

/-- Reflexivity of implication. -/
theorem Provable.imp_refl (Gamma : Set (Pattern S Var)) (phi : Pattern S Var) :
    Provable Gamma (.imp phi phi) := by
  exact .taut (θ := fun _ => phi) taut_imp_refl

private theorem taut_imp_trans :
    PForm.Taut (.imp (.imp (.atom 0) (.atom 1))
      (.imp (.imp (.atom 1) (.atom 2)) (.imp (.atom 0) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

/-- Transitivity of implication. -/
theorem Provable.imp_trans {Gamma : Set (Pattern S Var)}
    {phi psi chi : Pattern S Var} (h1 : Provable Gamma (.imp phi psi))
    (h2 : Provable Gamma (.imp psi chi)) : Provable Gamma (.imp phi chi) := by
  have ht : Provable Gamma
      (.imp (.imp phi psi) (.imp (.imp psi chi) (.imp phi chi))) := by
    exact .taut (θ := fun n => if n = 0 then phi else if n = 1 then psi else chi)
      taut_imp_trans
  exact .mp h2 (.mp h1 ht)

private theorem taut_top : PForm.Taut (.imp .bot .bot) := by
  intro _
  rfl

/-- `⊤` is derivable in every theory. -/
theorem provable_top (Gamma : Set (Pattern S Var)) :
    Provable Gamma (Pattern.tp : Pattern S Var) := by
  exact .taut (θ := fun _ => .bot) taut_top

private theorem taut_imp_of :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- A theorem remains derivable under an arbitrary antecedent. -/
theorem Provable.imp_of {Gamma : Set (Pattern S Var)}
    {phi psi : Pattern S Var} (h : Provable Gamma phi) : Provable Gamma (.imp psi phi) := by
  have ht : Provable Gamma (.imp phi (.imp psi phi)) := by
    exact .taut (θ := fun n => if n = 0 then phi else psi) taut_imp_of
  exact .mp h ht

private theorem taut_and_intro :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1)
      (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Derived conjunction introduction. -/
theorem Provable.and_intro {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : Provable Gamma phi) (hpsi : Provable Gamma psi) :
    Provable Gamma (Pattern.and phi psi) := by
  have ht : Provable Gamma (.imp phi (.imp psi (Pattern.and phi psi))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi)
        taut_and_intro)
  exact .mp hpsi (.mp hphi ht)

private theorem taut_and_elim_left :
    PForm.Taut (.imp (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot) (.atom 0)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Left conjunction elimination. -/
theorem Provable.and_elim_left (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp (Pattern.and phi psi) phi) := by
  simpa [PForm.subst, Pattern.and, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi)
      taut_and_elim_left)

private theorem taut_and_elim_right :
    PForm.Taut (.imp (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot) (.atom 1)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Right conjunction elimination. -/
theorem Provable.and_elim_right (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp (Pattern.and phi psi) psi) := by
  simpa [PForm.subst, Pattern.and, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi)
      taut_and_elim_right)

private theorem taut_or_intro_left :
    PForm.Taut (.imp (.atom 0) (.imp (.imp (.atom 0) .bot) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Left disjunction introduction. -/
theorem Provable.or_intro_left (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp phi (Pattern.or phi psi)) := by
  simpa [PForm.subst, Pattern.or, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi)
      taut_or_intro_left)

private theorem taut_or_intro_right :
    PForm.Taut (.imp (.atom 1) (.imp (.imp (.atom 0) .bot) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Right disjunction introduction. -/
theorem Provable.or_intro_right (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp psi (Pattern.or phi psi)) := by
  simpa [PForm.subst, Pattern.or, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi)
      taut_or_intro_right)

/-- Introduce the pinned finite conjunction of a list of derivable patterns. -/
theorem provable_conj {Gamma : Set (Pattern S Var)} (l : List (Pattern S Var))
    (h : ∀ delta ∈ l, Provable Gamma delta) : Provable Gamma (conj l) := by
  induction l with
  | nil => exact provable_top Gamma
  | cons delta l ih =>
      exact .and_intro (h delta (by simp))
        (ih (by intro psi hpsi; exact h psi (by simp [hpsi])))

private theorem taut_imp_apply :
    PForm.Taut (.imp (.imp (.atom 0) (.atom 1))
      (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
        (.imp (.atom 0) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

private theorem Provable.imp_apply {Gamma : Set (Pattern S Var)}
    {alpha beta gamma : Pattern S Var} (h1 : Provable Gamma (.imp alpha beta))
    (h2 : Provable Gamma (.imp alpha (.imp beta gamma))) : Provable Gamma (.imp alpha gamma) := by
  have ht : Provable Gamma
      (.imp (.imp alpha beta) (.imp (.imp alpha (.imp beta gamma)) (.imp alpha gamma))) := by
    exact .taut (θ := fun n => if n = 0 then alpha else if n = 1 then beta else gamma)
      taut_imp_apply
  exact .mp h2 (.mp h1 ht)

private theorem taut_imp_imp_trans :
    PForm.Taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.imp (.atom 2) (.atom 3))
        (.imp (.atom 0) (.imp (.atom 1) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]

private theorem Provable.imp_imp_trans {Gamma : Set (Pattern S Var)}
    {alpha beta gamma delta : Pattern S Var}
    (h1 : Provable Gamma (.imp alpha (.imp beta gamma)))
    (h2 : Provable Gamma (.imp gamma delta)) :
    Provable Gamma (.imp alpha (.imp beta delta)) := by
  have ht : Provable Gamma
      (.imp (.imp alpha (.imp beta gamma))
        (.imp (.imp gamma delta) (.imp alpha (.imp beta delta)))) := by
    exact .taut (θ := fun n =>
      if n = 0 then alpha else if n = 1 then beta else if n = 2 then gamma else delta)
      taut_imp_imp_trans
  exact .mp h2 (.mp h1 ht)

private theorem taut_not_or :
    PForm.Taut (.imp (.imp (.atom 0) .bot)
      (.imp (.imp (.atom 1) .bot)
        (.imp (.imp (.imp (.atom 0) .bot) (.atom 1)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem Provable.not_or {Gamma : Set (Pattern S Var)}
    (phi psi : Pattern S Var) :
    Provable Gamma
      (.imp (Pattern.nt phi) (.imp (Pattern.nt psi)
        (Pattern.nt (Pattern.or phi psi)))) := by
  simpa [PForm.subst, Pattern.nt, Pattern.or] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi) taut_not_or)

private theorem taut_imp_and :
    PForm.Taut (.imp (.imp (.atom 0) (.atom 1))
      (.imp (.imp (.atom 0) (.atom 2))
        (.imp (.atom 0) (.imp (.imp (.atom 1) (.imp (.atom 2) .bot)) .bot)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]

/-- Combine two consequences with the same antecedent. -/
theorem Provable.imp_and {Gamma : Set (Pattern S Var)}
    {alpha beta gamma : Pattern S Var} (h1 : Provable Gamma (.imp alpha beta))
    (h2 : Provable Gamma (.imp alpha gamma)) :
    Provable Gamma (.imp alpha (Pattern.and beta gamma)) := by
  have ht : Provable Gamma
      (.imp (.imp alpha beta) (.imp (.imp alpha gamma) (.imp alpha (Pattern.and beta gamma)))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then alpha else if n = 1 then beta else gamma) taut_imp_and)
  exact .mp h2 (.mp h1 ht)

private theorem taut_imp_imp_and :
    PForm.Taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 3)))
        (.imp (.atom 0) (.imp (.atom 1)
          (.imp (.imp (.atom 2) (.imp (.atom 3) .bot)) .bot))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]

private theorem Provable.imp_imp_and {Gamma : Set (Pattern S Var)}
    {alpha beta gamma delta : Pattern S Var}
    (h1 : Provable Gamma (.imp alpha (.imp beta gamma)))
    (h2 : Provable Gamma (.imp alpha (.imp beta delta))) :
    Provable Gamma (.imp alpha (.imp beta (Pattern.and gamma delta))) := by
  have ht : Provable Gamma
      (.imp (.imp alpha (.imp beta gamma))
        (.imp (.imp alpha (.imp beta delta))
          (.imp alpha (.imp beta (Pattern.and gamma delta))))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n =>
          if n = 0 then alpha else if n = 1 then beta else if n = 2 then gamma else delta)
        taut_imp_imp_and)
  exact .mp h2 (.mp h1 ht)

/-! ### Definition 67: finite-premise local derivability -/

/-- `Γ ⊢loc φ`: a finite list of premises from `Γ` has a theorem implication to
`φ`.  Lists, rather than finite sets, are the pinned representation of the
finite conjunction and make its bracketing explicit. -/
def LocProvable (Gamma : Set (Pattern S Var)) (phi : Pattern S Var) : Prop :=
  ∃ l : List (Pattern S Var), (∀ delta ∈ l, delta ∈ Gamma) ∧
    Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)

/-- Definition 68: local consistency. -/
def LocConsistent (Gamma : Set (Pattern S Var)) : Prop :=
  ¬ LocProvable Gamma (.bot : Pattern S Var)

/-- Definition 68: a locally consistent set with no locally consistent strict
extension. -/
def IsMCS (Gamma : Set (Pattern S Var)) : Prop :=
  LocConsistent Gamma ∧ ∀ {Delta : Set (Pattern S Var)}, Gamma ⊂ Delta → ¬ LocConsistent Delta

namespace LocProvable

theorem mono {Gamma Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGD : Gamma ⊆ Delta) (h : LocProvable Gamma phi) : LocProvable Delta phi := by
  rcases h with ⟨l, hl, hp⟩
  exact ⟨l, fun delta hdelta => hGD (hl delta hdelta), hp⟩

theorem of_mem {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : phi ∈ Gamma) : LocProvable Gamma phi := by
  refine ⟨[phi], ?_, ?_⟩
  · intro delta hdelta
    have hEq : delta = phi := by simpa using hdelta
    simpa [hEq] using h
  · simpa [conj] using Provable.and_elim_left (∅ : Set (Pattern S Var)) phi Pattern.tp

theorem of_provable {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable (∅ : Set (Pattern S Var)) phi) : LocProvable Gamma phi := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · simpa [conj] using h.imp_of

private theorem conj_append_left (l r : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var)) (.imp (conj (l ++ r)) (conj l)) := by
  induction l with
  | nil => simpa [conj] using (provable_top (∅ : Set (Pattern S Var))).imp_of
  | cons phi l ih =>
      apply Provable.imp_and
      · exact Provable.and_elim_left _ phi (conj (l ++ r))
      · exact (Provable.and_elim_right _ phi (conj (l ++ r))).imp_trans ih

private theorem conj_append_right (l r : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var)) (.imp (conj (l ++ r)) (conj r)) := by
  induction l with
  | nil => simpa using Provable.imp_refl (∅ : Set (Pattern S Var)) (conj r)
  | cons phi l ih =>
      exact (Provable.and_elim_right _ phi (conj (l ++ r))).imp_trans ih

theorem mp {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : LocProvable Gamma phi) (himp : LocProvable Gamma (.imp phi psi)) :
    LocProvable Gamma psi := by
  rcases hphi with ⟨lphi, hlphi, hp⟩
  rcases himp with ⟨limp, hlimp, hi⟩
  refine ⟨lphi ++ limp, ?_, ?_⟩
  · intro delta hdelta
    rcases List.mem_append.mp hdelta with hdelta | hdelta
    · exact hlphi delta hdelta
    · exact hlimp delta hdelta
  · exact ((conj_append_left lphi limp).imp_trans hp).imp_apply
      ((conj_append_right lphi limp).imp_trans hi)

theorem and_intro {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : LocProvable Gamma phi) (hpsi : LocProvable Gamma psi) :
    LocProvable Gamma (Pattern.and phi psi) := by
  rcases hphi with ⟨lphi, hlphi, hp⟩
  rcases hpsi with ⟨lpsi, hlpsi, hq⟩
  refine ⟨lphi ++ lpsi, ?_, ?_⟩
  · intro delta hdelta
    rcases List.mem_append.mp hdelta with hdelta | hdelta
    · exact hlphi delta hdelta
    · exact hlpsi delta hdelta
  · exact Provable.imp_and ((conj_append_left lphi lpsi).imp_trans hp)
      ((conj_append_right lphi lpsi).imp_trans hq)

private theorem filter_imp_conj (phi : Pattern S Var) (l : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var))
      (.imp (conj (l.filter (fun delta => decide (delta ≠ phi)))) (.imp phi (conj l))) := by
  classical
  induction l with
  | nil =>
      simpa [conj] using ((provable_top (∅ : Set (Pattern S Var))).imp_of).imp_of
  | cons delta l ih =>
      by_cases hdelta : delta = phi
      · subst delta
        simpa [conj] using (Provable.imp_imp_and (Provable.imp_refl _ _ |>.imp_of) ih)
      · let tail := conj (l.filter fun eta => decide (eta ≠ phi))
        have hleft : Provable (∅ : Set (Pattern S Var))
            (.imp (Pattern.and delta tail) (.imp phi delta)) :=
          (Provable.and_elim_left _ delta tail).imp_trans
            (Provable.taut (θ := fun n => if n = 0 then delta else phi) taut_imp_of)
        have hright : Provable (∅ : Set (Pattern S Var))
            (.imp (Pattern.and delta tail) (.imp phi (conj l))) :=
          (Provable.and_elim_right _ delta tail).imp_trans ih
        simpa [tail, hdelta, conj] using Provable.imp_imp_and hleft hright

/-- A single added local premise can be discharged inside the finite-premise
definition.  This is propositional only; it does not use the global deduction
theorem, which would be unsound for unrestricted quantifier generalisation. -/
theorem deduction_insert {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (h : LocProvable (insert phi Gamma) psi) : LocProvable Gamma (.imp phi psi) := by
  classical
  rcases h with ⟨l, hl, hp⟩
  refine ⟨l.filter (fun delta => decide (delta ≠ phi)), ?_, ?_⟩
  · intro delta hdelta
    have hlin : delta ∈ l := (List.mem_filter.mp hdelta).1
    have hne : delta ≠ phi := of_decide_eq_true (List.mem_filter.mp hdelta).2
    rcases hl delta hlin with hEq | hGamma
    · exact False.elim (hne hEq)
    · exact hGamma
  · exact (filter_imp_conj phi l).imp_imp_trans hp

end LocProvable

/-! ### Proposition 69: maximal-consistent-set closure -/

namespace IsMCS

private theorem not_mem_loc_neg {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) (hphi : phi ∉ Gamma) : LocProvable Gamma (Pattern.nt phi) := by
  by_contra hneg
  have hstrict : Gamma ⊂ insert phi Gamma := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_insert _ _, ?_⟩
    intro hEq
    exact hphi (hEq ▸ Set.mem_insert phi Gamma)
  have hbad : ¬ LocConsistent (insert phi Gamma) := hM.2 hstrict
  apply hbad
  intro hbot
  exact hneg (hbot.deduction_insert)

/-- Proposition 69(1): membership is exactly local derivability. -/
theorem mem_iff_locProvable {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) : phi ∈ Gamma ↔ LocProvable Gamma phi := by
  constructor
  · exact LocProvable.of_mem
  · intro hphi
    by_contra hnot
    have hneg := not_mem_loc_neg hM hnot
    apply hM.1
    exact hphi.mp hneg

/-- Proposition 69(2): an MCS contains precisely one of a pattern and its
negation. -/
theorem neg_mem_iff_not_mem {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.nt phi ∈ Gamma ↔ phi ∉ Gamma := by
  constructor
  · intro hneg hphi
    apply hM.1
    exact (hM.mem_iff_locProvable.mp hphi).mp (hM.mem_iff_locProvable.mp hneg)
  · intro hphi
    exact hM.mem_iff_locProvable.mpr (not_mem_loc_neg hM hphi)

/-- Proposition 69(3), binary case. -/
theorem and_mem_iff {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.and phi psi ∈ Gamma ↔ phi ∈ Gamma ∧ psi ∈ Gamma := by
  constructor
  · intro hand
    constructor
    · exact hM.mem_iff_locProvable.mpr
        ((hM.mem_iff_locProvable.mp hand).mp
          (LocProvable.of_provable (Provable.and_elim_left _ phi psi)))
    · exact hM.mem_iff_locProvable.mpr
        ((hM.mem_iff_locProvable.mp hand).mp
          (LocProvable.of_provable (Provable.and_elim_right _ phi psi)))
  · rintro ⟨hphi, hpsi⟩
    exact hM.mem_iff_locProvable.mpr
      ((hM.mem_iff_locProvable.mp hphi).and_intro (hM.mem_iff_locProvable.mp hpsi))

/-- Proposition 69(3), for the repository's finite-list conjunction. -/
theorem conj_mem_iff {Gamma : Set (Pattern S Var)} (hM : IsMCS Gamma)
    (l : List (Pattern S Var)) : conj l ∈ Gamma ↔ ∀ phi ∈ l, phi ∈ Gamma := by
  induction l with
  | nil =>
      simp [conj, hM.mem_iff_locProvable.mpr (LocProvable.of_provable (provable_top _))]
  | cons phi l ih =>
      simp [conj, hM.and_mem_iff, ih]

/-- Proposition 69(4), binary case. -/
theorem or_mem_iff {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.or phi psi ∈ Gamma ↔ phi ∈ Gamma ∨ psi ∈ Gamma := by
  constructor
  · intro hor
    by_contra hneither
    have hnotphi : phi ∉ Gamma := fun hphi => hneither (Or.inl hphi)
    have hnotpsi : psi ∉ Gamma := fun hpsi => hneither (Or.inr hpsi)
    have hnphi : Pattern.nt phi ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnotphi
    have hnpsi : Pattern.nt psi ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnotpsi
    have hnotor : Pattern.nt (Pattern.or phi psi) ∈ Gamma := by
      have hstep : LocProvable Gamma
          (.imp (Pattern.nt psi) (Pattern.nt (Pattern.or phi psi))) :=
        (hM.mem_iff_locProvable.mp hnphi).mp
          (LocProvable.of_provable (Provable.not_or phi psi))
      exact hM.mem_iff_locProvable.mpr ((hM.mem_iff_locProvable.mp hnpsi).mp hstep)
    exact hM.1 ((hM.mem_iff_locProvable.mp hor).mp (hM.mem_iff_locProvable.mp hnotor))
  · intro h
    apply hM.mem_iff_locProvable.mpr
    rcases h with hphi | hpsi
    · exact (hM.mem_iff_locProvable.mp hphi).mp
        (LocProvable.of_provable (Provable.or_intro_left _ phi psi))
    · exact (hM.mem_iff_locProvable.mp hpsi).mp
        (LocProvable.of_provable (Provable.or_intro_right _ phi psi))

/-- Proposition 69(5). -/
theorem mp_mem {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) (hphi : phi ∈ Gamma) (himp : Pattern.imp phi psi ∈ Gamma) :
    psi ∈ Gamma :=
  hM.mem_iff_locProvable.mpr ((hM.mem_iff_locProvable.mp hphi).mp
    (hM.mem_iff_locProvable.mp himp))

end IsMCS

end

end MatchingLogic
