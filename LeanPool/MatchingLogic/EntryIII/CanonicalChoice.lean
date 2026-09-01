/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The finite-product decision step in Chen--Rosu TR Theorem 73.

The report distributes `psi or not psi` through every coordinate and chooses
one of the resulting `2^n` applications in the ambient MCS.  The implementation
below makes the same joint choice coordinate by coordinate; the final theorem
returns one total Boolean function and one application in which every
coordinate has been strengthened according to that function.
-/
import LeanPool.MatchingLogic.EntryIII.MCSAlpha

/-!
# MatchingLogic.EntryIII.CanonicalChoice
-/

namespace MatchingLogic

variable {S : Signature}

private def pfNot (p : PForm) : PForm := .imp p .bot
private def pfOr (p q : PForm) : PForm := .imp (pfNot p) q
private def pfAnd (p q : PForm) : PForm := pfNot (.imp p (pfNot q))

private theorem taut_and_intro :
    PForm.Taut (.imp (.atom 1) (.imp (.atom 0) (pfAnd (.atom 0) (.atom 1)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;>
    simp [pfAnd, pfNot, PForm.eval, h0, h1]

private theorem taut_and_or_distrib :
    PForm.Taut
      (.imp (pfAnd (.atom 0) (pfOr (.atom 1) (pfNot (.atom 1))))
        (pfOr (pfAnd (.atom 0) (.atom 1))
          (pfAnd (.atom 0) (pfNot (.atom 1))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;>
    simp [pfAnd, pfOr, pfNot, PForm.eval, h0, h1]

/-- Propositional decision while retaining the current finite-stage
conjunction: `Phi -> (Phi and psi) or (Phi and not psi)`. -/
theorem Provable.and_decide {Gamma : Set (Pattern S Nat)}
    (Phi psi : Pattern S Nat) :
    Provable Gamma (.imp Phi
      (Pattern.or (Pattern.and Phi psi) (Pattern.and Phi (Pattern.nt psi)))) := by
  let em : Pattern S Nat := Pattern.or psi (Pattern.nt psi)
  have hem : Provable Gamma em := by
    simpa [em, Pattern.or] using
      (Provable.imp_refl Gamma (Pattern.nt psi))
  have hkeep : Provable Gamma (.imp em (.imp Phi (Pattern.and Phi em))) := by
    simpa [PForm.subst, pfAnd, pfNot, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then Phi else em) taut_and_intro)
  have hconj : Provable Gamma (.imp Phi (Pattern.and Phi em)) := .mp hem hkeep
  have hdist : Provable Gamma
      (.imp (Pattern.and Phi em)
        (Pattern.or (Pattern.and Phi psi) (Pattern.and Phi (Pattern.nt psi)))) := by
    simpa [PForm.subst, pfAnd, pfOr, pfNot, Pattern.and, Pattern.or,
      Pattern.nt, em] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then Phi else psi) taut_and_or_distrib)
  exact hconj.imp_trans hdist

/-- The one-coordinate distribution step.  It is the binary branching node in
the source's `2^n` disjunction argument. -/
theorem IsMCS.app_choice_at {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (args : Fin (S.arity sigma) -> Pattern S Nat)
    (i : Fin (S.arity sigma)) (psi : Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma) :
    ∃ b : Bool,
      Pattern.app sigma
        (Function.update args i
          (Pattern.and (args i) (if b then psi else Pattern.nt psi))) ∈ Gamma := by
  let pos : Pattern S Nat := Pattern.and (args i) psi
  let neg : Pattern S Nat := Pattern.and (args i) (Pattern.nt psi)
  have hframe0 := Provable.framing (Γ := (∅ : Set (Pattern S Nat)))
    (σ := sigma) (i := i) (args := args)
    (Provable.and_decide (Gamma := (∅ : Set (Pattern S Nat))) (args i) psi)
  have hframe : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args)
        (.app sigma (Function.update args i (Pattern.or pos neg)))) := by
    simpa [pos, neg] using hframe0
  have hdisjArg : Pattern.app sigma
      (Function.update args i (Pattern.or pos neg)) ∈ Gamma :=
    hM.mem_of_provable_imp happ hframe
  have hdisjApp : Pattern.or
      (.app sigma (Function.update args i pos))
      (.app sigma (Function.update args i neg)) ∈ Gamma :=
    hM.mem_of_provable_imp hdisjArg
      (Provable.propOr (Γ := (∅ : Set (Pattern S Nat)))
        (σ := sigma) (i := i) (args := args) (φ₁ := pos) (φ₂ := neg))
  rcases hM.or_mem_iff.mp hdisjApp with hpos | hneg
  · exact ⟨true, by simpa [pos] using hpos⟩
  · exact ⟨false, by simpa [neg] using hneg⟩

private def Pattern.choiceArgs {n : Nat} (selected : Finset (Fin n))
    (choose : Fin n -> Bool) (Phi : Fin n -> Pattern S Nat)
    (psi : Pattern S Nat) : Fin n -> Pattern S Nat :=
  fun i => if i ∈ selected then
    Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi)
  else Phi i

private theorem IsMCS.app_joint_choice_aux {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat)
    (psi : Pattern S Nat) (happ : Pattern.app sigma Phi ∈ Gamma)
    (selected : Finset (Fin (S.arity sigma))) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (Pattern.choiceArgs selected choose Phi psi) ∈ Gamma := by
  induction selected using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => false, ?_⟩
      have heq : Pattern.choiceArgs ∅ (fun _ => false) Phi psi = Phi := by
        funext i
        simp [Pattern.choiceArgs]
      simpa [heq] using happ
  | @insert i selected hi ih =>
      rcases ih with ⟨choose, hchosen⟩
      rcases hM.app_choice_at (Pattern.choiceArgs selected choose Phi psi) i psi
          hchosen with ⟨b, hb⟩
      let choose' := Function.update choose i b
      refine ⟨choose', ?_⟩
      have heq :
          Function.update (Pattern.choiceArgs selected choose Phi psi) i
              (Pattern.and (Pattern.choiceArgs selected choose Phi psi i)
                (if b then psi else Pattern.nt psi)) =
            Pattern.choiceArgs (insert i selected) choose' Phi psi := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [Pattern.choiceArgs, hi, choose']
        · simp [Pattern.choiceArgs, hji, choose']
      simpa only [heq] using hb

/-- Joint finite-product decision used in every stage of the n-ary canonical
Existence Lemma.  This includes the nullary case. -/
theorem IsMCS.app_joint_choice {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat)
    (psi : Pattern S Nat) (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i =>
        Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by
  rcases hM.app_joint_choice_aux Phi psi happ Finset.univ with ⟨choose, hchoose⟩
  refine ⟨choose, ?_⟩
  have heq : Pattern.choiceArgs Finset.univ choose Phi psi = fun i =>
      Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi) := by
    funext i
    simp [Pattern.choiceArgs]
  simpa [heq] using hchoose

/-- List-conjunction specialization consumed directly by the simultaneous
finite-stage construction in the canonical Existence Lemma. -/
theorem IsMCS.exists_joint_choice {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (L : Fin (S.arity sigma) -> List (Pattern S Nat))
    (psi : Pattern S Nat)
    (happ : Pattern.app sigma (fun i => conj (L i)) ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i => Pattern.and (conj (L i))
        (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by
  exact hM.app_joint_choice (fun i => conj (L i)) psi happ

end MatchingLogic
