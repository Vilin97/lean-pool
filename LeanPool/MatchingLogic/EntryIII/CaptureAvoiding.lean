/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Total capture-avoiding variable substitution for entry point (iii).

The source works modulo alpha equivalence and therefore treats `p[y/x]` as a
total operation.  The verified base has raw named syntax and exposes only the
partial `substVar`, guarded by `CaptureFree`.  This additive module alpha-renames
binders named `y`, then applies `substVar`, and proves that the result has the
source operation's proof-theoretic and semantic properties.
-/
import LeanPool.MatchingLogic.EntryIII.Alpha
import LeanPool.MatchingLogic.EntryIII.LocalTheory
import LeanPool.MatchingLogic.Soundness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# MatchingLogic.EntryIII.CaptureAvoiding
-/

namespace MatchingLogic

variable {S : Signature}

namespace Pattern

@[simp] theorem substVar_self (x : Nat) (p : Pattern S Nat) : substVar x x p = p := by
  induction p with
  | var z => by_cases h : z = x <;> simp [substVar, h]
  | bot => rfl
  | app sigma args ih =>
      simp only [substVar]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [substVar, ihphi, ihpsi]
  | ex z phi ih => by_cases h : z = x <;> simp [substVar, h, ih]

theorem captureFree_self (x : Nat) (p : Pattern S Nat) : CaptureFree x x p := by
  induction p with
  | var z => trivial
  | bot => trivial
  | app sigma args ih => exact ih
  | imp phi psi ihphi ihpsi => exact ⟨ihphi, ihpsi⟩
  | ex z phi ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (Or.inr ⟨hzx, ih⟩)

end Pattern

theorem Provable.ex_mono {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (h : Provable Gamma (.imp p q)) :
    Provable Gamma (.imp (.ex x p) (.ex x q)) := by
  have hq : Provable Gamma (.imp q (.ex x q)) := by
    simpa only [Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma) (Pattern.captureFree_self x q))
  exact .exGen (h.imp_trans hq) (by simp)

private theorem imp_mono_taut :
    PForm.Taut
      (.imp (.imp (.atom 2) (.atom 0))
        (.imp (.imp (.atom 1) (.atom 3))
          (.imp (.imp (.atom 0) (.atom 1)) (.imp (.atom 2) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]

theorem Provable.imp_mono {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat}
    (hp : Provable Gamma (.imp p' p)) (hq : Provable Gamma (.imp q q')) :
    Provable Gamma (.imp (.imp p q) (.imp p' q')) := by
  have ht : Provable Gamma
      (.imp (.imp p' p) (.imp (.imp q q') (.imp (.imp p q) (.imp p' q')))) := by
    exact .taut (θ := fun n =>
      if n = 0 then p else if n = 1 then q else if n = 2 then p' else q')
      imp_mono_taut
  exact .mp hq (.mp hp ht)

private def replaceOn {n : Nat} (s : Finset (Fin n))
    (args args' : Fin n → Pattern S Nat) : Fin n → Pattern S Nat :=
  fun i => if i ∈ s then args' i else args i

private theorem replaceOn_empty {n : Nat}
    (args args' : Fin n → Pattern S Nat) : replaceOn ∅ args args' = args := by
  funext i
  simp [replaceOn]

private theorem replaceOn_univ {n : Nat}
    (args args' : Fin n → Pattern S Nat) : replaceOn Finset.univ args args' = args' := by
  funext i
  simp [replaceOn]

theorem Provable.app_mono {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat}
    (h : ∀ i, Provable Gamma (.imp (args i) (args' i))) :
    Provable Gamma (.imp (.app sigma args) (.app sigma args')) := by
  classical
  have hs : ∀ s : Finset (Fin (S.arity sigma)),
      Provable Gamma (.imp (.app sigma args)
        (.app sigma (replaceOn s args args'))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [replaceOn_empty]
        exact .imp_refl Gamma _
    | @insert i s hi ih =>
        have hstep : Provable Gamma
            (.imp (.app sigma (replaceOn s args args'))
              (.app sigma (replaceOn (insert i s) args args'))) := by
          have hf := Provable.framing (σ := sigma) (i := i)
            (args := replaceOn s args args') (h i)
          have hleft : Function.update (replaceOn s args args') i (args i) =
              replaceOn s args args' := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [replaceOn, hi]
            · simp [hji]
          have hright : Function.update (replaceOn s args args') i (args' i) =
              replaceOn (insert i s) args args' := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [replaceOn]
            · simp [replaceOn, hji]
          simpa only [hleft, hright] using hf
        exact ih.imp_trans hstep
  rw [← replaceOn_univ args args']
  exact hs Finset.univ

namespace Pattern

open scoped BigOperators

/-- Name-insensitive structural complexity for strong induction in the Truth Lemma. -/
def complexity : Pattern S Nat → Nat
  | .var _ => 1
  | .bot => 1
  | .app _ args => 1 + ∑ i, (args i).complexity
  | .imp p q => 1 + p.complexity + q.complexity
  | .ex _ p => 1 + p.complexity

theorem complexity_substVar (x y : Nat) (p : Pattern S Nat) :
    (substVar x y p).complexity = p.complexity := by
  induction p with
  | var z => by_cases h : z = x <;> simp [substVar, complexity, h]
  | bot => rfl
  | app sigma args ih =>
      simp only [substVar, complexity, Nat.add_left_cancel_iff]
      exact Finset.sum_congr rfl (fun i _ => ih i)
  | imp p q ihp ihq => simp [substVar, complexity, ihp, ihq]
  | ex z p ih => by_cases h : z = x <;> simp [substVar, complexity, h, ih]

/-- Kernel-level replacement for the source's quotient by alpha equivalence:
both implication directions are derivable, and structural complexity agrees. -/
structure AlphaEq (p q : Pattern S Nat) : Prop where
  forward : ∀ Gamma : Set (Pattern S Nat), Provable Gamma (.imp p q)
  backward : ∀ Gamma : Set (Pattern S Nat), Provable Gamma (.imp q p)
  complexity_eq : p.complexity = q.complexity

namespace AlphaEq

theorem refl (p : Pattern S Nat) : AlphaEq p p :=
  ⟨fun Gamma => .imp_refl Gamma p, fun Gamma => .imp_refl Gamma p, rfl⟩

theorem symm {p q : Pattern S Nat} (h : AlphaEq p q) : AlphaEq q p :=
  ⟨h.backward, h.forward, h.complexity_eq.symm⟩

theorem trans {p q r : Pattern S Nat} (hpq : AlphaEq p q) (hqr : AlphaEq q r) :
    AlphaEq p r :=
  ⟨fun Gamma => (hpq.forward Gamma).imp_trans (hqr.forward Gamma),
   fun Gamma => (hqr.backward Gamma).imp_trans (hpq.backward Gamma),
   hpq.complexity_eq.trans hqr.complexity_eq⟩

theorem imp {p p' q q' : Pattern S Nat} (hp : AlphaEq p p') (hq : AlphaEq q q') :
    AlphaEq (.imp p q) (.imp p' q') :=
  ⟨fun Gamma => .imp_mono (hp.backward Gamma) (hq.forward Gamma),
   fun Gamma => .imp_mono (hp.forward Gamma) (hq.backward Gamma),
   by simp [complexity, hp.complexity_eq, hq.complexity_eq]⟩

theorem app {sigma : S.Sym} {args args' : Fin (S.arity sigma) → Pattern S Nat}
    (h : ∀ i, AlphaEq (args i) (args' i)) :
    AlphaEq (.app sigma args) (.app sigma args') :=
  ⟨fun Gamma => .app_mono (fun i => (h i).forward Gamma),
   fun Gamma => .app_mono (fun i => (h i).backward Gamma),
   by
     simp only [complexity, Nat.add_left_cancel_iff]
     exact Finset.sum_congr rfl (fun i _ => (h i).complexity_eq)⟩

theorem ex (x : Nat) {p q : Pattern S Nat} (h : AlphaEq p q) :
    AlphaEq (.ex x p) (.ex x q) :=
  ⟨fun Gamma => (h.forward Gamma).ex_mono,
   fun Gamma => (h.backward Gamma).ex_mono,
   by simp [complexity, h.complexity_eq]⟩

theorem alphaEx {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    AlphaEq (.ex x p) (.ex y (substVar x y p)) :=
  ⟨fun Gamma => .alphaEx_forward hy,
   fun Gamma => .alphaEx_backward hy,
   by simp [complexity, complexity_substVar]⟩

theorem denote_eq {p q : Pattern S Nat} (h : AlphaEq p q)
    (M : Model S) (rho : Nat → M.carrier) : M.denote rho p = M.denote rho q := by
  have hf : GlobalCons (∅ : Set (Pattern S Nat)) (.imp p q) :=
    soundness (∅ : Set (Pattern S Nat)) (.imp p q) (h.forward ∅)
  have hb : GlobalCons (∅ : Set (Pattern S Nat)) (.imp q p) :=
    soundness (∅ : Set (Pattern S Nat)) (.imp q p) (h.backward ∅)
  have hempty : M.SatSet (∅ : Set (Pattern S Nat)) := by
    intro gamma hgamma
    exact hgamma.elim
  have hfp := hf M hempty rho
  have hbp := hb M hempty rho
  apply Set.Subset.antisymm
  · intro u hu
    have hui : u ∈ M.denote rho (.imp p q) := by rw [hfp]; trivial
    change u ∈ (M.denote rho p)ᶜ ∪ M.denote rho q at hui
    rcases hui with hnp | hq
    · exact absurd hu hnp
    · exact hq
  · intro u hu
    have hui : u ∈ M.denote rho (.imp q p) := by rw [hbp]; trivial
    change u ∈ (M.denote rho q)ᶜ ∪ M.denote rho p at hui
    rcases hui with hnq | hp
    · exact absurd hu hnq
    · exact hp

end AlphaEq

/-- No existential binder in a pattern uses `y` as its raw name. -/
def AvoidsBinder (y : Nat) : Pattern S Nat → Prop
  | .var _ => True
  | .bot => True
  | .app _ args => ∀ i, AvoidsBinder y (args i)
  | .imp p q => AvoidsBinder y p ∧ AvoidsBinder y q
  | .ex z p => z ≠ y ∧ AvoidsBinder y p

/-- Alpha-normalize all binders named `y`. -/
def avoidBinder (y : Nat) : Pattern S Nat → Pattern S Nat
  | .var x => .var x
  | .bot => .bot
  | .app sigma args => .app sigma (fun i => avoidBinder y (args i))
  | .imp p q => .imp (avoidBinder y p) (avoidBinder y q)
  | .ex z p =>
      let q := avoidBinder y p
      if _h : z = y then
        let w := (Pattern.ex y q).fresh
        Pattern.ex w (substVar y w q)
      else
        Pattern.ex z q

theorem AvoidsBinder.substVar {y x z : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder y p) : AvoidsBinder y (substVar x z p) := by
  induction p with
  | var a =>
      rw [MatchingLogic.substVar]
      split <;> trivial
  | bot => trivial
  | app sigma args ih => exact fun i => ih i (h i)
  | imp p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ex a p ih =>
      by_cases hax : a = x
      · rw [MatchingLogic.substVar, ite_eq_left hax]
        exact h
      · rw [MatchingLogic.substVar, ite_eq_right hax]
        change a ≠ y ∧ AvoidsBinder y (MatchingLogic.substVar x z p)
        exact ⟨h.1, ih h.2⟩

theorem avoidBinder_avoids (y : Nat) (p : Pattern S Nat) :
    AvoidsBinder y (avoidBinder y p) := by
  induction p with
  | var x => trivial
  | bot => trivial
  | app sigma args ih => exact ih
  | imp p q ihp ihq => exact ⟨ihp, ihq⟩
  | ex z p ih =>
      simp only [avoidBinder]
      split
      · rename_i hzy
        subst z
        let w := (Pattern.ex y (avoidBinder y p)).fresh
        have hw := fresh_not_mem_allVars (Pattern.ex y (avoidBinder y p))
        have hwy : w ≠ y := by
          intro h
          apply hw
          simp [w, h, allVars]
        exact ⟨hwy, ih.substVar⟩
      · rename_i hzy
        exact ⟨hzy, ih⟩

theorem AvoidsBinder.captureFree {y x : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder y p) : CaptureFree x y p := by
  induction p with
  | var z => trivial
  | bot => trivial
  | app sigma args ih => exact fun i => ih i (h i)
  | imp p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ex z p ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (Or.inr ⟨h.1, ih h.2⟩)

theorem avoidBinder_alphaEq (y : Nat) (p : Pattern S Nat) :
    AlphaEq p (avoidBinder y p) := by
  induction p with
  | var x => exact .refl _
  | bot => exact .refl _
  | app sigma args ih => exact .app ih
  | imp p q ihp ihq => exact .imp ihp ihq
  | ex z p ih =>
      simp only [avoidBinder]
      split
      · rename_i hzy
        subst z
        let w := (Pattern.ex y (avoidBinder y p)).fresh
        have hw0 := fresh_not_mem_allVars (Pattern.ex y (avoidBinder y p))
        have hw : w ∉ (avoidBinder y p).allVars := by
          intro hmem
          exact hw0 (by simp [w, allVars, hmem])
        exact (AlphaEq.ex y ih).trans (AlphaEq.alphaEx hw)
      · exact AlphaEq.ex z ih

theorem avoidBinder_eq_self_of_not_mem_allVars {y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : avoidBinder y p = p := by
  induction p with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hy
      simp only [avoidBinder]
      congr
      funext i
      exact ih i (hy i)
  | imp p q ihp ihq =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      simp [avoidBinder, ihp hy.1, ihq hy.2]
  | ex z p ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      simp [avoidBinder, Ne.symm hy.1, ih hy.2]

/-- Total source-style capture-avoiding substitution on raw `Nat` names. -/
def captureAvoidingSubst (x y : Nat) (p : Pattern S Nat) : Pattern S Nat :=
  substVar x y (avoidBinder y p)

/-- Relational specification exposing the alpha-equivalent, capture-free body
used by total substitution. -/
def IsCaptureAvoidingSubst (x y : Nat) (p q : Pattern S Nat) : Prop :=
  ∃ p', AlphaEq p p' ∧ CaptureFree x y p' ∧ q = substVar x y p'

theorem captureAvoidingSubst_spec (x y : Nat) (p : Pattern S Nat) :
    IsCaptureAvoidingSubst x y p (captureAvoidingSubst x y p) := by
  refine ⟨avoidBinder y p, avoidBinder_alphaEq y p, ?_, rfl⟩
  exact (avoidBinder_avoids y p).captureFree

theorem exists_isCaptureAvoidingSubst (x y : Nat) (p : Pattern S Nat) :
    ∃ q, IsCaptureAvoidingSubst x y p q :=
  ⟨captureAvoidingSubst x y p, captureAvoidingSubst_spec x y p⟩

theorem captureAvoidingSubst_eq_substVar_of_fresh {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : captureAvoidingSubst x y p = substVar x y p := by
  simp [captureAvoidingSubst, avoidBinder_eq_self_of_not_mem_allVars hy]

/-- Total substitution preserves structural complexity, so the substituted body
is available to the strong induction used by the Truth Lemma. -/
theorem complexity_captureAvoidingSubst (x y : Nat) (p : Pattern S Nat) :
    (captureAvoidingSubst x y p).complexity = p.complexity := by
  rw [captureAvoidingSubst, complexity_substVar]
  exact (avoidBinder_alphaEq y p).complexity_eq.symm

theorem IsCaptureAvoidingSubst.complexity_eq {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) : q.complexity = p.complexity := by
  rcases h with ⟨p', halpha, _hcf, rfl⟩
  rw [complexity_substVar]
  exact halpha.complexity_eq.symm

end Pattern

theorem Model.denote_captureAvoidingSubst (M : Model S)
    (rho : Nat → M.carrier) (x y : Nat) (p : Pattern S Nat) :
    M.denote rho (Pattern.captureAvoidingSubst x y p) =
      M.denote (Function.update rho x (rho y)) p := by
  rw [Pattern.captureAvoidingSubst,
    M.denote_substVar_of_captureFree rho
      (Pattern.avoidBinder_avoids y p).captureFree]
  exact (Pattern.avoidBinder_alphaEq y p).denote_eq M _ |>.symm

namespace Pattern

theorem IsCaptureAvoidingSubst.denote {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) (M : Model S)
    (rho : Nat → M.carrier) :
    M.denote rho q = M.denote (Function.update rho x (rho y)) p := by
  rcases h with ⟨p', halpha, hcf, rfl⟩
  rw [M.denote_substVar_of_captureFree rho hcf]
  exact halpha.denote_eq M _ |>.symm

end Pattern

theorem Provable.captureAvoidingExQuant {Gamma : Set (Pattern S Nat)}
    (x y : Nat) (p : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.captureAvoidingSubst x y p) (.ex x p)) := by
  have hcf := (Pattern.avoidBinder_avoids y p).captureFree (x := x)
  have hraw : Provable Gamma
      (.imp (substVar x y (Pattern.avoidBinder y p))
        (.ex x (Pattern.avoidBinder y p))) := .exQuant hcf
  have halpha := Pattern.AlphaEq.ex x (Pattern.avoidBinder_alphaEq y p)
  exact hraw.imp_trans (halpha.backward Gamma)

theorem Pattern.IsCaptureAvoidingSubst.exQuant {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p q : Pattern S Nat} (h : IsCaptureAvoidingSubst x y p q) :
    Provable Gamma (.imp q (.ex x p)) := by
  rcases h with ⟨p', halpha, hcf, rfl⟩
  exact (Provable.exQuant hcf).imp_trans ((AlphaEq.ex x halpha).backward Gamma)

end MatchingLogic
