/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Raw-syntax alpha conversion for entry point (iii).

The source identifies alpha-equivalent patterns.  The verified base instead
uses raw names and a partial, side-conditioned variable substitution.  The
lemmas below recover the source's binder-renaming step when the replacement
name is absent from `allVars`, hence absent both free and bound.
-/
import LeanPool.MatchingLogic.EntryIII.Fresh
import LeanPool.MatchingLogic.ProofSystem

/-!
# MatchingLogic.EntryIII.Alpha
-/

namespace MatchingLogic

variable {S : Signature}

namespace Pattern

/-- Substitution does nothing when its source name occurs neither free nor bound. -/
theorem substVar_eq_self_of_not_mem_allVars {x y : Nat} {p : Pattern S Nat}
    (hx : x ∉ p.allVars) : substVar x y p = p := by
  induction p with
  | var z =>
      simp only [allVars, Finset.mem_singleton] at hx
      simp [substVar, Ne.symm hx]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hx
      simp only [substVar]
      congr
      funext i
      exact ih i (hx i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hx
      simp [substVar, ihphi hx.1, ihpsi hx.2]
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hx
      simp [substVar, Ne.symm hx.1, ih hx.2]

/-- Replacing `x` by a wholly fresh `y`, then `y` by `x`, is literally the
original raw pattern.  No quotient by alpha equivalence is used. -/
theorem substVar_roundtrip {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    substVar y x (substVar x y p) = p := by
  induction p with
  | var z =>
      simp only [allVars, Finset.mem_singleton] at hy
      by_cases hzx : z = x
      · subst z
        simp [substVar]
      · have hzy : z ≠ y := Ne.symm hy
        simp [substVar, hzx, hzy]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      simp [substVar, ihphi hy.1, ihpsi hy.2]
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hzx : z = x
      · subst z
        by_cases hxy : x = y
        · subst y
          simp [substVar]
        · simp [substVar, hxy, substVar_eq_self_of_not_mem_allVars hy.2]
      · have hzy : z ≠ y := Ne.symm hy.1
        simp [substVar, hzx, hzy, ih hy.2]

/-- A name absent from all raw occurrences is capture-free as a replacement. -/
theorem captureFree_of_not_mem_allVars {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : CaptureFree x y p := by
  induction p with
  | var z => trivial
  | bot => trivial
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hy
      intro i
      exact ih i (hy i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      exact ⟨ihphi hy.1, ihpsi hy.2⟩
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (Or.inr ⟨Ne.symm hy.1, ih hy.2⟩)

/-- The reverse leg of a fresh substitution is itself capture-free. -/
theorem captureFree_reverse_substVar {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    CaptureFree y x (substVar x y p) := by
  induction p with
  | var z =>
      rw [substVar]
      split <;> trivial
  | bot => trivial
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hy
      intro i
      exact ih i (hy i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      exact ⟨ihphi hy.1, ihpsi hy.2⟩
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hzx : z = x
      · subst z
        simp only [substVar, ite_eq_left]
        exact Or.inr (Or.inl (fun hymem => hy.2 (phi.FV_subset_allVars hymem)))
      · simp only [substVar, ite_eq_right hzx]
        exact Or.inr (Or.inr ⟨hzx, ih hy.2⟩)

/-- If source and replacement differ, no free source occurrence remains after
variable-for-variable substitution. -/
theorem substVar_source_not_mem_FV {x y : Nat} (p : Pattern S Nat)
    (hxy : x ≠ y) : x ∉ FV (substVar x y p) := by
  induction p with
  | var z =>
      by_cases hzx : z = x
      · subst z
        simp [substVar, hxy]
      · simp [substVar, hzx, Ne.symm hzx]
  | bot => simp [substVar]
  | app sigma args ih =>
      simp only [substVar, FV_app, Set.mem_iUnion, not_exists]
      exact ih
  | imp phi psi ihphi ihpsi =>
      simp [substVar, ihphi, ihpsi]
  | ex z phi ih =>
      by_cases hzx : z = x
      · subst z
        simp [substVar]
      · simp only [substVar, ite_eq_right hzx, FV_ex]
        intro hxmem
        exact ih hxmem.1

end Pattern

/-- Derived forward alpha conversion for an existential binder. -/
theorem Provable.alphaEx_forward {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex x p) (.ex y (substVar x y p))) := by
  have hq : Provable Gamma
      (.imp (substVar y x (substVar x y p)) (.ex y (substVar x y p))) :=
    .exQuant (Pattern.captureFree_reverse_substVar hy)
  rw [Pattern.substVar_roundtrip hy] at hq
  by_cases hxy : x = y
  · subst y
    exact .exGen hq (by simp)
  · exact .exGen hq (by
      intro hx
      exact Pattern.substVar_source_not_mem_FV p hxy hx.1)

/-- Derived backward alpha conversion for an existential binder. -/
theorem Provable.alphaEx_backward {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex y (substVar x y p)) (.ex x p)) := by
  exact .exGen (.exQuant (Pattern.captureFree_of_not_mem_allVars hy)) (by
    intro hymem
    exact hy (p.FV_subset_allVars hymem.1))

end MatchingLogic
