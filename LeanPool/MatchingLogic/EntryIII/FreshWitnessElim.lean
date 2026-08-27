/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Fresh-witness elimination for the n-ary canonical construction.

Unlike the ordinary `Witnessed` interface, `FreshWitnessed` supplies a name
absent from every raw occurrence of the body being instantiated.  This makes
the substitution-composition step below an equality, including the otherwise
awkward self-substitution case.
-/
import LeanPool.MatchingLogic.EntryIII.WitnessPush
import LeanPool.MatchingLogic.EntryIII.Witnessed

/-!
# MatchingLogic.EntryIII.FreshWitnessElim
-/

namespace MatchingLogic

variable {S : Signature}

namespace Pattern

private theorem allVars_substVar_mem {x y z : Nat} {p : Pattern S Nat}
    (hz : z ∈ (substVar x y p).allVars) : z = y ∨ z ∈ p.allVars := by
  induction p with
  | var a =>
      by_cases hax : a = x
      · subst a
        exact Or.inl (by simpa [substVar, allVars] using hz)
      · simpa [substVar, allVars, hax] using Or.inr hz
  | bot => simp [substVar, allVars] at hz
  | app sigma args ih =>
      simp only [substVar, allVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with ⟨i, hi⟩
      rcases ih i hi with hzy | hmem
      · exact Or.inl hzy
      · exact Or.inr ⟨i, hmem⟩
  | imp p q ihp ihq =>
      simp only [substVar, allVars, Finset.mem_union] at hz ⊢
      rcases hz with hp | hq
      · rcases ihp hp with hzy | hmem
        · exact Or.inl hzy
        · exact Or.inr (Or.inl hmem)
      · rcases ihq hq with hzy | hmem
        · exact Or.inl hzy
        · exact Or.inr (Or.inr hmem)
  | ex a p ih =>
      by_cases hax : a = x
      · subst a
        simp only [substVar, ite_eq_left, allVars, Finset.mem_insert] at hz ⊢
        exact Or.inr hz
      · simp only [substVar, ite_eq_right hax, allVars, Finset.mem_insert] at hz ⊢
        rcases hz with hza | hz
        · exact Or.inr (Or.inl hza)
        · rcases ih hz with hzy | hmem
          · exact Or.inl hzy
          · exact Or.inr (Or.inr hmem)

private theorem substVar_not_mem_allVars_of_ne {x y z : Nat} {p : Pattern S Nat}
    (hzy : z ≠ y) (hz : z ∉ p.allVars) : z ∉ (substVar x y p).allVars := by
  intro h
  rcases allVars_substVar_mem h with hEq | hp
  · exact hzy hEq
  · exact hz hp

private theorem substVar_comp_of_fresh {x y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    substVar y z (substVar x y p) = substVar x z p := by
  induction p with
  | var a =>
      simp only [allVars, Finset.mem_singleton] at hy
      have hay : a ≠ y := Ne.symm hy
      by_cases hax : a = x <;> simp [substVar, hax, hay]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i)
  | imp p q ihp ihq =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      simp [substVar, ihp hy.1, ihq hy.2]
  | ex a p ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hax : a = x
      · subst a
        have hxy : x ≠ y := Ne.symm hy.1
        simp only [substVar, ite_eq_left, ite_eq_right hxy]
        rw [Pattern.substVar_eq_self_of_not_mem_allVars hy.2]
      · have hay : a ≠ y := Ne.symm hy.1
        simp [substVar, hax, hay, ih hy.2]

/-- Exact composition when the result name is fresh for the current body.
The `z = y` case is an inert self-substitution; otherwise support tracking
shows that the second capture-avoidance pass is a raw substitution. -/
theorem captureAvoidingSubst_comp_eq_of_fresh_result {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ p.allVars) (hz : z ∉ p.allVars)
    (hzs : z ∉ (substVar x y p).allVars) :
    captureAvoidingSubst y z (captureAvoidingSubst x y p) =
      captureAvoidingSubst x z p := by
  by_cases hzy : z = y
  · subst z
    rw [captureAvoidingSubst_eq_substVar_of_fresh hy]
    simp only [captureAvoidingSubst, avoidBinder_eq_self_of_not_mem_allVars hzs]
    exact Pattern.substVar_eq_self_of_not_mem_allVars hzs
  · rw [captureAvoidingSubst_eq_substVar_of_fresh hy]
    rw [captureAvoidingSubst_eq_substVar_of_fresh
      (substVar_not_mem_allVars_of_ne hzy hz)]
    rw [captureAvoidingSubst_eq_substVar_of_fresh hz]
    exact substVar_comp_of_fresh hy

end Pattern

/-- One fresh witness may be eliminated inside an MCS while retaining the
strong raw freshness fact needed by subsequent substitutions. -/
theorem IsMCS.freshWitness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {y : Nat} {q : Pattern S Nat}
    (hmem : Pattern.ex y q ∈ Gamma) :
    ∃ z, z ∉ q.allVars ∧ Pattern.captureAvoidingSubst y z q ∈ Gamma := by
  obtain ⟨z, hzfresh, himp⟩ := hW hmem
  exact ⟨z, hzfresh, hM.mp_mem hmem himp⟩

namespace Pattern

/-- The body obtained by successively eliminating an ordered list of names. -/
def substList : List Nat → List Nat → Pattern S Nat → Pattern S Nat
  | y :: ys, z :: zs, p => substList ys zs (substVar y z p)
  | _, _, p => p

/-- The stronger freshness record carried through a nested witness
elimination.  Each returned name is fresh for the exact remaining body. -/
def FreshExListTrace : List Nat → List Nat → Pattern S Nat → Prop
  | [], [], _ => True
  | y :: ys, z :: zs, p =>
      z ∉ (exList ys p).allVars ∧ FreshExListTrace ys zs (substVar y z p)
  | _, _, _ => False

end Pattern

/-- Recursively eliminate an `exList` in a fresh-witness MCS.  The result is
an actual raw substitution trace, not an appeal to alpha quotienting. -/
theorem IsMCS.exList_freshWitness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma)
    (ys : List Nat) (hys : ys.Nodup) (p : Pattern S Nat)
    (hmem : Pattern.exList ys p ∈ Gamma) :
    ∃ zs, Pattern.FreshExListTrace ys zs p ∧ Pattern.substList ys zs p ∈ Gamma := by
  induction ys generalizing p with
  | nil =>
      exact ⟨[], trivial, by simpa [Pattern.exList, Pattern.substList] using hmem⟩
  | cons y ys ih =>
      rcases List.nodup_cons.mp hys with ⟨hyNotMem, hysNodup⟩
      have hynot : ∀ a ∈ ys, y ≠ a := by
        intro a ha hEq
        exact hyNotMem (by simpa [hEq] using ha)
      have htailmem : Pattern.ex y (Pattern.exList ys p) ∈ Gamma := by
        simpa [Pattern.exList] using hmem
      obtain ⟨z, hzfresh, hsub⟩ := hM.freshWitness_elim hW htailmem
      have hraw : substVar y z (Pattern.exList ys p) ∈ Gamma := by
        simpa [Pattern.captureAvoidingSubst_eq_substVar_of_fresh hzfresh] using hsub
      have hnext : Pattern.exList ys (substVar y z p) ∈ Gamma := by
        rw [← Pattern.substVar_exList ys p hynot]
        exact hraw
      obtain ⟨zs, htrace, hlast⟩ := ih hysNodup (substVar y z p) hnext
      refine ⟨z :: zs, ?_, ?_⟩
      · exact ⟨hzfresh, htrace⟩
      · simpa [Pattern.substList] using hlast

/-- Apply Lemma 80 and eliminate its nested existential witnesses using the
fresh strengthened interface.  `FreshExListTrace` records exactly the
all-variable freshness available at every recursive step, so consumers do not
need to guess a raw-syntax normalization convention. -/
theorem IsMCS.witnessPush_freshTrace {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ z : List Nat,
      Pattern.FreshExListTrace (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∧
      Pattern.substList (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma := by
  let body : Pattern S Nat := .app sigma (fun i => Pattern.and (Phi i)
    (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))
  have hpush : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi) (Pattern.exList (List.ofFn y) body)) := by
    simpa [body] using Provable.witnessPush Phi p x y hyinj
      (fun i h => hyfreshP i (p.FV_subset_allVars h))
      (fun i j h => hyfreshPhi i j ((Phi j).FV_subset_allVars h))
  have hnested : Pattern.exList (List.ofFn y) body ∈ Gamma :=
    hM.mem_of_provable_imp happ hpush
  have hnodup : (List.ofFn y).Nodup := by
    rw [List.nodup_ofFn]
    exact hyinj
  simpa [body] using hM.exList_freshWitness_elim hW (List.ofFn y) hnodup body hnested

end MatchingLogic
