/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Hoare.HoareTheory
import LeanPool.MRiscX.Delab.DelabHoare
import Mathlib.Data.Set.BooleanAlgebra

/-!
This file contains the hoare rules from the paper of lundberg et al.
Those rules are being defined and proved.
By proving these rules, we archive
1. showing the correctness of the rules themselves
2. verifying the compatibility of the constructed machine model and the hoare
  logic from lundberg et al.


The assumptions of Hoare's rules used here differ in some respects from those in lundberg et al.
This is because conditions such as $L_W \cap L_B = \emptyset$ are preconditions from
the judgement of \mathcal{L}_{AS}.
These statements must be valid in order for the conditions for applying the assumptions to be met.

TODO: prove of S_LOOP
-/

/--
Allows to weaken the Hoare triple by removing a set
`L` from `L_B` without any restrictions
-/
theorem BL_SUBSET : ∀ (code : Code) (P Q : Assertion) (l: UInt64) (L_w L_b L : Set UInt64),
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b \ L⟩⦃Q⦄
:= by
  intros c P Q l L_w L_b L T
  unfold hoareTripleUp
  intros H _ h_LwEmpty s HCode pre H_pc
  have L_b_sub : L_b \ L ⊆ L_b := by
    apply Set.diff_subset
  specialize H T h_LwEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  constructor
  · apply weak_with_less_BL_weakens; exact H1
  · constructor
    · exact H2
    · apply Set.notMem_subset
      · exact L_b_sub
      · exact H3

/--
Allows to weaken the Hoare triple
by moving a set `L` it to `L_W` without restrictions.
-/
theorem BL_TO_WL : ∀ (code : Code) (P Q : Assertion) (l : UInt64) (L_w L_b L : Set UInt64),
  L ⊆ L_b →
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  L_w ≠ ∅ →
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  code
  ⦃P⦄ l ↦ ⟨L_w ∪ L | L_b \ L⟩⦃Q⦄
  := by
  intros c P Q l L_w L_b L TSub TInter TEmpty
  unfold hoareTripleUp
  intros H _ _ s HCode pre H_pc
  specialize H  TInter TEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  unfold weak
  constructor
  · apply weak_L_w_with_L_from_L_b <;> try assumption
  · constructor <;> try assumption
    apply Set.notMem_subset (t := L_b) <;> try assumption
    apply Set.diff_subset



/--
This rule can be used to transfer the set `L` from `L_W` to `L_B`.
However, this requires that the postcondition `Q` does not cause the PC
to point to a line from `L`.
-/
theorem WL_TO_BL : ∀ (c : Code) (P Q : Assertion) (l : UInt64) (L_w L_b L : Set UInt64),
  L ⊂ L_w →
  (∀ (s:MState), Q s → s.pc ∉ L) →
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w \ L | L_b ∪ L⟩⦃Q⦄
  := by
  intros c P Q l L_w L_b L HLSubL_w HSPost TInter TEmpty
  unfold hoareTripleUp
  intros H _ _ s HCode  pre H_pc
  specialize H TInter TEmpty s HCode  pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  unfold weak at H1
  specialize H1 HCode
  rcases H1 with ⟨n', ⟨H1', H2', H3', H4'⟩⟩
  unfold weak
  exists s'
  constructor
  · intros _
    exists n'
    try repeat (constructor <;> try assumption)
    · apply HSPost
      exact H2
    · intros n'' Hn''
      specialize H4' n'' Hn''
      apply MState.runNSteps_diff <;> try assumption
      simp only [Set.union_subset_iff, Set.diff_subset_iff, Set.subset_union_right, true_and]
      constructor
      · intros hx h
        apply Set.mem_union_right
        exact Set.mem_union_left L_b h
      · intros hx h
        apply Set.mem_union_left
        apply HLSubL_w.left h
  · constructor
    · exact H2
    · simp only [Set.mem_union, not_or]
      constructor
      · exact H3
      · apply HSPost
        exact H2



/--
Enables the merge of two Hoare-triples into one, given that the postcondition
of the first triple is equal to the precondition of the second triple.
-/
theorem S_SEQ' : ∀(P R Q : Assertion) (c : Code) (l : UInt64) (L_w L_b L_w' L_b' : Set UInt64),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃R⦄ →
  (∀ l', l' ∈ L_w →
  c
  ⦃R⦄ l' ↦ ⟨L_w' | L_b'⟩ ⦃Q⦄) →
  c
  ⦃P⦄ l ↦ ⟨L_w' | L_b ∩ L_b'⟩ ⦃Q⦄
  := by
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoareTripleUp
  intros HFirst HSecond _ h_empty' s HCode H_pc pre
  specialize HFirst TInter TEmpty s HCode H_pc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  specialize HFirstWeak HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    simp
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  specialize HSecondWeak HCode'
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  · unfold weak
    intros HCode
    exists (m + m')
    constructor <;> try assumption
    · exact Nat.add_gt_zero _ _ HFW1
    · constructor <;> try assumption
      · rw [<- HFW2] at HSW2
        simp only [MState.run_n_m_steps_comp] at HSW2
        exact HSW2
      · constructor <;> try assumption
        · intros m'' Hm''
          apply MState.run_n_plus_m_intersect <;> assumption
  · constructor <;> try assumption
    · simp only [Set.mem_inter_iff, not_and]
      intros _
      exact HSecondPc



/--
Enables the merge of two Hoare-triples into one, given that the postcondition
of the first triple is equal to the precondition of the second triple.

This rule lets you apply S_SEQ with any form of `L_{B''}` but asks for
a proof of `L_{B''} = L_B ∩ L_{B'}`
-/
theorem S_SEQ {L_b'' : Set UInt64} :
    ∀(P R Q : Assertion) (c : Code) (l : UInt64) (L_w L_b L_w' L_b' : Set UInt64),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃R⦄ →
  (∀ l':UInt64, l' ∈ L_w →
  c
  ⦃R⦄ l' ↦ ⟨L_w' | L_b'⟩ ⦃Q⦄) →
  L_b'' = L_b ∩ L_b' →
  c
  ⦃P⦄ l ↦ ⟨L_w' | L_b''⟩ ⦃Q⦄
  := by
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoareTripleUp
  intros HFirst HSecond def_L_b'' _ h_empty' s HCode H_pc pre
  specialize HFirst TInter TEmpty s HCode H_pc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  specialize HFirstWeak HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    simp
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  specialize HSecondWeak HCode'
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  · unfold weak
    intros HCode
    exists (m + m')
    constructor <;> try assumption
    · exact Nat.add_gt_zero _ _ HFW1
    · constructor <;> try assumption
      · rw [<- HFW2] at HSW2
        simp only [MState.run_n_m_steps_comp] at HSW2
        exact HSW2
      · constructor <;> try assumption
        · intros m'' Hm''
          rw [def_L_b'']
          apply MState.run_n_plus_m_intersect <;> assumption
  · constructor <;> try assumption
    · rw [def_L_b'']
      simp only [Set.mem_inter_iff, not_and]
      intros _
      exact HSecondPc


/--
Allows to strenghten the precondition of a given Hoare-triple
-/
theorem PRE_STR : ∀(c : Code) (P1 P2 Q : Assertion) (L_w L_b : Set UInt64) (l : UInt64),
  (∀ (s : MState),
  s.code = c →
  (s.pc = l ∧ P2 s) → P1 s) →
  c
  ⦃P1⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P2⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by
  intros c P1 P2 Q L_w L_b l HTaut
  unfold hoareTripleUp
  intros H HInter HEmpty s HCode H_pc pre
  apply H HInter <;> try assumption
  specialize HTaut s HCode
  · apply HTaut
    · constructor <;> try assumption


/--
Allows to weaken the postcondition of a given Hoare-triple
-/
theorem POST_WEAK : ∀(c : Code) (P Q1 Q2 : Assertion) (L_w L_b : Set UInt64) (l : UInt64),
  (∀ (s : MState),
  s.code = c →
  (s.pc ∈ L_w ∧ Q1 s) → Q2 s) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q1⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q2⦄
  := by
  intros c P Q1 Q2 L_w L_b l
  unfold hoareTripleUp
  intros HTaut H HInter HEmpty  s HCode pre H_pc
  specialize H HInter HEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨P1, P2, P3⟩⟩
  exists s'
  constructor; try assumption
  · constructor <;> try assumption
    · apply HTaut
      · unfold weak at P1
        specialize P1 HCode
        rcases P1 with ⟨_, _, K, _⟩
        rw [← K]
        simp only [MState.runNSteps_code_remains]
        exact HCode
      · constructor <;> try assumption
        · unfold weak at P1
          specialize P1 HCode
          rcases P1 with ⟨_, _, _, K, _⟩
          exact K


/--
In this rule, a condition `C` is evaluated and, depending on whether it is fulfilled or not,
either the command chain `S_1` or `S_2`$ is executed.
-/
theorem S_COND : ∀ (c : Code) (P C Q : Assertion) (l : UInt64)
  (L_w L_b : Set UInt64),
  c
  ⦃P ∧∧ C⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P ∧∧ ∼C⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by
  intros c P C Q l L_w L_b
  unfold hoareTripleUp
  intros h_RunCondTrue h_RunCondFalse h_LwInterLb h_LwNotEmpty s h_code h_pc pre
  specialize h_RunCondTrue h_LwInterLb h_LwNotEmpty s h_code
  specialize h_RunCondFalse h_LwInterLb h_LwNotEmpty s h_code
  apply excluded_middle_implication (P s) (C s)
  constructor
  · intros H
    specialize h_RunCondTrue h_pc H
    exact h_RunCondTrue
  · intros H
    specialize h_RunCondFalse h_pc H
    exact h_RunCondFalse
  exact pre


/--
A rule to verify the formal correctness of a loop.
Requires:

* A Condition `C`
* An Invariant `I`
* A Variant `V`


  High-level proof idea of S_LOOP

  - Define C v := “for any state s at l with invariant I and variant V s = v, we can reach some s'
      satisfying Q via weak with the original L_w/L_b.”
  - Prove C v by well-founded induction on v.
      - If C s (the loop condition) holds, use the given loop-body triple at variant v to get a next
          state s' back at l with strictly smaller variant (V s' < v) and still I.
        Then apply induction hypothesis to V s' to get a final state s'' satisfying Q.
        Finally, compose the two runs to build weak s s'' ... (this is where we stitch step counts
          and the “no earlier hit” condition).
      - If ¬C s, use the given exit triple to get Q directly.
  - Apply C (V s) to your original starting state s.
-/
theorem S_LOOP {α : Type} [Preorder α] [WellFoundedLT α] :
    ∀ (Q C I : Assertion) (code : Code) (l : UInt64)
    (L_w L_b : Set UInt64) (V : MState → α),
  l ∉ L_w →
  l ∉ L_b →
  (∀ (x : α),
    code
    ⦃fun st => C st ∧ I st ∧ V st = x⦄
    l ↦ ⟨{l} ∪ L_w | L_b⟩
    ⦃fun st => V st < x ∧ I st ∧ st.pc = l⦄) →
  code
  ⦃fun st => ¬C st ∧ I st⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  code
  ⦃I⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by
  intros Q C I code l L_w L_b V h_l_not_mem_Lw h_l_not_mem_Lb h_true h_false
  unfold hoareTripleUp
  intros h_inter h_nonempty s h_code h_pc hI
  have h_inter' : ({l} ∪ L_w) ∩ L_b = ∅ := by
    rw [Set.union_inter_distrib_right]
    simp only [Set.union_empty_iff, Set.singleton_inter_eq_empty]
    constructor
    · exact h_l_not_mem_Lb
    · exact h_inter
  have h_nonempty' : ({l} ∪ L_w) ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty, Set.union_nonempty]
    right
    rw [Set.nonempty_iff_ne_empty]
    exact h_nonempty
  let P : α → Prop :=
    fun v =>
      ∀ s : MState,
        s.code = code →
        s.pc = l →
        I s →
        V s = v →
        ∃ s', weak s s' L_w L_b code ∧ Q s' ∧ s'.pc ∉ L_b
  have loop_correct_at : ∀ v, P v := by
    let wf := (inferInstance : WellFoundedLT α).wf
    intro v0
    apply wf.induction v0
    intro v ih s h_code h_pc hI hV
    by_cases hC : C s
    · -- Guard true: run one loop iteration, then recurse on the smaller variant.
      have hpre : C s ∧ I s ∧ V s = v := by
        exact ⟨hC, hI, hV⟩
      specialize h_true v h_inter' h_nonempty' s h_code h_pc hpre
      rcases h_true with ⟨s', hweak', ⟨hVlt, hI', hpc'⟩, hnotinLb'⟩
      have h_code' : s'.code = code := by
        specialize hweak' h_code
        rcases hweak' with ⟨m, hm_pos, hrun, -, -⟩
        exact MState.code_remains_same s s' code m h_code hrun
      specialize ih (V s') hVlt s' h_code' hpc' hI' rfl
      rcases ih with ⟨s'', hweak'', hQ'', hnotinLb''⟩
      have hweak : weak s s'' L_w L_b code := by
        unfold weak
        intro h_code0
        specialize hweak' h_code0
        rcases hweak' with ⟨m, hm_pos, hrun, -, hsafe⟩
        specialize hweak'' h_code'
        rcases hweak'' with ⟨m', hm'_pos, hrun', hpc_in, hsafe'⟩
        refine ⟨m + m', Nat.add_gt_zero _ _ hm_pos, ?_, hpc_in, ?_⟩
        · apply MState.runNSteps_add <;> try assumption
        · intro n hn
          apply MState.run_n_plus_m_pc_not_in_set (set := (L_w ∪ L_b)) <;> try assumption
          intro n' hn'
          rcases hn' with ⟨hn'le, hn'le_m⟩
          rw [Nat.le_iff_lt_or_eq] at hn'le_m
          cases hn'le_m with
          | inl hlt =>
              specialize hsafe n' ⟨hn'le, hlt⟩
              simp only [Set.mem_union] at hsafe
              push Not at hsafe
              rcases hsafe with ⟨⟨-, hnotLw⟩, hnotLb⟩
              simp only [Set.mem_union, not_or]
              exact ⟨hnotLw, hnotLb⟩
          | inr heq =>
              simp only [Set.mem_union, not_or]
              rw [heq, hrun, hpc']
              exact ⟨h_l_not_mem_Lw, h_l_not_mem_Lb⟩
      exact ⟨s'', hweak, hQ'', hnotinLb''⟩
    · -- Guard false: discharge with the exit rule.
      exact h_false h_inter h_nonempty s h_code h_pc ⟨hC, hI⟩
  exact loop_correct_at (V s) s h_code h_pc hI rfl
