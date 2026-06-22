/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.VCDimension

/-!
# Littlestone Dimension (Online Paradigm)

The online-learning analog of VC dimension.
Characterizes mistake-bounded learnability.
-/

universe u v

/-- A mistake tree (Littlestone tree): a complete binary tree
    where each internal node is labeled with an instance x. -/
inductive MistakeTree (X : Type u) where
  | leaf : MistakeTree X
  | branch : X → MistakeTree X → MistakeTree X → MistakeTree X

/-- Depth of a mistake tree. -/
def MistakeTree.depth {X : Type u} : MistakeTree X → ℕ
  | .leaf => 0
  | .branch _ l r => 1 + max l.depth r.depth

/-- A mistake tree is shattered by C if every root-to-leaf path is
    realized by some concept in C.

    **Note:** This branch-wise definition does NOT restrict the concept class at
    recursive calls. It allows different witness concepts at each tree level without
    requiring path consistency. Counterexample: C = {const_true, const_false} gives
    LittlestoneDim = ⊤ under this definition, but C is online-learnable with M = 1.

    The correct definition (used in `Theorem/Online.lean`) restricts C at each branch:
      | .branch x l r =>
          (∃ c ∈ C, c x = true) ∧ (∃ c ∈ C, c x = false) ∧
          isShattered X {c ∈ C | c x = true} l ∧
          isShattered X {c ∈ C | c x = false} r

    The characterization theorem uses the corrected version. -/
def MistakeTree.isShattered (X : Type u) (C : ConceptClass X Bool) :
    MistakeTree X → Prop
  | .leaf => True
  | .branch x l r =>
      (∃ c ∈ C, c x = true ∧ MistakeTree.isShattered X C l) ∧
      (∃ c ∈ C, c x = false ∧ MistakeTree.isShattered X C r)

/-- Littlestone dimension (branch-wise variant): see `Theorem/Online.lean` for the
    corrected path-consistent version used in the characterization theorem. -/
noncomputable def BranchWiseLittlestoneDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (T : MistakeTree X) (_ : T.isShattered X C), (T.depth : WithTop ℕ)

/-- Build a complete binary tree from a list of instances. -/
def MistakeTree.fromList {X : Type u} : List X → MistakeTree X
  | [] => .leaf
  | x :: xs => .branch x (fromList xs) (fromList xs)

/-- The depth of a mistake tree built from a list of length `n` equals `n`. The basic
well-formedness property of the `fromList` constructor: depth tracks list length
exactly, so the Littlestone dimension can be read off from a built tree. -/
theorem MistakeTree.fromList_depth {X : Type u} :
    ∀ (l : List X), (MistakeTree.fromList l).depth = l.length
  | [] => rfl
  | _ :: xs => by
    simp only [MistakeTree.fromList, MistakeTree.depth, fromList_depth xs, Nat.max_self,
      List.length_cons]
    omega

/-- If C shatters a Finset S (every labeling realized), restricting to a subset still shatters. -/
theorem Shatters.subset {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hS : Shatters X C S) (hTS : T ⊆ S) : Shatters X C T := by
  classical
  intro f
  -- Extend `f` from `T` to `S` by `false` outside `T`.
  let g : ↥S → Bool := fun ⟨x, _⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hc⟩ := hS g
  refine ⟨c, hcC, fun ⟨x, hx⟩ => ?_⟩
  have := hc ⟨x, hTS hx⟩
  simpa only [g, dif_pos hx] using this

/-- A shattered tree can be built from any list of elements from a shattered Finset. -/
theorem MistakeTree.fromList_shattered {X : Type u} [DecidableEq X] {C : ConceptClass X Bool}
    (l : List X) (hl : l.Nodup) (hS : Shatters X C l.toFinset) :
    (MistakeTree.fromList l).isShattered X C := by
  induction l with
  | nil => exact trivial
  | cons x xs ih =>
    unfold fromList isShattered
    have hnd := (List.nodup_cons.mp hl).2
    have hxS : x ∈ (x :: xs).toFinset := by simp
    have hsub : xs.toFinset ⊆ (x :: xs).toFinset := by
      intro a ha
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at ha ⊢
      exact Or.inr ha
    have hxs_shat : Shatters X C xs.toFinset := hS.subset hsub
    refine ⟨?_, ?_⟩
    · obtain ⟨c, hcC, hc⟩ := hS (fun _ => true)
      exact ⟨c, hcC, hc ⟨x, hxS⟩, ih hnd hxs_shat⟩
    · obtain ⟨c, hcC, hc⟩ := hS (fun _ => false)
      exact ⟨c, hcC, hc ⟨x, hxS⟩, ih hnd hxs_shat⟩

/-- Ldim (branch-wise) upper bounds VCdim: Ldim(C) ≥ VCdim(C) for all C.
    Uses the branch-wise definition. See Theorem/Online.lean for the corrected version. -/
theorem BranchWiseLittlestoneDim_ge_VCDim (X : Type u)
    (C : ConceptClass X Bool) : VCDim X C ≤ BranchWiseLittlestoneDim X C := by
  classical
  unfold VCDim BranchWiseLittlestoneDim
  apply iSup₂_le
  intro S hS
  let T := MistakeTree.fromList S.toList
  have hd : T.depth = S.card := by
    simp only [T, MistakeTree.fromList_depth]
    exact S.length_toList
  have ht : T.isShattered X C :=
    MistakeTree.fromList_shattered _ S.nodup_toList (by rwa [Finset.toList_toFinset])
  exact hd ▸ le_iSup₂_of_le T ht le_rfl
