/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The arity-zero boundary case of Chen--Rosu's Theorem 73.

The general, simultaneous finite-stage construction belongs below this
boundary lemma.  Keeping the zero-arity case explicit is important: the
paper's definition says that a constant is interpreted by the worlds which
contain that constant, and no argument-world construction may be smuggled in.
-/
import LeanPool.MatchingLogic.EntryIII.CanonicalCore

/-!
# MatchingLogic.EntryIII.CanonicalExistence
-/

namespace MatchingLogic

open Set

variable {S : Signature}

noncomputable section

/-- The exact one-sorted universal statement of the source's canonical
Existence Lemma.  It lives with the stage-system interface so the construction
precedes, rather than imports, the Truth Lemma that consumes it. -/
def CanonicalExistenceProperty (S : Signature) : Prop :=
  ∀ (Gamma : CanonicalCarrier S) (sigma : S.Sym)
    (args : Fin (S.arity sigma) → Pattern S Nat),
    Pattern.app sigma args ∈ Gamma.val →
      ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
        (∀ i, args i ∈ (components i).val) ∧
          Gamma ∈ canonicalInterp sigma components

/-! ### The simultaneous finite-stage invariant

The following is the exact one-sorted form of the invariant in the proof of
TR Theorem 73.  A stage is a *finite list* at every argument position.  The
important `app_mem` field is joint: extending each argument theory separately
would not establish the universal clause of `canonicalInterp`.
-/

/-- The finite, simultaneous construction used in the n-ary Existence Lemma.
`enum` is shared by every argument position because this development is
one-sorted.  `decide` is condition (1), `witness` is condition (2), and
`app_mem` is condition (4) in the source proof. -/
structure NaryStageSystem (sigma : S.Sym) (Gamma : CanonicalCarrier S)
    (phi : Fin (S.arity sigma) → Pattern S Nat) (enum : Nat → Pattern S Nat) where
  /-- The finite theory accumulated at each stage and argument position. -/
  stages : Nat → Fin (S.arity sigma) → List (Pattern S Nat)
  base : ∀ i, phi i ∈ stages 0 i
  mono : ∀ k i, ∀ q ∈ stages k i, q ∈ stages (k + 1) i
  app_mem : ∀ k, Pattern.app sigma (fun i => conj (stages k i)) ∈ Gamma.val
  decide : ∀ k i, enum k ∈ stages (k + 1) i ∨ Pattern.nt (enum k) ∈ stages (k + 1) i
  witness : ∀ k i x p, enum k = Pattern.ex x p →
    ∃ y, y ∉ p.allVars ∧
      Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ stages (k + 1) i

/-! ### Simultaneous fresh tuples for Lemma 80 -/

namespace Pattern

/-- A finite bound containing every raw variable (free or bound) of the
existential body and of all finite-stage component conjunctions. -/
def tupleAllVars (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Finset Nat :=
  p.allVars ∪ Finset.univ.biUnion (fun i => (Phi i).allVars)

private def tupleFreshBase (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Nat :=
  (insert 0 (tupleAllVars p Phi)).max' (by simp)

/-- The source's tuple of pairwise distinct fresh variables, constructed from
a single finite support bound.  The stronger `allVars` freshness makes the
later raw-syntax alpha bridge possible. -/
def freshTuple (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Fin n → Nat :=
  fun i => tupleFreshBase p Phi + 1 + i.val

private theorem le_tupleFreshBase {p : Pattern S Nat} {Phi : Fin n → Pattern S Nat}
    {z : Nat} (hz : z ∈ tupleAllVars p Phi) : z ≤ tupleFreshBase p Phi := by
  exact Finset.le_max' (insert 0 (tupleAllVars p Phi)) z (Finset.mem_insert_of_mem hz)

theorem freshTuple_injective (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) :
    Function.Injective (freshTuple p Phi) := by
  intro i j hij
  apply Fin.ext
  dsimp [freshTuple] at hij
  omega

theorem freshTuple_not_mem_body_allVars (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat)
    (i : Fin n) : freshTuple p Phi i ∉ p.allVars := by
  intro hi
  have hle := le_tupleFreshBase (p := p) (Phi := Phi)
    (Finset.mem_union_left _ hi)
  dsimp [freshTuple] at hle
  omega

theorem freshTuple_not_mem_component_allVars (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ (Phi j).allVars := by
  intro hi
  have hsupport : freshTuple p Phi i ∈ tupleAllVars p Phi := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
  have hle := le_tupleFreshBase (p := p) (Phi := Phi) hsupport
  dsimp [freshTuple] at hle
  omega

theorem freshTuple_not_mem_body_FV (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat)
    (i : Fin n) : freshTuple p Phi i ∉ FV p := by
  intro hi
  exact freshTuple_not_mem_body_allVars p Phi i (p.FV_subset_allVars hi)

theorem freshTuple_not_mem_component_FV (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ FV (Phi j) := by
  intro hi
  exact freshTuple_not_mem_component_allVars p Phi i j ((Phi j).FV_subset_allVars hi)

end Pattern

namespace NaryStageSystem

variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)

/-- The component theory at the limit of the finite construction. -/
def limit (i : Fin (S.arity sigma)) : Set (Pattern S Nat) :=
  {q | ∃ k, q ∈ T.stages k i}

theorem stage_mono {k l : Nat} (hkl : k ≤ l) (i : Fin (S.arity sigma))
    {q : Pattern S Nat} (hq : q ∈ T.stages k i) : q ∈ T.stages l i := by
  induction l, hkl using Nat.le_induction with
  | base => exact hq
  | succ l hle ih => exact T.mono l i _ ih

private theorem conj_imp_mem (l : List (Pattern S Nat)) {q : Pattern S Nat}
    (hq : q ∈ l) :
    Provable (∅ : Set (Pattern S Nat)) (.imp (conj l) q) := by
  induction l with
  | nil => simp at hq
  | cons a l ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · simpa [conj] using Provable.and_elim_left (∅ : Set (Pattern S Nat)) _ _
      · simpa [conj] using
          (Provable.and_elim_right (∅ : Set (Pattern S Nat)) _ _).imp_trans (ih hq)

private theorem conj_imp_of_subset (l r : List (Pattern S Nat))
    (hsub : ∀ q ∈ r, q ∈ l) :
    Provable (∅ : Set (Pattern S Nat)) (.imp (conj l) (conj r)) := by
  induction r with
  | nil =>
      simpa [conj] using
        (provable_top (∅ : Set (Pattern S Nat))).imp_of (psi := conj l)
  | cons q r ih =>
      simpa [conj] using
        (conj_imp_mem l (hsub q (by simp))).imp_and
          (ih (fun p hp => hsub p (by simp [hp])))

/-- Condition (4) makes every finite stage locally consistent.  This is the
source's framing-to-bottom argument, factored through the singleton result in
`CanonicalCore`. -/
theorem stage_locConsistent (k : Nat) (i : Fin (S.arity sigma)) :
    LocConsistent ({q | q ∈ T.stages k i} : Set (Pattern S Nat)) := by
  intro hbad
  rcases hbad with ⟨r, hr, hbot⟩
  have hsub : ∀ q ∈ r, q ∈ T.stages k i := by
    intro q hq
    exact hr q hq
  have hconjbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (conj (T.stages k i)) .bot) :=
    (conj_imp_of_subset (T.stages k i) r hsub).imp_trans hbot
  have hsingle : LocConsistent ({conj (T.stages k i)} : Set (Pattern S Nat)) :=
    (CanonicalCarrier.isMCS Gamma).singleton_argument_locConsistent (T.app_mem k) i
  apply hsingle
  exact (LocProvable.of_mem (by simp)).mp (LocProvable.of_provable hconjbot)

/-- A finite collection of limit premises already appears at a common stage. -/
private theorem finite_limit_covered (i : Fin (S.arity sigma))
    (l : List (Pattern S Nat)) (hl : ∀ q ∈ l, q ∈ T.limit i) :
    ∃ k, ∀ q ∈ l, q ∈ T.stages k i := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
      rcases hl q (by simp) with ⟨kq, hkq⟩
      rcases ih (by intro p hp; exact hl p (by simp [hp])) with ⟨kl, hkl⟩
      refine ⟨max kq kl, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact T.stage_mono (Nat.le_max_left _ _) i hkq
      · exact T.stage_mono (Nat.le_max_right _ _) i (hkl p hp)

theorem limit_locConsistent (i : Fin (S.arity sigma)) : LocConsistent (T.limit i) := by
  intro hbad
  rcases hbad with ⟨l, hl, hbot⟩
  rcases T.finite_limit_covered i l hl with ⟨k, hk⟩
  exact T.stage_locConsistent k i ⟨l, hk, hbot⟩

theorem limit_freshWitnessed (henum : Function.Surjective enum)
    (i : Fin (S.arity sigma)) : FreshWitnessed (T.limit i) := by
  intro x p _hp
  obtain ⟨k, hk⟩ := henum (.ex x p)
  obtain ⟨y, hyfresh, hy⟩ := T.witness k i x p hk
  exact ⟨y, hyfresh, k + 1, hy⟩

theorem limit_witnessed (henum : Function.Surjective enum)
    (i : Fin (S.arity sigma)) : Witnessed (T.limit i) :=
  FreshWitnessed.toWitnessed (T.limit_freshWitnessed henum i)

theorem limit_isMCS (henum : Function.Surjective enum) (i : Fin (S.arity sigma)) :
    IsMCS (T.limit i) := by
  constructor
  · exact T.limit_locConsistent i
  · intro Delta hstrict hDelta
    rcases Set.ssubset_iff_subset_ne.mp hstrict with ⟨hsub, hne⟩
    have hnot : ¬ Delta ⊆ T.limit i := by
      intro h
      exact hne (Set.Subset.antisymm hsub h)
    rcases Set.not_subset.mp hnot with ⟨q, hqD, hqL⟩
    rcases henum q with ⟨k, rfl⟩
    rcases T.decide k i with hpos | hneg
    · exact hqL ⟨k + 1, hpos⟩
    · apply hDelta
      exact (LocProvable.of_mem hqD).mp (LocProvable.of_mem (hsub ⟨k + 1, hneg⟩))

theorem limit_contains_base (i : Fin (S.arity sigma)) : phi i ∈ T.limit i :=
  ⟨0, T.base i⟩

/-- The joint invariant implies the universal membership condition of the
canonical interpretation. -/
theorem root_mem_canonicalInterp (henum : Function.Surjective enum) :
    Gamma ∈ canonicalInterp sigma
        (fun i => ⟨T.limit i, ⟨T.limit_isMCS henum i,
          T.limit_freshWitnessed henum i⟩⟩) := by
  intro args hargs
  classical
  choose k hk using hargs
  let K : Nat := Finset.univ.sup k
  have hle : ∀ i : Fin (S.arity sigma), k i ≤ K := by
    intro i
    exact Finset.le_sup (s := Finset.univ) (f := k) (by simp)
  have hstage : ∀ i : Fin (S.arity sigma), args i ∈ T.stages K i := by
    intro i
    exact T.stage_mono (hle i) i (hk i)
  exact (CanonicalCarrier.isMCS Gamma).app_mem_of_mono
    (fun i => conj_imp_mem (T.stages K i) (hstage i)) (T.app_mem K)

/-- Once the paper's simultaneous finite-stage invariant has been built, its
limit gives exactly the component worlds required by Theorem 73. -/
theorem canonicalExistence_of_stageSystem
    (T : NaryStageSystem sigma Gamma phi enum) (henum : Function.Surjective enum) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by
  let components : Fin (S.arity sigma) → CanonicalCarrier S := fun i =>
    ⟨NaryStageSystem.limit T i,
      ⟨NaryStageSystem.limit_isMCS T henum i, NaryStageSystem.limit_freshWitnessed T henum i⟩⟩
  refine ⟨components, ?_, ?_⟩
  · intro i
    exact NaryStageSystem.limit_contains_base T i
  · exact NaryStageSystem.root_mem_canonicalInterp T henum

end NaryStageSystem

/-- The arity-zero case of the canonical Existence Lemma.  It is stated
separately because the tuple of component worlds is genuinely empty, and the
universal clause in `canonicalInterp` reduces exactly to membership of the
constant application in the output MCS. -/
theorem canonicalExistence_zero
    {sigma : S.Sym} {Gamma : CanonicalCarrier S}
    {phi : Fin (S.arity sigma) → Pattern S Nat}
    (harity : S.arity sigma = 0)
    (happ : Pattern.app sigma phi ∈ Gamma.val) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by
  let components : Fin (S.arity sigma) → CanonicalCarrier S := fun i =>
    Fin.elim0 (by simpa [harity] using i)
  refine ⟨components, ?_, ?_⟩
  · intro i
    exact Fin.elim0 (by simpa [harity] using i)
  · intro args _
    have hargs : args = phi := by
      funext i
      exact Fin.elim0 (by simpa [harity] using i)
    simpa [hargs] using happ

end

end MatchingLogic
