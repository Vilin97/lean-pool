/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagSourceCancellation

/-!
# Step 1: recovering maximal-flag codes

This file implements the unconditional part of the maximal-flag encoding theorem.

The explicit map

```
MaximalFlagCode.toSimplex hp : Code p → Simplex p (p - 1)
```

is proved injective.  The proof recovers the bottom and top permutations from the endpoint
vertices and recovers the bar-removal permutation from the successive retained-bar sets.
Consequently `Code p` is equivalent to the subtype of maximal strict flags lying in the image of
the explicit stage construction.

The surjectivity statement is isolated as `EveryMaximalFlagEncoded hp`. From this classification
the file constructs `simplexToCode`, proves both inverse
identities, and packages the requested equivalence with all maximal strict flags.  No cycle,
coefficient, or cancellation statement is included in that classification hypothesis.
-/

namespace NRR

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace MaximalFlagCode

/-- The first (bottom) stage index, in `Fin p`. -/
def firstStage (hp : Nat.Prime p) : Fin p := ⟨0, hp.pos⟩

/-- The last (top) stage index, in `Fin p`. -/
def lastStage (hp : Nat.Prime p) : Fin p := ⟨p - 1, by have := hp.pos; omega⟩

/-- Cast a stage index back to the arithmetic index used by a maximal simplex. -/
def simplexIndex (hp : Nat.Prime p) (j : Fin p) : Fin (p - 1 + 1) :=
  Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm j

@[simp] theorem stageIndex_simplexIndex
    (hp : Nat.Prime p) (j : Fin p) :
    stageIndex hp (simplexIndex hp j) = j := by
  apply Fin.ext
  rfl

@[simp] theorem stageIndex_last
    (hp : Nat.Prime p) :
    stageIndex hp (Fin.last (p - 1)) = lastStage hp := by
  apply Fin.ext
  rfl

/-- At stage zero every original bar is retained. -/
theorem retainedBars_zero (hp : Nat.Prime p) (z : Code p) :
    retainedBars z (firstStage hp) = Finset.univ := by
  ext r
  simp [retainedBars, removedBefore, firstStage]

/-- At the final stage every bar has been removed. -/
theorem retainedBars_last (hp : Nat.Prime p) (z : Code p) :
    retainedBars z (lastStage hp) = ∅ := by
  ext r
  rw [mem_retainedBars_iff]
  constructor
  · intro h
    exfalso
    have hr := (z.removal.symm r).2
    have hl : (lastStage hp).1 = p - 1 := rfl
    omega
  · intro h
    exact absurd h (Finset.notMem_empty r)

/-- At stage zero the block number is the bottom-permutation rank. -/
theorem stageBlock_zero
    (hp : Nat.Prime p) (z : Code p) (x : Fin p) :
    stageBlock z (firstStage hp) x = (z.bottom x).1 := by
  classical
  unfold stageBlock
  rw [retainedBars_zero hp z]
  let q := z.bottom x
  have hqle : q.1 ≤ p - 1 := by have := q.2; omega
  have hcard :
      ((Finset.univ : Finset (Fin (p - 1))).filter
        (fun r => r.1 < q.1)).card = q.1 := by
    let e : Fin q.1 ≃ {r : Fin (p - 1) // r.1 < q.1} :=
      { toFun := fun i => ⟨⟨i.1, lt_of_lt_of_le i.2 hqle⟩, i.2⟩
        invFun := fun r => ⟨r.1.1, r.2⟩
        left_inv := fun i => by apply Fin.ext; rfl
        right_inv := fun r => by apply Subtype.ext; apply Fin.ext; rfl }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  simpa [q] using hcard

/-- At the final stage every label has block number zero. -/
theorem stageBlock_last
    (hp : Nat.Prime p) (z : Code p) (x : Fin p) :
    stageBlock z (lastStage hp) x = 0 := by
  simp [stageBlock, retainedBars_last hp z]

/-- A finite permutation is determined by the strict order it induces. -/
theorem perm_eq_of_lt_iff
    {n : Nat} (sigma tau : Equiv.Perm (Fin n))
    (horder : ∀ x y, sigma x < sigma y ↔ tau x < tau y) :
    sigma = tau := by
  apply Equiv.Perm.ext
  intro i
  have h_card_sigma : Fintype.card {j : Fin n | sigma j < sigma i} = sigma i := by
    have heq : {j : Fin n | sigma j < sigma i} = sigma.symm '' {x : Fin n | x < sigma i} := by
      ext j
      simp
    simp_rw [heq]
    rw [Set.card_image_of_injective _ sigma.symm.injective]
    rw [Fintype.card_of_subtype (s := Finset.Iio (sigma i))]
    · simp
    · intro x; simp
  have h_card_tau : Fintype.card {j : Fin n | tau j < tau i} = tau i := by
    have heq : {j : Fin n | tau j < tau i} = tau.symm '' {x : Fin n | x < tau i} := by
      ext j
      simp
    simp_rw [heq]
    rw [Set.card_image_of_injective _ tau.symm.injective]
    rw [Fintype.card_of_subtype (s := Finset.Iio (tau i))]
    · simp
    · intro x; simp
  have hset_eq : {j : Fin n | sigma j < sigma i} = {j : Fin n | tau j < tau i} := by
    ext j
    exact horder j i
  have heq_card : Fintype.card {j : Fin n | sigma j < sigma i} = Fintype.card {j : Fin n | tau j < tau i} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquivRight ?_ |>.symm
    simp only [Set.mem_ofPred_eq]
    intro x
    exact ⟨fun h => (horder x i).mpr h, fun h => (horder x i).mp h⟩
  omega

/-- The first stage rank is exactly the coded bottom permutation. -/
theorem stageRank_zero
    (hp : Nat.Prime p) (z : Code p) :
    stageRank z (firstStage hp) = z.bottom := by
  apply perm_eq_of_lt_iff
  intro x y
  rw [Fin.lt_def, Fin.lt_def, stageRank_lt_iff]
  simp only [stageKey, stageBlock_zero hp z]
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (h | ⟨hb, ht⟩)
    · exact h
    · have hxy : x = y := z.bottom.injective (Fin.ext hb)
      subst hxy
      exact absurd ht (lt_irrefl _)
  · intro h
    exact Or.inl h

/-- The final stage rank is exactly the coded top permutation. -/
theorem stageRank_last
    (hp : Nat.Prime p) (z : Code p) :
    stageRank z (lastStage hp) = z.top := by
  apply perm_eq_of_lt_iff
  intro x y
  rw [Fin.lt_def, Fin.lt_def, stageRank_lt_iff]
  simp only [stageKey, stageBlock_last hp z]
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (h | ⟨_, ht⟩)
    · exact absurd h (lt_irrefl _)
    · exact ht
  · intro h
    exact Or.inr ⟨rfl, h⟩

/-- The first stage cell is the all-singleton cell determined by `bottom`. -/
theorem stageCell_zero
    (hp : Nat.Prime p) (z : Code p) :
    stageCell z (firstStage hp) =
      { rank := z.bottom, bars := Finset.univ } := by
  apply BarredPermutation.ext
  · exact stageRank_zero hp z
  · exact retainedBars_zero hp z

/-- The final stage cell is the top cell determined by `top`. -/
theorem stageCell_last
    (hp : Nat.Prime p) (z : Code p) :
    stageCell z (lastStage hp) =
      { rank := z.top, bars := ∅ } := by
  apply BarredPermutation.ext
  · exact stageRank_last hp z
  · exact retainedBars_last hp z

/-- A bar removed at step `q` is present immediately before that step. -/
theorem removal_mem_retained_castSucc
    (hp : Nat.Prime p) (z : Code p) (q : Fin (p - 1)) :
    z.removal q ∈ retainedBars z (stageIndex hp q.castSucc) := by
  rw [mem_retainedBars_iff, Equiv.symm_apply_apply]
  have : (stageIndex hp q.castSucc).1 = q.1 := rfl
  omega

/-- A bar removed at step `q` is absent immediately after that step. -/
theorem removal_not_mem_retained_succ
    (hp : Nat.Prime p) (z : Code p) (q : Fin (p - 1)) :
    z.removal q ∉ retainedBars z (stageIndex hp q.succ) := by
  rw [mem_retainedBars_iff, Equiv.symm_apply_apply]
  have : (stageIndex hp q.succ).1 = q.1 + 1 := rfl
  omega

/-- Equality of every retained-bar stage determines the removal permutation. -/
theorem removal_eq_of_retainedBars_eq
    (hp : Nat.Prime p) {z w : Code p}
    (hbars : ∀ j : Fin p, retainedBars z j = retainedBars w j) :
    z.removal = w.removal := by
  apply Equiv.ext
  intro q
  let r : Fin (p - 1) := z.removal q
  have hr0 : r ∈ retainedBars w (stageIndex hp q.castSucc) := by
    rw [← hbars (stageIndex hp q.castSucc)]
    exact removal_mem_retained_castSucc hp z q
  have hr1 : r ∉ retainedBars w (stageIndex hp q.succ) := by
    rw [← hbars (stageIndex hp q.succ)]
    exact removal_not_mem_retained_succ hp z q
  rw [mem_retainedBars_iff] at hr0
  rw [mem_retainedBars_iff] at hr1
  have hc0 : (stageIndex hp q.castSucc).1 = q.1 := rfl
  have hc1 : (stageIndex hp q.succ).1 = q.1 + 1 := rfl
  have htime : w.removal.symm r = q := by
    apply Fin.ext
    have hq := (w.removal.symm r).2
    rw [hc0] at hr0
    rw [hc1] at hr1
    omega
  calc
    z.removal q = r := rfl
    _ = w.removal (w.removal.symm r) := by simp
    _ = w.removal q := by rw [htime]

/-- The explicit maximal-flag code map is injective. -/
theorem toSimplex_injective (hp : Nat.Prime p) :
    Function.Injective (toSimplex hp : Code p → Simplex p (p - 1)) := by
  intro z w hzw
  apply Code.ext
  · have h0 := congrArg
      (fun s : Simplex p (p - 1) => (s (simplexIndex hp (firstStage hp))).rank) hzw
    simpa [toSimplex_apply, stageCell_zero hp] using h0
  · apply removal_eq_of_retainedBars_eq hp
    intro j
    have hj := congrArg
      (fun s : Simplex p (p - 1) => (s (simplexIndex hp j)).bars) hzw
    change (stageCell z j).bars = (stageCell w j).bars at hj
    change retainedBars z j = retainedBars w j at hj
    exact hj
  · have hlast := congrArg
      (fun s : Simplex p (p - 1) =>
        (s (Fin.last (p - 1))).rank) hzw
    simpa [toSimplex_apply, stageCell_last hp] using hlast

/-- Maximal strict flags produced by the explicit stage construction. -/
def EncodedSimplex (hp : Nat.Prime p) :=
  {s : Simplex p (p - 1) // s ∈ Set.range (toSimplex hp)}

instance (hp : Nat.Prime p) : Finite (EncodedSimplex hp) := by
  unfold EncodedSimplex
  infer_instance

noncomputable instance (hp : Nat.Prime p) : Fintype (EncodedSimplex hp) :=
  Fintype.ofFinite _

noncomputable instance (hp : Nat.Prime p) : DecidableEq (EncodedSimplex hp) :=
  Classical.decEq _

/-- Recover the unique code of an encoded maximal flag. -/
noncomputable def encodedSimplexToCode
    (hp : Nat.Prime p) (s : EncodedSimplex hp) : Code p :=
  Classical.choose s.2

@[simp] theorem toSimplex_encodedSimplexToCode
    (hp : Nat.Prime p) (s : EncodedSimplex hp) :
    toSimplex hp (encodedSimplexToCode hp s) = s.1 :=
  Classical.choose_spec s.2

@[simp] theorem encodedSimplexToCode_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    encodedSimplexToCode hp ⟨toSimplex hp z, ⟨z, rfl⟩⟩ = z := by
  apply toSimplex_injective hp
  exact toSimplex_encodedSimplexToCode hp _

/-- Unconditional equivalence between codes and the image of the explicit stage construction. -/
noncomputable def codeEquivEncodedSimplex
    (hp : Nat.Prime p) : Code p ≃ EncodedSimplex hp where
  toFun z := ⟨toSimplex hp z, ⟨z, rfl⟩⟩
  invFun := encodedSimplexToCode hp
  left_inv := encodedSimplexToCode_toSimplex hp
  right_inv s := by
    apply Subtype.ext
    exact toSimplex_encodedSimplexToCode hp s

/-- The classification statement for Step 1: every maximal strict flag is encoded. -/
def EveryMaximalFlagEncoded (hp : Nat.Prime p) : Prop :=
  Function.Surjective (toSimplex hp : Code p → Simplex p (p - 1))

/-- Recover a code from an arbitrary maximal flag once the classification theorem is available. -/
noncomputable def simplexToCodeOfSurjective
    (hp : Nat.Prime p) (hall : EveryMaximalFlagEncoded hp)
    (s : Simplex p (p - 1)) : Code p :=
  Classical.choose (hall s)

@[simp] theorem toSimplex_simplexToCodeOfSurjective
    (hp : Nat.Prime p) (hall : EveryMaximalFlagEncoded hp)
    (s : Simplex p (p - 1)) :
    toSimplex hp (simplexToCodeOfSurjective hp hall s) = s :=
  Classical.choose_spec (hall s)

@[simp] theorem simplexToCodeOfSurjective_toSimplex
    (hp : Nat.Prime p) (hall : EveryMaximalFlagEncoded hp)
    (z : Code p) :
    simplexToCodeOfSurjective hp hall (toSimplex hp z) = z := by
  apply toSimplex_injective hp
  exact toSimplex_simplexToCodeOfSurjective hp hall _

/-- Equivalence with all maximal strict flags, conditional on the surjectivity/classification theorem. -/
noncomputable def maximalFlagEquivOfSurjective
    (hp : Nat.Prime p) (hall : EveryMaximalFlagEncoded hp) :
    Code p ≃ Simplex p (p - 1) where
  toFun := toSimplex hp
  invFun := simplexToCodeOfSurjective hp hall
  left_inv := simplexToCodeOfSurjective_toSimplex hp hall
  right_inv := toSimplex_simplexToCodeOfSurjective hp hall

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step 1 is unconditional on the image of the explicit maximal-flag construction. -/
theorem simplestRoute_maximalFlagEncoding_injective :
    ∀ {p : Nat} (hp : Nat.Prime p),
      Function.Injective
        (FoxNeuwirthOrderComplex.MaximalFlagCode.toSimplex hp) :=
  fun hp => FoxNeuwirthOrderComplex.MaximalFlagCode.toSimplex_injective hp

end AAK

end NRR
