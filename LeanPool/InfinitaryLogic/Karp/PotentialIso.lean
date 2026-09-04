/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.BackAndForth
import Mathlib.SetTheory.Ordinal.Family

/-!
# Potential Isomorphism

This file defines potential isomorphism between structures and connects it to
back-and-forth equivalence at all ordinal levels.

## Main Definitions

- `PotentialIso`: A potential isomorphism between structures M and N is a family of
  finite partial maps containing the empty map and closed under extension in both directions.

## Main Results

- `PotentialIso.countable_toEquiv`: Potentially isomorphic countable structures are isomorphic.
- `BFEquiv_all_implies_potentialIso`: Back-and-forth equivalence at every ordinal yields a
  potential isomorphism.

## References

- [KK04], Theorem 1.2.1
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

open FirstOrder Structure Fin Ordinal

/-- A potential isomorphism between structures M and N is a family of finite partial
maps (given as pairs of compatible tuples) that contains the empty map and is closed
under extension in both directions.

This is the model-theoretic notion corresponding to "back-and-forth system" or
"winning strategy in the infinite EF game." -/
structure PotentialIso (L : Language.{u, v}) [L.IsRelational]
    (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] where
  /-- The family of partial maps, represented as pairs of tuples of equal length. -/
  family : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N))
  /-- The family contains the empty map. -/
  empty_mem : ⟨0, Fin.elim0, Fin.elim0⟩ ∈ family
  /-- Each pair in the family preserves atomic type. -/
  compatible : ∀ p ∈ family, SameAtomicType (L := L) p.2.1 p.2.2
  /-- Forth: for any pair and any element of M, there's an extension in the family. -/
  forth : ∀ p ∈ family, ∀ m : M, ∃ n' : N,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family
  /-- Back: for any pair and any element of N, there's an extension in the family. -/
  back : ∀ p ∈ family, ∀ n' : N, ∃ m : M,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family

namespace PotentialIso

variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

/-- The trivial potential isomorphism from M to itself via the identity. -/
noncomputable def refl (M : Type w) [L.Structure M] : PotentialIso L M M where
  family := { p | SameAtomicType (L := L) p.2.1 p.2.2 ∧ p.2.1 = p.2.2 }
  empty_mem := by simp only [Set.mem_ofPred_eq]; exact ⟨SameAtomicType.refl _, trivial⟩
  compatible := fun p hp => hp.1
  forth := fun p hp m => by
    simp only [Set.mem_ofPred_eq] at hp ⊢
    use m
    constructor
    · simp only [hp.2]
      exact SameAtomicType.refl _
    · simp only [hp.2]
  back := fun p hp n' => by
    simp only [Set.mem_ofPred_eq] at hp ⊢
    use n'
    constructor
    · simp only [hp.2]
      exact SameAtomicType.refl _
    · simp only [hp.2]

/-- Potential isomorphism is symmetric. -/
noncomputable def symm (p : PotentialIso L M N) : PotentialIso L N M where
  family := { q | ⟨q.1, q.2.2, q.2.1⟩ ∈ p.family }
  empty_mem := by simpa [Set.mem_ofPred_eq] using p.empty_mem
  compatible := fun q hq => by
    simpa [Set.mem_ofPred_eq] using (p.compatible ⟨q.1, q.2.2, q.2.1⟩ hq).symm
  forth := fun ⟨n, b, a⟩ hq n' => by
    simpa [Set.mem_ofPred_eq] using p.back ⟨n, a, b⟩ (by simpa [Set.mem_ofPred_eq] using hq) n'
  back := fun ⟨n, b, a⟩ hq m => by
    simpa [Set.mem_ofPred_eq] using p.forth ⟨n, a, b⟩ (by simpa [Set.mem_ofPred_eq] using hq) m

end PotentialIso

/-! ### PotentialIso implies isomorphism for countable structures -/

/-- Build a chain of compatible matchings from a PotentialIso by alternating forth and back
steps using the enumerations of M and N. The chain at step i has size i and is in P.family. -/
private noncomputable def PotentialIso.buildChain
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) :
    (i : ℕ) → { p : (Fin i → M) × (Fin i → N) // ⟨i, p.1, p.2⟩ ∈ P.family }
  | 0 => ⟨(Fin.elim0, Fin.elim0), P.empty_mem⟩
  | i + 1 =>
    let ⟨(a, b), hmem⟩ := P.buildChain enumM enumN i
    if i % 2 = 0 then
      let m := enumM (i / 2)
      let h := P.forth ⟨i, a, b⟩ hmem m
      ⟨(Fin.snoc a m, Fin.snoc b (Classical.choose h)), Classical.choose_spec h⟩
    else
      let n := enumN (i / 2)
      let h := P.back ⟨i, a, b⟩ hmem n
      ⟨(Fin.snoc a (Classical.choose h), Fin.snoc b n), Classical.choose_spec h⟩

/-- The chain at step i+1 extends the chain at step i: the first i elements are preserved. -/
private theorem PotentialIso.buildChain_coherent_fst
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) (i : ℕ) (j : Fin i) :
    (P.buildChain enumM enumN (i + 1)).val.1 (Fin.castSucc j) =
    (P.buildChain enumM enumN i).val.1 j := by
  simp only [PotentialIso.buildChain]
  split <;> simp [Fin.snoc_castSucc]

/-- Same coherence for the N-side. -/
private theorem PotentialIso.buildChain_coherent_snd
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) (i : ℕ) (j : Fin i) :
    (P.buildChain enumM enumN (i + 1)).val.2 (Fin.castSucc j) =
    (P.buildChain enumM enumN i).val.2 j := by
  simp only [PotentialIso.buildChain]
  split <;> simp [Fin.snoc_castSucc]

/-- At a forth step (even i), the last M-element is enumM(i/2). -/
private theorem PotentialIso.buildChain_forth_last
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) (i : ℕ) (hi : i % 2 = 0) :
    (P.buildChain enumM enumN (i + 1)).val.1 (Fin.last i) = enumM (i / 2) := by
  simp only [PotentialIso.buildChain, hi, ↓reduceIte, Fin.snoc_last]

/-- At a back step (odd i), the last N-element is enumN(i/2). -/
private theorem PotentialIso.buildChain_back_last
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) (i : ℕ) (hi : ¬ i % 2 = 0) :
    (P.buildChain enumM enumN (i + 1)).val.2 (Fin.last i) = enumN (i / 2) := by
  simp only [PotentialIso.buildChain, hi, ↓reduceIte, Fin.snoc_last]

/-- SameAtomicType holds at every chain step. -/
private theorem PotentialIso.buildChain_sat
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N) (i : ℕ) :
    SameAtomicType (L := L) (P.buildChain enumM enumN i).val.1
                             (P.buildChain enumM enumN i).val.2 :=
  P.compatible _ (P.buildChain enumM enumN i).prop

/-- Extended coherence: the value at position j < k in the chain at step k
equals the value at position j in the chain at step j+1. -/
private theorem PotentialIso.buildChain_coherent_fst_general
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N)
    {k : ℕ} {j : ℕ} (hjk : j < k) :
    (P.buildChain enumM enumN k).val.1 ⟨j, hjk⟩ =
    (P.buildChain enumM enumN (j + 1)).val.1 (Fin.last j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hjk' : j < k
    · rw [show (⟨j, hjk⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hjk'⟩ from rfl]
      rw [P.buildChain_coherent_fst enumM enumN k ⟨j, hjk'⟩]
      exact ih hjk'
    · have hjeqk : j = k := by omega
      subst hjeqk
      rfl

/-- Extended coherence for the N-side. -/
private theorem PotentialIso.buildChain_coherent_snd_general
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (enumM : ℕ → M) (enumN : ℕ → N)
    {k : ℕ} {j : ℕ} (hjk : j < k) :
    (P.buildChain enumM enumN k).val.2 ⟨j, hjk⟩ =
    (P.buildChain enumM enumN (j + 1)).val.2 (Fin.last j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hjk' : j < k
    · rw [show (⟨j, hjk⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hjk'⟩ from rfl]
      rw [P.buildChain_coherent_snd enumM enumN k ⟨j, hjk'⟩]
      exact ih hjk'
    · have hjeqk : j = k := by omega
      subst hjeqk
      rfl

/-- For countable structures, a potential isomorphism implies actual isomorphism.

This is a direct back-and-forth construction that doesn't go through Scott sentences
or Karp's theorem, avoiding circular dependencies in the formalization. -/
theorem PotentialIso.countable_toEquiv
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (P : PotentialIso L M N) : Nonempty (M ≃[L] N) := by
  classical
  -- Handle empty M
  by_cases hM : IsEmpty M
  · have hN : IsEmpty N := by
      by_contra hN; rw [not_isEmpty_iff] at hN
      exact hM.elim (P.back _ P.empty_mem hN.some).choose
    have hSAT₀ := P.compatible _ P.empty_mem
    refine ⟨⟨Equiv.equivOfIsEmpty M N,
      fun f' _ => (IsEmpty.false f').elim,
      fun {k} r x => ?_⟩⟩
    -- x : Fin k → M with IsEmpty M forces k = 0
    have hk : k = 0 := by by_contra h; exact hM.elim (x ⟨0, Nat.pos_of_ne_zero h⟩)
    subst hk
    have hrel := hSAT₀ (AtomicIdx.rel r Fin.elim0)
    simp only [AtomicIdx.holds] at hrel
    constructor
    · intro h; convert hrel.symm.mp (by convert h)
    · intro h; convert hrel.symm.mpr (by convert h)
  rw [not_isEmpty_iff] at hM
  have : Nonempty M := hM
  have : Nonempty N := ⟨(P.forth _ P.empty_mem (Classical.arbitrary M)).choose⟩
  -- Get enumerations
  obtain ⟨enumM, hM_surj⟩ := exists_surjective_nat M
  obtain ⟨enumN, hN_surj⟩ := exists_surjective_nat N
  -- Build chain of compatible matchings
  let chain := P.buildChain enumM enumN
  let aSeq : ℕ → M := fun i => (chain (i + 1)).val.1 (Fin.last i)
  let bSeq : ℕ → N := fun i => (chain (i + 1)).val.2 (Fin.last i)
  -- aSeq(2k) = enumM(k) and bSeq(2k+1) = enumN(k)
  have haSeq : ∀ k, aSeq (2 * k) = enumM k := fun k => by
    change (chain (2 * k + 1)).val.1 (Fin.last (2 * k)) = enumM k
    have h := P.buildChain_forth_last enumM enumN (2 * k) (by omega)
    rwa [show 2 * k / 2 = k by omega] at h
  have hbSeq : ∀ k, bSeq (2 * k + 1) = enumN k := fun k => by
    change (chain (2 * k + 1 + 1)).val.2 (Fin.last (2 * k + 1)) = enumN k
    have h := P.buildChain_back_last enumM enumN (2 * k + 1) (by omega)
    rwa [show (2 * k + 1) / 2 = k by omega] at h
  have hSAT : ∀ s, SameAtomicType (L := L) (chain s).val.1 (chain s).val.2 :=
    P.buildChain_sat enumM enumN
  -- Equality preservation: aSeq(i) = aSeq(j) ↔ bSeq(i) = bSeq(j) for i,j < s
  have hEq : ∀ {i j s : ℕ} (_ : i < s) (_ : j < s),
      aSeq i = aSeq j ↔ bSeq i = bSeq j := by
    intro i j s hi hj
    have h := hSAT s (AtomicIdx.eq ⟨i, hi⟩ ⟨j, hj⟩)
    simp only [AtomicIdx.holds] at h
    rw [P.buildChain_coherent_fst_general enumM enumN hi,
        P.buildChain_coherent_fst_general enumM enumN hj,
        P.buildChain_coherent_snd_general enumM enumN hi,
        P.buildChain_coherent_snd_general enumM enumN hj] at h
    exact h
  -- Define f : M → N and g : N → M
  let idxM : M → ℕ := fun m => 2 * Nat.find (hM_surj m)
  have hidxM : ∀ m, aSeq (idxM m) = m := fun m => by
    simp only [idxM]; rw [haSeq]; exact Nat.find_spec (hM_surj m)
  let f : M → N := fun m => bSeq (idxM m)
  let idxN : N → ℕ := fun n => 2 * Nat.find (hN_surj n) + 1
  have hidxN : ∀ n, bSeq (idxN n) = n := fun n => by
    simp only [idxN]; rw [hbSeq]; exact Nat.find_spec (hN_surj n)
  let g : N → M := fun n => aSeq (idxN n)
  -- f and g are inverses
  have hgf : ∀ m, g (f m) = m := by
    intro m
    change aSeq (idxN (bSeq (idxM m))) = m
    conv_rhs => rw [← hidxM m]
    exact (hEq (by omega : idxN (bSeq (idxM m)) < idxN (bSeq (idxM m)) + idxM m + 2)
               (by omega : idxM m < idxN (bSeq (idxM m)) + idxM m + 2)).mpr
      (hidxN (bSeq (idxM m)))
  have hfg : ∀ n, f (g n) = n := by
    intro n
    change bSeq (idxM (aSeq (idxN n))) = n
    conv_rhs => rw [← hidxN n]
    exact (hEq (by omega : idxM (aSeq (idxN n)) < idxM (aSeq (idxN n)) + idxN n + 2)
               (by omega : idxN n < idxM (aSeq (idxN n)) + idxN n + 2)).mp
      (hidxM (aSeq (idxN n)))
  let e : M ≃ N := {
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
  }
  -- Relation preservation
  refine ⟨⟨e, fun f' _ => (IsEmpty.false f').elim, fun r x => ?_⟩⟩
  -- Choose s large enough to contain all idxM(x i) positions
  let s := (Finset.sup Finset.univ (fun i : Fin _ => idxM (x i))) + 1
  have hi_lt : ∀ i, idxM (x i) < s :=
    fun i => Nat.lt_add_one_iff.mpr (Finset.le_sup (f := fun j => idxM (x j)) (Finset.mem_univ i))
  have hRel := hSAT s (AtomicIdx.rel r (fun i => ⟨idxM (x i), hi_lt i⟩))
  simp only [AtomicIdx.holds] at hRel
  have hM_eq : ∀ i, (chain s).val.1 ⟨idxM (x i), hi_lt i⟩ = x i :=
    fun i => (P.buildChain_coherent_fst_general enumM enumN (hi_lt i)).trans (hidxM (x i))
  have hN_eq : ∀ i, (chain s).val.2 ⟨idxM (x i), hi_lt i⟩ = f (x i) :=
    fun i => P.buildChain_coherent_snd_general enumM enumN (hi_lt i)
  -- Goal: RelMap r (e ∘ x) ↔ RelMap r x
  constructor
  · intro hfx
    have h1 : RelMap r (fun i => (chain s).val.2 ⟨idxM (x i), hi_lt i⟩) := by
      convert hfx using 1; exact funext fun i => hN_eq i
    change RelMap r x
    convert hRel.mpr h1 using 1; exact (funext fun i => hM_eq i).symm
  · intro hx
    have h1 : RelMap r (fun i => (chain s).val.1 ⟨idxM (x i), hi_lt i⟩) := by
      convert hx using 1; exact funext fun i => hM_eq i
    change RelMap r (fun i => f (x i))
    convert hRel.mp h1 using 1; exact (funext fun i => hN_eq i).symm

/-- BF-equivalence at all ordinals implies potential isomorphism.

The proof constructs the family of tuples `(n, a, b)` such that `BFEquiv α n a b` holds
for every ordinal `α`, and verifies the forth and back properties by a supremum
contradiction argument.

**Universe constraint**: The proof requires the ordinal universe to match the type universe
`w` (via `Ordinal.bddAbove_of_small`). This is because the contradiction argument takes a
supremum of ordinals indexed by `N : Type w`, which requires `Ordinal.{w}`. -/
theorem BFEquiv_all_implies_potentialIso
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N]
    (hBF : ∀ α : Ordinal.{w}, BFEquiv (L := L) α 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (PotentialIso L M N) := by
  refine ⟨{
    family := { p | ∀ α : Ordinal.{w}, BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
    empty_mem := ?_
    compatible := ?_
    forth := ?_
    back := ?_
  }⟩
  · -- empty_mem: the hypothesis gives BFEquiv at all ordinals for the empty tuple
    exact hBF
  · -- compatible: BFEquiv at level 0 gives SameAtomicType
    intro p hp
    exact (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone le_rfl (hp 0))
  · -- forth: by sSup contradiction
    intro ⟨n, a, b⟩ hfamily m
    simp only [Set.mem_ofPred_eq] at hfamily ⊢
    by_contra h_no
    push Not at h_no
    -- For each n' : N, choose an ordinal where BFEquiv fails
    choose αbad hbad using h_no
    -- The supremum exists because N : Type w and ordinals are in Ordinal.{w}
    have hbdd : BddAbove (Set.range αbad) := Ordinal.bddAbove_of_small
    -- At Order.succ of the supremum, BFEquiv.forth gives a witness
    obtain ⟨n'₀, hn'₀⟩ := BFEquiv.forth (hfamily (Order.succ (⨆ n', αbad n'))) m
    -- But αbad n'₀ ≤ ⨆, so by monotonicity BFEquiv holds at αbad n'₀, contradiction
    exact hbad n'₀ (BFEquiv.monotone (le_ciSup hbdd n'₀) hn'₀)
  · -- back: symmetric argument
    intro ⟨n, a, b⟩ hfamily n'
    simp only [Set.mem_ofPred_eq] at hfamily ⊢
    by_contra h_no
    push Not at h_no
    choose αbad hbad using h_no
    have hbdd : BddAbove (Set.range αbad) := Ordinal.bddAbove_of_small
    obtain ⟨m₀, hm₀⟩ := BFEquiv.back (hfamily (Order.succ (⨆ m, αbad m))) n'
    exact hbad m₀ (BFEquiv.monotone (le_ciSup hbdd m₀) hm₀)

end Language

end FirstOrder
