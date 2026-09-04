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
- `PotentialIso.ofExtensionFamily`: builds one from a relation-form extension family. A
  producer-facing adapter, strictly below the BF-equivalence machinery.
- `ExtensionPresentation`: the proof-relevant variant, for callers holding *states* rather than
  a predicate.
- `ExtensionPresentation.toPotentialIso`: its induced potential isomorphism, via the existential
  image of the states and routed solely through `ofExtensionFamily`.

## Main Results

- `potentialIso_iff_BFEquiv_all`: Potential isomorphism is equivalent to BF-equivalence
  at all ordinal levels (for the empty tuple).

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

/-! ### Producer-facing adapters

Two thin constructors for callers who have a back-and-forth system in hand and want the standard
object.  Both build `family` directly and route through nothing else — no `BFEquiv`, no ordinal
induction, no Scott formulas, no infinitary formula agreement.  In particular they sit *below*
`implies_BFEquiv_all` in this file and below `Karp/CarrierTheorem.lean` in the import graph.

Contrast `bfEquiv_all_of_extensionFamily`, which serves the opposite purpose: it consumes an
extension family to produce formula-level agreement.  These produce the `PotentialIso` itself. -/

/-- **Build a potential isomorphism from a relation-form extension family.**

The family is literally `{p | R p.1 p.2.1 p.2.2}`.  Tuples are arbitrary functions `Fin n → M`, so
repeated coordinates are supported and no injectivity is assumed; atomic compatibility is exactly
`SameAtomicType`.  Carrier universes stay independent. -/
private def ofExtensionFamily
    (R : ∀ n : ℕ, (Fin n → M) → (Fin n → N) → Prop)
    (empty : R 0 Fin.elim0 Fin.elim0)
    (compatible : ∀ {n a b}, R n a b → SameAtomicType (L := L) a b)
    (forth : ∀ {n a b}, R n a b → ∀ m : M,
      ∃ n' : N, R (n + 1) (Fin.snoc a m) (Fin.snoc b n'))
    (back : ∀ {n a b}, R n a b → ∀ n' : N,
      ∃ m : M, R (n + 1) (Fin.snoc a m) (Fin.snoc b n')) :
    PotentialIso L M N where
  family := {p | R p.1 p.2.1 p.2.2}
  empty_mem := by simpa only [Set.mem_ofPred_eq] using empty
  compatible := fun _ hp => compatible (by simpa only [Set.mem_ofPred_eq] using hp)
  forth := fun _ hp m => by
    simpa only [Set.mem_ofPred_eq] using forth (by simpa only [Set.mem_ofPred_eq] using hp) m
  back := fun _ hp n' => by
    simpa only [Set.mem_ofPred_eq] using back (by simpa only [Set.mem_ofPred_eq] using hp) n'





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
    show (chain (2 * k + 1)).val.1 (Fin.last (2 * k)) = enumM k
    have h := P.buildChain_forth_last enumM enumN (2 * k) (by omega)
    rwa [show 2 * k / 2 = k by omega] at h
  have hbSeq : ∀ k, bSeq (2 * k + 1) = enumN k := fun k => by
    show (chain (2 * k + 1 + 1)).val.2 (Fin.last (2 * k + 1)) = enumN k
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
    show aSeq (idxN (bSeq (idxM m))) = m
    conv_rhs => rw [← hidxM m]
    exact (hEq (by omega : idxN (bSeq (idxM m)) < idxN (bSeq (idxM m)) + idxM m + 2)
               (by omega : idxM m < idxN (bSeq (idxM m)) + idxM m + 2)).mpr
      (hidxN (bSeq (idxM m)))
  have hfg : ∀ n, f (g n) = n := by
    intro n
    show bSeq (idxM (aSeq (idxN n))) = n
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
    show RelMap r x
    convert hRel.mpr h1 using 1; exact (funext fun i => hM_eq i).symm
  · intro hx
    have h1 : RelMap r (fun i => (chain s).val.1 ⟨idxM (x i), hi_lt i⟩) := by
      convert hx using 1; exact funext fun i => hM_eq i
    show RelMap r (fun i => f (x i))
    convert hRel.mp h1 using 1; exact (funext fun i => hN_eq i).symm

/-- Given a potential isomorphism, BFEquiv holds at every ordinal level for any pair
in the family. This is the key inductive step for the (→) direction of the
potential isomorphism characterization.

The proof proceeds by ordinal induction: the zero case uses atomic type preservation,
the successor case uses the forth/back extension properties, and the limit case
follows from the induction hypothesis.

The structures may live in different universes, and no countability of the language is
required: the induction consumes only the family's atomic-type compatibility and its two
extension properties. -/
private theorem PotentialIso.family_bfEquiv
    {M : Type w} [L.Structure M]
    {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (α : Ordinal)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : ⟨n, a, b⟩ ∈ P.family) : BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    exact (BFEquiv.zero a b).mpr (P.compatible _ hab)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih hab, ?_, ?_⟩
    · intro m
      obtain ⟨n', hn'⟩ := P.forth _ hab m
      exact ⟨n', ih hn'⟩
    · intro n'
      obtain ⟨m, hm⟩ := P.back _ hab n'
      exact ⟨m, ih hm⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ hab



/-- A potential isomorphism implies BF-equivalence at all ordinals for the empty tuple. -/
theorem PotentialIso.implies_BFEquiv_all
    {M : Type w} [L.Structure M]
    {N : Type w'} [L.Structure N]
    (P : PotentialIso L M N) (α : Ordinal) :
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  P.family_bfEquiv α P.empty_mem

/-- BF-equivalence at all ordinals implies potential isomorphism.

The proof constructs the family of tuples `(n, a, b)` such that `BFEquiv α n a b` holds
for every ordinal `α`, and verifies the forth and back properties by a supremum
contradiction argument.

**Universe constraint**: The proof requires the ordinal universe to match the type universe
`w` (via `Ordinal.bddAbove_of_small`). This is because the contradiction argument takes a
supremum of ordinals indexed by `N : Type w`, which requires `Ordinal.{w}`. The forward
direction (`PotentialIso.implies_BFEquiv_all`) is fully universe-polymorphic. -/
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

/-- A potential isomorphism exists if and only if BFEquiv holds at all ordinals
for the empty tuple. This is the main characterization theorem for potential isomorphism.

**Universe note**: The ordinal universe is constrained to match the type universe `w`
by `BFEquiv_all_implies_potentialIso` (which uses a supremum over `N : Type w`).
The forward direction is universe-polymorphic; the backward direction requires this match. -/
private theorem potentialIso_iff_BFEquiv_all
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] :
    Nonempty (PotentialIso L M N) ↔
    ∀ α : Ordinal.{w}, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  ⟨fun ⟨P⟩ α => P.implies_BFEquiv_all α, BFEquiv_all_implies_potentialIso⟩

/-! ## Proof-relevant presentations

A second producer-facing adapter, for callers who build *states* (partial maps, finite
approximations, game positions) rather than a predicate.  It exists so that certificates need not
be flattened into a global relation by hand.

`State` is proof-relevant on purpose: different certificates may present the same tuple pair, and
nothing here quotients or picks canonical representatives.  This introduces **no** competing
back-and-forth structure — its output is the existing `PotentialIso`, built through
`ofExtensionFamily`, and the eventual isomorphism still comes only from
`PotentialIso.countable_toEquiv`. -/

/-- A back-and-forth system presented by states rather than by a predicate. -/
structure ExtensionPresentation (L : Language.{u, v}) [L.IsRelational]
    (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] where
  /-- The states at each tuple length. -/
  State : ℕ → Type*
  /-- The `M`-tuple a state presents. -/
  left : ∀ {n}, State n → Fin n → M
  /-- The `N`-tuple a state presents. -/
  right : ∀ {n}, State n → Fin n → N
  /-- A state over the empty tuple. -/
  empty : State 0
  /-- Every state presents an atomic-type-preserving pair. -/
  compatible : ∀ {n} (s : State n), SameAtomicType (L := L) (left s) (right s)
  /-- Forth, witnessed by a successor state. -/
  forth : ∀ {n} (s : State n) (m : M), ∃ (n' : N) (s' : State (n + 1)),
    left s' = Fin.snoc (left s) m ∧ right s' = Fin.snoc (right s) n'
  /-- Back, witnessed by a successor state. -/
  back : ∀ {n} (s : State n) (n' : N), ∃ (m : M) (s' : State (n + 1)),
    left s' = Fin.snoc (left s) m ∧ right s' = Fin.snoc (right s) n'

namespace ExtensionPresentation

variable {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
variable (P : ExtensionPresentation L M N)

/-- The family a presentation induces: the **existential image** of its states.  Two distinct
states presenting the same pair collapse here and nowhere earlier. -/
private def Rel (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∃ s : P.State n, P.left s = a ∧ P.right s = b



/-- The standard object a presentation produces. -/
private def toPotentialIso : PotentialIso L M N :=
  PotentialIso.ofExtensionFamily P.Rel
    ⟨P.empty, funext fun i => i.elim0, funext fun i => i.elim0⟩
    (fun ⟨s, hl, hr⟩ => hl ▸ hr ▸ P.compatible s)
    (fun {_ _ _} h m => by
      obtain ⟨s, rfl, rfl⟩ := h
      obtain ⟨n', s', hl, hr⟩ := P.forth s m
      exact ⟨n', s', hl, hr⟩)
    (fun {_ _ _} h n' => by
      obtain ⟨s, rfl, rfl⟩ := h
      obtain ⟨m, s', hl, hr⟩ := P.back s n'
      exact ⟨m, s', hl, hr⟩)

end ExtensionPresentation

end Language

end FirstOrder
