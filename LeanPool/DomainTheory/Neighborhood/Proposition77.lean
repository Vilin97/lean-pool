/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example61
import LeanPool.DomainTheory.Neighborhood.Definition72

/-!
# Proposition 7.7 (Scott 1981, PRG-19, §7) — `D^§` is effectively given

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19,
Lecture VII.

> **Proposition 7.7.** For any effectively given domain `D`, the domain `D^§` is
also effectively
> given, and all the combinators of Example 6.1 prove to be computable.

Scott transposes everything back to `ℕ` and gives the enumeration of `D^§`
(Example 6.1's tree
algebra, `Example61.Dsharp`) by a course-of-values recursion. In our model `D^§`
lives over
`List Bool × α` (Example 6.1), so the enumeration is `V : ℕ → Set (List Bool ×
α)`:

* `V 0 = Γ`                  (the master neighbourhood of `D^§`);
* `V (2n+1) = 0·Xₙ`          (`embZero` of the `n`-th `D`-neighbourhood `Xₙ = P.X
n`);
* `V (2n+2) = 1·V_{p n} ∪ 2·V_{q n}` (`embPair` of two earlier neighbourhoods).

Here `p n = n.unpair.1` and `q n = n.unpair.2` are Scott's `p, q` (inverse
pairing): both are `≤ n`,
hence the subscripts `p n, q n` of `V_{2n+2}` are `< 2n+2`, so the recursion is
well-founded and
membership stays recursive — exactly Scott's observation.

This file builds the construction in milestones:

* **Foundational layer (this commit):** `Vsharp` and its core math — `mem_X` (each
`V k ∈ 𝒟^§`),
  `surj` (every `𝒟^§`-neighbourhood is some `V k`), nonemptiness. All choice-free.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-! ### A left bound for `Nat.unpair` (local, to keep `Recursive.lean`'s cache
warm). -/

/-- `a ≤ Nat.pair a b` (choice-free). -/
private theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair; split <;> omega

/-- `n.unpair.1 ≤ n` (choice-free); the decreasing measure for `Vsharp`'s left
child. -/
theorem unpair_fst_le (n : ℕ) : n.unpair.1 ≤ n := by
  have h := le_pair_left n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

/-- The three index shapes: `0` (master `Γ`), `2a+1` (leaf), `2a+2` (node).
Choice-free. -/
theorem nat_shape (n : ℕ) : n = 0 ∨ (∃ a, n = 2 * a + 1) ∨ (∃ a, n = 2 * a + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · rcases Nat.lt_or_ge (n % 2) 1 with h | h
    · exact Or.inr (Or.inr ⟨n / 2 - 1, by omega⟩)
    · exact Or.inr (Or.inl ⟨n / 2, by omega⟩)

/-! ### `Nat.pair` is strictly monotone on strict componentwise order.

Needed so the node∩node recursive child code `pair (a.1) (b.1)` is `< pair (2a+2)
(2b+2)`, hence
present in the memo table. Proof via `max² ≤ pair _ _ < (max+1)²`. -/

private theorem pair_lt_succ_sq (x y : ℕ) : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
  have hm : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  unfold Nat.pair
  rcases lt_or_ge x y with h | h
  · rw [if_pos h, show max x y = y by omega, hm]; omega
  · rw [if_neg (by omega), show max x y = x by omega, hm]; omega

private theorem max_sq_le_pair (i j : ℕ) : max i j * max i j ≤ Nat.pair i j := by
  unfold Nat.pair
  rcases lt_or_ge i j with h | h
  · rw [if_pos h, show max i j = j by omega]; omega
  · rw [if_neg (by omega), show max i j = i by omega]; omega

theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have h1 : Nat.pair x y < (max x y + 1) * (max x y + 1) := pair_lt_succ_sq x y
  have h2 : max i j * max i j ≤ Nat.pair i j := max_sq_le_pair i j
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

/-! ### The enumeration `V : ℕ → 𝒫(List Bool × α)`. -/

/-- **Proposition 7.7 (Scott 1981, PRG-19).** Scott's enumeration of `D^§`:
`V₀ = Γ`, `V_{2n+1} = 0·Xₙ`, `V_{2n+2} = 1·V_{p n} ∪ 2·V_{q n}` (`p = unpair.1`,
`q = unpair.2`). -/
def Vsharp (D : NeighborhoodSystem α) (P : ComputablePresentation D) :
    ℕ → Set (List Bool × α)
  | 0 => Gamma D
  | (k + 1) =>
      if (k + 1) % 2 = 1 then
        embZero (P.X (k / 2))
      else
        embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2)
  termination_by k => k
  decreasing_by
    · have := unpair_fst_le ((k - 1) / 2); omega
    · have := unpair_snd_le ((k - 1) / 2); omega

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_zero : Vsharp D P 0 = Gamma D := by rw [Vsharp]

/-- One-step unfolding of `Vsharp` at a successor index. -/
theorem Vsharp_succ (k : ℕ) :
    Vsharp D P (k + 1) =
      if (k + 1) % 2 = 1 then embZero (P.X (k / 2))
      else embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2) := by
  rw [Vsharp]

theorem Vsharp_odd (n : ℕ) : Vsharp D P (2 * n + 1) = embZero (P.X n) := by
  rw [Vsharp_succ, if_pos (by omega), show 2 * n / 2 = n from by omega]

theorem Vsharp_even (n : ℕ) :
    Vsharp D P (2 * n + 2) = embPair (Vsharp D P n.unpair.1) (Vsharp D P n.unpair.2) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Vsharp_succ, if_neg (by omega),
    show (2 * n + 1 - 1) / 2 = n from by omega]

/-! ### `mem_X`, `surj`, nonemptiness. -/

/-- Every `V k` is a neighbourhood of `D^§`. -/
theorem Vsharp_mem (k : ℕ) : MemS D (Vsharp D P k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Vsharp_zero]; exact MemS.gamma
    · -- `k ≥ 1` is odd `2n+1` or even `2n+2`, decided choice-free by `k % 2`.
      rcases (by
        rcases Nat.lt_or_ge (k % 2) 1 with h | h
        · exact Or.inr ⟨k / 2 - 1, by omega⟩
        · exact Or.inl ⟨k / 2, by omega⟩ :
          (∃ n, k = 2 * n + 1) ∨ (∃ n, k = 2 * n + 2)) with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · rw [Vsharp_odd]; exact MemS.zero (P.mem_X n)
      · rw [Vsharp_even]
        exact MemS.pair (ih _ (by have := unpair_fst_le n; omega))
          (ih _ (by have := unpair_snd_le n; omega))

/-- Every neighbourhood of `D^§` is enumerated as some `V k` (surjectivity of
`V`). -/
theorem Vsharp_surj {W : Set (List Bool × α)} (hW : MemS D W) : ∃ k, Vsharp D P k = W := by
  induction hW with
  | gamma => exact ⟨0, Vsharp_zero P⟩
  | @zero X hX => obtain ⟨n, hn⟩ := P.surj hX; exact ⟨2 * n + 1, by rw [Vsharp_odd, hn]⟩
  | @pair Pp Qq _ _ ihP ihQ =>
      obtain ⟨a, ha⟩ := ihP
      obtain ⟨b, hb⟩ := ihQ
      refine ⟨2 * Nat.pair a b + 2, ?_⟩
      have h1 : (Nat.pair a b).unpair.1 = a := by rw [unpair_pair]
      have h2 : (Nat.pair a b).unpair.2 = b := by rw [unpair_pair]
      rw [Vsharp_even, h1, h2, ha, hb]

/-- Under `∅ ∉ 𝒟`, no `V k` is empty. -/
theorem Vsharp_nonempty (hD : ∀ X, D.mem X → X.Nonempty) (k : ℕ) : (Vsharp D P k).Nonempty :=
  memS_nonempty hD (Vsharp_mem P k)

/-! ### Per-parity intersection identities.

These are the choice-free heart of Scott's "the reader has to check that
7.1(i)–(ii) hold for the
`Vₖ`. The idea is that any such check is either (1) trivial, or (2) something
already assumed about
`D` and the `Xₙ`, or (3) can be thrown back to some sets `Vₘ` with strictly
smaller subscripts."

* `V₀ = Γ` is the identity for `∩` (cases (1));
* odd ∩ odd reduces to `D`'s own intersection `Xₐ ∩ X_b` (case (2));
* odd ∩ even (and even ∩ odd) are `∅` — inconsistent (case (1), and `∅ ∉ 𝒟^§`);
* even ∩ even is `embPair` of the *component* intersections, whose subscripts
`unpair.1 / unpair.2`
  are strictly smaller (case (3)). -/

theorem Vsharp_zero_inter (m : ℕ) : Vsharp D P 0 ∩ Vsharp D P m = Vsharp D P m := by
  rw [Vsharp_zero, Set.inter_eq_right]; exact memS_subset_gamma (Vsharp_mem P m)

theorem Vsharp_inter_zero (n : ℕ) : Vsharp D P n ∩ Vsharp D P 0 = Vsharp D P n := by
  rw [Vsharp_zero, Set.inter_eq_left]; exact memS_subset_gamma (Vsharp_mem P n)

theorem Vsharp_odd_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 1) = embZero (P.X a ∩ P.X b) := by
  rw [Vsharp_odd, Vsharp_odd, embZero_inter]

theorem Vsharp_odd_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 2) = ∅ := by
  rw [Vsharp_odd, Vsharp_even, embZero_inter_embPair]

theorem Vsharp_even_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 1) = ∅ := by
  rw [Set.inter_comm]; exact Vsharp_odd_inter_even P b a

theorem Vsharp_even_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 2)
      = embPair (Vsharp D P a.unpair.1 ∩ Vsharp D P b.unpair.1)
                (Vsharp D P a.unpair.2 ∩ Vsharp D P b.unpair.2) := by
  rw [Vsharp_even, Vsharp_even, embPair_inter]

/-! ### `MemS`-subset inversions and the consistency-via-subset equivalences.

A nonempty `D^§`-neighbourhood contained in `embZero Y` must itself be an
`embZero` (its tokens have
empty `{1,2}`-path); contained in `embPair A B`, an `embPair`. These give the
bridge between Scott's
consistency relation on `D^§` (`∃ l, V_l ⊆ V_n ∩ V_m`) and the recursive
sub-checks: `embZero`
consistency reduces to `D`'s, and `embPair` consistency to the two components'. -/

theorem memS_sub_embZero (hD : ∀ X, D.mem X → X.Nonempty) {W : Set (List Bool × α)} {Y : Set α}
    (hW : MemS D W) (hsub : W ⊆ embZero Y) : ∃ Z, D.mem Z ∧ W = embZero Z := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)).1 (by simp)
  | @zero Z hZ => exact ⟨Z, hZ, rfl⟩
  | @pair Pp Qq hP hQ =>
      obtain ⟨⟨pth, a⟩, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Qq)
      have hmem := hsub ht
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · exact absurd (hp'.symm.trans hmem.1) (by simp)
      · exact absurd (hq'.symm.trans hmem.1) (by simp)

theorem memS_sub_embPair (hD : ∀ X, D.mem X → X.Nonempty)
    {W A B : Set (List Bool × α)} (hW : MemS D W) (hsub : W ⊆ embPair A B) :
    ∃ Pp Qq, MemS D Pp ∧ MemS D Qq ∧ W = embPair Pp Qq := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      rcases hsub (show (([], a) : List Bool × α) ∈ Gamma D from
        ha) with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @zero Z hZ =>
      obtain ⟨a, ha⟩ := hD Z hZ
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero Z from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @pair Pp Qq hP hQ => exact ⟨Pp, Qq, hP, hQ, rfl⟩

theorem exists_sub_embZero_iff (hD : ∀ X, D.mem X → X.Nonempty) (Y : Set α) :
    (∃ l, Vsharp D P l ⊆ embZero Y) ↔ ∃ k, P.X k ⊆ Y := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Z, hZ, hWZ⟩ := memS_sub_embZero hD (Vsharp_mem P l) hl
    rw [hWZ] at hl
    obtain ⟨k, hk⟩ := P.surj hZ
    exact ⟨k, hk ▸ embZero_subset.mp hl⟩
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by rw [Vsharp_odd]; exact embZero_subset.mpr hk⟩

theorem exists_sub_embPair_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (A B : Set (List Bool × α)) :
    (∃ l, Vsharp D P l ⊆ embPair A B) ↔
      (∃ l, Vsharp D P l ⊆ A) ∧ (∃ l, Vsharp D P l ⊆ B) := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Pp, Qq, hP, hQ, hWeq⟩ := memS_sub_embPair hD (Vsharp_mem P l) hl
    rw [hWeq] at hl
    obtain ⟨hPA, hQB⟩ := embPair_subset.mp hl
    obtain ⟨l1, h1⟩ := Vsharp_surj P hP
    obtain ⟨l2, h2⟩ := Vsharp_surj P hQ
    exact ⟨⟨l1, h1 ▸ hPA⟩, ⟨l2, h2 ▸ hQB⟩⟩
  · rintro ⟨⟨l1, h1⟩, ⟨l2, h2⟩⟩
    obtain ⟨l, hl⟩ := Vsharp_surj P (MemS.pair (Vsharp_mem P l1) (Vsharp_mem P l2))
    exact ⟨l, by rw [hl]; exact embPair_subset.mpr ⟨h1, h2⟩⟩

theorem Vsharp_eq_Gamma_iff (hD : ∀ X, D.mem X → X.Nonempty) (j : ℕ) :
    Vsharp D P j = Gamma D ↔ j = 0 := by
  constructor
  · intro h
    rcases nat_shape j with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rfl
    · rw [Vsharp_odd] at h; exact absurd h (embZero_ne_Gamma D hD (P.X a))
    · rw [Vsharp_even] at h; exact absurd h (embPair_ne_Gamma D hD _ _)
  · rintro rfl; exact Vsharp_zero P

/-! ### A primitive-recursive course-of-values memo evaluator.

The `D^§` deciders (`cons`, `inter`, equality) recurse on the index *trees*: e.g.
`inter(2a+2, 2b+2)` recurses on `inter(a.1, b.1)` and `inter(a.2, b.2)`. The
combined measure
`w = Nat.pair n m` strictly decreases on every recursive call, so each decider is
a **unary
course-of-values recursion** on `w`. We realise course-of-values by a
primitive-recursive *memo
table*: `rtbl step w` codes the reverse list `[g(w-1), …, g 0]` (`g v = step (pair
v (table for v))`),
built by a single `Nat.Primrec.prec` whose step is a cons. To read `g v` for `v <
w` inside `step`,
we look up position `w-1-v` of the reverse table via `listGet`. All choice-free. -/

/-- One step of the list-indexing fold: state `pair countdown value`; capture the
current element
when `countdown = 1`, else carry the value and decrement. -/
def listGetStp (t : ℕ) : ℕ :=
  Nat.pair (t.unpair.2.unpair.1.unpair.1 - 1)
    (selectFn (isOne t.unpair.2.unpair.1.unpair.1) t.unpair.1 t.unpair.2.unpair.1.unpair.2)

/-- `listGet c i = (decodeList c).getD i 0`: the `i`-th entry of the list coded by
`c`. -/
def listGet (c i : ℕ) : ℕ :=
  (foldCode listGetStp 0 (Nat.pair (i + 1) 0) c).unpair.2

/-- The fold step on an explicit accumulator `pair cd val`. -/
private theorem listGetStp_pair (cd val x : ℕ) :
    listGetStp (Nat.pair x (Nat.pair (Nat.pair cd val) 0))
      = Nat.pair (cd - 1) (selectFn (isOne cd) x val) := by
  unfold listGetStp
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- With `cd = 0` the fold is a fixed point on the value. -/
private theorem listGet_foldl_zero (l : List ℕ) (val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0))) (Nat.pair 0 val) l).unpair.2
      = val := by
  induction l generalizing val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.zero_sub,
        show isOne 0 = 0 from rfl, selectFn_zero, ih]

/-- The fold reads off the `cd-1`-th element (default `val`). -/
private theorem listGet_foldl (l : List ℕ) (c val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0)))
        (Nat.pair (c + 1) val) l).unpair.2 = l.getD c val := by
  induction l generalizing c val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · rw [show isOne (0 + 1) = 1 from rfl, selectFn_one, listGet_foldl_zero,
          List.getD_cons_zero]
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [show isOne (c' + 1 + 1) = 0 by unfold isOne; omega, selectFn_zero, ih,
          List.getD_cons_succ]

/-- **Correctness of `listGet`** on a coded list. -/
theorem listGet_encodeList (l : List ℕ) (i : ℕ) : listGet (encodeList l) i = l.getD i 0 := by
  unfold listGet
  rw [foldCode_eq]
  exact listGet_foldl l i 0

/-- `listGet` is primitive recursive (on the `Nat.pair` coding of `c, i`). -/
theorem primrec_listGet : Nat.Primrec (fun p => listGet p.unpair.1 p.unpair.2) := by
  have hstp : Nat.Primrec listGetStp := by
    unfold listGetStp
    have hcd : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.1) :=
      Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hval : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.2) :=
      Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hx : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
    exact (primrec_sub₂ hcd (Nat.Primrec.const 1)).pair
      (primrec_selectFn (primrec_isOne.comp hcd) hx hval)
  have hz : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.2 + 1) 0) :=
    (Nat.Primrec.succ.comp Nat.Primrec.right).pair (Nat.Primrec.const 0)
  exact (Nat.Primrec.right.comp
    (primrec_foldCode hstp (Nat.Primrec.const 0) hz Nat.Primrec.left)).of_eq fun p => rfl

/-- The reverse memo table: `rtbl step w` codes `[g(w-1), …, g 0]`. -/
def rtbl (step : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (w + 1) => Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1

/-- The course-of-values value at `w`: `g w = step (pair w (table of g below w))`. -/
def gOf (step : ℕ → ℕ) (w : ℕ) : ℕ := step (Nat.pair w (rtbl step w))

theorem gOf_def (step : ℕ → ℕ) (w : ℕ) : gOf step w = step (Nat.pair w (rtbl step w)) := rfl

/-- The reverse list of memo values `[g(w-1), …, g 0]`. -/
def gList (step : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | (w + 1) => gOf step w :: gList step w

theorem rtbl_eq_encode (step : ℕ → ℕ) (w : ℕ) : rtbl step w = encodeList (gList step w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
      change Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1
        = encodeList (gList step (w + 1))
      rw [gList, encodeList, gOf, ih]

theorem gList_length (step : ℕ → ℕ) (w : ℕ) : (gList step w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [gList, List.length_cons, ih]

theorem getD_gList (step : ℕ → ℕ) : ∀ (w p : ℕ), p < w →
    (gList step w).getD p 0 = gOf step (w - 1 - p) := by
  intro w
  induction w with
  | zero => intro p hp; omega
  | succ w ih =>
      intro p hp
      cases p with
      | zero =>
          rw [gList, List.getD_cons_zero]
          have : w + 1 - 1 - 0 = w := by omega
          rw [this]
      | succ p =>
          rw [gList, List.getD_cons_succ, ih p (by omega)]
          have : w + 1 - 1 - (p + 1) = w - 1 - p := by omega
          rw [this]

/-- **The course-of-values lookup.** Inside `step` at `w`, position `w-1-v` of the
reverse table is
exactly `g v`, for any earlier `v < w`. -/
theorem listGet_rtbl (step : ℕ → ℕ) {v w : ℕ} (hv : v < w) :
    listGet (rtbl step w) (w - 1 - v) = gOf step v := by
  rw [rtbl_eq_encode, listGet_encodeList, getD_gList step w (w - 1 - v) (by omega)]
  congr 1; omega

private theorem rtbl_eq_rec (step : ℕ → ℕ) (w : ℕ) :
    rtbl step w
      = Nat.rec (motive := fun _ => ℕ) 0
          (fun y IH => Nat.pair (step (Nat.pair y IH)) IH + 1) w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [rtbl, ih]

/-- `rtbl step` is primitive recursive when `step` is (a single `prec` whose step
is a cons). -/
theorem primrec_rtbl {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (rtbl step) := by
  have hg : Nat.Primrec (fun c => Nat.pair (step c.unpair.2) c.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hstep.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))
  refine ((Nat.Primrec.prec Nat.Primrec.zero hg).comp
    (Nat.Primrec.zero.pair primrec_id)).of_eq fun w => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rtbl_eq_rec]

/-- `gOf step` is primitive recursive when `step` is. -/
theorem primrec_gOf {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (gOf step) :=
  (hstep.comp (primrec_id.pair (primrec_rtbl hstep))).of_eq fun _ => rfl

/-- `listGet` as a binary primrec composite. -/
theorem primrec_listGet₂ {c i : ℕ → ℕ} (hc : Nat.Primrec c) (hi : Nat.Primrec i) :
    Nat.Primrec (fun p => listGet (c p) (i p)) :=
  (primrec_listGet.comp (hc.pair hi)).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd]

/-! ### The combined `D^§` decider step (`eq`/`cons`/`inter` triple).

All three `D^§` deciders recurse the same way on `(i, j)`, so we compute them
together as a packed
triple `packT eqBit consBit interIdx`. The step `dsharpStep fcons feq finter` is
fed Scott's three
`D`-level primitive-recursive functions: `fcons`/`feq` are the extracted `{0,1}`
characteristic
functions of `P.cons_computable`/`P.eq_computable`, and `finter` is `P.inter` (on
`Nat.pair` codes).
The combined index is `w = Nat.pair i j`; in the node∩node case the children's
results are read from
the memo table by `listGet`. -/

/-- Pack the triple `(eqBit, consBit, interIdx)` into one natural. -/
def packT (e c ii : ℕ) : ℕ := Nat.pair e (Nat.pair c ii)

/-- Equality bit of a packed triple. -/
def eqB (r : ℕ) : ℕ := r.unpair.1
/-- Consistency bit of a packed triple. -/
def consB (r : ℕ) : ℕ := r.unpair.2.unpair.1
/-- Intersection index of a packed triple. -/
def intI (r : ℕ) : ℕ := r.unpair.2.unpair.2

@[simp] theorem eqB_packT (e c ii : ℕ) : eqB (packT e c ii) = e := by
  simp only [eqB, packT, unpair_pair_fst]
@[simp] theorem consB_packT (e c ii : ℕ) : consB (packT e c ii) = c := by
  simp only [consB, packT, unpair_pair_fst, unpair_pair_snd]
@[simp] theorem intI_packT (e c ii : ℕ) : intI (packT e c ii) = ii := by
  simp only [intI, packT, unpair_pair_snd]

variable (fcons feq finter : ℕ → ℕ)

/-- **The `D^§` decider step.** `p = pair (pair i j) tbl`. Returns `packT eqBit
consBit interIdx`,
case-splitting on `i = 0` / `j = 0` (the `Γ` identity), then on parities (leaf
`2a+1` vs node
`2a+2`). Leaf∩leaf delegates to `D`'s deciders; node∩node ANDs/combines the two
children read from
the memo table `tbl`. -/
def dsharpStep (p : ℕ) : ℕ :=
  let i := p.unpair.1.unpair.1
  let j := p.unpair.1.unpair.2
  let tbl := p.unpair.2
  let w := p.unpair.1
  let na := i / 2 - 1
  let nb := j / 2 - 1
  let r1 := listGet tbl (w - 1 - Nat.pair na.unpair.1 nb.unpair.1)
  let r2 := listGet tbl (w - 1 - Nat.pair na.unpair.2 nb.unpair.2)
  selectFn (1 - i) (packT (1 - j) 1 j)
    (selectFn (1 - j) (packT (1 - i) 1 i)
      (selectFn (i % 2)
        (selectFn (j % 2)
          (packT (feq (Nat.pair (i / 2) (j / 2))) (fcons (Nat.pair (i / 2) (j / 2)))
            (2 * finter (Nat.pair (i / 2) (j / 2)) + 1))
          (packT 0 0 0))
        (selectFn (j % 2) (packT 0 0 0)
          (packT (eqB r1 * eqB r2) (consB r1 * consB r2)
            (2 * Nat.pair (intI r1) (intI r2) + 2)))))

theorem dsharpStep_i0 (j tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair 0 j) tbl) = packT (1 - j) 1 j := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

theorem dsharpStep_j0 {i : ℕ} (tbl : ℕ) (hi : i ≠ 0) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair i 0) tbl) = packT (1 - i) 1 i := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - i = 0 by omega, selectFn_zero, Nat.sub_zero, selectFn_one]

theorem dsharpStep_ll (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 1) (2 * b + 1)) tbl)
      = packT (feq (Nat.pair a b)) (fcons (Nat.pair a b)) (2 * finter (Nat.pair a b) + 1) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega]

theorem dsharpStep_ln (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 1) (2 * b +
      2)) tbl) = packT 0 0 0 := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * b + 2) % 2 = 0 by omega, selectFn_zero]

theorem dsharpStep_nl (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b +
      1)) tbl) = packT 0 0 0 := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one]

theorem dsharpStep_nn (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b + 2)) tbl)
      = packT
          (eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b +
              2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b +
            2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b +
              2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (2 * Nat.pair
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b +
              2) - 1 - Nat.pair a.unpair.1 b.unpair.1)))
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b +
              2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
            + 2) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * a + 2) / 2 - 1 = a by omega, show (2 * b + 2) / 2 - 1 = b by omega]

/-- The decider step is primitive recursive when the `D`-level functions are. -/
theorem primrec_dsharpStep (hfcons : Nat.Primrec fcons) (hfeq : Nat.Primrec feq)
    (hfinter : Nat.Primrec finter) : Nat.Primrec (dsharpStep fcons feq finter) := by
  have hi : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hj : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have htbl : Nat.Primrec (fun p : ℕ => p.unpair.2) := Nat.Primrec.right
  have hw : Nat.Primrec (fun p : ℕ => p.unpair.1) := Nat.Primrec.left
  have hidiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2) := primrec_div2.comp hi
  have hjdiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2) := primrec_div2.comp hj
  have hna : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2 - 1) :=
    primrec_sub₂ hidiv (Nat.Primrec.const 1)
  have hnb : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2 - 1) :=
    primrec_sub₂ hjdiv (Nat.Primrec.const 1)
  have hv1 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1 (p.unpair.1.unpair.2 / 2 - 1).unpair.1) :=
    (Nat.Primrec.left.comp hna).pair (Nat.Primrec.left.comp hnb)
  have hv2 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2 (p.unpair.1.unpair.2 / 2 - 1).unpair.2) :=
    (Nat.Primrec.right.comp hna).pair (Nat.Primrec.right.comp hnb)
  have hr1 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        (p.unpair.1.unpair.2 / 2 - 1).unpair.1)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv1)
  have hr2 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        (p.unpair.1.unpair.2 / 2 - 1).unpair.2)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv2)
  have hidiv2 : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.1.unpair.1 / 2) (
    p.unpair.1.unpair.2 / 2)) :=
    hidiv.pair hjdiv
  have hpackT : ∀ {e c ii : ℕ → ℕ}, Nat.Primrec e → Nat.Primrec c → Nat.Primrec ii →
      Nat.Primrec (fun p => packT (e p) (c p) (ii p)) := by
    intro e c ii he hc hii
    exact (he.pair (hc.pair hii)).of_eq fun p => rfl
  have hleaf : Nat.Primrec (fun p : ℕ =>
      packT (feq (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (fcons (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (2 * finter (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)) + 1)) :=
    hpackT (hfeq.comp hidiv2) (hfcons.comp hidiv2)
      (Nat.Primrec.succ.comp (primrec_mul₂ (Nat.Primrec.const 2) (hfinter.comp hidiv2)))
  have hzero : Nat.Primrec (fun _ : ℕ => packT 0 0 0) := Nat.Primrec.const _
  have heqB1 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr1
  have heqB2 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr2
  have hconsB1 : Nat.Primrec (fun p => consB _) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).comp hr1
  have hconsB2 : Nat.Primrec (fun p => consB _) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).comp hr2
  have hintI1 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr1
  have hintI2 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr2
  have hnode : Nat.Primrec (fun p : ℕ =>
      packT
        (eqB (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
          * eqB (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (consB (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
          * consB (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (2 * Nat.pair
          (intI (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1)))
          (intI (listGet p.unpair.2
            (p.unpair.1 - 1 -
              Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2))) + 2)) :=
    hpackT (primrec_mul₂ heqB1 heqB2) (primrec_mul₂ hconsB1 hconsB2)
      ((Nat.Primrec.succ.comp Nat.Primrec.succ).comp (primrec_mul₂ (Nat.Primrec.const 2)
        (hintI1.pair hintI2)))
  refine (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hi)
    (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hj) (Nat.Primrec.const 1) hj)
    (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hj)
      (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hi) (Nat.Primrec.const 1) hi)
      (primrec_selectFn (primrec_mod2.comp hi)
        (primrec_selectFn (primrec_mod2.comp hj) hleaf hzero)
        (primrec_selectFn (primrec_mod2.comp hj) hzero hnode)))).of_eq fun p => rfl

/-! ### Correctness of the decider step (strong induction on the combined code).

Given that `fcons`/`feq`/`finter` correctly decide `D`-consistency / `D`-equality
/ `D`-intersection,
the packed triple `gOf (dsharpStep …)` correctly decides `D^§`-consistency,
computes the
`D^§`-intersection index, and decides `D^§`-equality. Proved together by strong
induction on the
combined code `Nat.pair i j`; the node∩node case recurses to strictly smaller
codes (present in the
memo table by `pair_lt_pair_of_lt`). -/

theorem dsharp_decider_spec (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ,
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · -- i = 0 (Γ ∩ V_j = V_j)
        simp only [gOf_def]
        rw [dsharpStep_i0 fcons feq finter j]
        simp only [eqB_packT, consB_packT, intI_packT]
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨fun _ => ⟨j, (Vsharp_zero_inter P j).ge⟩, fun _ => trivial⟩
        · intro _; rw [Vsharp_zero_inter P]
        · constructor
          · intro h
            have hj : j = 0 := by omega
            rw [hj]
          · intro h
            have hj : j = 0 := (Vsharp_eq_Gamma_iff P hD j).mp (h.symm.trans (Vsharp_zero P))
            omega
      · -- i = 2a+1 (leaf)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 1, (Vsharp_inter_zero P (2 * a + 1)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 1)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (leaf ∩ leaf)
          simp only [gOf_def]
          rw [dsharpStep_ll fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_odd P, exists_sub_embZero_iff P hD]; exact hcons a b
          · intro hp
            rw [Vsharp_odd_inter_odd P] at hp ⊢
            rw [exists_sub_embZero_iff P hD] at hp
            rw [Vsharp_odd P, hinter a b hp]
          · rw [Vsharp_odd P, Vsharp_odd P, heq a b]
            exact ⟨fun h => by rw [h], fun h => embZero_injective h⟩
        · -- j = 2b+2 (leaf ∩ node : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_ln fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd_inter_even P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd P, Vsharp_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h (embZero_ne_embPair D hD (P.mem_X a) _ _)
      · -- i = 2a+2 (node)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 2, (Vsharp_inter_zero P (2 * a + 2)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 2)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (node ∩ leaf : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_nl fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_even_inter_odd P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_even P, Vsharp_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h.symm (embZero_ne_embPair D hD (P.mem_X b) _ _)
        · -- j = 2b+2 (node ∩ node : recurse)
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (
              by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (
              by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          obtain ⟨ihc1, ihi1, ihe1⟩ :=
            ih (Nat.pair a.unpair.1 b.unpair.1) (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl
          obtain ⟨ihc2, ihi2, ihe2⟩ :=
            ih (Nat.pair a.unpair.2 b.unpair.2) (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl
          simp only [gOf_def]
          rw [dsharpStep_nn fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          rw [hr1, hr2]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_even P, exists_sub_embPair_iff P hD, nat_mul_eq_one]
            exact and_congr ihc1 ihc2
          · intro hp
            rw [Vsharp_even_inter_even P] at hp ⊢
            rw [exists_sub_embPair_iff P hD] at hp
            obtain ⟨hp1, hp2⟩ := hp
            rw [Vsharp_even P]
            simp only [unpair_pair_fst, unpair_pair_snd]
            rw [ihi1 hp1, ihi2 hp2]
          · rw [Vsharp_even P, Vsharp_even P, nat_mul_eq_one, ihe1, ihe2]
            constructor
            · rintro ⟨h1, h2⟩; rw [h1, h2]
            · intro h; exact embPair_injective h
  intro i j
  exact key (Nat.pair i j) i j rfl

/-- **Intersection-index correctness in isolation.** The `intI` component of `gOf
(dsharpStep …)` is
independent of the `eq`/`cons` bits (`fcons`/`feq`), so it is correct assuming
only that `finter`
correctly intersects in `D`. This lets the `inter` *data* field be built with
dummy `fcons`/`feq`
while staying choice-free. -/
theorem dsharp_intI_correct (hD : ∀ X, D.mem X → X.Nonempty)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ, (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · intro _
        simp only [gOf_def]; rw [dsharpStep_i0 fcons feq finter j]
        simp only [intI_packT]; rw [Vsharp_zero_inter P]
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 1)).symm
        · intro hp
          simp only [gOf_def]; rw [dsharpStep_ll fcons feq finter a b]
          simp only [intI_packT]
          rw [Vsharp_odd_inter_odd P] at hp ⊢
          rw [exists_sub_embZero_iff P hD] at hp
          rw [Vsharp_odd P, hinter a b hp]
        · intro hp
          exfalso
          rw [Vsharp_odd_inter_even P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 2)).symm
        · intro hp
          exfalso
          rw [Vsharp_even_inter_odd P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
        · intro hp
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (
              by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (
              by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          rw [Vsharp_even_inter_even P] at hp ⊢
          rw [exists_sub_embPair_iff P hD] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [gOf_def]; rw [dsharpStep_nn fcons feq finter a b]
          simp only [intI_packT]; rw [hr1, hr2, Vsharp_even P]
          simp only [unpair_pair_fst, unpair_pair_snd]
          rw [ih _ (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl hp1,
              ih _ (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl hp2]
  intro i j; exact key (Nat.pair i j) i j rfl

/-- **Decidability of `7.1(i)` for `D^§`.** `Vₙ ∩ Vₘ = V_k` iff `(n,m)` is
consistent and the
computed intersection index agrees with `k` under `D^§`-equality. Inconsistency
forces the product
to `0` (and then `Vₙ ∩ Vₘ = ∅ ≠ V_k`, since `V_k` is nonempty), so the single
product decider is
correct on the nose. -/
theorem dsharp_interEq_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b)
    (n m k : ℕ) :
    (Vsharp D P n ∩ Vsharp D P m = Vsharp D P k) ↔
      consB (gOf (dsharpStep fcons feq finter) (Nat.pair n m))
        * eqB (gOf (dsharpStep fcons feq finter)
            (Nat.pair (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k)) = 1 := by
  obtain ⟨hc0, hi0, _⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter n m
  obtain ⟨_, _, he⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter
    (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k
  rw [nat_mul_eq_one]
  constructor
  · intro hEq
    have hch : ∃ l, Vsharp D P l ⊆ Vsharp D P n ∩ Vsharp D P m := ⟨k, hEq.ge⟩
    exact ⟨hc0.mpr hch, he.mpr ((hi0 hch).trans hEq)⟩
  · rintro ⟨hcb, heb⟩
    rw [← hi0 (hc0.mp hcb)]; exact he.mp heb

/-! ### Proposition 7.7: `D^§` is effectively given.

Assembling the pieces into a `ComputablePresentation (Dsharp D hD)`. The
enumeration is `Vsharp`;
relation 7.1(ii) (consistency) and 7.1(i) (intersection-equality) are decided by
the packed-triple
deciders; the primitive-recursive intersection function reads the `intI` component
(built with dummy
`eq`/`cons` bits, which it does not depend on). Choice-free: the `Prop` fields
obtain `D`'s
existential deciders, the data fields use only `P.inter` (data). -/

/-- **Proposition 7.7 (Scott 1981, PRG-19).** A computable presentation of `D^§`
from one of `D`. -/
def dsharpPresentation (hD : ∀ X, D.mem X → X.Nonempty) :
    ComputablePresentation (Dsharp D hD) where
  X := Vsharp D P
  mem_X := fun n => Vsharp_mem P n
  surj := fun hY => Vsharp_surj P hY
  interEq_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b)
      simp only [unpair_pair_fst, unpair_pair_snd] at this
      exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b)
      simp only [unpair_pair_fst, unpair_pair_snd] at this
      exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (
          Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2.unpair.1))
        * eqB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
            (Nat.pair (intI (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
              (Nat.pair t.unpair.1 t.unpair.2.unpair.1))) t.unpair.2.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      have hc0 := hg.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))
      exact primrec_mul₂ ((Nat.Primrec.left.comp Nat.Primrec.right).comp hc0)
        (Nat.Primrec.left.comp (hg.comp
          (((Nat.Primrec.right.comp Nat.Primrec.right).comp hc0).pair
            (Nat.Primrec.right.comp Nat.Primrec.right))))
    · exact dsharp_interEq_iff P fc fe (fun s => P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
  cons_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b)
      simp only [unpair_pair_fst, unpair_pair_snd] at this
      exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b)
      simp only [unpair_pair_fst, unpair_pair_snd] at this
      exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (
          Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      exact (Nat.Primrec.left.comp Nat.Primrec.right).comp
        (hg.comp (Nat.Primrec.left.pair Nat.Primrec.right))
    · exact (dsharp_decider_spec P fc fe (fun s =>
      P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2).1.symm
  inter := fun n m => intI (gOf (dsharpStep (fun _ => 0) (fun _ => 0)
    (fun s => P.inter s.unpair.1 s.unpair.2)) (Nat.pair n m))
  inter_primrec := by
    have hg := primrec_gOf (primrec_dsharpStep (fun _ => 0) (fun _ => 0)
      (fun s => P.inter s.unpair.1 s.unpair.2) (Nat.Primrec.const 0) (Nat.Primrec.const 0)
      P.inter_primrec)
    have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2) :=
      Nat.Primrec.left.pair Nat.Primrec.right
    exact (Nat.Primrec.right.comp Nat.Primrec.right).comp (hg.comp hpair)
  inter_spec := by
    intro n m h
    exact dsharp_intI_correct P (fun _ => 0) (fun _ => 0) (
      fun s => P.inter s.unpair.1 s.unpair.2) hD
      (fun a b hh => by simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec hh) n m h
  masterIdx := 0
  masterIdx_spec := Vsharp_zero P

/-- **Proposition 7.7 (Scott 1981, PRG-19).** If `D` is effectively given, so is
`D^§`. -/
theorem dsharp_isEffectivelyGiven (P : ComputablePresentation D)
    (hD : ∀ X, D.mem X → X.Nonempty) :
    (Dsharp D hD).IsEffectivelyGiven :=
  ⟨dsharpPresentation P hD⟩

end Proposition77

end Domain.Neighborhood
