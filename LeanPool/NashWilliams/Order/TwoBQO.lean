/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import LeanPool.NashWilliams.Combinatorics.Ramsey.Infinite
import LeanPool.NashWilliams.Order.WellQuasiOrder.Regular

/-!
# 2-better-quasi-orders (2-BQO)

A formalization of 2-better-quasi-orders, following Pequignot, *Towards better: A motivated
introduction to better-quasi-orders*, EMS Surveys 2017. A 2-BQO is a strengthening of
well-quasi-order (WQO) phrased via *pair-sequences* `f : ∀ m n, m < n → α` instead of plain
sequences: `r` is 2-BQO if every pair-sequence has a *good triple* `m < n < l` with
`r (f m n) (f n l)`.

2-BQO implies WQO (`TwoBQO.wellQuasiOrdered`), and unlike WQO it is closed under several
constructions that WQO alone is not known to be closed under, most importantly forming an
infinite sum indexed by a 2-BQO (`TwoBQO.lexSigmaQO`) and passing to sequences under a suitable
embedding relation (`TwoBQO.embedForAll_wqo`).

## Main definitions

* `PairSeq α`: a pair-sequence, assigning a value to every pair `m < n` of naturals.
* `TwoBQO r`: `r` is 2-BQO if every pair-sequence has a good triple.
* `DomOrder r X Y`: `X` dominates into `Y`, i.e. every element of `X` is `r`-below some element
  of `Y`.
* `EmbedForAll r`: the pointwise-embedding preorder on sequences `ℕ → α` induced by `r`.
* `TwoBQO.LexSumRelQO r s t`: the lexicographic sum of quasi-orders `t i` on `s i`, ordered along
  `r` on the index type.

## Main results

* `TwoBQO.wellQuasiOrdered`: 2-BQO implies WQO.
* `TwoBQO.of_finite_coloring`: a preorder with a finite partial order quotient is 2-BQO.
* `TwoBQO.of_wellFoundedLT`: well-founded linear orders are 2-BQO.
* `Ordinal.isTwoBQO`: ordinals are 2-BQO.
* `TwoBQO.comap`, `TwoBQO.mono`: 2-BQO is closed under monotone preimage and relation weakening.
* `TwoBQO.union`: closure under covering by two 2-BQO parts.
* `TwoBQO.prod`, `TwoBQO.pi`: closure under finite products.
* `TwoBQO.lexSigmaQO`: closure under lexicographic sum along a 2-BQO index.
* `TwoBQO.dom_twoBQO`: the domination order on subsets of a 2-BQO is WQO.
* `TwoBQO.embedForAll_wqo`: `EmbedForAll r` is WQO on `ℕ → Q` whenever `r` is 2-BQO on `Q`.
-/

open Set Preorder

noncomputable section

/-!
## Bad pair-sequences and 2-BQO
-/

/-- A **pair-sequence** in `α` assigns a value to every pair `(m, n)` with `m < n`. -/
abbrev PairSeq (α : Type*) := ∀ m n : ℕ, m < n → α

namespace PairSeq

/-- Restrict a pair-sequence along a strictly monotone reindexing. -/
def restrict {α : Type*} (f : PairSeq α) (e : ℕ → ℕ) (he_mono : StrictMono e) : PairSeq α :=
  fun m n hmn => f (e m) (e n) (he_mono hmn)

/-- A pair-sequence `f` is **bad** for `r` if `f (m, n)` and `f (n, l)` are never `r`-related. -/
def IsBad {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ m n l : ℕ, ∀ (hmn : m < n) (hnl : n < l), ¬ r (f m n hmn) (f n l hnl)

/-- A pair-sequence `f` is **perfect** for `r` if `f (m, n)` and `f (n, l)` are always
`r`-related. -/
def IsPerfect {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ m n l : ℕ, ∀ (hmn : m < n) (hnl : n < l), r (f m n hmn) (f n l hnl)

/-- Every pair-sequence has a restriction that is perfect or bad for `r`: colour each triple
`h < i < j` by whether `r (f h i) (f i j)` holds and apply `infinite_ramsey_triples`. -/
theorem perfect_or_bad {α : Type*} (r : α → α → Prop) (f : PairSeq α) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      IsPerfect r (restrict f e he_mono) ∨ IsBad r (restrict f e he_mono) := by
  classical
  obtain ⟨e, he_mono, k, hk⟩ := @infinite_ramsey_triples Bool inferInstance
    fun h i j (hs : h < i ∧ i < j) => decide (r (f h i hs.1) (f i j hs.2))
  refine ⟨e, he_mono, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hk_false | hk_true
  · left
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_false] at h_color
    simpa [restrict, decide_eq_false_iff_not] using h_color
  · right
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_true] at h_color
    simpa [restrict, decide_eq_true_eq] using h_color

end PairSeq

/-- `r` is **2-BQO** if there is no bad pair-sequence for `r`. -/
private def TwoBQO_n {α : Type*} (r : α → α → Prop) : Prop :=
  ¬ ∃ f : PairSeq α, PairSeq.IsBad r f

/-- `r` is **2-BQO** if every pair-sequence has a good triple `m < n < l`, i.e.
`r (f m n) (f n l)`. -/
def TwoBQO {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ f : PairSeq α, ∃ m n l : ℕ, ∃ (hmn : m < n) (hnl : n < l), r (f m n hmn) (f n l hnl)

theorem TwoBQO.iff_noBad {α : Type*} (r : α → α → Prop) : TwoBQO r ↔ TwoBQO_n r := by
  simp only [TwoBQO_n, PairSeq.IsBad, not_exists, not_forall, not_not]
  exact Iff.symm (Eq.to_iff rfl)

/-!
## 2-BQO implies WQO
-/

/-- **2-BQO implies WQO.** Given a sequence `g : ℕ → α`, apply 2-BQO to the pair-sequence
`(m, n, _) ↦ g m`. A good triple `m < n < l` yields `r (g m) (g n)`. -/
theorem TwoBQO.wellQuasiOrdered {α : Type*} {r : α → α → Prop} (h : TwoBQO r) :
    WellQuasiOrdered r := fun g =>
  let ⟨m, n, _, hmn, _, hrel⟩ := h fun m _ _ => g m
  ⟨m, n, hmn, hrel⟩

/-!
## Finite preorders are TwoBQO
-/

/-- **A preorder with a finite partial order quotient is 2-BQO.** If `c : α → κ` with `κ`
finite and *same colour ⟹ `r`-related*, then `r` is 2-BQO: colour pairs by `c (f m n)`,
Ramsey-for-pairs (`infinite_ramsey_pairs`) makes the restriction monochromatic, so any triple is
good. In particular, if `r` is a preorder whose induced partial order on `r`-equivalence classes
has finitely many classes, taking `c` to be the quotient map gives `TwoBQO r`. -/
theorem TwoBQO.of_finite_coloring {α κ : Type*} [Finite κ] (r : α → α → Prop) (c : α → κ)
    (hc : ∀ a b, c a = c b → r a b) : TwoBQO r := by
  intro f
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_pairs fun m n h => c (f m n h)
  exact ⟨e 0, e 1, e 2, he (by norm_num), he (by norm_num),
    hc _ _ ((hk 0 1 (by norm_num)).trans (hk 1 2 (by norm_num)).symm)⟩

/-!
## Well-orders are 2-BQO
-/

/-- **Well-orders are 2-BQO.** If `f` is bad for a well-order `<`, the sequence `n ↦ f (n, n+1)`
is strictly decreasing, contradicting well-foundedness. -/
theorem TwoBQO.of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    TwoBQO (α := α) (· ≤ ·) := by
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  have hstrict : ∀ n, f (n + 1) (n + 2) (Nat.lt_succ_self _) < f n (n + 1) (Nat.lt_succ_self _) :=
    fun n => not_le.mp (hbad n (n + 1) (n + 2) (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1)))
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    fun n => f n (n + 1) (Nat.lt_succ_self n)
  exact hn (hstrict n)

/-- **Ordinals are 2-BQO** with respect to `≤`. -/
theorem Ordinal.isTwoBQO : TwoBQO (α := Ordinal) (· ≤ ·) :=
  TwoBQO.of_wellFoundedLT

/-!
## Closure properties

### Monotone preimage (downward closure)
-/

/-- 2-BQO is closed under monotone preimage: if `φ : β → α` is monotone and `r` on `α` is
2-BQO, then the pullback of `r` along `φ` is 2-BQO. -/
theorem TwoBQO.comap {α β : Type*} {r : α → α → Prop} (h : TwoBQO r) (φ : β → α) :
    TwoBQO fun a b => r (φ a) (φ b) := by
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨fun m n hmn => φ (f m n hmn), fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel⟩

/-- **Subtype closure.** -/
theorem TwoBQO.subtype {α : Type*} {r : α → α → Prop} (h : TwoBQO r) (p : α → Prop) :
    TwoBQO fun a b : Subtype p => r a.val b.val :=
  h.comap Subtype.val

theorem TwoBQO.mono {α : Type*} {r s : α → α → Prop} (h : TwoBQO r)
    (hincl : ∀ a b, r a b → s a b) : TwoBQO s := by
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨f, fun m n l hmn hnl hrel => hbad m n l hmn hnl (hincl _ _ hrel)⟩

/-!
### Union of two parts

Rests on Ramsey for pairs (`infinite_ramsey_pairs`): a 2-colouring of pairs by which *part* the
single value `f m n` lands in has an infinite homogeneous restriction, on which the relevant
2-BQO gives a good triple.
-/

/-- **Union of two 2-BQO parts is 2-BQO.** If `p, q` cover `α` and `r` is 2-BQO on each
sub-part `{x // p x}` and `{x // q x}`, then `r` is 2-BQO on `α`.

2-colour each pair `(m,n)` by whether `p (f m n)` holds; Ramsey-for-pairs gives an infinite
restriction landing wholly in one part, where the corresponding 2-BQO supplies a good triple. -/
theorem TwoBQO.union {α : Type*} (r : α → α → Prop) (p q : α → Prop) (hcover : ∀ a, p a ∨ q a)
    (hp : TwoBQO (fun a b : {x : α // p x} => r a.val b.val))
    (hq : TwoBQO (fun a b : {x : α // q x} => r a.val b.val)) :
    TwoBQO r := by
  classical
  intro f
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_pairs fun m n h => (decide (p (f m n h)) : Bool)
  cases k with
  | true =>
    have hpf : ∀ i j (h : i < j), p (f (e i) (e j) (he h)) :=
      fun i j h => of_decide_eq_true (hk i j h)
    obtain ⟨i, j, l, hij, hjl, hrel⟩ := hp fun i j h => ⟨f (e i) (e j) (he h), hpf i j h⟩
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩
  | false =>
    have hqf : ∀ i j (h : i < j), q (f (e i) (e j) (he h)) :=
      fun i j h => (hcover _).resolve_left (of_decide_eq_false (hk i j h))
    obtain ⟨i, j, l, hij, hjl, hrel⟩ := hq fun i j h => ⟨f (e i) (e j) (he h), hqf i j h⟩
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩

/-!
### Finite products (Dickson's lemma for 2-BQO)
-/

/-- **Product closure** (Dickson's lemma for 2-BQO). If `r` on `α` and `s` on `β` are 2-BQO,
then the componentwise product `fun (a₁,b₁) (a₂,b₂) => r a₁ a₂ ∧ s b₁ b₂` on `α × β` is
2-BQO. -/
theorem TwoBQO.prod {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (hr : TwoBQO r)
    (hs : TwoBQO s) : TwoBQO fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2 := by
  rw [TwoBQO.iff_noBad] at hr hs ⊢
  intro ⟨f, hbad⟩
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  obtain ⟨e₁, he₁, hperf₁ | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
  · let f₂ : PairSeq β := fun m n h => (PairSeq.restrict f e₁ he₁ m n h).2
    obtain ⟨e₂, he₂, hperf₂ | hbad₂⟩ := PairSeq.perfect_or_bad s f₂
    · -- Both coordinates are perfect along `e₁ ∘ e₂`, contradicting `hbad`.
      exact hbad (e₁ (e₂ 0)) (e₁ (e₂ 1)) (e₁ (e₂ 2))
        (he₁ (he₂ (by norm_num : 0 < 1))) (he₁ (he₂ (by norm_num : 1 < 2)))
        ⟨hperf₁ (e₂ 0) (e₂ 1) (e₂ 2) (he₂ (by norm_num : 0 < 1)) (he₂ (by norm_num : 1 < 2)),
         hperf₂ 0 1 2 (by norm_num : 0 < 1) (by norm_num : 1 < 2)⟩
    · exact hs ⟨PairSeq.restrict f₂ e₂ he₂, hbad₂⟩
  · exact hr ⟨PairSeq.restrict f₁ e₁ he₁, hbad₁⟩

/-- **Iterated finite product.** For a `Fintype` index `ι`, the product `∀ i, α i` with pointwise
quasi-order is 2-BQO when each component is. -/
theorem TwoBQO.pi : ∀ (n : ℕ) (α : Fin n → Type*) (r : ∀ i : Fin n, α i → α i → Prop),
    (∀ i, TwoBQO (r i)) → TwoBQO fun f g : ∀ i, α i => ∀ i, r i (f i) (g i) := by
  intro n
  induction n with
  | zero => intro α r h f; exact ⟨0, 1, 2, by norm_num, by norm_num, fun i => i.elim0⟩
  | succ n ih =>
    intro α r h
    have hpi := ih (fun i => α (Fin.castSucc i)) (fun i => r (Fin.castSucc i))
      fun i => h (Fin.castSucc i)
    have hprod := (h (Fin.last n)).prod hpi
    have key : TwoBQO (fun f g : ∀ i : Fin (n + 1), α i =>
        r (Fin.last n) (f (Fin.last n)) (g (Fin.last n)) ∧
        ∀ i : Fin n, r (Fin.castSucc i) (f (Fin.castSucc i)) (g (Fin.castSucc i))) :=
      hprod.comap fun f : ∀ i : Fin (n + 1), α i => (f (Fin.last n), fun i => f (Fin.castSucc i))
    convert key using 2
    ext f
    constructor
    · intro hall; exact ⟨hall (Fin.last n), fun i => hall (Fin.castSucc i)⟩
    · intro ⟨hlast, hcast⟩ i; exact Fin.lastCases hlast hcast i

theorem TwoBQO.prodN : ∀ n : ℕ, TwoBQO fun f g : Fin n → ℕ => ∀ i, f i ≤ g i := fun n =>
  TwoBQO.pi n (fun _ => ℕ) (fun _ => (· ≤ ·)) fun _ => TwoBQO.of_wellFoundedLT

/-!
### Sum along a 2-BQO (the main closure theorem)

**Setup.** Given a quasi-order `r` on `ι` and quasi-orders `s i` on `α i`, the **sum** `Σᵢ αᵢ` is
ordered by `(i, x) ≤ (j, y)` iff `r i j ∧ i ≠ j` (strictly above), or `i = j ∧ s i x y` (same
fibre). This is Pequignot's Proposition 2.4(iii) lifted to 2-BQO.
-/

/-- The **lexicographic sum order along a partial order** on `Σ i, α i`: `(i,x) ≤ (j,y)` iff
`r i j` and `i ≠ j` (strictly above in `r`), or `i = j` and `x ≤ y` in `t i`. -/
def TwoBQO.LexSumRelQO {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) : (Σ i, s i) → (Σ i, s i) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ => (r i j ∧ i ≠ j) ∨ ∃ h : i = j, t i x (h ▸ y)

variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)

/-- `TwoBQO.LexSumRelQO r s t` is reflexive whenever each `t i` is. -/
theorem TwoBQO.LexSumRelQO.refl (ht_refl : ∀ i (x : s i), t i x x) (σ : Σ i, s i) :
    TwoBQO.LexSumRelQO r s t σ σ := by
  obtain ⟨i, x⟩ := σ
  exact Or.inr ⟨rfl, ht_refl i x⟩

/-- `TwoBQO.LexSumRelQO r s t` is transitive whenever `r` is reflexive, **antisymmetric**, and
transitive, and each `t i` is transitive. -/
theorem TwoBQO.LexSumRelQO.trans (hr_refl : ∀ i, r i i)
    (hr_antisymm : ∀ i j, r i j → r j i → i = j) (hr_trans : ∀ i j k, r i j → r j k → r i k)
    (ht_trans : ∀ i (x y z : s i), t i x y → t i y z → t i x z) {σ₁ σ₂ σ₃ : Σ i, s i}
    (h₁₂ : TwoBQO.LexSumRelQO r s t σ₁ σ₂) (h₂₃ : TwoBQO.LexSumRelQO r s t σ₂ σ₃) :
    TwoBQO.LexSumRelQO r s t σ₁ σ₃ := by
  obtain ⟨i, x⟩ := σ₁
  obtain ⟨j, y⟩ := σ₂
  obtain ⟨k, z⟩ := σ₃
  simp only [TwoBQO.LexSumRelQO] at h₁₂ h₂₃ ⊢
  rcases h₁₂ with ⟨hrij, hij_ne⟩ | ⟨hij, htxy⟩ <;> rcases h₂₃ with ⟨hrjk, hjk_ne⟩ | ⟨hjk, htyz⟩
  · -- (strict, strict)
    refine Or.inl ⟨hr_trans i j k hrij hrjk, fun hik => ?_⟩
    have hrki : r k i := hik ▸ hr_refl i
    have hrkj : r k j := hik ▸ hrij
    exact hjk_ne (hr_antisymm j k hrjk hrkj)
  · -- (strict, same)
    exact Or.inl ⟨hjk ▸ hrij, hjk ▸ hij_ne⟩
  · -- (same, strict)
    exact Or.inl ⟨hij ▸ hrjk, hij ▸ hjk_ne⟩
  · -- (same, same): compose the `t`-steps after substituting the two index equalities.
    refine Or.inr ⟨hij.trans hjk, ?_⟩
    subst hij; subst hjk
    exact ht_trans i x y z htxy htyz

/-- **Sum theorem for 2-BQO along a quasi-order, restricted to a bad pair-sequence.** If `f` is
bad for `LexSumRelQO r s t`, then some restriction of `f` either has a bad index projection
(for `r`), or has a constant index `i` along which the second components form a bad
pair-sequence for `t i`. The constructive content underlying `TwoBQO.lexSigmaQO`. -/
theorem TwoBQO.lexSigmaQO_reflect {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (f : PairSeq (Σ i, s i))
    (hf_bad : PairSeq.IsBad (TwoBQO.LexSumRelQO r s t) f) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      PairSeq.IsBad r (fun m n hmn => (f (e m) (e n) (he_mono hmn)).1) ∨
      ∃ (i : ι) (hmem : ∀ m n (hmn : m < n), (f (e m) (e n) (he_mono hmn)).1 = i),
        PairSeq.IsBad (t i) fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he_mono hmn)).2 := by
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
  · by_cases hconst : ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
        (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · set c := (f (e 0) (e 1) (he (by norm_num : (0 : ℕ) < 1))).1
      have hmem : ∀ m n : ℕ, (hmn : m < n) → (f (e m) (e n) (he hmn)).1 = c := by
        have hsucc : ∀ n : ℕ, (f (e n) (e (n + 1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n + 1) (n + 2) (Nat.lt_succ_self n)
              (Nat.lt_succ_self (n + 1))).symm.trans ih
        intro m n hmn
        exact (hconst m n (n + 1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      let g : PairSeq (s c) := fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      have hg_bad : PairSeq.IsBad (t c) g := by
        intro m n l hmn hnl htrel
        apply hf_bad (e m) (e n) (e l) (he hmn) (he hnl)
        set σ_mn := f (e m) (e n) (he hmn) with hσ_mn
        set σ_nl := f (e n) (e l) (he hnl) with hσ_nl
        have h_mn : σ_mn.1 = c := hmem m n hmn
        have h_nl : σ_nl.1 = c := hmem n l hnl
        rw [show σ_mn = ⟨c, h_mn ▸ σ_mn.2⟩ from by ext <;> simp [h_mn]]
        rw [show σ_nl = ⟨c, h_nl ▸ σ_nl.2⟩ from by ext <;> simp [h_nl]]
        exact Or.inr ⟨rfl, htrel⟩
      exact ⟨e, he, Or.inr ⟨c, hmem, hg_bad⟩⟩
    · exfalso
      push Not at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      exact hf_bad (e m) (e n) (e l) (he hmn) (he hnl) (Or.inl ⟨hperf m n l hmn hnl, hne⟩)
  · exact ⟨e, he, Or.inl hbad₁⟩

/-- **Sum theorem for 2-BQO along a quasi-order.** If `r` on `ι` is 2-BQO and each `t i` on
`s i` is 2-BQO, then `Σ i, s i` with `LexSumRelQO r s t` is 2-BQO. -/
theorem TwoBQO.lexSigmaQO {ι : Type*} (r : ι → ι → Prop) (hr : TwoBQO r) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (ht : ∀ i, TwoBQO (t i)) : TwoBQO (TwoBQO.LexSumRelQO r s t) := by
  intro f
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad⟩ := PairSeq.perfect_or_bad r f₁
  · by_cases hconst : ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
        (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · set c := (f (e 0) (e 1) (he (by norm_num : (0 : ℕ) < 1))).1
      have hmem : ∀ m n : ℕ, (hmn : m < n) → (f (e m) (e n) (he hmn)).1 = c := by
        have hsucc : ∀ n : ℕ, (f (e n) (e (n + 1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n + 1) (n + 2) (Nat.lt_succ_self n)
              (Nat.lt_succ_self (n + 1))).symm.trans ih
        intro m n hmn
        exact (hconst m n (n + 1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      let g : PairSeq (s c) := fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      obtain ⟨m, n, l, hmn, hnl, hrel⟩ := ht c g
      refine ⟨e m, e n, e l, he hmn, he hnl, ?_⟩
      show TwoBQO.LexSumRelQO r s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      have h_mn : (f (e m) (e n) (he hmn)).fst = c := hmem m n hmn
      have h_nl : (f (e n) (e l) (he hnl)).fst = c := hmem n l hnl
      refine Or.inr ⟨h_mn.trans h_nl.symm, ?_⟩
      revert hrel; simp only [g]; intro hrel; convert hrel using 1 <;> simp
    · push Not at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      refine ⟨e m, e n, e l, he hmn, he hnl, ?_⟩
      exact Or.inl ⟨hperf m n l hmn hnl, hne⟩
  · exfalso
    rw [TwoBQO.iff_noBad] at hr
    exact hr ⟨PairSeq.restrict f₁ e he, hbad⟩

/-!
## Domination order on subsets
-/

/-- `X` **dominates** into `Y`: every element of `X` is `r`-below some element of `Y`. -/
def DomOrder {α : Type*} (r : α → α → Prop) (X Y : Set α) : Prop := ∀ x ∈ X, ∃ y ∈ Y, r x y

/-- A bad sequence for `DomOrder r` yields a bad pair-sequence for the underlying `r`: pick, for
each `m < n`, an element of `f m` that is not `r`-below anything in `f n` (available since
`f m` does not dominate into `f n`). -/
private theorem badSeq_dom_to_pairSeq {α : Type*} {r : α → α → Prop} (f : ℕ → Set α)
    (hbad : ∀ m n, m < n → ¬ DomOrder r (f m) (f n)) :
    ∃ f_ : PairSeq α, (∀ m n (hmn : m < n), f_ m n hmn ∈ f m) ∧ PairSeq.IsBad r f_ := by
  have hex : ∀ m n, m < n → ∃ x, x ∈ f m ∧ ∀ y ∈ f n, ¬ r x y := by
    intro m n hmn
    have h := hbad m n hmn
    unfold DomOrder at h
    push Not at h
    exact h
  let g : ∀ m n, m < n → α := fun m n hmn => Classical.choose (hex m n hmn)
  have hg_mem : ∀ m n (hmn : m < n), g m n hmn ∈ f m :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).1
  have hg_bad : ∀ m n (hmn : m < n), ∀ y ∈ f n, ¬ r (g m n hmn) y :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).2
  refine ⟨g, hg_mem, ?_⟩
  intro m n l hmn hnl
  exact hg_bad m n hmn (g n l hnl) (hg_mem n l hnl)

/-- **The domination order on subsets of a 2-BQO is WQO.** -/
theorem TwoBQO.dom_twoBQO {α : Type*} {r : α → α → Prop} (hr : TwoBQO r) :
    WellQuasiOrdered (DomOrder r) := by
  intro g
  by_contra hcon
  push Not at hcon
  obtain ⟨f_, _, hf_bad⟩ := badSeq_dom_to_pairSeq g hcon
  rw [TwoBQO.iff_noBad] at hr
  exact hr ⟨f_, hf_bad⟩

/-!
## Infinite sequences

Infinite sequences `ℕ → Q` in a 2-BQO `Q` are WQO under `EmbedForAll`.
-/

/-- `s` **embeds pointwise** into `s'`: there is a strictly monotone reindexing `e` with
`r (s n) (s' (e n))` for every `n`. -/
def EmbedForAll {α : Type*} (r : α → α → Prop) (s s' : ℕ → α) : Prop :=
  ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (s n) (s' (e n))

/-- `EmbedForAll r` is a preorder on `ℕ → Q` whenever `r` is (reflexivity via the identity
reindexing, transitivity via composition of strictly monotone reindexings). -/
instance EmbedForAll.isPreorder {Q : Type*} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (ℕ → Q) (EmbedForAll r) where
  refl s := ⟨id, strictMono_id, fun n => refl_of r (s n)⟩
  trans := by
    rintro s s' s'' ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩
    exact ⟨e₂ ∘ e₁, he₂.comp he₁, fun n => trans_of r (h₁ n) (h₂ (e₁ n))⟩

private theorem exists_strictMono_of_greedy {P : ℕ → ℕ → Prop}
    (hbuild : ∀ start i : ℕ, ∃ j, start < j ∧ P i j) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, P i (e i) := by
  let e : ℕ → ℕ := fun i =>
    Nat.rec (motive := fun _ => ℕ) (hbuild 0 0).choose
      (fun n prev => (hbuild prev (n + 1)).choose) i
  have he0 : e 0 = (hbuild 0 0).choose := rfl
  have hesucc : ∀ n, e (n + 1) = (hbuild (e n) (n + 1)).choose := fun n => rfl
  have hP0 : P 0 (e 0) := he0 ▸ (hbuild 0 0).choose_spec.2
  have hPsucc : ∀ n, P (n + 1) (e (n + 1)) := fun n =>
    (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.2
  have hlt : ∀ n, e n < e (n + 1) := fun n => (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.1
  refine ⟨e, strictMono_nat_of_lt_succ hlt, fun i => ?_⟩
  cases i with
  | zero => exact hP0
  | succ n => exact hPsucc n

/-- **Strengthening of regularity.** If `f` is a regular sequence for a relation, then for every
threshold `n` there is a strictly monotone reindexing `e : ℕ → ℕ` whose values all lie at or
above `n` and which dominates `f` pointwise: `n ≤ e i` and `f i ≤ f (e i)` for every `i`. Proved
greedily via `exists_strictMono_of_greedy`, picking at each step a later index that is both `>`
the previous one and `≥ n`, available by regularity. -/
theorem Preorder.IsRegularSeq.exists_strictMono_dominating {Q : Type*} {le : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq le f) (n : ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, n ≤ e i ∧ le (f i) (f (e i)) := by
  apply exists_strictMono_of_greedy (P := fun i j => n ≤ j ∧ le (f i) (f j))
  intro start i
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt (max start n)
  exact ⟨j, lt_of_le_of_lt (le_max_left _ _) hj_gt,
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hj_gt), hj_mem⟩

/-- If `List.SublistForall₂ r l₁ l₂` then there is a strictly monotone `φ` witnessing `r` between
`l₁` and its image in `l₂`. -/
private theorem sublistForall₂_to_embedding {α : Type*} (r : α → α → Prop) (l₁ l₂ : List α)
    (h : List.SublistForall₂ r l₁ l₂) :
    ∃ φ : Fin l₁.length → Fin l₂.length, StrictMono φ ∧ ∀ i, r (l₁.get i) (l₂.get (φ i)) := by
  induction h
  · simp +decide [StrictMono]
  · simp_all +decide only [StrictMono, List.get_eq_getElem, List.length_cons,
      Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff, true_and, Fin.succ_pos,
      forall_const, Fin.succ_lt_succ_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    obtain ⟨φ, hφ₁, hφ₂⟩ := ‹_›
    use Fin.cons 0 (Fin.succ ∘ φ)
    aesop
  · rename_i l₁ l₂ h ih
    obtain ⟨φ, hφ₁, hφ₂⟩ := ih
    use fun i => Fin.succ (φ i)
    simp_all +decide [StrictMono]

/-- Combine a strictly monotone embedding `ψ` of an initial segment `[0, ka)` and a strictly
monotone embedding `eG` of the tail (shifted by `kb`) into a single strictly monotone
embedding `e : ℕ → ℕ` witnessing `r (Fa n) (Fb (e n))` for every `n`. -/
private theorem embed_combine {α : Type*} (r : α → α → Prop) (Fa Fb : ℕ → α) (ka kb : ℕ)
    (ψ : ℕ → ℕ) (hψ_lt : ∀ n, n < ka → ψ n < kb) (hψ_mono : ∀ m n, m < n → n < ka → ψ m < ψ n)
    (hψ_rel : ∀ n, n < ka → r (Fa n) (Fb (ψ n))) (eG : ℕ → ℕ) (heG_mono : StrictMono eG)
    (heG_rel : ∀ i, r (Fa (i + ka)) (Fb (eG i + kb))) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (Fa n) (Fb (e n)) := by
  refine ⟨fun n => if hn : n < ka then ψ n else eG (n - ka) + kb, ?_, ?_⟩
  · intro m n hmn
    by_cases hm : m < ka <;> by_cases hn : n < ka <;>
      simp +decide only [hm, ↓reduceDIte, hn, add_lt_add_iff_right]
    · exact hψ_mono m n hmn hn
    · linarith [hψ_lt m hm, heG_mono.monotone (Nat.zero_le (n - ka))]
    · linarith
    · exact heG_mono (by omega)
  · grind

/-- **`EmbedForAll r` is WQO on `ℕ → Q` whenever `r` is 2-BQO on `Q`.**

**Proof sketch.** Split each sequence `F n` into a regular tail `G n` preceded by a finite head
`w n` (`WellQuasiOrdered.eventuallyRegular`). Apply the product of Higman's lemma on the heads
(`WellQuasiOrdered.sublistForall₂`) and of the domination order on the downsets
`S n = {x | ∃ i, r x (G n i)}` of the tails (`TwoBQO.dom_twoBQO`) to a pair `a < b` with both
components related. The domination relation on downsets, combined with regularity, produces a
pointwise embedding of the tail `G a` into `G b`; the Higman relation on the heads produces a
pointwise embedding of the head `w a` into `w b`; `embed_combine` splices the two into a single
embedding of `F a` into `F b`. -/
theorem TwoBQO.embedForAll_wqo {α : Type*} {r : α → α → Prop} [IsPreorder α r] (hr : TwoBQO r) :
    WellQuasiOrdered (EmbedForAll r) := by
  intro F
  have hreg : ∀ n, ∃ k, IsRegularSeq r fun i => F n (i + k) :=
    fun n => hr.wellQuasiOrdered.eventuallyRegular r (F n)
  choose kk hkk using hreg
  set G : ℕ → ℕ → α := fun n i => F n (i + kk n) with hG_def
  set w : ℕ → List α := fun n => (List.range (kk n)).map (F n) with hw_def
  have hw_len : ∀ n, (w n).length = kk n := fun n => by simp [hw_def]
  have hw_get : ∀ n (i : ℕ) (h : i < (w n).length), (w n)[i] = F n i := fun n i h => by
    simp [hw_def, List.getElem_map, List.getElem_range]
  have hwqo_list : WellQuasiOrdered (List.SublistForall₂ r) := hr.wellQuasiOrdered.sublistForall₂
  have hdom_wqo : WellQuasiOrdered (DomOrder r) := hr.dom_twoBQO
  set S : ℕ → Set α := fun n => {x : α | ∃ i, r x (G n i)} with hS_def
  have hprod_wqo : WellQuasiOrdered
      (fun p q : List α × Set α => List.SublistForall₂ r p.1 q.1 ∧ DomOrder r p.2 q.2) :=
    WellQuasiOrdered.prod hwqo_list hdom_wqo
  obtain ⟨a, b, hab, hwgood, hSgood⟩ := hprod_wqo fun n => (w n, S n)
  have hpt : ∀ i, ∃ j, r (G a i) (G b j) := fun i => by
    obtain ⟨y, ⟨j, hy_mem⟩, hy_rel⟩ := hSgood (G a i) ⟨i, refl (G a i)⟩
    exact ⟨j, _root_.trans hy_rel hy_mem⟩
  have hbuild : ∀ start i : ℕ, ∃ j, start < j ∧ r (G a i) (G b j) := fun start i => by
    obtain ⟨j0, hj0⟩ := hpt i
    obtain ⟨j, hmem, hgt⟩ := Set.Infinite.exists_gt (hkk b j0) start
    exact ⟨j, hgt, IsTrans.trans _ _ _ hj0 hmem⟩
  obtain ⟨eG, heG_mono, heG_rel⟩ := exists_strictMono_of_greedy hbuild
  obtain ⟨φ, hφ_mono, hφ_rel⟩ := sublistForall₂_to_embedding r (w a) (w b) hwgood
  refine ⟨a, b, hab, ?_⟩
  refine embed_combine r (F a) (F b) (kk a) (kk b)
    (fun n => if h : n < kk a then (φ (Fin.cast (hw_len a).symm ⟨n, h⟩)).val else 0)
    ?_ ?_ ?_ eG heG_mono ?_
  · -- bound: the head map stays below `kk b`
    intro n hn
    simp only [dite_eq_left hn]
    have h := (φ (Fin.cast (hw_len a).symm ⟨n, hn⟩)).isLt
    have hl := hw_len b
    omega
  · -- monotonicity of the head map
    intro m n hmn hn
    have hm : m < kk a := lt_trans hmn hn
    simp only [dite_eq_left hm, dite_eq_left hn]
    have h := hφ_mono (a := Fin.cast (hw_len a).symm ⟨m, hm⟩)
      (b := Fin.cast (hw_len a).symm ⟨n, hn⟩) (by simpa using hmn)
    simpa using h
  · -- the head map witnesses `r`
    intro n hn
    simp only [dite_eq_left hn]
    have h := hφ_rel (Fin.cast (hw_len a).symm ⟨n, hn⟩)
    simpa [hw_def, List.get_eq_getElem, List.getElem_map, List.getElem_range,
      Fin.val_cast] using h
  · -- the tail map witnesses `r` (definitionally `G`)
    exact heG_rel

end
