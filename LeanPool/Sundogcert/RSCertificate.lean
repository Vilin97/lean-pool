/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Reed–Solomon evaluation certificate — the interpolation-dual of the syndrome certificate

A third instance of `Sundogcert.Certificate`'s discipline: **machine-check the deductive cheap-CHECK
core, name the imported hard-FIND wall.** The syndrome certificate views a code through its
**parity-check / coset**; this views the *same* Reed–Solomon code through its **evaluation** face: a
codeword is the evaluation vector `i ↦ f(xᵢ)` of a degree-`<k` polynomial `f` at `n` distinct nodes.

* **CHEAP to VERIFY (proved):** `k` evaluations DETERMINE the unique degree-`<k` polynomial
  (`rs_unique`, a thin specialization of `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`). A claimed
  decoding `f` of a word `y` is verified by one forward pass — degree `<k`, agreement with `y` in
  `≥ n−τ` positions (`O(n·k)`); `accept_sound` makes the check SOUND. Within the unique-decoding
  radius (`2τ+k ≤ n`) the decoding is *the* unique one (`unique_decoding`, inclusion–exclusion +
  `rs_unique`). Node-distinctness is a one-determinant certificate (`nodes_distinct_cert`).

* **DETERMINE but LOSE (the new face vs the syndrome pillar):** `corruption_fiber_nontrivial` — many
  words decode to the SAME `f`. The evaluation shadow DETERMINES the message but LOSES which
  corruptions were applied — the determining-shadow split, on a DIFFERENT mathlib core (polynomial
  root-counting) the syndrome lane never touches.

* **HARD to FIND (the imported wall, NOT proved):** a low-degree poly agreeing with a CORRUPTED
  word *past* the unique-decoding radius is list decoding — NP-hard for general RS (Guruswami–Vardy
  2005). Named, not proved, as the syndrome certificate imports ISD/decoding hardness.

## The one imported analytic input
`Polynomial.eq_of_natDegree_lt_card_of_eval_eq` (a domain polynomial of degree `< #points` vanishing
there is zero) + `det_vandermonde_ne_zero_iff`. A field discharges `[CommRing]+[IsDomain]`.

## References
* Reed–Solomon 1960; MacWilliams–Sloane (two RS views); Guruswami–Vardy 2005 (list-decode NP-hard).
* `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`, `Matrix.det_vandermonde_ne_zero_iff`.
-/

namespace Sundog.RSCertificate

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- A Reed–Solomon scheme: `n` DISTINCT nodes, message-degree bound `k`, decode radius `τ`.
Trust surface: `hnodes` (node distinctness — itself cheaply certifiable, below). -/
structure RSScheme (F : Type*) [Field F] where
  /-- Block length: the number of evaluation nodes. -/
  n : ℕ
  /-- Message-degree bound: codewords are evaluations of polynomials of degree `< k`. -/
  k : ℕ
  /-- Decode radius: at most `τ` disagreements are tolerated. -/
  τ : ℕ
  /-- The evaluation nodes (must be distinct, see `hnodes`). -/
  nodes : Fin n → F
  /-- Node distinctness: the nodes are pairwise distinct. -/
  hnodes : Function.Injective nodes

variable (S : RSScheme F)

/-- The codeword of a message polynomial: its evaluation vector at the nodes. -/
def encode (f : F[X]) : Fin S.n → F := fun i => f.eval (S.nodes i)

/-- The positions where a polynomial's codeword agrees with a received word `y`. -/
def agree (f : F[X]) (y : Fin S.n → F) : Finset (Fin S.n) :=
  Finset.univ.filter (fun i => f.eval (S.nodes i) = y i)

lemma mem_agree {f : F[X]} {y : Fin S.n → F} {i : Fin S.n} :
    i ∈ agree S f y ↔ f.eval (S.nodes i) = y i := by
  simp [agree]

/-- `f` is a valid decoding of `y`: degree `<k`, at most `τ` disagreements (`n ≤ #agree + τ`). -/
def Decodes (f : F[X]) (y : Fin S.n → F) : Prop :=
  f.natDegree < S.k ∧ S.n ≤ (agree S f y).card + S.τ

/-- Semantic safety: the received word has a valid decoding. -/
def Safe (y : Fin S.n → F) : Prop := ∃ f, Decodes S f y

omit [DecidableEq F] in
/--
**CORE (cheap-check soundness) — `k` evaluations DETERMINE the degree-`<k` polynomial.**
Two polys of `natDegree < k` agreeing on a set `s` of `≥k` distinct nodes are EQUAL, by
`Polynomial.eq_of_natDegree_lt_card_of_eval_eq` (`max deg < #s`, nodes restricted to `s` injective).
The deductive core: the evaluation map is injective on degree-`<k` messages. -/
theorem rs_unique {p q : F[X]} {s : Finset (Fin S.n)} (hp : p.natDegree < S.k)
    (hq : q.natDegree < S.k) (hk : S.k ≤ s.card)
    (hagree : ∀ i ∈ s, p.eval (S.nodes i) = q.eval (S.nodes i)) : p = q := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
    (f := fun i : {x // x ∈ s} => S.nodes i.1) ?_ ?_ ?_
  · intro a b hab; exact Subtype.ext (S.hnodes hab)
  · intro i; exact hagree i.1 i.2
  · rw [Fintype.card_coe]; exact lt_of_lt_of_le (max_lt hp hq) hk

omit [DecidableEq F] in
/-- **Node-distinctness is a one-determinant certificate.** A single nonzero Vandermonde determinant
cheaply certifies the scheme's trust-surface hypothesis `hnodes`. -/
theorem nodes_distinct_cert :
    (Matrix.vandermonde S.nodes).det ≠ 0 ↔ Function.Injective S.nodes :=
  Matrix.det_vandermonde_ne_zero_iff

/-! ## The cheap verifier and its accept-soundness. -/

/-- A cheap verifier: a forward decoder whose `some f` output carries a proof it decodes. -/
structure Verifier (S : RSScheme F) where
  /-- Forward decoder: optionally produce a decoding polynomial for a received word. -/
  decode? : (Fin S.n → F) → Option F[X]
  /-- Soundness of the decoder: any returned polynomial genuinely decodes the received word. -/
  decode_sound : ∀ y f, decode? y = some f → Decodes S f y

/-- The two-valued verdict of the Reed–Solomon verifier. -/
inductive Verdict
  /-- A decoding polynomial was exhibited. -/
  | accept
  /-- No decoding was found by the cheap forward decoder. -/
  | quarantine
deriving DecidableEq

/-- accept if a decoding is exhibited; quarantine otherwise (the cheap forward check). -/
def Verifier.run (V : Verifier S) (y : Fin S.n → F) : Verdict :=
  match V.decode? y with
  | some _ => Verdict.accept
  | none => Verdict.quarantine

/-- **Accept-soundness (by construction).** accept ⟹ Safe — the exhibited decoding IS a witness. -/
theorem accept_sound (V : Verifier S) (y : Fin S.n → F) :
    V.run S y = Verdict.accept → Safe S y := by
  intro h
  cases hd : V.decode? y with
  | some f => exact ⟨f, V.decode_sound y f hd⟩
  | none => simp only [Verifier.run, hd] at h; exact absurd h (by decide)

/--
**UNIQUE DECODING (the quantitative half) — within the radius the decoding is THE unique one.** If
`2τ+k ≤ n` (the unique-decoding radius `2τ ≤ n−k`), two valid decodings of a word are equal. Each
agrees with `y` in `≥ n−τ` positions, so (inclusion–exclusion) they agree with EACH OTHER in
`≥ n−2τ ≥ k` positions — whence `rs_unique`. So `accept` returns the unique message. -/
theorem unique_decoding (hrad : 2 * S.τ + S.k ≤ S.n) (y : Fin S.n → F)
    {p q : F[X]} (hp : Decodes S p y) (hq : Decodes S q y) : p = q := by
  have h1 : S.n ≤ (agree S p y).card + S.τ := hp.2
  have h2 : S.n ≤ (agree S q y).card + S.τ := hq.2
  have hunion := Finset.card_union_add_card_inter (agree S p y) (agree S q y)
  have hUle : (agree S p y ∪ agree S q y).card ≤ S.n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hk : S.k ≤ (agree S p y ∩ agree S q y).card := by omega
  refine rs_unique S hp.1 hq.1 hk ?_
  intro i hi
  rw [Finset.mem_inter, mem_agree, mem_agree] at hi
  rw [hi.1, hi.2]

/--
**CORRUPTION_FIBER_NONTRIVIAL — DETERMINE the message, LOSE the corruption.** For degree-`<k` `f`
and radius `τ ≥ 1` (`n ≥ 1`), at least TWO distinct words decode to the same `f`: the clean codeword
`encode f`, and `encode f` with one position corrupted (still `≤ τ` errors). So it DETERMINES
the message but LOSES which corruptions were applied — the determine/lose split, on the
polynomial-evaluation core. -/
theorem corruption_fiber_nontrivial (hτ : 1 ≤ S.τ) (hn : 1 ≤ S.n)
    {f : F[X]} (hf : f.natDegree < S.k) :
    ∃ y₁ y₂ : Fin S.n → F, y₁ ≠ y₂ ∧ Decodes S f y₁ ∧ Decodes S f y₂ := by
  let i₀ : Fin S.n := ⟨0, hn⟩
  let c : Fin S.n → F := encode S f
  obtain ⟨v, hv⟩ := exists_ne (c i₀)        -- a value ≠ the clean symbol at i₀
  refine ⟨c, Function.update c i₀ v, ?_, ?_, ?_⟩
  · -- the two words differ at i₀
    intro h
    have := congrFun h i₀
    rw [Function.update_self] at this
    exact hv this.symm
  · -- the clean codeword decodes: it agrees everywhere
    refine ⟨hf, ?_⟩
    have : agree S f c = Finset.univ := by
      ext i; simp [mem_agree, encode, c]
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  · -- the corrupted word decodes: it agrees everywhere except i₀ (≥ n−1 ≥ n−τ)
    refine ⟨hf, ?_⟩
    have hsub : Finset.univ.erase i₀ ⊆ agree S f (Function.update c i₀ v) := by
      intro i hi
      rw [Finset.mem_erase] at hi
      rw [mem_agree, Function.update_of_ne hi.1]
      simp [encode, c]
    have : S.n - 1 ≤ (agree S f (Function.update c i₀ v)).card := by
      have hcard : (Finset.univ.erase i₀).card = S.n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      calc S.n - 1 = (Finset.univ.erase i₀).card := hcard.symm
        _ ≤ _ := Finset.card_le_card hsub
    omega

end Sundog.RSCertificate

-- Axiom audit: the cheap-check core + soundness + the determine/lose theorem should depend only on
-- mathlib's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
