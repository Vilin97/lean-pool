/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Data.Matrix.Mul           -- Matrix, mulVec/vecMul, the `*ᵥ` / `ᵥ*` notation
import Mathlib.InformationTheory.Hamming  -- hammingNorm (the error weight)
import Mathlib.Data.Fintype.BigOperators  -- Fintype.card_fun (for secret_bits_lost)
import Mathlib.Algebra.Order.BigOperators.Group.Finset  -- card_biUnion_le_card_mul (column-weight)

/-!
  Sundog syndrome certificate — soundness + lossiness core  (Lean 4 / mathlib v4.30.0)
  ALL theorems PROVED, kernel-checked + axiom-clean (propext/Classical.choice/Quot.sound only).
    lossiness-by-algebra: syndrome ⟂ secret; |F|^k bodies per syndrome.
    soundness: accept ⟹ Safe; no accepted body is unsafe; reject ⟹ ¬Safe under a sound `lb`.
    two concrete sound bounds: `supportLb` (τ=0) and the non-degenerate column-weight bound
    `colWeightLb` (`reject_sound_colweight`, rejects at τ>0; loose global worst-column divisor).
  OUT OF SCOPE for Lean: the ISD/SIS one-wayness — an imported hardness assumption, NOT a theorem.
  TRUST SURFACE = the `Scheme` fields (esp. `hHG`) + `Safe`; everything else is machine-checked.
-/

open Matrix

namespace Sundog.Certificate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
-- Deployed instance: `F := ZMod 2` (the [n=128, k=64] GF(2) certificate). Field-generic below.

/-- Hamming weight = number of nonzero coordinates (the error weight). -/
def wt {n : ℕ} (e : Fin n → F) : ℕ := hammingNorm e

/-! ### THE TRUST SURFACE — a reviewer audits these definitions; the rest is machine-checked. -/

/-- A syndrome-certificate scheme.  Load-bearing definitional content: `hHG` (the code lies in
    `ker H`) and the meaning of `τ` (the safe decoding radius). -/
structure Scheme (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  /-- Block length: the number of coordinates of a body. -/
  n : ℕ
  /-- Message dimension: the number of secret symbols. -/
  k : ℕ
  /-- Syndrome length: the number of parity checks. -/
  m : ℕ
  /-- Generator matrix: its rows span the safe code `C = range (· ᵥ* G)`. -/
  G : Matrix (Fin k) (Fin n) F
  /-- Parity-check matrix: the shadow map `y ↦ H *ᵥ y`. -/
  H : Matrix (Fin m) (Fin n) F
  /-- Safe decoding radius: bodies within this Hamming radius of the code are safe. -/
  τ : ℕ
  /-- The dual-pair law: every codeword has zero syndrome. -/
  hHG : ∀ s : Fin k → F, H *ᵥ (s ᵥ* G) = 0

variable (S : Scheme F)

/-- The body `y = sG + e`: secret message `s`, sparse error `e`. -/
def body (s : Fin S.k → F) (e : Fin S.n → F) : Fin S.n → F := s ᵥ* S.G + e

/-- **Safety predicate** (semantic): some same-syndrome witness has weight ≤ τ.
    The planted `e` is a *label*, never referenced here. -/
def Safe (y : Fin S.n → F) : Prop :=
  ∃ e' : Fin S.n → F, S.H *ᵥ e' = S.H *ᵥ y ∧ wt e' ≤ S.τ

/-! ### The verifier (cheap, three-valued) -/

/-- The three-valued verdict a cheap verifier returns. -/
inductive Verdict
  /-- A light same-syndrome witness was exhibited. -/
  | accept
  /-- The cheap lower bound rules out every light witness. -/
  | reject
  /-- Neither accepted nor rejected: needs a stronger check. -/
  | quarantine
  deriving DecidableEq

/-- A cheap verifier: a forward witness search + a sound lower bound.  The *witness* spec is
    bundled in (clean); the *lower-bound* spec is deferred to `reject_sound`. -/
structure Verifier (S : Scheme F) where
  /-- Forward witness search: optionally produce a same-syndrome light witness for a body. -/
  witnessOpt : (Fin S.n → F) → Option (Fin S.n → F)
  /-- A sound lower bound on the minimum same-syndrome weight, read off the syndrome. -/
  lb : (Fin S.m → F) → ℕ
  /-- Soundness of the witness search: any returned witness is genuinely same-syndrome and light. -/
  witness_sound : ∀ y e', witnessOpt y = some e' → S.H *ᵥ e' = S.H *ᵥ y ∧ wt e' ≤ S.τ

/-- accept if a light witness is exhibited; reject if the cheap bound rules out every light
    witness; quarantine otherwise. -/
def Verifier.run (V : Verifier S) (y : Fin S.n → F) : Verdict :=
  match V.witnessOpt y with
  | some _ => Verdict.accept
  | none => if S.τ < V.lb (S.H *ᵥ y) then Verdict.reject else Verdict.quarantine

/-! ### CORE — clean, by-construction; formalize first. -/

/-- **Lossiness by algebra.**  syndrome(sG+e) = syndrome(e): independent of the secret `s`.
    `H (sG + e) = H(sG) + He = 0 + He` since codewords have zero syndrome (`hHG`). -/
theorem syndrome_independent_of_secret (s : Fin S.k → F) (e : Fin S.n → F) :
    S.H *ᵥ body S s e = S.H *ᵥ e := by
  unfold body
  rw [Matrix.mulVec_add, S.hHG s, zero_add]

/-- **Secret indistinguishability.**  With `e` fixed, the syndrome separates no two secrets —
    the fiber is the whole message space (the content of "s is gone"). -/
theorem secret_fiber_eq_univ (e : Fin S.n → F) :
    {s : Fin S.k → F | S.H *ᵥ body S s e = S.H *ᵥ e} = Set.univ :=
  Set.eq_univ_of_forall fun s => syndrome_independent_of_secret S s e

/-- **`|F|ᵏ`-to-one.**  The shadow loses `k·log|F|` bits. -/
theorem secret_bits_lost :
    Fintype.card (Fin S.k → F) = (Fintype.card F) ^ S.k := by
  simp

/-- **Accept-soundness (the by-construction core).**  accept ⟹ Safe.
    The only way to `accept` is via an exhibited witness, which *is* a proof of `Safe`. -/
theorem accept_sound (V : Verifier S) (y : Fin S.n → F) :
    V.run S y = Verdict.accept → Safe S y := by
  intro h
  unfold Verifier.run at h
  cases hw : V.witnessOpt y with
  | some e' => exact ⟨e', V.witness_sound y e' hw⟩
  | none => simp only [hw] at h; split at h <;> simp at h

/-- **Spoof impossibility** (corollary): no accepted body is unsafe. -/
theorem no_passing_unsafe (V : Verifier S) :
    ¬ ∃ y, V.run S y = Verdict.accept ∧ ¬ Safe S y := by
  rintro ⟨y, hacc, hunsafe⟩
  exact hunsafe (accept_sound S V y hacc)

/-! ### Reject-soundness, and a concrete sound lower bound -/

/-- The cheap lower bound never exceeds any same-syndrome witness weight. -/
def LbSound (V : Verifier S) : Prop :=
  ∀ y e', S.H *ᵥ e' = S.H *ᵥ y → V.lb (S.H *ᵥ y) ≤ wt e'

/-- **Reject-soundness.**  If the cheap bound is sound (`LbSound`) and the verifier rejects, the
    body is unsafe: a light witness forces `lb ≤ wt e' ≤ τ`, contradicting the `τ < lb` that fired
    the reject. -/
theorem reject_sound (V : Verifier S) (hLb : LbSound S V) (y : Fin S.n → F) :
    V.run S y = Verdict.reject → ¬ Safe S y := by
  intro h hsafe
  obtain ⟨e', he, hwt⟩ := hsafe
  have hlb := hLb y e' he
  unfold Verifier.run at h
  cases hw : V.witnessOpt y with
  | some w => simp [hw] at h
  | none =>
      simp only [hw] at h
      split at h
      · omega          -- reject branch: τ < lb ≤ wt e' ≤ τ, contradiction
      · simp at h       -- quarantine ≠ reject

/-- A **concrete** cheap sound lower bound: a nonzero syndrome forces error weight ≥ 1 (because
    `H 0 = 0`, so any witness for a nonzero syndrome is itself nonzero).  Cheap (one zero-test) and
    provably sound.  HONEST LIMIT: it only lets the verifier `reject` at `τ = 0` (the degenerate
    cheap-reject branch, RISK-1 in the prototype note).  The non-degenerate column-weight bound
    `wt e ≥ ⌈hammingNorm (H y) / maxColWeight H⌉` is the documented next target. -/
def supportLb (z : Fin S.m → F) : ℕ := if z = 0 then 0 else 1

theorem supportLb_sound (y e' : Fin S.n → F) (he : S.H *ᵥ e' = S.H *ᵥ y) :
    supportLb S (S.H *ᵥ y) ≤ wt e' := by
  unfold supportLb
  by_cases hz : S.H *ᵥ y = 0
  · simp [hz]
  · simp only [hz, if_false]
    have hne : e' ≠ 0 := fun h0 => hz (by rw [← he, h0, Matrix.mulVec_zero])
    have hnz : hammingNorm e' ≠ 0 := fun h => hne (hammingNorm_eq_zero.mp h)
    rw [wt]; omega

/-- `supportLb` is `LbSound` for any verifier that uses it. -/
theorem supportLb_lbSound (V : Verifier S) (hlb : V.lb = supportLb S) : LbSound S V := by
  intro y e' he
  rw [hlb]
  exact supportLb_sound S y e' he

/-- **Unconditional reject-soundness** for the concrete `supportLb` verifier (no hypothesis). -/
theorem reject_sound_support (V : Verifier S) (hlb : V.lb = supportLb S) (y : Fin S.n → F) :
    V.run S y = Verdict.reject → ¬ Safe S y :=
  reject_sound S V (supportLb_lbSound S V hlb) y

/-! ### Column-weight bound — a NON-DEGENERATE concrete sound bound (rejects at `τ > 0`).
    Stronger than `supportLb`: it bounds error weight below by (syndrome weight / worst column
    weight of `H`).  Honest caveat: loose (a global worst-column divisor) — a soundness/coverage
    win over `supportLb`, not a tightness win. -/

variable {a b : ℕ}

/-- Support of a vector: where it is nonzero (`hammingNorm` counts exactly this). -/
def vsupp {n : ℕ} (v : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)

omit [Fintype F] in
/-- `hammingNorm` is the cardinality of the support. -/
theorem hammingNorm_eq_card_vsupp {n : ℕ} (v : Fin n → F) :
    hammingNorm v = (vsupp v).card := by
  simp only [hammingNorm, vsupp]

/-- Worst-case column weight of `M`: the most nonzero entries in any single column. -/
def colBound (M : Matrix (Fin a) (Fin b) F) : ℕ :=
  Finset.univ.sup (fun j => (Finset.univ.filter (fun i => M i j ≠ 0)).card)

omit [Fintype F] in
/-- Every column's support is no larger than `colBound M`. -/
theorem card_colSupp_le (M : Matrix (Fin a) (Fin b) F) (j : Fin b) :
    (Finset.univ.filter (fun i => M i j ≠ 0)).card ≤ colBound M :=
  Finset.le_sup (f := fun j => (Finset.univ.filter (fun i => M i j ≠ 0)).card)
    (Finset.mem_univ j)

omit [Fintype F] in
/-- Support inclusion: `support(M *ᵥ e) ⊆ ⋃_{j ∈ support e} support(col j)`.  A product coordinate
    is nonzero only if some term `M i j * e j` is — i.e. both factors are. -/
theorem vsupp_mulVec_subset (M : Matrix (Fin a) (Fin b) F) (e : Fin b → F) :
    vsupp (M *ᵥ e) ⊆ (vsupp e).biUnion (fun j => Finset.univ.filter (fun i => M i j ≠ 0)) := by
  intro i hi
  simp only [vsupp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hne : (∑ j, M i j * e j) ≠ 0 := by
    simpa only [Matrix.mulVec, dotProduct] using hi
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [mul_ne_zero_iff] at hj
  simp only [Finset.mem_biUnion, vsupp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, hj.2, hj.1⟩

omit [Fintype F] in
/-- **Key lemma.**  A heavy syndrome forces a heavy error — each error coordinate lights up at most
    `colBound M` rows: `hammingNorm (M *ᵥ e) ≤ colBound M * hammingNorm e`. -/
theorem hammingNorm_mulVec_le (M : Matrix (Fin a) (Fin b) F) (e : Fin b → F) :
    hammingNorm (M *ᵥ e) ≤ colBound M * hammingNorm e := by
  rw [hammingNorm_eq_card_vsupp, hammingNorm_eq_card_vsupp]
  calc (vsupp (M *ᵥ e)).card
      ≤ ((vsupp e).biUnion (fun j => Finset.univ.filter (fun i => M i j ≠ 0))).card :=
        Finset.card_le_card (vsupp_mulVec_subset M e)
    _ ≤ (vsupp e).card * colBound M :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun j _ => card_colSupp_le M j)
    _ = colBound M * (vsupp e).card := Nat.mul_comm _ _

/-- **Concrete non-degenerate bound:** syndrome weight / worst column weight of `H`.  Cheap (one
    `hammingNorm` zero-test + one division; `colBound S.H` amortized once per scheme).  Unlike
    `supportLb` it can exceed 1, so `reject` fires at `τ > 0`.  Floor division is the SOUND
    direction (it only under-estimates weight); `colBound = 0` ⟹ `H = 0` ⟹ syndrome `= 0`, sound. -/
def colWeightLb (z : Fin S.m → F) : ℕ := hammingNorm z / colBound S.H

/-- `colWeightLb` never exceeds any same-syndrome witness weight (soundness). -/
theorem colWeightLb_sound (y e' : Fin S.n → F) (he : S.H *ᵥ e' = S.H *ᵥ y) :
    colWeightLb S (S.H *ᵥ y) ≤ wt e' := by
  unfold colWeightLb wt
  have hkey : hammingNorm (S.H *ᵥ y) ≤ colBound S.H * hammingNorm e' := by
    rw [← he]; exact hammingNorm_mulVec_le S.H e'
  exact Nat.div_le_of_le_mul hkey

/-- `colWeightLb` is `LbSound` for any verifier that adopts it. -/
theorem colWeightLb_lbSound (V : Verifier S) (hlb : V.lb = colWeightLb S) : LbSound S V := by
  intro y e' he
  rw [hlb]
  exact colWeightLb_sound S y e' he

/-- **Unconditional, non-degenerate reject-soundness** for the column-weight verifier. -/
theorem reject_sound_colweight (V : Verifier S) (hlb : V.lb = colWeightLb S) (y : Fin S.n → F) :
    V.run S y = Verdict.reject → ¬ Safe S y :=
  reject_sound S V (colWeightLb_lbSound S V hlb) y

end Sundog.Certificate
