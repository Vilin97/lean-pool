/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBridge
import LeanPool.BrillNoetherGraphs.Demazure.Transpositions

/-!
# Sign-changing inversions

Section 6 of the twice-marked banana paper proves the chain theorem
(`thm:bngChain`, Theorem 1.13) through a single combinatorial estimate on the
Demazure product: `prop:sciInvStar` (6.13).  This file introduces the
statistic it is about and states the two results, with the paper's proofs
recorded as the plan for discharging them.

## Where this sits

The Lean development already has:

* `eq:tauGlued` — `Utilities.satisfiesTransmission_wedgeAddDivisor_star`;
* the two-factor and `ℓ`-fold gluing of transmission existence
  (`Utilities.ChainGluing`), conditional on a *factorization* property;
* `lem:tauChars` — `tauChars_rank_eq_southeast` and its northwest twin;
* the raw-`ℤ → ℤ`-to-`AspPerm` bridge (`Bananas/TransmissionBridge.lean`).

Note that `Utilities.ChainGluing` reaches the chain statement by a
*different* route from the paper: it asks for a length-budgeted factorization
`τ = α ⋆ β`, whereas the paper never factors, and instead bounds
`sci (α ⋆ β)` directly.  The `sci` route below is the paper's, and is the one
that does not require inventing a splitting.

## Status

Both estimates are proved, with no `sorry`.  This file proves the induction
for `prop:sciInvStar` (6.13) from a named `AffineReductionData k`; the companion
module `AffineReduction.lean` constructs that datum from the ordinary adjacent
descent theorem and a direct count of periodic inversion classes, and exports
the unconditional theorem `sci_star_le`.  The base case is
`sci_star_le_of_kInversionCount_eq_zero`.

`sci_star_sigma_le` (`lem-SciSimpleRefl`, 6.12) is unconditional.

Downstream: `prop:sciLambda` (6.10) relates `sci (τ_D)` to the Weierstrass
partition and needs `lem:tauChars` (available as `tauChars_rank_eq_southeast`
and its northwest twin) plus a Riemann-Roch telescoping sum;
`thm:glueBNGtoKGT` (6.6) is then 6.10 + 6.13 + `eq:tauGlued`;
`prop:glueMarked` (6.14) needs the wedge rank formula, available as
`Utilities.VertexWedgeRankFormula.vertexWedge_rank_ge_iff_profile_inequalities`;
and `thm:bngChain` (6.16) is the induction over the chain.
-/

namespace Bananas

open Utilities

/-- Paper source: Definition 6.9.

A *sign-changing inversion* of `α` is a pair `u < v` with `α u > 0` and
`α v ≤ 0`.  Unlike an ordinary inversion this compares each value against the
fixed threshold `0` rather than against the other value. -/
def sciSet (α : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | p.1 < p.2 ∧ 0 < α p.1 ∧ α p.2 ≤ 0 }

/-- Paper source: Definition 6.9, the count `sci(α)`.

As with `kInversionCount`, `Set.ncard` is `0` on an infinite set, so every
statement below that bounds `sci` from above must either carry finiteness or be
read only for `α` where the set is finite.  For an almost-sign-preserving `α`
it is automatically finite. -/
noncomputable def sci (α : ℤ → ℤ) : ℕ := (sciSet α).ncard

theorem mem_sciSet_iff (α : ℤ → ℤ) (p : ℤ × ℤ) :
    p ∈ sciSet α ↔ p.1 < p.2 ∧ 0 < α p.1 ∧ α p.2 ≤ 0 := Iff.rfl

/-- A shift has no sign-changing inversions in the relevant range: this is the
base case of the induction in `prop:sciInvStar`.  Stated for the identity,
which is the only case the induction actually consumes. -/
theorem sciSet_id : sciSet (fun n : ℤ => n) = ∅ := by
  ext p
  simp only [mem_sciSet_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hlt hpos
  omega

@[simp] theorem sci_id : sci (fun n : ℤ => n) = 0 := by
  rw [sci, sciSet_id, Set.ncard_empty]

/-- The affine simple reflection `σ^k_n` of Section 6: it swaps `m` and `m + 1`
for every `m ≡ n (mod k)` and fixes everything else.

The paper writes `σ^k_n = σ_{n + kℤ}`; the definition below makes that action
explicit. -/
def affineSimpleReflection (k n : ℤ) : ℤ → ℤ := fun m =>
  if (m - n) % k = 0 then m + 1
  else if (m - 1 - n) % k = 0 then m - 1
  else m

/-! ## The pigeonhole core of Lemma 6.12

The whole content of `lem-SciSimpleRefl` is that an `α` with few sign-changing
inversions cannot flip sign twice within one residue class mod `k`.  That
statement involves neither the Demazure product nor `σ_S`, so it is isolated
here. -/

/-- Two sign flips of `α` at positions congruent mod `k` force `k - 1`
sign-changing inversions.

The injection is the paper's: for each `u` strictly between the two flip
positions, either `(u, m₂)` or `(m₁ + 1, u)` is a sign-changing inversion,
according to the sign of `α u`, and these are pairwise distinct. -/
theorem sub_one_le_sci_of_two_signFlips
    (α : ℤ → ℤ) (k : ℤ) (hfin : (sciSet α).Finite)
    {m₁ m₂ : ℤ} (hlt : m₁ < m₂) (hdvd : k ∣ (m₂ - m₁))
    (h₁ : 0 < α (m₁ + 1)) (h₂ : α m₂ ≤ 0) :
    k - 1 ≤ (sci α : ℤ) := by
  classical
  -- `k` divides a positive difference, so it is at most that difference.
  have hk : k ≤ m₂ - m₁ := Int.le_of_dvd (by omega) hdvd
  set n : ℕ := (m₂ - m₁ - 1).toNat with hn
  have hnval : (n : ℤ) = m₂ - m₁ - 1 := by
    rw [hn, Int.toNat_of_nonneg]; omega
  -- For each `u` strictly between the flips, one of the two candidate pairs is
  -- a sign-changing inversion, according to the sign of `α u`.
  set f : Fin n → ℤ × ℤ := fun i =>
    if 0 < α (m₁ + 1 + i.val) then (m₁ + 1 + i.val, m₂)
    else (m₁ + 1, m₁ + 1 + i.val) with hf
  have hrange : ∀ i : Fin n, m₁ + 1 + (i.val : ℤ) < m₂ := by
    intro i
    have := i.isLt
    omega
  have hmaps : ∀ i : Fin n, i ∈ (Set.univ : Set (Fin n)) → f i ∈ sciSet α := by
    intro i _
    have hlt' := hrange i
    by_cases hpos : 0 < α (m₁ + 1 + (i.val : ℤ))
    · simp only [hf, if_pos hpos]
      exact ⟨hlt', hpos, h₂⟩
    · have hne : m₁ + 1 < m₁ + 1 + (i.val : ℤ) := by
        rcases Nat.eq_zero_or_pos i.val with h0 | hpos'
        · exact absurd (by simpa [h0] using h₁) hpos
        · have : (0 : ℤ) < (i.val : ℤ) := by exact_mod_cast hpos'
          omega
      simp only [hf, if_neg hpos]
      exact ⟨hne, h₁, not_lt.mp hpos⟩
  have hinj : Set.InjOn f (Set.univ : Set (Fin n)) := by
    intro a _ b _ hab
    have hra := hrange a
    have hrb := hrange b
    apply Fin.ext
    by_cases hpa : 0 < α (m₁ + 1 + (a.val : ℤ)) <;>
      by_cases hpb : 0 < α (m₁ + 1 + (b.val : ℤ))
    · simp only [hf, if_pos hpa, if_pos hpb, Prod.mk.injEq] at hab
      omega
    · -- `(m₁+1+a, m₂) = (m₁+1, m₁+1+b)` forces `m₂ = m₁+1+b`, impossible.
      simp only [hf, if_pos hpa, if_neg hpb, Prod.mk.injEq] at hab
      omega
    · simp only [hf, if_neg hpa, if_pos hpb, Prod.mk.injEq] at hab
      omega
    · simp only [hf, if_neg hpa, if_neg hpb, Prod.mk.injEq] at hab
      omega
  have hle := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set (Fin n)))
    (t := sciSet α) f hmaps hinj hfin
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  rw [sci]
  omega

/-- An ASP permutation has finitely many sign-changing inversions.

`is_asp` says only finitely many `n` satisfy `n * α n < 0`.  Choose `N`
bounding that set together with `α⁻¹ 0`.  Then every sign-changing inversion
lies in the box `[-N, N]²`: if `u < -N` then `u < 0` and `u ∉ F` force
`α u ≤ 0`; if `v > N` then `v > 0` and `v ∉ F ∪ {α⁻¹ 0}` force `0 < α v`; and
`u < v` propagates the two bounds to the other coordinates. -/
theorem sciSet_finite (α : AspPerm) : (sciSet α.func).Finite := by
  classical
  obtain ⟨z, hz⟩ := α.surjective 0
  set F : Set ℤ := { n : ℤ | n * α.func n < 0 } with hF
  have hFfin : F.Finite := α.asp
  set T : Set ℤ := insert z F with hT
  have hTfin : T.Finite := hFfin.insert z
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ n ∈ T, |n| ≤ N := by
    obtain ⟨a, ha⟩ := hTfin.bddAbove
    obtain ⟨b, hb⟩ := hTfin.bddBelow
    refine ⟨max a (-b), fun n hn => ?_⟩
    have h1 : n ≤ a := ha hn
    have h2 : b ≤ n := hb hn
    rw [abs_le]
    constructor <;> [skip; skip] <;> simp only [le_max_iff, neg_le] <;> omega
  have hN0 : 0 ≤ N := le_trans (abs_nonneg z) (hN z (Set.mem_insert _ _))
  -- Outside `T`, the sign of `α n` matches the sign of `n`.
  have hout : ∀ n : ℤ, |n| > N → (0 < n → 0 < α.func n) ∧ (n < 0 → α.func n < 0) := by
    intro n hn
    have hnF : n ∉ F := fun h => absurd (hN n (Set.mem_insert_of_mem _ h)) (by omega)
    have hnz : n ≠ z := by
      intro h
      exact absurd (hN n (h ▸ Set.mem_insert _ _)) (by omega)
    have hnzero : α.func n ≠ 0 := by
      intro h
      exact hnz (α.injective (by rw [h, hz]))
    simp only [hF, Set.mem_ofPred_eq, not_lt] at hnF
    constructor <;> intro hsign <;> rcases lt_trichotomy (α.func n) 0 with h | h | h <;>
      first
        | omega
        | (exfalso; nlinarith)
  refine Set.Finite.subset ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)) ?_
  rintro ⟨u, v⟩ ⟨hlt0, hpos0, hnonpos0⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  -- Projections of an explicit pair, restated so `omega` sees the atoms.
  have hlt : u < v := hlt0
  have hpos : 0 < α.func u := hpos0
  have hnonpos : α.func v ≤ 0 := hnonpos0
  have hu : -N ≤ u := by
    by_contra h
    have hb : |u| > N := by rw [abs_of_nonpos (by omega)]; omega
    have := (hout u hb).2 (by omega)
    omega
  have hv : v ≤ N := by
    by_contra h
    have hb : |v| > N := by rw [abs_of_nonneg (by omega)]; omega
    have := (hout v hb).1 (by omega)
    omega
  exact ⟨⟨hu, by omega⟩, ⟨by omega, hv⟩⟩

/-! ## Transport along an adjacent-transposition permutation -/

/-- The positions in `S` at which `α` flips from nonpositive to positive.
These are exactly the pairs that `σ_S` can turn into a new sign-changing
inversion. -/
def flipSet (α : ℤ → ℤ) (S : Set ℤ) : Set ℤ :=
  { l | l ∈ S ∧ α l ≤ 0 ∧ 0 < α (l + 1) }

/-- Precomposing with `σ_S` creates at most one new sign-changing inversion,
provided `α` has at most one flip position in `S`.

This is the transport half of `lem-SciSimpleRefl`.  Note that no "rising"
hypothesis on `S` is needed: a pair that `σ_S` moves out of order is forced to
be `(l, l + 1)` with `l` a flip position, and those are counted by
`flipSet`. -/
theorem sci_comp_sigmaFun_le
    (α : ℤ → ℤ) (S : Set ℤ) (hS : Transpositions.NoConsecutive S)
    (hfin : (sciSet α).Finite) (hsub : (flipSet α S).Subsingleton) :
    sci (fun m => α (Transpositions.sigmaFun S m)) ≤ sci α + 1 := by
  classical
  set σ : ℤ → ℤ := Transpositions.sigmaFun S with hσdef
  set β : ℤ → ℤ := fun m => α (σ m) with hβdef
  -- Pointwise description of `σ`.
  have hmem : ∀ m, m ∈ S → σ m = m + 1 := by
    intro m hm; simp [hσdef, Transpositions.sigmaFun, hm]
  have hpred : ∀ m, m ∉ S → m - 1 ∈ S → σ m = m - 1 := by
    intro m hm hm'; simp [hσdef, Transpositions.sigmaFun, hm, hm']
  have hnone : ∀ m, m ∉ S → m - 1 ∉ S → σ m = m := by
    intro m hm hm'; simp [hσdef, Transpositions.sigmaFun, hm, hm']
  have htri : ∀ m, σ m = m + 1 ∨ σ m = m - 1 ∨ σ m = m := by
    intro m
    by_cases h : m ∈ S
    · exact Or.inl (hmem m h)
    · by_cases h' : m - 1 ∈ S
      · exact Or.inr (Or.inl (hpred m h h'))
      · exact Or.inr (Or.inr (hnone m h h'))
  have hsucc : ∀ m, σ m = m + 1 → m ∈ S := by
    intro m hm
    by_contra h
    by_cases h' : m - 1 ∈ S
    · have := hpred m h h'; omega
    · have := hnone m h h'; omega
  have hinj : Function.Injective σ := (Transpositions.sigma S hS).bijective.1
  -- Split `sciSet β` into the part `σ` keeps in order and the rest.
  set A : Set (ℤ × ℤ) := { p | p ∈ sciSet β ∧ σ p.1 < σ p.2 } with hAdef
  have hAsub : A ⊆ sciSet β := fun p hp => hp.1
  -- The ordered part injects into `sciSet α`.
  have hAcard : A.ncard ≤ sci α := by
    refine Set.ncard_le_ncard_of_injOn (fun p => (σ p.1, σ p.2)) ?_ ?_ hfin
    · rintro p ⟨⟨-, hp2, hp3⟩, hord⟩
      exact ⟨hord, hp2, hp3⟩
    · rintro p ⟨-, -⟩ q ⟨-, -⟩ hpq
      rw [Prod.mk.injEq] at hpq
      exact Prod.ext (hinj hpq.1) (hinj hpq.2)
  -- Everything else is a flip position, and there is at most one of those.
  have hrest : ∀ p ∈ sciSet β \ A, p.1 ∈ flipSet α S ∧ p.2 = p.1 + 1 := by
    rintro p ⟨⟨hlt, hpos, hnonpos⟩, hnot⟩
    have hord : ¬ σ p.1 < σ p.2 := fun h => hnot ⟨⟨hlt, hpos, hnonpos⟩, h⟩
    -- `β p.i` is literally `α (σ p.i)`.
    have hpos' : 0 < α (σ p.1) := hpos
    have hnonpos' : α (σ p.2) ≤ 0 := hnonpos
    have hne : σ p.1 ≠ σ p.2 := by
      intro h
      rw [h] at hpos'
      omega
    have hgt : σ p.2 < σ p.1 := by omega
    have h1 := htri p.1
    have h2 := htri p.2
    have hfst : σ p.1 = p.1 + 1 := by omega
    have hsnd : σ p.2 = p.2 - 1 := by omega
    have hadj : p.2 = p.1 + 1 := by omega
    refine ⟨⟨hsucc p.1 hfst, ?_, ?_⟩, hadj⟩
    · rw [hsnd, hadj] at hnonpos'
      simpa using hnonpos'
    · rw [hfst] at hpos'
      exact hpos'
  have hrestSub : (sciSet β \ A).Subsingleton := by
    intro p hp q hq
    obtain ⟨hp1, hp2⟩ := hrest p hp
    obtain ⟨hq1, hq2⟩ := hrest q hq
    have : p.1 = q.1 := hsub hp1 hq1
    exact Prod.ext this (by rw [hp2, hq2, this])
  have hrestCard : (sciSet β \ A).ncard ≤ 1 := by
    rcases hrestSub.eq_empty_or_singleton with h | ⟨x, hx⟩
    · simp [h]
    · simp [hx]
  calc sci β = (A ∪ (sciSet β \ A)).ncard := by
        rw [Set.union_sdiff_cancel hAsub]; rfl
    _ ≤ A.ncard + (sciSet β \ A).ncard := Set.ncard_union_le _ _
    _ ≤ sci α + 1 := by omega

/-- Paper source: `lem-SciSimpleRefl` (Lemma 6.12).

Composing with one `σ_S` whose support lies in a single residue class mod `k`
raises the sign-changing inversion count by at most one, as soon as
`sci α ≤ k - 2`.  The paper states this for `σ^k_n = σ_{n + kℤ}`; the only
property of that set the argument uses is that any two of its elements are
congruent mod `k`, so it is assumed directly.

Proof.  `Demazure.Transpositions.starSigma` (`eq:starSigma`, [PflDemProd, Thm
8.7]) replaces the Demazure product by the ordinary product with `σ_R`, `R` the
rising set.  `sci_comp_sigmaFun_le` then reduces the claim to `α` having at
most one flip position in `R`, and two flip positions congruent mod `k` would
give `k - 1` sign-changing inversions by
`sub_one_le_sci_of_two_signFlips`, contradicting `sci α ≤ k - 2`. -/
theorem sci_star_sigma_le
    (k : ℤ) (α : AspPerm) (S : Set ℤ) (hS : Transpositions.NoConsecutive S)
    (hcong : ∀ l₁ ∈ S, ∀ l₂ ∈ S, k ∣ (l₂ - l₁))
    (hfin : (sciSet α.func).Finite)
    (hsci : (sci α.func : ℤ) ≤ k - 2) :
    (sci (α ⋆ Transpositions.sigma S hS).func : ℤ) ≤ (sci α.func : ℤ) + 1 := by
  classical
  rw [Transpositions.starSigma α S hS]
  have hflip : (flipSet α.func (Transpositions.risingSet α S)).Subsingleton := by
    intro l₁ hl₁ l₂ hl₂
    by_contra hne
    -- Two distinct flip positions, congruent mod `k`, force `k - 1` inversions.
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := sub_one_le_sci_of_two_signFlips α.func k hfin hlt
        (hcong l₁ hl₁.1.1 l₂ hl₂.1.1) hl₁.2.2 hl₂.2.1
      omega
    · have := sub_one_le_sci_of_two_signFlips α.func k hfin hlt
        (hcong l₂ hl₂.1.1 l₁ hl₁.1.1) hl₂.2.2 hl₁.2.1
      omega
  -- A subset of a set with no consecutive pair again has none.
  have hR : Transpositions.NoConsecutive (Transpositions.risingSet α S) := by
    intro n hn hn'
    exact hS n hn.1 hn'.1
  have key := sci_comp_sigmaFun_le α.func (Transpositions.risingSet α S) hR hfin hflip
  -- `(α * σ_R).func` is literally `fun m => α (σ_R m)`; the proof argument of
  -- `sigma` is irrelevant, so this matches the rewritten goal.
  have hgoal : (sci (α * Transpositions.sigma (Transpositions.risingSet α S) hR).func : ℤ)
      ≤ (sci α.func : ℤ) + 1 := by exact_mod_cast key
  exact hgoal

/-! ## Inversion-free factors

The base case of the induction in `prop:sciInvStar`.  The paper argues that a
`k`-affine permutation with no `k`-inversions is a shift; in fact all that is
needed is that it has no inversions at all, which is both weaker and enough. -/

/-- A `k`-affine permutation with no `k`-inversions has no inversions at all:
any inversion translates into the fundamental range `[0, k)` by `k`-affinity. -/
theorem inv_set_eq_empty_of_kInversionCount_eq_zero
    (k : ℕ) (hk : 0 < k) (β : AspPerm)
    (hβ : IsKAffine k β.func) (hcount : kInversionCount k β.func = 0) :
    inv_set β.func = ∅ := by
  have hfin := kInversions_finite_of_isKAffine hk hβ
  have hempty : kInversions k β.func = ∅ := by
    rw [kInversionCount, Set.ncard_eq_zero hfin] at hcount
    exact hcount
  have hk' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hij, hji⟩
  set q : ℤ := -(p.1 / (k : ℤ)) with hq
  have hshift : p.1 + q * (k : ℤ) = p.1 % (k : ℤ) := by
    rw [hq, Int.emod_def]; ring
  have h1 := IsKAffine.iterate_int hβ p.1 q
  have h2 := IsKAffine.iterate_int hβ p.2 q
  have hmem : (⟨p.1 + q * (k : ℤ), p.2 + q * (k : ℤ)⟩ : ℤ × ℤ) ∈
      kInversions k β.func := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [h1, h2]; omega
    · rw [hshift]; exact Int.emod_nonneg p.1 (ne_of_gt hk')
    · rw [hshift]; exact Int.emod_lt_of_pos p.1 hk'
  rw [hempty] at hmem
  exact hmem

/-- Base case of `prop:sciInvStar`: a factor with no `k`-inversions cannot
raise the sign-changing inversion count.

With no inversions the product is reduced, so the Demazure product is the
ordinary one, and `β` carries `sciSet (α ∘ β)` injectively into `sciSet α`
because it preserves the order of every pair. -/
theorem sci_star_le_of_kInversionCount_eq_zero
    (k : ℕ) (hk : 0 < k) (α β : AspPerm)
    (hβ : IsKAffine k β.func) (hcount : kInversionCount k β.func = 0) :
    sci (α ⋆ β).func ≤ sci α.func := by
  have hinv := inv_set_eq_empty_of_kInversionCount_eq_zero k hk β hβ hcount
  -- `β` has no inversions, hence neither does `β⁻¹`.
  have hinvInv : inv_set (β⁻¹).func = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨u, hu⟩ := β.surjective x.2
    obtain ⟨v, hv⟩ := β.surjective x.1
    have := (β.inv_set_inverse u v).mpr (by rw [hu, hv]; exact hx)
    rw [hinv] at this
    exact this
  have hred : AspPerm.ReducedProduct α β := by
    unfold AspPerm.ReducedProduct
    rw [hinvInv]
    simp
  rw [(ReducedProducts.star_eq_mul_iff_reducedProduct α β).mpr hred]
  -- `β` preserves the order of every pair, so it maps `sciSet` into `sciSet`.
  have horder : ∀ a b : ℤ, a < b → β.func a < β.func b := by
    intro a b hab
    rcases lt_trichotomy (β.func a) (β.func b) with h | h | h
    · exact h
    · exact absurd (β.injective h) (by omega)
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp hinv ⟨a, b⟩ ⟨hab, h⟩)
        not_false
  refine Set.ncard_le_ncard_of_injOn (fun p => (β.func p.1, β.func p.2)) ?_ ?_
    (sciSet_finite α)
  · rintro p ⟨hlt, hpos, hnonpos⟩
    exact ⟨horder p.1 p.2 hlt, hpos, hnonpos⟩
  · rintro a - b - hab
    rw [Prod.mk.injEq] at hab
    exact Prod.ext (β.injective hab.1) (β.injective hab.2)

/-- The one fact about the affine Coxeter structure of `Aff~_k` that the
induction in `prop:sciInvStar` still consumes, isolated as a named input: a
`k`-affine permutation with a `k`-inversion has a simple descent `n`, and
factoring out the affine simple reflection `σ^k_n` on the left drops the
`k`-inversion count by exactly one, the product being reduced.

The local module `AffineReduction.lean` supplies this structure by reducing to
the ordinary adjacent-descent theorem and counting normalized periodic
inversion representatives.  The base case above needs no such input. -/
structure AffineReductionData (k : ℕ) : Prop where
  /-- A `k`-inversion yields a reduced factorization by one affine simple
  reflection, dropping the count by one. -/
  reduce : ∀ β : AspPerm, IsKAffine k β.func → 0 < kInversionCount k β.func →
    ∃ (S : Set ℤ) (hS : Transpositions.NoConsecutive S) (β' : AspPerm),
      (∀ l₁ ∈ S, ∀ l₂ ∈ S, (k : ℤ) ∣ (l₂ - l₁)) ∧
      β = Transpositions.sigma S hS ⋆ β' ∧
      IsKAffine k β'.func ∧
      kInversionCount k β'.func + 1 = kInversionCount k β.func

/-- Paper source: `prop:sciInvStar` (Proposition 6.13).

As long as the budget `k` strictly exceeds the two statistics combined, the
Demazure product does not overshoot their sum.  This is the estimate the whole
chain theorem rests on.

The induction is the paper's, on `inv_k β`: the base case is the `shift`
clause, and the inductive step splits off one affine simple reflection with
`reduce`, bounds its effect by `sci_star_sigma_le` (Lemma 6.12), and reapplies
the hypothesis to the smaller factor.  The budget survives the step because
6.12 costs one and the count drops by one. -/
theorem sci_star_le_of_affineReductionData
    (k : ℕ) (hdata : AffineReductionData k) (α β : AspPerm)
    (hβ : IsKAffine k β.func)
    (hbudget : (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) < (k : ℤ)) :
    (sci (α ⋆ β).func : ℤ) ≤
      (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) := by
  suffices H : ∀ n : ℕ, ∀ α β : AspPerm, IsKAffine k β.func →
      kInversionCount k β.func = n → (sci α.func : ℤ) + (n : ℤ) < (k : ℤ) →
      (sci (α ⋆ β).func : ℤ) ≤ (sci α.func : ℤ) + (n : ℤ) by
    exact H _ α β hβ rfl hbudget
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β hβ hcount hbud
    rcases Nat.eq_zero_or_pos n with hzero | hpos
    · subst hzero
      have hkpos : 0 < k := by
        have : (0 : ℤ) ≤ (sci α.func : ℤ) := Int.natCast_nonneg _
        omega
      have := sci_star_le_of_kInversionCount_eq_zero k hkpos α β hβ (by omega)
      omega
    · obtain ⟨S, hS, β', hcong, hfact, hβ', hcount'⟩ :=
        hdata.reduce β hβ (by omega)
      have hassoc : α ⋆ β = (α ⋆ Transpositions.sigma S hS) ⋆ β' := by
        rw [hfact]
        exact (AspPerm.star_assoc α _ β').symm
      have h12 : (sci (α ⋆ Transpositions.sigma S hS).func : ℤ) ≤
          (sci α.func : ℤ) + 1 :=
        sci_star_sigma_le (k : ℤ) α S hS hcong (sciSet_finite α) (by omega)
      have hrec := ih (kInversionCount k β'.func) (by omega)
        (α ⋆ Transpositions.sigma S hS) β' hβ' rfl (by omega)
      rw [hassoc]
      omega

end Bananas
