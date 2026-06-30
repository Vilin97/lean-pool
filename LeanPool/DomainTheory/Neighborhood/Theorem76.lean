/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem75
import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Theorem 7.6 (Scott 1981, PRG-19, §7) — `fix : (𝒟 → 𝒟) → 𝒟` is computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19,
Lecture VII.

> **Theorem 7.6.** For any effectively given domain `𝒟`, the combinator `fix : (𝒟
→ 𝒟) → 𝒟` is
> computable.

Scott's proof reads off the neighbourhood relation of `fix` from the fixed-point
construction of
Theorem 4.1/4.2: writing `𝒟 = {Xₙ}` effectively given,

  `⋂_{i<q} [X_{nᵢ}, X_{mᵢ}] fix X_ℓ` iff for some finite sequence `Δ = X_{k₀}, …,
  X_{k_p} = X_ℓ`
  we have, for each `j < p`, `⋂{ X_{mᵢ} ∣ X_{kⱼ} ⊆ X_{nᵢ} } ⊆ X_{kⱼ₊₁}`.

Inside "for some finite sequence" all the checks are *decidable* (by the effective
presentation), and
the existential quantification of a decidable predicate is recursively enumerable.
(Since there is no
bound on the length of the sequence, this is genuinely r.e. and not generally
recursive.)

## Strategy (choice-free)

The function-space neighbourhood `F = Xenum c` (Theorem 7.5) is a finite
intersection
`⋂[X_{nᵢ}, X_{mᵢ}]`; its *least map* is `ĝ = toApproxMap (↑F)`, and `(fix V).rel F
(X_ℓ)` unfolds via
`rel_iff_mem_principal` + `fixMap_toElementMap` + `mem_fixElement` to

  `∃ p, (ĝᵖ).rel Δ (X_ℓ)`.

The one-step relation `ĝ.rel (X_a) (X_b) ↔ F ⊆ [X_a, X_b]` is exactly Scott's
`⋂{X_{mᵢ} ∣ X_a ⊆ X_{nᵢ}} ⊆ X_b`, and — crucially — it is **recursively
decidable**, because
`[X_a, X_b] = Xenum (codePair a b)` (a one-entry, always-consistent function-space
neighbourhood) so
the test is the decidable function-space inclusion `Xenum c ⊆ Xenum (codePair a
b)`
(`funPresentation.incl_computable`, Theorem 7.5).

We model a finite `ĝ`-chain by a **list of indices** (using `surj` to name each
intermediate
neighbourhood) and prove the characterisation `(fix V).rel (Xenum c) (X_ℓ) ↔ ∃
full, gStepsOK …`
(soundness/completeness over the list, choice-free). The existential over the list
is then realised
as the r.e. `∃ i, q (pair i n)`, where `q` decodes `i` to the chain, runs a single
primitive-recursive
`foldCode` (`fixChainChar`) threading the previous index and a `{0,1}` consistency
flag, and checks
the flag together with the final inclusion `X_{last} ⊆ X_ℓ`. Everything audits
`⊆ {propext, Quot.sound}`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-! ### A finite `g`-chain over presentation indices.

`gStepsOK g P a full` says: starting from the index `a`, the consecutive `g`-steps
along the index
list `full` all hold, and `gLastOf a full` is the final index reached. -/

/-- The last index of the chain `a, full₀, full₁, …`. -/
def gLastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, (b :: rest) => gLastOf b rest

/-- The consecutive `g`-steps `g.rel (X_a) (X_{full₀})`, `g.rel (X_{full₀})
(X_{full₁})`, … all
hold. -/
def gStepsOK (g : ApproximableMap V V) (P : ComputablePresentation V) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => g.rel (P.X a) (P.X b) ∧ gStepsOK g P b rest

/-- **Soundness of a chain.** A valid `g`-chain from `a` realises the iterate
relation
`(gᵏ).rel (X_a) (X_{last})` with `k` the chain length. -/
theorem gStepsOK_sound (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (full : List ℕ) (a : ℕ), gStepsOK g P a full →
      (g.iterMap full.length).rel (P.X a) (P.X (gLastOf a full)) := by
  intro full
  induction full with
  | nil =>
    intro a _
    change (g.iterMap ([] : List ℕ).length).rel (P.X a) (P.X a)
    rw [List.length_nil, iterMap_zero]
    exact idMap_rel.mpr ⟨P.mem_X a, P.mem_X a, subset_rfl⟩
  | cons b rest ih =>
    intro a hsteps
    obtain ⟨h1, hrest⟩ := hsteps
    have hcomm : g.iterMap (rest.length + 1) = (g.iterMap rest.length).comp g := by
      rw [iterMap_succ]; exact iter_comm g rest.length
    change (g.iterMap (b :: rest).length).rel (P.X a) (P.X (gLastOf b rest))
    rw [List.length_cons, hcomm, comp_rel]
    exact ⟨P.X b, h1, ih b hrest⟩

/-- **Completeness of a chain.** If `(gⁿ).rel (X_a) (X_ℓ)`, then there is a valid
`g`-chain from `a`
whose final neighbourhood is contained in `X_ℓ`. (The intermediate neighbourhoods
are named via
`surj`; the relaxed final condition `X_{last} ⊆ X_ℓ` handles the `n = 0` base.) -/
theorem gStepsOK_complete (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (n a ℓ : ℕ), (g.iterMap n).rel (P.X a) (P.X ℓ) →
      ∃ full, gStepsOK g P a full ∧ P.X (gLastOf a full) ⊆ P.X ℓ := by
  intro n
  induction n with
  | zero =>
    intro a ℓ h
    rw [iterMap_zero, idMap_rel] at h
    exact ⟨[], trivial, h.2.2⟩
  | succ n ih =>
    intro a ℓ h
    have hcomm : g.iterMap (n + 1) = (g.iterMap n).comp g := by
      rw [iterMap_succ]; exact iter_comm g n
    rw [hcomm, comp_rel] at h
    obtain ⟨Y, h1, h2⟩ := h
    obtain ⟨k, hk⟩ := P.surj (g.rel_cod h1)
    rw [← hk] at h1 h2
    obtain ⟨full', hs', hl'⟩ := ih k ℓ h2
    exact ⟨k :: full', ⟨h1, hs'⟩, hl'⟩

/-- **Chain characterisation of `g`'s least fixed point.** A neighbourhood `X_ℓ`
is in `fix(g)`
iff a
valid `g`-chain (from a master index `a₀` with `X_{a₀} = Δ`) reaches a final
neighbourhood inside
`X_ℓ`. -/
theorem fixElement_mem_iff_chain (g : ApproximableMap V V) (P : ComputablePresentation V)
    (a0 : ℕ) (ha0 : P.X a0 = V.master) (ℓ : ℕ) :
    g.fixElement.mem (P.X ℓ) ↔
      ∃ full, gStepsOK g P a0 full ∧ P.X (gLastOf a0 full) ⊆ P.X ℓ := by
  rw [mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩
    rw [← ha0] at hn
    exact gStepsOK_complete g P n a0 ℓ hn
  · rintro ⟨full, hsteps, hlast⟩
    refine ⟨full.length, ?_⟩
    have hsound := gStepsOK_sound g P full a0 hsteps
    have hmono := (g.iterMap full.length).mono hsound subset_rfl hlast (P.mem_X a0) (P.mem_X ℓ)
    rwa [ha0] at hmono

/-! ### The least map of `Xenum c` and its decidable one-step relation. -/

/-- The one-entry function-space code: `Xenum (codePair a b) = [X_a, X_b]`. -/
def codePair (a b : ℕ) : ℕ := Nat.pair (Nat.pair a b) 0 + 1

variable (P : ComputablePresentation V)

/-- `Xenum (codePair a b) = [X_a, X_b]` (a one-entry, always-consistent
function-space
neighbourhood); a thin wrapper around `Xenum_singleton`. -/
theorem Xenum_codePair (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (a b : ℕ) :
    Xenum P P gN (codePair a b) = step (P.X a) (P.X b) :=
  Xenum_singleton P P gN hgN a b

/-- The least map `ĝ` of the function-space neighbourhood `Xenum c` relates `X_a`
to `X_b` exactly
when `Xenum c ⊆ [X_a, X_b]` (Scott's `⋂{X_{mᵢ} ∣ X_a ⊆ X_{nᵢ}} ⊆ X_b`). -/
theorem leastMap_Xenum_rel (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c a b : ℕ) :
    (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))).rel (P.X a) (P.X b)
      ↔ Xenum P P gN c ⊆ step (P.X a) (P.X b) := by
  rw [toApproxMap_rel, mem_principal]
  exact ⟨fun h => h.2, fun h => ⟨step_mem (P.mem_X a) (P.mem_X b), h⟩⟩

/-- **The `fix` neighbourhood relation, chain form.** `(fix V).rel (Xenum c)
(X_ℓ)` holds iff
there is
a valid least-map chain from the master index reaching a neighbourhood inside
`X_ℓ`. This is Scott's
"`⋂[X_{nᵢ}, X_{mᵢ}] fix X_ℓ` iff for some finite sequence …". -/
theorem fixMap_rel_iff (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c ℓ : ℕ) :
    (fixMap V).rel (Xenum P P gN c) (P.X ℓ) ↔
      ∃ full : List ℕ,
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c)))
          P P.masterIdx full
        ∧ P.X (gLastOf P.masterIdx full) ⊆ P.X ℓ := by
  rw [(fixMap V).rel_iff_mem_principal (Xenum_mem P P gN hgN c), fixMap_toElementMap]
  exact fixElement_mem_iff_chain _ P P.masterIdx P.masterIdx_spec ℓ

/-! ### The decidable chain predicate and its primitive-recursive `foldCode`. -/

/-- The decidable mirror of `gStepsOK`, phrased with the function-space inclusion
char `fincl`. -/
def chainDec (fincl : ℕ → ℕ) (c : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => fincl (Nat.pair c (codePair a b)) = 1 ∧ chainDec fincl c b rest

/-- `chainDec` is equivalent to `gStepsOK` of the least map, via the inclusion
char's spec and
`Xenum (codePair a b) = [X_a, X_b]`. -/
theorem chainDec_iff_gStepsOK (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (fincl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2) (c : ℕ) :
    ∀ (full : List ℕ) (a : ℕ),
      chainDec fincl c a full ↔
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))) P a full := by
  intro full
  induction full with
  | nil => intro a; exact Iff.rfl
  | cons b rest ih =>
    intro a
    constructor
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mp hrest⟩
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b] at hstep
      exact (leastMap_Xenum_rel P gN hgN c a b).mpr hstep
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mpr hrest⟩
      have hsub : Xenum P P gN c ⊆ step (P.X a) (P.X b) :=
        (leastMap_Xenum_rel P gN hgN c a b).mp hstep
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b]
      exact hsub

/-- One packed `foldCode` step: state `pair acc params` with `acc = pair prev
flag`, current element
`x`. Updates the flag with the one-step consistency test and advances `prev` to
`x`. -/
def fixStp (fincl : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0)

/-- The pure left-fold step corresponding to `fixStp` (parameter `c`, accumulator
`acc = pair prev
flag`, current element `x`). -/
def fixPStep (fincl : ℕ → ℕ) (c acc x : ℕ) : ℕ :=
  Nat.pair x (selectFn acc.unpair.2 (isOne (fincl (Nat.pair c (codePair acc.unpair.1 x)))) 0)

theorem fixStp_eq (fincl : ℕ → ℕ) (c acc x : ℕ) :
    fixStp fincl (Nat.pair x (Nat.pair acc c)) = fixPStep fincl c acc x := by
  unfold fixStp fixPStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_fixStp (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fixStp fincl) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hprev : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hcode : Nat.Primrec (fun w : ℕ => codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hprev.pair hx).pair (Nat.Primrec.const 0))
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2
      (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)) := hc.pair hcode
  have hsel : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp (hfinclp.comp hinner)) (Nat.Primrec.const 0)
  exact (hx.pair hsel).of_eq (fun _ => rfl)

/-- The chain `foldCode`: starts from `pair masterIdx 1`, threads the parameter
`c`, over the list
coded by `i`. Returns `pair lastIdx flag`. -/
def fixChainChar (fincl : ℕ → ℕ) (c i : ℕ) : ℕ :=
  foldCode (fixStp fincl) c (Nat.pair P.masterIdx 1) i

theorem fixChainChar_eq (fincl : ℕ → ℕ) (c i : ℕ) :
    fixChainChar P fincl c i
      = List.foldl (fixPStep fincl c) (Nat.pair P.masterIdx 1) (decodeList i) := by
  unfold fixChainChar
  rw [foldCode_eq']
  have hstep : (fun acc x => fixStp fincl (Nat.pair x (Nat.pair acc c))) = fixPStep fincl c := by
    funext acc x; exact fixStp_eq fincl c acc x
  rw [hstep]

theorem primrec_fixChainChar (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fun t => fixChainChar P fincl t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_fixStp fincl hfinclp) Nat.Primrec.left
    (Nat.Primrec.const (Nat.pair P.masterIdx 1)) Nat.Primrec.right).of_eq (fun _ => rfl)

/-- The `foldCode` tracks the last index reached. -/
theorem fixPStep_foldl_fst (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ),
      (List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.1 = gLastOf prev full := by
  intro full
  induction full with
  | nil =>
    intro prev fl
    change (Nat.pair prev fl).unpair.1 = prev
    exact unpair_pair_fst prev fl
  | cons b rest ih =>
    intro prev fl
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep, ih b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0)]
    rfl

/-- The `foldCode` flag is `1` iff the start flag is `1` and the whole chain is
consistent. -/
theorem fixPStep_foldl_snd (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ), fl ≤ 1 →
      ((List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.2 = 1 ↔
        fl = 1 ∧ chainDec fincl c prev full) := by
  intro full
  induction full with
  | nil =>
    intro prev fl _
    change (Nat.pair prev fl).unpair.2 = 1 ↔ fl = 1 ∧ chainDec fincl c prev []
    rw [unpair_pair_snd]
    simp [chainDec]
  | cons b rest ih =>
    intro prev fl _
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set nf := selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0 with hnf
    have hnfle : nf ≤ 1 := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; exact Nat.zero_le 1
      · rw [selectFn_one]; exact isOne_le_one _
    rw [ih b nf hnfle]
    have hnf1 : nf = 1 ↔ (fl = 1 ∧ fincl (Nat.pair c (codePair prev b)) = 1) := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; simp
      · rw [selectFn_one, isOne_eq_one_iff]; simp
    rw [hnf1]
    constructor
    · rintro ⟨⟨hfl1, hfincl1⟩, hrest⟩; exact ⟨hfl1, hfincl1, hrest⟩
    · rintro ⟨hfl1, hfincl1, hrest⟩; exact ⟨⟨hfl1, hfincl1⟩, hrest⟩

/-- Read-off of the `foldCode`: its `.1` is the last index of `decodeList i`, and
its `.2 = 1` iff
the decoded chain is consistent. -/
theorem fixChainChar_spec (fincl : ℕ → ℕ) (c i : ℕ) :
    (fixChainChar P fincl c i).unpair.1 = gLastOf P.masterIdx (decodeList i)
  ∧ ((fixChainChar P fincl c i).unpair.2 = 1 ↔ chainDec fincl c P.masterIdx (decodeList i)) := by
  rw [fixChainChar_eq]
  refine ⟨fixPStep_foldl_fst fincl c (decodeList i) P.masterIdx 1, ?_⟩
  rw [fixPStep_foldl_snd fincl c (decodeList i) P.masterIdx 1 (le_refl 1)]
  simp

/-- **Theorem 7.6 (Scott 1981, PRG-19) — `fix` is computable (choice-free).** For
any effectively
given domain `𝒟` (here a computable presentation `P` of `V`, together with the
function-space
consistency/inclusion/equality chars of Theorem 7.5), the combinator `fix : (𝒟 →
𝒟) → 𝒟` is
computable: its neighbourhood relation is the recursively-enumerable existential
`∃ chain` over the
decidable least-map step relation. -/
theorem fixMap_isComputable
    (gN incl eq : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    IsComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp) P
      (fixMap V) := by
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq
      heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  change REPred₂ (fun c ℓ => (fixMap V).rel (Xenum P P gN c) (P.X ℓ))
  refine ⟨fun w =>
      (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2 = 1
      ∧ incl (Nat.pair (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1
          w.unpair.2.unpair.2) = 1,
    ?_, ?_⟩
  · -- the search predicate is recursively decidable.
    have hcc : Nat.Primrec (fun w => fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1) :=
      ((primrec_fixChainChar P fincl hfinclp).comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq (fun w => by
          simp only [unpair_pair_fst, unpair_pair_snd])
    have hA : Nat.Primrec (fun w =>
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2) :=
      Nat.Primrec.right.comp hcc
    have hB : Nat.Primrec (fun w => incl (Nat.pair
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1 w.unpair.2.unpair.2)) :=
      hinclp.comp ((Nat.Primrec.left.comp hcc).pair (Nat.Primrec.right.comp Nat.Primrec.right))
    exact (RecDecidable.natEq hA (Nat.Primrec.const 1)).and
      (RecDecidable.natEq hB (Nat.Primrec.const 1))
  · -- the search predicate enumerates `fix`'s neighbourhood relation.
    intro t
    change (fixMap V).rel (Xenum P P gN t.unpair.1) (P.X t.unpair.2) ↔ _
    rw [fixMap_rel_iff P gN hgN t.unpair.1 t.unpair.2]
    constructor
    · rintro ⟨full, hsteps, hlast⟩
      refine ⟨encodeList full, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      have hdec : decodeList (encodeList full) = full := decodeList_encodeList full
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 (encodeList full)
      rw [hdec] at hfst hsnd
      refine ⟨hsnd.mpr
        ((chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 full P.masterIdx).mpr hsteps), ?_⟩
      rw [hfst, hincl, unpair_pair_fst, unpair_pair_snd]
      exact hlast
    · rintro ⟨i, hi⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 i
      refine ⟨decodeList i, ?_, ?_⟩
      · exact (chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 (decodeList i)
          P.masterIdx).mp (hsnd.mp hi1)
      · rw [← hfst]
        have hi2' := (hincl (Nat.pair (fixChainChar P fincl t.unpair.1 i).unpair.1
          t.unpair.2)).mp hi2
        rwa [unpair_pair_fst, unpair_pair_snd] at hi2'

end Domain.Neighborhood
