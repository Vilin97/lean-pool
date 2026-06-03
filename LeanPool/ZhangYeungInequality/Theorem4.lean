/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.EntropyRegion
import LeanPool.ZhangYeungInequality.Theorem3

/-!
# Theorem 4: Shannon incompleteness at `n = 4`

Theorem 4 of [@zhangyeung1998, §II, eq. 26] is the scientific payoff of the Zhang-Yeung
inequality:
the Shannon outer bound `Γ_n` strictly contains the set of entropy functions of `n`
discrete random
variables for `n ≥ 4`. At `n = 4` the witness is explicit (paper lines 368-377): a
concrete
rational-valued set function on the 16 subsets of `Fin 4` that satisfies the three
Shannon-cone
axioms (paper eq. 11) but violates the Zhang-Yeung inequality (paper eq. 21) at the
canonical
labeling.

The milestone lands four ingredients:

- **Parts (a), (b)** -- pure set-function arithmetic. The witness `FWitnessℚ : Finset
  (Fin 4) →
  ℚ` satisfies `shannonCone FWitness` and fails `zhangYeungHolds FWitness`. Both are
  decidable
  finite checks.
- **Part (c), the bridge** -- for any four discrete random variables `X : ∀ i : Fin 4, Ω
  → S i`,
  possibly with different finite codomains `S : Fin 4 → Type u`, their entropy function
  `entropyFn
  X μ : Finset (Fin 4) → ℝ` satisfies `zhangYeungHolds` at every permutation of the four
  coordinates. This is a direct restatement of M3's `ZhangYeung.zhangYeung` in the
  set-function
  language the closure proof consumes.
- **Part (d), the exact theorem** -- the headline separation. The public `theorem4` is
  now the
  paper's exact `n = 4` closure statement `∃ F ∈ Γ_4, F ∉ closure(Γ_4^*)`, with
  `theorem4_ge_four`
  lifting it to all `n ≥ 4`.

## Main definitions

- `ZhangYeung.IF`, `ZhangYeung.condIF`, `ZhangYeung.deltaF`: the set-function
  information-theoretic calculus (unconditional mutual info, conditional mutual info,
  and the
  Zhang-Yeung delta at the set-function level).
- `ZhangYeung.shannonCone`: the Shannon outer bound `Γ_4` (paper eq. 11) stated as a
  predicate on
  `Finset (Fin 4) → ℝ`.
- `ZhangYeung.shannonRegionN`, `ZhangYeung.entropyRegionN`,
  `ZhangYeung.almostEntropicRegionN`:
  the set-level Shannon, entropic, and almost-entropic regions on `Finset (Fin n) → ℝ`.
- `ZhangYeung.zhangYeungAt`: the Zhang-Yeung inequality (paper eq. 21) at a specific
  4-tuple
  labeling.
- `ZhangYeung.zhangYeungHolds`: the Zhang-Yeung cone `tildeΓ_4` (paper eq. 25),
  expressed as
  `zhangYeungAt` at every permutation of `Fin 4`.
- `ZhangYeung.FWitnessℚ`: the paper's `n = 4` counterexample, as a `ℚ`-valued set
  function with
  `a = 1`.
- `ZhangYeung.FWitness`: the `ℝ`-cast of `FWitnessℚ`.
- `ZhangYeung.entropyFn`, `ZhangYeung.entropyFnN`: the four-variable and generic
  set-function
  views of joint entropy.

## Main statements

- `ZhangYeung.shannonCone_of_witness` -- Part (a): `FWitness` lies in the Shannon cone.
- `ZhangYeung.not_zhangYeungHolds_witness` -- Part (b): `FWitness` fails the
  Zhang-Yeung
  inequality at the canonical permutation.
- `ZhangYeung.shannon_incomplete` -- intermediate form: there exists a set function in
  `Γ_4` that
  is not in `tildeΓ_4`.
- `ZhangYeung.zhangYeungAt_entropyFn`, `ZhangYeung.zhangYeungHolds_of_entropy` -- Part
  (c), the
  bridge: every entropy function of four discrete random variables lies in `tildeΓ_4`.
- `ZhangYeung.theorem4_finite` -- the finite auxiliary separation, excluding `FWitness`
  from the
  literal entropy region.
- `ZhangYeung.theorem4` -- the exact paper-level `n = 4` statement `∃ F ∈ Γ_4, F ∉
  closure(Γ_4^*)`.
- `ZhangYeung.theorem4_ge_four` -- the exact paper-level `n ≥ 4` statement `∃ F ∈ Γ_n, F
  ∉
  closure(Γ_n^*)`.
- `ZhangYeung.theorem4_seqClosure` -- the sequence-level surrogate over `tildeΓ_4`
  retained as a
  supporting lemma.
- `ZhangYeung.shannon_incomplete_ge_four` -- the stronger cone-level corollary `∃ F ∈
  Γ_n, F ∉
  tildeΓ_n`.

## Implementation notes

The witness is defined first over `ℚ` so that Parts (a) and (b) reduce to finite
rational
arithmetic before casting to `ℝ` at the witness boundary. `FWitness` is a plain
pointwise cast
`fun S => (FWitnessℚ S : ℝ)`; the companion lemma `FWitness_eq_cast` trivializes
downstream
`push_cast`/`norm_cast` work. Fixing `a = 1` collapses the paper's parametric family
into a single
`ℚ`-valued function without losing any content: `theorem4` and `theorem4_ge_four` are
existential
separations, so the homogeneity the paper uses `a` to exhibit is vacuous at that level.

The Zhang-Yeung cone is quantified over `Equiv.Perm (Fin 4)` to match paper eq. (25)
literally; the
specific violation uses the permutation `Equiv.swap 0 2 * Equiv.swap 1 3` sending `(0,
1, 2, 3) ↦
(2, 3, 0, 1)`, which instantiates `zhangYeungAt F (σ 0) (σ 1) (σ 2) (σ 3)` as
`zhangYeungAt F 2 3 0
1` -- exactly the labeling the paper evaluates on lines 378-388. Permutation evaluation
`(σ 0, σ 1,
σ 2, σ 3)` is discharged by `decide` once and reused.

The bridge binds the four codomains as a heterogeneous family `S : Fin 4 → Type u` at a
single
universe `u` and consumes M3's `ZhangYeung.zhangYeung` directly. Each per-subset bridge
lemma
(`entropyFn_empty`, `entropyFn_singleton`, `entropyFn_pair`, `entropyFn_triple`,
`entropyFn_quad`)
transports across an explicit `Equiv` between a `Finset`-indexed subtype of `Fin 4` and
a standard
`Fin k`, invoking PFR's `entropy_comp_of_injective` to move `H[·; μ]` under that
transport. The
exact theorem then packages this bridge through `ZhangYeung/EntropyRegion.lean`:
`closure (Γ_4^*)`
sits inside the closed Zhang-Yeung region, while `FWitness` sits outside it.

## References

* [@zhangyeung1998, §II, Theorem 4 and its proof, lines 358-388] -- statement, witness
  construction, and Zhang-Yeung violation verification.
* [@zhangyeung1998, §II, definition of `tildeΓ_4` at eq. (25), lines 339-355] -- the
  Zhang-Yeung
  cone.
* [@zhangyeung1998, §II, Shannon cone `Γ_n` at eq. (11)] -- the three Shannon-cone
  axioms.

## Tags

Shannon entropy, non-Shannon information inequality, Zhang-Yeung, Shannon
incompleteness, entropic
region
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR

universe u

/-! ### Set-function information-theoretic calculus

Paper eqs. (3)-(5), restated at the set-function level on `Finset (Fin 4) → ℝ`. These
mirror the
random-variable-level information measures PFR exposes (`I[X : Y]`, `I[X : Y | Z]`) but
do not
require any measure-theoretic context. -/

/--
Set-function mutual information: `IF(α; β) = F α + F β - F (α ∪ β)`. When `F` is the
entropy
function of a discrete random-variable family (with `F ∅ = 0`), this coincides with
`I[X_α : X_β]`.
-/
def IF (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ :=
  F α + F β - F (α ∪ β)

/--
Set-function conditional mutual information: `condIF(α; β | γ) = F (α ∪ γ) + F (β ∪ γ)
- F (α ∪ β
∪ γ) - F γ`. When `F` is the entropy function of a discrete random-variable family, this
coincides
with `I[X_α : X_β | X_γ]`.
-/
def condIF (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/--
Set-function Zhang-Yeung delta at a 4-tuple of coordinates: `deltaF(i, j | k, l) =
IF({i}; {j}) -
condIF({i}; {j} | {k}) - condIF({i}; {j} | {l})`. Mirrors `ZhangYeung.delta` at the
set-function
level.
-/
def deltaF (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ :=
  IF F {i} {j} - condIF F {i} {j} {k} - condIF F {i} {j} {l}

/-! ### Shannon and Zhang-Yeung cone predicates -/

/--
The Shannon outer bound `Γ_4` from [@zhangyeung1998, eq. 11]: a set function lies in
`Γ_4` iff it
vanishes on the empty set, is monotone under subset inclusion, and is submodular.
-/
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)

/-- The Zhang-Yeung inequality at a specific 4-tuple labeling (paper eq. 21):

  `deltaF F i j k l ≤ (1/2) * (IF F {k} {l} + IF F {k} ({i} ∪ {j}) + condIF F {i}
  {j} {k} -
  condIF F {i} {j} {l})`.

This is the set-function-level restatement of `ZhangYeung.zhangYeung`. -/
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop :=
  deltaF F i j k l ≤ (1 / 2) * (IF F {k} {l} + IF F {k} ({i} ∪ {j})
    + condIF F {i} {j} {k} - condIF F {i} {j} {l})

/--
The Zhang-Yeung cone `tildeΓ_4` from [@zhangyeung1998, eq. 25]: a set function `F` lies
in
`tildeΓ_4` iff `zhangYeungAt F (π 0) (π 1) (π 2) (π 3)` holds at every permutation `π`
of `Fin 4`.
-/
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3)

/-! ### The paper's `n = 4` counterexample witness

The witness `FWitnessℚ` is the `a = 1` specialization of the parametric witness on
paper lines
368-377: zero on the empty set, `2` on singletons, `4` on `{0, 1}`, `3` on the other
five pairs,
and `4` on all triples and the 4-set. It is implemented as a cascade of `if-then-else`
on
cardinality, with a special case for `{0, 1}`, so the finite witness checks stay
explicit and
reducible on all 16 subsets of `Fin 4`. -/

/-- The `ℚ`-valued Zhang-Yeung counterexample witness (paper lines 368-377, specialized
to `a =
1`):

  `FWitnessℚ ∅ = 0`, `FWitnessℚ {i} = 2`, `FWitnessℚ {0, 1} = 4`, `FWitnessℚ {i,
  j} = 3`
  for other pairs, `FWitnessℚ S = 4` for triples and the 4-set.

Living over `ℚ` so the witness arithmetic stays exact before the final cast to `ℝ`.
-/
def FWitnessℚ : Finset (Fin 4) → ℚ := fun S =>
  if S.card = 0 then 0
  else if S.card = 1 then 2
  else if S = ({0, 1} : Finset (Fin 4)) then 4
  else if S.card = 2 then 3
  else 4

/--
The `ℝ`-cast of `FWitnessℚ`, used in the main statements `shannonCone_of_witness`,
`not_zhangYeungHolds_witness`, `shannon_incomplete`, `theorem4_finite`, `theorem4`, and
`theorem4_ge_four`.
-/
noncomputable def FWitness : Finset (Fin 4) → ℝ := fun S => (FWitnessℚ S : ℝ)

/--
Definitional-shape lemma: `FWitness` is the pointwise `ℚ → ℝ` cast of `FWitnessℚ`.
Used to push
`FWitness` into `FWitnessℚ`-shaped goals before closing them over `ℚ`.
-/
lemma FWitness_eq_cast (S : Finset (Fin 4)) :
    FWitness S = (FWitnessℚ S : ℝ) := rfl

private def pair01 : Finset (Fin 4) := {0, 1}

private def nonemptyBonus (S : Finset (Fin 4)) : ℚ := if S.Nonempty then 1 else 0

private def fullBonus (S : Finset (Fin 4)) : ℚ := if S = Finset.univ then 1 else 0

private def pairBonus (S : Finset (Fin 4)) : ℚ := if S = pair01 then 1 else 0

private def baseWitness (S : Finset (Fin 4)) : ℚ := (S.card : ℚ) + nonemptyBonus S - fullBonus S

private lemma fullBonus_nonneg (S : Finset (Fin 4)) : 0 ≤ fullBonus S := by
  by_cases h : S = Finset.univ <;> simp [fullBonus, h]

private lemma pairBonus_nonneg (S : Finset (Fin 4)) : 0 ≤ pairBonus S := by
  by_cases h : S = pair01 <;> simp [pairBonus, h]

private lemma FWitnessℚ_eq_base_add_pair :
    ∀ S : Finset (Fin 4), FWitnessℚ S = baseWitness S + pairBonus S := by
  intro S
  by_cases h0 : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp h0
    subst hEmpty
    have hFull : (∅ : Finset (Fin 4)) ≠ Finset.univ := by decide
    have hPairLit : (∅ : Finset (Fin 4)) ≠ ({0, 1} : Finset (Fin 4)) := by decide
    simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, pair01, hFull, hPairLit]
  · by_cases h1 : S.card = 1
    · have hPair : S ≠ pair01 := by
        intro h
        rw [h, pair01] at h1
        norm_num at h1
      have hFull : S ≠ Finset.univ := by
        intro h
        rw [h] at h1
        norm_num at h1
      have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h1, hPair, hFull,
        hNonempty]
      norm_num
    · by_cases hPair : S = pair01
      · subst hPair
        have hFullLit : ({0, 1} : Finset (Fin 4)) ≠ Finset.univ := by decide
        simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, pair01, hFullLit]
        norm_num
      · by_cases h2 : S.card = 2
        · have hFull : S ≠ Finset.univ := by
            intro h
            rw [h] at h2
            norm_num at h2
          have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
          have hPairLit : S ≠ ({0, 1} : Finset (Fin 4)) := by simpa [pair01] using hPair
          simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h2, hPair,
            hPairLit, hFull, hNonempty]
          norm_num
        · have hCardLe : S.card ≤ 4 := by simpa using Finset.card_le_univ S
          have h34 : S.card = 3 ∨ S.card = 4 := by omega
          cases h34 with
          | inl h3 =>
              have hFull : S ≠ Finset.univ := by
                intro h
                rw [h] at h3
                norm_num at h3
              have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
              have hPairLit : S ≠ ({0, 1} : Finset (Fin 4)) := by simpa [pair01] using hPair
              simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h3, hPair,
                hPairLit, hFull, hNonempty]
              norm_num
          | inr h4 =>
              have hFull : S = Finset.univ := by
                exact S.card_eq_iff_eq_univ.mp (by simpa using h4)
              have hPairUniv : (Finset.univ : Finset (Fin 4)) ≠ pair01 := by decide
              have hPairUnivLit : (Finset.univ : Finset (Fin 4)) ≠ ({0,
                1} : Finset (Fin 4)) := by decide
              have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
              simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, hFull,
                hPairUniv, hPairUnivLit]

private lemma card_modular (α β : Finset (Fin 4)) :
    ((α ∪ β).card : ℚ) + (α ∩ β).card = (α.card : ℚ) + β.card := by
  exact_mod_cast Finset.card_union_add_card_inter α β

private lemma nonemptyBonus_submodular (α β : Finset (Fin 4)) :
    nonemptyBonus (α ∪ β) + nonemptyBonus (α ∩ β) ≤ nonemptyBonus α + nonemptyBonus
      β := by
  by_cases hα : α.Nonempty
  · by_cases hβ : β.Nonempty
    · have hUnion : (α ∪ β).Nonempty := Finset.union_nonempty.2 (Or.inl hα)
      by_cases hInter : (α ∩ β).Nonempty
      · simp [nonemptyBonus, hα, hβ, hUnion, hInter]
      · simp [nonemptyBonus, hα, hβ, hUnion, hInter]
    · have hβ' : β = ∅ := Finset.not_nonempty_iff_eq_empty.mp hβ
      rw [hβ']
      simp [nonemptyBonus, hα]
  · have hα' : α = ∅ := Finset.not_nonempty_iff_eq_empty.mp hα
    rw [hα']
    simp [nonemptyBonus]

private lemma fullBonus_supermodular (α β : Finset (Fin 4)) :
    fullBonus α + fullBonus β ≤ fullBonus (α ∪ β) + fullBonus (α ∩ β) := by
  by_cases hα : α = Finset.univ
  · subst hα
    by_cases hβ : β = Finset.univ
    · subst hβ
      simp [fullBonus]
    · simp [fullBonus, hβ]
  · by_cases hβ : β = Finset.univ
    · subst hβ
      simp [fullBonus, hα]
    · have hUnion : 0 ≤ fullBonus (α ∪ β) := fullBonus_nonneg _
      have hInter : 0 ≤ fullBonus (α ∩ β) := fullBonus_nonneg _
      have hSum : 0 ≤ fullBonus (α ∪ β) + fullBonus (α ∩ β) := by
        linarith
      simpa [fullBonus, hα, hβ] using hSum

private lemma baseWitness_submodular (α β : Finset (Fin 4)) :
    baseWitness (α ∪ β) + baseWitness (α ∩ β) ≤ baseWitness α + baseWitness β := by
  have hCard := card_modular α β
  have hNonempty := nonemptyBonus_submodular α β
  have hFull := fullBonus_supermodular α β
  unfold baseWitness
  linarith

private abbrev PairBonusExceptional (α β : Finset (Fin 4)) : Prop :=
  (α = ({0} : Finset (Fin 4)) ∧ β = ({1} : Finset (Fin 4))) ∨
    (α = ({1} : Finset (Fin 4)) ∧ β = ({0} : Finset (Fin 4))) ∨
    (α = ({0, 1, 2} : Finset (Fin 4)) ∧ β = ({0, 1, 3} : Finset (Fin 4))) ∨
    (α = ({0, 1, 3} : Finset (Fin 4)) ∧ β = ({0, 1, 2} : Finset (Fin 4)))

private lemma exceptional_of_union_pair :
    ∀ α β : Finset (Fin 4),
      α ∪ β = pair01 → α ≠ pair01 → β ≠ pair01 → PairBonusExceptional α β := by
  decide

private lemma exceptional_of_inter_pair :
    ∀ α β : Finset (Fin 4),
      α ∩ β = pair01 → α ≠ pair01 → β ≠ pair01 → PairBonusExceptional α β := by
  decide

private lemma pairBonus_submodular_left_pair (β : Finset (Fin 4)) :
    pairBonus (pair01 ∪ β) + pairBonus (pair01 ∩ β) ≤ pairBonus pair01 + pairBonus β := by
  by_cases hSub : β ⊆ pair01
  · by_cases hSup : pair01 ⊆ β
    · have hβ : β = pair01 := Finset.Subset.antisymm hSub hSup
      subst hβ
      simp [pairBonus]
    · have hβ : β ≠ pair01 := by
        intro h
        have hEqSub : pair01 ⊆ β := by simp [h]
        exact hSup hEqSub
      have hUnion : pair01 ∪ β = pair01 := Finset.union_eq_left.mpr hSub
      have hInter : pair01 ∩ β ≠ pair01 := by
        intro h
        exact hSup (Finset.inter_eq_left.mp h)
      simp [pairBonus, hUnion, hInter, hβ]
  · by_cases hSup : pair01 ⊆ β
    · have hβ : β ≠ pair01 := by
        intro h
        have hEqSub : β ⊆ pair01 := by simp [h]
        exact hSub hEqSub
      have hUnion : pair01 ∪ β ≠ pair01 := by
        intro h
        exact hSub (Finset.union_eq_left.mp h)
      have hInter : pair01 ∩ β = pair01 := Finset.inter_eq_left.mpr hSup
      simp [pairBonus, hUnion, hInter, hβ]
    · have hβ : β ≠ pair01 := by
        intro h
        have hEqSub : β ⊆ pair01 := by simp [h]
        exact hSub hEqSub
      have hUnion : pair01 ∪ β ≠ pair01 := by
        intro h
        exact hSub (Finset.union_eq_left.mp h)
      have hInter : pair01 ∩ β ≠ pair01 := by
        intro h
        exact hSup (Finset.inter_eq_left.mp h)
      simp [pairBonus, hUnion, hInter, hβ]

private lemma pairBonus_submodular_outside_exceptional :
    ∀ α β : Finset (Fin 4), ¬ PairBonusExceptional α β →
      pairBonus (α ∪ β) + pairBonus (α ∩ β) ≤ pairBonus α + pairBonus β := by
  intro α β hExceptional
  by_cases hα : α = pair01
  · subst hα
    simpa [pairBonus] using pairBonus_submodular_left_pair β
  · by_cases hβ : β = pair01
    · subst hβ
      simpa [Finset.union_comm, Finset.inter_comm, pairBonus, add_comm, add_left_comm,
        add_assoc] using
        pairBonus_submodular_left_pair α
    · by_cases hUnion : α ∪ β = pair01
      · exact False.elim (hExceptional (exceptional_of_union_pair α β hUnion hα hβ))
      · by_cases hInter : α ∩ β = pair01
        · exact False.elim (hExceptional (exceptional_of_inter_pair α β hInter hα hβ))
        · simp [pairBonus, hα, hβ, hUnion, hInter]

private lemma FWitnessℚ_submodular :
    ∀ α β : Finset (Fin 4),
      FWitnessℚ (α ∪ β) + FWitnessℚ (α ∩ β) ≤ FWitnessℚ α +
        FWitnessℚ β := by
  intro α β
  by_cases hExceptional : PairBonusExceptional α β
  · rcases hExceptional with h01 | h10 | h012013 | h013012
    · rcases h01 with ⟨rfl, rfl⟩
      have hUnion : FWitnessℚ (({0} : Finset (Fin 4)) ∪ {1}) = 4 := by decide
      have hInter : FWitnessℚ (({0} : Finset (Fin 4)) ∩ {1}) = 0 := by decide
      have h0 : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
      have h1 : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
      rw [hUnion, hInter, h0, h1]
      norm_num
    · rcases h10 with ⟨rfl, rfl⟩
      have hUnion : FWitnessℚ (({1} : Finset (Fin 4)) ∪ {0}) = 4 := by decide
      have hInter : FWitnessℚ (({1} : Finset (Fin 4)) ∩ {0}) = 0 := by decide
      have h1 : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
      have h0 : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
      rw [hUnion, hInter, h1, h0]
      norm_num
    · rcases h012013 with ⟨rfl, rfl⟩
      have hUnion : FWitnessℚ (({0, 1, 2} : Finset (Fin 4)) ∪ {0, 1, 3}) = 4 := by decide
      have hInter : FWitnessℚ (({0, 1, 2} : Finset (Fin 4)) ∩ {0, 1, 3}) = 4 := by decide
      have h012 : FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 := by decide
      have h013 : FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 := by decide
      rw [hUnion, hInter, h012, h013]
    · rcases h013012 with ⟨rfl, rfl⟩
      have hUnion : FWitnessℚ (({0, 1, 3} : Finset (Fin 4)) ∪ {0, 1, 2}) = 4 := by decide
      have hInter : FWitnessℚ (({0, 1, 3} : Finset (Fin 4)) ∩ {0, 1, 2}) = 4 := by decide
      have h013 : FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 := by decide
      have h012 : FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 := by decide
      rw [hUnion, hInter, h013, h012]
  · rw [FWitnessℚ_eq_base_add_pair (α ∪ β), FWitnessℚ_eq_base_add_pair (α ∩ β),
      FWitnessℚ_eq_base_add_pair α, FWitnessℚ_eq_base_add_pair β]
    have hBase := baseWitness_submodular α β
    have hPair := pairBonus_submodular_outside_exceptional α β hExceptional
    linarith

/-! ### Part (a): the witness lies in the Shannon cone -/

/--
Part (a) of Theorem 4: the witness satisfies the three Shannon-cone axioms (paper eq.
11). The
empty-set and monotonicity checks close by finite `decide` over the `ℚ`-valued witness,
while
submodularity is proved structurally by decomposing the witness into a cardinality
profile plus one
exceptional pair bonus.
-/
theorem shannonCone_of_witness : shannonCone FWitness := by
  refine ⟨?_, ?_, ?_⟩
  · -- `FWitness ∅ = 0`
    change ((FWitnessℚ ∅ : ℚ) : ℝ) = 0
    have h : FWitnessℚ ∅ = 0 := by decide
    exact_mod_cast h
  · -- Monotonicity.
    intro α β hαβ
    have h : ∀ α β : Finset (Fin 4), α ⊆ β → FWitnessℚ α ≤ FWitnessℚ β := by
      decide
    simp only [FWitness_eq_cast]
    exact_mod_cast h α β hαβ
  · -- Submodularity.
    intro α β
    simp only [FWitness_eq_cast]
    exact_mod_cast FWitnessℚ_submodular α β

/-! ### Part (b): the witness violates the Zhang-Yeung inequality -/

/--
The concrete numerical failure underlying Part (b): at the paper's canonical labeling
`(i, j, k, l)
= (2, 3, 0, 1)` (paper lines 378-388), the witness fails the Zhang-Yeung inequality; the
check
reduces to `1 ≤ 1/2`. Kept as a private helper so both the permutation form
(`not_zhangYeungHolds_witness`) and the `Fin n` lift (`not_zhangYeungHolds_witness_n`)
can consume
it without reproducing the concrete witness evaluation block.
-/
private lemma not_zhangYeungAt_witness_canonical :
    ¬ zhangYeungAt FWitness 2 3 0 1 := by
  intro h
  simp only [zhangYeungAt, deltaF, IF, condIF, FWitness_eq_cast] at h
  have h00 : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
  have h11 : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
  have h22 : FWitnessℚ ({2} : Finset (Fin 4)) = 2 := by decide
  have h33 : FWitnessℚ ({3} : Finset (Fin 4)) = 2 := by decide
  have h01 : FWitnessℚ (({0} : Finset (Fin 4)) ∪ {1}) = 4 := by decide
  have h02 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {0}) = 3 := by decide
  have h03 : FWitnessℚ (({3} : Finset (Fin 4)) ∪ {0}) = 3 := by decide
  have h12 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {1}) = 3 := by decide
  have h13 : FWitnessℚ (({3} : Finset (Fin 4)) ∪ {1}) = 3 := by decide
  have h23 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3}) = 3 := by decide
  have h023 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {0}) = 4 := by decide
  have h123 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {1}) = 4 := by decide
  have h023' : FWitnessℚ (({0} : Finset (Fin 4)) ∪ (({2} : Finset (Fin 4)) ∪ {3})) = 4 := by
    decide
  rw [h00, h11, h22, h33, h01, h02, h03, h12, h13, h23, h023, h123, h023'] at h
  norm_num at h

/--
Part (b) of Theorem 4: the witness fails the Zhang-Yeung inequality at the canonical
labeling `(i,
j, k, l) = (2, 3, 0, 1)` (paper lines 378-388). The permutation exhibiting the violation
is `σ =
Equiv.swap 0 2 * Equiv.swap 1 3`; after permutation evaluation the obligation is the
canonical
failure `not_zhangYeungAt_witness_canonical`.
-/
theorem not_zhangYeungHolds_witness : ¬ zhangYeungHolds FWitness := by
  intro h
  specialize h (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
  rw [show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 0 = 2 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 = 3 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 2 = 0 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 3 = 1 from by decide] at h
  exact not_zhangYeungAt_witness_canonical h

/--
Intermediate conclusion (pre-bridge): the Shannon cone strictly contains the Zhang-Yeung
cone, `Γ_4
⊋ tildeΓ_4`. Part (a) and Part (b) combined. This remains a useful stronger auxiliary:
`theorem4_finite` strengthens it to exclusion from the literal entropy region, while
`theorem4`
packages the exact closure statement from the paper.
-/
theorem shannon_incomplete :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  ⟨FWitness, shannonCone_of_witness, not_zhangYeungHolds_witness⟩

/-!
### Part (c): the bridge from the random-variable form (M3) to the set-function form
-/

section EntropyFnEvaluation

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [∀ i, Finite (S i)] in
/--
Per-subset bridge lemma at the empty subset: `entropyFn X μ ∅ = 0`. The subtype `{j // j
∈ (∅ :
Finset (Fin 4))}` is empty, so the dependent-product codomain `∀ j : ∅, S j.1` is a
subsingleton;
the joint tuple is constant, and its entropy is zero.
-/
lemma entropyFn_empty : entropyFn X μ ∅ = 0 := by
  simp only [entropyFn, entropyFnN]
  haveI : IsEmpty {j : Fin 4 // j ∈ (∅ : Finset (Fin 4))} :=
    ⟨fun ⟨j, hj⟩ => Finset.notMem_empty j hj⟩
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have h_eq : (fun ω : Ω => fun j : (∅ : Finset (Fin 4)) => X j.1 ω)
      = fun _ =>
        (fun j : (∅ : Finset (Fin 4)) => X j.1 (Classical.arbitrary Ω)) := by
    funext ω
    exact Subsingleton.elim _ _
  rw [h_eq]
  exact entropy_const _

omit [IsProbabilityMeasure μ] in
/--
Per-subset bridge lemma at a singleton subset: `entropyFn X μ {i} = H[X i; μ]`. The
joint tuple
over the single-element subset `{i}` is, up to a measurable bijection into `S i`, just
`X i`.
-/
lemma entropyFn_singleton (hX : ∀ i, Measurable (X i)) (i : Fin 4) :
    entropyFn X μ {i} = H[X i; μ] := by
  letI : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  -- Projection π : (∀ j : {i}, S j.1) → S i sending g to its value at ⟨i, mem⟩.
  let π : (∀ j : ({i} : Finset (Fin 4)), S j.1) → S i :=
    fun g => g ⟨i, Finset.mem_singleton.mpr rfl⟩
  -- Injectivity: every j : {i} satisfies j.1 = i, so g is determined by its
  -- value at ⟨i, _⟩.
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    funext j
    obtain ⟨j, hj⟩ := j
    have hji : j = i := Finset.mem_singleton.mp hj
    subst hji
    exact heq
  -- The joint RV is measurable: each coordinate `X j.1` is measurable.
  have h_meas : Measurable
      (fun ω : Ω => fun j : ({i} : Finset (Fin 4)) => X j.1 ω) :=
    measurable_pi_lambda _ (fun j => hX j.1)
  -- π ∘ joint = X i definitionally, so the composed entropy collapses.
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/--
Per-subset bridge lemma at a two-element subset: `entropyFn X μ {i, j} = H[⟨X i, X j⟩;
μ]` for `i ≠
j`. The joint tuple over `{i, j}` is measurably bijective with the pair `(X i, X j)`.
-/
lemma entropyFn_pair (hX : ∀ i, Measurable (X i))
    {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩; μ] := by
  letI : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  -- Projection π : (∀ k : {i, j}, S k.1) → S i × S j evaluating at both indices.
  have hi : i ∈ ({i, j} : Finset (Fin 4)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin 4)) := by simp
  let π : (∀ k : ({i, j} : Finset (Fin 4)), S k.1) → S i × S j :=
    fun g => (g ⟨i, hi⟩, g ⟨j, hj⟩)
  -- Injectivity: every k : {i, j} satisfies k.1 = i ∨ k.1 = j.
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have h₁ : g₁ ⟨i, hi⟩ = g₂ ⟨i, hi⟩ := (Prod.mk.inj heq).1
    have h₂ : g₁ ⟨j, hj⟩ = g₂ ⟨j, hj⟩ := (Prod.mk.inj heq).2
    funext k
    obtain ⟨k, hk⟩ := k
    rcases Finset.mem_insert.mp hk with hki | hk'
    · subst hki; exact h₁
    · have : k = j := Finset.mem_singleton.mp hk'
      subst this; exact h₂
  have h_meas : Measurable
      (fun ω : Ω => fun k : ({i, j} : Finset (Fin 4)) => X k.1 ω) :=
    measurable_pi_lambda _ (fun k => hX k.1)
  -- π ∘ joint = ⟨X i, X j⟩ definitionally.
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/--
Per-subset bridge lemma at a three-element subset: `entropyFn X μ {i, j, k} = H[⟨X i, ⟨X
j, X k⟩⟩;
μ]` for pairwise distinct `i, j, k`. The joint tuple over `{i, j, k}` is measurably
bijective with
the triple `(X i, (X j, X k))`.
-/
lemma entropyFn_triple (hX : ∀ i, Measurable (X i))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩; μ] := by
  letI : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  have hi : i ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  have hj : j ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  have hk : k ∈ ({i, j, k} : Finset (Fin 4)) := by simp
  let π : (∀ m : ({i, j, k} : Finset (Fin 4)), S m.1) → S i × (S j × S k) :=
    fun g => (g ⟨i, hi⟩, (g ⟨j, hj⟩, g ⟨k, hk⟩))
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have h₁ : g₁ ⟨i, hi⟩ = g₂ ⟨i, hi⟩ := (Prod.mk.inj heq).1
    have h₂ : g₁ ⟨j, hj⟩ = g₂ ⟨j, hj⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).1
    have h₃ : g₁ ⟨k, hk⟩ = g₂ ⟨k, hk⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).2
    funext m
    obtain ⟨m, hm⟩ := m
    rcases Finset.mem_insert.mp hm with hmi | hm'
    · subst hmi; exact h₁
    · rcases Finset.mem_insert.mp hm' with hmj | hmk
      · subst hmj; exact h₂
      · have : m = k := Finset.mem_singleton.mp hmk
        subst this; exact h₃
  have h_meas : Measurable
      (fun ω : Ω => fun m : ({i, j, k} : Finset (Fin 4)) => X m.1 ω) :=
    measurable_pi_lambda _ (fun m => hX m.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

omit [IsProbabilityMeasure μ] in
/--
Per-subset bridge lemma at the full four-element subset: `entropyFn X μ {0, 1, 2, 3} =
H[⟨X 0, ⟨X
1, ⟨X 2, X 3⟩⟩⟩; μ]`. The joint tuple over the full index set is measurably bijective
with the
right-associated 4-tuple.
-/
lemma entropyFn_quad (hX : ∀ i, Measurable (X i)) :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩; μ] := by
  letI : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  have h0 : (0 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h2 : (2 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h3 : (3 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  let π : (∀ m : ({0, 1, 2, 3} : Finset (Fin 4)), S m.1)
      → S 0 × (S 1 × (S 2 × S 3)) :=
    fun g => (g ⟨0, h0⟩, (g ⟨1, h1⟩, (g ⟨2, h2⟩, g ⟨3, h3⟩)))
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have e1 : g₁ ⟨0, h0⟩ = g₂ ⟨0, h0⟩ := (Prod.mk.inj heq).1
    have e2 : g₁ ⟨1, h1⟩ = g₂ ⟨1, h1⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).1
    have e3 : g₁ ⟨2, h2⟩ = g₂ ⟨2, h2⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).1
    have e4 : g₁ ⟨3, h3⟩ = g₂ ⟨3, h3⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).2
    funext m
    obtain ⟨m, hm⟩ := m
    fin_cases m
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have h_meas : Measurable
      (fun ω : Ω => fun m : ({0, 1, 2, 3} : Finset (Fin 4)) => X m.1 ω) :=
    measurable_pi_lambda _ (fun m => hX m.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  exact h_ent.symm

end EntropyFnEvaluation

/--
The permutation-indexed bridge: at any permutation `π` of `Fin 4`, the entropy function
satisfies
the Zhang-Yeung inequality (paper eq. 21) at the labeling `(π 0, π 1, π 2, π 3)`. Proved
by
unfolding `zhangYeungAt`, rewriting each `entropyFn` evaluation into a joint entropy via
the
per-subset bridge lemmas, and matching the resulting inequality against M3's
`ZhangYeung.zhangYeung` applied to `(X (π 0), X (π 1), X (π 2), X (π 3))`.
-/
lemma _root_.ZhangYeung.zhangYeungAt_entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3) := by
  -- Distinctness of the four permuted indices from injectivity of `π`.
  have h01 : π 0 ≠ π 1 := fun h => absurd (π.injective h) (by decide)
  have h02 : π 0 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have h03 : π 0 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  have h12 : π 1 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have h13 : π 1 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  have h23 : π 2 ≠ π 3 := fun h => absurd (π.injective h) (by decide)
  -- Apply M3 at the labeling `(X_M3, Y_M3, Z_M3, U_M3) =
  -- (X (π 2), X (π 3), X (π 0), X (π 1))`.
  have hM3 := ZhangYeung.zhangYeung (hX (π 2)) (hX (π 3)) (hX (π 0)) (hX (π 1)) μ
  -- Fully unfold `hM3` into unconditional `H[_; μ]` arithmetic, matching the
  -- shape the set-function bridge produces.
  rw [delta_def, mutualInfo_def, mutualInfo_def, mutualInfo_def,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 3)) μ,
      chain_rule'' μ (hX (π 0)) (hX (π 2)),
      chain_rule'' μ (hX (π 1)) (hX (π 2)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 2)),
      chain_rule'' μ (hX (π 0)) (hX (π 3)),
      chain_rule'' μ (hX (π 1)) (hX (π 3)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 3)),
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 3)) μ] at hM3
  -- Unfold the set-function calculus on the goal.
  unfold zhangYeungAt deltaF IF condIF
  -- Collapse `{x} ∪ s` and `insert a s ∪ t` to canonical `insert`-form so the
  -- `entropyFn_pair`/`entropyFn_triple` bridges fire without further massage.
  simp only [Finset.singleton_union, Finset.insert_union]
  -- Apply the per-subset bridge lemmas.
  rw [entropyFn_singleton X μ hX (π 0), entropyFn_singleton X μ hX (π 1),
      entropyFn_singleton X μ hX (π 2), entropyFn_singleton X μ hX (π 3),
      entropyFn_pair X μ hX h01, entropyFn_pair X μ hX h02,
      entropyFn_pair X μ hX h03, entropyFn_pair X μ hX h12,
      entropyFn_pair X μ hX h13, entropyFn_pair X μ hX h23,
      entropyFn_triple X μ hX h01 h02 h12,
      entropyFn_triple X μ hX h01 h03 h13,
      entropyFn_triple X μ hX h02.symm h12.symm h01]
  linarith

/--
Part (c), the full bridge: the entropy function of any four-variable random-variable
family lies in
`tildeΓ_4`. One-line wrapper around `zhangYeungAt_entropyFn`.
-/
theorem _root_.ZhangYeung.zhangYeungHolds_of_entropy
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) :=
  fun π => zhangYeungAt_entropyFn hX μ π

/-! ### Part (d): Theorem 4 -/

/--
Finite auxiliary form of Theorem 4 at `n = 4`: the witness lies in `Γ_4` but is not the
entropy
function of any single four-variable discrete family. The exact paper-level closure
statement is
the later theorem `theorem4`.
-/
theorem _root_.ZhangYeung.theorem4_finite :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ := by
  refine ⟨FWitness, shannonCone_of_witness, ?_⟩
  intro Ω _ μ _ S _ _ _ X hX heq
  apply not_zhangYeungHolds_witness
  rw [heq]
  exact zhangYeungHolds_of_entropy hX μ

/-! ### Closure form

Each inequality `zhangYeungAt F (π 0) (π 1) (π 2) (π 3)` is a finite linear inequality
among the
coordinate evaluations `F α`, hence defines a closed subset of `Finset (Fin 4) → ℝ` in
the
pointwise topology. Their intersection is the closed Zhang-Yeung region `tildeΓ_4`.
Since every
four-variable entropy function lies in `tildeΓ_4` by `zhangYeungHolds_of_entropy`, the
almost-entropic region `closure (Γ_4^*)` lies there as well, while the explicit witness
does not.
This yields the exact paper-level theorem `theorem4`. The sequence-level surrogate is
retained
separately as `theorem4_seqClosure`. -/

/--
`IF` is jointly continuous in the set-function argument under pointwise convergence.
-/
private lemma IF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β : Finset (Fin 4)) :
    Filter.Tendsto (fun k => IF (F_seq k) α β) Filter.atTop (𝓝 (IF F α β)) := by
  simp only [IF]
  exact ((h α).add (h β)).sub (h _)

/--
`condIF` is jointly continuous in the set-function argument under pointwise
convergence.
-/
private lemma condIF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β γ : Finset (Fin 4)) :
    Filter.Tendsto (fun k => condIF (F_seq k) α β γ) Filter.atTop (𝓝 (condIF F α β
      γ)) := by
  simp only [condIF]
  exact (((h _).add (h _)).sub (h _)).sub (h _)

/--
`deltaF` is jointly continuous in the set-function argument under pointwise
convergence.
-/
private lemma deltaF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (i j k l : Fin 4) :
    Filter.Tendsto (fun n => deltaF (F_seq n) i j k l) Filter.atTop
      (𝓝 (deltaF F i j k l)) := by
  simp only [deltaF]
  exact ((IF_tendsto h _ _).sub (condIF_tendsto h _ _ _)).sub (condIF_tendsto h _ _ _)

/--
`zhangYeungHolds` is closed under pointwise convergence: if each `F_seq k` lies in
`tildeΓ_4` and
`F_seq k α → F α` pointwise, then `F` lies in `tildeΓ_4` too. The inequality
`zhangYeungAt F` is a
finite `≤` between continuous linear combinations of coordinate evaluations, hence
preserved under
pointwise limits.
-/
lemma _root_.ZhangYeung.zhangYeungHolds_of_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F := by
  intro π
  have h_LHS := deltaF_tendsto h_lim (π 0) (π 1) (π 2) (π 3)
  have h_RHS :
      Filter.Tendsto
        (fun k => (1 / 2 : ℝ) * (IF (F_seq k) {π 2} {π 3}
              + IF (F_seq k) {π 2} ({π 0} ∪ {π 1})
              + condIF (F_seq k) {π 0} {π 1} {π 2}
              - condIF (F_seq k) {π 0} {π 1} {π 3}))
        Filter.atTop
        (𝓝 ((1 / 2 : ℝ) * (IF F {π 2} {π 3}
            + IF F {π 2} ({π 0} ∪ {π 1})
            + condIF F {π 0} {π 1} {π 2}
            - condIF F {π 0} {π 1} {π 3}))) := by
    refine Filter.Tendsto.const_mul _ ?_
    exact (((IF_tendsto h_lim _ _).add (IF_tendsto h_lim _ _)).add
      (condIF_tendsto h_lim _ _ _)).sub (condIF_tendsto h_lim _ _ _)
  exact le_of_tendsto_of_tendsto' h_LHS h_RHS (fun k => h_seq k π)

private lemma continuous_IF (α β : Finset (Fin 4)) :
    Continuous (fun F : Finset (Fin 4) → ℝ => IF F α β) := by
  simpa [IF] using ((continuous_apply α).add (continuous_apply β)).sub (continuous_apply (α
    ∪ β))

private lemma continuous_condIF (α β γ : Finset (Fin 4)) :
    Continuous (fun F : Finset (Fin 4) → ℝ => condIF F α β γ) := by
  simpa [condIF, Finset.union_assoc] using
    (((continuous_apply (α ∪ γ)).add (continuous_apply (β ∪ γ))).sub
      (continuous_apply (α ∪ (β ∪ γ)))).sub (continuous_apply γ)

private lemma continuous_deltaF (i j k l : Fin 4) :
    Continuous (fun F : Finset (Fin 4) → ℝ => deltaF F i j k l) := by
  simpa [deltaF] using
    ((continuous_IF {i} {j}).sub (continuous_condIF {i} {j} {k})).sub
      (continuous_condIF {i} {j} {l})

private lemma isClosed_zhangYeungAt_set (π : Equiv.Perm (Fin 4)) :
    IsClosed {F : Finset (Fin 4) → ℝ | zhangYeungAt F (π 0) (π 1) (π 2) (π 3)} := by
  unfold zhangYeungAt
  refine isClosed_le (continuous_deltaF _ _ _ _) ?_
  refine continuous_const.mul ?_
  exact (((continuous_IF {π 2} {π 3}).add (continuous_IF {π 2} ({π 0} ∪ {π 1}))).add
    (continuous_condIF {π 0} {π 1} {π 2})).sub (continuous_condIF {π 0} {π 1} {π 3})

private def zhangYeungRegion_4 : Set (Finset (Fin 4) → ℝ) :=
  {F | zhangYeungHolds F}

/--
The Zhang-Yeung region on `Finset (Fin 4) → ℝ` is closed in the pointwise topology.
-/
private lemma isClosed_zhangYeungRegion_4 : IsClosed zhangYeungRegion_4 := by
  classical
  have h_eq : zhangYeungRegion_4 =
      ⋂ π : Equiv.Perm (Fin 4),
        {F : Finset (Fin 4) → ℝ | zhangYeungAt F (π 0) (π 1) (π 2) (π 3)} := by
    ext F
    simp [zhangYeungRegion_4, zhangYeungHolds]
  rw [h_eq]
  exact isClosed_iInter fun π : Equiv.Perm (Fin 4) => isClosed_zhangYeungAt_set π

/-- Every entropic point in dimension `4` lies in the closed Zhang-Yeung region. -/
private lemma entropyRegion_four_subset_zhangYeungRegion_4 :
    entropyRegionN.{u} 4 ⊆ zhangYeungRegion_4 := by
  intro F hF
  rcases hF with ⟨Ω, hΩ, μ, hμ, S, hS, hFin, hMSC, X, hX, h_eq⟩
  letI : MeasurableSpace Ω := hΩ
  letI : IsProbabilityMeasure μ := hμ
  letI : ∀ i, MeasurableSpace (S i) := hS
  letI : ∀ i, Fintype (S i) := hFin
  letI : ∀ i, MeasurableSingletonClass (S i) := hMSC
  rw [h_eq]
  simpa [zhangYeungRegion_4] using zhangYeungHolds_of_entropy hX μ

/-- Every almost-entropic point in dimension `4` lies in the Zhang-Yeung region. -/
private lemma almostEntropicRegion_four_subset_zhangYeungRegion_4 :
    almostEntropicRegionN.{u} 4 ⊆ zhangYeungRegion_4 := by
  simpa [almostEntropicRegionN] using
    (closure_minimal entropyRegion_four_subset_zhangYeungRegion_4 isClosed_zhangYeungRegion_4)

/-- The witness is not almost entropic in dimension `4`. -/
private lemma not_mem_almostEntropicRegion_witness : FWitness ∉ almostEntropicRegionN.{u} 4 :=
  by
  intro hF
  exact not_zhangYeungHolds_witness (almostEntropicRegion_four_subset_zhangYeungRegion_4 hF)

/--
**Theorem 4 of [@zhangyeung1998, §II, eq. 26]** at `n = 4`. The Shannon outer bound
`Γ_4` strictly
contains the closure of the entropic region: there exists a set function in `Γ_4` that
is not
almost entropic. The non-membership claim is universe-polymorphic: for every universe
`u`,
`FWitness ∉ almostEntropicRegionN.{u} 4`, since the closedness argument in
`zhangYeungRegion_4`
lives entirely at the level of `Finset (Fin 4) → ℝ`.
-/
theorem _root_.ZhangYeung.theorem4 :
    ∃ F : Finset (Fin 4) → ℝ,
      F ∈ shannonRegionN 4 ∧ F ∉ almostEntropicRegionN.{u} 4 := by
  refine ⟨FWitness, ?_, not_mem_almostEntropicRegion_witness⟩
  change shannonConeN FWitness
  exact shannonCone_of_witness

/--
Sequence-level strengthening of the witness exclusion: `FWitness` is not the pointwise
limit of
any sequence of set functions in `tildeΓ_4`. This auxiliary is stronger than `theorem4`,
but it is
phrased in the larger Zhang-Yeung cone rather than in `closure (Γ_4^*)`.
-/
theorem _root_.ZhangYeung.theorem4_seqClosure :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False := by
  refine ⟨FWitness, shannonCone_of_witness, ?_⟩
  intro F_seq h_seq h_lim
  exact not_zhangYeungHolds_witness (zhangYeungHolds_of_tendsto h_seq h_lim)

/-! ### `n ≥ 4` extension

The witness `FWitnessN` is the lift of `FWitness` along the canonical embedding `Fin
4 ↪ Fin n`
via `Finset.preimage`. It still lies in the Shannon cone and still violates the
Zhang-Yeung
inequality at the lifted canonical labeling `(Fin.castLE hn 2, Fin.castLE hn 3,
Fin.castLE hn 0,
Fin.castLE hn 1)`. The exact paper-level `n ≥ 4` theorem then follows by restricting any
hypothetical almost-entropic realization back down to the first four coordinates. The
generic cone
predicates `zhangYeungAtN` and `zhangYeungHoldsN` consumed below live in
`ZhangYeung.EntropyRegion`. -/

/--
The `n = 4` witness lifted to `Fin n` for `n ≥ 4`: `FWitnessN hn α` evaluates
`FWitness` on the
preimage of `α` under the canonical embedding `Fin 4 ↪ Fin n`. Equivalent to `FWitness`
applied to
the intersection of `α` with the initial segment `{0, 1, 2, 3 : Fin n}`.
-/
noncomputable def _root_.ZhangYeung.FWitnessN
    {n : ℕ} (hn : 4 ≤ n) (α : Finset (Fin n)) : ℝ :=
  FWitness (α.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn)

/--
The lifted witness lies in `Γ_n`: each Shannon-cone axiom transports across
`Finset.preimage` via
`preimage_empty`, `monotone_preimage`, `preimage_union`, and `preimage_inter`, and then
reduces to
the base `shannonCone_of_witness`.
-/
theorem _root_.ZhangYeung.shannonCone_of_witness_n {n : ℕ} (hn : 4 ≤ n) :
    shannonConeN (FWitnessN hn) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [FWitnessN] using shannonCone_of_witness.1
  · intro α β hαβ
    simpa [FWitnessN] using shannonCone_of_witness.2.1 _ _
      (Finset.monotone_preimage (Fin.castLE_injective hn) hαβ)
  · intro α β
    have h_inter :
        α.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn ∩
            β.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn =
          (α ∩ β).preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn := by
      ext i
      simp [Finset.mem_preimage]
    rw [FWitnessN, FWitnessN, FWitnessN, FWitnessN]
    rw [Finset.preimage_union, ← h_inter]
    exact shannonCone_of_witness.2.2
      (α.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn)
      (β.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn)

/-- The preimage of a singleton `{Fin.castLE hn i}` under `Fin.castLE hn` is `{i}`. -/
private lemma preimage_singleton_castLE {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    ({Fin.castLE hn i} : Finset (Fin n)).preimage (Fin.castLE hn)
        (Fin.castLE_injective hn).injOn = ({i} : Finset (Fin 4)) := by
  ext j
  simp [Finset.mem_preimage, Finset.mem_singleton,
    (Fin.castLE_injective hn).eq_iff]

/--
Restricting the lifted witness back to the first four coordinates recovers the base
witness.
-/
theorem _root_.ZhangYeung.restrictFirstFour_witness_n {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn (FWitnessN hn) = FWitness := by
  ext α
  unfold restrictFirstFour FWitnessN
  congr
  simpa using (Finset.preimage_map (Fin.castLEEmb hn) α)

/--
The Zhang-Yeung inequality at the lifted canonical labeling pulls back to the base
labeling: every
set-function operation in `zhangYeungAtN FWitnessN` reduces through `Finset.preimage`
to the
corresponding `zhangYeungAt FWitness` operation on `Fin 4`.
-/
private lemma zhangYeungAtN_witness_castLE {n : ℕ} (hn : 4 ≤ n) (i j k l : Fin 4) :
    zhangYeungAtN (FWitnessN hn) (Fin.castLE hn i) (Fin.castLE hn j)
        (Fin.castLE hn k) (Fin.castLE hn l)
      ↔ zhangYeungAt FWitness i j k l := by
  unfold zhangYeungAtN zhangYeungAt deltaFN deltaF IFN IF condIFN condIF FWitnessN
  simp only [Finset.preimage_union, preimage_singleton_castLE]

/--
Part (b) lifted to `Fin n`: the lifted witness fails `zhangYeungHoldsN` at the lifted
canonical
labeling.
-/
theorem _root_.ZhangYeung.not_zhangYeungHolds_witness_n {n : ℕ} (hn : 4 ≤ n) :
    ¬ zhangYeungHoldsN (FWitnessN hn) := by
  intro h
  have inj := Fin.castLE_injective hn
  have d23 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 3 :=
    fun e => absurd (inj e) (by decide)
  have d20 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 0 :=
    fun e => absurd (inj e) (by decide)
  have d21 : (Fin.castLE hn 2 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have d30 : (Fin.castLE hn 3 : Fin n) ≠ Fin.castLE hn 0 :=
    fun e => absurd (inj e) (by decide)
  have d31 : (Fin.castLE hn 3 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have d01 : (Fin.castLE hn 0 : Fin n) ≠ Fin.castLE hn 1 :=
    fun e => absurd (inj e) (by decide)
  have hat := h (Fin.castLE hn 2) (Fin.castLE hn 3) (Fin.castLE hn 0) (Fin.castLE hn 1)
    d23 d20 d21 d30 d31 d01
  exact not_zhangYeungAt_witness_canonical ((zhangYeungAtN_witness_castLE hn 2 3 0 1).mp hat)

/--
Stronger cone-level corollary for `n ≥ 4`: the lifted witness separates `Γ_n` from the
`Fin
n`-indexed Zhang-Yeung cone. Since `closure (Γ_n^*) ⊆ tildeΓ_n`, this strictly
strengthens the
exact paper-level theorem `theorem4_ge_four`.
-/
theorem _root_.ZhangYeung.shannon_incomplete_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonConeN F ∧ ¬ zhangYeungHoldsN F :=
  ⟨FWitnessN hn, shannonCone_of_witness_n hn, not_zhangYeungHolds_witness_n hn⟩

/--
**Theorem 4 of [@zhangyeung1998, §II, eq. 26]** for all `n ≥ 4`. The Shannon outer bound
`Γ_n`
strictly contains the closure of the entropic region: there exists a set function in
`Γ_n` that is
not almost entropic. The non-membership claim is universe-polymorphic: for every
universe `u`,
`FWitnessN hn ∉ almostEntropicRegionN.{u} n`, by restricting any hypothetical
almost-entropic
realization back down to the first four coordinates and applying the `n = 4` exclusion.
-/
theorem _root_.ZhangYeung.theorem4_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ,
      F ∈ shannonRegionN n ∧ F ∉ almostEntropicRegionN.{u} n := by
  refine ⟨FWitnessN hn, ?_, ?_⟩
  · change shannonConeN (FWitnessN hn)
    exact shannonCone_of_witness_n hn
  · intro hF
    have h_restrict : FWitness ∈ almostEntropicRegionN.{u} 4 := by
      simpa [restrictFirstFour_witness_n hn] using restrictFirstFour_mem_almostEntropicRegionN
        hn hF
    exact not_mem_almostEntropicRegion_witness h_restrict

end ZhangYeung
