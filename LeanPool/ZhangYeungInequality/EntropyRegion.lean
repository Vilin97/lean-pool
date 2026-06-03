/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Prelude

/-!
# Entropy-region infrastructure for Theorem 4

This module packages the generic `Fin n` set-function surface used by the exact
entropic-region
closure form of Theorem 4: the `n`-ary entropy function `entropyFnN`, the generic cone
predicates
`zhangYeungAtN` and `zhangYeungHoldsN`, the Shannon and entropic region sets, and the
restriction
map from `Fin n` down to the first four coordinates. Witness-specific `Fin n` lemmas
(the lifted
witness and its cone membership / violation) live in `ZhangYeung.Theorem4`.
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory
open scoped Topology

universe u

/-- `IF` generalized to `Finset (Fin n)`. -/
def IFN {n : ℕ} (F : Finset (Fin n) → ℝ) (α β : Finset (Fin n)) : ℝ :=
  F α + F β - F (α ∪ β)

/-- `condIF` generalized to `Finset (Fin n)`. -/
def condIFN {n : ℕ} (F : Finset (Fin n) → ℝ) (α β γ : Finset (Fin n)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ

/-- `deltaF` generalized to `Finset (Fin n)`. -/
def deltaFN {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : ℝ :=
  IFN F {i} {j} - condIFN F {i} {j} {k} - condIFN F {i} {j} {l}

/-- `Γ_n` (paper eq. 11) as a predicate on `Finset (Fin n) → ℝ`. -/
def shannonConeN {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin n), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin n), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)

/-- The Zhang-Yeung inequality at a 4-tuple labeling over `Fin n`. -/
def zhangYeungAtN {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : Prop :=
  deltaFN F i j k l ≤ (1 / 2) * (IFN F {k} {l} + IFN F {k} ({i} ∪ {j})
    + condIFN F {i} {j} {k} - condIFN F {i} {j} {l})

/--
The `Fin n`-indexed Zhang-Yeung cone `tildeΓ_n`: the Zhang-Yeung inequality holds at
every ordered
4-tuple of pairwise distinct indices. This "pairwise-distinctness" presentation is
extensionally
equivalent to the paper's card-4 form (eq. 25) quantified over `Equiv.Perm (Fin n)` —
every
permutation yields a pairwise-distinct 4-tuple, and every pairwise-distinct 4-tuple
extends to a
permutation — but it is easier to manipulate in proofs, so the `Fin n` lift uses it in
place of the
`Equiv.Perm` form that `zhangYeungHolds` uses at `n = 4`. The point-level predicate
`zhangYeungAtN` does agree definitionally with `zhangYeungAt` at `n = 4` (pinned by
`Iff.rfl` in
the test module); the quantifier shapes of `zhangYeungHoldsN` and `zhangYeungHolds`
differ, so
their equivalence at `n = 4` is extensional rather than definitional.
-/
def zhangYeungHoldsN {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    zhangYeungAtN F i j k l

/--
The entropy function of an `n`-variable random-variable family `X : ∀ i : Fin n, Ω → S
i`,
expressed as a set function on `Finset (Fin n)`.
-/
noncomputable def entropyFnN
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) : Finset (Fin n) → ℝ :=
  fun α => H[(fun ω : Ω => fun i : α => X i.1 ω); μ]

/--
The original four-variable entropy function surface, now as the `n = 4` specialization
of
`entropyFnN`.
-/
noncomputable abbrev entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) : Finset (Fin 4) → ℝ :=
  entropyFnN X μ

/--
The Shannon outer bound `Γ_n`, packaged as a set. Membership is definitionally
`shannonConeN`.
-/
def shannonRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | shannonConeN F}

/--
The entropic region `Γ_n^*`, packaged as the set of actual entropy functions of `n`
discrete random
variables. The quantified probability space and codomain family range over the ambient
universe
`u`, so a `Type u` realization is literally a member of the set.
-/
def entropyRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type u) (_ : ∀ i, MeasurableSpace (S i)) (_ : ∀ i, Fintype (S i))
      (_ : ∀ i, MeasurableSingletonClass (S i))
      (X : ∀ i : Fin n, Ω → S i),
      (∀ i, Measurable (X i)) ∧ F = entropyFnN X μ}

/--
The almost-entropic region `closure (Γ_n^*)`. Inherits the universe parameter from
`entropyRegionN`: the closure is taken in the same ambient universe `u`, so a point
witnessed by a
`Type u` entropy function (or a limit of such) is literally a member of the set.
-/
def almostEntropicRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  closure (entropyRegionN.{u} n)

/-- Restrict a set function on `Fin n` to its first four coordinates. -/
def restrictFirstFour {n : ℕ} (hn : 4 ≤ n) :
    (Finset (Fin n) → ℝ) → (Finset (Fin 4) → ℝ) :=
  fun F α => F (α.map (Fin.castLEEmb hn))

/-- `restrictFirstFour` is continuous in the pointwise topology. -/
theorem restrictFirstFour_continuous {n : ℕ} (hn : 4 ≤ n) :
  Continuous (restrictFirstFour hn) := by
  refine continuous_pi fun α => ?_
  simpa [restrictFirstFour] using (continuous_apply (α.map (Fin.castLEEmb hn)))

/--
Restricting an `n`-variable entropy function to the first four coordinates agrees with
taking the
entropy function of the restricted family.
-/
theorem entropyFnN_restrictFirstFour
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin n, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) (hn : 4 ≤ n) :
    restrictFirstFour hn (entropyFnN X μ) =
      entropyFnN (fun i : Fin 4 => X (Fin.castLE hn i)) μ := by
  letI : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  ext α
  let e : Fin 4 ↪ Fin n := Fin.castLEEmb hn
  let π : (∀ j : α.map e, S j.1) → (∀ i : α, S (e i.1)) :=
    fun g i => g ⟨e i.1, by exact (Finset.mem_map' e).2 i.2⟩
  have hπ : Function.Injective π := by
    intro g₁ g₂ hMapEq
    funext j
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
    have hValueEq : g₁ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ =
        g₂ ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ :=
      congrFun hMapEq ⟨i, hi⟩
    have hj : j = ⟨e i, by simpa using (Finset.mem_map' e).2 hi⟩ := by
      apply Subtype.ext
      exact hij.symm
    cases hj
    simpa using hValueEq
  have h_meas : Measurable (fun ω : Ω => fun j : α.map e => X j.1 ω) :=
    measurable_pi_lambda _ (fun j => hX j.1)
  have h_ent := entropy_comp_of_injective μ h_meas π hπ
  change H[(fun ω : Ω => fun j : α.map e => X j.1 ω); μ] =
    H[(fun ω : Ω => fun i : α => X (e i.1) ω); μ]
  simpa [π, Function.comp_def] using h_ent.symm

/-- Entropic points remain entropic after restriction to the first four coordinates. -/
theorem restrictFirstFour_mem_entropyRegionN
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ entropyRegionN.{u} n) :
    restrictFirstFour hn F ∈ entropyRegionN.{u} 4 := by
  rcases hF with ⟨Ω, hΩ, μ, hμ, S, hS, hFin, hMSC, X, hX, rfl⟩
  letI : MeasurableSpace Ω := hΩ
  letI : IsProbabilityMeasure μ := hμ
  letI : ∀ i, MeasurableSpace (S i) := hS
  letI : ∀ i, Fintype (S i) := hFin
  letI : ∀ i, MeasurableSingletonClass (S i) := hMSC
  refine ⟨Ω, inferInstance, μ, inferInstance, (fun i : Fin 4 => S (Fin.castLE hn i)),
    inferInstance,
    inferInstance, inferInstance, (fun i : Fin 4 => X (Fin.castLE hn i)), ?_, ?_⟩
  · intro i
    exact hX (Fin.castLE hn i)
  · simpa using entropyFnN_restrictFirstFour hX μ hn

/--
Almost-entropic points remain almost entropic after restriction to the first four
coordinates.
-/
theorem restrictFirstFour_mem_almostEntropicRegionN
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ almostEntropicRegionN.{u} n) :
    restrictFirstFour hn F ∈ almostEntropicRegionN.{u} 4 := by
  have h_map : Set.MapsTo (restrictFirstFour hn) (entropyRegionN.{u} n) (entropyRegionN.{u} 4) :=
    fun _ h_mem => restrictFirstFour_mem_entropyRegionN hn h_mem
  simpa [almostEntropicRegionN] using h_map.closure (restrictFirstFour_continuous hn) hF

end ZhangYeung
