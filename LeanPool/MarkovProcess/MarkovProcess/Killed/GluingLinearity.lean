/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingMinimal

/-!
# Linearity of the transported local resolvents and of their supremum

The transported local resolvents of `Killed/GluingMinimal.lean` inherit additivity and
homogeneity from the kernel resolvents they extend (`localResolvent_add`,
`localResolvent_const_mul`).  Homogeneity passes to the supremum without further hypotheses
(`minimalResolvent_const_mul`), while additivity passes to it exactly when the transported
resolvents are monotone in the index, so that the two suprema can be added term by term
(`minimalResolvent_add`).

A uniformly bounded observable has a uniformly bounded supremum resolvent: at the shift `lam`
the bound is the bound of the observable divided by `lam`
(`minimalResolvent_le_of_le_const`), so the value is finite (`minimalResolvent_ne_top`).  This
is the estimate which makes the real-valued form of the supremum resolvent well defined.

The transported resolvents at two shifts commute (`localResolvent_comm`), and so do their
suprema once the family is monotone in the index (`minimalResolvent_comm`).

Nothing here uses the part-process identity; monotonicity in the index is a bare hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- The transported resolvent is additive on measurable observables. -/
theorem localResolvent_add {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ f y + g y) x =
      localResolvent R emb m lam f x + localResolvent R emb m lam g x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective lam f y,
      localResolvent_apply R emb hemb.injective lam g y]
    exact (R m).kernelSemigroup.kernelResolvent_add lam (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m lam f hx,
      localResolvent_of_notMem R emb m lam g hx, add_zero]

/-- The transported resolvent is homogeneous under multiplication by an extended-real
constant. -/
theorem localResolvent_const_mul {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ c * f y) x = c * localResolvent R emb m lam f x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective lam f y]
    exact (R m).kernelSemigroup.kernelResolvent_const_mul lam c (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m lam f hx,
      mul_zero]

/-- **The supremum resolvent is additive** on measurable observables, as soon as the transported
resolvents are monotone in the index: the suprema of two monotone families add term by term. -/
theorem minimalResolvent_add (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ f y + g y) x =
      minimalResolvent R emb lam f x + minimalResolvent R emb lam g x := by
  unfold minimalResolvent
  rw [ENNReal.iSup_add_iSup_of_monotone (hmono lam hlam hf x) (hmono lam hlam hg x)]
  exact iSup_congr fun m ↦ localResolvent_add R emb (hemb m) lam hf x

/-- The supremum resolvent is homogeneous under multiplication by an extended-real constant. -/
theorem minimalResolvent_const_mul (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ c * f y) x = c * minimalResolvent R emb lam f x := by
  unfold minimalResolvent
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun m ↦ localResolvent_const_mul R emb (hemb m) lam c hf x

/-- **The uniform bound.**  At a positive shift, a uniform bound for the observable divided by
the shift is a uniform bound for the supremum resolvent. -/
theorem minimalResolvent_le_of_le_const (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} {c : ℝ≥0∞} (hfc : ∀ y, f y ≤ c)
    (x : alpha) :
    minimalResolvent R emb lam f x ≤ c * ENNReal.ofReal lam⁻¹ := by
  calc minimalResolvent R emb lam f x
      ≤ minimalResolvent R emb lam (fun _ ↦ c * 1) x :=
        minimalResolvent_mono_of_le R emb (fun m ↦ (hemb m).injective) lam
          (fun y ↦ by simpa using hfc y) x
    _ = c * minimalResolvent R emb lam (fun _ ↦ 1) x :=
        minimalResolvent_const_mul R emb hemb lam c measurable_const x
    _ ≤ c * ENNReal.ofReal lam⁻¹ :=
        mul_le_mul' le_rfl (minimalResolvent_one_le R emb (fun m ↦ (hemb m).injective) hlam x)

/-- At a positive shift the supremum resolvent of a uniformly bounded observable is finite. -/
theorem minimalResolvent_ne_top (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfc : ∀ y, f y ≤ c) (x : alpha) :
    minimalResolvent R emb lam f x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top)
    (minimalResolvent_le_of_le_const R emb hemb hlam hfc x)

/-- The transported resolvents at two shifts commute. -/
theorem localResolvent_comm {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam mu : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (localResolvent R emb m mu f) x =
      localResolvent R emb m mu (localResolvent R emb m lam f) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    have hinner : ∀ nu : ℝ, (fun z ↦ localResolvent R emb m nu f (emb m z)) =
        (R m).kernelSemigroup.kernelResolvent nu fun z ↦ f (emb m z) := by
      intro nu
      funext z
      exact localResolvent_apply R emb hemb.injective nu f z
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective mu _ y, hinner, hinner]
    exact (R m).kernelSemigroup.kernelResolvent_comm lam mu (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m mu _ hx]

/-- **The supremum resolvents at two shifts commute**, as soon as the transported resolvents are
monotone in the index: each composition is the supremum of the commuting compositions along the
diagonal. -/
theorem minimalResolvent_comm (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam (minimalResolvent R emb mu f) x =
      minimalResolvent R emb mu (minimalResolvent R emb lam f) x := by
  rw [minimalResolvent_comp_eq_iSup R emb hemb hmono hlam hmu hf x,
    minimalResolvent_comp_eq_iSup R emb hemb hmono hmu hlam hf x]
  exact iSup_congr fun n ↦ localResolvent_comm R emb (hemb n) lam mu hf x

/-- At a positive shift the supremum resolvent of the zero observable vanishes. -/
theorem minimalResolvent_zero (hemb : ∀ m, MeasurableEmbedding (emb m)) {lam : ℝ}
    (hlam : 0 < lam) (x : alpha) :
    minimalResolvent R emb lam (fun _ ↦ 0) x = 0 := by
  refine le_antisymm ?_ zero_le
  simpa using minimalResolvent_le_of_le_const R emb hemb hlam
    (f := fun _ : alpha ↦ (0 : ℝ≥0∞)) (c := 0) (fun _ ↦ le_rfl) x

end MarkovProcess
