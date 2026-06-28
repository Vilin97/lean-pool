/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.ENat.Basic
import LeanPool.OrdvecFormalization.FiniteFiberTopology
import LeanPool.OrdvecFormalization.QuotientRefinementKernel

/-!
# Finite observation windows

This file turns the Takens-style observation-window idea into a generic
quotient/kernel API.  A single lossy observation may be non-injective, but a
finite family or prefix window of lossy observations has a joint code whose
kernel is the intersection of the coordinate kernels.

The production-relevant target is usually not full injectivity.  It is target
separation: two observations with the same whole window code must have the same
target behavior.
-/

namespace OrdvecFormalization

open Function

/-! ## Arbitrary observation families -/

/-- Joint code induced by an arbitrary family of observations. -/
def observationFamilyMap {Ω ι Z : Type} (obs : ι → Ω → Z) : Ω → ι → Z :=
  fun ω i => obs i ω

@[simp]
theorem observationFamilyMap_apply {Ω ι Z : Type}
    (obs : ι → Ω → Z) (ω : Ω) (i : ι) :
    observationFamilyMap obs ω i = obs i ω :=
  rfl

/-- Two observations agree on every coordinate of a family. -/
def ObservationFamilyAgreement {Ω ι Z : Type}
    (obs : ι → Ω → Z) (ω₁ ω₂ : Ω) : Prop :=
  ∀ i : ι, obs i ω₁ = obs i ω₂

/-- A family separates points when coordinatewise agreement forces equality. -/
def ObservationFamilySeparates {Ω ι Z : Type}
    (obs : ι → Ω → Z) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, ObservationFamilyAgreement obs ω₁ ω₂ → ω₁ = ω₂

/-- A family is sufficient for a target when coordinatewise agreement preserves the target. -/
def ObservationFamilyTargetInvariant {Ω ι Z A : Type}
    (obs : ι → Ω → Z) (target : Ω → A) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄,
    ObservationFamilyAgreement obs ω₁ ω₂ → target ω₁ = target ω₂

/-- Equality of family codes is coordinatewise agreement. -/
theorem observationFamilyMap_eq_iff {Ω ι Z : Type}
    (obs : ι → Ω → Z) (ω₁ ω₂ : Ω) :
    observationFamilyMap obs ω₁ = observationFamilyMap obs ω₂ ↔
      ObservationFamilyAgreement obs ω₁ ω₂ := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- The kernel of the family map is coordinatewise agreement. -/
theorem kernel_observationFamilyMap_iff {Ω ι Z : Type}
    (obs : ι → Ω → Z) (ω₁ ω₂ : Ω) :
    Kernel (observationFamilyMap obs) ω₁ ω₂ ↔
      ObservationFamilyAgreement obs ω₁ ω₂ := by
  exact observationFamilyMap_eq_iff obs ω₁ ω₂

/-- Family-map injectivity is exactly point separation by coordinate agreement. -/
theorem observationFamilyMap_injective_iff_separates {Ω ι Z : Type}
    (obs : ι → Ω → Z) :
    Function.Injective (observationFamilyMap obs) ↔
      ObservationFamilySeparates obs := by
  constructor
  · intro hinj ω₁ ω₂ hagree
    exact hinj ((observationFamilyMap_eq_iff obs ω₁ ω₂).mpr hagree)
  · intro hsep ω₁ ω₂ hcode
    exact hsep ((observationFamilyMap_eq_iff obs ω₁ ω₂).mp hcode)

/-- Family target-invariance is exactly kernel containment for the joint code. -/
theorem kernelContainedInTarget_familyMap_iff_targetInvariant {Ω ι Z A : Type}
    (obs : ι → Ω → Z) (target : Ω → A) :
    KernelContainedInTarget (observationFamilyMap obs) target ↔
      ObservationFamilyTargetInvariant obs target := by
  constructor
  · intro hker ω₁ ω₂ hagree
    exact hker ((kernel_observationFamilyMap_iff obs ω₁ ω₂).mpr hagree)
  · intro hinv ω₁ ω₂ hker
    exact hinv ((kernel_observationFamilyMap_iff obs ω₁ ω₂).mp hker)

/--
Factoring through the reachable image of a family map is exactly target
invariance on the family fibers.
-/
theorem ruleFactorsThrough_familyMap_image_iff_targetInvariant {Ω ι Z A : Type}
    [Fintype Ω] [DecidableEq (ι → Z)]
    (obs : ι → Ω → Z) (target : Ω → A) :
    RuleFactorsThrough (imageQuotient (observationFamilyMap obs)) target ↔
      ObservationFamilyTargetInvariant obs target := by
  rw [ruleFactorsThrough_image_iff_kernelContainedInTarget,
    kernelContainedInTarget_familyMap_iff_targetInvariant]

/-! ## Prefix windows of a countable observation stream -/

/-- The finite prefix window of a countable observation stream. -/
def windowMap {Ω Z : Type} (obs : ℕ → Ω → Z) (k : ℕ) : Ω → Fin k → Z :=
  fun ω i => obs i.val ω

@[simp]
theorem windowMap_apply {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (ω : Ω) (i : Fin k) :
    windowMap obs k ω i = obs i.val ω :=
  rfl

/-- Two points agree on all observations in the first `k` coordinates. -/
def WindowAgreement {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (ω₁ ω₂ : Ω) : Prop :=
  ∀ i : Fin k, obs i.val ω₁ = obs i.val ω₂

/-- The prefix window separates points when window agreement forces equality. -/
def WindowSeparates {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) : Prop :=
  Function.Injective (windowMap obs k)

/-- The prefix window is target-sufficient when window agreement preserves the target. -/
def WindowTargetInvariant {Ω Z A : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (target : Ω → A) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, WindowAgreement obs k ω₁ ω₂ → target ω₁ = target ω₂

/-- Equality of prefix-window codes is coordinatewise agreement on the prefix. -/
theorem windowMap_eq_iff {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (ω₁ ω₂ : Ω) :
    windowMap obs k ω₁ = windowMap obs k ω₂ ↔
      WindowAgreement obs k ω₁ ω₂ := by
  exact observationFamilyMap_eq_iff (fun i : Fin k => obs i.val) ω₁ ω₂

/-- The prefix-window kernel is agreement on every coordinate in the prefix. -/
theorem kernel_windowMap_iff {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (ω₁ ω₂ : Ω) :
    Kernel (windowMap obs k) ω₁ ω₂ ↔
      WindowAgreement obs k ω₁ ω₂ := by
  exact windowMap_eq_iff obs k ω₁ ω₂

/-- Window injectivity is exactly point separation by the finite prefix. -/
theorem windowSeparates_iff {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) :
    WindowSeparates obs k ↔
      ∀ ⦃ω₁ ω₂ : Ω⦄, WindowAgreement obs k ω₁ ω₂ → ω₁ = ω₂ := by
  exact observationFamilyMap_injective_iff_separates (fun i : Fin k => obs i.val)

/-- Window target-invariance is exactly kernel containment for the prefix code. -/
theorem kernelContainedInTarget_windowMap_iff_targetInvariant {Ω Z A : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (target : Ω → A) :
    KernelContainedInTarget (windowMap obs k) target ↔
      WindowTargetInvariant obs k target := by
  exact kernelContainedInTarget_familyMap_iff_targetInvariant
    (fun i : Fin k => obs i.val) target

/--
Factoring through the reachable image of a finite window is exactly target
invariance on the window fibers.
-/
theorem ruleFactorsThrough_windowMap_image_iff_targetInvariant {Ω Z A : Type}
    (obs : ℕ → Ω → Z) (k : ℕ)
    [Fintype Ω] [DecidableEq (Fin k → Z)]
    (target : Ω → A) :
    RuleFactorsThrough (imageQuotient (windowMap obs k)) target ↔
      WindowTargetInvariant obs k target := by
  exact ruleFactorsThrough_familyMap_image_iff_targetInvariant
    (fun i : Fin k => obs i.val) target

/-! ## Coincidence length and finite existence -/

/--
The first coordinate where two points disagree under a countable observation
stream, or `⊤` if they never disagree.
-/
noncomputable def observationCoincidenceLength {Ω Z : Type}
    (obs : ℕ → Ω → Z) (ω₁ ω₂ : Ω) : ℕ∞ :=
  open Classical in
  if h : ∃ i : ℕ, obs i ω₁ ≠ obs i ω₂ then ↑(Nat.find h) else ⊤

/--
A target-sufficient finite window exists exactly when every target-disagreeing
pair is eventually separated by some coordinate.
-/
theorem exists_windowTargetInvariant_iff_eventually_separates_target
    {Ω Z A : Type} [Finite Ω]
    (obs : ℕ → Ω → Z) (target : Ω → A) :
    (∃ k : ℕ, WindowTargetInvariant obs k target) ↔
      ∀ ω₁ ω₂ : Ω, target ω₁ ≠ target ω₂ →
        ∃ i : ℕ, obs i ω₁ ≠ obs i ω₂ := by
  constructor
  · rintro ⟨k, hinv⟩ ω₁ ω₂ htarget
    by_contra hnone
    have hall : ∀ i : ℕ, obs i ω₁ = obs i ω₂ := by
      intro i
      by_contra hneq
      exact hnone ⟨i, hneq⟩
    exact htarget (hinv fun i => hall i.val)
  · intro heventual
    classical
    let _ := Fintype.ofFinite Ω
    let idx : Ω → Ω → ℕ := fun ω₁ ω₂ =>
      if htarget : target ω₁ = target ω₂ then
        0
      else
        Classical.choose (heventual ω₁ ω₂ htarget)
    use (Finset.univ.sup fun ω₁ =>
      Finset.univ.sup fun ω₂ => idx ω₁ ω₂) + 1
    intro ω₁ ω₂ hagree
    by_cases htarget : target ω₁ = target ω₂
    · exact htarget
    · have hle : idx ω₁ ω₂ ≤
          Finset.univ.sup fun ω₁' =>
            Finset.univ.sup fun ω₂' => idx ω₁' ω₂' :=
        Finset.le_sup_of_le (Finset.mem_univ ω₁)
          (Finset.le_sup_of_le (Finset.mem_univ ω₂) le_rfl)
      have hlt : idx ω₁ ω₂ <
          (Finset.univ.sup fun ω₁' =>
            Finset.univ.sup fun ω₂' => idx ω₁' ω₂') + 1 := by
        omega
      have hdiff : obs (idx ω₁ ω₂) ω₁ ≠ obs (idx ω₁ ω₂) ω₂ := by
        unfold idx
        rw [dif_neg htarget]
        exact Classical.choose_spec (heventual ω₁ ω₂ htarget)
      exact (hdiff (hagree ⟨idx ω₁ ω₂, hlt⟩)).elim

/--
A fully separating finite window exists exactly when every distinct pair is
eventually separated by some coordinate.  This is the generic Takens-style
finite existence theorem.
-/
theorem exists_windowSeparates_iff_eventually_separates
    {Ω Z : Type} [Finite Ω]
    (obs : ℕ → Ω → Z) :
    (∃ k : ℕ, WindowSeparates obs k) ↔
      ∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → ∃ i : ℕ, obs i ω₁ ≠ obs i ω₂ := by
  constructor
  · rintro ⟨k, hsep⟩ ω₁ ω₂ hne
    by_contra hnone
    have hall : ∀ i : ℕ, obs i ω₁ = obs i ω₂ := by
      intro i
      by_contra hneq
      exact hnone ⟨i, hneq⟩
    exact hne ((windowSeparates_iff obs k).mp hsep fun i => hall i.val)
  · intro heventual
    rcases (exists_windowTargetInvariant_iff_eventually_separates_target
        (obs := obs) (target := id)).mpr heventual with ⟨k, hinv⟩
    exact ⟨k, (windowSeparates_iff obs k).mpr hinv⟩

/-! ## Monotonicity and refinement -/

/-- A longer window refines a shorter window. -/
theorem windowMap_refines_of_le {Ω Z : Type}
    (obs : ℕ → Ω → Z) {m n : ℕ} (hmn : m ≤ n) :
    QuotientRefines (windowMap obs n) (windowMap obs m) := by
  refine ⟨fun zn i => zn ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, ?_⟩
  intro ω
  funext i
  rfl

/-- Longer-window kernel collisions are also shorter-window collisions. -/
theorem windowMap_kernel_subset_of_le {Ω Z : Type}
    (obs : ℕ → Ω → Z) {m n : ℕ} (hmn : m ≤ n) :
    ∀ ⦃ω₁ ω₂ : Ω⦄,
      Kernel (windowMap obs n) ω₁ ω₂ →
        Kernel (windowMap obs m) ω₁ ω₂ :=
  quotientRefines_kernel_subset (windowMap_refines_of_le obs hmn)

/-- Adding observations can only preserve target sufficiency. -/
theorem windowTargetInvariant_of_le {Ω Z A : Type}
    (obs : ℕ → Ω → Z) {m n : ℕ} (hmn : m ≤ n)
    {target : Ω → A}
    (h : WindowTargetInvariant obs m target) :
    WindowTargetInvariant obs n target := by
  intro ω₁ ω₂ hagree
  exact h fun i => hagree ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

/-- Anything that factors through a shorter window also factors through any longer window. -/
theorem ruleFactorsThrough_windowMap_of_le {Ω Z A : Type}
    (obs : ℕ → Ω → Z) {m n : ℕ} (hmn : m ≤ n)
    {target : Ω → A}
    (h : RuleFactorsThrough (windowMap obs m) target) :
    RuleFactorsThrough (windowMap obs n) target :=
  RuleFactorsThrough.of_refines (windowMap_refines_of_le obs hmn) h

/--
Anything that factors through the reachable image of a shorter window also
factors through the reachable image of any longer window.
-/
theorem ruleFactorsThrough_windowMap_image_of_le {Ω Z A : Type}
    (obs : ℕ → Ω → Z) {m n : ℕ} (hmn : m ≤ n)
    [Fintype Ω] [DecidableEq (Fin m → Z)] [DecidableEq (Fin n → Z)]
    {target : Ω → A}
    (h : RuleFactorsThrough (imageQuotient (windowMap obs m)) target) :
    RuleFactorsThrough (imageQuotient (windowMap obs n)) target := by
  exact (ruleFactorsThrough_windowMap_image_iff_targetInvariant obs n target).mpr
    (windowTargetInvariant_of_le obs hmn
      ((ruleFactorsThrough_windowMap_image_iff_targetInvariant obs m target).mp h))

/-! ## Sample falsifiers -/

/--
If two sampled points have the same whole window code but different labels, no
window-factorized target can fit the sample.
-/
theorem no_window_compatible_target_of_same_code_label_disagreement
    {Ω Z A : Type}
    (obs : ℕ → Ω → Z) (k : ℕ) (label : Ω → A) (sample : Finset Ω)
    {ω₁ ω₂ : Ω}
    (hω₁ : ω₁ ∈ sample) (hω₂ : ω₂ ∈ sample)
    (hwindow : WindowAgreement obs k ω₁ ω₂)
    (hlabel : label ω₁ ≠ label ω₂) :
    ¬ ∃ target : Ω → A,
      QuotientCompatible (windowMap obs k) target ∧
        FullTargetFitsSample label target sample :=
  no_compatible_target_of_sample_collision
    (windowMap obs k) label sample hω₁ hω₂
    ((windowMap_eq_iff obs k ω₁ ω₂).mpr hwindow) hlabel

/--
The same finite falsifier applies to targets factoring through the reachable
image quotient of the window.
-/
theorem no_window_image_compatible_target_of_same_code_label_disagreement
    {Ω Z A : Type}
    (obs : ℕ → Ω → Z) (k : ℕ)
    [Fintype Ω] [DecidableEq (Fin k → Z)]
    (label : Ω → A) (sample : Finset Ω)
    {ω₁ ω₂ : Ω}
    (hω₁ : ω₁ ∈ sample) (hω₂ : ω₂ ∈ sample)
    (hwindow : WindowAgreement obs k ω₁ ω₂)
    (hlabel : label ω₁ ≠ label ω₂) :
    ¬ ∃ target : Ω → A,
      RuleFactorsThrough (imageQuotient (windowMap obs k)) target ∧
        FullTargetFitsSample label target sample :=
  no_compatible_target_of_sample_collision
    (imageQuotient (windowMap obs k)) label sample hω₁ hω₂
    (Subtype.ext ((windowMap_eq_iff obs k ω₁ ω₂).mpr hwindow)) hlabel

/-- On a finite type, the number of realized window codes is at most the domain size. -/
theorem windowMap_image_card_le {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ)
    [Fintype Ω] [DecidableEq (Fin k → Z)] :
    (Finset.univ.image (windowMap obs k)).card ≤ Fintype.card Ω := by
  classical
  exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)

/-- If the window is injective, its realized image has exactly the domain size. -/
theorem windowMap_image_card_of_injective {Ω Z : Type}
    (obs : ℕ → Ω → Z) (k : ℕ)
    [Fintype Ω] [DecidableEq (Fin k → Z)]
    (h : WindowSeparates obs k) :
    (Finset.univ.image (windowMap obs k)).card = Fintype.card Ω := by
  classical
  rw [Finset.card_image_of_injective _ h, Finset.card_univ]

end OrdvecFormalization
