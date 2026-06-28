/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment

/-!
# Finite quotient search

This file formalizes version-space reduction under a quotient contract.  A
quotient-compatible target is a bucket-level rule; same-bucket label
disagreements falsify quotient compatibility for a sample; consistent samples
fix observed buckets while leaving reachable, unobserved image buckets freely
assignable for induced full-space targets.
-/

namespace OrdvecFormalization

/-- A full-space target is compatible with a quotient if it factors through it. -/
def QuotientCompatible {Ω Ωq A : Type} (Q : Ω → Ωq) (target : Ω → A) : Prop :=
  RuleFactorsThrough Q target

/-- The quotient buckets observed by a finite sample. -/
def ObservedQuotients {Ω Ωq : Type} [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω) : Finset Ωq :=
  sample.image Q

/-- A list-facing wrapper for observed quotient buckets. -/
def ObservedQuotientsList {Ω Ωq : Type} [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : List Ω) : Finset Ωq :=
  (sample.map Q).toFinset

/-- A finite sample is consistent when labels are constant on sampled quotient fibers. -/
def SampleConsistent {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄,
    ω₁ ∈ sample →
    ω₂ ∈ sample →
    Q ω₁ = Q ω₂ →
    label ω₁ = label ω₂

/-- A quotient-level rule fits a finite labeled sample. -/
def QuotientRuleFitsSample {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω) (ruleq : Ωq → A) : Prop :=
  ∀ ⦃ω : Ω⦄, ω ∈ sample → ruleq (Q ω) = label ω

/-- A full-space target fits a finite labeled sample. -/
def FullTargetFitsSample {Ω A : Type}
    (label target : Ω → A) (sample : Finset Ω) : Prop :=
  ∀ ⦃ω : Ω⦄, ω ∈ sample → target ω = label ω

/-- Full-space targets that both factor through the quotient and fit the sample. -/
def CompatibleTargets {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω) : Set (Ω → A) :=
  {target | QuotientCompatible Q target ∧ FullTargetFitsSample label target sample}

/-- Quotient-level rules that fit the sample. -/
def CompatibleQuotientRules {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω) : Set (Ωq → A) :=
  {ruleq | QuotientRuleFitsSample Q label sample ruleq}

/-- A quotient-compatible target has a quotient-level representative. -/
theorem quotientCompatible_exists_ruleq {Ω Ωq A : Type}
    (Q : Ω → Ωq) (target : Ω → A)
    (h : QuotientCompatible Q target) :
    ∃ ruleq : Ωq → A, ∀ ω : Ω, target ω = ruleq (Q ω) :=
  h

/-- Every quotient-level rule induces a quotient-compatible full-space target. -/
theorem quotientRule_induces_compatible_target {Ω Ωq A : Type}
    (Q : Ω → Ωq) (ruleq : Ωq → A) :
    QuotientCompatible Q (fun ω : Ω => ruleq (Q ω)) := by
  exact ⟨ruleq, fun _ => rfl⟩

/-- Equal quotient-level rules induce equal full-space targets. -/
theorem induced_targets_eq_of_ruleq_eq {Ω Ωq A : Type}
    (Q : Ω → Ωq) {ruleq₁ ruleq₂ : Ωq → A}
    (h : ruleq₁ = ruleq₂) :
    (fun ω : Ω => ruleq₁ (Q ω)) = (fun ω : Ω => ruleq₂ (Q ω)) := by
  ext ω
  rw [h]

/-- Quotient-level rules that agree on the image of Q induce the same full-space target. -/
theorem induced_targets_eq_of_agree_on_range {Ω Ωq A : Type}
    (Q : Ω → Ωq) {ruleq₁ ruleq₂ : Ωq → A}
    (h : ∀ z : Ωq, z ∈ Set.range Q → ruleq₁ z = ruleq₂ z) :
    (fun ω : Ω => ruleq₁ (Q ω)) = (fun ω : Ω => ruleq₂ (Q ω)) := by
  ext ω
  exact h (Q ω) ⟨ω, rfl⟩

/-- A quotient-compatible target cannot disagree inside a sampled quotient fiber. -/
theorem sampleConsistent_of_quotientCompatible {Ω Ωq A : Type}
    (Q : Ω → Ωq) (target : Ω → A) (sample : Finset Ω)
    (h : QuotientCompatible Q target) :
    SampleConsistent Q target sample := by
  rcases h with ⟨ruleq, htarget⟩
  intro ω₁ ω₂ _hω₁ _hω₂ hQ
  rw [htarget ω₁, htarget ω₂, hQ]

/--
If two sampled points share a quotient but have different labels, no
quotient-compatible target fits the sample.
-/
theorem no_compatible_target_of_sample_collision {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    {ω₁ ω₂ : Ω}
    (hω₁ : ω₁ ∈ sample) (hω₂ : ω₂ ∈ sample)
    (hQ : Q ω₁ = Q ω₂)
    (hlabel : label ω₁ ≠ label ω₂) :
    ¬ ∃ target : Ω → A,
      QuotientCompatible Q target ∧ FullTargetFitsSample label target sample := by
  rintro ⟨target, hcompat, hfit⟩
  rcases hcompat with ⟨ruleq, htarget⟩
  have ht₁ : target ω₁ = label ω₁ := hfit hω₁
  have ht₂ : target ω₂ = label ω₂ := hfit hω₂
  have hsame : target ω₁ = target ω₂ := by
    rw [htarget ω₁, htarget ω₂, hQ]
  exact hlabel (by
    rw [← ht₁, ← ht₂]
    exact hsame)

/-- Existence of a quotient-level sample-fitting rule implies sample consistency. -/
theorem sampleConsistent_of_exists_quotientRuleFitsSample {Ω Ωq A : Type}
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    (h : ∃ ruleq : Ωq → A, QuotientRuleFitsSample Q label sample ruleq) :
    SampleConsistent Q label sample := by
  rcases h with ⟨ruleq, hfit⟩
  intro ω₁ ω₂ hω₁ hω₂ hQ
  have h₁ : ruleq (Q ω₁) = label ω₁ := hfit hω₁
  have h₂ : ruleq (Q ω₂) = label ω₂ := hfit hω₂
  rw [← h₁, ← h₂, hQ]

/-- A consistent sample admits at least one quotient-level rule fitting it. -/
theorem exists_quotientRuleFitsSample_of_sampleConsistent {Ω Ωq A : Type}
    [Inhabited A] (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    (hconsistent : SampleConsistent Q label sample) :
    ∃ ruleq : Ωq → A, QuotientRuleFitsSample Q label sample ruleq := by
  classical
  let ruleq : Ωq → A := fun z =>
    if hz : z ∈ ObservedQuotients Q sample then
      label (Classical.choose (Finset.mem_image.mp hz))
    else
      default
  refine ⟨ruleq, ?_⟩
  intro ω hω
  have hz : Q ω ∈ ObservedQuotients Q sample :=
    Finset.mem_image.mpr ⟨ω, hω, rfl⟩
  have hchosen := Classical.choose_spec (Finset.mem_image.mp hz)
  have hchosen_mem : Classical.choose (Finset.mem_image.mp hz) ∈ sample := hchosen.1
  have hchosen_Q : Q (Classical.choose (Finset.mem_image.mp hz)) = Q ω := hchosen.2
  change (if hz' : Q ω ∈ ObservedQuotients Q sample then
      label (Classical.choose (Finset.mem_image.mp hz')) else default) = label ω
  rw [dif_pos hz]
  exact hconsistent hchosen_mem hω hchosen_Q

/-- A finite labeled sample is quotient-consistent iff some quotient-level rule fits it. -/
theorem sampleConsistent_iff_exists_quotientRuleFitsSample {Ω Ωq A : Type}
    [Inhabited A] (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω) :
    SampleConsistent Q label sample ↔
      ∃ ruleq : Ωq → A, QuotientRuleFitsSample Q label sample ruleq := by
  constructor
  · exact exists_quotientRuleFitsSample_of_sampleConsistent Q label sample
  · exact sampleConsistent_of_exists_quotientRuleFitsSample Q label sample

/-- Finite image buckets of a quotient map. -/
abbrev QuotientImageFinset {Ω Ωq : Type} [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) : Finset Ωq :=
  Finset.univ.image Q

/-- The image-bucket subtype. -/
abbrev QuotientImageBucket {Ω Ωq : Type} [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) : Type :=
  {z : Ωq // z ∈ QuotientImageFinset Q}

/--
Rules on a finite reachable image have search-space size
`|A| ^ |image Q|`.
-/
theorem card_quotientImageRules {Ω Ωq A : Type}
    [Fintype Ω] [DecidableEq Ωq] [Fintype A] (Q : Ω → Ωq) :
    Fintype.card (QuotientImageBucket Q → A) =
      Fintype.card A ^ (QuotientImageFinset Q).card := by
  classical
  letI : Fintype (QuotientImageBucket Q) :=
    Fintype.ofFinset (QuotientImageFinset Q) (by
      intro z
      constructor <;> intro hz <;> exact hz)
  rw [Fintype.card_fun]
  congr
  simp [QuotientImageBucket]

/-- Reachable quotient buckets that have not appeared in a finite sample. -/
abbrev UnobservedReachableQuotients {Ω Ωq : Type}
    [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω) : Type :=
  {z : Ωq // z ∈ QuotientImageFinset Q \ ObservedQuotients Q sample}

noncomputable instance unobservedReachableQuotientsFintype {Ω Ωq : Type}
    [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω) :
    Fintype (UnobservedReachableQuotients Q sample) :=
  Fintype.ofFinset (QuotientImageFinset Q \ ObservedQuotients Q sample) (by
    intro z
    constructor <;> intro hz <;> exact hz)

/-- Restrict a quotient-level representative to image buckets. -/
def restrictRuleToImage {Ω Ωq A : Type} [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) (ruleq : Ωq → A) :
    QuotientImageBucket Q → A :=
  fun z => ruleq z.1

/-- Extend an image-bucket rule to a full-space target. -/
def imageRuleToFullTarget {Ω Ωq A : Type} [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) (ruleImg : QuotientImageBucket Q → A) :
    Ω → A :=
  fun ω => ruleImg ⟨Q ω, Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩⟩

/-- Every image-bucket rule induces a quotient-compatible full target. -/
theorem imageRuleToFullTarget_quotientCompatible {Ω Ωq A : Type}
    [Fintype Ω] [DecidableEq Ωq] [Inhabited A]
    (Q : Ω → Ωq) (ruleImg : QuotientImageBucket Q → A) :
    QuotientCompatible Q (imageRuleToFullTarget Q ruleImg) := by
  let ruleq : Ωq → A := fun z =>
    if hz : z ∈ QuotientImageFinset Q then ruleImg ⟨z, hz⟩ else default
  refine ⟨ruleq, ?_⟩
  intro ω
  have hz : Q ω ∈ QuotientImageFinset Q :=
    Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩
  change imageRuleToFullTarget Q ruleImg ω =
    (if hz' : Q ω ∈ QuotientImageFinset Q then ruleImg ⟨Q ω, hz'⟩ else default)
  rw [dif_pos hz]
  rfl

/-- Any two quotient rules fitting a sample agree on observed buckets. -/
theorem quotientRules_agree_on_observed_of_fit {Ω Ωq A : Type}
    [DecidableEq Ωq]
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    {ruleq₁ ruleq₂ : Ωq → A}
    (hfit₁ : QuotientRuleFitsSample Q label sample ruleq₁)
    (hfit₂ : QuotientRuleFitsSample Q label sample ruleq₂)
    {z : Ωq} (hz : z ∈ ObservedQuotients Q sample) :
    ruleq₁ z = ruleq₂ z := by
  rcases Finset.mem_image.mp hz with ⟨ω, hω, hQω⟩
  rw [← hQω, hfit₁ hω, hfit₂ hω]

/-- Fitting quotient rules are determined on observed buckets. -/
theorem fitting_quotient_rules_determined_on_observed {Ω Ωq A : Type}
    [DecidableEq Ωq]
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    {ruleq₁ ruleq₂ : Ωq → A}
    (hfit₁ : QuotientRuleFitsSample Q label sample ruleq₁)
    (hfit₂ : QuotientRuleFitsSample Q label sample ruleq₂) :
    ∀ ⦃z : Ωq⦄, z ∈ ObservedQuotients Q sample → ruleq₁ z = ruleq₂ z := by
  intro z hz
  exact quotientRules_agree_on_observed_of_fit Q label sample hfit₁ hfit₂ hz

/-- Extend a fitting rule by arbitrary assignments on ambient unobserved buckets. -/
def extendWithUnobserved {Ω Ωq A : Type} [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω)
    (baseq : Ωq → A)
    (freeq : {z : Ωq // z ∉ ObservedQuotients Q sample} → A) :
    Ωq → A :=
  fun z =>
    if hz : z ∈ ObservedQuotients Q sample then
      baseq z
    else
      freeq ⟨z, hz⟩

/-- Extending a fitting rule arbitrarily on ambient unobserved buckets still fits the sample. -/
theorem extendWithUnobserved_fits_sample {Ω Ωq A : Type}
    [DecidableEq Ωq]
    (Q : Ω → Ωq) (label : Ω → A) (sample : Finset Ω)
    (baseq : Ωq → A)
    (hbase : QuotientRuleFitsSample Q label sample baseq)
    (freeq : {z : Ωq // z ∉ ObservedQuotients Q sample} → A) :
    QuotientRuleFitsSample Q label sample
      (extendWithUnobserved Q sample baseq freeq) := by
  intro ω hω
  unfold extendWithUnobserved
  have hz : Q ω ∈ ObservedQuotients Q sample :=
    Finset.mem_image.mpr ⟨ω, hω, rfl⟩
  rw [dif_pos hz]
  exact hbase hω

/-- The total number of full-space targets is `|A| ^ |Ω|`. -/
theorem card_fullTargets {Ω A : Type} [DecidableEq Ω] [Fintype Ω] [Fintype A] :
    Fintype.card (Ω → A) = Fintype.card A ^ Fintype.card Ω := by
  simp

/-- The number of quotient-level rules over the quotient codomain is `|A| ^ |Ωq|`. -/
theorem card_quotientRules {Ωq A : Type} [DecidableEq Ωq] [Fintype Ωq] [Fintype A] :
    Fintype.card (Ωq → A) = Fintype.card A ^ Fintype.card Ωq := by
  simp

/-- Quotient-level rules provide an upper-bound search space for compatible targets. -/
theorem quotientCompatible_search_space_bound {Ωq A : Type}
    [DecidableEq Ωq] [Fintype Ωq] [Fintype A] :
    Fintype.card (Ωq → A) = Fintype.card A ^ Fintype.card Ωq :=
  card_quotientRules

/--
Assignments on reachable unobserved quotient buckets have cardinality
`|A| ^ |unobserved|`.
-/
theorem card_unobserved_assignments {Ω Ωq A : Type}
    [Fintype Ω] [Fintype A] [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω) :
    Fintype.card (UnobservedReachableQuotients Q sample → A) =
      Fintype.card A ^
        Fintype.card (UnobservedReachableQuotients Q sample) := by
  simp

/-- Bool assignments on reachable unobserved buckets have cardinality `2 ^ |unobserved|`. -/
theorem card_unobserved_bool_assignments {Ω Ωq : Type}
    [Fintype Ω] [DecidableEq Ωq]
    (Q : Ω → Ωq) (sample : Finset Ω) :
    Fintype.card (UnobservedReachableQuotients Q sample → Bool) =
      2 ^ Fintype.card (UnobservedReachableQuotients Q sample) := by
  rw [card_unobserved_assignments Q sample]
  simp

/-- `Qfine` refines `Qcoarse` when the coarse quotient can be computed from the fine one. -/
def QuotientRefines {Ω Ωfine Ωcoarse : Type}
    (Qfine : Ω → Ωfine) (Qcoarse : Ω → Ωcoarse) : Prop :=
  ∃ f : Ωfine → Ωcoarse, ∀ ω : Ω, Qcoarse ω = f (Qfine ω)

namespace RuleFactorsThrough

/-- Anything that factors through a coarse quotient also factors through any finer quotient. -/
theorem of_refines {Ω Ωfine Ωcoarse A : Type}
    {Qfine : Ω → Ωfine} {Qcoarse : Ω → Ωcoarse} {target : Ω → A}
    (href : QuotientRefines Qfine Qcoarse)
    (hcoarse : RuleFactorsThrough Qcoarse target) :
    RuleFactorsThrough Qfine target := by
  rcases href with ⟨f, hf⟩
  rcases hcoarse with ⟨ruleCoarse, htarget⟩
  refine ⟨fun zfine => ruleCoarse (f zfine), ?_⟩
  intro ω
  rw [htarget ω, hf ω]

/-- A paired target factors through a quotient iff both components do. -/
theorem prod_iff {Ω Ωq A B : Type}
    (Q : Ω → Ωq) (targetA : Ω → A) (targetB : Ω → B) :
    RuleFactorsThrough Q (fun ω => (targetA ω, targetB ω)) ↔
      RuleFactorsThrough Q targetA ∧ RuleFactorsThrough Q targetB := by
  constructor
  · intro hpair
    rcases hpair with ⟨ruleq, hruleq⟩
    constructor
    · refine ⟨fun z => (ruleq z).1, ?_⟩
      intro ω
      exact congrArg Prod.fst (hruleq ω)
    · refine ⟨fun z => (ruleq z).2, ?_⟩
      intro ω
      exact congrArg Prod.snd (hruleq ω)
  · rintro ⟨hA, hB⟩
    rcases hA with ⟨ruleA, hruleA⟩
    rcases hB with ⟨ruleB, hruleB⟩
    refine ⟨fun z => (ruleA z, ruleB z), ?_⟩
    intro ω
    change (targetA ω, targetB ω) = (ruleA (Q ω), ruleB (Q ω))
    rw [hruleA ω, hruleB ω]

end RuleFactorsThrough

/-- If a target does not factor through a finer quotient, it cannot factor through a coarser one. -/
theorem not_ruleFactorsThrough_coarse_of_not_fine {Ω Ωfine Ωcoarse A : Type}
    {Qfine : Ω → Ωfine} {Qcoarse : Ω → Ωcoarse} {target : Ω → A}
    (href : QuotientRefines Qfine Qcoarse)
    (hnotfine : ¬ RuleFactorsThrough Qfine target) :
    ¬ RuleFactorsThrough Qcoarse target := by
  intro hcoarse
  exact hnotfine (RuleFactorsThrough.of_refines href hcoarse)

namespace QuotientRefines

/-- Quotient refinement is reflexive. -/
theorem refl {Ω Ωq : Type} (Q : Ω → Ωq) :
    QuotientRefines Q Q :=
  ⟨id, fun _ => rfl⟩

/-- Quotient refinement is transitive. -/
theorem trans {Ω Ω₁ Ω₂ Ω₃ : Type}
    {Q₁ : Ω → Ω₁} {Q₂ : Ω → Ω₂} {Q₃ : Ω → Ω₃}
    (h12 : QuotientRefines Q₁ Q₂)
    (h23 : QuotientRefines Q₂ Q₃) :
    QuotientRefines Q₁ Q₃ := by
  rcases h12 with ⟨f12, hf12⟩
  rcases h23 with ⟨f23, hf23⟩
  refine ⟨fun z₁ => f23 (f12 z₁), ?_⟩
  intro ω
  rw [hf23 ω, hf12 ω]

end QuotientRefines

namespace SampleConsistent

/-- Product-label sample consistency is equivalent to componentwise consistency. -/
theorem prod_iff {Ω Ωq A B : Type}
    (Q : Ω → Ωq) (labelA : Ω → A) (labelB : Ω → B) (sample : Finset Ω) :
    SampleConsistent Q (fun ω => (labelA ω, labelB ω)) sample ↔
      SampleConsistent Q labelA sample ∧ SampleConsistent Q labelB sample := by
  constructor
  · intro hpair
    constructor
    · intro ω₁ ω₂ hω₁ hω₂ hQ
      exact congrArg Prod.fst (hpair hω₁ hω₂ hQ)
    · intro ω₁ ω₂ hω₁ hω₂ hQ
      exact congrArg Prod.snd (hpair hω₁ hω₂ hQ)
  · rintro ⟨hA, hB⟩
    intro ω₁ ω₂ hω₁ hω₂ hQ
    exact Prod.ext (hA hω₁ hω₂ hQ) (hB hω₁ hω₂ hQ)

end SampleConsistent

end OrdvecFormalization
