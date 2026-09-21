/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpRestrict
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MeasureClass

/-!
# A countable family of measures, assembled into one

For a sequence of measures `μ : ℕ → Measure X` the **slice sum**

```text
sliceSum μ := ∑ₙ (μ n).map (x ↦ (x, n))
```

is a single measure on `X × ℕ` whose `L²` space is the Hilbert sum of the `L²(μ n)`, with the
multiplication operator by `g ∘ Prod.fst` matching multiplication by `g` on each summand.

This is what converts a *direct sum of multiplication models* into a *single* multiplication
model.  It is the step that makes the rest of multiplicity theory pure measure theory: once a
normal operator is presented as multiplication by the spectral coordinate on one `L²` space, the
remaining normalisation -- dominating the measures, passing to level sets, rearranging the
fibres -- happens entirely inside `Measure (X × ℕ)` and is transported back by the
Radon--Nikodym unitary and the relabelling unitary, never touching the Hilbert space again.

## Main results

* `TauCeti.sliceSum`: the measure.
* `TauCeti.restrict_sliceSum`: its restriction to the `n`-th slice is the pushforward of `μ n`.
* `TauCeti.sliceLp`: the `n`-th summand embedding.
* `TauCeti.isHilbertSum_sliceLp`: **`L²(sliceSum μ)` is the Hilbert sum of the `L²(μ n)`.**
* `TauCeti.sliceLp_mulLp`: the embeddings intertwine the multiplication operators.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

section CongrMeasure

variable {α : Type*} [MeasurableSpace α]

/-- Transporting `L²` along an equality of measures.  Needed because the slice decomposition
produces `L²` of a *restriction* while the summand is `L²` of a *pushforward*, and the two
measures are equal but not syntactically so. -/
noncomputable def lpCongrMeasure {μ ν : Measure α} (h : μ = ν) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν :=
  h ▸ LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ)

/-- Transporting along an equality of measures commutes with multiplication -- trivially, once
the equality is substituted away, but the statement is what call sites need. -/
theorem lpCongrMeasure_mulLp {μ ν : Measure α} (h : μ = ν) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 μ) :
    lpCongrMeasure h (mulLp μ hg hgC F) = mulLp ν hg hgC (lpCongrMeasure h F) := by
  subst h
  rfl

/-- **Transport along an equality of measures is `star`-equivariant** -- trivially, once the
equality is substituted away, but the statement is what the real-part transfer needs. -/
theorem star_lpCongrMeasure {μ ν : Measure α} (h : μ = ν) (F : Lp ℂ 2 μ) :
    star (lpCongrMeasure h F) = lpCongrMeasure h (star F) := by
  subst h
  rfl

end CongrMeasure

section HilbertSumTransport

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
variable {G G' : ι → Type*}
variable [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
variable [∀ i, NormedAddCommGroup (G' i)] [∀ i, InnerProductSpace ℂ (G' i)]

/-- **A Hilbert sum decomposition transports along unitaries of the summands.**

Precomposing each summand embedding with a unitary changes neither orthogonality nor the range,
so the decomposition survives verbatim.  This is how a decomposition into `L²` spaces of
restrictions becomes one into `L²` spaces of the original measures. -/
theorem isHilbertSum_comp_linearIsometryEquiv [∀ i, CompleteSpace (G i)]
    [∀ i, CompleteSpace (G' i)]
    {V : ∀ i, G i →ₗᵢ[ℂ] E} (h : IsHilbertSum ℂ G V) (e : ∀ i, G' i ≃ₗᵢ[ℂ] G i) :
    IsHilbertSum ℂ G' fun i => (V i).comp (e i).toLinearIsometry := by
  have hrange : ∀ i, LinearMap.range ((V i).comp (e i).toLinearIsometry).toLinearMap
      = LinearMap.range (V i).toLinearMap := by
    intro i
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨e i v, rfl⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨(e i).symm w, by simp⟩
  refine IsHilbertSum.mk (fun i j hij v w => ?_) ?_
  · exact h.OrthogonalFamily hij (e i v) (e j w)
  · have htop : LinearMap.range h.OrthogonalFamily.linearIsometry.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr h.surjective_isometry
    rw [h.OrthogonalFamily.range_linearIsometry] at htop
    simp only [hrange]
    exact htop.ge

end HilbertSumTransport

section SliceSum

variable {X : Type*} [MeasurableSpace X]

/-- The inclusion of `X` as the `n`-th slice of `X × ℕ`. -/
def sliceMap (n : ℕ) : X → X × ℕ := fun x => (x, n)

/-- The slice inclusion is measurable. -/
theorem measurable_sliceMap (n : ℕ) : Measurable (sliceMap (X := X) n) :=
  measurable_id.prodMk measurable_const

/-- The slice inclusion is a measurable embedding, so `L²` transports along it. -/
theorem measurableEmbedding_sliceMap (n : ℕ) : MeasurableEmbedding (sliceMap (X := X) n) :=
  measurableEmbedding_prod_mk_right n

/-- The `n`-th slice of `X × ℕ`. -/
def slice (n : ℕ) : Set (X × ℕ) := {p | p.2 = n}

/-- A slice is measurable, the index type being discrete. -/
theorem measurableSet_slice (n : ℕ) : MeasurableSet (slice (X := X) n) :=
  measurable_snd (measurableSet_singleton n)

omit [MeasurableSpace X] in
/-- Distinct slices are disjoint. -/
theorem pairwise_disjoint_slice :
    Pairwise fun m n => Disjoint (slice (X := X) m) (slice n) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun p hpm hpn => hmn ?_
  rw [← hpm, ← hpn]

omit [MeasurableSpace X] in
/-- The slices cover `X × ℕ`; together with disjointness they are a countable measurable
partition, which is what the decomposition theorem consumes. -/
theorem iUnion_slice : (⋃ n, slice (X := X) n) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  exact Set.mem_iUnion.mpr ⟨p.2, rfl⟩

/-- **The slice sum** of a sequence of measures: a single measure on `X × ℕ` carrying the whole
family, the `n`-th member sitting on the `n`-th slice. -/
noncomputable def sliceSum (μ : ℕ → Measure X) : Measure (X × ℕ) :=
  Measure.sum fun n => (μ n).map (sliceMap n)

omit [MeasurableSpace X] in
/-- Membership in a slice, unfolded.  Stated so that consumers outside this module can use it
without the definition having to be exposed. -/
theorem mem_slice {n : ℕ} {p : X × ℕ} : p ∈ slice (X := X) n ↔ p.2 = n := Iff.rfl

/-- **The slice sum restricted to a slice is the pushforward of that member.** -/
theorem restrict_sliceSum (μ : ℕ → Measure X) (n : ℕ) :
    (sliceSum μ).restrict (slice n) = (μ n).map (sliceMap n) := by
  rw [sliceSum, Measure.restrict_sum _ (measurableSet_slice n)]
  refine Measure.ext fun t ht => ?_
  rw [Measure.sum_apply _ ht, tsum_eq_single n ?_]
  · rw [Measure.restrict_apply ht,
      Measure.map_apply (measurable_sliceMap n) (ht.inter (measurableSet_slice n)),
      Measure.map_apply (measurable_sliceMap n) ht]
    congr 1
    refine Set.ext fun x => ?_
    simp [sliceMap, slice]
  · intro m hm
    rw [Measure.restrict_apply ht,
      Measure.map_apply (measurable_sliceMap m) (ht.inter (measurableSet_slice n))]
    convert measure_empty (μ := μ m)
    refine Set.ext fun x => ?_
    simp [sliceMap, slice, hm]

/-- The slice sum, evaluated: a countable sum of the members' measures of the fibres. -/
theorem sliceSum_apply (μ : ℕ → Measure X) {t : Set (X × ℕ)} (ht : MeasurableSet t) :
    sliceSum μ t = ∑' n, μ n {x | (x, n) ∈ t} := by
  rw [sliceSum, Measure.sum_apply _ ht]
  exact tsum_congr fun n => Measure.map_apply (measurable_sliceMap n) ht

/-- The slice sum gives each slice the total mass of the corresponding member. -/
theorem sliceSum_slice (μ : ℕ → Measure X) (n : ℕ) :
    sliceSum μ (slice n) = μ n Set.univ := by
  rw [sliceSum_apply _ (measurableSet_slice n), tsum_eq_single n ?_]
  · congr 1
    refine Set.ext fun x => ?_
    simp [slice]
  · intro m hm
    convert measure_empty (μ := μ m)
    refine Set.ext fun x => ?_
    simp [slice, hm]

/-- **The slice sum, pushed forward along the first coordinate, is the sum of its members.**

Forgetting which slice a point came from collapses the whole family onto one measure.  This is
what identifies the measure class of a multiplication model on `X × ℕ` with a measure class on
`X`. -/
theorem map_fst_sliceSum (μ : ℕ → Measure X) :
    (sliceSum μ).map Prod.fst = Measure.sum μ := by
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply measurable_fst ht, sliceSum_apply _ (measurable_fst ht),
    Measure.sum_apply _ ht]
  exact tsum_congr fun n => by congr 1

/-- **The slice sum of finite measures is σ-finite**, the slices themselves being the spanning
sets.  This is what lets the Radon--Nikodym unitary apply to slice sums. -/
instance sigmaFinite_sliceSum (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] :
    SigmaFinite (sliceSum μ) := by
  refine ⟨⟨⟨fun n => slice n, fun _ => trivial, fun n => ?_, iUnion_slice⟩⟩⟩
  rw [sliceSum_slice]
  exact measure_lt_top _ _

/-- **Slice sums of equivalent families are equivalent.**  Measure class is checked fibrewise,
and a countable sum in `ℝ≥0∞` vanishes exactly when every term does. -/
theorem measureEquiv_sliceSum {μ ν : ℕ → Measure X} (h : ∀ n, MeasureEquiv (μ n) (ν n)) :
    MeasureEquiv (sliceSum μ) (sliceSum ν) := by
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
    rw [sliceSum_apply _ ht, ENNReal.tsum_eq_zero] at h0 ⊢
    exact fun n => (h n).1 (h0 n)
  · refine Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
    rw [sliceSum_apply _ ht, ENNReal.tsum_eq_zero] at h0 ⊢
    exact fun n => (h n).2 (h0 n)

/-- **The Lebesgue integral against a slice sum** is the sum of the sliced integrals. -/
theorem lintegral_sliceSum (μ : ℕ → Measure X) {f : X × ℕ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(sliceSum μ) = ∑' n, ∫⁻ x, f (x, n) ∂(μ n) := by
  rw [sliceSum, lintegral_sum_measure]
  exact tsum_congr fun n => lintegral_map hf (measurable_sliceMap n)

/-- **The Bochner integral against a slice sum** is the sum of the sliced integrals. -/
theorem integral_sliceSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ℕ → Measure X) {f : X × ℕ → E} (hf : Integrable f (sliceSum μ)) :
    ∫ p, f p ∂(sliceSum μ) = ∑' n, ∫ x, f (x, n) ∂(μ n) := by
  rw [sliceSum] at hf ⊢
  rw [integral_sum_measure hf]
  exact tsum_congr fun n => integral_map (measurable_sliceMap n).aemeasurable
    (hf.mono_measure (Measure.le_sum _ n)).aestronglyMeasurable

/-- A property holding almost everywhere on every slice holds almost everywhere for the slice
sum.  Converse of `ae_sliceSum`. -/
theorem ae_sliceSum_of_forall {μ : ℕ → Measure X} {p : X × ℕ → Prop}
    (h : ∀ n, ∀ᵐ x ∂(μ n), p (x, n)) : ∀ᵐ q ∂(sliceSum μ), p q := by
  rw [ae_iff]
  have hN : ∀ n, ∃ N : Set X, MeasurableSet N ∧ μ n N = 0 ∧ {x | ¬ p (x, n)} ⊆ N := by
    intro n
    refine ⟨toMeasurable (μ n) {x | ¬ p (x, n)}, measurableSet_toMeasurable _ _, ?_,
      subset_toMeasurable _ _⟩
    rw [measure_toMeasurable]
    exact (ae_iff.mp (h n))
  choose N hNm hN0 hNsub using hN
  refine measure_mono_null (t := ⋃ n, N n ×ˢ ({n} : Set ℕ)) ?_ ?_
  · rintro ⟨x, n⟩ hq
    exact Set.mem_iUnion.mpr ⟨n, hNsub n hq, rfl⟩
  · have hmeas : MeasurableSet (⋃ n, N n ×ˢ ({n} : Set ℕ)) :=
      MeasurableSet.iUnion fun n => (hNm n).prod (measurableSet_singleton n)
    rw [sliceSum_apply _ hmeas, ENNReal.tsum_eq_zero]
    intro n
    refine measure_mono_null (t := N n) (fun x hx => ?_) (hN0 n)
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hx1, hx2⟩ := hm
    have : n = m := hx2
    exact this ▸ hx1

/-- An almost-everywhere property for a slice sum holds almost everywhere on every slice. -/
theorem ae_sliceSum {μ : ℕ → Measure X} {p : X × ℕ → Prop}
    (h : ∀ᵐ q ∂(sliceSum μ), p q) (n : ℕ) : ∀ᵐ x ∂(μ n), p (x, n) := by
  rw [ae_iff] at h ⊢
  set t := toMeasurable (sliceSum μ) {q | ¬ p q} with ht
  have htm : MeasurableSet t := measurableSet_toMeasurable _ _
  have ht0 : sliceSum μ t = 0 := by rw [ht, measure_toMeasurable, h]
  rw [sliceSum_apply _ htm, ENNReal.tsum_eq_zero] at ht0
  refine measure_mono_null (t := {x | (x, n) ∈ t}) (fun x hx => ?_) (ht0 n)
  exact subset_toMeasurable _ _ hx

/-- The `n`-th summand, identified with `L²` of the slice restriction. -/
noncomputable def sliceLpEquiv (μ : ℕ → Measure X) (n : ℕ) :
    Lp ℂ 2 (μ n) ≃ₗᵢ[ℂ] Lp ℂ 2 ((sliceSum μ).restrict (slice n)) :=
  (embLpEquiv (measurableEmbedding_sliceMap n) (μ n)).symm.trans
    (lpCongrMeasure (restrict_sliceSum μ n).symm)

/-- **The `n`-th summand embedding** `L²(μ n) →ₗᵢ[ℂ] L²(sliceSum μ)`. -/
noncomputable def sliceLp (μ : ℕ → Measure X) (n : ℕ) :
    Lp ℂ 2 (μ n) →ₗᵢ[ℂ] Lp ℂ 2 (sliceSum μ) :=
  (extendLp (sliceSum μ) (measurableSet_slice n)).comp (sliceLpEquiv μ n).toLinearIsometry

/-- **`L²` of the slice sum is the Hilbert sum of the `L²` spaces of the members.** -/
theorem isHilbertSum_sliceLp (μ : ℕ → Measure X) :
    IsHilbertSum ℂ (fun n => Lp ℂ 2 (μ n)) (sliceLp μ) :=
  isHilbertSum_comp_linearIsometryEquiv (E := Lp ℂ 2 (sliceSum μ))
    (isHilbertSum_extendLp (sliceSum μ) (fun n => measurableSet_slice (X := X) n)
      pairwise_disjoint_slice (by rw [iUnion_slice, Set.compl_univ, measure_empty]))
    (sliceLpEquiv μ)

/-- **The summand embeddings intertwine the multiplication operators.**  Multiplication by `g`
on `L²(μ n)` becomes multiplication by `g ∘ Prod.fst` on `L²(sliceSum μ)`: the assembled model
multiplies by the *first* coordinate, so the slice index is a passive label. -/
theorem sliceLp_mulLp (μ : ℕ → Measure X) (n : ℕ) {g : X → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 (μ n)) :
    sliceLp μ n (mulLp (μ n) hg hgC F)
      = mulLp (sliceSum μ) (hg.comp measurable_fst) (fun p => hgC p.1) (sliceLp μ n F) := by
  have h1 : (embLpEquiv (measurableEmbedding_sliceMap (X := X) n) (μ n)).symm
        (mulLp (μ n) hg hgC F)
      = mulLp ((μ n).map (sliceMap n)) (hg.comp measurable_fst) (fun p => hgC p.1)
        ((embLpEquiv (measurableEmbedding_sliceMap (X := X) n) (μ n)).symm F) :=
    embLpEquiv_symm_mulLp (measurableEmbedding_sliceMap n) (μ n) (hg.comp measurable_fst)
      (fun p => hgC p.1) F
  have h2 := lpCongrMeasure_mulLp (restrict_sliceSum μ n).symm (hg.comp measurable_fst)
    (fun p : X × ℕ => hgC p.1)
    ((embLpEquiv (measurableEmbedding_sliceMap (X := X) n) (μ n)).symm F)
  have hstep : sliceLpEquiv μ n (mulLp (μ n) hg hgC F)
      = mulLp ((sliceSum μ).restrict (slice n)) (hg.comp measurable_fst) (fun p => hgC p.1)
        (sliceLpEquiv μ n F) := by
    simp only [sliceLpEquiv, LinearIsometryEquiv.trans_apply]
    rw [h1, h2]
  simp only [sliceLp, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hstep, extendLp_mulLp]

/-- **The summand identification is `star`-equivariant**, being built from the pushforward
unitary and a transport along an equality of measures, both of which are. -/
theorem star_sliceLpEquiv (μ : ℕ → Measure X) (n : ℕ) (F : Lp ℂ 2 (μ n)) :
    star (sliceLpEquiv μ n F) = sliceLpEquiv μ n (star F) := by
  simp only [sliceLpEquiv, LinearIsometryEquiv.trans_apply]
  rw [star_lpCongrMeasure, star_embLpEquiv_symm]

/-- **The summand embeddings are `star`-equivariant.**  With
`TauCeti.star_compLp`, `TauCeti.star_extendLp` and `TauCeti.star_rnDerivL2Equiv`, this completes
the list of assembly steps of the multiplicity model that carry the `star`-fixed classes of one
`L²` space into those of the next. -/
theorem star_sliceLp (μ : ℕ → Measure X) (n : ℕ) (F : Lp ℂ 2 (μ n)) :
    star (sliceLp μ n F) = sliceLp μ n (star F) := by
  simp only [sliceLp, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [star_extendLp, star_sliceLpEquiv]

end SliceSum

end TauCeti
