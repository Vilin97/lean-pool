/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SeparableCyclic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSumIntertwine
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MultiplicityLevels

/-!
# The multiplication model of a normal operator, in multiplicity normal form

**Every bounded normal operator on a separable complex Hilbert space is unitarily equivalent to
multiplication by the spectral coordinate on `L²` of a level-set family.**  That is the existence
half of Hahn--Hellinger, and it is what makes "same spectral multiplicity" a statement with
content rather than a statement about an opaque term.

The datum produced by the complex existence theorem is a `TauCeti.MultiplicityDatum ℂ`: a finite
measure `base` on `ℂ` supported in
a ball, together with an **antitone** sequence of measurable level sets.  Its meaning is the
usual one -- `base` carries the measure class of the operator and `k ↦ level k` is the sequence
of super-level sets of the multiplicity function -- and its `operator` is multiplication by the
spectral coordinate on the assembled `L²` space.

## The chain

1. `exists_countable_isHilbertSum_lp_diagMeasure_complex`: `H` is the Hilbert sum of the `L²`
spaces of
   the scalar spectral measures of countably many vectors, with `a` acting by coordinate
   multiplication on each.
2. `embLpEquiv`: those measures move off the `spectrum` subtype onto `ℂ`, where models of
   different operators can be compared.
3. `isHilbertSum_sliceLp`: the same family of `L²` spaces assembles into `L²` of a single measure
   on `ℂ × ℕ`, again with coordinate multiplication.
4. `operatorUnitaryEquiv_of_isHilbertSum`: two Hilbert sums of one family carry the same
   operator, so `a` *is* that multiplication operator.
5. `exists_multiplicityLevels`: the assembled measure is normalised to level-set form.

Only step 1 uses separability, and only to make the index type `ℕ` -- which the level-set
normalisation needs, since ranks count *earlier* indices.

## Main results

* `TauCeti.MultiplicityDatum`: the datum.
* `TauCeti.MultiplicityDatum.multiplicity` and `TauCeti.MultiplicityDatum.mem_level_iff`: the
  **cardinal-valued multiplicity function**, and the fact that the datum's level sets are
  exactly its super-level sets.  `measurable_multiplicity` proves it measurable.
* `TauCeti.exists_hasMultiplicityModel`: **existence of a
model.**
* `TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex`: **data agreeing up to measure class and
null
  sets present unitarily equivalent operators.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

section Coord

/-- **The spectral coordinate, truncated outside a ball.**  Multiplication operators need a
*bounded* symbol, and the coordinate is unbounded on `ℂ`; truncating outside a ball that already
contains the spectrum changes nothing where the spectral measure lives. -/
noncomputable def coordTrunc (R : ℝ) : ℂ → ℂ := fun z => if ‖z‖ ≤ R then z else 0

/-- The truncated coordinate is measurable: it is the identity on a closed sublevel set of the
norm and zero off it. -/
theorem measurable_coordTrunc (R : ℝ) : Measurable (coordTrunc R) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    measurable_const

/-- The truncated coordinate is bounded by the truncation radius -- which is the whole point of
truncating. -/
theorem norm_coordTrunc_le {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖coordTrunc R z‖ ≤ R := by
  rw [coordTrunc]
  split_ifs with h
  · exact h
  · simpa using hR

/-- Inside the ball the truncation does nothing, so a model whose measure lives there multiplies
by the coordinate itself. -/
theorem coordTrunc_eq_self {R : ℝ} {z : ℂ} (h : ‖z‖ ≤ R) : coordTrunc R z = z := ite_eq_left h

/-- The truncated spectral coordinate, interpreted in the scalar field of the model.

The underlying spectral parameter remains `ℂ`.  Only the *values* of the multiplier are changed:
`RCLike.map ℂ 𝕜` is the identity for `𝕜 = ℂ` and the real-part map for `𝕜 = ℝ`.  This is the
field axis needed by the real Hahn--Hellinger model; it deliberately does not replace the base
measure by a measure on `𝕜`. -/
noncomputable def coordTruncField (𝕜 : Type*) [RCLike 𝕜] (R : ℝ) : ℂ → 𝕜 :=
  fun z => RCLike.map ℂ 𝕜 (coordTrunc R z)

/-- The field-valued truncated coordinate is measurable. -/
theorem measurable_coordTruncField (𝕜 : Type*) [RCLike 𝕜] (R : ℝ) :
    Measurable (coordTruncField 𝕜 R) :=
  (RCLike.map ℂ 𝕜).continuous.measurable.comp (measurable_coordTrunc R)

/-- A convenient uniform bound for the field-valued coordinate.  The operator norm of the
canonical real-linear map is used instead of case-splitting on `𝕜`; for the complex model the
map is the identity, while the exact constant is irrelevant to the resulting multiplication
operator. -/
theorem norm_coordTruncField_le (𝕜 : Type*) [RCLike 𝕜] {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    ‖coordTruncField 𝕜 R z‖ ≤ ‖RCLike.map ℂ 𝕜‖ * R := by
  calc
    ‖coordTruncField 𝕜 R z‖ ≤ ‖RCLike.map ℂ 𝕜‖ * ‖coordTrunc R z‖ :=
      (RCLike.map ℂ 𝕜).le_opNorm (coordTrunc R z)
    _ ≤ ‖RCLike.map ℂ 𝕜‖ * R :=
      mul_le_mul_of_nonneg_left (norm_coordTrunc_le hR z) (norm_nonneg _)

/-- At complex scalars the field-valued coordinate symbol is the original one.

This is what keeps the `RCLike`-generic `coordTruncField` a strict generalization rather
than a parallel definition: every statement previously proved about `coordTrunc` transfers
to `coordTruncField ℂ` by `rfl`-level rewriting, so the complex specialization of the
field-indexed datum is the datum that was there before. -/
@[simp] theorem coordTruncField_complex (R : ℝ) : coordTruncField ℂ R = coordTrunc R := by
  funext z
  simp [coordTruncField]

/-- At real scalars the field-valued coordinate symbol is the **real part** of the original one,
because `RCLike.map ℂ ℝ` is `RCLike.reCLM`.  Stated because `coordTruncField` is not exposed, so
a consumer in another module cannot reach this by unfolding. -/
@[simp] theorem coordTruncField_real (R : ℝ) (z : ℂ) :
    coordTruncField ℝ R z = (coordTrunc R z).re := by
  simp [coordTruncField]

end Coord

section FieldMultiplication

variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]

/-- A uniformly bounded measurable `𝕜`-valued function multiplies `L²(𝕜)` into itself.

This is intentionally local to the multiplicity model rather than a generalisation of the
complex Radon--Nikodym API: field-indexing `MultiplicityDatum.operator` is a typing refactor,
whereas a field-generic Radon--Nikodym unitary is separate mathematics. -/
theorem memLp_two_mul_field (ρ : Measure α) {g : α → 𝕜} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp 𝕜 2 ρ) : MemLp (fun x => g x * F x) 2 ρ := by
  refine MemLp.mono' ((Lp.memLp F).norm.const_mul C)
    (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)) ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hgC x) (norm_nonneg _)

/-- The `L²` seminorm estimate for multiplication by a bounded `𝕜`-valued symbol. -/
theorem eLpNorm_two_mul_field_le (ρ : Measure α) {g : α → 𝕜} {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (f : α → 𝕜) :
    eLpNorm (fun x => g x * f x) 2 ρ ≤ ENNReal.ofReal |C| * eLpNorm f 2 ρ := by
  have hle : eLpNorm (fun x => g x * f x) 2 ρ ≤
      eLpNorm (((|C| : ℝ) : 𝕜) • f) 2 ρ := by
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (norm_nonneg _)
  rw [eLpNorm_const_smul] at hle
  refine hle.trans_eq ?_
  congr 1
  rw [← ofReal_norm, RCLike.norm_ofReal, abs_abs]

/-- The norm estimate that makes field-valued multiplication a bounded operator on `L²`. -/
theorem norm_toLp_mul_field_le (ρ : Measure α) {g : α → 𝕜} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp 𝕜 2 ρ) :
    ‖MemLp.toLp (fun x => g x * F x) (memLp_two_mul_field ρ hg hgC F)‖ ≤ |C| * ‖F‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_ofReal (abs_nonneg C), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ (eLpNorm_two_mul_field_le ρ hgC _)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)

/-- Multiplication by a bounded measurable `𝕜`-valued function on `L²(𝕜)`. -/
noncomputable def mulLpField (ρ : Measure α) {g : α → 𝕜} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) : Lp 𝕜 2 ρ →L[𝕜] Lp 𝕜 2 ρ :=
  LinearMap.mkContinuous
    { toFun := fun F => MemLp.toLp (fun x => g x * F x) (memLp_two_mul_field ρ hg hgC F)
      map_add' := fun F G => by
        rw [← MemLp.toLp_add (memLp_two_mul_field ρ hg hgC F)
          (memLp_two_mul_field ρ hg hgC G)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simp only [Pi.add_apply, hx]
        ring
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_two_mul_field ρ hg hgC F)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul]
        ring }
    |C| (norm_toLp_mul_field_le ρ hg hgC)

/-- Field-valued multiplication, unfolded. -/
theorem mulLpField_apply (ρ : Measure α) {g : α → 𝕜} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp 𝕜 2 ρ) :
    mulLpField ρ hg hgC F =
      MemLp.toLp (fun x => g x * F x) (memLp_two_mul_field ρ hg hgC F) := (rfl)

/-- Field-valued multiplication is pointwise multiplication almost everywhere. -/
theorem coeFn_mulLpField (ρ : Measure α) {g : α → 𝕜} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp 𝕜 2 ρ) :
    (mulLpField ρ hg hgC F : α → 𝕜) =ᵐ[ρ] fun x => g x * F x := by
  rw [mulLpField_apply]
  exact MemLp.coeFn_toLp _

/-- Field-valued multiplication depends on the symbol only almost everywhere.  The `mulLp`
counterpart is `TauCeti.mulLp_congr_ae`. -/
theorem mulLpField_congr_ae (ρ : Measure α) {g g' : α → 𝕜} (hg : Measurable g)
    (hg' : Measurable g') {C C' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (hgC' : ∀ x, ‖g' x‖ ≤ C')
    (h : g =ᵐ[ρ] g') : mulLpField ρ hg hgC = mulLpField ρ hg' hgC' := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLpField ρ hg hgC F, coeFn_mulLpField ρ hg' hgC' F, h] with x h1 h2 h3
  rw [h1, h2, h3]

end FieldMultiplication

section Datum

/-- **A multiplicity datum**: a finite measure on `ℂ` supported in a ball, together with an
antitone sequence of measurable level sets.

The measure carries the measure class; the level sets encode the cardinal-valued multiplicity
function by its super-level sets, which is what makes every hypothesis a plain `MeasurableSet`
rather than measurability of an `ℕ∞`-valued function.  The scalar parameter `𝕜` indexes only the
`L²` operator presented by the datum: `base` remains a `Measure ℂ`, and the level sets remain
subsets of `ℂ`.  The bound is part of the *presentation*, not of the invariant: it exists only so
the coordinate symbol is bounded. -/
structure MultiplicityDatum (𝕜 : Type*) [RCLike 𝕜] where
  /-- The base measure, carrying the measure class. -/
  base : Measure ℂ
  /-- A bound outside which the base measure vanishes. -/
  bound : ℝ
  /-- The super-level sets of the multiplicity function. -/
  level : ℕ → Set ℂ
  /-- The base measure is finite. -/
  base_finite : IsFiniteMeasure base
  /-- The bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The base measure lives inside the ball of radius `bound`. -/
  base_supported : base {z | bound < ‖z‖} = 0
  /-- **The base measure is carried by the zeroth level set**, i.e. by the set where the
  multiplicity is nonzero.

  Without this the base measure is not determined even in principle: mass outside `level 0`
  contributes to no summand of `measure`, so two data differing only there present the *same*
  operator while carrying different measure classes.  Any uniqueness statement about the datum
  is false without it, and every model produced by `exists_hasMultiplicityModel` satisfies it,
  because `level 0` is exactly the union of the supports the construction starts from. -/
  base_supported_level_zero : base (level 0)ᶜ = 0
  /-- The level sets are measurable. -/
  measurableSet_level : ∀ k, MeasurableSet (level k)
  /-- The level sets decrease: this is what makes them super-level sets of a function. -/
  antitone_level : Antitone level

attribute [instance] MultiplicityDatum.base_finite

/-- The measure of the model: the slice sum of the restrictions to the level sets. -/
noncomputable def MultiplicityDatum.measure {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) : Measure (ℂ × ℕ) :=
  sliceSum fun k => D.base.restrict (D.level k)

/-- The model measure, unfolded.  Stated so that consumers outside this module can rewrite with
it without the definition having to be exposed. -/
theorem MultiplicityDatum.measure_def {𝕜 : Type*} [RCLike 𝕜] (D : MultiplicityDatum 𝕜) :
    D.measure = sliceSum fun k => D.base.restrict (D.level k) := (rfl)

/-- The model measure is σ-finite: its slices are spanning sets of finite measure, because the
base measure is finite.  This is what lets the Radon--Nikodym unitary compare two models. -/
instance MultiplicityDatum.sigmaFinite_measure {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) :
    SigmaFinite D.measure := by
  rw [MultiplicityDatum.measure]
  infer_instance

/-- **The multiplicity function of a datum**: the number of level sets containing a point,
as an element of `ℕ∞`.

The datum records the *level sets* rather than this function, because that keeps every
hypothesis a plain `MeasurableSet` instead of measurability of an `ℕ∞`-valued map.  But the
function is what Davis and Kahan's Theorem 3.1 names, and `mem_level_iff` below says the two
carry exactly the same information: `level k` **is** `{z | k < multiplicity z}`.  So the level
sets are the super-level sets of a genuine cardinal-valued function, not a proxy for one --
which is what `MultiplicityDatum.antitone_level` is there to guarantee. -/
noncomputable def MultiplicityDatum.multiplicity {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) (z : ℂ) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : z ∈ D.level k), ((k : ℕ∞) + 1)

/-- **The level sets are the super-level sets of the multiplicity function.**

Forwards is the definition: membership in `level k` puts `k + 1` into the supremum.  Backwards
is antitonicity: if the supremum exceeds `k` then some `level j` with `j ≥ k` contains the
point, and `level j ⊆ level k`. -/
theorem MultiplicityDatum.mem_level_iff {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) (k : ℕ) (z : ℂ) :
    z ∈ D.level k ↔ (k : ℕ∞) < D.multiplicity z := by
  constructor
  · intro hz
    refine lt_of_lt_of_le ?_
      (le_iSup₂ (f := fun (j : ℕ) (_ : z ∈ D.level j) => ((j : ℕ∞) + 1)) k hz)
    exact_mod_cast Nat.lt_succ_self k
  · intro h
    rw [MultiplicityDatum.multiplicity, lt_iSup_iff] at h
    obtain ⟨j, hj⟩ := h
    rw [lt_iSup_iff] at hj
    obtain ⟨hzj, hlt⟩ := hj
    have hkj : k ≤ j := by
      have : (k : ℕ) < j + 1 := by exact_mod_cast hlt
      omega
    exact D.antitone_level hkj hzj

/-- **The multiplicity function is measurable.**

`ℕ∞` is countable and carries the discrete σ-algebra, so it is enough to identify each fibre,
and `mem_level_iff` turns every fibre into a Boolean combination of level sets: the fibre over
`⊤` is their intersection, the fibre over `0` is the complement of `level 0`, and the fibre over
`n + 1` is `level n` minus `level (n + 1)`. -/
theorem MultiplicityDatum.measurable_multiplicity {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) :
    Measurable D.multiplicity := by
  refine measurable_to_countable' fun c => ?_
  induction c with
  | top =>
    have hset : D.multiplicity ⁻¹' {(⊤ : ℕ∞)} = ⋂ k : ℕ, D.level k := by
      refine Set.ext fun z => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro hz k
        rw [D.mem_level_iff k z, hz]
        exact lt_of_le_of_ne le_top (by simp)
      · intro hz
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
        have hlt := (D.mem_level_iff n z).mp (hz n)
        rw [← hn] at hlt
        exact lt_irrefl _ hlt
    rw [hset]
    exact MeasurableSet.iInter fun k => D.measurableSet_level k
  | coe n =>
    match n with
    | 0 =>
      have hset : D.multiplicity ⁻¹' {((0 : ℕ) : ℕ∞)} = (D.level 0)ᶜ := by
        refine Set.ext fun z => ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
          D.mem_level_iff 0 z, Nat.cast_zero, not_lt, le_zero_iff]
      rw [hset]
      exact (D.measurableSet_level 0).compl
    | (n + 1) =>
      have hset : D.multiplicity ⁻¹' {((n + 1 : ℕ) : ℕ∞)}
          = D.level n \ D.level (n + 1) := by
        refine Set.ext fun z => ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
          D.mem_level_iff n z, D.mem_level_iff (n + 1) z, not_lt]
        constructor
        · intro hz
          refine ⟨hz ▸ ?_, hz ▸ le_rfl⟩
          exact_mod_cast Nat.lt_succ_self n
        · rintro ⟨h1, h2⟩
          refine le_antisymm h2 ?_
          exact Order.add_one_le_of_lt (by exact_mod_cast h1)
      rw [hset]
      exact (D.measurableSet_level n).diff (D.measurableSet_level (n + 1))

/-- **The model operator**: multiplication by the spectral coordinate, with values in the
model's scalar field.

The model measure still lives on `ℂ × ℕ`; field-indexing changes only the `L²` fibres and the
value field of the coordinate multiplier. -/
noncomputable def MultiplicityDatum.operator {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) : Lp 𝕜 2 D.measure →L[𝕜] Lp 𝕜 2 D.measure :=
  mulLpField D.measure ((measurable_coordTruncField 𝕜 D.bound).comp measurable_fst)
    (fun p => norm_coordTruncField_le 𝕜 D.bound_nonneg p.1)

/-- The model operator, unfolded.  Stated so that consumers can rewrite with it without the
definition having to be exposed. -/
theorem MultiplicityDatum.operator_def {𝕜 : Type*} [RCLike 𝕜] (D : MultiplicityDatum 𝕜) :
    D.operator = mulLpField D.measure ((measurable_coordTruncField 𝕜 D.bound).comp measurable_fst)
      (fun p => norm_coordTruncField_le 𝕜 D.bound_nonneg p.1) := (rfl)

/-- The field-indexed model operator is pointwise multiplication by the field-valued truncated
spectral coordinate. -/
theorem MultiplicityDatum.coeFn_operator {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) (F : Lp 𝕜 2 D.measure) :
    (D.operator F : ℂ × ℕ → 𝕜) =ᵐ[D.measure]
      fun p => coordTruncField 𝕜 D.bound p.1 * F p :=
  coeFn_mulLpField D.measure ((measurable_coordTruncField 𝕜 D.bound).comp measurable_fst)
    (fun p => norm_coordTruncField_le 𝕜 D.bound_nonneg p.1) F

/-- The model measure lives where the coordinate is bounded by the datum's bound. -/
theorem MultiplicityDatum.ae_norm_le_bound {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) :
    ∀ᵐ p ∂D.measure, ‖p.1‖ ≤ D.bound := by
  rw [ae_iff]
  have hmeas : MeasurableSet {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound} :=
    (measurableSet_le (measurable_norm.comp measurable_fst) measurable_const).compl
  rw [MultiplicityDatum.measure, sliceSum_apply _ hmeas, ENNReal.tsum_eq_zero]
  intro k
  have hfib : {z : ℂ | (z, k) ∈ {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound}} = {z : ℂ | D.bound < ‖z‖} := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_ofPred_eq, not_le]
  rw [hfib, Measure.restrict_apply (measurableSet_lt measurable_const measurable_norm)]
  exact measure_mono_null Set.inter_subset_left D.base_supported

end Datum

section Equivalence

/-- On complex `L²`, the field-indexed model operator is the existing complex multiplication
operator.  This keeps the established complex Hahn--Hellinger and uniqueness theory unchanged
while making the datum itself available at `𝕜 = ℝ`. -/
theorem MultiplicityDatum.operator_eq_mulLp (D : MultiplicityDatum ℂ) :
    D.operator = mulLp D.measure ((measurable_coordTrunc D.bound).comp measurable_fst)
      (fun p => norm_coordTrunc_le D.bound_nonneg p.1) := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [D.coeFn_operator F,
    coeFn_mulLp D.measure ((measurable_coordTrunc D.bound).comp measurable_fst)
      (fun p => norm_coordTrunc_le D.bound_nonneg p.1) F] with p hfield hcomplex
  rw [hfield, hcomplex]
  simp only [coordTruncField_complex, Function.comp_apply]

/-- **A datum read in a different scalar field.**

Every field of `TauCeti.MultiplicityDatum` -- base measure, bound, level sets and their
properties -- is scalar-field independent; the field enters only through
`TauCeti.MultiplicityDatum.operator`, whose `L²` fibres and multiplier take values in `𝕜`.  So a
datum for one field is literally a datum for any other, and this is the (identity-on-fields) map
that says so.  It is what lets the *complex* datum produced by Hahn--Hellinger be read as the
*real* datum a real classification statement needs, with the measure class and the level sets --
the entire multiplicity content -- unchanged. -/
def MultiplicityDatum.retype {𝕜 : Type*} [RCLike 𝕜] (𝕜' : Type*) [RCLike 𝕜']
    (D : MultiplicityDatum 𝕜) : MultiplicityDatum 𝕜' where
  base := D.base
  bound := D.bound
  level := D.level
  base_finite := D.base_finite
  bound_nonneg := D.bound_nonneg
  base_supported := D.base_supported
  base_supported_level_zero := D.base_supported_level_zero
  measurableSet_level := D.measurableSet_level
  antitone_level := D.antitone_level

/-- Retyping leaves the base measure alone. -/
@[simp] theorem MultiplicityDatum.retype_base {𝕜 : Type*} [RCLike 𝕜] (𝕜' : Type*) [RCLike 𝕜']
    (D : MultiplicityDatum 𝕜) : (D.retype 𝕜').base = D.base := (rfl)

/-- Retyping leaves the bound alone. -/
@[simp] theorem MultiplicityDatum.retype_bound {𝕜 : Type*} [RCLike 𝕜] (𝕜' : Type*) [RCLike 𝕜']
    (D : MultiplicityDatum 𝕜) : (D.retype 𝕜').bound = D.bound := (rfl)

/-- Retyping leaves the level sets alone -- which is the whole point: the multiplicity data are
the invariant, and they do not move. -/
@[simp] theorem MultiplicityDatum.retype_level {𝕜 : Type*} [RCLike 𝕜] (𝕜' : Type*) [RCLike 𝕜']
    (D : MultiplicityDatum 𝕜) : (D.retype 𝕜').level = D.level := (rfl)

/-- **Transport a real unitary equivalence into the retyped datum's presentation.**

Same reason as `starOperatorUnitaryEquiv_operator_of_mulLp_sliceSum`: neither
`TauCeti.MultiplicityDatum.measure` nor `TauCeti.MultiplicityDatum.operator` nor
`TauCeti.MultiplicityDatum.retype` is exposed, so outside this module the model `L²` space of
`D.retype ℝ` is not visibly the model `L²` space of `D`.  Inside it, the two sides are the same
term. -/
theorem operatorUnitaryEquiv_retype_real_operator_of_mulLpField {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : E →L[ℝ] E} (D : MultiplicityDatum ℂ)
    (h : OperatorUnitaryEquiv T (mulLpField D.measure
      ((measurable_coordTruncField ℝ D.bound).comp measurable_fst)
      (fun p => norm_coordTruncField_le ℝ D.bound_nonneg p.1))) :
    OperatorUnitaryEquiv T (D.retype ℝ).operator :=
  h

/-- **Transport a `star`-equivariant equivalence into the datum's own presentation.**

`TauCeti.MultiplicityDatum.measure` is not exposed, so a consumer in another module cannot see by
unfolding that `D.measure` *is* `sliceSum fun k => D.base.restrict (D.level k)`; and the measure
occurs in the *type* of the model `L²` space, so `TauCeti.MultiplicityDatum.measure_def` cannot
be rewritten with at the call site either.  This lemma performs the transport once, in the module
that can see the definition.  The plain `TauCeti.OperatorUnitaryEquiv` form needs no such lemma:
its unifier reaches the same defeq through the operator arguments alone. -/
theorem starOperatorUnitaryEquiv_operator_of_mulLp_sliceSum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {cH : H → H} {A : H →L[ℂ] H} (D : MultiplicityDatum ℂ)
    (h : StarOperatorUnitaryEquiv cH star A
      (mulLp (sliceSum fun k => D.base.restrict (D.level k))
        ((measurable_coordTrunc D.bound).comp measurable_fst)
        (fun p => norm_coordTrunc_le D.bound_nonneg p.1))) :
    StarOperatorUnitaryEquiv cH star A D.operator := by
  rw [MultiplicityDatum.operator_eq_mulLp]
  exact h

/-- The two truncations of the coordinate agree where the model measure lives. -/
theorem operator_eq_mulLp_of_le {D : MultiplicityDatum ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hle : D.bound ≤ R) :
    D.operator = mulLp D.measure ((measurable_coordTrunc R).comp measurable_fst)
      (fun p => norm_coordTrunc_le hR p.1) := by
  rw [D.operator_eq_mulLp]
  refine mulLp_congr_ae _ _ _ _ _ ?_
  filter_upwards [D.ae_norm_le_bound] with p hp
  rw [Function.comp_apply, Function.comp_apply, coordTrunc_eq_self hp,
    coordTrunc_eq_self (hp.trans hle)]

/-- **The model operator is multiplication by the coordinate truncated at any larger bound**, at
any scalar field.  The `𝕜 = ℂ` case is `operator_eq_mulLp_of_le`, stated separately because that
one lands in `mulLp` rather than `mulLpField`. -/
theorem MultiplicityDatum.operator_eq_mulLpField_of_le {𝕜 : Type*} [RCLike 𝕜]
    {D : MultiplicityDatum 𝕜} {R : ℝ} (hR : 0 ≤ R) (hle : D.bound ≤ R) :
    D.operator = mulLpField D.measure ((measurable_coordTruncField 𝕜 R).comp measurable_fst)
      (fun p => norm_coordTruncField_le 𝕜 hR p.1) := by
  rw [MultiplicityDatum.operator_def]
  refine mulLpField_congr_ae _ _ _ _ _ ?_
  filter_upwards [D.ae_norm_le_bound] with p hp
  simp only [Function.comp_apply, coordTruncField, coordTrunc_eq_self hp,
    coordTrunc_eq_self (hp.trans hle)]

/-- **Data agreeing up to measure class and null sets have model measures in the same
class.**

Split out of `operatorUnitaryEquiv_of_measureEquiv_complex` because it is scalar-field independent
-- the
model *measure* never mentions `𝕜` -- and the real classification needs it at `𝕜 = ℝ`. -/
theorem measureEquiv_measure_of_measureEquiv_base {𝕜 : Type*} [RCLike 𝕜]
    {D E : MultiplicityDatum 𝕜} (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    MeasureEquiv D.measure E.measure := by
  have hlev : ∀ k, (D.level k : Set ℂ) =ᵐ[D.base] (E.level k : Set ℂ) := fun k =>
    measure_symmDiff_eq_zero_iff.mp (hlevel k)
  have hfib : ∀ k, MeasureEquiv (D.base.restrict (D.level k)) (E.base.restrict (E.level k)) :=
    fun k => (measureEquiv_restrict_congr (hlev k)).trans (hbase.restrict (E.level k))
  rw [MultiplicityDatum.measure, MultiplicityDatum.measure]
  exact measureEquiv_sliceSum hfib

/-- **Data agreeing up to measure class and null sets present unitarily equivalent operators.**

The measure classes of the two model measures agree fibrewise -- restricting one base measure to
almost-equal sets gives literally the same measure, and the bases are equivalent -- so the
Radon--Nikodym unitary applies once the two coordinate symbols are truncated at a common
bound. -/
theorem operatorUnitaryEquiv_of_measureEquiv_complex {D E : MultiplicityDatum ℂ}
    (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    OperatorUnitaryEquiv D.operator E.operator := by
  have hmeas : MeasureEquiv D.measure E.measure :=
    measureEquiv_measure_of_measureEquiv_base hbase hlevel
  set R : ℝ := max D.bound E.bound with hRdef
  have hR0 : 0 ≤ R := le_trans D.bound_nonneg (le_max_left _ _)
  rw [operator_eq_mulLp_of_le (D := D) hR0 (le_max_left _ _),
    operator_eq_mulLp_of_le (D := E) hR0 (le_max_right _ _)]
  exact operatorUnitaryEquiv_of_intertwines (rnDerivL2Equiv hmeas.1 hmeas.2) fun F =>
    rnDerivL2Equiv_mulLp hmeas.1 hmeas.2 ((measurable_coordTrunc R).comp measurable_fst)
      (fun p => norm_coordTrunc_le hR0 p.1) F

end Equivalence

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- Multiplication by any symbol that agrees with the coordinate on the spectrum *is* coordinate
multiplication.  Stated with the symbol arbitrary so that call sites never have to match a
truncation syntactically. -/
theorem mulLp_eq_coordMulLp (ha : IsStarNormal a) (ξ : H) {g : spectrum ℂ a → ℂ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ w, ‖g w‖ ≤ C)
    (hgeq : ∀ w : spectrum ℂ a, g w = (w : ℂ)) (F : Lp ℂ 2 (diagMeasure ha ξ)) :
    mulLp (diagMeasure ha ξ) hg hgC F = coordMulLp ha ξ F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulLp (diagMeasure ha ξ) hg hgC F, coeFn_coordMulLp ha ξ F] with w h1 h2
  rw [h1, h2, hgeq w]

/-- **Every bounded normal operator on a separable complex Hilbert space has a multiplicity
model.**  This is the existence half of Hahn--Hellinger. -/
theorem exists_hasMultiplicityModel [TopologicalSpace.SeparableSpace H] (ha : IsStarNormal a) :
    ∃ D : MultiplicityDatum ℂ, OperatorUnitaryEquiv a D.operator := by
  classical
  have hR0 : (0 : ℝ) ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hspec : ∀ w : spectrum ℂ a, ‖(w : ℂ)‖ ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := by
    intro w
    have hw := spectrum.subset_closedBall_norm_mul a w.2
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hmeasSpec : MeasurableSet (spectrum ℂ a) := (spectrum.isCompact a).isClosed.measurableSet
  have hemb : MeasurableEmbedding ((↑) : spectrum ℂ a → ℂ) :=
    MeasurableEmbedding.subtype_coe hmeasSpec
  obtain ⟨ξ, hsum⟩ := exists_countable_isHilbertSum_lp_diagMeasure_complex ha
  have hfin : ∀ n, IsFiniteMeasure (Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) := fun n => Measure.isFiniteMeasure_map _ _
  have hsum' : IsHilbertSum ℂ
      (fun n => Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))))
      (fun n => (cyclicIsometry ha (ξ n)).comp
        (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) :=
    isHilbertSum_comp_linearIsometryEquiv hsum fun n => embLpEquiv hemb (diagMeasure ha (ξ n))
  have hsum2 := isHilbertSum_sliceLp
    (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))
  have hA : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      a (((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) F)
        = ((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry)
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) := by
    intro n F
    have h1 : embLpEquiv hemb (diagMeasure ha (ξ n))
        (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F)
        = coordMulLp ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F) :=
      (embLpEquiv_mulLp hemb (diagMeasure ha (ξ n))
        (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F).trans
        (mulLp_eq_coordMulLp ha (ξ n) _ _ (fun w => coordTrunc_eq_self (hspec w)) _)
    change a (cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F))
      = cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) _)
    rw [h1, cyclicIsometry_coordMulLp ha (ξ n)]
  have hB : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      (mulLp _ ((measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)).comp measurable_fst)
          (fun p => norm_coordTrunc_le hR0 p.1))
        (sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
          (diagMeasure ha (ξ n))) n F)
        = sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))) n
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) :=
    fun n F => (sliceLp_mulLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ m))) n (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0) F).symm
  have hstep1 := operatorUnitaryEquiv_of_isHilbertSum hsum' hsum2 hA hB
  obtain ⟨ρ, D, hρfin, hDmeas, hDanti, hρsupp, hρzero, hstep2⟩ :=
    exists_multiplicityLevels (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0)
  refine ⟨⟨ρ, ‖a‖ * ‖(1 : H →L[ℂ] H)‖, D, hρfin, hR0, ?_, hρzero, hDmeas, hDanti⟩, ?_⟩
  · refine hρsupp _ (measurableSet_lt measurable_const measurable_norm) fun n => ?_
    rw [Measure.map_apply hemb.measurable (measurableSet_lt measurable_const measurable_norm)]
    convert measure_empty (μ := diagMeasure ha (ξ n))
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    exact absurd (hspec w) (not_le.mpr hw)
  · rw [MultiplicityDatum.operator_eq_mulLp]
    exact hstep1.trans hstep2.toOperatorUnitaryEquiv

end BorelCalculus

end TauCeti
