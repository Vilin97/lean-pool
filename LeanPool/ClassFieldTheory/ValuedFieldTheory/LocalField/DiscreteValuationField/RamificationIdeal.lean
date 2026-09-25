/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
/-!
# Ramification ideals in finite complete-DVF extensions

This file records the ideal-theoretic source behind the local-field structure theory.
The base maximal ideal maps to the `e`-th power of the target maximal ideal, where
`e` is the canonical ramification index.  Every statement is expressed directly
in the ambient valued-extension context; no extension marker is involved.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- No power of the target maximal ideal is contained in the next power.

This is the ideal-level form of the uniformizer-power separation lemma. -/
theorem target_maximalIdeal_pow_not_le_pow_succ
    {π : target.valuationSubring}
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    ¬ target.maximalIdeal ^ n ≤ target.maximalIdeal ^ (n + 1) := by
  intro hle
  have hπpow_mem : π ^ n ∈ target.maximalIdeal ^ n := by
    rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ n]
    exact Ideal.mem_span_singleton_self (π ^ n)
  exact target.uniformizer_pow_not_mem_maximalIdeal_pow_succ hπ n
    (hle hπpow_mem)

/-- The image of the base maximal ideal is the `e`-th power of the target
maximal ideal. -/
theorem maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex :
    Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rcases target.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal)
      (maximalIdeal_map_integerMap_ne_bot base.toDVF target.toDVF) with
    ⟨n, hn⟩
  have hle :
      Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ n := by
    rw [hn]
  have hnot :
      ¬ Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ (n + 1) := by
    intro hle_succ
    rcases target.exists_uniformizer with ⟨π, hπ⟩
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ n
      (by simpa [hn] using hle_succ)
  have he : ramificationIndex base.toDVF target.toDVF = n := by
    simpa [ramificationIndex, integerMap] using
      (Ideal.ramificationIdx'_spec
        (p := base.maximalIdeal) (P := target.maximalIdeal) hle hnot)
  rw [he]
  exact hn

/-- The image of the `n`-th power of the base maximal ideal is the
`(e*n)`-th power of the target maximal ideal. -/
theorem maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex
    (n : ℕ) :
    Ideal.map (integerMap base.toDVF target.toDVF) (base.maximalIdeal ^ n) =
      target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF * n) := by
  calc
    Ideal.map (integerMap base.toDVF target.toDVF) (base.maximalIdeal ^ n) =
        (Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal) ^ n := by
      rw [Ideal.map_pow]
    _ = (target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF) ^ n := by
      rw [maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target]
    _ = target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF * n) := by
      rw [pow_mul]

/-- Elements in `m_K^n` map into `m_L^(e*n)`. -/
theorem integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex
    {n : ℕ} {x : base.valuationSubring}
    (hx : x ∈ base.maximalIdeal ^ n) :
    integerMap base.toDVF target.toDVF x ∈
      target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF * n) := by
  rw [← maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex
    base target n]
  exact Ideal.mem_map_of_mem (integerMap base.toDVF target.toDVF) hx

/-- The image of `m_K^n` is not contained in the next target maximal-ideal
power after `m_L^(e*n)`. -/
theorem maximalIdeal_pow_map_not_le_target_next_pow_mul_ramificationIndex
    (n : ℕ) :
    ¬ Ideal.map (integerMap base.toDVF target.toDVF) (base.maximalIdeal ^ n) ≤
      target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF * n + 1) := by
  rw [maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex
    base target n]
  rcases target.exists_uniformizer with ⟨π, hπ⟩
  exact target_maximalIdeal_pow_not_le_pow_succ target hπ
    (ramificationIndex base.toDVF target.toDVF * n)

/-- The image of a base uniformizer generates the `e`-th target maximal-ideal
power. -/
theorem span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  calc
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
        Ideal.map (integerMap base.toDVF target.toDVF)
          (Ideal.span ({ϖ} : Set base.valuationSubring)) := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal := by
      rw [base.maximalIdeal_eq_span_uniformizer hϖ]
    _ = target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target

/-- The image of the `n`-th power of a base uniformizer generates
`m_L^(e*n)`. -/
theorem span_base_uniformizer_pow_image_eq_target_maximalIdeal_pow_mul_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) (n : ℕ) :
    Ideal.span ({integerMap base.toDVF target.toDVF (ϖ ^ n)} :
        Set target.valuationSubring) =
      target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF * n) := by
  calc
    Ideal.span ({integerMap base.toDVF target.toDVF (ϖ ^ n)} :
        Set target.valuationSubring) =
        Ideal.map (integerMap base.toDVF target.toDVF)
          (Ideal.span ({ϖ ^ n} : Set base.valuationSubring)) := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.map (integerMap base.toDVF target.toDVF)
        (base.maximalIdeal ^ n) := by
      rw [base.maximalIdeal_pow_eq_span_uniformizer_pow hϖ n]
    _ = target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF * n) :=
      maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex
        base target n

/-- The image of a base uniformizer lies in the `e`-th target maximal-ideal
power. -/
theorem base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    integerMap base.toDVF target.toDVF ϖ ∈
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rw [← span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    base target hϖ]
  exact Ideal.mem_span_singleton_self (integerMap base.toDVF target.toDVF ϖ)

/-- The image of a base uniformizer has exact target maximal-ideal order `e`:
it is not in the next power. -/
theorem base_uniformizer_image_not_mem_target_maximalIdeal_pow_succ_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    integerMap base.toDVF target.toDVF ϖ ∉
      target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF + 1) := by
  intro hx
  have hspan :
      Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
          Set target.valuationSubring) =
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  have hspan_le :
      Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
          Set target.valuationSubring) ≤
        target.maximalIdeal ^
          (ramificationIndex base.toDVF target.toDVF + 1) := by
    rw [Ideal.span_le]
    intro y hy
    have hy_eq : y = integerMap base.toDVF target.toDVF ϖ := by
      simpa using hy
    simpa [hy_eq] using hx
  rcases target.exists_uniformizer with ⟨π, hπ⟩
  exact target_maximalIdeal_pow_not_le_pow_succ target hπ
    (ramificationIndex base.toDVF target.toDVF)
    (by simpa [hspan] using hspan_le)

/-- The image of a base uniformizer is a unit multiple of the `e`-th power of
any target uniformizer. -/
theorem exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) :
    ∃ u : target.valuationSubringˣ,
      integerMap base.toDVF target.toDVF ϖ =
        (u : target.valuationSubring) *
          π ^ ramificationIndex base.toDVF target.toDVF := by
  have hspan :
      Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
          Set target.valuationSubring) =
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  have hx_mem :
      integerMap base.toDVF target.toDVF ϖ ∈
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  rcases
      (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hπ
        (ramificationIndex base.toDVF target.toDVF)).1 hx_mem with
    ⟨u, hu⟩
  have hu_unit : IsUnit u := by
    by_contra hnot_unit
    have hu_mem : u ∈ target.maximalIdeal := by
      by_contra hnot_mem
      exact hnot_unit ((IsLocalRing.notMem_maximalIdeal (x := u)).1 hnot_mem)
    have hπpow_mem :
        π ^ ramificationIndex base.toDVF target.toDVF ∈
          target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
      rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ
        (ramificationIndex base.toDVF target.toDVF)]
      exact Ideal.mem_span_singleton_self
        (π ^ ramificationIndex base.toDVF target.toDVF)
    have hx_deep :
        integerMap base.toDVF target.toDVF ϖ ∈
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [hu]
      have hmul :
          π ^ ramificationIndex base.toDVF target.toDVF * u ∈
            target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF *
              target.maximalIdeal :=
        Ideal.mul_mem_mul hπpow_mem hu_mem
      simpa [pow_succ] using hmul
    have hspan_le :
        Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
            Set target.valuationSubring) ≤
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [Ideal.span_le]
      intro y hy
      have hy_eq : y = integerMap base.toDVF target.toDVF ϖ := by
        simpa using hy
      simpa [hy_eq] using hx_deep
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ
      (ramificationIndex base.toDVF target.toDVF)
      (by simpa [hspan] using hspan_le)
  rcases hu_unit with ⟨uunit, huunit⟩
  refine ⟨uunit, ?_⟩
  simpa [huunit, mul_comm] using hu

/-- Powers of a base uniformizer map to unit multiples of the corresponding
target uniformizer power. -/
theorem exists_unit_mul_target_uniformizer_pow_mul_eq_base_uniformizer_pow_image
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    ∃ u : target.valuationSubringˣ,
      integerMap base.toDVF target.toDVF (ϖ ^ n) =
        (u : target.valuationSubring) *
          π ^ (ramificationIndex base.toDVF target.toDVF * n) := by
  rcases exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
      base target hϖ hπ with ⟨u, hu⟩
  refine ⟨u ^ n, ?_⟩
  calc
    integerMap base.toDVF target.toDVF (ϖ ^ n) =
        integerMap base.toDVF target.toDVF ϖ ^ n := by
      rw [map_pow]
    _ = ((u : target.valuationSubring) *
          π ^ ramificationIndex base.toDVF target.toDVF) ^ n := by
      rw [hu]
    _ = (u : target.valuationSubring) ^ n *
          (π ^ ramificationIndex base.toDVF target.toDVF) ^ n := by
      rw [mul_pow]
    _ = ((u ^ n : target.valuationSubringˣ) : target.valuationSubring) *
          π ^ (ramificationIndex base.toDVF target.toDVF * n) := by
      rw [pow_mul]
      simp

/-- The image of a power of a base uniformizer lies in the corresponding
target maximal-ideal power. -/
theorem base_uniformizer_pow_image_mem_target_maximalIdeal_pow_mul_ramificationIndex
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    integerMap base.toDVF target.toDVF (ϖ ^ n) ∈
      target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF * n) := by
  rcases
      exists_unit_mul_target_uniformizer_pow_mul_eq_base_uniformizer_pow_image
        base target hϖ hπ n with
    ⟨u, hu⟩
  rw [hu, target.maximalIdeal_pow_eq_span_uniformizer_pow hπ]
  exact Ideal.mul_mem_left _ (u : target.valuationSubring)
    (Ideal.mem_span_singleton_self
      (π ^ (ramificationIndex base.toDVF target.toDVF * n)))

/-- The image of a power of a base uniformizer has exact target
maximal-ideal order `e*n`. -/
theorem base_uniformizer_pow_image_not_mem_target_next_pow_mul_ramificationIndex
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    integerMap base.toDVF target.toDVF (ϖ ^ n) ∉
      target.maximalIdeal ^
        (ramificationIndex base.toDVF target.toDVF * n + 1) := by
  rcases
      exists_unit_mul_target_uniformizer_pow_mul_eq_base_uniformizer_pow_image
        base target hϖ hπ n with
    ⟨u, hu⟩
  intro hx
  have hpow :
      (u : target.valuationSubring) *
        π ^ (ramificationIndex base.toDVF target.toDVF * n) ∈
        target.maximalIdeal ^
          (ramificationIndex base.toDVF target.toDVF * n + 1) := by
    simpa [hu] using hx
  have hu_unit : IsUnit (u : target.valuationSubring) := u.isUnit
  let I : Ideal target.valuationSubring :=
    target.maximalIdeal ^
      (ramificationIndex base.toDVF target.toDVF * n + 1)
  have hpowI :
      (u : target.valuationSubring) *
        π ^ (ramificationIndex base.toDVF target.toDVF * n) ∈ I := by
    simpa [I] using hpow
  have hpow' :
      π ^ (ramificationIndex base.toDVF target.toDVF * n) ∈
        target.maximalIdeal ^
          (ramificationIndex base.toDVF target.toDVF * n + 1) := by
    have hpiI :
        π ^ (ramificationIndex base.toDVF target.toDVF * n) ∈ I :=
      (I.unit_mul_mem_iff_mem hu_unit).1 hpowI
    simpa [I] using hpiI
  exact target.uniformizer_pow_not_mem_maximalIdeal_pow_succ hπ
    (ramificationIndex base.toDVF target.toDVF * n) hpow'

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
