/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Topology.UniformSpace.AbsoluteValue
/-!
# Absolute values and exponential valuations

This module collects the valuation-theory material used by local class field
theory. General results on equivalence of absolute values, Ostrowski theory,
approximation, and rational-function examples are imported from Mathlib where
needed.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The distance attached by the absolute-value construction to an absolute value. -/
def absoluteValueDist {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) : ℝ :=
  v (x - y)

/-- The absolute-value distance is nonnegative. -/
theorem absoluteValueDist_nonneg
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) :
    0 ≤ absoluteValueDist v x y := by
  exact v.nonneg (x - y)

/-- The absolute-value distance separates points. -/
theorem absoluteValueDist_eq_zero_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) :
    absoluteValueDist v x y = 0 ↔ x = y := by
  change v (x - y) = 0 ↔ x = y
  exact AbsoluteValue.map_sub_eq_zero_iff (abv := v) x y

/-- The absolute-value distance from a point to itself is zero. -/
@[simp]
theorem absoluteValueDist_self
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x : K) :
    absoluteValueDist v x x = 0 := by
  simpa using (absoluteValueDist_eq_zero_iff v x x).mpr rfl

/-- The absolute-value distance is symmetric. -/
theorem absoluteValueDist_comm
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) :
    absoluteValueDist v x y = absoluteValueDist v y x := by
  simpa [absoluteValueDist] using (AbsoluteValue.map_sub v x y)

/-- The absolute-value distance satisfies the triangle inequality. -/
theorem absoluteValueDist_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y z : K) :
    absoluteValueDist v x z ≤
      absoluteValueDist v x y + absoluteValueDist v y z := by
  simpa [absoluteValueDist] using v.sub_le x y z

/-- The uniformity induced by the absolute-value construction distance is mathlib's uniformity
attached
to the same absolute value. -/
theorem absoluteValueUniformity_basis
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (@uniformity K v.uniformSpace).HasBasis ((0 : ℝ) < ·)
      (fun ε => {p : K × K | absoluteValueDist v p.2 p.1 < ε}) := by
  simpa [absoluteValueDist] using
    (AbsoluteValue.hasBasis_uniformity (abv := v))

/-- The excluded trivial absolute value: all nonzero elements have value `1`. -/
def TrivialAbsoluteValue {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : K, x ≠ 0 → v x = 1

/-- Being nontrivial is exactly having some nonzero element whose value is not
`1`. -/
theorem not_trivialAbsoluteValue_iff_exists_ne_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    ¬ TrivialAbsoluteValue v ↔ ∃ x : K, x ≠ 0 ∧ v x ≠ 1 := by
  classical
  constructor
  · intro h
    by_contra hnone
    apply h
    intro x hx
    by_contra hvx
    exact hnone ⟨x, hx, hvx⟩
  · rintro ⟨x, hx, hvx⟩ htriv
    exact hvx (htriv x hx)

/-- excluding the trivial absolute value is mathlib's nontriviality
condition for absolute values. -/
theorem not_trivialAbsoluteValue_iff_isNontrivial
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    ¬ TrivialAbsoluteValue v ↔ v.IsNontrivial := by
  exact not_trivialAbsoluteValue_iff_exists_ne_one v

/-- Definition of valuation, unpacked from mathlib's bundled `AbsoluteValue`. -/
theorem absoluteValue_axioms
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (∀ x : K, 0 ≤ v x ∧ (v x = 0 ↔ x = 0)) ∧
      (∀ x y : K, v (x * y) = v x * v y) ∧
        ∀ x y : K, v (x + y) ≤ v x + v y := by
  exact ⟨fun x => ⟨v.nonneg x, v.eq_zero⟩, v.map_mul, v.add_le⟩

/-- Finite triangle inequality for a absolute values. -/
theorem absoluteValue_finset_sum_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (s.sum f) ≤ s.sum (fun i => v (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (v.add_le (f i) (s.sum f)).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left ih (v (f i)))

/-- The equivalence relation on absolute values: two absolute values are equivalent if they
induce the
same topology. -/
def EquivalentAbsoluteValues {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (.refl K))

/-- absolute-value equivalence is the same as mathlib's equivalence relation on real
absolute values. -/
theorem equivalentAbsoluteValues_iff_isEquiv
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ v.IsEquiv w :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph v w).symm

/-- Mathlib-equivalent absolute values are equivalent under the defining equivalence relation. -/
theorem equivalentAbsoluteValues_of_isEquiv
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) :
    EquivalentAbsoluteValues v w :=
  (equivalentAbsoluteValues_iff_isEquiv v w).mpr h

/-- equivalent absolute values are mathlib-equivalent. -/
theorem isEquiv_of_equivalentAbsoluteValues
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : EquivalentAbsoluteValues v w) :
    v.IsEquiv w :=
  (equivalentAbsoluteValues_iff_isEquiv v w).mp h

/-- absolute-value equivalence is reflexive. -/
theorem equivalentAbsoluteValues_refl
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v v :=
  equivalentAbsoluteValues_of_isEquiv (AbsoluteValue.IsEquiv.rfl (v := v))

/-- absolute-value equivalence is symmetric. -/
theorem equivalentAbsoluteValues_symm
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : EquivalentAbsoluteValues v w) :
    EquivalentAbsoluteValues w v :=
  equivalentAbsoluteValues_of_isEquiv
    (isEquiv_of_equivalentAbsoluteValues h).symm

/-- absolute-value equivalence is transitive. -/
theorem equivalentAbsoluteValues_trans
    {K : Type*} [Field K] {v₁ v₂ v₃ : AbsoluteValue K ℝ}
    (h₁₂ : EquivalentAbsoluteValues v₁ v₂)
    (h₂₃ : EquivalentAbsoluteValues v₂ v₃) :
    EquivalentAbsoluteValues v₁ v₃ :=
  equivalentAbsoluteValues_of_isEquiv
    ((isEquiv_of_equivalentAbsoluteValues h₁₂).trans
      (isEquiv_of_equivalentAbsoluteValues h₂₃))

/-- The power characterization of equivalent absolute values: two real absolute values are
equivalent exactly when
one is a positive real power of the other. -/
theorem equivalentAbsoluteValues_iff_exists_rpow_eq
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∃ s : ℝ, 0 < s ∧ (v · ^ s) = w := by
  exact
    (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_exists_rpow_eq (v := v) (w := w))

/-- The criterion used in the proof of the power characterization of equivalent absolute values:
equivalence is the
same as preserving the strict unit ball. -/
theorem equivalentAbsoluteValues_iff_lt_one
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∀ x : K, v x < 1 ↔ w x < 1 := by
  exact
    (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_lt_one_iff (v := v) (w := w))

/-- The first construction in the proof of the weak approximation theorem:
for any one valuation in a finite pairwise-inequivalent family, there is an
element large for it and small for all the others. -/
theorem absoluteValueApproximation_exists_separating_element
    {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ)
    (hnontrivial : ∀ i, ¬ TrivialAbsoluteValue (v i))
    (hinequiv : Pairwise fun i j => ¬ EquivalentAbsoluteValues (v i) (v j)) :
    ∀ i, ∃ z : K, 1 < v i z ∧ ∀ j, j ≠ i → v j z < 1 := by
  apply AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
  · intro i
    exact (not_trivialAbsoluteValue_iff_isNontrivial (v i)).mp (hnontrivial i)
  · intro i j hij hIsEquiv
    exact
      (hinequiv hij)
        ((equivalentAbsoluteValues_iff_isEquiv (v i) (v j)).mpr hIsEquiv)

/-- The bump-function construction in the proof of the weak approximation theorem: from an
element large at `i` and small at the other valuations, produce
an element close to `1` at `i` and close to `0` at the others. -/
theorem absoluteValueApproximation_exists_bump_element
    {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ) {i : ι} {z : K}
    (hlarge : 1 < v i z)
    (hsmall : ∀ j, j ≠ i → v j z < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : K, v i (e - 1) < ε ∧ ∀ j, j ≠ i → v j e < ε := by
  classical
  let a : K := z⁻¹
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hlarge
    norm_num at hlarge
  have hi_a_lt_one : v i a < 1 := by
    dsimp [a]
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hlarge
  have hi_tendsto_element :
      Tendsto
        (fun n : ℕ => ((WithAbs.equiv (v i)).symm (1 / (1 + a ^ n)) :
          WithAbs (v i)))
        atTop (𝓝 1) :=
    WithAbs.tendsto_one_div_one_add_pow_nhds_one (v := v i) hi_a_lt_one
  have hi_tendsto :
      Tendsto (fun n : ℕ => v i (1 / (1 + a ^ n) - 1)) atTop (𝓝 0) := by
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hi_tendsto_element
    simpa [WithAbs.norm_eq_apply_ofAbs] using hnorm
  have hi_eventually :
      ∀ᶠ n : ℕ in atTop, v i (1 / (1 + a ^ n) - 1) < ε :=
    hi_tendsto.eventually (Iio_mem_nhds hε)
  have hothers_eventually :
      ∀ᶠ n : ℕ in atTop, ∀ j, j ≠ i → v j (1 / (1 + a ^ n)) < ε := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ hj => (hj hji).elim
    · have hj_a_gt_one : 1 < v j a := by
        dsimp [a]
        rw [map_inv₀]
        exact (one_lt_inv₀ ((v j).pos hz_ne_zero)).mpr (hsmall j hji)
      exact
        ((AbsoluteValue.tendsto_div_one_add_pow_nhds_zero
          (v := v j) hj_a_gt_one).eventually (Iio_mem_nhds hε)).mono
          fun _ hlt _ => hlt
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (hi_eventually.and hothers_eventually)
  refine ⟨1 / (1 + a ^ N), ?_, ?_⟩
  · exact (hN N le_rfl).1
  · intro j hji
    exact (hN N le_rfl).2 j hji

/-- Finite bump family used in the proof of the weak approximation theorem. -/
theorem absoluteValueApproximation_exists_bump_family
    {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ)
    (hnontrivial : ∀ i, ¬ TrivialAbsoluteValue (v i))
    (hinequiv : Pairwise fun i j => ¬ EquivalentAbsoluteValues (v i) (v j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ι → K,
      ∀ i, v i (e i - 1) < ε ∧ ∀ j, j ≠ i → v j (e i) < ε := by
  classical
  have hsep :=
    absoluteValueApproximation_exists_separating_element
      (v := v) hnontrivial hinequiv
  choose z hz using hsep
  have hbump :
      ∀ i, ∃ e : K,
        v i (e - 1) < ε ∧ ∀ j, j ≠ i → v j e < ε := by
    intro i
    exact absoluteValueApproximation_exists_bump_element
      (v := v) (i := i) (z := z i) (hz i).1 (hz i).2 hε
  choose e he using hbump
  exact ⟨e, he⟩

/-- Algebraic decomposition of the final approximation sum in the weak approximation theorem. -/
theorem absoluteValueApproximation_sum_sub
    {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a e : ι → K) (i : ι) :
    (∑ j, a j * e j) - a i =
      ∑ j, if j = i then a j * (e j - 1) else a j * e j := by
  classical
  have hsingle : (∑ j : ι, if j = i then a j else 0) = a i := by
    simp
  calc
    (∑ j, a j * e j) - a i
        = (∑ j, a j * e j) - ∑ j, (if j = i then a j else 0) := by
            rw [hsingle]
    _ = ∑ j, (a j * e j - if j = i then a j else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ j, if j = i then a j * (e j - 1) else a j * e j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · simp [hji, mul_sub]
            · simp [hji]

/-- The finite-sum estimate in the weak approximation theorem, after the bump
functions have been chosen with errors already weighted by the coefficients. -/
theorem absoluteValueApproximation_from_weighted_bump_family
    {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (v : ι → AbsoluteValue K ℝ) (a e : ι → K) {ε δ : ℝ}
    (hεδ : (Fintype.card ι : ℝ) * δ < ε)
    (hdiag : ∀ i, v i (a i) * v i (e i - 1) < δ)
    (hoff : ∀ i j, j ≠ i → v i (a j) * v i (e j) < δ) :
    ∃ x : K, ∀ i, v i (x - a i) < ε := by
  classical
  let x : K := ∑ j, a j * e j
  refine ⟨x, ?_⟩
  intro i
  have hsum_le :
      v i (∑ j, if j = i then a j * (e j - 1) else a j * e j) ≤
        ∑ j, v i (if j = i then a j * (e j - 1) else a j * e j) := by
    simpa using
      absoluteValue_finset_sum_le (v i) Finset.univ
        (fun j => if j = i then a j * (e j - 1) else a j * e j)
  have hterms_le :
      (∑ j, v i (if j = i then a j * (e j - 1) else a j * e j)) ≤
        ∑ _j : ι, δ := by
    refine Finset.sum_le_sum ?_
    intro j _
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl, (v i).map_mul]
      exact le_of_lt (hdiag i)
    · rw [ite_eq_right hji, (v i).map_mul]
      exact le_of_lt (hoff i j hji)
  have hsum_bound :
      (∑ j, v i (if j = i then a j * (e j - 1) else a j * e j)) < ε := by
    calc
      (∑ j, v i (if j = i then a j * (e j - 1) else a j * e j))
          ≤ ∑ _j : ι, δ := hterms_le
      _ = (Fintype.card ι : ℝ) * δ := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ < ε := hεδ
  calc
    v i (x - a i)
        = v i ((∑ j, a j * e j) - a i) := by rfl
    _ = v i (∑ j, if j = i then a j * (e j - 1) else a j * e j) := by
            rw [absoluteValueApproximation_sum_sub a e i]
    _ ≤ ∑ j, v i (if j = i then a j * (e j - 1) else a j * e j) := hsum_le
    _ < ε := hsum_bound

/-- A single positive precision small enough after multiplication by all finitely
many coefficients appearing in the weak approximation theorem. -/
theorem absoluteValueApproximation_exists_coefficient_precision
    {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ) (a : ι → K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ i j, v i (a j) * η < δ := by
  classical
  let := Fintype.ofFinite ι
  classical
  let C : ℝ := ∑ i : ι, ∑ j : ι, v i (a j)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => (v i).nonneg (a j)
  let η : ℝ := δ / (C + 1)
  have hC_add_pos : 0 < C + 1 := by linarith
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos hδ hC_add_pos
  have hC_mul_eta_lt : C * η < δ := by
    have hC_div_lt_one : C / (C + 1) < 1 := by
      exact (div_lt_one hC_add_pos).mpr (by linarith)
    calc
      C * η = δ * (C / (C + 1)) := by
        dsimp [η]
        ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hC_div_lt_one hδ
      _ = δ := by ring
  refine ⟨η, hη_pos, ?_⟩
  intro i j
  have hcoeff_le_inner : v i (a j) ≤ ∑ k : ι, v i (a k) :=
    Finset.single_le_sum
      (fun k _ => (v i).nonneg (a k)) (Finset.mem_univ j)
  have hinner_nonneg :
      ∀ k : ι, 0 ≤ ∑ l : ι, v k (a l) := by
    intro k
    exact Finset.sum_nonneg fun l _ => (v k).nonneg (a l)
  have hinner_le_C : (∑ l : ι, v i (a l)) ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum
      (fun k _ => hinner_nonneg k) (Finset.mem_univ i)
  have hcoeff_le_C : v i (a j) ≤ C :=
    hcoeff_le_inner.trans hinner_le_C
  exact
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hcoeff_le_C (le_of_lt hη_pos))
      hC_mul_eta_lt

/-- The weak approximation theorem, Approximation Theorem for a finite family of pairwise
inequivalent nontrivial absolute values. -/
theorem absoluteValueApproximation
    {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ)
    (hnontrivial : ∀ i, ¬ TrivialAbsoluteValue (v i))
    (hinequiv : Pairwise fun i j => ¬ EquivalentAbsoluteValues (v i) (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, ∀ i, v i (x - a i) < ε := by
  classical
  let := Fintype.ofFinite ι
  classical
  let δ : ℝ := ε / ((Fintype.card ι : ℝ) + 1)
  have hcard_add_pos : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hcard_add_pos
  have hεδ : (Fintype.card ι : ℝ) * δ < ε := by
    have hcard_div_lt_one :
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) < 1 := by
      exact (div_lt_one hcard_add_pos).mpr (by linarith)
    calc
      (Fintype.card ι : ℝ) * δ =
          ε * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1)) := by
        dsimp [δ]
        ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hcard_div_lt_one hε
      _ = ε := by ring
  obtain ⟨η, hη_pos, hη⟩ :=
    absoluteValueApproximation_exists_coefficient_precision (v := v) (a := a) hδ_pos
  obtain ⟨e, he⟩ :=
    absoluteValueApproximation_exists_bump_family
      (v := v) hnontrivial hinequiv (ε := η) hη_pos
  exact
    absoluteValueApproximation_from_weighted_bump_family
      (v := v) (a := a) (e := e) hεδ
      (fun i => by
        have hmul_le :
            v i (a i) * v i (e i - 1) ≤ v i (a i) * η :=
          mul_le_mul_of_nonneg_left (le_of_lt (he i).1) ((v i).nonneg (a i))
        exact lt_of_le_of_lt hmul_le (hη i i))
      (fun i j hji => by
        have hsmall : v i (e j) < η := (he j).2 i (Ne.symm hji)
        have hmul_le :
            v i (a j) * v i (e j) ≤ v i (a j) * η :=
          mul_le_mul_of_nonneg_left (le_of_lt hsmall) ((v i).nonneg (a j))
        exact lt_of_le_of_lt hmul_le (hη i j))

/-- The archimedean/nonarchimedean dichotomy: a valuation is nonarchimedean when its values on the
natural numbers are bounded. -/
def NonarchimedeanAbsoluteValue {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C

/-- The archimedean/nonarchimedean dichotomy: archimedean valuations are those which are not
nonarchimedean in the boundedness-on-integers sense. -/
def ArchimedeanAbsoluteValue {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : Prop :=
  ¬ NonarchimedeanAbsoluteValue v

/-- The strong triangle inequality appearing in the boundedness characterization of
nonarchimedean absolute values. -/
def StrongTriangle {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x y : K, v (x + y) ≤ max (v x) (v y)

/-- The archimedean/nonarchimedean dichotomy, unfolded. -/
theorem nonarchimedean_iff_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    NonarchimedeanAbsoluteValue v ↔ ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C :=
  Iff.rfl

/-- The archimedean/nonarchimedean dichotomy, archimedean case unfolded. -/
theorem archimedean_iff_not_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    ArchimedeanAbsoluteValue v ↔ ¬ NonarchimedeanAbsoluteValue v :=
  Iff.rfl

/-- The boundedness characterization of nonarchimedean absolute values, strong triangle
inequality as mathlib's
`IsNonarchimedean` predicate. -/
theorem strong_triangle_iff_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    StrongTriangle v ↔ IsNonarchimedean (v : K → ℝ) :=
  Iff.rfl

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values:
the strong triangle inequality
bounds the values of the natural numbers by `1`. -/
theorem nat_le_one_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) (n : ℕ) :
    v (n : K) ≤ 1 := by
  exact ((strong_triangle_iff_isNonarchimedean v).mp hstrong).apply_natCast_le_one
    (by simp) (by simp)

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: a
valuation satisfying the strong
triangle inequality is nonarchimedean in the boundedness-on-integers sense. -/
theorem nonarchimedean_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) :
    NonarchimedeanAbsoluteValue v :=
  ⟨1, nat_le_one_of_strong_triangle v hstrong⟩

/-- In the boundedness characterization of nonarchimedean absolute values, any bound for the
values of the natural numbers is at
least `1`. -/
theorem nat_bound_ge_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) :
    1 ≤ C := by
  simpa using hC 1

/-- The binomial-estimate step in the proof of the boundedness characterization of
nonarchimedean absolute values: boundedness
of the values of natural numbers gives a polynomial factor in the estimate for
`(x + y)^n`. -/
theorem add_pow_le_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K) (n : ℕ) :
    v ((x + y) ^ n) ≤
      ((n + 1 : ℕ) : ℝ) * C * (max (v x) (v y)) ^ n := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_nonneg : 0 ≤ C :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  have hsum_le :
      v ((Finset.range (n + 1)).sum
          (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) ≤
        (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) :=
    absoluteValue_finset_sum_le v (Finset.range (n + 1))
      (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        v (x ^ m * y ^ (n - m) * (n.choose m : K)) ≤ C * M ^ n := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hxpow : v (x ^ m) ≤ M ^ m := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg x) (le_max_left (v x) (v y)) m
    have hypow : v (y ^ (n - m)) ≤ M ^ (n - m) := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg y) (le_max_right (v x) (v y)) (n - m)
    have hxy :
        v (x ^ m) * v (y ^ (n - m)) ≤ M ^ m * M ^ (n - m) :=
      mul_le_mul hxpow hypow (v.nonneg (y ^ (n - m))) (pow_nonneg hM_nonneg m)
    have hchoose : v ((n.choose m : ℕ) : K) ≤ C := hC (n.choose m)
    calc
      v (x ^ m * y ^ (n - m) * (n.choose m : K))
          = v (x ^ m) * v (y ^ (n - m)) * v ((n.choose m : ℕ) : K) := by
              rw [map_mul, map_mul]
      _ ≤ (M ^ m * M ^ (n - m)) * C := by
              exact mul_le_mul hxy hchoose
                (v.nonneg ((n.choose m : ℕ) : K))
                (mul_nonneg (pow_nonneg hM_nonneg m)
                  (pow_nonneg hM_nonneg (n - m)))
      _ = C * M ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
              ring
  calc
    v ((x + y) ^ n)
        = v ((Finset.range (n + 1)).sum
            (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) := by
            rw [add_pow]
    _ ≤ (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) := hsum_le
    _ ≤ (Finset.range (n + 1)).sum (fun _m => C * M ^ n) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The real-variable limit used at the end of the boundedness characterization of
nonarchimedean absolute values: after taking
`n`-th roots, the polynomial factor `(n+1)C` disappears. -/
theorem tendsto_linear_bound_rpow_inv
    {C : ℝ} (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
      atTop (𝓝 1) := by
  have hCroot :
      Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => C ^ t) 0 :=
      Real.continuousAt_const_rpow hC.ne'
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun t : ℝ => C ^ t) ∘ fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 1)
    simpa only [Real.rpow_zero] using hcont.tendsto.comp hzero
  have hshiftReal :
      Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1)))) atTop (𝓝 1) :=
    tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one
  have hshiftNat :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    have hnatshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    refine (hshiftReal.comp hnatshift).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [Nat.cast_add, Nat.cast_one, one_div, add_assoc]
  have htarget :
      Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 (1 * 1)) := by
    refine (hshiftNat.mul hCroot).congr' ?_
    exact Eventually.of_forall fun n => by
      have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul :=
        (Real.mul_rpow (z := ((n : ℝ)⁻¹)) hn_nonneg (le_of_lt hC)).symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa using htarget

/-- The root form of the binomial estimate in the boundedness characterization of nonarchimedean
absolute values. -/
theorem add_le_root_bound_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K)
    {n : ℕ} (hn : n ≠ 0) :
    v (x + y) ≤
      ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
        max (v x) (v y) := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  by_cases hMzero : M = 0
  · have hx_le_zero : v x ≤ 0 := by
      simpa [M, hMzero] using (le_max_left (v x) (v y))
    have hy_le_zero : v y ≤ 0 := by
      simpa [M, hMzero] using (le_max_right (v x) (v y))
    have hxzero : x = 0 := (v.eq_zero).mp (le_antisymm hx_le_zero (v.nonneg x))
    have hyzero : y = 0 := (v.eq_zero).mp (le_antisymm hy_le_zero (v.nonneg y))
    simp [hxzero, hyzero]
  · have hpow :
        (v (x + y)) ^ n ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      simpa [map_pow, M] using
        add_pow_le_of_bounded_nat v hC x y n
    have hright_nonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt hC_pos))
        (pow_nonneg hM_nonneg n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hroot :
        v (x + y) ≤
          (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (v.nonneg (x + y)) hright_nonneg hn_pos]
      simpa [Real.rpow_natCast] using hpow
    calc
      v (x + y)
          ≤ (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := hroot
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
            have hcoef_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * C :=
              mul_nonneg (by positivity) (le_of_lt hC_pos)
            rw [Real.mul_rpow hcoef_nonneg (pow_nonneg hM_nonneg n)]
            rw [Real.pow_rpow_inv_natCast hM_nonneg hn]
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
            max (v x) (v y) := by
            rfl

/-- The converse direction of the boundedness characterization of nonarchimedean absolute
values: a bounded-on-integers
valuation satisfies the strong triangle inequality. -/
theorem strong_triangle_of_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : NonarchimedeanAbsoluteValue v) :
    StrongTriangle v := by
  rcases hnonarch with ⟨C, hC⟩
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  intro x y
  let M : ℝ := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv hC_pos).mul
        (tendsto_const_nhds (x := M))
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  have hle :
      v (x + y) ≤ M :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually
  simpa [M, StrongTriangle] using hle

/-- The boundedness characterization of nonarchimedean absolute values: the boundedness
definition of nonarchimedean is
equivalent to the strong triangle inequality. -/
theorem nonarchimedean_iff_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    NonarchimedeanAbsoluteValue v ↔ StrongTriangle v :=
  ⟨strong_triangle_of_nonarchimedean v,
    nonarchimedean_of_strong_triangle v⟩

/-- A consequence of the boundedness characterization: unequal values force equality in the
strong triangle inequality. -/
theorem strong_triangle_eq_max_of_ne
    {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
    (hstrong : StrongTriangle v)
    {x y : K} (hxy : v x ≠ v y) :
    v (x + y) = max (v x) (v y) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hy_le : v y ≤ v (x + y) := by
      have hbase : v y ≤ max (v (x + y)) (v x) := by
        calc
          v y = v ((x + y) + -x) := by ring_nf
          _ ≤ max (v (x + y)) (v (-x)) := hstrong (x + y) (-x)
          _ = max (v (x + y)) (v x) := by rw [AbsoluteValue.map_neg]
      by_contra hnot
      exact (not_lt_of_ge hbase) (max_lt (lt_of_not_ge hnot) hlt)
    apply le_antisymm
    · simpa [max_eq_right (le_of_lt hlt)] using hstrong x y
    · simpa [max_eq_right (le_of_lt hlt)] using hy_le
  · have hx_le : v x ≤ v (x + y) := by
      have hbase : v x ≤ max (v (x + y)) (v y) := by
        calc
          v x = v ((x + y) + -y) := by ring_nf
          _ ≤ max (v (x + y)) (v (-y)) := hstrong (x + y) (-y)
          _ = max (v (x + y)) (v y) := by rw [AbsoluteValue.map_neg]
      by_contra hnot
      exact (not_lt_of_ge hbase) (max_lt (lt_of_not_ge hnot) hgt)
    apply le_antisymm
    · simpa [max_eq_left (le_of_lt hgt)] using hstrong x y
    · simpa [max_eq_left (le_of_lt hgt)] using hx_le

/-- Ostrowski's classification of absolute values on `ℚ`, stated with the canonical
equivalence relation and with the trivial absolute value excluded.
The classification itself is mathlib's `Rat.AbsoluteValue.equiv_real_or_padic`;
this theorem only translates the equivalence predicate. -/
theorem rat_equivalent_real_or_padic
    (v : AbsoluteValue ℚ ℝ) (hnontrivial : ¬ TrivialAbsoluteValue v) :
    EquivalentAbsoluteValues v Rat.AbsoluteValue.real ∨
      ∃! p : ℕ, ∃ (_ : Fact p.Prime),
        EquivalentAbsoluteValues v (Rat.AbsoluteValue.padic p) := by
  have hv : v.IsNontrivial :=
    (not_trivialAbsoluteValue_iff_isNontrivial v).mp hnontrivial
  rcases Rat.AbsoluteValue.equiv_real_or_padic v hv with hreal | hpadic
  · exact .inl (equivalentAbsoluteValues_of_isEquiv hreal)
  · refine .inr ?_
    rcases hpadic with ⟨p, hp, hpuniq⟩
    refine ⟨p, ?_, ?_⟩
    · rcases hp with ⟨hpPrime, hpEquiv⟩
      exact
        ⟨hpPrime,
          equivalentAbsoluteValues_of_isEquiv hpEquiv⟩
    · intro q hq
      rcases hq with ⟨hqPrime, hqEquiv⟩
      exact
        hpuniq q
          ⟨hqPrime,
            isEquiv_of_equivalentAbsoluteValues hqEquiv⟩

end Valuations
end LubinTate
