/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.SimplexExponentialLaw
import LeanPool.Feige.NNRealExponentialLaw

/-!
# Event bridge for the exponential and simplex statistics

This file records the deterministic normalization identity between the
simplex statistic in (2.1) and the internal exponential representation, in
the `NNReal` coordinate model used by `expProductMeasure`.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory

namespace Feige

variable {n : ℕ}

theorem expMeasure_one_eq_withDensity_unitExponentialDensity :
    expMeasure 1 = volume.withDensity
      (fun x ↦ ENNReal.ofReal (unitExponentialDensity x)) := by
  unfold expMeasure gammaMeasure
  congr 1
  funext x
  unfold gammaPDF gammaPDFReal unitExponentialDensity
  by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]

/-- Binary density-product bridge used in the finite-dimensional
induction. -/
theorem prod_withDensity_eq_volume_withDensity
    {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure β)]
    {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ((volume : Measure α).withDensity f).prod
        ((volume : Measure β).withDensity g) =
      ((volume : Measure α).prod (volume : Measure β)).withDensity
        (fun z ↦ f z.1 * g z.2) := by
  rw [prod_withDensity hf hg]

/-- Transporting a density through a measure-preserving measurable
equivalence transports the underlying measure and composes the density
with the equivalence. -/
theorem MeasurePreserving.map_withDensity_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (T : α ≃ᵐ β) (hT : MeasurePreserving T μ ν)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    Measure.map T (μ.withDensity (f ∘ T)) =
      ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply T.measurable hs]
  rw [withDensity_apply _ (hs.preimage T.measurable)]
  rw [withDensity_apply _ hs]
  simpa only [Function.comp_apply] using
    hT.setLIntegral_comp_preimage hs hf

/-- One induction step: adjoining an independent unit exponential to a
finite-dimensional density multiplies the joint density. -/
theorem expMeasure_prod_withDensity
    {β : Type*} [MeasureSpace β]
    [SFinite (volume : Measure β)]
    {g : β → ℝ≥0∞} (hg : Measurable g) :
    (expMeasure 1).prod ((volume : Measure β).withDensity g) =
      ((volume : Measure ℝ).prod (volume : Measure β)).withDensity
        (fun z ↦ ENNReal.ofReal (unitExponentialDensity z.1) * g z.2) := by
  rw [expMeasure_one_eq_withDensity_unitExponentialDensity]
  exact prod_withDensity_eq_volume_withDensity
    (by
      apply Measurable.ennreal_ofReal
      unfold unitExponentialDensity
      exact (Real.measurable_exp.comp measurable_neg).indicator
        measurableSet_Ici) hg

/-- The joint unit-exponential density on `Fin n → ℝ`. -/
noncomputable def finExponentialDensity (n : ℕ) :
    (Fin n → ℝ) → ℝ≥0∞ :=
  fun x ↦ ∏ i, ENNReal.ofReal (unitExponentialDensity (x i))

theorem measurable_finExponentialDensity (n : ℕ) :
    Measurable (finExponentialDensity n) := by
  unfold finExponentialDensity
  apply Finset.measurable_fun_prod
  intro i _
  apply Measurable.ennreal_ofReal
  unfold unitExponentialDensity
  exact ((Real.measurable_exp.comp measurable_neg).comp
    (measurable_pi_apply i)).indicator
      (measurableSet_Ici.preimage (measurable_pi_apply i))

/-- The finite product of unit exponential laws has the product of the
one-dimensional exponential densities with respect to Lebesgue volume. -/
theorem pi_expMeasure_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (finExponentialDensity n) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  induction n with
  | zero =>
      have hpi :
          Measure.pi (fun _ : Fin 0 ↦ expMeasure 1) =
            (volume : Measure (Fin 0 → ℝ)) := by
        rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ expMeasure 1),
          Measure.volume_pi_eq_dirac]
      have hd : finExponentialDensity 0 = 1 := by
        funext x
        simp [finExponentialDensity]
      rw [hpi, hd, withDensity_one]
  | succ n ih =>
      let T : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hExp :
          MeasurePreserving T
            (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1))
            ((expMeasure 1).prod
              (Measure.pi (fun _ : Fin n ↦ expMeasure 1))) := by
        simpa [T] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ expMeasure 1) 0)
      have hVol :
          MeasurePreserving T
            (volume : Measure (Fin (n + 1) → ℝ))
            (volume : Measure (ℝ × (Fin n → ℝ))) := by
        simpa [T] using
          (volume_preserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ℝ) 0)
      have hdensity :
          (fun z : ℝ × (Fin n → ℝ) ↦
              ENNReal.ofReal (unitExponentialDensity z.1) *
                finExponentialDensity n z.2) =
            finExponentialDensity (n + 1) ∘ T.symm := by
        funext z
        simp [finExponentialDensity, T,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.prod_univ_succ]
      calc
        Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1) =
            Measure.map T.symm
              ((expMeasure 1).prod
                (Measure.pi (fun _ : Fin n ↦ expMeasure 1))) := by
          rw [← hExp.map_eq]
          exact (MeasurableEquiv.map_symm_map T).symm
        _ = Measure.map T.symm
              ((expMeasure 1).prod
                ((volume : Measure (Fin n → ℝ)).withDensity
                  (finExponentialDensity n))) := by rw [ih]
        _ = Measure.map T.symm
              ((volume : Measure (ℝ × (Fin n → ℝ))).withDensity
                (fun z ↦
                  ENNReal.ofReal (unitExponentialDensity z.1) *
                    finExponentialDensity n z.2)) := by
          rw [expMeasure_prod_withDensity
            (measurable_finExponentialDensity n)]
          rw [Measure.volume_eq_prod]
        _ = Measure.map T.symm
              ((volume : Measure (ℝ × (Fin n → ℝ))).withDensity
                (finExponentialDensity (n + 1) ∘ T.symm)) := by
          rw [hdensity]
        _ = (volume : Measure (Fin (n + 1) → ℝ)).withDensity
              (finExponentialDensity (n + 1)) := by
          exact MeasurePreserving.map_withDensity_equiv T.symm hVol.symm
            (measurable_finExponentialDensity (n + 1))

theorem productExponentialDensity_eq_ofReal_joint
    (e : ℝ × (Fin n → ℝ)) :
    ENNReal.ofReal (unitExponentialDensity e.1) *
        finExponentialDensity n e.2 =
      ENNReal.ofReal (jointUnitExponentialDensity e) := by
  unfold finExponentialDensity jointUnitExponentialDensity
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    by_cases hi : 0 ≤ e.2 i
    · simp [unitExponentialDensity, Set.indicator, hi,
        (Real.exp_pos (-e.2 i)).le]
    · simp [unitExponentialDensity, Set.indicator, hi]
  · unfold unitExponentialDensity
    by_cases h0 : 0 ≤ e.1
    · simp [Set.indicator, h0, (Real.exp_pos (-e.1)).le]
    · simp [Set.indicator, h0]

theorem expMeasure_prod_pi_eq_realExponentialProductMeasure :
    (expMeasure 1).prod
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) =
      realExponentialProductMeasure (n := n) := by
  rw [pi_expMeasure_eq_withDensity n]
  rw [expMeasure_prod_withDensity
    (measurable_finExponentialDensity n)]
  rw [← Measure.volume_eq_prod]
  unfold realExponentialProductMeasure
  rw [← withDensity_indicator
    (μ := (volume : Measure (ℝ × (Fin n → ℝ))))
    isMeasurableSet_positiveExponentialOrthant]
  apply withDensity_congr_ae
  have hne : ∀ᵐ e : ℝ × (Fin n → ℝ) ∂volume,
      e ≠ (0, fun _ ↦ 0) := by
    rw [ae_iff]
    simpa using
      (volume_singleton_zeroExponentialVector (n := n))
  filter_upwards [hne] with e hne
  rw [productExponentialDensity_eq_ofReal_joint]
  by_cases hnonneg : 0 ≤ e.1 ∧ ∀ i, 0 ≤ e.2 i
  · have ht := nonnegative_nonzero_exponentialTotal_pos
      hnonneg.1 hnonneg.2 hne
    have hm : e ∈ positiveExponentialOrthant (n := n) :=
      ⟨hnonneg.1, hnonneg.2, ht⟩
    rw [Set.indicator_of_mem hm]
    rw [jointUnitExponentialDensity_eq_exp_neg_total
      e hnonneg.1 hnonneg.2]
  · have hnmem : e ∉ positiveExponentialOrthant (n := n) := by
      intro he
      exact hnonneg ⟨he.1, he.2.1⟩
    simp only [Set.indicator, ite_eq_right hnmem]
    have hjoint : jointUnitExponentialDensity e = 0 := by
      apply jointUnitExponentialDensity_eq_zero_of_neg
      by_cases hfirst : 0 ≤ e.1
      · right
        push Not at hnonneg
        exact hnonneg hfirst
      · exact Or.inl (lt_of_not_ge hfirst)
    simp [hjoint]

/-- Coerce every coordinate of an `NNReal` vector to a real number. -/
def nnrealOptionToRealOption
    (e : Option (Fin n) → NNReal) : Option (Fin n) → ℝ :=
  fun i ↦ (e i : ℝ)

theorem measurable_nnrealOptionToRealOption :
    Measurable (nnrealOptionToRealOption (n := n)) := by
  unfold nnrealOptionToRealOption
  fun_prop

theorem map_expProductMeasure_to_realOption :
    Measure.map (nnrealOptionToRealOption (n := n))
        (expProductMeasure (Fin n)) =
      Measure.pi (fun _ : Option (Fin n) ↦ expMeasure 1) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  unfold expProductMeasure nnrealOptionToRealOption
  rw [Measure.pi_map_pi
    (fun _ : Option (Fin n) ↦ NNReal.continuous_coe.measurable.aemeasurable)]
  simp only [map_nnexpMeasure_coe]

/-- Split an optional-indexed vector into its distinguished and finite parts. -/
def realOptionToProduct
    (e : Option (Fin n) → ℝ) : ℝ × (Fin n → ℝ) :=
  (e none, fun i ↦ e (some i))

theorem measurable_realOptionToProduct :
    Measurable (realOptionToProduct (n := n)) := by
  unfold realOptionToProduct
  fun_prop

theorem map_realOptionProductMeasure :
    Measure.map (realOptionToProduct (n := n))
        (Measure.pi (fun _ : Option (Fin n) ↦ expMeasure 1)) =
      (expMeasure 1).prod
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let q : (Option (Fin n) → ℝ) ≃ᵐ
      ((Fin n → ℝ) × ℝ) :=
    MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ ℝ)
  have hq :
      Measure.map q
          (Measure.pi (fun _ : Option (Fin n) ↦ expMeasure 1)) =
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)).prod
          (expMeasure 1) := by
    rw [q.map_apply_eq_iff_map_symm_apply_eq]
    simpa [q] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ expMeasure 1)).symm
  rw [show realOptionToProduct (n := n) = Prod.swap ∘ q by rfl]
  rw [← Measure.map_map measurable_swap q.measurable]
  rw [hq, Measure.prod_swap]

theorem map_expProductMeasure_to_realProduct :
    Measure.map
        (realOptionToProduct (n := n) ∘
          nnrealOptionToRealOption (n := n))
        (expProductMeasure (Fin n)) =
      realExponentialProductMeasure (n := n) := by
  rw [← Measure.map_map measurable_realOptionToProduct
    measurable_nnrealOptionToRealOption]
  rw [map_expProductMeasure_to_realOption,
    map_realOptionProductMeasure,
    expMeasure_prod_pi_eq_realExponentialProductMeasure]

/-- The total mass of an optional-indexed nonnegative vector. -/
def nnrealExponentialTotal (e : Option (Fin n) → NNReal) : ℝ :=
  (e none : ℝ) + ∑ i, (e (some i) : ℝ)

/-- Normalize the finite coordinates by the total exponential mass. -/
noncomputable def nnrealNormalizedCoordinates
    (e : Option (Fin n) → NNReal) : Fin n → ℝ :=
  fun i ↦ (e (some i) : ℝ) / nnrealExponentialTotal e

theorem measurable_nnrealExponentialTotal :
    Measurable (nnrealExponentialTotal :
      (Option (Fin n) → NNReal) → ℝ) := by
  unfold nnrealExponentialTotal
  fun_prop

theorem measurable_nnrealNormalizedCoordinates :
    Measurable (nnrealNormalizedCoordinates :
      (Option (Fin n) → NNReal) → (Fin n → ℝ)) := by
  unfold nnrealNormalizedCoordinates
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply (some i)).coe_nnreal_real).div
    measurable_nnrealExponentialTotal

theorem nnrealNormalizedCoordinates_mem_fullSimplex
    {e : Option (Fin n) → NNReal}
    (ht : 0 < nnrealExponentialTotal e) :
    nnrealNormalizedCoordinates e ∈ fullSimplex (Fin n) := by
  rw [mem_fullSimplex_iff]
  constructor
  · intro i
    exact div_nonneg (e (some i)).coe_nonneg ht.le
  · unfold nnrealNormalizedCoordinates nnrealExponentialTotal
    rw [← Finset.sum_div]
    apply (div_le_one ht).2
    exact le_add_of_nonneg_left (e none).coe_nonneg

/-- On every nonzero exponential vector, the event defining `dirichletK`
is exactly the simplex halfspace event after normalization. -/
theorem mem_kEvent_iff_normalized_simplex_event
    (y : Fin n → ℝ) {e : Option (Fin n) → NNReal}
    (ht : 0 < nnrealExponentialTotal e) :
    e ∈ kEvent y ↔
      simplexLinearForm y (nnrealNormalizedCoordinates e) ≤ 1 := by
  unfold kEvent simplexLinearForm nnrealNormalizedCoordinates
  change
    (∑ i, (y i - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ) ↔
      ∑ i, y i * ((e (some i) : ℝ) / nnrealExponentialTotal e) ≤ 1
  have hsum :
      ∑ i, y i * ((e (some i) : ℝ) / nnrealExponentialTotal e) =
        (∑ i, y i * (e (some i) : ℝ)) /
          nnrealExponentialTotal e := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  rw [div_le_one ht]
  unfold nnrealExponentialTotal
  constructor <;> intro h
  · calc
      ∑ i, y i * (e (some i) : ℝ) =
          ∑ i, ((y i - 1) * (e (some i) : ℝ) +
            (e (some i) : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, (y i - 1) * (e (some i) : ℝ)) +
          ∑ i, (e (some i) : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (e none : ℝ) + ∑ i, (e (some i) : ℝ) := by
        linarith
  · have :
        ∑ i, (y i - 1) * (e (some i) : ℝ) =
          (∑ i, y i * (e (some i) : ℝ)) -
            ∑ i, (e (some i) : ℝ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    change ∑ i, (y i - 1) * (e (some i) : ℝ) ≤ (e none : ℝ)
    rw [this]
    linarith

theorem normalizedCoordinates_realProduct_comp
    (e : Option (Fin n) → NNReal) :
    normalizedExponentialCoordinates
        (realOptionToProduct (nnrealOptionToRealOption e)) =
      nnrealNormalizedCoordinates e := by
  rfl

theorem mem_kEvent_iff_normalized_simplex_event'
    (y : Fin n → ℝ) (e : Option (Fin n) → NNReal) :
    e ∈ kEvent y ↔
      simplexLinearForm y (nnrealNormalizedCoordinates e) ≤ 1 := by
  by_cases ht : 0 < nnrealExponentialTotal e
  · exact mem_kEvent_iff_normalized_simplex_event y ht
  · have htotal : nnrealExponentialTotal e = 0 := by
      apply le_antisymm
      · exact le_of_not_gt ht
      · unfold nnrealExponentialTotal
        positivity
    have hnone : e none = 0 := by
      have hnonneg : 0 ≤ ∑ i, (e (some i) : ℝ) :=
        Finset.sum_nonneg fun i _ ↦ (e (some i)).coe_nonneg
      rw [← NNReal.coe_eq_zero]
      unfold nnrealExponentialTotal at htotal
      exact le_antisymm (by linarith) (e none).coe_nonneg
    have hsome : ∀ i, e (some i) = 0 := by
      intro i
      apply NNReal.eq
      have hsum : ∑ j, (e (some j) : ℝ) = 0 := by
        unfold nnrealExponentialTotal at htotal
        simp only [hnone, NNReal.coe_zero, zero_add] at htotal
        exact htotal
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ (e (some j)).coe_nonneg)).mp hsum i
          (Finset.mem_univ i)
    simp [kEvent, simplexLinearForm, nnrealNormalizedCoordinates,
      htotal, hnone, hsome]

theorem map_expProductMeasure_normalizedCoordinates :
    Measure.map (nnrealNormalizedCoordinates (n := n))
        (expProductMeasure (Fin n)) =
      simplexUniformMeasure (Fin n) := by
  calc
    Measure.map (nnrealNormalizedCoordinates (n := n))
        (expProductMeasure (Fin n)) =
      Measure.map (normalizedExponentialCoordinates (n := n))
        (Measure.map
          (realOptionToProduct (n := n) ∘
            nnrealOptionToRealOption (n := n))
          (expProductMeasure (Fin n))) := by
            rw [Measure.map_map
              measurable_normalizedExponentialCoordinates
              (measurable_realOptionToProduct.comp
                measurable_nnrealOptionToRealOption)]
            apply Measure.map_congr
            filter_upwards [] with e
            exact (normalizedCoordinates_realProduct_comp e).symm
    _ = Measure.map (normalizedExponentialCoordinates (n := n))
        (realExponentialProductMeasure (n := n)) := by
          rw [map_expProductMeasure_to_realProduct]
    _ = simplexUniformMeasure (Fin n) :=
      map_realExponentialProductMeasure_normalizedCoordinates

theorem simplexExponentialIdentification (n : ℕ) :
    SimplexExponentialIdentification n := by
  intro y
  unfold dirichletK simplexK
  rw [← map_expProductMeasure_normalizedCoordinates (n := n)]
  rw [map_measureReal_apply measurable_nnrealNormalizedCoordinates
    (measurableSet_simplexK_event y)]
  congr 1
  ext e
  exact mem_kEvent_iff_normalized_simplex_event' y e

end Feige
