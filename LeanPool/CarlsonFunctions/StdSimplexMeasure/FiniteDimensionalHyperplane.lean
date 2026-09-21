/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Null affine hyperplanes in finite real products

This file proves that the solution set of a nontrivial weighted affine equation in a finite
product of real lines is a null set for the product measure. Coordinate and coordinate-sum
hyperplanes are recorded as volume corollaries.

This is the finite-product companion of `Measure.pi_hyperplane`. The corresponding statement
for a proper affine subspace of a finite-dimensional real space is `addHaar_affineSubspace`;
the lemmas here avoid that Haar/affine-subspace API.

This is a temporary project home. Intended Mathlib placement:

* `pi_weighted_hyperplane`, `ae_weighted_hyperplane`
  → `Mathlib.MeasureTheory.Constructions.Pi`, after `pi_hyperplane` / `ae_eval_ne`

The volume wrappers `volume_setOf_eval_eq` and `volume_setOf_fin_sum_eq` are local
conveniences for the present project.

TODO: if those lemmas land in Mathlib, delete this file and switch uses to the upstream names.
-/

open MeasureTheory MeasurableEquiv

public noncomputable section

namespace MeasureTheory.Measure

/-- The fibre of a weighted coordinate sum, after splitting off the `i`-th coordinate, is a
singleton. -/
private theorem weightedHyperplane_insertNth_section {n : ℕ}
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : a i ≠ 0) (c : ℝ) (y : Fin n → ℝ) :
    {t | ∑ j, a j * Fin.insertNth i t y j = c} =
      {(c - ∑ j, a (i.succAbove j) * y j) / a i} := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [i.sum_univ_succAbove]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  constructor
  · intro h
    exact (eq_div_iff hi).2 (by linarith)
  · intro ht
    rw [eq_div_iff hi] at ht
    linarith

/-- A level set of a weighted coordinate sum on `Fin n → ℝ` is a null set for a finite product
of sigma-finite measures, provided the sliced coordinate has no atoms. -/
private theorem pi_weighted_hyperplane_fin {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (a : Fin n → ℝ) (i : Fin n)
    [NullSingletonClass (μ i)] (hi : a i ≠ 0) (c : ℝ) :
    Measure.pi μ {x | ∑ j, a j * x j = c} = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).trans
      (MeasurableEquiv.prodComm : ℝ × (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ)
    have hmp : MeasurePreserving e (Measure.pi μ)
        ((Measure.pi fun j ↦ μ (i.succAbove j)).prod (μ i)) :=
      measurePreserving_swap.comp (measurePreserving_piFinSuccAbove μ i)
    have hmeas : MeasurableSet {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c} := by
      change MeasurableSet ((fun x : Fin (n + 1) → ℝ ↦ ∑ j, a j * x j) ⁻¹' {c})
      exact (Finset.univ.measurable_sum fun j _ ↦
        measurable_const.mul (measurable_pi_apply j)) (measurableSet_singleton c)
    have hpremeas : MeasurableSet
        (e.symm ⁻¹' {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}) :=
      hmeas.preimage e.symm.measurable
    rw [← hmp.symm.measure_preimage_equiv
      {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}]
    change ((Measure.pi fun j ↦ μ (i.succAbove j)).prod (μ i)) (e.symm ⁻¹' _) = 0
    refine (Measure.measure_prod_null hpremeas).2 (Filter.Eventually.of_forall fun y ↦ ?_)
    have hsection : Prod.mk y ⁻¹' (e.symm ⁻¹'
        {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c}) =
        {(c - ∑ j, a (i.succAbove j) * y j) / a i} := by
      ext t
      have he : e.symm (y, t) = Fin.insertNth i t y := by
        ext j
        rcases eq_or_ne j i with rfl | hj
        · simp [e, MeasurableEquiv.prodComm, Fin.insertNth_apply_same]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simp [e, MeasurableEquiv.prodComm, Fin.insertNth_apply_succAbove]
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, he]
      simpa [Set.mem_ofPred_eq, Set.mem_singleton_iff] using
        (Set.ext_iff.mp (weightedHyperplane_insertNth_section a i hi c y) t)
    change (μ i) (Prod.mk y ⁻¹' (e.symm ⁻¹'
      {x : Fin (n + 1) → ℝ | ∑ j, a j * x j = c})) = 0
    rw [hsection]
    simp

/-- A level set of a weighted coordinate sum has product measure zero if one of its
coefficients is nonzero. This is the finite-product form of the fact that a proper affine
hyperplane is Lebesgue-null; compare `pi_hyperplane` and `addHaar_affineSubspace`. -/
theorem pi_weighted_hyperplane {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (a : ι → ℝ) (i : ι)
    [NullSingletonClass (μ i)] (hi : a i ≠ 0) (c : ℝ) :
    Measure.pi μ {x | ∑ j, a j * x j = c} = 0 := by
  classical
  let σ := Fintype.equivFin ι
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) σ.symm
  have hmp := measurePreserving_piCongrLeft (μ := μ) σ.symm
  rw [← hmp.measure_preimage_equiv {x : ι → ℝ | ∑ j, a j * x j = c}]
  have hpre : e ⁻¹' {x : ι → ℝ | ∑ j, a j * x j = c} =
      {x : Fin (Fintype.card ι) → ℝ | ∑ j, a (σ.symm j) * x j = c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have he : ∀ j, e x j = x (σ j) := by
      intro j
      simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ι ↦ ℝ) σ.symm x (σ j)
    simp_rw [he]
    change (∑ j, a j * x (σ j)) = c ↔ _
    rw [← σ.symm.sum_comp (fun j ↦ a j * x (σ j))]
    simp
  rw [hpre]
  have : NullSingletonClass (μ (σ.symm (σ i))) := by
    simpa using (inferInstance : NullSingletonClass (μ i))
  exact pi_weighted_hyperplane_fin (fun j ↦ μ (σ.symm j)) (fun j ↦ a (σ.symm j))
    (σ i) (by simpa [σ]) c

/-- Almost every point of a finite real product lies off a nontrivial weighted hyperplane. -/
theorem ae_weighted_hyperplane {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (a : ι → ℝ) (i : ι)
    [NullSingletonClass (μ i)] (hi : a i ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂Measure.pi μ, ∑ j, a j * x j ≠ c :=
  compl_mem_ae_iff.2 (pi_weighted_hyperplane μ a i hi c)

/-- A level set of a weighted coordinate sum in a finite real product has volume zero if one
of its coefficients is nonzero. -/
theorem volume_setOf_fintype_weighted_sum_eq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (i : ι) (hi : a i ≠ 0) (c : ℝ) :
    volume {x : ι → ℝ | ∑ j, a j * x j = c} = 0 := by
  rw [volume_pi]
  exact pi_weighted_hyperplane (fun _ : ι ↦ (volume : Measure ℝ)) a i hi c

/-- A level set of a coordinate projection in a finite real product has volume zero. -/
theorem volume_setOf_eval_eq {ι : Type*} [Fintype ι] (i : ι) (c : ℝ) :
    volume {x : ι → ℝ | x i = c} = 0 := by
  rw [volume_pi]
  exact pi_hyperplane (fun _ : ι ↦ (volume : Measure ℝ)) i c

/-- A level set of the coordinate sum in a nonempty finite real product has volume zero.
The nonempty hypothesis is necessary: in dimension zero the level set at zero is the whole
space. -/
theorem volume_setOf_fintype_sum_eq {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    volume {x : ι → ℝ | ∑ i, x i = c} = 0 := by
  classical
  let i : ι := Classical.choice inferInstance
  rw [show {x : ι → ℝ | ∑ j, x j = c} =
      {x | ∑ j, (1 : ℝ) * x j = c} by ext x; simp]
  exact volume_setOf_fintype_weighted_sum_eq (fun _ : ι ↦ 1) i one_ne_zero c

/-- A level set of the coordinate sum in a nonempty finite real product has volume zero. -/
theorem volume_setOf_fin_sum_eq {n : ℕ} (hn : 0 < n) (c : ℝ) :
    volume {x : Fin n → ℝ | ∑ i, x i = c} = 0 := by
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact volume_setOf_fintype_sum_eq c

end MeasureTheory.Measure

end
