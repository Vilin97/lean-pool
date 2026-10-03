/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Sliced convolution integrals and product-measure slicing

Two measure-theoretic facts used when a family of spatial statements indexed by
time, such as the slice-wise pressure equation of `lem:delta-p`, is assembled
into a single space-time statement.

* `stronglyMeasurable_slice_kernel_integral`: convolving a jointly measurable
  space-time integrand with a continuous kernel in the space variable alone
  produces a jointly measurable function of the space-time point.

* `ae_ae_of_ae_prod_snd` and `ae_prod_of_ae_ae_snd`: the two directions relating
  a product-almost-everywhere statement to its iterated form sliced in the
  *second* factor, which is the time factor in the product carrier `Vec3 × ℝ`.
  Mathlib states these for slices in the first factor; the versions here are
  obtained by transporting along the measure-preserving coordinate swap.
-/

public section

open MeasureTheory MeasureTheory.Measure


noncomputable section

namespace CKN

/-- A convolution-type integral against a continuous kernel, taken in the first factor only,
is jointly measurable in both factors. -/
theorem stronglyMeasurable_slice_kernel_integral {d : ℕ} {K : Vec d → ℝ}
    (hK : Continuous K) {P : Vec d × ℝ → ℝ} (hP : MeasureTheory.StronglyMeasurable P) :
    MeasureTheory.StronglyMeasurable
      (fun z : Vec d × ℝ =>
        ∫ y, K y * P (z.1 - y, z.2) ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d))) := by
  have hf : MeasureTheory.StronglyMeasurable
      (fun q : (Vec d × ℝ) × Vec d => K q.2 * P (q.1.1 - q.2, q.1.2)) := by
    apply Measurable.stronglyMeasurable
    exact (hK.measurable.comp measurable_snd).mul (hP.measurable.comp (by fun_prop))
  exact MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := MeasureTheory.volume) hf

/-- Slicing a product-almost-everywhere statement in the second factor. -/
theorem ae_ae_of_ae_prod_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] {p : α × β → Prop}
    (h : ∀ᵐ z ∂(μ.prod ν), p z) : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p (x, y) := by
  have h' : ∀ᵐ w ∂(ν.prod μ), p (Prod.swap w) :=
    (MeasureTheory.Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae h
  simpa only [Prod.swap_prod_mk] using
    (MeasureTheory.Measure.ae_ae_of_ae_prod (μ := ν) (ν := μ)
      (p := fun w => p (Prod.swap w)) h')

/-- Assembling a product-almost-everywhere membership from slices in the second factor. -/
theorem ae_prod_of_ae_ae_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] {s : Set (α × β)}
    (hs : MeasurableSet s) (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, (x, y) ∈ s) :
    ∀ᵐ z ∂(μ.prod ν), z ∈ s := by
  refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (μ := μ) (ν := ν) hs).mpr ?_
  exact (MeasureTheory.Measure.ae_ae_comm (μ := μ) (ν := ν)
    (p := fun x y => (x, y) ∈ s) (by simpa using hs)).mpr h

end CKN

end
