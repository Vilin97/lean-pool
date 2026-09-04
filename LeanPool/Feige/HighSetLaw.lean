/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TwoPointInduction
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The discrete law of the high set

This file packages the product weights used in the proof of Theorem 2.1 as
an actual probability measure on `Finset (Fin m)`.  It also identifies the
probability of the rejection event with `twoPointRejectionMass`, so the
finite two-point calibration result can be stated directly as a probability
bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Feige

noncomputable instance highSetMeasurableSpace (m : ℕ) :
    MeasurableSpace (Finset (Fin m)) :=
  ⊤

/-- The probability mass function of the independent high set. -/
noncomputable def highSetPMF {m : ℕ} (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    PMF (Finset (Fin m)) :=
  PMF.ofFintype (fun S ↦ ENNReal.ofReal (highSetMass p S)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · have hu :
          (Finset.univ : Finset (Finset (Fin m))) =
            (Finset.univ : Finset (Fin m)).powerset := by
          ext S
          simp
      rw [hu, sum_highSetMass]
      exact ENNReal.ofReal_one
    · intro S _
      exact highSetMass_nonneg hp0 hp1 S)

/-- The high-set probability measure. -/
noncomputable def highSetMeasure {m : ℕ} (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    Measure (Finset (Fin m)) :=
  (highSetPMF p hp0 hp1).toMeasure

noncomputable instance highSetMeasure.isProbabilityMeasure {m : ℕ}
    (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    IsProbabilityMeasure (highSetMeasure p hp0 hp1) :=
  PMF.toMeasure.isProbabilityMeasure (highSetPMF p hp0 hp1)

@[simp]
theorem highSetPMF_apply {m : ℕ} (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset (Fin m)) :
    highSetPMF p hp0 hp1 S = ENNReal.ofReal (highSetMass p S) :=
  rfl

/-- Probability of a finite collection of high sets. -/
theorem highSetMeasure_apply_finset {m : ℕ} (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (A : Finset (Finset (Fin m))) :
    highSetMeasure p hp0 hp1 A =
      ∑ S ∈ A, ENNReal.ofReal (highSetMass p S) := by
  change (highSetPMF p hp0 hp1).toMeasure (A : Set (Finset (Fin m))) = _
  rw [PMF.toMeasure_apply_finset]
  simp

/-- Real-valued probability of a finite collection of high sets. -/
theorem highSetMeasure_real_apply_finset {m : ℕ} (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (A : Finset (Finset (Fin m))) :
    (highSetMeasure p hp0 hp1).real A =
      ∑ S ∈ A, highSetMass p S := by
  rw [measureReal_def, highSetMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun S _ ↦ ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro S hS
  simp [ENNReal.toReal_ofReal (highSetMass_nonneg hp0 hp1 S)]

/-- The rejection event in the high-set sample space. -/
noncomputable def twoPointRejectionEvent {m : ℕ} (γ β : Fin m → ℝ) (α : ℝ) :
    Finset (Finset (Fin m)) :=
  Finset.univ.filter fun S ↦ twoPointKFinset γ β S ≤ α

/-- Its actual probability is the finite two-point rejection mass. -/
theorem highSetMeasure_rejectionEvent {m : ℕ}
    (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i)
    (α : ℝ) :
    (highSetMeasure (twoPointHighProbability γ β)
      (twoPointHighProbability_nonneg (hγ := hγ) (hβ := hβ))
      (twoPointHighProbability_le_one (hγ := hγ) (hβ := hβ))).real
        (twoPointRejectionEvent γ β α) =
      twoPointRejectionMass γ β α := by
  rw [highSetMeasure_real_apply_finset]
  rfl

/-- Canonical two-point random vector on the high-set probability space. -/
noncomputable def canonicalTwoPointVector {m : ℕ}
    (γ β : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then highValue (β i) else lowValue (γ i)

/-- Each coordinate of the canonical two-point vector has mean one.  This is
the scalar identity underlying the product construction. -/
theorem canonicalTwoPoint_coordinate_mean_one {m : ℕ}
    (γ β : Fin m → ℝ) (i : Fin m) (h : γ i + β i ≠ 0) :
    highProbability (γ i) (β i) * canonicalTwoPointVector γ β {i} i +
      (1 - highProbability (γ i) (β i)) *
        canonicalTwoPointVector γ β ∅ i = 1 := by
  simp only [canonicalTwoPointVector]
  simp only [Finset.mem_singleton, ite_true, Finset.notMem_empty, ite_false]
  exact twoPoint_mean_one h

/-- Equivalent product-`Bool` realization of the canonical two-point
vector.  This model makes coordinate independence available directly from
the product-measure API. -/
def canonicalTwoPointPiVector {m : ℕ}
    (γ β : Fin m → ℝ) (ω : Fin m → Bool) (i : Fin m) : ℝ :=
  if ω i then highValue (β i) else lowValue (γ i)

/-- The coordinates of the canonical two-point vector are independent under
any product law on the underlying Boolean coordinates. -/
theorem iIndepFun_canonicalTwoPointPiVector {m : ℕ}
    (γ β : Fin m → ℝ) (μ : Fin m → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] :
    iIndepFun (fun i ω ↦ canonicalTwoPointPiVector γ β ω i)
      (Measure.pi μ) := by
  have hcoord :
      iIndepFun (fun i (ω : Fin m → Bool) ↦ ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ measurable_id.aemeasurable)
  have hmap : ∀ i : Fin m,
      Measurable (fun b : Bool ↦ if b then highValue (β i) else lowValue (γ i)) :=
    fun _ ↦ measurable_of_countable _
  simpa [canonicalTwoPointPiVector, Function.comp_def] using
    hcoord.comp
      (fun i b ↦ if b then highValue (β i) else lowValue (γ i)) hmap

end Feige
