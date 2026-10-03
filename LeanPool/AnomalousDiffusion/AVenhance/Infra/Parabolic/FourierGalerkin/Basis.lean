/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite symmetric Fourier cutoffs on the two-torus

The frequency box is indexed by integer pairs and is invariant under negation.  The Fourier partial
sum of a real-valued function is therefore real-valued; the real projection below is its real part,
with a theorem identifying its complexification with the partial sum itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance basisMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance basisMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance basisProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Two-dimensional unit torus carrying the periodic Galerkin equation. -/
abbrev Torus := UnitAddTorus (Fin 2)

/-- The integer frequency represented by an ordered pair. -/
def pairFrequency (p : ℤ × ℤ) : Fin 2 → ℤ :=
  fun i => if i = 0 then p.1 else p.2

@[simp]
theorem pairFrequency_neg (p : ℤ × ℤ) : pairFrequency (-p) = -pairFrequency p := by
  funext i
  fin_cases i <;> simp [pairFrequency]

/-- The finite symmetric cutoff `[-N,N]²` in frequency space. -/
def symmetricFrequencyBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem neg_mem_symmetricFrequencyBox {N : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ symmetricFrequencyBox N) : -p ∈ symmetricFrequencyBox N := by
  simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  rcases hp with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  change (-(N : ℤ) ≤ (-p).1 ∧ (-p).1 ≤ N) ∧
    (-(N : ℤ) ≤ (-p).2 ∧ (-p).2 ≤ N)
  rw [Prod.fst_neg, Prod.snd_neg]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- The complex Fourier partial sum over a finite symmetric box. -/
def complexFourierPartialSum (N : ℕ) (f : Torus → ℝ) (x : Torus) : ℂ :=
  ∑ p ∈ symmetricFrequencyBox N,
    UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) (pairFrequency p) *
      UnitAddTorus.mFourier (pairFrequency p) x

/-- The real-valued Fourier projection associated with the symmetric frequency box. -/
def realFourierProjection (N : ℕ) (f : Torus → ℝ) (x : Torus) : ℝ :=
  (complexFourierPartialSum N f x).re

theorem Basis.mFourierCoeff_conj (f : Torus → ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => star (f x)) k =
      star (UnitAddTorus.mFourierCoeff f (-k)) := by
  simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
  rw [neg_neg]
  calc
    ∫ t, UnitAddTorus.mFourier (-k) t * star (f t) =
        ∫ t, star (UnitAddTorus.mFourier k t * f t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Complex.star_def]
      simp [UnitAddTorus.mFourier_neg, map_mul]
    _ = star (∫ t, UnitAddTorus.mFourier k t * f t) := by
      simp only [Complex.star_def]
      rw [integral_conj]

theorem mFourierCoeff_real_neg (f : Torus → ℝ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) (-k) =
      star (UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k) := by
  have h := Basis.mFourierCoeff_conj (fun x => (f x : ℂ)) (-k)
  have hreal : (fun x => star ((f x : ℂ))) = fun x => (f x : ℂ) := by
    funext x
    simp
  rw [hreal] at h
  simpa [neg_neg] using h

theorem complexFourierPartialSum_real (N : ℕ) (f : Torus → ℝ) (x : Torus) :
    star (complexFourierPartialSum N f x) = complexFourierPartialSum N f x := by
  unfold complexFourierPartialSum
  rw [star_sum]
  apply Finset.sum_bij (fun p _ => -p)
  · intro p hp
    exact neg_mem_symmetricFrequencyBox hp
  · intro p₁ hp₁ p₂ hp₂ h
    exact neg_injective h
  · intro p hp
    exact ⟨-p, neg_mem_symmetricFrequencyBox hp, by simp⟩
  · intro p hp
    change (starRingEnd ℂ)
        (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) (pairFrequency p) *
          UnitAddTorus.mFourier (pairFrequency p) x) = _
    rw [map_mul]
    change star (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) (pairFrequency p)) *
      star (UnitAddTorus.mFourier (pairFrequency p) x) = _
    rw [pairFrequency_neg, ← mFourierCoeff_real_neg]
    congr 1
    exact (UnitAddTorus.mFourier_neg (n := pairFrequency p) (x := x)).symm

theorem complexFourierPartialSum_eq_ofReal (N : ℕ) (f : Torus → ℝ) (x : Torus) :
    (realFourierProjection N f x : ℂ) = complexFourierPartialSum N f x := by
  apply Complex.ext
  · simp [realFourierProjection]
  · have h := congrArg Complex.im (complexFourierPartialSum_real N f x)
    have him : (complexFourierPartialSum N f x).im = 0 := by
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith
    simpa [realFourierProjection] using him.symm

/-- The finite Fourier sum is a real-valued trigonometric polynomial for real input. -/
theorem realFourierProjection_complexification (N : ℕ) (f : Torus → ℝ) :
    (fun x => (realFourierProjection N f x : ℂ)) = complexFourierPartialSum N f := by
  funext x
  exact complexFourierPartialSum_eq_ofReal N f x

end AVenhance.Infra.Parabolic.FourierGalerkin

end
