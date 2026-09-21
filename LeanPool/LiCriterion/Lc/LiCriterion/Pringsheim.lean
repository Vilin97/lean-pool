/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Pringsheim-style tools for the reverse direction of Li’s criterion.

The actual Pringsheim step (“a power series with nonnegative coefficients has a singularity on the
positive real axis at its radius of convergence”) is not implemented here yet.

This file collects small, reusable lemmas about complex conjugation and derivatives, which are
needed to reduce “nonnegativity of real parts” to “nonnegativity of coefficients” once we prove
that the relevant Taylor coefficients are real.
-/

open Complex
open scoped ComplexConjugate

namespace LiCriterion

/-! ### Conjugation and derivatives -/

/-- If `f` commutes with complex conjugation, then so does `deriv f` (with `deriv` using the
`0`-convention at nondifferentiable points). -/
lemma deriv_conj_eq_of_conj_invariant (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  classical
  by_cases hd : DifferentiableAt ℂ f z
  · have hder : HasDerivAt f (deriv f z) z := hd.hasDerivAt
    have hconj :
        HasDerivAt (conj ∘ f ∘ conj) (conj (deriv f z)) (conj z) :=
      (HasDerivAt.conj_conj (f := f) (f' := deriv f z) (x := z) hder)
    have hfun : (conj ∘ f ∘ conj) = f := by
      funext w
      have hw : f w = conj (f (conj w)) := by
        simpa using (hf (conj w))
      simpa [Function.comp_def] using hw.symm
    have hconj' : HasDerivAt f (conj (deriv f z)) (conj z) := by
      simpa [hfun] using hconj
    have hd_conj : DifferentiableAt ℂ f (conj z) := by
      have hd' :
          DifferentiableAt ℂ (conj ∘ f ∘ conj) (conj z) :=
        (DifferentiableAt.conj_conj (f := f) (x := z) hd)
      simpa [hfun] using hd'
    have hder_conj : HasDerivAt f (deriv f (conj z)) (conj z) := hd_conj.hasDerivAt
    exact (hder_conj.unique hconj')
  · have hd_conj : ¬ DifferentiableAt ℂ f (conj z) := by
      intro h
      have h' :
          DifferentiableAt ℂ (conj ∘ f ∘ conj) (conj (conj z)) :=
        (DifferentiableAt.conj_conj (f := f) (x := conj z) h)
      have hfun : (conj ∘ f ∘ conj) = f := by
        funext w
        have hw : f w = conj (f (conj w)) := by
          simpa using (hf (conj w))
        simpa [Function.comp_def] using hw.symm
      have : DifferentiableAt ℂ f z := by simpa [hfun] using h'
      exact hd this
    simp [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd_conj]

/-- If `f` commutes with conjugation, then so do all iterated derivatives. -/
lemma iteratedDeriv_conj_eq_of_conj_invariant (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z)) :
    ∀ n : ℕ, ∀ z : ℂ, (deriv^[n] f) (conj z) = conj ((deriv^[n] f) z) := by
  intro n
  induction n with
  | zero =>
      intro z
      simpa using hf z
  | succ n ih =>
      intro z
      simp only [Function.iterate_succ', Function.comp_apply]
      -- Apply the `deriv` lemma to `deriv^[n] f`, using the induction hypothesis as the
      -- conjugation commutation.
      have hcomm :
          ∀ w : ℂ, (deriv^[n] f) (conj w) = conj ((deriv^[n] f) w) := ih
      simpa using
        (deriv_conj_eq_of_conj_invariant (f := deriv^[n] f) hcomm z)

/-- In particular, a conjugation-invariant function has conjugation-invariant iterated derivatives
at `0`. -/
lemma conj_iteratedDeriv_zero_of_conj_invariant (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z))
    (n : ℕ) :
    conj ((deriv^[n] f) 0) = (deriv^[n] f) 0 := by
  have := iteratedDeriv_conj_eq_of_conj_invariant f hf n (0 : ℂ)
  simpa using this.symm

/-! ### Conjugation for Mellin transforms and `completedRiemannZeta₀`

To show the Li coefficients are real, it is convenient to know that the completed zeta functions
from Mathlib commute with complex conjugation.

Mathlib defines `completedRiemannZeta₀` as a Hurwitz-zeta specialization, ultimately as a Mellin
transform of a real-valued kernel; this section packages the resulting conjugation lemma.
-/

section CompletedZetaConj

open MeasureTheory

private lemma mellin_conj_real (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t) (s : ℂ) :
    conj (mellin f s) = mellin f (conj s) := by
  change
    conj (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s - 1) * f t) =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (conj s - 1) * f t
  have hconj :
      conj (∫ (t : ℝ) in Set.Ioi 0, (t : ℂ) ^ (s - 1) * f t) =
        ∫ (t : ℝ) in Set.Ioi 0, conj ((t : ℂ) ^ (s - 1) * f t) := by
    simpa using
      (integral_conj
        (μ := (volume.restrict (Set.Ioi (0 : ℝ))))
        (f := fun t : ℝ => (t : ℂ) ^ (s - 1) * f t)).symm
  have harg : ∀ t : ℝ, t ∈ Set.Ioi (0 : ℝ) → (t : ℂ).arg ≠ Real.pi := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have harg0 : (t : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg ht0
    simpa [harg0] using (Real.pi_ne_zero.symm)
  calc
    conj (∫ (t : ℝ) in Set.Ioi 0, (t : ℂ) ^ (s - 1) * f t)
        = ∫ (t : ℝ) in Set.Ioi 0, conj ((t : ℂ) ^ (s - 1) * f t) := hconj
    _ = ∫ (t : ℝ) in Set.Ioi 0, (t : ℂ) ^ (conj s - 1) * f t := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      have ht' : (t : ℂ).arg ≠ Real.pi := harg t ht
      have hcpow : conj ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (conj s - 1) := by
        have h := Complex.cpow_conj (x := (t : ℂ)) (n := s - 1) ht'
        have htconj : conj (t : ℂ) = (t : ℂ) := by simp
        have h' : (t : ℂ) ^ (conj (s - 1)) = conj ((t : ℂ) ^ (s - 1)) := by
          simpa [htconj] using h
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'.symm
      calc
        conj ((t : ℂ) ^ (s - 1) * f t)
            = conj ((t : ℂ) ^ (s - 1)) * conj (f t) := by simp [map_mul]
        _ = (t : ℂ) ^ (conj s - 1) * f t := by simp [hf t, hcpow]

private lemma conj_indicator {s : Set ℝ} {f : ℝ → ℂ} (hf : ∀ x, conj (f x) = f x) (x : ℝ) :
    conj (s.indicator f x) = s.indicator f x := by
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem, hx, hf]
  · simp [Set.indicator_of_notMem, hx]

private lemma hurwitzEvenFEPair_f_modif_conj (a : UnitAddCircle) (x : ℝ) :
    conj ((HurwitzZeta.hurwitzEvenFEPair a).f_modif x)
      = (HurwitzZeta.hurwitzEvenFEPair a).f_modif x := by
  classical
  simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, conj_indicator]

private lemma conj_two : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
  simpa using (map_natCast (starRingEnd ℂ) 2)

private lemma conj_inv_two : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  calc
    (starRingEnd ℂ) ((2 : ℂ)⁻¹) = ((starRingEnd ℂ) (2 : ℂ))⁻¹ := by
      simp
    _ = (2 : ℂ)⁻¹ := by
      rw [conj_two]

private lemma completedHurwitzZetaEven₀_conj (a : UnitAddCircle) (s : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven₀ a (conj s)
      = conj (HurwitzZeta.completedHurwitzZetaEven₀ a s) := by
  have hf : ∀ t : ℝ,
      conj ((HurwitzZeta.hurwitzEvenFEPair a).f_modif t)
        = (HurwitzZeta.hurwitzEvenFEPair a).f_modif t :=
    fun t => hurwitzEvenFEPair_f_modif_conj (a := a) t
  -- Unfold the `Λ₀` / Mellin definitions; then use `mellin_conj_real`.
  unfold HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  simp only [div_eq_mul_inv]
  have hsarg : conj (s * (2 : ℂ)⁻¹) = conj s * (2 : ℂ)⁻¹ := by
    have hinv : conj ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := conj_inv_two
    have hmul : conj (s * (2 : ℂ)⁻¹) = conj s * conj ((2 : ℂ)⁻¹) :=
      map_mul (starRingEnd ℂ) s ((2 : ℂ)⁻¹)
    simp [hinv]
  have hm :
      conj (mellin (HurwitzZeta.hurwitzEvenFEPair a).f_modif (s * (2 : ℂ)⁻¹)) =
        mellin (HurwitzZeta.hurwitzEvenFEPair a).f_modif (conj (s * (2 : ℂ)⁻¹)) :=
    mellin_conj_real (f := (HurwitzZeta.hurwitzEvenFEPair a).f_modif) hf (s * (2 : ℂ)⁻¹)
  rw [map_mul, conj_inv_two]
  simpa [hsarg] using congrArg (fun z => z * (2 : ℂ)⁻¹) hm.symm

/-- `completedRiemannZeta₀` commutes with complex conjugation. -/
lemma completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  simpa [completedRiemannZeta₀] using
    (completedHurwitzZetaEven₀_conj (a := (0 : UnitAddCircle)) s)

end CompletedZetaConj

end LiCriterion
