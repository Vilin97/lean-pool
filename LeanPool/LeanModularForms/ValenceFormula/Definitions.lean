/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Valence Formula Definitions

Definitions for the valence formula for SL₂(ℤ): elliptic points i and ρ,
orbifold coefficients, the order of vanishing, and the canonical fundamental domain.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The elliptic point i as an element of ℍ. -/
def ellipticPointI' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩

/-- The elliptic point `i` as a complex number. -/
abbrev ellipticPointI : ℂ := (ellipticPointI' : ℂ)

/-- The elliptic point ρ = e^{2πi/3} = -1/2 + (√3/2)i as an element of ℍ. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)

/-- The T-translate ρ+1 = e^{πi/3} = 1/2 + (√3/2)i. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)

theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I; ring

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1; rw [rho_plus_one_normSq_eq_one, Real.sqrt_one]

theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1; rw [rho_normSq_eq_one, Real.sqrt_one]

theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointI', mem_setOf_eq]
  constructor
  · simp [Complex.normSq_I]
  · simp only [UpperHalfPlane.re]; norm_num

theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointRho', mem_setOf_eq]
  exact ⟨rho_normSq_eq_one ▸ le_refl _, by simp only [UpperHalfPlane.re]; norm_num⟩

lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1; norm_num at h1

/-- Order of vanishing of f at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

/-- The order of vanishing at the cusp (in the q-expansion). -/
noncomputable def orderAtCusp' {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (UpperHalfPlane.qExpansion 1 f).order.toNat

end
