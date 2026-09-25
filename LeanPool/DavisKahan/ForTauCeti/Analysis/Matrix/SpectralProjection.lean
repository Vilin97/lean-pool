/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable

/-! # Fixed-threshold spectral projectors

The indicator of `[c, infinity)` is generally discontinuous on the real line. A finite
matrix spectrum, however, is discrete: every function is continuous on it. Mathlib's
`Matrix.IsHermitian.cfc_eq` therefore applies without a gap hypothesis, even when `c` is
an eigenvalue. Continuous ramps which equal one at `c` converge to this closed-threshold
indicator. Their CFCs give a Borel measurable projector without choosing eigenvectors
measurably. This finite-spectrum argument must not be transferred to arbitrary bounded
operators whose spectra can accumulate at `c`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology Matrix

namespace TauCeti.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Orthogonal spectral projector onto eigenvalues in the closed upper ray. -/
noncomputable def spectralProjectionIci (c : ℝ) (A : Matrix (Fin n) (Fin n) 𝕜)
    (_hA : A.IsHermitian) : Matrix (Fin n) (Fin n) 𝕜 :=
  cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A

/-- The matrix threshold indicator defines a self-adjoint projection. -/
theorem isHermitian_spectralProjectionIci (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (spectralProjectionIci c A hA).IsHermitian := by
  exact (cfc_predicate (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A).isHermitian

/-- Selecting a spectral set twice has the same effect as selecting it once. -/
theorem isIdempotentElem_spectralProjectionIci (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    IsIdempotentElem (spectralProjectionIci c A hA) := by
  classical
  let f := Set.indicator (Set.Ici c) (1 : ℝ → ℝ)
  let D : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (fun i => (f (hA.eigenvalues i) : 𝕜))
  have hd : D * D = D := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : c ≤ hA.eigenvalues i <;> simp [f, hi]
  have h := congrArg (Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary) hd
  change spectralProjectionIci c A hA * spectralProjectionIci c A hA
      = spectralProjectionIci c A hA
  simpa only [map_mul, spectralProjectionIci, hA.cfc_eq, Matrix.IsHermitian.cfc,
    Function.comp_def, D, f] using h

/-- The diagonal coefficients of the threshold projector are exactly zero or one. -/
theorem spectralProjectionIci_eq_conj_diagonal (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    spectralProjectionIci c A hA =
      Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => if c ≤ hA.eigenvalues i then 1 else 0)) := by
  rw [spectralProjectionIci, hA.cfc_eq, Matrix.IsHermitian.cfc]
  congr 1
  ext i j
  simp [Set.indicator, Function.comp_def]

/-- In eigenvector coordinates, the threshold projector retains exactly the chosen columns. -/
theorem spectralProjectionIci_mul_eigenvectorUnitary (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    spectralProjectionIci c A hA * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) =
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) *
        Matrix.diagonal (fun i => if c ≤ hA.eigenvalues i then 1 else 0) := by
  rw [spectralProjectionIci_eq_conj_diagonal, Unitary.conjStarAlgAut_apply]
  simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]

/-- The projector fixes a unitary eigenvector column whose eigenvalue equals the cut. -/
theorem spectralProjectionIci_mulVec_of_eigenvalue_eq (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (i : Fin n)
    (hi : hA.eigenvalues i = c) :
    (spectralProjectionIci c A hA) *ᵥ
        (fun j => (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) j i) =
      (fun j => (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) j i) := by
  funext j
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i)
    (spectralProjectionIci_mul_eigenvectorUnitary c hA)
  rw [Matrix.mul_diagonal] at h
  simp only [hi, le_refl, ite_true, mul_one] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h

private def thresholdRamp (c : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 + ((m : ℝ) + 1) * (x - c)))

private theorem continuous_thresholdRamp (c : ℝ) (m : ℕ) :
    Continuous (thresholdRamp c m) := by
  unfold thresholdRamp
  fun_prop

private theorem thresholdRamp_eventually_eq (c x : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      thresholdRamp c m x = (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) x := by
  by_cases hx : c ≤ x
  · apply Filter.Eventually.of_forall
    intro m
    have hprod : 0 ≤ ((m : ℝ) + 1) * (x - c) := by positivity
    have hmin : min 1 (1 + ((m : ℝ) + 1) * (x - c)) = 1 := min_eq_left (by linarith)
    simp [thresholdRamp, hx, hmin]
  · have hpos : 0 < c - x := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (c - x))
    have hN' : 1 ≤ (N : ℝ) * (c - x) := (div_le_iff₀ hpos).mp hN
    filter_upwards [eventually_ge_atTop N] with m hm
    have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hprod : 1 ≤ ((m : ℝ) + 1) * (c - x) :=
      hN'.trans (mul_le_mul_of_nonneg_right (by linarith) hpos.le)
    have hneg : 1 + ((m : ℝ) + 1) * (x - c) ≤ 0 := by nlinarith
    have hmin : min 1 (1 + ((m : ℝ) + 1) * (x - c)) = 1 + ((m : ℝ) + 1) * (x - c) :=
      min_eq_right (by linarith)
    have hmax : max 0 (1 + ((m : ℝ) + 1) * (x - c)) = 0 := max_eq_left hneg
    simp [thresholdRamp, hx, hmin, hmax]

/-- A fixed-threshold projector is Borel measurable on finite Hermitian matrices. -/
theorem measurable_spectralProjectionIci (c : ℝ) :
    Measurable fun A : {A : Matrix (Fin n) (Fin n) 𝕜 // A.IsHermitian} =>
      spectralProjectionIci c A.1 A.2 := by
  apply measurable_of_tendsto_metrizable' atTop
    (fun m => (continuous_cfc_on_hermitian _ (continuous_thresholdRamp c m)).measurable)
  apply tendsto_pi_nhds.mpr
  intro A
  apply tendsto_cfc_of_pointwise A.2
  intro x _
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (thresholdRamp_eventually_eq c x))

/-- A measurable Hermitian random matrix has a measurable fixed-threshold projector. -/
theorem measurable_spectralProjectionIci_of_hermitian {Ω : Type*}
    [MeasurableSpace Ω] (c : ℝ)
    {Bm : Ω → Matrix (Fin n) (Fin n) 𝕜} (hBmeas : Measurable Bm)
    (hherm : ∀ w, (Bm w).IsHermitian) :
    Measurable fun w => spectralProjectionIci c (Bm w) (hherm w) :=
  (measurable_spectralProjectionIci c).comp (hBmeas.subtype_mk (h := hherm))

end TauCeti.Matrix
