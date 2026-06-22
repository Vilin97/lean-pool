/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # TrueLevelBasis.lean
  WIP merged implementation for the true Hermite level `k` basis.

  Scaffolding notes:
  - `Basis/true_level_basis.md`

  This file now carries the previously split circle and bridge API directly.
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.Definitions
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # TrueLevelBasis -/


open Complex MeasureTheory Real Finset
open scoped BigOperators Topology

noncomputable section

namespace HermitekLEAN

-- This merged basis proof file carries a large amount of mechanically stable proof script.
-- Suppress repetitive local lint classes here rather than bloating the file with one-off rewrites.

/-- `T`: T. -/
abbrev T : ℝ := HermiteLEAN.T
/-- `Circle`: Circle. -/
abbrev Circle := HermiteLEAN.Circle
/-- `posPart`: pos Part. -/
abbrev posPart := HermiteLEAN.posPart

/-- The circle defect `rhoh(w) = ||1+w| - 1|`. -/
abbrev rhoh : ℂ → ℝ := HermiteLEAN.rho

/-- `weightedInner`: weighted Inner. -/
abbrev weightedInner := HermiteLEAN.weightedInner
/-- `weightedNormSq`: weighted Norm Sq. -/
abbrev weightedNormSq := HermiteLEAN.weightedNormSq
/-- `weightedNorm`: weighted Norm. -/
abbrev weightedNorm := HermiteLEAN.weightedNorm
/-- `modulusDefect`: modulus Defect. -/
abbrev modulusDefect := HermiteLEAN.modulusDefect
/-- `weightedDefectNormSq`: weighted Defect Norm Sq. -/
abbrev weightedDefectNormSq := HermiteLEAN.weightedDefectNormSq
/-- `weightedDefectNorm`: weighted Defect Norm. -/
abbrev weightedDefectNorm := HermiteLEAN.weightedDefectNorm
/-- `positiveTrigonometricPolynomial`: positive Trigonometric Polynomial. -/
abbrev positiveTrigonometricPolynomial := HermiteLEAN.positiveTrigonometricPolynomial
/-- `frequencyBand`: frequency Band. -/
abbrev frequencyBand := HermiteLEAN.frequencyBand
/-- `circleL2Sq`: circle L2 Sq. -/
abbrev circleL2Sq := HermiteLEAN.circleL2Sq
/-- `circleRhoNormSq`: circle Rho Norm Sq. -/
abbrev circleRhoNormSq := HermiteLEAN.circleRhoNormSq
/-- `circleModulusDefect`: circle Modulus Defect. -/
abbrev circleModulusDefect := HermiteLEAN.circleModulusDefect
/-- `circleDefectNormSq`: circle Defect Norm Sq. -/
abbrev circleDefectNormSq := HermiteLEAN.circleDefectNormSq
/-- `annulus`: annulus. -/
abbrev annulus := HermiteLEAN.annulus
/-- `annulusIntegralSq`: annulus Integral Sq. -/
abbrev annulusIntegralSq := HermiteLEAN.annulusIntegralSq
/-- `squareBlock`: square Block. -/
abbrev squareBlock := HermiteLEAN.squareBlock
/-- `circlePoint`: circle Point. -/
abbrev circlePoint := HermiteLEAN.circlePoint

/-! ## Core Basis Objects -/

/-- The holomorphic Fock basis vector `e_n(z) = z^n / sqrt(n!)`. -/
def eBasis (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)

/--
The true Hermite basis vector at level `k`, written directly as the explicit
finite `z`/`conj z` expansion used downstream.

The raising/lowering-operator derivation is only bookkeeping motivation; the
public API stays explicit and finitary.
-/
noncomputable def Phi : ℕ → ℕ → ℂ → ℂ := fun k n z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))

/-- The distinguished lowest vector in level `k`. -/
def phi0 (k : ℕ) : ℂ → ℂ := Phi k 0

/-- The closed span of the true Hermite level-`k` basis.

  An element `G` belongs to `Hk k` when its canonical Hermite-coefficient
  expansion converges pointwise to `G` and its weighted square norm is
  integrable. Equivalently, `Hk k` is the weighted-`L²` closure of
  `span {Φₖ,ₙ}` together with the pointwise Hermite expansion data. -/
def Hk (k : ℕ) : Set (ℂ → ℂ) :=
  {G | Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ∧
      ∀ z, HasSum (fun n => weightedInner G (Phi k n) * Phi k n z) (G z)}

/-- A finite Hermite sum `sum_{n < D} a_n Phi_{k,n}`. -/
def finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, a n * Phi k n.1 z

/-- The top coefficient of a degree-`d` finite Hermite sum. -/
def topCoeff {d : ℕ} (a : Fin (d + 1) → ℂ) : ℂ :=
  a ⟨d, Nat.lt_succ_self d⟩

/-- The canonical coefficient extractor for the true level basis. -/
def hermiteCoeff (k : ℕ) (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  weightedInner G (Phi k n)

/-- The partial Hermite sum with the first `J + 1` canonical coefficients of `G`. -/
def truncate (k J : ℕ) (G : ℂ → ℂ) : ℂ → ℂ :=
  finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1)

/-- The real radial coefficient in the polar decomposition of `Phi k n`. -/
noncomputable def qkn : ℕ → ℕ → ℝ → ℝ := fun k n r =>
  (1 / Real.sqrt (Nat.factorial n : ℝ)) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
        r ^ ((n : ℤ) - 2 * (j : ℤ)))

/-- The scalar front factor in the polar representation. -/
def circleLeadingFactor (k : ℕ) (r : ℝ) : ℂ :=
  ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) : ℝ) : ℂ)

/-- The finitely supported circle coefficient map attached to finite Hermite data. -/
def finiteCircleCoeff (k : ℕ) (r : ℝ) {D : ℕ} (a : Fin D → ℂ) : ℕ → ℂ :=
  fun n => if h : n < D then a ⟨n, h⟩ * (qkn k n r : ℂ) else 0

/-- The finite Fourier polynomial on the circle attached to a finite Hermite sum. -/
def finiteCirclePoly (k : ℕ) (r : ℝ) {D : ℕ} (a : Fin D → ℂ) : Circle → ℂ :=
  positiveTrigonometricPolynomial (frequencyBand 0 D) (finiteCircleCoeff k r a)

/-- The finite circle polynomial built from the truncated coefficient vector of `G`. -/
def truncCirclePoly (k : ℕ) (r : ℝ) (J : ℕ) (G : ℂ → ℂ) : Circle → ℂ :=
  finiteCirclePoly k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)

/-- The total mass of `F` on annuli `A_j` with `j >= j0`. -/
def tailAnnulusMass (F : ℂ → ℂ) (j0 : ℕ) : ℝ :=
  ∑' j : ℕ, if j0 ≤ j then annulusIntegralSq F j else 0

-- to_mathlib: Mathlib/Algebra/BigOperators/Intervals
/-- Reindex a finite sum over `Icc N (N + L - 1)` to `Fin L`. -/
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    change N + (n - N) = n
    omega
  · intro _ _
    rfl

private lemma filter_natCast_eq_singleton {D : ℕ} (k : Fin D) :
    (Finset.univ : Finset (Fin D)).filter
      (fun j => ((j.val : ℕ) : ℤ) = ((k.val : ℕ) : ℤ)) = {k} := by
  ext j
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro h
    have h' : j.val = k.val := by
      omega
    exact Fin.ext h'
  · simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    rw [h]

private lemma circleL2Sq_finFourierPoly {D : ℕ} (c : Fin D → ℂ) :
    circleL2Sq (fun t : Circle => ∑ k : Fin D, c k * fourier (k.val : ℤ) t) =
      ∑ k : Fin D, ‖c k‖ ^ 2 := by
  let E' := (Finset.univ : Finset (Fin D)).map
    ⟨fun k => (k.val : ℤ), fun k₁ k₂ h => by
      have h' : (k₁ : ℕ) = k₂ := by
        exact Nat.cast_injective (R := ℤ) h
      exact Fin.ext h'⟩
  let b : ℤ → ℂ := fun n => ∑ k ∈ (Finset.univ : Finset (Fin D)).filter
    (fun k => ((k.val : ℕ) : ℤ) = n), c k
  have hb_eq : ∀ k : Fin D, b (k.val : ℤ) = c k := by
    intro k
    simp only [b]
    rw [filter_natCast_eq_singleton, Finset.sum_singleton]
  let Pcont : C(Circle, ℂ) := ∑ k : Fin D, c k • fourier (k.val : ℤ)
  have hPcont_eq : ∀ t : Circle, (Pcont : Circle → ℂ) t = ∑ k : Fin D, c k * fourier (k.val : ℤ) t
      := by
    intro t
    simp only [Pcont, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
  let PLp := (ContinuousMap.toLp (α := Circle) 2 AddCircle.haarAddCircle ℂ) Pcont
  have hPLp' : PLp = ∑ n ∈ E', b n • fourierLp 2 n := by
    simp only [PLp, Pcont, fourierLp, map_sum, map_smul, E', b]
    rw [Finset.sum_map]
    congr 1
    ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [filter_natCast_eq_singleton, Finset.sum_singleton]
  have hinner_orth : @inner ℂ _ _ PLp PLp = Complex.ofReal (∑ k : Fin D, ‖c k‖ ^ 2) := by
    rw [hPLp', orthonormal_fourier.inner_sum b b E']
    rw [show E' = (Finset.univ : Finset (Fin D)).map
      ⟨fun k => (k.val : ℤ), fun k₁ k₂ h => by
        have h' : (k₁ : ℕ) = k₂ := by
          exact Nat.cast_injective (R := ℤ) h
        exact Fin.ext h'⟩ from rfl]
    rw [Finset.sum_map, Complex.ofReal_sum]
    congr 1
    ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [hb_eq k, mul_comm (starRingEnd ℂ _), mul_conj]
    exact_mod_cast (Complex.sq_norm (c k)).symm
  have hcombine := (L2.inner_def (𝕜 := ℂ) PLp PLp).symm.trans hinner_orth
  have hae := ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  calc
    circleL2Sq (fun t : Circle => ∑ k : Fin D, c k * fourier (k.val : ℤ) t)
      = ∫ t : Circle, ‖(∑ k : Fin D, c k * fourier (k.val : ℤ) t)‖ ^ 2 ∂AddCircle.haarAddCircle :=
          by
          rfl
    _ = ∫ t, ‖(↑↑PLp : Circle → ℂ) t‖ ^ 2 ∂AddCircle.haarAddCircle := by
          symm
          apply integral_congr_ae
          filter_upwards [hae] with t ht
          rw [show (↑↑PLp : Circle → ℂ) t = Pcont t from ht, hPcont_eq t]
    _ = (∫ t, @inner ℂ ℂ _ ((↑↑PLp : Circle → ℂ) t)
            ((↑↑PLp : Circle → ℂ) t) ∂AddCircle.haarAddCircle).re := by
          have hint := L2.integrable_inner (𝕜 := ℂ) PLp PLp
          symm
          calc
            _ = Complex.reCLM
                  (∫ t, @inner ℂ ℂ _ ((↑↑PLp : Circle → ℂ) t)
                    ((↑↑PLp : Circle → ℂ) t) ∂AddCircle.haarAddCircle) := rfl
            _ = ∫ t, Complex.reCLM
                  (@inner ℂ ℂ _ ((↑↑PLp : Circle → ℂ) t) ((↑↑PLp : Circle → ℂ) t))
                    ∂AddCircle.haarAddCircle := (ContinuousLinearMap.integral_comp_comm _ hint).symm
            _ = _ := by
                  congr 1
                  ext t
                  exact @inner_self_eq_norm_sq ℂ ℂ _ _ _ _
    _ = ∑ k : Fin D, ‖c k‖ ^ 2 := by
          rw [show (∫ t : Circle, @inner ℂ ℂ _ ((↑↑PLp : Circle → ℂ) t)
              ((↑↑PLp : Circle → ℂ) t) ∂AddCircle.haarAddCircle) =
              Complex.ofReal (∑ k : Fin D, ‖c k‖ ^ 2) from hcombine, Complex.ofReal_re]

/-! ## Explicit and Polar Formulas -/

/-- Off-diagonal case: monomial moments vanish when indices differ. -/
private lemma gaussian_monomial_moments_off_diag {a b : ℕ} (hab : a ≠ b) :
    ∫ z : ℂ, ((z ^ a) * (star z) ^ b).re * Real.exp (-‖z‖ ^ 2) = 0 := by
  -- Rotation trick: pick ω on the unit circle s.t. ω^(a-b) = -1, then I = -I.
  set d : ℤ := (a : ℤ) - (b : ℤ) with hd_def
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (by exact_mod_cast hab)
  set ω : _root_.Circle := _root_.Circle.exp (Real.pi / (d : ℝ))
  -- Key: ω^a * conj(ω)^b = -1
  have hω_factor : ((ω : ℂ) ^ a * star (ω : ℂ) ^ b) = -1 := by
    rw [star_def, ← _root_.Circle.coe_inv_eq_conj]
    rw [← _root_.Circle.coe_pow, ← _root_.Circle.coe_pow, ← _root_.Circle.coe_mul]
    -- Goal: ↑(ω^a * ω⁻¹^b) = -1. Reduce ω^a * ω⁻¹^b to ω^d.
    have hprod : ω ^ a * ω⁻¹ ^ b = ω ^ d := by
      rw [hd_def]
      rw [show ω ^ a * ω⁻¹ ^ b = ω ^ a * (ω ^ b)⁻¹ from by rw [inv_pow]]
      rw [← zpow_natCast ω a, ← zpow_natCast ω b, ← zpow_sub]
    rw [hprod]
    -- ω^d = Circle.exp(π/d)^d = Circle.exp(d * (π/d)) = Circle.exp(π) = -1
    rw [show ω = _root_.Circle.exp (Real.pi / (d : ℝ)) from rfl]
    rw [← _root_.Circle.exp_intCast_mul (Real.pi / (d : ℝ)) d]
    rw [show (d : ℝ) * (Real.pi / (d : ℝ)) = Real.pi from by field_simp]
    simp [_root_.Circle.coe_exp, Complex.exp_pi_mul_I]
  -- The rotation ω preserves the measure
  set rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation ω
  have hmp := rot.measurePreserving
  have hemb : MeasurableEmbedding (⇑rot) :=
    rot.toHomeomorph.measurableEmbedding
  -- Express the integral after rotation
  have hI : ∀ z : ℂ,
      ((rot z) ^ a * star (rot z) ^ b).re * Real.exp (-‖rot z‖ ^ 2) =
      -((z ^ a * star z ^ b).re * Real.exp (-‖z‖ ^ 2)) := by
    intro z
    simp only [rot, rotation_apply, mul_pow, star_mul]
    rw [norm_mul, _root_.Circle.norm_coe, one_mul]
    have : (↑ω ^ a * z ^ a * (star z ^ b * star ↑ω ^ b)).re =
        ((↑ω ^ a * star ↑ω ^ b) * (z ^ a * star z ^ b)).re := by ring_nf
    rw [this, hω_factor]
    simp only [Complex.neg_re, Complex.mul_re, neg_mul, one_mul,
      neg_sub]
    ring
  -- Apply rotation to the integral: ∫ f(rot z) dz = ∫ f(z) dz
  set f : ℂ → ℝ := fun z => (z ^ a * star z ^ b).re * Real.exp (-‖z‖ ^ 2) with hf_def
  have hrot_eq : ∫ z, f (rot z) = ∫ z, f z :=
    hmp.integral_comp hemb f
  -- But f(rot z) = -f(z), so ∫ -f = ∫ f, hence ∫ f = 0
  have hrot_neg : ∀ z, f (rot z) = -f z := hI
  simp_rw [hrot_neg] at hrot_eq
  rw [integral_neg] at hrot_eq
  linarith

/-- Diagonal case: z^a * conj(z)^a = ‖z‖^{2a}. -/
private lemma zpow_conj_diag_re (z : ℂ) (a : ℕ) :
    (z ^ a * (starRingEnd ℂ) z ^ a).re = ‖z‖ ^ (2 * a) := by
  rw [← mul_pow, Complex.mul_conj']
  norm_cast
  rw [← pow_mul]

/-- Radial integral: ∫_ℂ ‖z‖^{2a} exp(-‖z‖²) = π a!. -/
private lemma integral_norm_pow_exp_gaussian (a : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) = π * (Nat.factorial a : ℝ) := by
  have h_rpow : ∀ z : ℂ, (‖z‖ : ℝ) ^ (2 * a) = ‖z‖ ^ ((2 * a : ℕ) : ℝ) := by
    intro z; exact (rpow_natCast ‖z‖ (2 * a)).symm
  have h_exp : ∀ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z‖ ^ (2 : ℝ)) := by
    intro z; norm_num
  simp_rw [h_rpow, h_exp]
  rw [show ((2 * a : ℕ) : ℝ) = ((2 * a : ℕ) : ℝ) from rfl]
  rw [Complex.integral_rpow_mul_exp_neg_rpow (show (1 : ℝ) ≤ 2 from by linarith)
    (show (-2 : ℝ) < ((2 * a : ℕ) : ℝ) from by
      have : (0 : ℝ) ≤ ((2 * a : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)]
  rw [show ((2 * a : ℕ) : ℝ) + 2 = 2 * ((a : ℝ) + 1) from by push_cast; ring]
  rw [show 2 * ((a : ℝ) + 1) / 2 = (a : ℝ) + 1 from by ring]
  rw [show 2 * π / 2 = π from by ring]
  rw [Real.Gamma_nat_eq_factorial]

/-- Gaussian monomial moments in the weighted plane. -/
theorem gaussian_monomial_moments :
    ∀ (a b : ℕ),
      (1 / Real.pi) *
          ∫ z : ℂ, ((z ^ a) * (star z) ^ b).re * Real.exp (-‖z‖ ^ 2)
        = if a = b then (Nat.factorial a : ℝ) else 0 := by
  intro a b
  by_cases hab : a = b
  · -- Diagonal case: a = b
    subst hab
    rw [if_pos rfl]
    have hre : ∀ z : ℂ, (z ^ a * star z ^ a).re * Real.exp (-‖z‖ ^ 2) =
        ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) := by
      intro z; rw [show star z = (starRingEnd ℂ) z from rfl, zpow_conj_diag_re]
    simp_rw [hre]; rw [integral_norm_pow_exp_gaussian]
    rw [show (1 : ℝ) / π * (π * ↑(Nat.factorial a)) = ↑(Nat.factorial a) from by
      field_simp]
  · -- Off-diagonal case: a ≠ b
    rw [if_neg hab, gaussian_monomial_moments_off_diag hab, mul_zero]

/-- Explicit finite expansion for the true Hermite basis vector `Phi k n`. -/
theorem phi_explicit :
    ∀ {k n : ℕ} {z : ℂ},
      Phi k n z =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
          Finset.sum (Finset.range (min k n + 1)) (fun j =>
            ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              z ^ (n - j) * (star z) ^ (k - j)) := by
  intro k n z
  rfl

/-- Powers of the basic Fourier mode remain Fourier modes. -/
private lemma fourier_one_pow (n : ℕ) (t : Circle) :
    ((fourier (1 : ℤ) t : ℂ) ^ n) = fourier (n : ℤ) t := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, ← fourier_add]
      norm_num

/-- The circle point has the expected Fourier power expansion. -/
private lemma circlePoint_pow (r : ℝ) (t : Circle) (n : ℕ) :
    (circlePoint r t : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) * fourier (n : ℤ) t := by
  change (((r : ℂ) * (fourier (1 : ℤ) t : ℂ)) ^ n) =
    ((r ^ n : ℝ) : ℂ) * fourier (n : ℤ) t
  rw [mul_pow, fourier_one_pow]
  norm_cast

/-- The conjugate circle point has the expected Fourier power expansion. -/
private lemma star_circlePoint_pow (r : ℝ) (t : Circle) (m : ℕ) :
    star (circlePoint r t) ^ m = ((r ^ m : ℝ) : ℂ) * fourier (-(m : ℤ)) t := by
  have hstar : star (circlePoint r t) = (r : ℂ) * fourier (-1 : ℤ) t := by
    change (starRingEnd ℂ) (circlePoint r t) = _
    unfold circlePoint HermiteLEAN.circlePoint
    rw [map_mul, Complex.conj_ofReal]; congr 1
    exact (fourier_neg (n := 1) (x := t)).symm
  rw [hstar, mul_pow]; congr 1; · push_cast; rfl
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← fourier_add]; congr 1; push_cast; ring_nf

-- The proof expands the polar normalization in the `Phi` polar formula.
/-- Polar formula for `Phi k n`. -/
theorem phi_polar :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        ∀ t : Circle,
          Phi k n (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                ((qkn k n r : ℂ) * fourier (n : ℤ) t) := by
  intro k n r hr t
  simp only [Phi, qkn, circleLeadingFactor]
  set S := Finset.range (min k n + 1)
  have hterm : ∀ j ∈ S,
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        (circlePoint r t) ^ (n - j) * star (circlePoint r t) ^ (k - j) =
      ((r ^ k : ℝ) : ℂ) * (fourier (-(k : ℤ)) t : ℂ) * (fourier ((n : ℤ)) t : ℂ) *
        (((-1 : ℝ) ^ j * (Nat.choose k j : ℝ) *
          ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
          r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ) := by
    intro j hj
    have hjk : j ≤ k := by simp [S] at hj; omega
    have hjn : j ≤ n := by simp [S] at hj; omega
    rw [circlePoint_pow, star_circlePoint_pow]
    have hf : (fourier ((n - j : ℕ) : ℤ) t : ℂ) * fourier (-(k - j : ℕ) : ℤ) t =
        (fourier (-(k : ℤ)) t : ℂ) * fourier ((n : ℤ)) t := by
      rw [← fourier_add, ← fourier_add]; congr 1
      have h1 : ((n - j : ℕ) : ℤ) = (n : ℤ) - (j : ℤ) := by omega
      have h2 : ((k - j : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := by omega
      rw [h1, h2]; ring_nf
    have hrpow : ((r ^ (n - j) : ℝ) : ℂ) * ((r ^ (k - j) : ℝ) : ℂ) =
        ((r ^ k : ℝ) : ℂ) * ((r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
      rw [← pow_add, show n - j + (k - j) = n + k - 2 * j from by omega]
      rw [← zpow_natCast r (n + k - 2 * j), ← zpow_natCast r k,
        ← zpow_add₀ (ne_of_gt hr)]
      congr 1; rw [Nat.cast_sub (by omega : 2 * j ≤ n + k)]; push_cast; ring
    calc _ = ((-1 : ℂ) ^ j * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
          (((r ^ (n - j) : ℝ) : ℂ) * ((r ^ (k - j) : ℝ) : ℂ)) *
          ((fourier ((n - j : ℕ) : ℤ) t : ℂ) *
            fourier (-(k - j : ℕ) : ℤ) t) := by ring
      _ = ((-1 : ℂ) ^ j * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
          (((r ^ k : ℝ) : ℂ) * ((r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ)) *
          ((fourier (-(k : ℤ)) t : ℂ) *
            fourier ((n : ℤ)) t) := by rw [hrpow, hf]
      _ = _ := by push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Real.sqrt_mul (Nat.cast_nonneg _)]
  simp_rw [← Complex.ofReal_sum S]
  push_cast; ring

/-- Explicit finite Laurent expansion for the radial coefficient `qkn`. -/
theorem qkn_explicit :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        qkn k n r =
          (1 / Real.sqrt (Nat.factorial n : ℝ)) *
            Finset.sum (Finset.range (min k n + 1)) (fun j =>
              ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                r ^ ((n : ℤ) - 2 * (j : ℤ))) := by
  intro k n r hr
  rfl

/-- Backward-compatible alias for the explicit Laurent expansion of `qkn`. -/
theorem qkn_structure :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        qkn k n r =
          (1 / Real.sqrt (Nat.factorial n : ℝ)) *
            Finset.sum (Finset.range (min k n + 1)) (fun j =>
              ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                r ^ ((n : ℤ) - 2 * (j : ℤ))) := by
  intro k n r hr
  exact qkn_explicit (k := k) (n := n) (r := r) hr

/-- The circle coefficients `qkn` remain fixed by complex conjugation. -/
@[simp] theorem qkn_real :
    ∀ {k n : ℕ} {r : ℝ}, star (qkn k n r : ℂ) = (qkn k n r : ℂ) := by
  intro k n r
  simp [qkn]

/-- Compatibility form of the leading-term asymptotic for `qkn`. -/
-- Helper: for r ≥ 1 and j ≥ 1, r ^ (-2 * (j : ℤ)) ≤ r ^ (-2 : ℤ)
private lemma zpow_neg_two_mul_le {r : ℝ} (hr : 1 ≤ r) {j : ℕ} (hj : 1 ≤ j) :
    r ^ (-2 * (j : ℤ)) ≤ r ^ (-2 : ℤ) := by
  apply zpow_le_zpow_right₀ hr
  omega

-- Helper: r ^ (-2 : ℤ) = 1 / r ^ 2
private lemma zpow_neg_two_eq (r : ℝ) :
    r ^ (-2 : ℤ) = 1 / r ^ 2 := by
  have : r ^ (-2 : ℤ) = (r ^ (2 : ℕ))⁻¹ := by
    rw [zpow_neg]; rfl
  rw [this, inv_eq_one_div]

-- Helper: zpow subtraction for positive reals
private lemma zpow_sub_mul {r : ℝ} (hr : r ≠ 0) (a b : ℤ) :
    r ^ a = r ^ b * r ^ (a - b) := by
  rw [← zpow_add₀ hr b (a - b), show b + (a - b) = a from by omega]

-- Helper: the j=0 term of the qkn expansion equals the leading constant times r^n
private lemma qkn_j0_term (k n : ℕ) :
    ((-1 : ℝ) ^ 0) * (Nat.choose k 0 : ℝ) *
      ((Nat.factorial n : ℝ) / (Nat.factorial (n - 0) : ℝ)) = 1 := by
  simp [Nat.factorial_ne_zero]

-- Core bound: for r ≥ 1, ‖qkn(k,n,r)/r^n - 1/√n!‖ ≤ M / r^2
private lemma qkn_div_rn_bound (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ε : ℝ), 0 < ε →
      ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ r : ℝ, R0 ≤ r →
        ‖(qkn k n r : ℂ) / ((r : ℂ) ^ n) -
          ((1 / Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ)‖ ≤ ε := by
  set c := 1 / Real.sqrt (Nat.factorial n : ℝ) with hc_def
  have hc_pos : 0 < c := by positivity
  set M := c * ∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
    ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) with hM_def
  have hM_nn : 0 ≤ M := by
    apply mul_nonneg (le_of_lt hc_pos)
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨M, hM_nn, fun ε hε => ?_⟩
  refine ⟨max (Real.sqrt (M / ε) + 1) 1, le_max_right _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrn_pos : 0 < r ^ n := pow_pos hr_pos n
  rw [show (qkn k n r : ℂ) / ((r : ℂ) ^ n) - ((c : ℝ) : ℂ) =
    ((qkn k n r / r ^ n - c : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real]
  have hqkn : qkn k n r / r ^ n = c *
      ∑ j ∈ Finset.range (min k n + 1),
        ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
          ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
          r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) := by
    unfold qkn
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have : r ^ ((n : ℤ) - 2 * (j : ℤ)) / r ^ n =
        r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) := by
      rw [zpow_sub_mul (ne_of_gt hr_pos) ((n : ℤ) - 2 * (j : ℤ)) (n : ℤ)]
      rw [zpow_natCast]
      exact mul_div_cancel_left₀ _ (pow_ne_zero n (ne_of_gt hr_pos))
    rw [mul_div_assoc, this]
  set S := fun j => ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
      ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
      r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) with hS_def
  have h0_in : 0 ∈ Finset.range (min k n + 1) := Finset.mem_range.mpr (by omega)
  have hS0 : S 0 = 1 := by
    simp [hS_def, Nat.factorial_ne_zero]
  have hdiff : qkn k n r / r ^ n - c = c *
      (∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j) := by
    rw [hqkn]
    rw [show ∑ j ∈ Finset.range (min k n + 1), S j =
      S 0 + ∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j from
        (Finset.add_sum_erase _ S h0_in).symm]
    rw [hS0, mul_add, mul_one]
    ring
  have htail_bound : |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j| ≤
      (∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2 := by
    calc |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j|
        ≤ ∑ j ∈ (Finset.range (min k n + 1)).erase 0, |S j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ (Finset.range (min k n + 1)).erase 0,
            ((Nat.choose k j : ℝ) *
              ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) /
                r ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj_pos : 1 ≤ j := by
            rw [Finset.mem_erase] at hj
            omega
          rw [hS_def]
          simp only []
          rw [abs_mul, abs_mul, abs_mul]
          calc |(-1 : ℝ) ^ j| * |(Nat.choose k j : ℝ)| *
                |(Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)| *
                |r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ))|
              = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                |r ^ ((-2 : ℤ) * (j : ℤ))| := by
                rw [show ((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ) = (-2 : ℤ) * (j : ℤ) from by omega]
                rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
                rw [abs_of_nonneg (Nat.cast_nonneg _)]
                rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
            _ ≤ (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                |r ^ ((-2 : ℤ))| := by
                apply mul_le_mul_of_nonneg_left
                · rw [abs_zpow, abs_of_pos hr_pos, abs_zpow, abs_of_pos hr_pos]
                  apply zpow_le_zpow_right₀ hr1
                  omega
                · apply mul_nonneg (Nat.cast_nonneg _)
                    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            _ = (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) /
                  (Nat.factorial (n - j) : ℝ)) / r ^ 2 := by
                rw [zpow_neg_two_eq, abs_of_nonneg (by positivity)]
                ring
      _ ≤ (∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro j _ _
          apply div_nonneg
          · apply mul_nonneg (Nat.cast_nonneg _)
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          · positivity
  rw [hdiff, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt hc_pos)]
  calc c * |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j|
      ≤ c * ((∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2) :=
        mul_le_mul_of_nonneg_left htail_bound (le_of_lt hc_pos)
    _ = M / r ^ 2 := by ring
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos hr_pos 2)]
        by_cases hM0 : M = 0
        · rw [hM0]; positivity
        · have hMpos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
          have hge : r ≥ Real.sqrt (M / ε) + 1 := le_trans (le_max_left _ _) hr
          have hr_sq : r ^ 2 ≥ M / ε := by
            have : r ≥ Real.sqrt (M / ε) := by linarith
            calc r ^ 2 = r * r := by ring
              _ ≥ Real.sqrt (M / ε) * Real.sqrt (M / ε) := by
                  apply mul_le_mul this this
                  · exact Real.sqrt_nonneg _
                  · linarith
              _ = M / ε := by rw [Real.mul_self_sqrt (le_of_lt (div_pos hMpos hε))]
          have : ε * r ^ 2 ≥ ε * (M / ε) :=
            mul_le_mul_of_nonneg_left hr_sq (le_of_lt hε)
          rw [mul_div_cancel₀ M (ne_of_gt hε)] at this
          linarith

theorem qkn_top_term_asymptotic :
    ∀ k n : ℕ,
      ∃ c : ℝ,
        c ≠ 0 ∧
          ∀ ε : ℝ,
            0 < ε →
              ∃ R0 : ℝ,
                ∀ r ≥ R0, ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - (c : ℂ)‖ ≤ ε := by
  intro k n
  refine ⟨1 / Real.sqrt (Nat.factorial n : ℝ), by positivity, ?_⟩
  intro ε hε
  obtain ⟨_, _, hbound⟩ := qkn_div_rn_bound k n
  obtain ⟨R₀, _, hR₀⟩ := hbound ε hε
  exact ⟨R₀, fun r hr => hR₀ r hr⟩

/-- After dividing by `r^n`, `qkn k n r` converges to its explicit top term. -/
theorem qkn_top_term_limit :
    ∀ k n : ℕ,
      ∀ ε : ℝ,
        0 < ε →
          ∃ R0 : ℝ,
            1 ≤ R0 ∧
              ∀ r : ℝ,
                R0 ≤ r →
                  ‖(qkn k n r : ℂ) / (r ^ n : ℂ) -
                      ((1 / Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ)‖ ≤ ε := by
  intro k n ε hε
  obtain ⟨_, _, hbound⟩ := qkn_div_rn_bound k n
  exact hbound ε hε

/-- Each `qkn k n` eventually dominates a positive multiple of `r^n`. -/
theorem qkn_eventual_lower_bound :
    ∀ k n : ℕ,
      ∃ R c : ℝ,
        1 ≤ R ∧
          0 < c ∧
            ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := by
  intro k n
  obtain ⟨c₀, hc₀ne, hlim⟩ := qkn_top_term_asymptotic k n
  have hc₀pos : 0 < ‖(c₀ : ℂ)‖ := by
    rw [Complex.norm_real, norm_pos_iff]
    exact hc₀ne
  set ε := ‖(c₀ : ℂ)‖ / 2 with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨R₀, hR₀⟩ := hlim ε hε
  refine ⟨max R₀ 1, ε, le_max_right _ _, hε, fun r hr => ?_⟩
  have hrR₀ : r ≥ R₀ := le_trans (le_max_left _ _) hr
  have hrge1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hrge1
  have hspec := hR₀ r hrR₀
  -- We have ‖qkn/r^n - c₀‖ ≤ ε = ‖c₀‖/2
  -- So ‖qkn/r^n‖ ≥ ‖c₀‖ - ε = ε
  have hrnne : (r ^ n : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (ne_of_gt hr_pos)
  have hrn_pos : (0 : ℝ) < r ^ n := pow_pos hr_pos n
  have h_tri : ε ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ := by
    have h1 := norm_sub_norm_le (c₀ : ℂ) ((qkn k n r : ℂ) / (r ^ n : ℂ))
    -- h1 : ‖c₀‖ - ‖qkn/r^n‖ ≤ ‖c₀ - qkn/r^n‖
    rw [norm_sub_rev] at h1
    -- h1 : ‖c₀‖ - ‖qkn/r^n‖ ≤ ‖qkn/r^n - c₀‖
    linarith
  rw [norm_div] at h_tri
  have hrn_norm : ‖(r ^ n : ℂ)‖ = r ^ n := by
    rw [show (r : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hrn_pos)]
  rw [hrn_norm] at h_tri
  rw [le_div_iff₀ hrn_pos] at h_tri
  linarith [Complex.norm_real (qkn k n r)]

/-- The radial coefficient `qkn k n` is eventually nonvanishing on large radii. -/
theorem qkn_eventually_nonzero :
    ∀ k n : ℕ,
      ∃ R0 : ℝ,
        1 ≤ R0 ∧
          ∀ r ≥ R0, qkn k n r ≠ 0 := by
  intro k n
  obtain ⟨R, c, hR, hc, hbound⟩ := qkn_eventual_lower_bound k n
  refine ⟨R, hR, fun r hr hqkn => ?_⟩
  have h1 := hbound r hr
  rw [hqkn, Complex.ofReal_zero, norm_zero] at h1
  have h2 : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR) hr
  linarith [mul_pos hc (pow_pos h2 n)]

/-- Lower modes are eventually suppressed by at least one power of `r`. -/
theorem qkn_ratio_control :
    ∀ {k n d : ℕ},
      n < d →
        ∃ C R0 : ℝ,
          0 < C ∧
            1 ≤ R0 ∧
              ∀ r : ℝ,
                R0 ≤ r →
                  ‖((qkn k n r : ℂ) / (qkn k d r : ℂ))‖ ≤ C / r := by
  intro k n d hnd
  -- Get upper bound on numerator: for large r, ‖qkn(k,n,r)/r^n - cn‖ ≤ 1
  obtain ⟨_, _, hbound_n⟩ := qkn_div_rn_bound k n
  obtain ⟨Rn, hRn1, hRn⟩ := hbound_n 1 one_pos
  -- Get lower bound on denominator: for large r, cd * r^d ≤ ‖qkn(k,d,r)‖
  obtain ⟨Rd, cd, hRd1, hcd, hRd⟩ := qkn_eventual_lower_bound k d
  set cn := 1 / Real.sqrt (Nat.factorial n : ℝ) with hcn_def
  have hcn_pos : 0 < cn := by positivity
  set C := (cn + 1) / cd
  refine ⟨C, max Rn Rd, by positivity, le_max_of_le_left hRn1, fun r hr => ?_⟩
  have hrRn : Rn ≤ r := le_trans (le_max_left _ _) hr
  have hrRd : Rd ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := le_trans hRn1 hrRn
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  -- Upper bound on numerator
  have hnum_spec := hRn r hrRn
  -- ‖qkn(k,n,r)/r^n - cn‖ ≤ 1, so ‖qkn(k,n,r)‖ ≤ (cn + 1) * r^n
  have hnum_upper : ‖(qkn k n r : ℂ)‖ ≤ (cn + 1) * r ^ n := by
    have h1 : ‖(qkn k n r : ℂ) / ((r : ℂ) ^ n)‖ ≤ cn + 1 := by
      have h2 := norm_sub_norm_le ((qkn k n r : ℂ) / ((r : ℂ) ^ n)) ((cn : ℝ) : ℂ)
      rw [Complex.norm_real] at h2
      have : ‖cn‖ = cn := Real.norm_of_nonneg (le_of_lt hcn_pos)
      linarith
    rw [norm_div, show ‖((r : ℂ) ^ n)‖ = r ^ n from by
      rw [show (r : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (le_of_lt hr_pos) n)]] at h1
    rwa [div_le_iff₀ (pow_pos hr_pos n)] at h1
  -- Lower bound on denominator
  have hden_lower : cd * r ^ d ≤ ‖(qkn k d r : ℂ)‖ := hRd r hrRd
  -- qkn k d r ≠ 0 since cd > 0 and r^d > 0
  have hden_ne : (qkn k d r : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden_lower
    linarith [mul_pos hcd (pow_pos hr_pos d)]
  -- The ratio bound
  rw [norm_div]
  rw [div_le_div_iff₀ (norm_pos_iff.mpr hden_ne) hr_pos]
  -- ‖qkn n‖ * r ≤ (cn+1)*r^(n+1) ≤ (cn+1)*r^d = C*cd*r^d ≤ C*‖qkn d‖
  calc ‖(qkn k n r : ℂ)‖ * r
      ≤ (cn + 1) * r ^ n * r := by
          linarith [mul_le_mul_of_nonneg_right
            hnum_upper (le_of_lt hr_pos)]
    _ = (cn + 1) * r ^ (n + 1) := by ring
    _ ≤ (cn + 1) * r ^ d := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_right₀ hr1 hnd
          · linarith
    _ = C * (cd * r ^ d) := by
          simp only [C]
          field_simp
    _ ≤ C * ‖(qkn k d r : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_left hden_lower
          positivity

/-! ## Finite-First Basis API -/

/-- Unit circle power factorization: ω^{p-j} * conj(ω)^{k-j} = ω^p * conj(ω)^k when |ω|=1. -/
private lemma circle_pow_factor (ω : _root_.Circle) {j k p : ℕ} (hjk : j ≤ k) (hjp : j ≤ p) :
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k := by
  have hωconj : (ω : ℂ) * star (ω : ℂ) = 1 := by
    rw [star_def]
    rw [show (starRingEnd ℂ) (ω : ℂ) = ↑(ω⁻¹ : _root_.Circle) from
      (_root_.Circle.coe_inv_eq_conj ω).symm]
    rw [← _root_.Circle.coe_mul, mul_inv_cancel, _root_.Circle.coe_one]
  have key : ((ω : ℂ) * star (ω : ℂ)) ^ j = 1 := by rw [hωconj]; simp
  rw [mul_pow] at key
  conv_rhs => rw [← Nat.sub_add_cancel hjp, ← Nat.sub_add_cancel hjk, pow_add, pow_add]
  rw [show (ω : ℂ) ^ (p - j) * (ω : ℂ) ^ j * (star (ω : ℂ) ^ (k - j) * star (ω : ℂ) ^ j) =
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) * ((ω : ℂ) ^ j * star (ω : ℂ) ^ j) from by ring]
  rw [key, mul_one]

/-- Equivariance of Phi under rotation: Phi k p (ω*z) = ω^p * conj(ω)^k * Phi k p z
for any unit complex number ω. -/
private lemma Phi_rotation_equivariant (ω : _root_.Circle) (z : ℂ) (k p : ℕ) :
    Phi k p ((ω : ℂ) * z) = (ω : ℂ) ^ p * star (ω : ℂ) ^ k * Phi k p z := by
  simp only [Phi, mul_pow, star_mul]
  -- Both sides have the same structure. We convert to a termwise equality.
  -- Reduce to termwise equality: for each j, the j-th LHS summand = j-th RHS summand
  -- after pulling ω^p * star(ω)^k through the normalization constant and sum.
  -- Strategy: multiply both sides by √(k!p!) to cancel the denominator, then compare termwise.
  -- Actually, just show the two sides are equal directly:
  suffices h : ∀ j ∈ Finset.range (min k p + 1),
      (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j)) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) by
    have hsum := Finset.sum_congr rfl h
    rw [← Finset.mul_sum] at hsum
    -- hsum: ∑ LHS_terms = ω^p * star(ω)^k * ∑ RHS_terms
    -- Goal: C * ∑ LHS = ω^p * star(ω)^k * (C * ∑ RHS)
    linear_combination (1 / ↑(Real.sqrt (↑k.factorial * ↑p.factorial))) * hsum
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  have hjp : j ≤ p := by simp [Finset.mem_range] at hj; omega
  have key := circle_pow_factor ω hjk hjp
  -- Replace ω^{p-j} * star(ω)^{k-j} by ω^p * star(ω)^k, then ring
  calc (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j))
      = ((ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j)) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by ring
    _ = ((ω : ℂ) ^ p * star (ω : ℂ) ^ k) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by rw [key]

/-! ## Helpers for the diagonal case of phi_orthonormal -/

-- Helper: (-1)^(k-j) = (-1)^k * (-1)^j for j ≤ k
private lemma neg_one_pow_sub {j k : ℕ} (hj : j ≤ k) :
    (-1 : ℤ) ^ (k - j) = (-1 : ℤ) ^ k * (-1 : ℤ) ^ j := by
  have key : (-1 : ℤ) ^ (k - j) * (-1 : ℤ) ^ j = (-1 : ℤ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hsq : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← pow_add]
    exact_mod_cast (neg_one_pow_eq_one_iff_even (R := ℤ) (by omega)).mpr ⟨j, rfl⟩
  calc (-1 : ℤ) ^ (k - j)
      = (-1) ^ (k - j) * ((-1) ^ j * (-1) ^ j) := by rw [hsq, mul_one]
    _ = (-1) ^ (k - j) * (-1) ^ j * (-1) ^ j := by rw [mul_assoc]
    _ = (-1) ^ k * (-1) ^ j := by rw [key]

private lemma alternating_vandermonde_coeff_poly (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      ((((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s * Polynomial.X ^ k).coeff N) := by
  let A : Polynomial ℤ := (Polynomial.C (1 : ℤ)) + Polynomial.X
  have hinner :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
        Polynomial.X ^ k := by
    let f : ℕ → Polynomial ℤ := fun j =>
      A ^ j * (-1 : Polynomial ℤ) ^ (k - j) * Polynomial.C (k.choose j : ℤ)
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
          ∑ j ∈ Finset.range (k + 1), f ((k + 1) - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
            have hsub : k - (k - j) = j := by omega
            simp [f, A, hsub, Nat.choose_symm hjk, mul_assoc, mul_comm]
      _ = ∑ j ∈ Finset.range (k + 1), f j := Finset.sum_range_reflect f (k + 1)
      _ = (A + (-1 : Polynomial ℤ)) ^ k := by
            symm
            simpa [f, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
              (add_pow A (-1 : Polynomial ℤ) k)
      _ = Polynomial.X ^ k := by
            simp [A, add_left_comm, add_comm]
  have hpoly :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
        A ^ s * Polynomial.X ^ k := by
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
          ∑ j ∈ Finset.range (k + 1),
            A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
              have hsub : k + s - j = s + (k - j) := by omega
              calc
                ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))) =
                    ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (s + (k - j)))) := by
                      simp [hsub]
                _ = ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ s * A ^ (k - j))) := by
                      simp [pow_add]
                _ = A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
      _ = A ^ s * ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) := by
            rw [Finset.mul_sum]
      _ = A ^ s * Polynomial.X ^ k := by rw [hinner]
  have hpolycoeff :
      ∑ j ∈ Finset.range (k + 1),
          (((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))).coeff N) =
        (A ^ s * Polynomial.X ^ k).coeff N := by
    simpa using congrArg (fun p : Polynomial ℤ => p.coeff N) hpoly
  have hsum :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      (A ^ s * Polynomial.X ^ k).coeff N := by
    refine Eq.trans ?_ hpolycoeff
    apply Finset.sum_congr rfl
    intro j hj
    rw [zsmul_eq_mul]
    simp only [A, Polynomial.C_1, Polynomial.coeff_intCast_mul,
      Polynomial.coeff_one_add_X_pow]
    push_cast
    ring
  simpa [A] using hsum

private lemma alternating_vandermonde_coeff (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      if k ≤ N then ↑(s.choose (N - k)) else 0 := by
  calc
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
        ((((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s * Polynomial.X ^ k).coeff N) :=
      alternating_vandermonde_coeff_poly k s N
    _ = if k ≤ N then (((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s).coeff (N - k) else 0 := by
          simpa using
            (Polynomial.coeff_mul_X_pow' (((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s) k N)
    _ = if k ≤ N then ↑(s.choose (N - k)) else 0 := by
          by_cases h : k ≤ N <;> simp [h, Polynomial.coeff_one_add_X_pow]

private theorem alternating_vandermonde (k s t : ℕ) (_ht : 1 ≤ t) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose (k + t)) = ↑(s.choose t) := by
  simpa [if_pos (by omega), Nat.add_sub_cancel_left k t] using
    alternating_vandermonde_coeff k s (k + t)

private theorem alternating_vandermonde_zero (k s : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose k) = 1 := by
  simpa [if_pos (Nat.le_refl k)] using alternating_vandermonde_coeff k s k

private theorem alternating_vandermonde_vanish (k s r : ℕ) (hr : r < k) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose r) = 0 := by
  simpa [if_neg (Nat.not_le_of_lt hr)] using alternating_vandermonde_coeff k s r

/-! ## Double-sum identity for phi_orthonormal diagonal case -/

-- Factoring: descFact(m, j) * (m+k-i-j)! = m! * C(m+k-i-j, k-i) * (k-i)!
private lemma desc_fact_mul_fact (k m i j : ℕ) (hi : i ≤ k) (hj : j ≤ m) :
    Nat.descFactorial m j * Nat.factorial (m + k - i - j) =
    Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by
  have hki : k - i ≤ m + k - i - j := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hki
  have hsubt : m + k - i - j - (k - i) = m - j := by omega
  rw [hsubt] at h1
  have h2 := Nat.factorial_mul_descFactorial hj
  calc Nat.descFactorial m j * Nat.factorial (m + k - i - j)
      = Nat.descFactorial m j * (Nat.choose (m + k - i - j) (k - i) *
          Nat.factorial (k - i) * Nat.factorial (m - j)) := by rw [h1]
    _ = (Nat.factorial (m - j) * Nat.descFactorial m j) *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by ring
    _ = Nat.factorial m *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by rw [h2]
    _ = Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by ring

-- Inner sum factoring for fixed i
-- Note: we prove the SUM equality, not per-term equality (which fails when j > m and i = k)
-- The proof repeatedly refactors the inner binomial sum across two disjoint index ranges.
private lemma inner_sum_factor (k m i : ℕ) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
      ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
        ↑(Nat.choose (m + k - i - j) (k - i)) := by
  -- Split into j ≤ m and j > m
  -- For j > m: descFact(m,j) = 0 so LHS term = 0.
  --            Also C(m+k-i-j, k-i) = 0 when i < k
  --            (since m+k-i-j < k-i).
  --            When i = k, k-i = 0, C(anything, 0) = 1,
  --            but j > m and j ≤ k = i ≤ m, contradiction!
  -- So actually j > m can't happen when i ≤ m and j ≤ k
  -- (since j ≤ k ≤ ... wait, j can be > m if k > m).
  -- But i ≤ m, so this is fine. When j > m: descFact = 0 makes LHS terms 0.
  -- For RHS: when j > m and i < k: C(m+k-i-j, k-i) = 0, so RHS term = 0. ✓
  -- When j > m and i = k: j > m ≥ i = k, but j ∈ range(k+1) means j ≤ k,
  -- contradicting j > m ≥ k. So impossible.
  -- So for j > m with j ≤ k: need i < k. Since i ≤ m < j ≤ k, we get
  -- i ≤ m < k, so i < k. ✓
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  by_cases hjm : j ≤ m
  · have h := desc_fact_mul_fact k m i j hi hjm
    have hcast : (↑(Nat.descFactorial m j) : ℤ) * ↑(Nat.factorial (m + k - i - j)) =
        ↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
        ↑(Nat.factorial (k - i)) := by exact_mod_cast h
    calc (-1 : ℤ) ^ j * ↑(k.choose j) * ↑(Nat.descFactorial m j) *
          ↑(Nat.factorial (m + k - i - j))
        = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by ring
      _ = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
          ↑(Nat.factorial (k - i))) := by rw [hcast]
      _ = ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
          ((-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.choose (m + k - i - j) (k - i))) := by ring
  · push Not at hjm
    -- j > m and j ≤ k, so i ≤ m < j ≤ k, hence i < k
    have hik : i < k := by omega
    have hdesc : Nat.descFactorial m j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hjm
    have hchoose : Nat.choose (m + k - i - j) (k - i) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hdesc, hchoose]

-- Inner sum at i = 0: equals m! * k!
private lemma inner_sum_at_zero (k m : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial k) := by
  have hrw : ∀ j, Nat.factorial (m + k - j) = Nat.factorial (m + k - 0 - j) := by
    intro j; simp
  simp_rw [hrw]
  rw [inner_sum_factor k m 0 (Nat.zero_le k) (Nat.zero_le m)]
  simp only [Nat.sub_zero]
  have hrw2 : ∀ j, Nat.choose (m + k - j) k = Nat.choose (k + m - j) k := by
    intro j; congr 1; omega
  simp_rw [hrw2]
  rw [alternating_vandermonde_zero k m]; ring

-- Inner sum at i ≥ 1: vanishes
private lemma inner_sum_vanish_pos (k m i : ℕ)
    (hi_pos : 1 ≤ i) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) = 0 := by
  rw [inner_sum_factor k m i hi him]
  have hrw : ∀ j, Nat.choose (m + k - i - j) (k - i) =
      Nat.choose (k + (m - i) - j) (k - i) := by intro j; congr 1; omega
  simp_rw [hrw]
  rw [alternating_vandermonde_vanish k (m - i) (k - i) (by omega)]
  ring

-- The double sum identity
-- This is the heaviest combinatorial normalization in the file:
-- expand, swap, factor, then collapse.
private theorem double_sum_vandermonde (k m : ℕ) :
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
      ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
      ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial k) * ↑(Nat.factorial m) := by
  have hfactor : ∀ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
        ↑(Nat.factorial (m + k - i - j)) =
      (-1 : ℤ) ^ i * ↑(k.choose i) * ↑(Nat.descFactorial m i) *
        (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by
    intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring
  rw [Finset.sum_congr rfl hfactor]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
      Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    rw [inner_sum_at_zero k m]; ring
  · intro i hi hi_ne
    have hik : i ≤ k := by simp [Finset.mem_range] at hi; omega
    by_cases him : i ≤ m
    · rw [inner_sum_vanish_pos k m i (by omega) hik him]; ring
    · push Not at him
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr him]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.zero_lt_succ k))

-- Helper: each monomial term ‖z‖^{2a} * exp(-‖z‖²) is integrable
private lemma integrable_norm_pow_exp (a : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2)) := by
  by_contra h
  have hint := integral_norm_pow_exp_gaussian a
  rw [MeasureTheory.integral_undef h] at hint
  linarith [show (0 : ℝ) < π * (Nat.factorial a : ℝ) from by positivity]

-- The main diagonal integral computation
-- The integral proof unfolds the diagonal formula and runs the full double-sum normalization.
-- double-sum expansion, cross-term simplification, and Vandermonde application
private theorem norm_sq_phi_integral (k m : ℕ) :
    ∫ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  -- Step 1: Express ‖Phi‖² * exp as a double sum * exp pointwise
  -- ‖Phi k m z‖² = (1/(k!*m!)) * Σ_{i,j} (-1)^{i+j} C(k,i) C(k,j)
  --   * descFact(m,i) descFact(m,j) ‖z‖^{2(m+k-i-j)}
  have hnsq : ∀ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial m : ℝ))) *
      ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro z
    suffices h : ‖Phi k m z‖ ^ 2 =
        (1 / ((↑k.factorial : ℝ) * ↑m.factorial)) *
        ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
          ↑(m.descFactorial i) * ↑(m.descFactorial j) *
          ‖z‖ ^ (2 * (m + k - i - j)) by
      rw [h, mul_assoc, Finset.sum_mul]
      congr 1; apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    simp only [Phi]
    rw [norm_mul, mul_pow]
    have hpre : ‖(1 : ℂ) / ↑√(↑k.factorial * ↑m.factorial)‖ ^ 2 =
        1 / ((↑k.factorial : ℝ) * ↑m.factorial) := by
      rw [norm_div, norm_one, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
      rw [one_div, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _), one_div]
    rw [hpre]; congr 1
    set S := Finset.range (min k m + 1)
    set g : ℕ → ℂ := fun j =>
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        z ^ (m - j) * star z ^ (k - j)
    change ‖∑ j ∈ S, g j‖ ^ 2 = _
    have hnorm_re : ‖∑ j ∈ S, g j‖ ^ 2 =
        ((∑ i ∈ S, g i) * (starRingEnd ℂ) (∑ j ∈ S, g j)).re := by
      rw [mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hnorm_re, map_sum, Finset.sum_mul_sum]
    simp_rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    have him : i ≤ m := by rw [Finset.mem_range] at hi; omega
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have hjk : j ≤ k := by rw [Finset.mem_range] at hj; omega
    -- Cross-term: (g i * conj(g j)).re = coeff * ‖z‖^{2(m+k-i-j)}
    -- Step 1: Expand conj(g j) - coefficients are real, conj swaps z and star z
    have hconj_g : (starRingEnd ℂ) (g j) =
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j) := by
      simp only [g, map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀]
      congr 1; congr 1; exact star_star z
    rw [hconj_g]; simp only [g]
    -- Step 2: Rearrange z-power product
    have hzpow : z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j)) =
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
      have h1 : z ^ (m - i) * z ^ (k - j) = z ^ (m + k - i - j) := by
        rw [← pow_add]; congr 1; omega
      have h2 : star z ^ (k - i) * star z ^ (m - j) = star z ^ (m + k - i - j) := by
        rw [← pow_add]; congr 1; omega
      calc z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j))
        = (z ^ (m - i) * z ^ (k - j)) * (star z ^ (k - i) * star z ^ (m - j)) := by ring
        _ = z ^ (m + k - i - j) * star z ^ (m + k - i - j) := by rw [h1, h2]
        _ = ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
            rw [← mul_pow, show z * star z = ↑(‖z‖ ^ 2 : ℝ) from by
              rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj']
              push_cast; rfl]
            push_cast; rw [← pow_mul]
    -- Step 3: Rearrange the full product into coeff * ↑(‖z‖^{2a})
    have hprod : (-1 : ℂ) ^ i * ↑(k.choose i) * (↑m.factorial / ↑(m - i).factorial) *
        z ^ (m - i) * star z ^ (k - i) *
        ((-1) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j)) =
        ((-1 : ℂ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        (↑m.factorial / ↑(m - i).factorial) * (↑m.factorial / ↑(m - j).factorial)) *
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
      rw [← hzpow, pow_add]; ring
    rw [hprod]
    -- Step 4: Replace m!/(m-j)! with descFactorial
    have hfact_desc_i : (↑m.factorial : ℂ) / ↑(m - i).factorial = ↑(m.descFactorial i : ℕ) := by
      have hdvd : (m - i).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m i)
      rw [Nat.descFactorial_eq_div him]
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    have hfact_desc_j : (↑m.factorial : ℂ) / ↑(m - j).factorial = ↑(m.descFactorial j : ℕ) := by
      have hdvd : (m - j).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m j)
      rw [Nat.descFactorial_eq_div hjm]
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    rw [hfact_desc_i, hfact_desc_j]
    -- Step 5: Everything is now ↑(real), so .re = the real value
    rw [show (-1 : ℂ) ^ (i + j) * ↑↑(k.choose i) * ↑↑(k.choose j) *
        ↑↑(m.descFactorial i) * ↑↑(m.descFactorial j) =
        ↑((-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(m.descFactorial i) * ↑(m.descFactorial j)) from by push_cast; ring]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hnsq]
  rw [integral_const_mul]
  -- Step 2: Swap sum and integral (finite sums, each term is integrable)
  have hint_each : ∀ (i j : ℕ),
      Integrable (fun z : ℂ =>
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i j
    exact (integrable_norm_pow_exp (m + k - i - j)).const_mul _
  have hswap_outer : ∀ i ∈ Finset.range (min k m + 1),
      Integrable (fun z : ℂ =>
        ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
          (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
          (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i _; exact integrable_finsetSum _ (fun j _ => hint_each i j)
  rw [integral_finsetSum _ hswap_outer]
  have hswap_inner : ∀ i, ∫ z : ℂ, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      ∑ j ∈ Finset.range (min k m + 1), ∫ z : ℂ,
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro i; exact integral_finsetSum _ (fun j _ => hint_each i j)
  simp_rw [hswap_inner]
  -- Step 3: Compute each monomial integral
  have hcompute : ∀ (i j : ℕ),
      ∫ z : ℂ, (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) := by
    intro i j
    rw [integral_const_mul, integral_norm_pow_exp_gaussian]
  simp_rw [hcompute]
  -- Step 4: Extend sum range from (min k m + 1) to (k + 1)
  -- Extra terms have descFactorial m j = 0 (when j > m and k > m) or choose k j = 0 (when j > k)
  -- Actually, we can fold everything into the double_sum_vandermonde directly.
  -- First, factor out π and get the double sum matching double_sum_vandermonde
  have hfold : ∀ (i j : ℕ),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) =
      π * ((-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ)) := by
    intro i j; ring
  simp_rw [hfold]
  -- Pull π out of sums: Σ (π * g(i,j)) = π * Σ g(i,j)
  simp_rw [← Finset.mul_sum]
  -- Now goal: (1/(k!*m!)) * (π * Σ_i (π * Σ_j (...))) = π
  -- After pulling π out of both sums: (1/(k!*m!)) * π * Σ_{i,j} (...) = π
  -- But actually after simp_rw [← Finset.mul_sum], the inner sum already pulled π out.
  -- Let me check what the goal looks like and adjust.
  -- Goal should be: (1/(k!*m!)) * π * (Σ_i Σ_j coeff) = π
  -- Extend sum from range(min k m + 1) to range(k + 1)
  -- Extra terms have descFactorial m i = 0 (when i > m and k > m)
  -- or choose k i = 0 (when i > k, which doesn't happen since range stops at min k m ≤ k)
  -- When k ≤ m: min k m = k, so range(min k m + 1) = range(k + 1), no extension needed
  -- When k > m: min k m = m, extra terms for m < i ≤ k have descFactorial m i = 0
  have hext_j : ∀ i, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    intro i
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro j hj hj'
    rw [Finset.mem_range] at hj hj'
    push Not at hj'
    -- j ≥ min k m + 1 and j < k + 1, so j > min k m
    have hjm : m < j := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hjm]
  simp_rw [hext_j]
  have hext_i : ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    push Not at hi'
    have him : m < i := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr him]
  rw [hext_i]
  -- Now apply double_sum_vandermonde (cast from ℤ to ℝ)
  have hvand := double_sum_vandermonde k m
  -- Cast hvand from ℤ to ℝ
  have hvand_real : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by
    have := congr_arg (fun x : ℤ => (x : ℝ)) hvand
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at this
    convert this using 1
  rw [hvand_real]
  -- Now: (1/(k!*m!)) * π * (k! * m!) = π
  have hpos : (0 : ℝ) < (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by positivity
  field_simp

/-- The level-`k` basis is orthonormal for the weighted inner product. -/
theorem phi_orthonormal :
    ∀ {k m n : ℕ},
      weightedInner (Phi k m) (Phi k n) = if m = n then 1 else 0 := by
  intro k m n
  by_cases hmn : m = n
  · -- Diagonal case: m = n
    subst hmn
    rw [if_pos rfl]
    unfold weightedInner HermiteLEAN.weightedInner
    have hint : ∫ (z : ℂ), Phi k m z * (starRingEnd ℂ) (Phi k m z) *
        ↑(rexp (-‖z‖ ^ 2)) = ↑Real.pi := by
      have hreal : ∀ z : ℂ, Phi k m z * (starRingEnd ℂ) (Phi k m z) *
          ↑(rexp (-‖z‖ ^ 2)) = ↑(‖Phi k m z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        intro z; rw [mul_conj]; push_cast; rw [Complex.normSq_eq_norm_sq]
        ring_nf; simp [mul_comm]
      simp_rw [hreal, integral_complex_ofReal]
      congr 1
      exact norm_sq_phi_integral k m
    rw [hint]; field_simp [Real.pi_ne_zero]
  · -- Off-diagonal case: m ≠ n. Use rotation trick on ℂ-valued integrand.
    rw [if_neg hmn]
    -- The ℂ-valued integrand
    set f : ℂ → ℂ := fun z =>
      Phi k m z * star (Phi k n z) * (↑(Real.exp (-‖z‖ ^ 2)) : ℂ) with hf_def
    -- Pick ω on the unit circle with ω^{m-n} = -1
    set d : ℤ := (m : ℤ) - (n : ℤ)
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (by exact_mod_cast hmn)
    set ω : _root_.Circle := _root_.Circle.exp (Real.pi / (d : ℝ))
    set rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation ω
    -- f(ω z) = -f(z) because each monomial z^{p-j} conj(z)^{k-j} picks up
    -- ω^{p-j} conj(ω)^{k-j} = ω^{p-k} (independent of j, since |ω|=1),
    -- so Phi k p (ωz) = ω^{p-k} Phi k p z, and the inner product factor is ω^{m-n} = -1.
    -- ω^m * star(ω)^n = -1 (same proof as gaussian_monomial_moments_off_diag)
    have hωmn : (ω : ℂ) ^ m * star (ω : ℂ) ^ n = -1 := by
      rw [star_def, ← _root_.Circle.coe_inv_eq_conj]
      rw [← _root_.Circle.coe_pow, ← _root_.Circle.coe_pow, ← _root_.Circle.coe_mul]
      rw [show ω ^ m * ω⁻¹ ^ n = ω ^ d from by
        rw [show ω ^ m * ω⁻¹ ^ n = ω ^ m * (ω ^ n)⁻¹ from by rw [inv_pow],
          ← zpow_natCast ω m, ← zpow_natCast ω n, ← zpow_sub]]
      rw [show ω = _root_.Circle.exp (Real.pi / (d : ℝ)) from rfl,
        ← _root_.Circle.exp_intCast_mul (Real.pi / (d : ℝ)) d,
        show (d : ℝ) * (Real.pi / (d : ℝ)) = Real.pi from by field_simp]
      simp only [_root_.Circle.coe_exp, Complex.exp_pi_mul_I,
        ]
    -- |ω|^{2k} = 1
    have hωmod : (ω : ℂ) ^ k * star (ω : ℂ) ^ k = 1 := by
      rw [← mul_pow]
      rw [show (ω : ℂ) * star (ω : ℂ) = 1 from by
        rw [star_def, ← _root_.Circle.coe_inv_eq_conj, ← _root_.Circle.coe_mul,
          mul_inv_cancel, _root_.Circle.coe_one]]
      simp
    have hrot_f : ∀ z, f (rot z) = -f z := by
      intro z
      simp only [hf_def, rot, rotation_apply, norm_mul, _root_.Circle.norm_coe, one_mul]
      rw [Phi_rotation_equivariant ω z k m, Phi_rotation_equivariant ω z k n]
      simp only [star_mul, star_star, star_pow]
      -- After simplification: star(star ↑ω ^ k) becomes ↑ω ^ k (via star_pow + star_star)
      -- star(↑ω ^ n) becomes star(↑ω) ^ n (via star_pow)
      calc (ω : ℂ) ^ m * star (ω : ℂ) ^ k * Phi k m z *
            (star (Phi k n z) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ n)) *
            ↑(rexp (-‖z‖ ^ 2))
          = ((ω : ℂ) ^ m * star (ω : ℂ) ^ n) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ k) *
            (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by ring
        _ = -1 * 1 * (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by
            rw [hωmn, hωmod]
        _ = _ := by ring
    -- From ∫ f(rot z) = ∫ f(z) and f(rot z) = -f(z), get ∫ f = 0
    have hmp := rot.measurePreserving
    have hemb := rot.toHomeomorph.measurableEmbedding
    have hint_eq : ∫ z, f (rot z) = ∫ z, f z := hmp.integral_comp hemb f
    simp_rw [hrot_f, integral_neg] at hint_eq
    -- hint_eq : -(∫ f) = ∫ f, so ∫ f = 0
    have hfzero : ∫ z, f z = 0 := by
      set I := ∫ z, f z
      have h : -I = I := hint_eq
      have h2 : I + I = 0 := by nth_rw 1 [← neg_neg I, h]; exact neg_add_cancel I
      have h3 : 2 • I = 0 := by rw [two_nsmul]; exact h2
      exact_mod_cast (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℕ) ≠ 0)
    -- Connect to weightedInner
    unfold weightedInner HermiteLEAN.weightedInner
    rw [show (∫ z : ℂ, Phi k m z * (starRingEnd ℂ) (Phi k n z) *
        ↑(Real.exp (-‖z‖ ^ 2))) = ∫ z, f z from by rfl]
    rw [hfzero, mul_zero]

-- Phi_mem_Hk is proved below, after finiteHermiteSum_normSq

theorem continuous_Phi (k n : ℕ) : Continuous (Phi k n) := by
  unfold Phi
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ ?_
  intro j hj
  have hpow : Continuous (fun z : ℂ => z ^ (n - j) * (star z) ^ (k - j)) := by
    exact (continuous_id.pow (n - j)).mul (continuous_star.pow (k - j))
  have hterm : Continuous (fun z : ℂ =>
      (((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
        (z ^ (n - j) * (star z) ^ (k - j))) := by
    exact continuous_const.mul hpow
  simpa [mul_assoc] using hterm

theorem integrable_weightedDiag (k n : ℕ) :
    Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  let f : ℂ → ℝ := fun z => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  by_contra hf
  have hfC : ¬ Integrable (fun z : ℂ => (f z : ℂ)) := by
    intro hC
    apply hf
    convert hC.re using 1
    funext x
    exact (RCLike.ofReal_re (f x)).symm
  have hzero : weightedInner (Phi k n) (Phi k n) = 0 := by
    unfold weightedInner HermiteLEAN.weightedInner
    calc
      (1 / Real.pi : ℂ) *
          ∫ z : ℂ, Phi k n z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
        = (1 / Real.pi : ℂ) * ∫ z : ℂ, (f z : ℂ) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with z
            rw [mul_conj]
            simp [f, Complex.normSq_eq_norm_sq]
      _ = (1 / Real.pi : ℂ) * 0 := by
            rw [MeasureTheory.integral_undef hfC]
      _ = 0 := by ring
  have hone : weightedInner (Phi k n) (Phi k n) = 1 := by
    simpa using (phi_orthonormal (k := k) (m := n) (n := n))
  have h01 : (0 : ℂ) = 1 := by
    calc
      (0 : ℂ) = weightedInner (Phi k n) (Phi k n) := hzero.symm
      _ = 1 := hone
  norm_num at h01

theorem integrable_weightedCross (k m n : ℕ) :
    Integrable (fun z : ℂ =>
      Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  let f : ℂ → ℂ := fun z =>
    Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let g : ℂ → ℝ := fun z =>
    ((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)
  have hg : Integrable g := by
    have hm : Integrable (fun z : ℂ => ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k m
    have hn : Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k n
    have hs : Integrable (fun z : ℂ =>
      (‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) +
        (‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) := hm.add hn
    convert hs.const_mul (1 / 2) using 1
    funext z
    ring
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcontExp : Continuous (fun z : ℂ => (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
      exact
        Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_neg.comp (continuous_norm.pow 2)))
    exact ((continuous_Phi k m).mul (continuous_star.comp (continuous_Phi k n))).mul hcontExp
      |>.aestronglyMeasurable
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ g z := by
    intro z
    calc
      ‖f z‖ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
        have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
        calc
          ‖Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖
            = ‖Phi k m z * (starRingEnd ℂ) (Phi k n z)‖ *
                ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
                  rw [norm_mul]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
                rw [norm_mul]
                rw [show ‖(starRingEnd ℂ) (Phi k n z)‖ = ‖Phi k n z‖ by simp]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
      _ ≤ (((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)) := by
            have hsq :
                2 * (‖Phi k m z‖ * ‖Phi k n z‖) ≤ ‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2 := by
              nlinarith [sq_nonneg (‖Phi k m z‖ - ‖Phi k n z‖)]
            have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
            nlinarith
      _ = g z := by simp [g]
  exact MeasureTheory.Integrable.mono' hg hf_meas (Filter.Eventually.of_forall hbound)

private lemma weightedNormSq_eq_re_weightedInner (F : ℂ → ℂ) :
    weightedNormSq F = Complex.re (weightedInner F F) := by
  unfold HermitekLEAN.weightedNormSq HermiteLEAN.weightedNormSq
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ => F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
        = fun z : ℂ => ((‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    rw [show F z * (starRingEnd ℂ) (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.mul_conj' (F z)]
    simp
  rw [hfun, integral_complex_ofReal]
  simp

private lemma weightedInner_conj_symm (F G : ℂ → ℂ) :
    weightedInner F G = star (weightedInner G F) := by
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  have hpi : (starRingEnd ℂ) ((1 : ℂ) / ↑Real.pi) = (1 : ℂ) / ↑Real.pi := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [hpi]
  congr 1
  rw [show (starRingEnd ℂ)
    (∫ z : ℂ, G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2))) =
    ∫ z : ℂ, (starRingEnd ℂ)
      (G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))
    from (integral_conj (f := fun z =>
      G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))).symm]
  congr 1
  ext z
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ring

private lemma integrable_finiteHermiteSum_weightedCross
    (k : ℕ) {D n : ℕ} (a : Fin D → ℂ) :
    Integrable (fun z : ℂ =>
      finiteHermiteSum k a z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  unfold finiteHermiteSum
  have hEq :
      (fun z : ℂ =>
        (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D, a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    funext z
    calc
      (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)
        = ∑ m : Fin D,
            (a m * Phi k m.1 z) *
              ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [mul_assoc, ← Finset.sum_mul]
      _ = ∑ m : Fin D,
          a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ring
  rw [hEq]
  refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin D)) ?_
  intro m hm
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (integrable_weightedCross k m.1 n).const_mul (a m)

private lemma integrable_truncate_weightedCross
    (k J n : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ =>
      truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  simpa [truncate] using
    (integrable_finiteHermiteSum_weightedCross (k := k) (n := n)
      (a := fun m : Fin (J + 1) => hermiteCoeff k G m.1))

private theorem weightedInner_add_left_of_integrable
    (F G H : ℂ → ℂ)
    (hF : Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    (hG : Integrable
      (fun z : ℂ => G z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (F + G) H = weightedInner F H + weightedInner G H := by
  have hsum := congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t) (integral_add hF hG)
  simpa [weightedInner, HermiteLEAN.weightedInner, Pi.add_apply, add_mul, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using hsum

private theorem weightedInner_finset_sum_left
    {α : Type*}
    (s : Finset α)
    (f : α → ℂ → ℂ)
    (g : ℂ → ℂ)
    (hf : ∀ a ∈ s,
      Integrable
        (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (fun z => Finset.sum s (fun a => f a z)) g =
      Finset.sum s (fun a => weightedInner (f a) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedInner, HermiteLEAN.weightedInner]
  | @insert a s ha ih =>
      have hf' :
          ∀ b ∈ s,
            Integrable
              (fun z : ℂ => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)
      have hfa :
          Integrable
            (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        exact hf a (Finset.mem_insert_self a s)
      simp_rw [Finset.sum_insert ha]
      have hsumInt :
          Integrable
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        have hsumInt' :
            Integrable
              (fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
          exact MeasureTheory.integrable_finsetSum s (fun b hb => hf' b hb)
        have hEq :
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) =
              fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
          funext z
          rw [mul_assoc]
          rw [Finset.sum_mul]
          simp [mul_left_comm, mul_comm]
        exact hEq.symm ▸ hsumInt'
      change weightedInner ((fun z : ℂ => f a z) + fun z => Finset.sum s (fun b => f b z)) g =
        weightedInner (f a) g + Finset.sum s (fun a => weightedInner (f a) g)
      rw [weightedInner_add_left_of_integrable (F := fun z => f a z)
        (G := fun z => Finset.sum s (fun b => f b z)) (H := g) hfa hsumInt]
      rw [ih hf']

private lemma weightedInner_finiteHermiteSum_basis
    (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      ∑ m : Fin D, a m * weightedInner (Phi k m.1) (Phi k n) := by
  unfold weightedInner HermiteLEAN.weightedInner
  simp_rw [finiteHermiteSum, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · change
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              a m *
                (Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
        ∑ m : Fin D,
          a m *
            ((1 / Real.pi : ℂ) *
              ∫ z : ℂ,
                Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    calc
        (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              ∫ z : ℂ,
                a m *
                  (Phi k m.1 z *
                    ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
          =
            ∑ m : Fin D,
              (1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  a m *
                    (Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              simp [Finset.mul_sum]
        _ =
            ∑ m : Fin D,
              a m *
                ((1 / Real.pi : ℂ) *
                  ∫ z : ℂ,
                    Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hconst :
                  (∫ z : ℂ,
                    a m *
                      (Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      a m *
                        ∫ z : ℂ,
                          Phi k m.1 z *
                            ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                exact
                  MeasureTheory.integral_const_mul (a m)
                    (fun z : ℂ =>
                      Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
              rw [hconst]
              ring_nf
  · intro m hm
    simpa [mul_assoc] using (integrable_weightedCross k m.1 n).const_mul (a m)

private lemma weightedInner_finiteHermiteSum
    (k : ℕ) {D : ℕ} (a b : Fin D → ℂ) :
    weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
      ∑ m : Fin D, (starRingEnd ℂ) (b m) *
        weightedInner (finiteHermiteSum k a) (Phi k m.1) := by
  unfold weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ =>
        finiteHermiteSum k a z *
          (starRingEnd ℂ) (finiteHermiteSum k b z) *
            (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D,
          (starRingEnd ℂ) (b m) *
            (finiteHermiteSum k a z *
              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
    funext z
    rw [finiteHermiteSum, finiteHermiteSum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · calc
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              (starRingEnd ℂ) (b m) *
                (finiteHermiteSum k a z *
                  ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
          (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              (starRingEnd ℂ) (b m) *
                ∫ z : ℂ,
                  finiteHermiteSum k a z *
                    ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              congr 1
              refine Finset.sum_congr rfl (fun m _ => ?_)
              exact
                MeasureTheory.integral_const_mul ((starRingEnd ℂ) (b m))
                  (fun z : ℂ =>
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
      _ =
          ∑ m : Fin D,
            (starRingEnd ℂ) (b m) *
              ((1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  (fun z => finiteHermiteSum k a z) z *
                    (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun m _ => ?_)
              have hintegral :
                  ∫ z : ℂ,
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
                    =
                      ∫ z : ℂ,
                        (fun z => finiteHermiteSum k a z) z *
                          (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ) := by
                apply integral_congr_ae
                filter_upwards with z
                ring
              exact
                calc
                  (1 / Real.pi : ℂ) *
                      ((starRingEnd ℂ) (b m) *
                        ∫ z : ℂ,
                          finiteHermiteSum k a z *
                            ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            finiteHermiteSum k a z *
                              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                        ring
                  _ =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            (fun z => finiteHermiteSum k a z) z *
                              (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
                        rw [hintegral]
      _ = ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1) :=
          by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rfl
  · intro m hm
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_finiteHermiteSum_weightedCross (k := k) (a := a) (n := m.1)).const_mul
        ((starRingEnd ℂ) (b m))

/-- Inner products of finite Hermite sums are finite coefficient inner products. -/
theorem finiteHermiteSum_inner :
    ∀ {k D : ℕ} (a b : Fin D → ℂ),
      weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
        ∑ n : Fin D, a n * star (b n) := by
  intro k D a b
  rw [weightedInner_finiteHermiteSum]
  calc
    ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1)
      = ∑ m : Fin D, a m * star (b m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [weightedInner_finiteHermiteSum_basis]
          have horth :
              ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k m.1) = if x = m then 1 else 0 := by
            intro x
            rw [phi_orthonormal]
            by_cases hxm : x = m
            · subst hxm
              simp
            · have hxval : x.1 ≠ m.1 := by
                intro hEq
                exact hxm (Fin.ext hEq)
              simp [hxm, hxval]
          calc
            star (b m) * ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k m.1)
              = star (b m) * ∑ x : Fin D, a x * (if x = m then (1 : ℂ) else 0) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [horth x]
            _ = star (b m) * a m := by simp
            _ = a m * star (b m) := by ring
    _ = ∑ n : Fin D, a n * star (b n) := by rfl

/-- The weighted norm square of a finite Hermite sum is the coefficient `ℓ²` norm square. -/
theorem finiteHermiteSum_normSq :
    ∀ {k D : ℕ} (a : Fin D → ℂ),
      weightedNormSq (finiteHermiteSum k a) = ∑ n : Fin D, ‖a n‖ ^ 2 := by
  intro k D a
  rw [weightedNormSq_eq_re_weightedInner, finiteHermiteSum_inner]
  simp [Complex.normSq, Complex.sq_norm]

/-- Every basis vector belongs to the true level space. -/
theorem Phi_mem_Hk (k n : ℕ) : Phi k n ∈ Hk k := by
  refine ⟨integrable_weightedDiag k n, ?_⟩
  intro z
  have hterm : (fun m => weightedInner (Phi k n) (Phi k m) * Phi k m z) =
      fun m => if m = n then Phi k n z else 0 := by
    ext m
    rw [phi_orthonormal]
    by_cases h : n = m
    · subst h
      simp
    · simp [h, show m ≠ n from Ne.symm h]
  rw [hterm]
  exact hasSum_ite_eq n (Phi k n z)

/-- Weighted norms are homogeneous under scalar multiplication. -/
theorem weightedNorm_smul (c : ℂ) (G : ℂ → ℂ) :
    weightedNorm (c • G) = ‖c‖ * weightedNorm G := by
  have hInt :
      ∫ z : ℂ, ‖(c • G) z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ∫ z : ℂ, ‖c‖ ^ 2 * (‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    congr with z
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hsq : weightedNormSq (c • G) = ‖c‖ ^ 2 * weightedNormSq G := by
    change (1 / Real.pi) * ∫ z : ℂ, ‖(c • G) z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
      = ‖c‖ ^ 2 * ((1 / Real.pi) * ∫ z : ℂ, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))
    rw [hInt]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hcsq : √(‖c‖ ^ 2) = ‖c‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg c)]
  change √(weightedNormSq (c • G)) = ‖c‖ * √(weightedNormSq G)
  rw [hsq, Real.sqrt_mul (by positivity), hcsq]

/-- Weighted defect norms are homogeneous under scalar multiplication. -/
theorem weightedDefectNorm_smul (c : ℂ) (F0 G : ℂ → ℂ) :
    weightedDefectNorm (c • F0) (c • G) = ‖c‖ * weightedDefectNorm F0 G := by
  have hInt :
      ∫ z : ℂ, (modulusDefect (c • F0) (c • G) z) ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ∫ z : ℂ, ‖c‖ ^ 2 * ((modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    congr with z
    have hpt : modulusDefect (c • F0) (c • G) z = ‖c‖ * modulusDefect F0 G z := by
      change |‖(c • F0) z + (c • G) z‖ - ‖(c • F0) z‖| = ‖c‖ * |‖F0 z + G z‖ - ‖F0 z‖|
      have hsum : (c • F0) z + (c • G) z = c * (F0 z + G z) := by
        simp [Pi.smul_apply, mul_add]
      have hleft : ‖(c • F0) z + (c • G) z‖ = ‖c‖ * ‖F0 z + G z‖ := by
        rw [hsum, norm_mul]
      have hright : ‖(c • F0) z‖ = ‖c‖ * ‖F0 z‖ := by
        simp
      rw [hleft, hright]
      have hfact : ‖c‖ * ‖F0 z + G z‖ - ‖c‖ * ‖F0 z‖ =
          ‖c‖ * (‖F0 z + G z‖ - ‖F0 z‖) := by
        ring
      rw [hfact, abs_mul, abs_of_nonneg (norm_nonneg c)]
    rw [hpt]
    ring
  have hsq : weightedDefectNormSq (c • F0) (c • G) = ‖c‖ ^ 2 * weightedDefectNormSq F0 G := by
    change (1 / Real.pi) * ∫ z : ℂ, (modulusDefect (c • F0) (c • G) z) ^ 2 * Real.exp (-‖z‖ ^ 2)
      = ‖c‖ ^ 2 * ((1 / Real.pi) * ∫ z : ℂ, (modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2))
    rw [hInt]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hcsq : √(‖c‖ ^ 2) = ‖c‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg c)]
  change √(weightedDefectNormSq (c • F0) (c • G)) = ‖c‖ * √(weightedDefectNormSq F0 G)
  rw [hsq, Real.sqrt_mul (by positivity), hcsq]

/-- Helper: Hermite coefficients of a finite sum. -/
private lemma weightedInner_finiteHermiteSum_coeff (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      if h : n < D then a ⟨n, h⟩ else 0 := by
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    calc ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x.1 = n then 1 else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _; rw [phi_orthonormal]
      _ = ∑ x : Fin D, (if x = m then a m else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _
          by_cases hx : x = m
          · subst hx; simp [m]
          · have : x.1 ≠ n := fun hEq => hx (Fin.ext (by simpa [m] using hEq))
            simp [this, hx]
      _ = a m := by simp
    simp [m, h]
  · have : ∀ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x; rw [phi_orthonormal]
      simp [show x.1 ≠ n from fun hEq => h (hEq ▸ x.isLt)]
    simp [this, h]

/-- Every finite Hermite sum belongs to the true level space. -/
theorem finiteHermiteSum_mem_Hk :
    ∀ (k : ℕ) {D : ℕ} (a : Fin D → ℂ), finiteHermiteSum k a ∈ Hk k := by
  intro k D a
  refine ⟨?_, ?_⟩
  · change Integrable (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2))
    by_contra habs
    have hzero :
        (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) = 0 := by
      rw [MeasureTheory.integral_undef habs]
      ring
    have hpos : (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
        ∑ n : Fin D, ‖a n‖ ^ 2 := by
      change weightedNormSq (finiteHermiteSum k a) = _
      exact finiteHermiteSum_normSq (k := k) (a := a)
    rw [hpos] at hzero
    have hall_zero : ∀ n : Fin D, a n = 0 := by
      intro n
      have :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖a i‖)).mp hzero n
            (Finset.mem_univ n)
      exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖a n‖])
    have hzero_fun : (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2)) = 0 := by
      ext z
      simp [finiteHermiteSum, hall_zero]
    rw [hzero_fun] at habs
    exact habs (integrable_zero ℂ ℝ volume)
  · intro z
    simp_rw [weightedInner_finiteHermiteSum_coeff]
    let f : ℕ → ℂ := fun n => (if h : n < D then a ⟨n, h⟩ else 0) * Phi k n z
    change HasSum f (finiteHermiteSum k a z)
    have hfin : ∀ n, n ∉ Finset.range D → f n = 0 := by
      intro n hn
      simp only [f, Finset.mem_range, not_lt] at hn ⊢
      simp [show ¬(n < D) from not_lt.mpr hn]
    have hval : finiteHermiteSum k a z = ∑ n ∈ Finset.range D, f n := by
      simp only [finiteHermiteSum, f]
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl ?_
      intro ⟨n, hn⟩ _
      simp [show n < D from hn]
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hfin

/-- The canonical coefficient extractor recovers the coefficients of a finite Hermite sum. -/
theorem hermiteCoeff_finiteHermiteSum :
    ∀ {k D : ℕ} (a : Fin D → ℂ) (n : ℕ),
      hermiteCoeff k (finiteHermiteSum k a) n = if h : n < D then a ⟨n, h⟩ else 0 := by
  intro k D a n
  unfold hermiteCoeff
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    have horth :
        ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k n) = if x = m then 1 else 0 := by
      intro x
      rw [phi_orthonormal]
      by_cases hx : x = m
      · subst hx
        simp [m]
      · have hxval : x.1 ≠ n := by
          intro hEq
          exact hx (Fin.ext (by simpa [m] using hEq))
        simp [hx, hxval, m]
    calc
      ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x = m then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [horth x]
      _ = a m := by simp
      _ = if h' : n < D then a ⟨n, h'⟩ else 0 := by simp [m, h]
  · have horth0 : ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x
      rw [phi_orthonormal]
      have hxne : x.1 ≠ n := by
        intro hEq
        exact h (hEq ▸ x.isLt)
      simp [hxne]
    rw [show (if h' : n < D then a ⟨n, h'⟩ else 0) = 0 by simp [h]]
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [horth0 x]
    simp

/-- The zeroth coefficient is the inner product against the lowest basis vector. -/
@[simp] theorem hermiteCoeff_phi0 :
    ∀ {k : ℕ} {G : ℂ → ℂ}, hermiteCoeff k G 0 = weightedInner G (phi0 k) := by
  intro k G
  rfl

/-- Orthogonality to `Phi k 0` is equivalent to vanishing zeroth Hermite coefficient. -/
theorem orthogonal_phi0_iff_hermiteCoeff_zero :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      weightedInner G (phi0 k) = 0 ↔ hermiteCoeff k G 0 = 0 := by
  simp [hermiteCoeff_phi0]

/-- The truncation operator is the explicit finite Hermite sum of the first coefficients. -/
theorem truncate_eq_finiteHermiteSum :
    ∀ {k J : ℕ} {G : ℂ → ℂ},
      truncate k J G =
        finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by
  intro k J G
  rfl

/-- The truncated circle polynomial is the finite circle polynomial of the truncated vector. -/
theorem truncCirclePoly_eq_finiteCirclePoly :
    ∀ {k J : ℕ} {G : ℂ → ℂ} {r : ℝ},
      truncCirclePoly k r J G =
        finiteCirclePoly k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by
  intro k J G r
  rfl

/-- The truncation keeps exactly the first `J + 1` Hermite coefficients. -/
theorem hermiteCoeff_truncate :
    ∀ {k J : ℕ} {G : ℂ → ℂ} (n : ℕ),
      hermiteCoeff k (truncate k J G) n =
        if _h : n < J + 1 then hermiteCoeff k G n else 0 := by
  intro k J G n
  classical
  simp [truncate_eq_finiteHermiteSum, hermiteCoeff_finiteHermiteSum]

private lemma hermiteCoeff_sub_truncate
    (k J : ℕ) (G : ℂ → ℂ) (n : ℕ) :
    hermiteCoeff k (fun z : ℂ => G z - truncate k J G z) n =
      if _h : n < J + 1 then 0 else hermiteCoeff k G n := by
  unfold hermiteCoeff
  let fG : ℂ → ℂ := fun z : ℂ =>
    G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fT : ℂ → ℂ := fun z : ℂ =>
    truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fR : ℂ → ℂ := fun z : ℂ =>
    (G z - truncate k J G z) * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  have hT : Integrable fT := by
    unfold fT
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_truncate_weightedCross k J n G)
  by_cases hG : Integrable fG
  · have hEq :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      unfold weightedInner HermiteLEAN.weightedInner
      calc
        (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z
          = (1 / Real.pi : ℂ) * ∫ z : ℂ, (fG z - fT z) := by
              congr with z
              unfold fR fG fT
              ring
        _ = (1 / Real.pi : ℂ) * ((∫ z : ℂ, fG z) - ∫ z : ℂ, fT z) := by
              simpa [fR, fG, fT] using
                congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t)
                  (MeasureTheory.integral_sub hG hT)
        _ = weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
              unfold weightedInner HermiteLEAN.weightedInner
              ring
    rw [hEq]
    have htruncate :
        weightedInner (truncate k J G) (Phi k n) =
          if h : n < J + 1 then hermiteCoeff k G n else 0 := by
      simpa [hermiteCoeff] using (hermiteCoeff_truncate (k := k) (J := J) (G := G) n)
    have hGcoeff : weightedInner G (Phi k n) = hermiteCoeff k G n := rfl
    by_cases hn : n < J + 1
    · simp [hn, htruncate, hGcoeff]
    · simp [hn, htruncate, hGcoeff]
  · have hGnot : ¬ Integrable fG := hG
    have hR : ¬ Integrable fR := by
      intro hR
      apply hGnot
      have hEq : fG = fun z : ℂ => fR z + fT z := by
        funext z
        unfold fR fG fT
        ring
      rw [hEq]
      exact hR.add hT
    have hzeroG : weightedInner G (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fG z = 0
      rw [MeasureTheory.integral_undef hGnot]
      ring
    have hzeroR :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z = 0
      rw [MeasureTheory.integral_undef hR]
      ring
    by_cases hn : n < J + 1
    · simp [hn, hzeroR]
    · simp [hn, hzeroR, hzeroG]

/-- Every truncation lies in the true level space. -/
theorem truncate_mem_Hk :
    ∀ (k J : ℕ) (G : ℂ → ℂ), truncate k J G ∈ Hk k := by
  intro k J G
  simpa [truncate] using
    (finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))

/-- Exact finite Parseval identity for Hermite truncations. -/
theorem truncate_normSq :
    ∀ (k J : ℕ) (G : ℂ → ℂ),
      weightedNormSq (truncate k J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 := by
  intro k J G
  simpa [truncate_eq_finiteHermiteSum] using
    (finiteHermiteSum_normSq (k := k) (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))

/-- Finite Hermite sums admit a finite circle representation. -/
theorem finiteHermiteSum_circle :
    ∀ {k D : ℕ} (a : Fin D → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          finiteHermiteSum k a (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                finiteCirclePoly k r a t := by
  intro k D a r hr t
  have hpoly :
      ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) = finiteCirclePoly k r a t := by
    by_cases hD : D = 0
    · subst hD
      have hband0 : frequencyBand 0 0 = Finset.range 1 := by
        simp [HermiteLEAN.frequencyBand]
      have hzero : finiteCirclePoly k r a t = 0 := by
        rw [finiteCirclePoly, positiveTrigonometricPolynomial, hband0]
        change Finset.sum (Finset.range 1) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ)
            t) = 0
        rw [Finset.sum_range_one]
        simp [finiteCircleCoeff]
      simp [hzero]
    · have hDpos : 1 ≤ D := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hD)
      have hsum :
          ∑ n ∈ frequencyBand 0 D,
              finiteCircleCoeff k r a n * fourier (n : ℤ) t =
            ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) := by
        simpa [HermiteLEAN.frequencyBand, finiteCircleCoeff, mul_assoc, mul_left_comm, mul_comm]
            using
          (sum_Icc_eq_sum_Fin 0 D hDpos
            (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t))
      simp only [finiteCirclePoly, positiveTrigonometricPolynomial]
      exact hsum.symm
  calc
    finiteHermiteSum k a (circlePoint r t)
        = ∑ n : Fin D, circleLeadingFactor k r *
            (fourier (-(k : ℤ)) t : ℂ) * (a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t)) := by
            rw [finiteHermiteSum]
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [phi_polar (k := k) (n := n.1) (r := r) hr t]
            ring
    _ = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
        ∑ n : Fin D, a n * ((qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t) := by
        rw [← Finset.mul_sum]
    _ = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * finiteCirclePoly k r a t := by
        rw [hpoly]

/-- The finite circle coefficient map vanishes outside the finite frequency range. -/
theorem finiteCircleCoeff_eq_zero_outside :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ) {n : ℕ},
      D ≤ n →
        finiteCircleCoeff k r a n = 0 := by
  intro k D r a n hn
  simp [finiteCircleCoeff, Nat.not_lt.mpr hn]

/-- The finite circle polynomial is supported in frequencies `{0, ..., D - 1}`. -/
theorem finiteCirclePoly_support :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      finiteCirclePoly k r a =
        positiveTrigonometricPolynomial (frequencyBand 0 D) (finiteCircleCoeff k r a) := by
  intro k D r a
  rfl

/-- If the zeroth coefficient vanishes, the finite circle polynomial has
positive-frequency support. -/
theorem finiteCirclePoly_support_pos :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin (D + 1) → ℂ),
      a 0 = 0 →
        finiteCirclePoly k r a =
          positiveTrigonometricPolynomial (frequencyBand 1 D) (finiteCircleCoeff k r a) := by
  intro k D r a h0
  ext t
  have hband : frequencyBand 0 (D + 1) = insert 0 (frequencyBand 1 D) := by
    simpa [HermiteLEAN.frequencyBand, Nat.succ_eq_add_one, Nat.succ_sub_one] using
      (Finset.insert_Icc_add_one_left_eq_Icc (a := (0 : ℕ)) (b := D) (by omega)).symm
  change
    Finset.sum (frequencyBand 0 (D + 1)) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t) =
      Finset.sum (frequencyBand 1 D) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t)
  rw [hband, Finset.sum_insert]
  · simp [finiteCircleCoeff, h0]
  · simp [HermiteLEAN.frequencyBand]

/-- Circle Parseval identity for finite Hermite sums. -/
theorem finiteCirclePoly_l2_identity :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      circleL2Sq (finiteCirclePoly k r a) =
        ∑ n : Fin D, ‖a n‖ ^ 2 * |qkn k n.1 r| ^ 2 := by
  intro k D r a
  by_cases hD : D = 0
  · subst hD
    simp [finiteCirclePoly, HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.frequencyBand,
      HermiteLEAN.circleL2Sq, finiteCircleCoeff]
  · have hDpos : 1 ≤ D := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hD)
    have hpoly :
        finiteCirclePoly k r a =
          fun t : Circle => ∑ n : Fin D, a n * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
      ext t
      change
        Finset.sum (Finset.Icc 0 (0 + D - 1))
            (fun n => (if h : n < D then a ⟨n, h⟩ * (qkn k n r : ℂ) else 0) * fourier (n : ℤ) t) =
          ∑ n : Fin D, a n * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t
      rw [sum_Icc_eq_sum_Fin 0 D hDpos]
      simp
    rw [hpoly, circleL2Sq_finFourierPoly]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring

/-- Truncations admit the corresponding finite circle representation. -/
theorem truncate_circle :
    ∀ (k J : ℕ) (G : ℂ → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          truncate k J G (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                truncCirclePoly k r J G t := by
  intro k J G r hr t
  simpa [truncate, truncCirclePoly_eq_finiteCirclePoly] using
    (finiteHermiteSum_circle (k := k) (D := J + 1)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1) (r := r) hr t)

/-- The truncation circle polynomial is supported in `{0, ..., J}`. -/
theorem truncCirclePoly_support :
    ∀ {k J : ℕ} (r : ℝ) (G : ℂ → ℂ),
      truncCirclePoly k r J G =
        positiveTrigonometricPolynomial
          (frequencyBand 0 (J + 1))
          (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by
  intro k J r G
  rfl

/-- Orthogonality to `Phi k 0` removes the zero frequency from every
truncation circle polynomial. -/
theorem truncCirclePoly_support_pos :
    ∀ {k J : ℕ} (r : ℝ) (G : ℂ → ℂ),
      weightedInner G (phi0 k) = 0 →
        truncCirclePoly k r J G =
          positiveTrigonometricPolynomial
            (frequencyBand 1 J)
            (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by
  intro k J r G h
  have h0 : hermiteCoeff k G 0 = 0 := by
    simpa [hermiteCoeff_phi0] using h
  simpa [truncCirclePoly, h0] using
    (finiteCirclePoly_support_pos (k := k) (D := J) (r := r)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1) h0)

/-- Circle Parseval identity for truncated Hermite sums. -/
theorem truncCirclePoly_l2_identity :
    ∀ (k J : ℕ) (r : ℝ) (G : ℂ → ℂ),
      circleL2Sq (truncCirclePoly k r J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 * |qkn k n.1 r| ^ 2 := by
  intro k J r G
  simpa [truncCirclePoly_eq_finiteCirclePoly] using
    (finiteCirclePoly_l2_identity (k := k) (D := J + 1) (r := r)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))

/-- Summability of polynomial-exponential factorial tails. -/
private lemma summable_nat_pow_mul_pow_div_factorial_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc : ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by
        exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
          gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : (n.factorial * (n + m).descFactorial m) = (n + m).factorial := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ)
          = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 := by
        exact Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m)
          = ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) / (Nat.factorial (n + m) : ℝ) := by
              simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) := by
              have hpowx :
                  ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := by
                exact mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
              have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
              rw [div_le_iff₀ hfacpos]
              calc
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := hpowx
                _ =
                    ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                        x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                      (Nat.factorial (n + m) : ℝ) := by
                        have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                        field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)

/-- Descending factorial ratios are controlled by a fixed successor power. -/
private lemma factorial_ratio_le_pow_succ {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv : (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat

/-- Partial binomial sums are bounded by the full `2^k` binomial sum. -/
private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤ (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
      ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx ⊢
            omega
          · intro j _ _
            positivity
    _ = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k

/-- Uniform disk majorant for the explicit basis vector `Phi k n`. -/
private lemma phi_norm_le_majorant {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Phi k n z‖ ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  rw [phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) := norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n := by
      calc
        ‖z‖ ^ (n - j) ≤ R ^ (n - j) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ n := by
          exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k := by
      calc
        ‖z‖ ^ (k - j) ≤ R ^ (k - j) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ k := by
          exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    calc
      ‖term j‖
        = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
            ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_pow]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by
            gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ring
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤ Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
    exact Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by
    rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ := norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) * Finset.sum S term‖
      ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => ‖term j‖) := by
            exact le_trans (norm_mul_le _ _) <|
              mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
            exact mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
            rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by
            rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          (((2 : ℝ) ^ k) * common) := by
            gcongr
            simpa [S] using choose_partial_sum_le_pow_two k n
    _ = ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
            dsimp [common]
            rw [div_eq_mul_inv]
            ring

/-! ## Basis Bridge -/

/-- The formal Hermite expansion attached to a coefficient sequence. -/
def hermiteSeries (k : ℕ) (g : ℕ → ℂ) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, g n * Phi k n z

/-- The circle series associated to Hermite coefficients at radius `r`. -/
def circleSeries (k : ℕ) (g : ℕ → ℂ) (r : ℝ) : Circle → ℂ :=
  fun t => ∑' n : ℕ, g n * (qkn k n r : ℂ) * fourier (n : ℤ) t

/-- The canonical coefficient extractor recovers the Hermite expansion of any `G ∈ H_k`. -/
theorem hermiteCoeff_expansion :
    ∀ {k : ℕ} {G : ℂ → ℂ}, G ∈ Hk k → G = hermiteSeries k (hermiteCoeff k G) := by
  intro k G hG
  ext z
  exact ((hG.2 z).tsum_eq).symm

/-- The truncation is the unique degree-`≤ J` element with the prescribed first coefficients. -/
theorem truncate_unique :
    ∀ {k J : ℕ} {G H : ℂ → ℂ},
      H ∈ Hk k →
        (∀ n : ℕ,
          hermiteCoeff k H n = if _h : n < J + 1 then hermiteCoeff k G n else 0) →
            H = truncate k J G := by
  intro k J G H hH hcoeffs
  have hexp := hermiteCoeff_expansion hH
  rw [hexp]
  ext z
  simp only [hermiteSeries, truncate, finiteHermiteSum]
  rw [show (∑' n : ℕ, hermiteCoeff k H n * Phi k n z) =
    ∑ n ∈ Finset.range (J + 1), hermiteCoeff k H n * Phi k n z from by
      apply tsum_eq_sum
      intro n hn
      rw [Finset.mem_range] at hn
      rw [hcoeffs n, dif_neg hn, zero_mul]]
  rw [Finset.sum_range]
  congr 1
  ext ⟨n, hn⟩
  simp only []
  rw [hcoeffs n, dif_pos hn]

/-- Truncation converges pointwise to G -/
private lemma truncate_tendsto_pointwise {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (z : ℂ) :
    Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) := by
  have hH := hG.2 z
  -- hH : HasSum (fun n => hermiteCoeff k G n * Phi k n z) (G z)
  -- HasSum means Tendsto of partial sums over Finsets
  -- We need the sequential version through range(J+1)
  have hseq : Filter.Tendsto
      (fun J => ∑ n ∈ Finset.range J, hermiteCoeff k G n * Phi k n z)
      Filter.atTop (nhds (G z)) :=
    hH.tendsto_sum_nat
  -- truncate k J G z = ∑ n : Fin (J+1), hermiteCoeff k G n.1 * Phi k n.1 z
  -- = ∑ n ∈ range(J+1), hermiteCoeff k G n * Phi k n z
  change Filter.Tendsto (fun J =>
    ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) Filter.atTop (nhds (G z))
  have hrw : (fun J => ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) =
      (fun J => ∑ n ∈ Finset.range (J + 1), hermiteCoeff k G n * Phi k n z) := by
    ext J; rw [Finset.sum_range]
  rw [hrw]
  exact hseq.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))

/-- Integrability of truncation norm squared with Gaussian weight. -/
theorem integrable_truncate_normSq_exp (k J : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
  simpa using (truncate_mem_Hk k J G).1

/-- Cross integrability: Phi_n * conj(G) * exp is integrable when ‖G‖² exp is.
    Uses AM-GM: |ab| ≤ (a² + b²)/2 with the Gaussian split. -/
private lemma integrable_Phi_conj_G_exp {k : ℕ} {G : ℂ → ℂ} (n : ℕ)
    (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ =>
      Phi k n z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  -- Bound: ‖Phi_n * conj G * exp‖ ≤ (‖Phi_n‖² + ‖G‖²) * exp
  -- Both ‖Phi_n‖² exp and ‖G‖² exp are integrable.
  have hDiag := integrable_weightedDiag k n
  have hBound : Integrable (fun z : ℂ =>
      (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) := by
    have : (fun z : ℂ => (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) =
        (fun z => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      ext z; ring
    rw [this]; exact hDiag.add hInt
  apply MeasureTheory.Integrable.mono' hBound
  · -- G is AEStronglyMeasurable: truncate_J G → G pointwise, each truncation
    -- is continuous (hence AEStronglyMeasurable).
    have hG_aesm : AEStronglyMeasurable G volume := by
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
      · intro J; unfold truncate finiteHermiteSum
        exact (continuous_finsetSum _ (fun m _ =>
          continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
    exact (((continuous_Phi k n).aestronglyMeasurable.mul
      (hG_aesm.star)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_neg.comp ((continuous_pow 2).comp
          continuous_norm)))).aestronglyMeasurable)
  · filter_upwards with z
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (exp_nonneg _)]
    nlinarith [sq_nonneg (‖Phi k n z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ),
      sq_abs ‖Phi k n z‖, sq_abs ‖G z‖]

private lemma bessel_truncate_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) (J : ℕ) :
    weightedNormSq (truncate k J G) ≤ weightedNormSq G := by
  -- Step 1: ⟨trunc, G⟩ expanded via finite sum in first argument
  set a := fun n : Fin (J + 1) => hermiteCoeff k G n.1
  -- Each cross integral is integrable:
  have hCross : ∀ m : Fin (J + 1),
      Integrable (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro m
    have h1 := integrable_Phi_conj_G_exp (k := k) m.1 hG hInt
    have heq : (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (fun z : ℂ => a m * (Phi k m.1 z * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ))) := by ext z; ring
    rw [heq]; exact h1.const_mul _
  -- ⟨truncate_J G, G⟩ via finite sum expansion
  have hInnerTG : weightedInner (truncate k J G) G =
      ∑ n : Fin (J + 1), a n * (starRingEnd ℂ) (hermiteCoeff k G n.1) := by
    change weightedInner (finiteHermiteSum k a) G = _
    unfold finiteHermiteSum
    rw [weightedInner_finset_sum_left Finset.univ (fun m => fun z => a m * Phi k m.1 z) G
        (fun m _ => hCross m)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    -- ⟨c * Phi_n, G⟩ = c * conj(⟨G, Phi_n⟩)
    have h1 : weightedInner (fun z => a n * Phi k n.1 z) G =
        a n * weightedInner (Phi k n.1) G := by
      unfold weightedInner HermiteLEAN.weightedInner
      conv_lhs => rw [show (fun z : ℂ => a n * Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2))) =
        (fun z => a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) from by ext z; ring]
      rw [show (∫ z : ℂ, a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) = a n * (∫ z : ℂ, (Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2)))) from
        MeasureTheory.integral_const_mul _ _]
      ring
    rw [h1]
    have h2 : weightedInner (Phi k n.1) G =
        (starRingEnd ℂ) (weightedInner G (Phi k n.1)) :=
      weightedInner_conj_symm (Phi k n.1) G
    rw [h2]; rfl
  -- Simplify: a n * conj(a n) = ‖a n‖² (as complex)
  have hInnerTG' : weightedInner (truncate k J G) G =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    rw [hInnerTG]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [a]
    rw [show hermiteCoeff k G ↑n * (starRingEnd ℂ) (hermiteCoeff k G ↑n) =
        ((‖hermiteCoeff k G ↑n‖ ^ 2 : ℝ) : ℂ) from by
      simpa using Complex.mul_conj' (hermiteCoeff k G ↑n)]; push_cast; ring
  -- Also: ⟨truncate, truncate⟩ = ∑ ‖a_n‖²
  have hInnerTT : weightedInner (truncate k J G) (truncate k J G) =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    change weightedInner (finiteHermiteSum k a) (finiteHermiteSum k a) = _
    rw [finiteHermiteSum_inner]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show a n * star (a n) = ((‖a n‖ ^ 2 : ℝ) : ℂ) from by
      simpa using Complex.mul_conj' (a n)]; push_cast; ring
  -- From the equalities: ⟨trunc, G⟩ = ⟨trunc, trunc⟩ (= ∑ ‖a_n‖²)
  have hCrossZero : weightedInner (truncate k J G) G =
      weightedInner (truncate k J G) (truncate k J G) := by
    rw [hInnerTG', hInnerTT]
  -- weightedNormSq T = Re⟨T, T⟩ = Re⟨T, G⟩
  rw [weightedNormSq_eq_re_weightedInner, ← hCrossZero]
  let Tfun : ℂ → ℂ := truncate k J G
  have hTInt : Integrable (fun z : ℂ => ‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    simpa [Tfun] using integrable_truncate_normSq_exp k J G
  have hAvgInt : Integrable (fun z : ℂ =>
      ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) := by
    have hsum : Integrable (fun z : ℂ =>
        ‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := hTInt.add hInt
    have hEq :
        (fun z : ℂ => ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) =
          (fun z : ℂ =>
            (1 / 2 : ℝ) *
              (‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      funext z
      ring
    rw [hEq]
    exact hsum.const_mul (1 / 2 : ℝ)
  have hInnerNormLe :
      ‖weightedInner Tfun G‖ ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := by
    have hpt :
        ∀ᵐ z : ℂ ∂volume,
          ‖Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ ≤
            ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
      refine Filter.Eventually.of_forall ?_
      intro z
      calc
        ‖Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖
            = (‖Tfun z‖ * ‖G z‖) * rexp (-‖z‖ ^ 2) := by
                rw [norm_mul, norm_mul]
                rw [show ‖(starRingEnd ℂ) (G z)‖ = ‖G z‖ by simp]
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
        _ ≤ ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
              nlinarith [sq_nonneg (‖Tfun z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ)]
    have hIntLe :
        ‖∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ ≤
          ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) :=
      MeasureTheory.norm_integral_le_of_norm_le hAvgInt hpt
    have hpi_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
    have hAvgEq :
        (1 / Real.pi) * ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) =
          (weightedNormSq Tfun + weightedNormSq G) / 2 := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      have hEq :
          (fun z : ℂ => ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) =
            (fun z : ℂ =>
              (1 / 2 : ℝ) *
                (‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
        funext z
        ring
      rw [hEq, MeasureTheory.integral_const_mul, MeasureTheory.integral_add hTInt hInt]
      ring
    have hpi_norm : ‖(1 / Real.pi : ℂ)‖ = (1 / Real.pi : ℝ) := by
      simp [one_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ Real.pi by
        positivity)]
    calc
      ‖weightedInner Tfun G‖
          = ‖(1 / Real.pi : ℂ) *
              ∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ := by
                rfl
      _ = (1 / Real.pi : ℝ) *
          ‖∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ := by
            rw [norm_mul, hpi_norm]
      _ ≤ (1 / Real.pi : ℝ) *
          ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hIntLe hpi_nonneg
      _ = (weightedNormSq Tfun + weightedNormSq G) / 2 := hAvgEq
  have hReEq : (weightedInner Tfun G).re = weightedNormSq Tfun := by
    calc
      (weightedInner Tfun G).re = (weightedInner Tfun Tfun).re := by
        simpa [Tfun] using congrArg Complex.re hCrossZero
      _ = weightedNormSq Tfun := (weightedNormSq_eq_re_weightedInner Tfun).symm
  have hTle : weightedNormSq Tfun ≤ weightedNormSq G := by
    have hmid : weightedNormSq Tfun ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := by
      calc
        weightedNormSq Tfun = (weightedInner Tfun G).re := hReEq.symm
        _ ≤ ‖weightedInner Tfun G‖ := Complex.re_le_norm _
        _ ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := hInnerNormLe
    linarith
  simpa [Tfun, hReEq] using hTle

/-- The non-integrable branch of `hermiteCoeff_parseval`: when `‖G‖²·exp` is not
integrable, both the weighted norm and the Hermite coefficient sum vanish.
Extracted to respect the proof size limit. -/
private lemma hermiteCoeff_parseval_not_integrable {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : ¬ Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    weightedNormSq G = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  have hLHS : weightedNormSq G = 0 := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    rw [MeasureTheory.integral_undef hInt]; ring
  rw [hLHS]
  have hnotSummable : ¬ Summable (fun n : ℕ => ‖hermiteCoeff k G n‖ ^ 2) := by
    intro hsum
    let t : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2
    have htrunc_tendsto :
        Filter.Tendsto (fun J => weightedNormSq (truncate k J G))
          Filter.atTop (nhds (∑' n : ℕ, t n)) := by
      have hnat :
          Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, t n)
            Filter.atTop (nhds (∑' n : ℕ, t n)) :=
        (hsum.hasSum_iff_tendsto_nat).1 hsum.hasSum
      have hshift :
          Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), t n)
            Filter.atTop (nhds (∑' n : ℕ, t n)) := by
        exact hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
      have hEqFun :
          (fun J => weightedNormSq (truncate k J G)) =
            (fun J => ∑ n ∈ Finset.range (J + 1), t n) := by
        funext J
        change weightedNormSq (truncate k J G) =
          ∑ n ∈ Finset.range (J + 1), ‖hermiteCoeff k G n‖ ^ 2
        rw [show ∑ n ∈ Finset.range (J + 1), ‖hermiteCoeff k G n‖ ^ 2 =
            ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by
          rw [Finset.sum_range]]
        exact truncate_normSq k J G
      rw [hEqFun]
      exact hshift
    have hpi_trunc_tendsto :
        Filter.Tendsto (fun J => Real.pi * weightedNormSq (truncate k J G))
          Filter.atTop (nhds (Real.pi * ∑' n : ℕ, t n)) :=
      Filter.Tendsto.const_mul Real.pi htrunc_tendsto
    have hLiminfENNR :
        Filter.liminf
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
            Filter.atTop =
          ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
      have hto :
          Filter.Tendsto
              (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
              Filter.atTop
              (nhds (ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp hpi_trunc_tendsto
      exact hto.liminf_eq
    have hLiminfPt :
        ∀ z : ℂ,
          Filter.liminf
              (fun J =>
                ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop =
            ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      intro z
      have htruncz : Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) :=
        truncate_tendsto_pointwise hG z
      have hreal :
          Filter.Tendsto (fun J => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
            Filter.atTop (nhds (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
        have hsq :
            Filter.Tendsto (fun J => ‖truncate k J G z‖ ^ 2)
              Filter.atTop (nhds (‖G z‖ ^ 2)) := by
          exact (htruncz.norm.pow 2)
        exact hsq.mul_const (rexp (-‖z‖ ^ 2))
      have hto :
          Filter.Tendsto
              (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop
              (nhds (ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) ) :=
        (ENNReal.continuous_ofReal.tendsto _).comp hreal
      exact hto.liminf_eq
    have hFatou :
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
          Filter.liminf
              (fun J =>
                ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop := by
      have hmeas :
          ∀ J : ℕ,
            AEMeasurable
              (fun z : ℂ =>
                ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ) volume := by
        intro J
        exact (integrable_truncate_normSq_exp k J
            G).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      have hfatou_raw := MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hmeas
      have hcongr :
          (∫⁻ z : ℂ,
              Filter.liminf
                (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                Filter.atTop) =
            ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        apply MeasureTheory.lintegral_congr_ae
        exact Filter.Eventually.of_forall hLiminfPt
      calc
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
            = ∫⁻ z : ℂ,
                Filter.liminf
                  (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                  Filter.atTop := hcongr.symm
        _ ≤ Filter.liminf
              (fun J =>
                ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop := hfatou_raw
    have hLinEqTrunc :
        ∀ J : ℕ,
          ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
            ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)) := by
      intro J
      have hIntJ : Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        exact integrable_truncate_normSq_exp k J G
      have hNonnegJ :
          ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
        exact Filter.Eventually.of_forall (fun z => by positivity)
      have hIntEq :
          ∫ z : ℂ, ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
            Real.pi * weightedNormSq (truncate k J G) := by
        unfold weightedNormSq HermiteLEAN.weightedNormSq
        field_simp [Real.pi_ne_zero]
      calc
        ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
            = ENNReal.ofReal (∫ z : ℂ, ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntJ hNonnegJ
        _ = ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)) := by rw [hIntEq]
    have hBound :
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
          ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
      calc
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
            ≤ Filter.liminf
                (fun J =>
                  ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                Filter.atTop := hFatou
        _ = Filter.liminf
              (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
              Filter.atTop := by
              congr 1
              funext J
              exact hLinEqTrunc J
        _ = ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := hLiminfENNR
    have hlin_lt_top :
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) < ⊤ := by
      exact lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
    have hG_aesm : AEStronglyMeasurable G volume := by
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
      · intro J
        unfold truncate finiteHermiteSum
        exact (continuous_finsetSum _ (fun m _ =>
          continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
    have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
      (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
    have hf_aesm :
        AEStronglyMeasurable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
      (hG_aesm.norm.pow 2).mul hExp_aesm
    have hnonneg :
        ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) :=
      Filter.Eventually.of_forall (fun z => by positivity)
    have hfi : MeasureTheory.HasFiniteIntegral (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume
        :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hlin_lt_top
    have hInt' : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := ⟨hf_aesm, hfi⟩
    exact hInt hInt'
  rw [tsum_eq_zero_of_not_summable hnotSummable]

/-- The Fatou (`≤`) direction of `hermiteCoeff_parseval` in the integrable case:
the weighted norm is bounded by the Hermite coefficient sum.  Extracted to
respect the proof size limit. -/
private lemma hermiteCoeff_parseval_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    weightedNormSq G ≤ ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  let t : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2
  have hsumRange : ∀ J, ∑ n ∈ Finset.range J, t n ≤ weightedNormSq G := by
    intro J
    by_cases hJ : J = 0
    · subst hJ
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      positivity
    · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      rw [show ∑ n ∈ Finset.range (J' + 1), t n =
          ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by
        rw [Finset.sum_range]]
      rw [← truncate_normSq k J' G]
      exact bessel_truncate_le hG hInt J'
  have hsum : Summable t := summable_of_sum_range_le (fun n => sq_nonneg ‖hermiteCoeff k G n‖)
    hsumRange
  have htrunc_tendsto :
      Filter.Tendsto (fun J => weightedNormSq (truncate k J G))
        Filter.atTop (nhds (∑' n : ℕ, t n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) :=
      (hsum.hasSum_iff_tendsto_nat).1 hsum.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) := by
      exact hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    have hEqFun :
        (fun J => weightedNormSq (truncate k J G)) =
          (fun J => ∑ n ∈ Finset.range (J + 1), t n) := by
      funext J
      change weightedNormSq (truncate k J G) =
        ∑ n ∈ Finset.range (J + 1), ‖hermiteCoeff k G n‖ ^ 2
      rw [show ∑ n ∈ Finset.range (J + 1), ‖hermiteCoeff k G n‖ ^ 2 =
          ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by
        rw [Finset.sum_range]]
      exact truncate_normSq k J G
    rw [hEqFun]
    exact hshift
  have hpi_trunc_tendsto :
      Filter.Tendsto (fun J => Real.pi * weightedNormSq (truncate k J G))
        Filter.atTop (nhds (Real.pi * ∑' n : ℕ, t n)) :=
    Filter.Tendsto.const_mul Real.pi htrunc_tendsto
  have hLiminfENNR :
      Filter.liminf
          (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
          Filter.atTop =
        ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
    have hto :
        Filter.Tendsto
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
            Filter.atTop
            (nhds (ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpi_trunc_tendsto
    exact hto.liminf_eq
  have hNonnegG : ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
    exact Filter.Eventually.of_forall (fun z => by positivity)
  have hLiminfPt :
      ∀ z : ℂ,
        Filter.liminf
            (fun J =>
              ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop =
          ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    intro z
    have htruncz : Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) :=
      truncate_tendsto_pointwise hG z
    have hreal :
        Filter.Tendsto (fun J => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          Filter.atTop (nhds (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      have hsq :
          Filter.Tendsto (fun J => ‖truncate k J G z‖ ^ 2)
            Filter.atTop (nhds (‖G z‖ ^ 2)) := by
        exact (htruncz.norm.pow 2)
      exact hsq.mul_const (rexp (-‖z‖ ^ 2))
    have hto :
        Filter.Tendsto
            (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop
            (nhds (ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) ) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hreal
    exact hto.liminf_eq
  have hFatou :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        Filter.liminf
            (fun J =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := by
    have hmeas :
        ∀ J : ℕ,
          AEMeasurable
            (fun z : ℂ =>
              ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ) volume := by
      intro J
      exact (integrable_truncate_normSq_exp k J
          G).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hfatou_raw := MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hmeas
    have hcongr :
        (∫⁻ z : ℂ,
            Filter.liminf
              (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop) =
          ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      apply MeasureTheory.lintegral_congr_ae
      exact Filter.Eventually.of_forall hLiminfPt
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ∫⁻ z : ℂ,
              Filter.liminf
                (fun J => ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                Filter.atTop := hcongr.symm
      _ ≤ Filter.liminf
            (fun J =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := hfatou_raw
  have hLinEqG :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
        ENNReal.ofReal (Real.pi * weightedNormSq G) := by
    have hIntEq : ∫ z : ℂ, ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) = Real.pi * weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      field_simp [Real.pi_ne_zero]
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ENNReal.ofReal (∫ z : ℂ, ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonnegG
      _ = ENNReal.ofReal (Real.pi * weightedNormSq G) := by rw [hIntEq]
  have hLinEqTrunc :
      ∀ J : ℕ,
        ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
          ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)) := by
    intro J
    have hIntJ : Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      exact integrable_truncate_normSq_exp k J G
    have hNonnegJ :
        ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
      exact Filter.Eventually.of_forall (fun z => by positivity)
    have hIntEq :
        ∫ z : ℂ, ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
          Real.pi * weightedNormSq (truncate k J G) := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      field_simp [Real.pi_ne_zero]
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ENNReal.ofReal (∫ z : ℂ, ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntJ hNonnegJ
      _ = ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)) := by rw [hIntEq]
  have hFatou' :
      ENNReal.ofReal (Real.pi * weightedNormSq G) ≤
        Filter.liminf
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
            Filter.atTop := by
    calc
      ENNReal.ofReal (Real.pi * weightedNormSq G)
          = ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := hLinEqG.symm
      _ ≤ Filter.liminf
            (fun J =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := hFatou
      _ = Filter.liminf
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
            Filter.atTop := by
            congr 1
            funext J
            exact hLinEqTrunc J
  have hpi_nonneg : 0 ≤ Real.pi * weightedNormSq G := by
    have hnorm_nonneg : 0 ≤ weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      have hpiinv_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
      have hint_nonneg : 0 ≤ ∫ z : ℂ, ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
        exact MeasureTheory.integral_nonneg (fun z => by positivity)
      exact mul_nonneg hpiinv_nonneg hint_nonneg
    exact mul_nonneg (le_of_lt Real.pi_pos) hnorm_nonneg
  have htsum_nonneg : 0 ≤ ∑' n : ℕ, t n := tsum_nonneg (fun n => sq_nonneg ‖hermiteCoeff k G n‖)
  have hpi_tsum_nonneg : 0 ≤ Real.pi * ∑' n : ℕ, t n :=
    mul_nonneg (le_of_lt Real.pi_pos) htsum_nonneg
  have hpi_mul_le :
      Real.pi * weightedNormSq G ≤ Real.pi * ∑' n : ℕ, t n := by
    have hfatou_toReal :
        (ENNReal.ofReal (Real.pi * weightedNormSq G)).toReal ≤
          (ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n)).toReal := by
      have hfatou_eq :
          ENNReal.ofReal (Real.pi * weightedNormSq G) ≤
            ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
        calc
          ENNReal.ofReal (Real.pi * weightedNormSq G)
              ≤ Filter.liminf
                  (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (truncate k J G)))
                  Filter.atTop := hFatou'
          _ = ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := hLiminfENNR
      exact (ENNReal.toReal_le_toReal (by simp) (by simp)).2 hfatou_eq
    simpa [ENNReal.toReal_ofReal hpi_nonneg, ENNReal.toReal_ofReal hpi_tsum_nonneg]
      using hfatou_toReal
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hfinal : weightedNormSq G ≤ ∑' n : ℕ, t n := by
    nlinarith [hpi_pos, hpi_mul_le]
  simpa [t] using hfinal

/-- Parseval identity for the canonical Hermite coefficients. -/
theorem hermiteCoeff_parseval :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        weightedNormSq G = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  intro k G hG
  -- Split by integrability of ‖G‖² exp.
  by_cases hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
  · -- CASE: integrable. Prove by le_antisymm.
    apply le_antisymm
    · -- (≤) Fatou direction: weightedNormSq G ≤ ∑' ‖a_n‖²
      exact hermiteCoeff_parseval_le hG hInt
    · -- (≥) Bessel direction: ∑' ‖a_n‖² ≤ weightedNormSq G
      apply Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) (fun J => ?_)
      by_cases hJ : J = 0
      · subst hJ
        simp only [Finset.range_zero, Finset.sum_empty]
        unfold weightedNormSq HermiteLEAN.weightedNormSq; positivity
      · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
        rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
            ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by rw [Finset.sum_range]]
        rw [← truncate_normSq k J' G]
        exact bessel_truncate_le hG hInt J'
  · exact hermiteCoeff_parseval_not_integrable hG hInt


/-- Every `G ∈ H_k` admits a Hermite expansion with Parseval. -/
theorem h_k_expansion :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            weightedNormSq G = ∑' n : ℕ, ‖g n‖ ^ 2 := by
  intro k G hG
  exact ⟨hermiteCoeff k G, hermiteCoeff_expansion hG, hermiteCoeff_parseval hG⟩

/-- Compatibility statement: polar/circle representation of an element of `H_k`. -/
theorem circle_representation :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            ∀ r : ℝ, 0 < r →
              ∀ t : Circle,
                G (circlePoint r t) =
                  circleLeadingFactor k r *
                    (fourier (-(k : ℤ)) t : ℂ) *
                      circleSeries k g r t := by
  intro k G hG
  refine ⟨hermiteCoeff k G, hermiteCoeff_expansion hG, fun r hr t => ?_⟩
  have hseries :=
    congrFun (hermiteCoeff_expansion (k := k) (G := G) hG) (circlePoint r t)
  rw [hseries]
  unfold hermiteSeries circleSeries
  simp_rw [phi_polar (k := k) (r := r) hr t]
  let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
  have htsum :
      (∑' n : ℕ,
          hermiteCoeff k G n *
            (circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
              ((qkn k n r : ℂ) * fourier (n : ℤ) t))) =
        ∑' n : ℕ,
          c * (hermiteCoeff k G n * ((qkn k n r : ℂ) * fourier (n : ℤ) t)) := by
    apply tsum_congr
    intro n
    simp [c]
    ring
  rw [htsum, tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  ring

/-- Canonical circle representation in terms of `hermiteCoeff`. -/
theorem circle_representation_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ, 0 < r →
          ∀ t : Circle,
            G (circlePoint r t) =
              circleLeadingFactor k r *
                (fourier (-(k : ℤ)) t : ℂ) *
                  circleSeries k (hermiteCoeff k G) r t := by
  intro k G hG r hr t
  have hseries := congrFun (hermiteCoeff_expansion (k := k) (G := G) hG) (circlePoint r t)
  rw [hseries]
  unfold hermiteSeries circleSeries
  simp_rw [phi_polar (k := k) (r := r) hr t]
  let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
  have htsum :
      (∑' n : ℕ,
          hermiteCoeff k G n *
            (circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
              ((qkn k n r : ℂ) * fourier (n : ℤ) t))) =
        ∑' n : ℕ, c * (hermiteCoeff k G n * ((qkn k n r : ℂ) * fourier (n : ℤ) t)) := by
    apply tsum_congr
    intro n
    simp [c]
    ring
  rw [htsum, tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  ring

private lemma summable_sq_Phi_eval (k : ℕ) (z : ℂ) :
    Summable (fun n => ‖Phi k n z‖ ^ 2) := by
  let R : ℝ := max 1 ‖z‖
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm]
  have hmajorant :
      Summable (fun n : ℕ => C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)))
          := by
    exact hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hmajorant
  intro n
  have hphi := phi_norm_le_majorant (k := k) (n := n) (R := R) hR hzR
  have hrhs_nonneg :
      0 ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
        Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
    positivity
  have hphi_sq :
      ‖Phi k n z‖ ^ 2 ≤
        (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hphi 2
  have hsqrt_ne : Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by
    positivity
  calc
    ‖Phi k n z‖ ^ 2
      ≤ (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := hphi_sq
    _ = C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
      dsimp [C]
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity)]

private lemma summable_sq_qkn (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun n => |qkn k n r| ^ 2) := by
  let t0 : Circle := QuotientAddGroup.mk 0
  let c : ℝ := ‖circleLeadingFactor k r‖ ^ 2
  have hc_ne : c ≠ 0 := by
    dsimp [c, circleLeadingFactor]
    rw [sq_eq_zero_iff, norm_eq_zero, Complex.ofReal_eq_zero]
    exact div_ne_zero (pow_ne_zero k (ne_of_gt hr))
      (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0)
  have hphi_sq :
      ∀ n : ℕ,
        ‖Phi k n (circlePoint r t0)‖ ^ 2 = c * |qkn k n r| ^ 2 := by
    intro n
    have hphi := phi_polar (k := k) (n := n) (r := r) hr t0
    have hfourk : ‖(fourier (-(k : ℤ)) t0 : ℂ)‖ ^ 2 = 1 := by
      simp [t0]
    have hfourn : ‖(fourier (n : ℤ) t0 : ℂ)‖ ^ 2 = 1 := by
      simp [t0]
    rw [hphi, norm_mul, norm_mul, mul_pow, mul_pow, hfourk]
    rw [norm_mul, mul_pow, hfourn]
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [show ‖circleLeadingFactor k r‖ ^ 2 = c by rfl]
    ring_nf
  have hsPhi := summable_sq_Phi_eval k (circlePoint r t0)
  have hsScaled : Summable (fun n => c⁻¹ * (‖Phi k n (circlePoint r t0)‖ ^ 2)) := by
    exact hsPhi.mul_left c⁻¹
  refine hsScaled.congr ?_
  intro n
  calc
    c⁻¹ * (‖Phi k n (circlePoint r t0)‖ ^ 2)
      = c⁻¹ * (c * |qkn k n r| ^ 2) := by rw [hphi_sq n]
    _ = (c⁻¹ * c) * |qkn k n r| ^ 2 := by ring
    _ = |qkn k n r| ^ 2 := by simp [hc_ne]

/-- Bessel bound for the partial Hermite coefficient squares. -/
private lemma sum_range_sq_hermiteCoeff_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    ∀ J, ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2 ≤ weightedNormSq G := by
  intro J
  by_cases hJ : J = 0
  · subst hJ
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    positivity
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
        ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 by
          rw [Finset.sum_range]]
    rw [← truncate_normSq k J' G]
    exact bessel_truncate_le hG hG.1 J'

private lemma summable_sq_hermiteCoeff {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    Summable (fun n => ‖hermiteCoeff k G n‖ ^ 2) := by
  exact summable_of_sum_range_le (fun n => sq_nonneg _) (sum_range_sq_hermiteCoeff_le hG)

/-- Point evaluations are bounded on `H_k`. -/
theorem point_eval_bounded :
    ∀ {k : ℕ} (z : ℂ),
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ {G : ℂ → ℂ}, G ∈ Hk k → ‖G z‖ ≤ C * weightedNorm G := by
  intro k z
  let C : ℝ := Real.sqrt (∑' n : ℕ, ‖Phi k n z‖ ^ 2)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro G hG
  let u : ℕ → ℝ := fun n => ‖hermiteCoeff k G n * Phi k n z‖
  have hsPhi := summable_sq_Phi_eval k z
  have hu_range : ∀ J, ∑ n ∈ Finset.range J, u n ≤ C * weightedNorm G := by
    intro J
    have hcoeffJ := sum_range_sq_hermiteCoeff_le hG J
    have hphiJ :
        ∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2 ≤ ∑' n : ℕ, ‖Phi k n z‖ ^ 2 := by
      exact hsPhi.sum_le_tsum (Finset.range J) (fun _ _ => sq_nonneg _)
    have hnormsq_nonneg : 0 ≤ weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      positivity
    calc
      ∑ n ∈ Finset.range J, u n
          = ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ * ‖Phi k n z‖ := by
              apply Finset.sum_congr rfl
              intro n hn
              simp [u]
      _ ≤
          Real.sqrt (∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2) *
            Real.sqrt (∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2) := by
              simpa using
                Real.sum_mul_le_sqrt_mul_sqrt (Finset.range J)
                  (fun n => ‖hermiteCoeff k G n‖) (fun n => ‖Phi k n z‖)
      _ ≤ Real.sqrt (weightedNormSq G) * Real.sqrt (∑' n : ℕ, ‖Phi k n z‖ ^ 2) := by
            exact mul_le_mul (Real.sqrt_le_sqrt hcoeffJ) (Real.sqrt_le_sqrt hphiJ)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = C * weightedNorm G := by
            dsimp [C]
            unfold weightedNorm HermiteLEAN.weightedNorm
            rw [mul_comm]
  have hu_summable : Summable u := by
    exact summable_of_sum_range_le (fun n => norm_nonneg _) hu_range
  have hnorm_series : Summable (fun n : ℕ => ‖hermiteCoeff k G n * Phi k n z‖) := by
    simpa [u] using hu_summable
  have htsum : (∑' n : ℕ, hermiteCoeff k G n * Phi k n z) = G z := by
    simpa [hermiteCoeff] using (hG.2 z).tsum_eq
  calc
    ‖G z‖ = ‖∑' n : ℕ, hermiteCoeff k G n * Phi k n z‖ := by
      rw [← htsum]
    _ ≤ ∑' n : ℕ, u n := by
      calc
        ‖∑' n : ℕ, hermiteCoeff k G n * Phi k n z‖
            ≤ ∑' n : ℕ, ‖hermiteCoeff k G n * Phi k n z‖ := norm_tsum_le_tsum_norm hnorm_series
        _ = ∑' n : ℕ, u n := by simp [u]
    _ ≤ C * weightedNorm G := by
      exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hu_range

private lemma summable_circleCoeff_norm {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ}
    (hr : 0 < r) :
    Summable (fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖) := by
  have hcoeff := summable_sq_hermiteCoeff hG
  have hqkn := summable_sq_qkn k hr
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ((hcoeff.add hqkn).div_const 2)
  intro n
  have hmul :
      ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤
        ‖hermiteCoeff k G n‖ * |qkn k n r| := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hAMGM :
      ‖hermiteCoeff k G n‖ * |qkn k n r| ≤
        (‖hermiteCoeff k G n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖hermiteCoeff k G n‖ - |qkn k n r|)]
  exact hmul.trans hAMGM

private lemma summable_circleCoeff_sq {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ}
    (hr : 0 < r) :
    Summable (fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ^ 2) := by
  let d : ℕ → ℝ := fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖
  have hd : Summable d := summable_circleCoeff_norm hG hr
  let M : ℝ := ∑' n : ℕ, d n
  have hM_nonneg : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg (d n)) ?_ (hd.mul_left M)
  intro n
  have hd_le : d n ≤ M := by
    have hsingle :=
      hd.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => norm_nonneg _)
    simpa [M, d] using hsingle
  have hd_nonneg : 0 ≤ d n := norm_nonneg _
  have hmul : d n * d n ≤ M * d n := mul_le_mul_of_nonneg_right hd_le hd_nonneg
  simpa [pow_two, d] using hmul

private lemma truncCirclePoly_eq_sum (k J : ℕ) (r : ℝ) (G : ℂ → ℂ) :
    truncCirclePoly k r J G =
      fun t : Circle =>
        ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
  ext t
  unfold truncCirclePoly finiteCirclePoly
  rw [show frequencyBand 0 (J + 1) = Finset.Icc 0 J by simp [HermiteLEAN.frequencyBand]]
  unfold positiveTrigonometricPolynomial
  calc
    ∑ n ∈ Finset.Icc 0 J,
        finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) n *
          fourier (n : ℤ) t
      = ∑ n : Fin (J + 1),
          finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) n.1 *
            fourier (n.1 : ℤ) t := by
              simpa using
                (sum_Icc_eq_sum_Fin 0 (J + 1) (Nat.succ_le_succ (Nat.zero_le J))
                  (fun n =>
                    finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) n *
                      fourier (n : ℤ) t))
    _ = ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
          simp [finiteCircleCoeff, show ∀ n : Fin (J + 1), n.1 ≤ J by
            intro n
            exact Nat.le_of_lt_succ n.isLt]

private lemma continuous_truncCirclePoly (k J : ℕ) (r : ℝ) (G : ℂ → ℂ) :
    Continuous (truncCirclePoly k r J G) := by
  rw [truncCirclePoly_eq_sum]
  classical
  refine continuous_finsetSum _ ?_
  intro n hn
  continuity

private lemma summable_circleSeries_terms {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ}
    (hr : 0 < r) (t : Circle) :
    Summable (fun n => hermiteCoeff k G n * (qkn k n r : ℂ) * fourier (n : ℤ) t) := by
  have hcoeff := summable_sq_hermiteCoeff hG
  have hqkn := summable_sq_qkn k hr
  refine Summable.of_norm_bounded
    (g := fun n => (‖hermiteCoeff k G n‖ ^ 2 + |qkn k n r| ^ 2) / 2)
    (((hcoeff.add hqkn).div_const 2)) ?_
  intro n
  have hmul :
      ‖hermiteCoeff k G n * (qkn k n r : ℂ) * fourier (n : ℤ) t‖ ≤
        ‖hermiteCoeff k G n‖ * |qkn k n r| := by
    calc
      ‖hermiteCoeff k G n * (qkn k n r : ℂ) * fourier (n : ℤ) t‖
          ≤ ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ * ‖fourier (n : ℤ) t‖ := by
            simp [mul_assoc]
      _ ≤ ‖hermiteCoeff k G n‖ * |qkn k n r| := by
            rw [show ‖fourier (n : ℤ) t‖ = 1 by
              simp]
            simp [Complex.norm_real, Real.norm_eq_abs]
  have hAMGM :
      ‖hermiteCoeff k G n‖ * |qkn k n r| ≤
        (‖hermiteCoeff k G n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖hermiteCoeff k G n‖ - |qkn k n r|)]
  exact hmul.trans hAMGM

private lemma truncCirclePoly_tendsto_circleSeries_pointwise {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    {r : ℝ} (hr : 0 < r) (t : Circle) :
    Filter.Tendsto
      (fun J => truncCirclePoly k r J G t)
      Filter.atTop
      (nhds (circleSeries k (hermiteCoeff k G) r t)) := by
  let a : ℕ → ℂ := fun n => hermiteCoeff k G n * (qkn k n r : ℂ) * fourier (n : ℤ) t
  have hs : Summable a := summable_circleSeries_terms hG hr t
  have hconv :
      Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, a n)
        Filter.atTop (nhds (circleSeries k (hermiteCoeff k G) r t)) := by
    simpa [circleSeries, a] using hs.hasSum.tendsto_sum_nat
  have hEqFun :
      (fun J => truncCirclePoly k r J G t) =
        (fun J => ∑ n ∈ Finset.range (J + 1), a n) := by
    ext J
    simpa [a, Finset.sum_range] using congrFun (truncCirclePoly_eq_sum k J r G) t
  rw [hEqFun]
  exact hconv.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))

private theorem circleSeries_l2_identity_canonical :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            circleL2Sq (circleSeries k (hermiteCoeff k G) r) =
              ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2 := by
  intro k G hG r hr
  let c : ℕ → ℂ := fun n => hermiteCoeff k G n * (qkn k n r : ℂ)
  have hc_norm : Summable (fun n => ‖c n‖) := by
    simpa [c] using summable_circleCoeff_norm (k := k) (G := G) hG hr
  have hc_sq : Summable (fun n => ‖c n‖ ^ 2) := by
    simpa [c] using summable_circleCoeff_sq (k := k) (G := G) hG hr
  let M : ℝ := ∑' n : ℕ, ‖c n‖
  have hM_nonneg : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  have hbound :
      ∀ J : ℕ, ∀ᵐ t : Circle ∂AddCircle.haarAddCircle,
        ‖‖truncCirclePoly k r J G t‖ ^ 2‖ ≤ (fun _ : Circle => M ^ 2) t := by
    intro J
    refine Filter.Eventually.of_forall ?_
    intro t
    have hpartial_le :
        ‖truncCirclePoly k r J G t‖ ≤ M := by
      rw [truncCirclePoly_eq_sum]
      calc
        ‖∑ n : Fin (J + 1), hermiteCoeff k G n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖
            ≤ ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖
                := by
              exact norm_sum_le _ _
        _ = ∑ n : Fin (J + 1), ‖c n.1‖ := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              calc
                ‖hermiteCoeff k G n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖
                    = ‖c n.1‖ * ‖fourier (n.1 : ℤ) t‖ := by
                        simp [c, mul_assoc]
                _ = ‖c n.1‖ := by
                      rw [show ‖fourier (n.1 : ℤ) t‖ = 1 by
                        simp]
                      ring
        _ = ∑ n ∈ Finset.range (J + 1), ‖c n‖ := by rw [Finset.sum_range]
        _ ≤ M := by
              exact hc_norm.sum_le_tsum _ (fun n hn => norm_nonneg _)
    have hnonneg : 0 ≤ ‖truncCirclePoly k r J G t‖ ^ 2 := sq_nonneg _
    have habs :
        ‖‖truncCirclePoly k r J G t‖ ^ 2‖ = ‖truncCirclePoly k r J G t‖ ^ 2 := by
      rw [Real.norm_of_nonneg hnonneg]
    rw [habs]
    have hsq_le : ‖truncCirclePoly k r J G t‖ ^ 2 ≤ M ^ 2 := by
      have hmul :=
        mul_le_mul hpartial_le hpartial_le (norm_nonneg _) hM_nonneg
      simpa [pow_two] using hmul
    simpa using hsq_le
  have hlim :
      ∀ᵐ t : Circle ∂AddCircle.haarAddCircle,
        Filter.Tendsto
          (fun J => ‖truncCirclePoly k r J G t‖ ^ 2)
          Filter.atTop
          (nhds (‖circleSeries k (hermiteCoeff k G) r t‖ ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    exact ((truncCirclePoly_tendsto_circleSeries_pointwise (k := k) (G := G) hG hr t).norm.pow 2)
  have hIntTendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := AddCircle.haarAddCircle)
      (fun _ : Circle => M ^ 2)
      (fun J =>
        ((continuous_truncCirclePoly k J r G).norm.pow 2).aestronglyMeasurable)
      (MeasureTheory.integrable_const (M ^ 2))
      hbound hlim
  have hCircleTendsto :
      Filter.Tendsto
        (fun J => circleL2Sq (truncCirclePoly k r J G))
        Filter.atTop
        (nhds (circleL2Sq (circleSeries k (hermiteCoeff k G) r))) := by
    simp only [circleL2Sq]
    exact hIntTendsto
  let d : ℕ → ℝ := fun n => |qkn k n r| ^ 2 * ‖hermiteCoeff k G n‖ ^ 2
  have hd : Summable d := by
    refine hc_sq.congr ?_
    intro n
    dsimp [d, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hsum_tendsto :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), d n.1)
        Filter.atTop
        (nhds (∑' n : ℕ, d n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, d n)
          Filter.atTop (nhds (∑' n : ℕ, d n)) :=
      (hd.hasSum_iff_tendsto_nat).1 hd.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), d n)
          Filter.atTop (nhds (∑' n : ℕ, d n)) := by
      exact hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    simpa [d, Finset.sum_range] using hshift
  have hsum_tendsto' :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖hermiteCoeff k G n.1‖ ^ 2)
        Filter.atTop
        (nhds (∑' n : ℕ, |qkn k n r| ^ 2 * ‖hermiteCoeff k G n‖ ^ 2)) := by
    simpa [d] using hsum_tendsto
  have hEqSeq :
      (fun J => circleL2Sq (truncCirclePoly k r J G)) =
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖hermiteCoeff k G n.1‖ ^ 2) := by
    ext J
    simpa [mul_comm, mul_left_comm, mul_assoc] using (truncCirclePoly_l2_identity k J r G)
  have hlimit_eq :
      circleL2Sq (circleSeries k (hermiteCoeff k G) r) =
        ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2 := by
    apply tendsto_nhds_unique hCircleTendsto
    rw [hEqSeq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_tendsto'
  exact hlimit_eq

/-- Compatibility statement: circle Parseval identity for an `H_k` expansion. -/
theorem circleSeries_l2_identity :
    ∀ {k : ℕ} {G : ℂ → ℂ} {g : ℕ → ℂ},
      G ∈ Hk k →
        G = hermiteSeries k g →
          Summable (fun n => ‖g n‖ ^ 2) →
          ∀ r : ℝ,
            0 < r →
              circleL2Sq (circleSeries k g r) =
                ∑' n : ℕ, ‖g n‖ ^ 2 * |qkn k n r| ^ 2 := by
  intro k G g _hG _hEq hg r hr
  let c : ℕ → ℂ := fun n => g n * (qkn k n r : ℂ)
  have hqkn := summable_sq_qkn k hr
  have hc_norm : Summable (fun n => ‖c n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ((hg.add hqkn).div_const 2)
    intro n
    have hmul :
        ‖g n * (qkn k n r : ℂ)‖ ≤ ‖g n‖ * |qkn k n r| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    have hAMGM :
        ‖g n‖ * |qkn k n r| ≤ (‖g n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖g n‖ - |qkn k n r|)]
    exact hmul.trans hAMGM
  have hc_sq : Summable (fun n => ‖c n‖ ^ 2) := by
    let d' : ℕ → ℝ := fun n => ‖c n‖
    have hd' : Summable d' := by simpa [d', c] using hc_norm
    let M' : ℝ := ∑' n : ℕ, d' n
    have hM'_nonneg : 0 ≤ M' := tsum_nonneg fun n => norm_nonneg _
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg (d' n)) ?_ (hd'.mul_left M')
    intro n
    have hd'_le : d' n ≤ M' := by
      have hsingle := hd'.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => norm_nonneg _)
      simpa [M', d'] using hsingle
    have hd'_nonneg : 0 ≤ d' n := norm_nonneg _
    have hmul : d' n * d' n ≤ M' * d' n := mul_le_mul_of_nonneg_right hd'_le hd'_nonneg
    simpa [pow_two, d'] using hmul
  have hpoly_eq :
      ∀ J,
        finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) =
          fun t : Circle => ∑ n : Fin (J + 1), g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
    intro J
    let aJ : Fin (J + 1) → ℂ := fun n => g n.1
    ext t
    change
      Finset.sum (Finset.Icc 0 (0 + (J + 1) - 1))
          (fun n => (if h : n < J + 1 then aJ ⟨n, h⟩ * (qkn k n r : ℂ) else 0) * fourier (n : ℤ)
              t) =
        ∑ n : Fin (J + 1), g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t
    rw [sum_Icc_eq_sum_Fin 0 (J + 1) (Nat.succ_le_succ (Nat.zero_le J))]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : (x : ℕ) < J + 1 := x.isLt
    simp [aJ, hx']
  have hcontPoly :
      ∀ J, Continuous (finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1)) := by
    intro J
    rw [hpoly_eq J]
    refine continuous_finsetSum _ ?_
    intro n hn
    continuity
  let M : ℝ := ∑' n : ℕ, ‖c n‖
  have hM_nonneg : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  have hbound :
      ∀ J : ℕ, ∀ᵐ t : Circle ∂AddCircle.haarAddCircle,
        ‖‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2‖ ≤ (fun _ : Circle => M ^ 2)
            t := by
    intro J
    refine Filter.Eventually.of_forall ?_
    intro t
    have hpartial_le :
        ‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ≤ M := by
      rw [hpoly_eq J]
      calc
        ‖∑ n : Fin (J + 1), g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖
            ≤ ∑ n : Fin (J + 1), ‖g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖ := by
              exact norm_sum_le _ _
        _ = ∑ n : Fin (J + 1), ‖c n.1‖ := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              calc
                ‖g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t‖ = ‖c n.1‖ * ‖fourier (n.1 : ℤ)
                    t‖ := by
                  simp [c, mul_assoc]
                _ = ‖c n.1‖ := by
                  rw [show ‖fourier (n.1 : ℤ) t‖ = 1 by
                    simp]
                  ring
        _ = ∑ n ∈ Finset.range (J + 1), ‖c n‖ := by rw [Finset.sum_range]
        _ ≤ M := by
              exact hc_norm.sum_le_tsum _ (fun n hn => norm_nonneg _)
    have hnonneg : 0 ≤ ‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2 := sq_nonneg _
    have habs :
        ‖‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2‖ =
          ‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2 := by
      rw [Real.norm_of_nonneg hnonneg]
    rw [habs]
    have hsq_le : ‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2 ≤ M ^ 2 := by
      have hmul := mul_le_mul hpartial_le hpartial_le (norm_nonneg _) hM_nonneg
      simpa [pow_two] using hmul
    simpa using hsq_le
  have hlim :
      ∀ᵐ t : Circle ∂AddCircle.haarAddCircle,
        Filter.Tendsto
          (fun J => ‖finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t‖ ^ 2)
          Filter.atTop
          (nhds (‖circleSeries k g r t‖ ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    let a : ℕ → ℂ := fun n => g n * (qkn k n r : ℂ) * fourier (n : ℤ) t
    have hs : Summable a := by
      refine Summable.of_norm_bounded (g := fun n => ‖c n‖) hc_norm ?_
      intro n
      have haeq : ‖a n‖ = ‖c n‖ := by
        calc
          ‖a n‖ = ‖c n‖ * ‖fourier (n : ℤ) t‖ := by
            simp [a, c, mul_assoc]
          _ = ‖c n‖ := by
            rw [show ‖fourier (n : ℤ) t‖ = 1 by
              simp]
            ring
      exact haeq.le
    have hconv :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, a n) Filter.atTop (nhds (circleSeries k g r
            t)) := by
      simpa [circleSeries, a] using hs.hasSum.tendsto_sum_nat
    have hEqFun :
        (fun J => finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t) =
          (fun J => ∑ n ∈ Finset.range (J + 1), a n) := by
      ext J
      simpa [a, Finset.sum_range] using congrFun (hpoly_eq J) t
    have hconv' :
        Filter.Tendsto
          (fun J => finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) t)
          Filter.atTop
          (nhds (circleSeries k g r t)) := by
      rw [hEqFun]
      exact hconv.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    exact (hconv'.norm.pow 2)
  have hIntTendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := AddCircle.haarAddCircle)
      (fun _ : Circle => M ^ 2)
      (fun J => ((hcontPoly J).norm.pow 2).aestronglyMeasurable)
      (MeasureTheory.integrable_const (M ^ 2))
      hbound hlim
  have hCircleTendsto :
      Filter.Tendsto
        (fun J => circleL2Sq (finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1)))
        Filter.atTop
        (nhds (circleL2Sq (circleSeries k g r))) := by
    simp only [circleL2Sq]
    exact hIntTendsto
  let d : ℕ → ℝ := fun n => |qkn k n r| ^ 2 * ‖g n‖ ^ 2
  have hd : Summable d := by
    refine hc_sq.congr ?_
    intro n
    dsimp [d, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hsum_tendsto :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), d n.1)
        Filter.atTop
        (nhds (∑' n : ℕ, d n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, d n) Filter.atTop (nhds (∑' n : ℕ, d n)) :=
      (hd.hasSum_iff_tendsto_nat).1 hd.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), d n) Filter.atTop
          (nhds (∑' n : ℕ, d n)) := by
      exact hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    simpa [d, Finset.sum_range] using hshift
  have hsum_tendsto' :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖g n.1‖ ^ 2)
        Filter.atTop
        (nhds (∑' n : ℕ, |qkn k n r| ^ 2 * ‖g n‖ ^ 2)) := by
    simpa [d] using hsum_tendsto
  have hEqSeq :
      (fun J => circleL2Sq (finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1))) =
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖g n.1‖ ^ 2) := by
    ext J
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (finiteCirclePoly_l2_identity (k := k) (D := J + 1) (r := r) (a := fun n : Fin (J + 1) => g
          n.1))
  apply tendsto_nhds_unique hCircleTendsto
  rw [hEqSeq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_tendsto'

/-- Circle Parseval identity for the canonical coefficient sequence. -/
theorem circleSeries_l2_identity_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            circleL2Sq (circleSeries k (hermiteCoeff k G) r) =
              ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2 := by
  intro k G hG r hr
  exact circleSeries_l2_identity_canonical (k := k) (G := G) hG r hr

/-- The canonical circle series has the expected Fourier coefficients. -/
theorem circleSeries_fourierCoeff_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ {r : ℝ}, 0 < r →
          ∀ n : ℕ,
            fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ) =
              hermiteCoeff k G n * (qkn k n r : ℂ) := by
  intro k G hG r hr n
  let c : ℕ → ℂ := fun m => hermiteCoeff k G m * (qkn k m r : ℂ)
  have hc_norm : Summable (fun m => ‖c m‖) := by
    simpa [c] using summable_circleCoeff_norm (k := k) (G := G) hG hr
  have hInt :
      ∀ m : ℕ,
        Integrable
          (fun t : Circle => fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t))
          AddCircle.haarAddCircle := by
    intro m
    have hcm :
        Integrable (fun t : Circle => c m * fourier (m : ℤ) t) AddCircle.haarAddCircle := by
      simpa [smul_eq_mul, mul_comm] using
        ((MeasureTheory.integrable_const (c m)).fourier_smul (T := T) (m : ℤ))
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hcm.fourier_smul (T := T) (-(n : ℤ)))
  have hIntNorm :
      Summable
        (fun m : ℕ =>
          ∫ t : Circle,
            ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖ ∂AddCircle.haarAddCircle) := by
    have hEq :
        (fun m : ℕ =>
          ∫ t : Circle,
            ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖ ∂AddCircle.haarAddCircle) =
          fun m : ℕ => ‖c m‖ := by
      ext m
      calc
        ∫ t : Circle, ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖ ∂AddCircle.haarAddCircle
          = ∫ t : Circle, ‖c m‖ ∂AddCircle.haarAddCircle := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [norm_mul, norm_mul]
              simp [c]
        _ = ‖c m‖ := by simp
    rw [hEq]
    exact hc_norm
  have hsCircle :
      ∀ t : Circle, Summable (fun m : ℕ => c m * fourier (m : ℤ) t) := by
    intro t
    refine Summable.of_norm_bounded (g := fun m => ‖c m‖) hc_norm ?_
    intro m
    rw [norm_mul, show ‖fourier (m : ℤ) t‖ = 1 by
      simp, mul_one]
  calc
    fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ)
      = ∑' m : ℕ,
          ∫ t : Circle,
            fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t) ∂AddCircle.haarAddCircle := by
            change
              ∫ t : Circle, fourier (-(n : ℤ)) t * circleSeries k (hermiteCoeff k G) r t
                ∂AddCircle.haarAddCircle =
                ∑' m : ℕ,
                  ∫ t : Circle,
                    fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t) ∂AddCircle.haarAddCircle
            have hfun :
                (fun t : Circle => fourier (-(n : ℤ)) t * circleSeries k (hermiteCoeff k G) r t) =
                  fun t : Circle => ∑' m : ℕ, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t) := by
              funext t
              unfold circleSeries
              rw [← tsum_mul_left]
            rw [hfun]
            rw [MeasureTheory.integral_tsum_of_summable_integral_norm hInt hIntNorm]
    _ = ∑' m : ℕ, if m = n then c m else 0 := by
          apply tsum_congr
          intro m
          calc
            ∫ t : Circle, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t) ∂AddCircle.haarAddCircle
              = fourierCoeff (fun t : Circle => c m * fourier (m : ℤ) t) (n : ℤ) := by
                  rfl
            _ = c m * fourierCoeff (fourier (m : ℤ)) (n : ℤ) := by
                  rw [fourierCoeff.const_mul]
            _ = if m = n then c m else 0 := by
                  by_cases hm : m = n
                  · subst m
                    have hfour :
                        fourierCoeff (T := T) (fourier (n : ℤ)) (n : ℤ) = 1 := by
                      simpa [Pi.single_apply] using
                        congrFun (fourierCoeff_fourier (T := T) (n : ℤ)) (n : ℤ)
                    simp [hfour]
                  · have hfour :
                        fourierCoeff (T := T) (fourier (m : ℤ)) (n : ℤ) = 0 := by
                      simpa [Pi.single_apply, hm] using
                        congrFun (fourierCoeff_fourier (T := T) (m : ℤ)) (n : ℤ)
                    simp [hm, hfour]
    _ = c n := by
          simp
    _ = hermiteCoeff k G n * (qkn k n r : ℂ) := by
          simp [c]

/-- Orthogonality to `Phi k 0` yields an expansion with vanishing zero mode. -/
theorem h_k_expansion_perp_phi0 :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        weightedInner G (Phi k 0) = 0 →
          ∃ g : ℕ → ℂ,
            G = hermiteSeries k g ∧
              g 0 = 0 := by
  intro k G hG hperp
  refine ⟨hermiteCoeff k G, hermiteCoeff_expansion (k := k) (G := G) hG, ?_⟩
  simpa [phi0] using (orthogonal_phi0_iff_hermiteCoeff_zero (k := k) (G := G)).mp hperp

private lemma sub_truncate_mem_Hk {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (J : ℕ) :
    (fun z => G z - truncate k J G z) ∈ Hk k := by
  refine ⟨?_, ?_⟩
  · have hG_aesm : AEStronglyMeasurable G volume := by
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
      · intro J
        unfold truncate finiteHermiteSum
        exact
          (continuous_finsetSum _ (fun m _ =>
            continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
    have hT_aesm : AEStronglyMeasurable (truncate k J G) volume := by
      unfold truncate finiteHermiteSum
      exact
        (continuous_finsetSum _ (fun m _ =>
          continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
    have hbound :
        Integrable
          (fun z : ℂ =>
            (2 : ℝ) *
              (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
                ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      simpa [two_mul, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using (hG.1.add (integrable_truncate_normSq_exp k J G)).const_mul (2 : ℝ)
    have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
      (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
    have hmeas :
        AEStronglyMeasurable
          (fun z : ℂ => ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume := by
      exact ((hG_aesm.sub hT_aesm).norm.pow 2).mul hExp_aesm
    refine MeasureTheory.Integrable.mono' hbound hmeas ?_
    filter_upwards with z
    have hsub : ‖G z - truncate k J G z‖ ≤ ‖G z‖ + ‖truncate k J G z‖ := norm_sub_le _ _
    have hexp : 0 ≤ rexp (-‖z‖ ^ 2) := exp_nonneg _
    have hsq :
        ‖G z - truncate k J G z‖ ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2) := by
      have hsubsq :
          ‖G z - truncate k J G z‖ ^ 2 ≤ (‖G z‖ + ‖truncate k J G z‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
      have hab :
          (‖G z‖ + ‖truncate k J G z‖) ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2) := by
        nlinarith [sq_nonneg (‖G z‖ - ‖truncate k J G z‖)]
      exact le_trans hsubsq hab
    have hmul :
        ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) ≤
          (2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hsq hexp
    have hnonneg :
        0 ≤ ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)
          ≤ (2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := hmul
      _ = (2 : ℝ) *
            (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
              ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by ring
  · intro z
    have hGz := hG.2 z
    have hTzH := (truncate_mem_Hk k J G).2 z
    have hcoeff_decomp : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      intro n
      have h1 := hermiteCoeff_sub_truncate k J G n
      have h2 := hermiteCoeff_truncate (k := k) (J := J) (G := G) n
      simp only [hermiteCoeff] at h1 h2
      rw [h1]
      by_cases hn : n < J + 1 <;> simp [hn, h2]
    have hterm : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) * Phi k n z =
          weightedInner G (Phi k n) * Phi k n z -
            weightedInner (truncate k J G) (Phi k n) * Phi k n z := by
      intro n
      rw [hcoeff_decomp]
      ring
    simp_rw [hterm]
    exact hGz.sub hTzH

/-- Truncations converge to `G` in the weighted norm. -/
theorem truncate_tendsto :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ ε : ℝ,
          0 < ε →
            ∃ J0 : ℕ, ∀ J ≥ J0, weightedNorm (truncate k J G - G) ≤ ε := by
  intro k G hG ε hε
  -- Step 1: G - truncate k J G ∈ Hk k
  have hDiff_mem : ∀ J, (fun z => G z - truncate k J G z) ∈ Hk k := by
    intro J
    refine ⟨?_, ?_⟩
    · have hG_aesm : AEStronglyMeasurable G volume := by
        apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
        · intro J
          unfold truncate finiteHermiteSum
          exact
            (continuous_finsetSum _ (fun m _ =>
              continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
        · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
      have hT_aesm : AEStronglyMeasurable (truncate k J G) volume := by
        unfold truncate finiteHermiteSum
        exact
          (continuous_finsetSum _ (fun m _ =>
            continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
      have hbound :
          Integrable
            (fun z : ℂ =>
              (2 : ℝ) *
                (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
                  ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
        simpa [two_mul, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using (hG.1.add (integrable_truncate_normSq_exp k J G)).const_mul (2 : ℝ)
      have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
        (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
      have hmeas :
          AEStronglyMeasurable
            (fun z : ℂ => ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume := by
        exact ((hG_aesm.sub hT_aesm).norm.pow 2).mul hExp_aesm
      refine MeasureTheory.Integrable.mono' hbound hmeas ?_
      filter_upwards with z
      have hsub : ‖G z - truncate k J G z‖ ≤ ‖G z‖ + ‖truncate k J G z‖ := norm_sub_le _ _
      have hexp : 0 ≤ rexp (-‖z‖ ^ 2) := exp_nonneg _
      have hsq :
          ‖G z - truncate k J G z‖ ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2) := by
        have hsubsq :
            ‖G z - truncate k J G z‖ ^ 2 ≤ (‖G z‖ + ‖truncate k J G z‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
        have hab :
            (‖G z‖ + ‖truncate k J G z‖) ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2) := by
          nlinarith [sq_nonneg (‖G z‖ - ‖truncate k J G z‖)]
        exact le_trans hsubsq hab
      have hmul :
          ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) ≤
            (2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_right hsq hexp
      have hnonneg :
          0 ≤ ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
        positivity
      rw [Real.norm_of_nonneg hnonneg]
      calc
        ‖G z - truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)
            ≤ (2 * (‖G z‖ ^ 2 + ‖truncate k J G z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := hmul
        _ = (2 : ℝ) *
              (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
                ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by ring
    · intro z
      have hGz := hG.2 z
      have hTzH := (truncate_mem_Hk k J G).2 z
      have hcoeff_decomp : ∀ n,
          weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) =
            weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
        intro n
        have h1 := hermiteCoeff_sub_truncate k J G n
        have h2 := hermiteCoeff_truncate (k := k) (J := J) (G := G) n
        simp only [hermiteCoeff] at h1 h2
        rw [h1]
        by_cases hn : n < J + 1 <;> simp [hn, h2]
      have hterm : ∀ n,
          weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) * Phi k n z =
            weightedInner G (Phi k n) * Phi k n z -
              weightedInner (truncate k J G) (Phi k n) * Phi k n z := by
        intro n
        rw [hcoeff_decomp]
        ring
      simp_rw [hterm]
      exact hGz.sub hTzH
  -- Step 2: Norm symmetry
  have hNormSym : ∀ J, weightedNorm (truncate k J G - G) =
      weightedNorm (fun z => G z - truncate k J G z) := by
    intro J
    change Real.sqrt _ = Real.sqrt _
    congr 1
    change (1 / Real.pi) * _ = (1 / Real.pi) * _
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [Pi.sub_apply]
    rw [norm_sub_rev]
  -- Step 3: Parseval for the difference
  have hParseval_diff : ∀ J, weightedNormSq (fun z => G z - truncate k J G z) =
      ∑' n : ℕ, ‖hermiteCoeff k (fun z => G z - truncate k J G z) n‖ ^ 2 := by
    intro J
    exact hermiteCoeff_parseval (hDiff_mem J)
  -- Step 4: Coefficient characterization via hermiteCoeff_sub_truncate
  have hCoeff_tail : ∀ J n,
      hermiteCoeff k (fun z => G z - truncate k J G z) n =
        if n < J + 1 then 0 else hermiteCoeff k G n := by
    intro J n
    exact hermiteCoeff_sub_truncate k J G n
  -- Step 5: Parseval for G
  have hParseval_G := hermiteCoeff_parseval hG
  -- Step 6: Simplify the tsum for the difference
  have hDiffNormSq : ∀ J, weightedNormSq (fun z => G z - truncate k J G z) =
      ∑' n : ℕ, if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2 := by
    intro J
    rw [hParseval_diff J]
    congr 1
    ext n
    rw [hCoeff_tail J n]
    split_ifs with h
    · simp
    · rfl
  -- Step 7: Conditional tsum equals shifted tsum
  have hShift : ∀ J, (∑' n : ℕ, if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2) =
      ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2 := by
    intro J
    let h := fun n : ℕ => if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2
    change ∑' n, h n = ∑' n, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2
    have hkey : ∑' c, h (c + (J + 1)) = ∑' c, ‖hermiteCoeff k G (c + (J + 1))‖ ^ 2 := by
      apply tsum_congr
      intro c
      simp only [h, show ¬ (c + (J + 1) < J + 1) from by omega, ite_false]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab; simp only [] at hab; omega
    have hsupp : Function.support h ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [h, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  -- Step 8: It suffices to show weightedNormSq → 0
  suffices h : ∃ J0 : ℕ, ∀ J ≥ J0,
      weightedNormSq (fun z => G z - truncate k J G z) ≤ ε ^ 2 by
    obtain ⟨J0, hJ0⟩ := h
    refine ⟨J0, fun J hJ => ?_⟩
    rw [hNormSym]
    unfold weightedNorm HermiteLEAN.weightedNorm
    rw [show ε = Real.sqrt (ε ^ 2) from by rw [Real.sqrt_sq (le_of_lt hε)]]
    exact Real.sqrt_le_sqrt (hJ0 J hJ)
  -- Step 9: Use tendsto_sum_nat_add
  have hTendsto := tendsto_sum_nat_add (fun n => ‖hermiteCoeff k G n‖ ^ 2)
  rw [Metric.tendsto_atTop] at hTendsto
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨N, hN⟩ := hTendsto (ε ^ 2) hεsq
  refine ⟨N, fun J hJ => ?_⟩
  rw [hDiffNormSq, hShift]
  have hJN := hN (J + 1) (by omega)
  rw [dist_zero_right] at hJN
  linarith [abs_nonneg (∑' n, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2),
    (abs_lt.mp hJN).2]

/-- Truncations converge locally uniformly on bounded sets. -/
theorem truncate_locally_uniform :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ R ε : ℝ,
          0 < R →
            0 < ε →
              ∃ J0 : ℕ,
                ∀ J ≥ J0,
                  ∀ z : ℂ, ‖z‖ ≤ R → ‖truncate k J G z - G z‖ ≤ ε := by
  intro k G hG R ε _hR hε
  let R' : ℝ := max 1 R
  have hR' : 1 ≤ R' := by
    exact le_max_left _ _
  have hRR' : R ≤ R' := by
    exact le_max_right _ _
  let B : ℕ → ℝ := fun n =>
    ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R' ^ k * R' ^ n) /
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))
  have hBsq :
      Summable (fun n : ℕ => B n ^ 2) := by
    let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R' ^ k) ^ 2) / (Nat.factorial k : ℝ)
    have hbase0 :
        Summable
          (fun n : ℕ => ((n + 1 : ℝ) ^ (2 * k)) * (R' ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
      apply summable_nat_pow_mul_pow_div_factorial_nonneg
      positivity
    have hbase :
        Summable (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R' ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
      refine hbase0.congr ?_
      intro n
      rw [← pow_mul, ← pow_mul]
      simp [pow_mul, Nat.mul_comm]
    have hmajorant :
        Summable
          (fun n : ℕ =>
            C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R' ^ n) ^ 2) / (Nat.factorial n : ℝ))) := by
      exact hbase.mul_left C
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg (B n)) ?_ hmajorant
    intro n
    have hsqrt_ne : Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by
      positivity
    calc
      B n ^ 2 ≤ B n ^ 2 := le_rfl
      _ = C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R' ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
          dsimp [B, C]
          field_simp [hsqrt_ne]
          rw [Real.sq_sqrt (by positivity)]
  have hcoeff : Summable (fun n => ‖hermiteCoeff k G n‖ ^ 2) := summable_sq_hermiteCoeff hG
  have hprod : Summable (fun n => ‖hermiteCoeff k G n‖ * B n) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ ((hcoeff.add hBsq).div_const 2)
    intro n
    nlinarith [sq_nonneg (‖hermiteCoeff k G n‖ - B n)]
  have htail := tendsto_sum_nat_add (fun n => ‖hermiteCoeff k G n‖ * B n)
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨J0, hJ0⟩ := htail ε hε
  refine ⟨J0, fun J hJ z hz => ?_⟩
  have hzR' : ‖z‖ ≤ R' := le_trans hz hRR'
  let a : ℕ → ℂ := fun n => hermiteCoeff k G n * Phi k n z
  have hs : Summable a := by
    refine Summable.of_norm_bounded (g := fun n => ‖hermiteCoeff k G n‖ * B n) hprod ?_
    intro n
    dsimp [a]
    calc
      ‖hermiteCoeff k G n * Phi k n z‖ = ‖hermiteCoeff k G n‖ * ‖Phi k n z‖ := by
        simp []
      _ ≤ ‖hermiteCoeff k G n‖ * B n := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact phi_norm_le_majorant (k := k) (n := n) (R := R') hR' hzR'
  have hprod_tail :
      Summable (fun n => ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1))) := by
    exact (_root_.summable_nat_add_iff
      (f := fun n => ‖hermiteCoeff k G n‖ * B n) (J + 1)).2 hprod
  have hs_tail : Summable (fun n : ℕ => a (n + (J + 1))) := by
    refine Summable.of_norm_bounded (g := fun n => ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J +
        1)))
      hprod_tail ?_
    intro n
    dsimp [a]
    calc
      ‖hermiteCoeff k G (n + (J + 1)) * Phi k (n + (J + 1)) z‖
          = ‖hermiteCoeff k G (n + (J + 1))‖ * ‖Phi k (n + (J + 1)) z‖ := by
            simp []
      _ ≤ ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact
              phi_norm_le_majorant (k := k) (n := n + (J + 1)) (R := R') hR' hzR'
  have hnorm_tail :
      Summable (fun n : ℕ => ‖a (n + (J + 1))‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hprod_tail
    intro n
    dsimp [a]
    calc
      ‖hermiteCoeff k G (n + (J + 1)) * Phi k (n + (J + 1)) z‖
          = ‖hermiteCoeff k G (n + (J + 1))‖ * ‖Phi k (n + (J + 1)) z‖ := by
            simp []
      _ ≤ ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact
              phi_norm_le_majorant (k := k) (n := n + (J + 1)) (R := R') hR' hzR'
  have htail_small :
      ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) < ε := by
    have hJtail := hJ0 (J + 1) (by omega)
    rw [dist_zero_right] at hJtail
    have hnonneg :
        0 ≤ ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
      exact tsum_nonneg fun n => by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hJtail
  have htrunc :
      truncate k J G z = ∑ n ∈ Finset.range (J + 1), a n := by
    change ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z = _
    rw [Finset.sum_range]
  have htsum : (∑' n : ℕ, a n) = G z := by
    simpa [a, hermiteCoeff] using (hG.2 z).tsum_eq
  have hsplit :
      ∑ n ∈ Finset.range (J + 1), a n + ∑' n : ℕ, a (n + (J + 1)) = G z := by
    simpa [htsum] using hs.sum_add_tsum_nat_add (J + 1)
  have htail_eq :
      truncate k J G z - G z = -∑' n : ℕ, a (n + (J + 1)) := by
    calc
      truncate k J G z - G z
          = (∑ n ∈ Finset.range (J + 1), a n) - G z := by rw [htrunc]
      _ = (∑ n ∈ Finset.range (J + 1), a n) -
            ((∑ n ∈ Finset.range (J + 1), a n) + ∑' n : ℕ, a (n + (J + 1))) := by rw [hsplit]
      _ = -∑' n : ℕ, a (n + (J + 1)) := by ring
  have htsum_le :
      ∑' n : ℕ, ‖a (n + (J + 1))‖ ≤
        ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
    refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) ?_
    intro N
    calc
      ∑ n ∈ Finset.range N, ‖a (n + (J + 1))‖
          ≤ ∑ n ∈ Finset.range N, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            dsimp [a]
            calc
              ‖hermiteCoeff k G (n + (J + 1)) * Phi k (n + (J + 1)) z‖
                  = ‖hermiteCoeff k G (n + (J + 1))‖ * ‖Phi k (n + (J + 1)) z‖ := by
                    simp []
              _ ≤ ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                    exact
                      phi_norm_le_majorant (k := k) (n := n + (J + 1)) (R := R') hR' hzR'
      _ ≤ ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := by
            exact hprod_tail.sum_le_tsum _ (fun n hn => by positivity)
  calc
    ‖truncate k J G z - G z‖ = ‖∑' n : ℕ, a (n + (J + 1))‖ := by rw [htail_eq, norm_neg]
    _ ≤ ∑' n : ℕ, ‖a (n + (J + 1))‖ := norm_tsum_le_tsum_norm hnorm_tail
    _ ≤ ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ * B (n + (J + 1)) := htsum_le
    _ ≤ ε := le_of_lt htail_small

/-- The finite circle polynomials of `G` converge in circle `L²` to the Hermite circle series. -/
theorem truncCirclePoly_tendsto_circleSeries :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            ∀ ε : ℝ,
              0 < ε →
                ∃ J0 : ℕ,
                  ∀ J ≥ J0,
                    circleL2Sq
                        (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r) ≤
                      ε := by
  intro k G hG r hr ε hε
  let d : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2
  have hd : Summable d := by
    refine (summable_circleCoeff_sq hG hr).congr ?_
    intro n
    dsimp [d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have htail := tendsto_sum_nat_add d
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨J0, hJ0⟩ := htail ε hε
  refine ⟨J0, fun J hJ => ?_⟩
  let HJ : ℂ → ℂ := fun z => G z - truncate k J G z
  have hHJ : HJ ∈ Hk k := sub_truncate_mem_Hk hG J
  have hpoint :
      truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r =
        fun t : Circle => -circleSeries k (hermiteCoeff k HJ) r t := by
    ext t
    let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
    have hc_ne : c ≠ 0 := by
      dsimp [c, circleLeadingFactor]
      apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr <|
          div_ne_zero (pow_ne_zero k (ne_of_gt hr))
            (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0)
      · change ((fourier (-(k : ℤ)) t : ℂ)) ≠ 0
        intro h0
        have hnorm : ‖(fourier (-(k : ℤ)) t : ℂ)‖ = 1 := by
          simp
        have : (0 : ℝ) = 1 := by
          rw [h0, norm_zero] at hnorm
          exact hnorm
        linarith
    have hGcircle := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
    have hTcircle := truncate_circle k J G hr t
    have hHcircle := circle_representation_hermiteCoeff (k := k) (G := HJ) hHJ r hr t
    have hmain :
        c * (circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t) =
          c * circleSeries k (hermiteCoeff k HJ) r t := by
      calc
        c * (circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t)
            = c * circleSeries k (hermiteCoeff k G) r t - c * truncCirclePoly k r J G t := by
                ring
        _ = circleSeries k (hermiteCoeff k G) r t * circleLeadingFactor k r *
              ↑(-↑k • t).toCircle -
              truncCirclePoly k r J G t * circleLeadingFactor k r * ↑(-↑k • t).toCircle := by
              dsimp [c]
              ring
        _ = G (circlePoint r t) - truncate k J G (circlePoint r t) := by
              dsimp [c] at hGcircle hTcircle
              rw [hGcircle, hTcircle]
              ring
        _ = HJ (circlePoint r t) := by rfl
        _ = c * circleSeries k (hermiteCoeff k HJ) r t := by
              simpa [HJ, c] using hHcircle
    have hcancel :
        circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t =
          circleSeries k (hermiteCoeff k HJ) r t := by
      exact mul_left_cancel₀ hc_ne hmain
    calc
      truncCirclePoly k r J G t - circleSeries k (hermiteCoeff k G) r t
          = -(circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t) := by ring
      _ = -circleSeries k (hermiteCoeff k HJ) r t := by rw [hcancel]
  have hL2eq :
      circleL2Sq (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r) =
        circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) := by
    unfold circleL2Sq
    refine integral_congr_ae ?_
    filter_upwards with t
    have ht := congrFun hpoint t
    simp [ht]
  have hcanon :=
    circleSeries_l2_identity_canonical (k := k) (G := HJ) hHJ r hr
  have hcoeff :
      ∀ n,
        ‖hermiteCoeff k HJ n‖ ^ 2 * |qkn k n r| ^ 2 =
          if n < J + 1 then 0 else d n := by
    intro n
    rw [show hermiteCoeff k HJ n = if n < J + 1 then 0 else hermiteCoeff k G n by
      simpa [HJ] using hermiteCoeff_sub_truncate k J G n]
    by_cases hn : n < J + 1
    · simp [hn, d]
    · simp [hn, d]
  have hcanon' :
      circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) =
        ∑' n : ℕ, if n < J + 1 then 0 else d n := by
    rw [hcanon]
    congr 1
    ext n
    exact hcoeff n
  have hshift :
      (∑' n : ℕ, if n < J + 1 then 0 else d n) = ∑' n : ℕ, d (n + (J + 1)) := by
    let f : ℕ → ℝ := fun n => if n < J + 1 then 0 else d n
    change ∑' n, f n = ∑' n, d (n + (J + 1))
    have hkey : ∑' c, f (c + (J + 1)) = ∑' c, d (c + (J + 1)) := by
      apply tsum_congr
      intro c
      dsimp [f]
      have hnot : ¬ (c + (J + 1) < J + 1) := by
        exact Nat.not_lt_of_ge (Nat.le_add_left (J + 1) c)
      rw [if_neg hnot]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    have hsupp : Function.support f ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [f, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  have htail_small :
      ∑' n : ℕ, d (n + (J + 1)) < ε := by
    have hJ1 : J0 ≤ J + 1 := le_trans hJ (Nat.le_succ J)
    have hJtail := hJ0 (J + 1) hJ1
    rw [dist_zero_right] at hJtail
    have hnonneg : 0 ≤ ∑' n : ℕ, d (n + (J + 1)) := by
      exact tsum_nonneg fun n => by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hJtail
  calc
    circleL2Sq (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r)
        = circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) := hL2eq
    _ = ∑' n : ℕ, if n < J + 1 then 0 else d n := hcanon'
    _ = ∑' n : ℕ, d (n + (J + 1)) := hshift
    _ ≤ ε := le_of_lt htail_small

/-- Hermite expansions converge locally uniformly, hence are continuous. -/
theorem hermite_series_locally_uniform :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            Continuous G := by
  intro k G hG
  refine ⟨hermiteCoeff k G, hermiteCoeff_expansion hG, ?_⟩
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Use locally uniform convergence: for R = ‖z₀‖ + 1, ε/3, get J0
  set R := ‖z₀‖ + 1 with hR_def
  have hRpos : 0 < R := by positivity
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨J0, hJ0⟩ := truncate_locally_uniform hG R (ε / 3) hRpos hε3
  -- truncate k J0 G is continuous
  have hcont_trunc : Continuous (truncate k J0 G) := by
    unfold truncate finiteHermiteSum
    refine continuous_finsetSum _ (fun n _ => ?_)
    exact continuous_const.mul (continuous_Phi k n.1)
  -- By continuity of truncate at z₀, find δ₁ such that dist < ε/3
  have hcontAt : ContinuousAt (truncate k J0 G) z₀ := hcont_trunc.continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcontAt (ε / 3) hε3
  -- Also need ‖z‖ ≤ R, so take δ₂ = 1
  set δ := min δ₁ 1 with hδ_def
  have hδpos : 0 < δ := lt_min hδ₁pos one_pos
  refine ⟨δ, hδpos, fun {z} hz => ?_⟩
  have hz_R : ‖z‖ ≤ R := by
    have h1 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_le_insert' z z₀
    have h2 : ‖z - z₀‖ = dist z z₀ := by rw [dist_eq_norm]
    linarith [hz, min_le_right δ₁ 1]
  have hz₀_R : ‖z₀‖ ≤ R := by linarith
  have hclose_z : ‖truncate k J0 G z - G z‖ ≤ ε / 3 := hJ0 J0 (le_refl _) z hz_R
  have hclose_z₀ : ‖truncate k J0 G z₀ - G z₀‖ ≤ ε / 3 := hJ0 J0 (le_refl _) z₀ hz₀_R
  have hclose_trunc : dist (truncate k J0 G z) (truncate k J0 G z₀) < ε / 3 :=
    hδ₁ (lt_of_lt_of_le hz (min_le_left δ₁ 1))
  rw [dist_eq_norm] at hclose_trunc
  calc dist (G z) (G z₀)
      = ‖G z - G z₀‖ := dist_eq_norm (G z) (G z₀)
    _ = ‖(G z - truncate k J0 G z) + (truncate k J0 G z - truncate k J0 G z₀) +
          (truncate k J0 G z₀ - G z₀)‖ := by ring_nf
    _ ≤ ‖G z - truncate k J0 G z‖ + ‖truncate k J0 G z - truncate k J0 G z₀‖ +
          ‖truncate k J0 G z₀ - G z₀‖ := by
        linarith [norm_add_le (G z - truncate k J0 G z + (truncate k J0 G z - truncate k J0 G z₀))
            (truncate k J0 G z₀ - G z₀),
          norm_add_le (G z - truncate k J0 G z) (truncate k J0 G z - truncate k J0 G z₀)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : ‖G z - truncate k J0 G z‖ ≤ ε / 3 := by
          rw [show G z - truncate k J0 G z = -(truncate k J0 G z - G z) by ring]
          rw [norm_neg]
          exact hclose_z
        linarith
    _ = ε := by ring

/-- Every element of `H_k` is continuous. -/
theorem continuous_of_mem_Hk :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k → Continuous G := by
  intro k G hG
  obtain ⟨_, _, hcont⟩ := hermite_series_locally_uniform hG
  exact hcont

/-- Square-summable circle coefficients are absolutely summable. -/
private lemma summable_circleCoeff_norm_of_summable {k : ℕ} {h : ℕ → ℂ} {r : ℝ}
    (hh : Summable (fun n => ‖h n‖ ^ 2)) (hr : 0 < r) :
    Summable (fun n => ‖h n * (qkn k n r : ℂ)‖) := by
  have hqkn := summable_sq_qkn k hr
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ((hh.add hqkn).div_const 2)
  intro n
  have hmul : ‖h n * (qkn k n r : ℂ)‖ ≤ ‖h n‖ * |qkn k n r| := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hAMGM : ‖h n‖ * |qkn k n r| ≤ (‖h n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖h n‖ - |qkn k n r|)]
  exact hmul.trans hAMGM

/-- The explicit circle series of a square-summable coefficient sequence has the expected Fourier
    coefficients. -/
private theorem circleSeries_fourierCoeff_of_summable :
    ∀ {k : ℕ} {h : ℕ → ℂ},
      Summable (fun n => ‖h n‖ ^ 2) →
        ∀ {r : ℝ}, 0 < r →
          ∀ n : ℕ,
            fourierCoeff (circleSeries k h r) (n : ℤ) = h n * (qkn k n r : ℂ) := by
  intro k h hh r hr n
  let c : ℕ → ℂ := fun m => h m * (qkn k m r : ℂ)
  have hc_norm : Summable (fun m => ‖c m‖) := by
    simpa [c] using summable_circleCoeff_norm_of_summable (k := k) (h := h) hh hr
  have hInt :
      ∀ m : ℕ,
        Integrable
          (fun t : Circle => fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t))
          AddCircle.haarAddCircle := by
    intro m
    have hcm :
        Integrable (fun t : Circle => c m * fourier (m : ℤ) t) AddCircle.haarAddCircle := by
      simpa [smul_eq_mul, mul_comm] using
        ((MeasureTheory.integrable_const (c m)).fourier_smul (T := T) (m : ℤ))
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hcm.fourier_smul (T := T) (-(n : ℤ)))
  have hIntNorm :
      Summable
        (fun m : ℕ =>
          ∫ t : Circle, ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖
            ∂AddCircle.haarAddCircle) := by
    have hEq :
        (fun m : ℕ =>
          ∫ t : Circle, ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖
            ∂AddCircle.haarAddCircle) =
          fun m : ℕ => ‖c m‖ := by
      ext m
      calc
        ∫ t : Circle, ‖fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)‖
            ∂AddCircle.haarAddCircle
          = ∫ t : Circle, ‖c m‖ ∂AddCircle.haarAddCircle := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [norm_mul, norm_mul]
              simp [c]
        _ = ‖c m‖ := by simp
    rw [hEq]
    exact hc_norm
  have hsCircle : ∀ t : Circle, Summable (fun m : ℕ => c m * fourier (m : ℤ) t) := by
    intro t
    refine Summable.of_norm_bounded (g := fun m => ‖c m‖) hc_norm ?_
    intro m
    rw [norm_mul, show ‖fourier (m : ℤ) t‖ = 1 by
      simp, mul_one]
  calc
    fourierCoeff (circleSeries k h r) (n : ℤ)
      = ∑' m : ℕ,
          ∫ t : Circle, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)
            ∂AddCircle.haarAddCircle := by
            change
              ∫ t : Circle, fourier (-(n : ℤ)) t * circleSeries k h r t ∂AddCircle.haarAddCircle =
                ∑' m : ℕ,
                  ∫ t : Circle, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)
                    ∂AddCircle.haarAddCircle
            have hfun :
                (fun t : Circle => fourier (-(n : ℤ)) t * circleSeries k h r t) =
                  fun t : Circle => ∑' m : ℕ, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t) := by
              funext t
              unfold circleSeries
              rw [← tsum_mul_left]
            rw [hfun]
            rw [MeasureTheory.integral_tsum_of_summable_integral_norm hInt hIntNorm]
    _ = ∑' m : ℕ, if m = n then c m else 0 := by
          apply tsum_congr
          intro m
          calc
            ∫ t : Circle, fourier (-(n : ℤ)) t * (c m * fourier (m : ℤ) t)
                ∂AddCircle.haarAddCircle
              = fourierCoeff (fun t : Circle => c m * fourier (m : ℤ) t) (n : ℤ) := by
                  rfl
            _ = c m * fourierCoeff (fourier (m : ℤ)) (n : ℤ) := by
                  rw [fourierCoeff.const_mul]
            _ = if m = n then c m else 0 := by
                  by_cases hm : m = n
                  · subst m
                    have hfour : fourierCoeff (T := T) (fourier (n : ℤ)) (n : ℤ) = 1 := by
                      simpa [Pi.single_apply] using
                        congrFun (fourierCoeff_fourier (T := T) (n : ℤ)) (n : ℤ)
                    simp [hfour]
                  · have hfour : fourierCoeff (T := T) (fourier (m : ℤ)) (n : ℤ) = 0 := by
                      simpa [Pi.single_apply, hm] using
                        congrFun (fourierCoeff_fourier (T := T) (m : ℤ)) (n : ℤ)
                    simp [hm, hfour]
    _ = c n := by
          simp
    _ = h n * (qkn k n r : ℂ) := by
          simp [c]

/-- The explicit Hermite series of a square-summable coefficient sequence has the expected polar
    representation on circles. -/
private theorem hermiteSeries_circle_representation_of_summable :
    ∀ {k : ℕ} {h : ℕ → ℂ},
      Summable (fun n => ‖h n‖ ^ 2) →
        ∀ r : ℝ, 0 < r →
          ∀ t : Circle,
            hermiteSeries k h (circlePoint r t) =
              circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * circleSeries k h r t := by
  intro k h hh r hr t
  have hsCircle :
      Summable (fun n : ℕ => h n * (qkn k n r : ℂ) * fourier (n : ℤ) t) := by
    have hqkn := summable_sq_qkn k hr
    refine Summable.of_norm_bounded
      (g := fun n => (‖h n‖ ^ 2 + |qkn k n r| ^ 2) / 2)
      (((hh.add hqkn).div_const 2)) ?_
    intro n
    have hmul :
        ‖h n * (qkn k n r : ℂ) * fourier (n : ℤ) t‖ ≤ ‖h n‖ * |qkn k n r| := by
      calc
        ‖h n * (qkn k n r : ℂ) * fourier (n : ℤ) t‖
            ≤ ‖h n * (qkn k n r : ℂ)‖ * ‖fourier (n : ℤ) t‖ := by
              simp [mul_assoc]
        _ ≤ ‖h n‖ * |qkn k n r| := by
              rw [show ‖fourier (n : ℤ) t‖ = 1 by
                simp]
              simp [Complex.norm_real, Real.norm_eq_abs]
    have hAMGM : ‖h n‖ * |qkn k n r| ≤ (‖h n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖h n‖ - |qkn k n r|)]
    exact hmul.trans hAMGM
  unfold hermiteSeries circleSeries
  simp_rw [phi_polar (k := k) (r := r) hr t]
  let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
  have htsum :
      (∑' n : ℕ,
          h n *
            (circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
              ((qkn k n r : ℂ) * fourier (n : ℤ) t))) =
        ∑' n : ℕ, c * (h n * ((qkn k n r : ℂ) * fourier (n : ℤ) t)) := by
    apply tsum_congr
    intro n
    simp [c]
    ring
  rw [htsum, tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  ring

/-- The circle leading factor is nonzero on every positive circle. -/
private lemma circleLeadingFactor_fourier_ne_zero {k : ℕ} {r : ℝ} (hr : 0 < r) (t : Circle) :
    circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) ≠ 0 := by
  dsimp [circleLeadingFactor]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr <|
      div_ne_zero (pow_ne_zero k (ne_of_gt hr))
        (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0)
  · change ((fourier (-(k : ℤ)) t : ℂ)) ≠ 0
    intro h0
    have hnorm : ‖(fourier (-(k : ℤ)) t : ℂ)‖ = 1 := by
      simp
    rw [h0, norm_zero] at hnorm
    norm_num at hnorm

/-- A square-summable Hermite expansion is unique. -/
private theorem hermiteSeries_unique_of_summable :
    ∀ {k : ℕ} {a b : ℕ → ℂ},
      Summable (fun n => ‖a n‖ ^ 2) →
        Summable (fun n => ‖b n‖ ^ 2) →
          hermiteSeries k a = hermiteSeries k b →
            ∀ n, a n = b n := by
  intro k a b ha hb hEq n
  obtain ⟨R0, hR0, hnonzero⟩ := qkn_eventually_nonzero k n
  let r : ℝ := R0
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hR0
  have hcircle : circleSeries k a r = circleSeries k b r := by
    ext t
    let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
    have hc_ne : c ≠ 0 := by
      simpa [c] using circleLeadingFactor_fourier_ne_zero (k := k) hr t
    have ha_repr := hermiteSeries_circle_representation_of_summable (k := k) (h := a) ha r hr t
    have hb_repr := hermiteSeries_circle_representation_of_summable (k := k) (h := b) hb r hr t
    have hz := congrFun hEq (circlePoint r t)
    have hmain : c * circleSeries k a r t = c * circleSeries k b r t := by
      calc
        c * circleSeries k a r t = hermiteSeries k a (circlePoint r t) := by
          simpa [c] using ha_repr.symm
        _ = hermiteSeries k b (circlePoint r t) := by simpa using hz
        _ = c * circleSeries k b r t := by
          simpa [c] using hb_repr
    exact mul_left_cancel₀ hc_ne hmain
  have hfour := congrArg (fun f : Circle → ℂ => fourierCoeff f (n : ℤ)) hcircle
  have ha_coeff := circleSeries_fourierCoeff_of_summable (k := k) (h := a) ha hr n
  have hb_coeff := circleSeries_fourierCoeff_of_summable (k := k) (h := b) hb hr n
  have hq_ne_real : qkn k n r ≠ 0 := hnonzero r le_rfl
  have hq_ne : (qkn k n r : ℂ) ≠ 0 := by exact_mod_cast hq_ne_real
  have hcoeff_eq : a n * (qkn k n r : ℂ) = b n * (qkn k n r : ℂ) := by
    simpa [ha_coeff, hb_coeff] using hfour
  exact mul_right_cancel₀ hq_ne hcoeff_eq

/-- Fourier inversion: the canonical coefficients of a Hermite series recover
    the original coefficient sequence. -/
theorem hermiteCoeff_hermiteSeries :
    ∀ {k : ℕ} {G : ℂ → ℂ} (h : ℕ → ℂ),
      G ∈ Hk k →
      G = hermiteSeries k h →
      Summable (fun n => ‖h n‖ ^ 2) →
      (∀ n, hermiteCoeff k G n = h n) := by
  intro k G h hG hEq hh n
  have hcanon : hermiteSeries k (hermiteCoeff k G) = hermiteSeries k h := by
    calc
      hermiteSeries k (hermiteCoeff k G) = G := by
        symm
        exact hermiteCoeff_expansion (k := k) (G := G) hG
      _ = hermiteSeries k h := hEq
  exact hermiteSeries_unique_of_summable (k := k) (a := hermiteCoeff k G) (b := h)
    (summable_sq_hermiteCoeff hG) hh hcanon n

/-- A bounded square-summable Hermite series converges pointwise absolutely. -/
private lemma summable_hermite_eval_mul
    (k : ℕ) (h : ℕ → ℂ) (_hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) (z : ℂ) :
    Summable (fun n => h n * Phi k n z) := by
  obtain ⟨Cz, _, hCz⟩ := point_eval_bounded (k := k) z
  have hRK_partial : ∀ J : ℕ, ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 ≤ Cz ^ 2 := by
    intro J
    let a : Fin (J + 1) → ℂ := fun n => starRingEnd ℂ (Phi k n z)
    have hF_mem : finiteHermiteSum k a ∈ Hk k := finiteHermiteSum_mem_Hk k a
    have heval := hCz hF_mem
    have hNormSq :
        weightedNormSq (finiteHermiteSum k a) =
          ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 := by
      rw [finiteHermiteSum_normSq]
      congr 1
      ext n
      simp [a]
    set S := ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun n _ => sq_nonneg _
    have hWN : weightedNorm (finiteHermiteSum k a) = Real.sqrt S := by
      change Real.sqrt (weightedNormSq (finiteHermiteSum k a)) = _
      rw [hNormSq, hS_def]
    have hFz : finiteHermiteSum k a z = (S : ℂ) := by
      unfold finiteHermiteSum a
      calc
        ∑ n : Fin (J + 1), starRingEnd ℂ (Phi k n z) * Phi k n.1 z
            = ∑ n : Fin (J + 1), ((‖Phi k n z‖ ^ 2 : ℝ) : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                simpa [mul_comm] using Complex.mul_conj' (Phi k n z)
        _ = (S : ℂ) := by
              rw [hS_def]
              exact_mod_cast rfl
    have hSqLe : S ≤ Cz * Real.sqrt S := by
      have hFz_norm : ‖finiteHermiteSum k a z‖ ≤ Cz * weightedNorm (finiteHermiteSum k a) := heval
      rw [hFz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nn, hWN] at hFz_norm
      exact hFz_norm
    by_cases hS0 : S = 0
    · rw [hS0]
      positivity
    · have hSpos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
      have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
      have hsqrt_le : Real.sqrt S ≤ Cz := by
        have hsqS : Real.sqrt S * Real.sqrt S = S := by
          nlinarith [Real.sq_sqrt hS_nn]
        nlinarith [hSqLe, hsqS, hsqrt_pos]
      have hCz_nn : 0 ≤ Cz := le_trans (by simp [hS_def]) hsqrt_le
      nlinarith [hsqrt_le, hCz_nn]
  have hRK_range : ∀ J : ℕ, ∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2 ≤ Cz ^ 2 := by
    intro J
    by_cases hJ : J = 0
    · subst hJ
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ
      calc
        ∑ n ∈ Finset.range (J' + 1), ‖Phi k n z‖ ^ 2
            = ∑ n : Fin (J' + 1), ‖Phi k ↑n z‖ ^ 2 := by
                simpa using
                  (Fin.sum_univ_eq_sum_range
                    (f := fun n : ℕ => ‖Phi k n z‖ ^ 2)
                    (J' + 1)).symm
        _ ≤ Cz ^ 2 := hRK_partial J'
  have hPhi_sq_summable : Summable (fun n => ‖Phi k n z‖ ^ 2) :=
    summable_of_sum_range_le (fun n => sq_nonneg _) hRK_range
  refine Summable.of_norm_bounded (g := fun n => (‖h n‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2)
    ((hl2.add hPhi_sq_summable).div_const 2) ?_
  intro n
  have hmul :
      ‖h n * Phi k n z‖ ≤ ‖h n‖ * ‖Phi k n z‖ := by
    simp
  have hAMGM : ‖h n‖ * ‖Phi k n z‖ ≤ (‖h n‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖h n‖ - ‖Phi k n z‖)]
  exact hmul.trans hAMGM

/-- Pointwise convergence of finite Hermite sums to the explicit Hermite series. -/
private lemma finiteHermiteSum_tendsto_hermiteSeries
    (k : ℕ) (h : ℕ → ℂ) (hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) (z : ℂ) :
    Filter.Tendsto
      (fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) z)
      Filter.atTop
      (𝓝 (hermiteSeries k h z)) := by
  have hsumm := summable_hermite_eval_mul k h hbdd hl2 z
  have hconv :
      Filter.Tendsto (fun J : ℕ => ∑ n ∈ Finset.range J, h n * Phi k n z) Filter.atTop
        (𝓝 (hermiteSeries k h z)) := by
    simpa [hermiteSeries] using hsumm.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun J : ℕ => J + 1) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_add_atTop_nat 1)
  have hconv' := hconv.comp hshift
  have hconv'' :
      Filter.Tendsto (fun J : ℕ => ∑ n ∈ Finset.range (J + 1), h n * Phi k n z) Filter.atTop
        (𝓝 (hermiteSeries k h z)) := hconv'
  have hmain :
      Filter.Tendsto
        (fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) z)
        Filter.atTop
        (𝓝 (hermiteSeries k h z)) := by
    convert hconv'' using 1
    ext J
    change ∑ n : Fin (J + 1), h n.1 * Phi k n.1 z =
      ∑ n ∈ Finset.range (J + 1), h n * Phi k n z
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun n : ℕ => h n * Phi k n z)
        (J + 1))
  simpa using hmain

/-- The explicit Hermite series is a.e. strongly measurable. -/
private theorem hermiteSeries_aestronglyMeasurable
    (k : ℕ) (h : ℕ → ℂ) (hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) :
    AEStronglyMeasurable (hermiteSeries k h) volume := by
  apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (f := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1))
  · intro J
    unfold finiteHermiteSum
    exact
      (continuous_finsetSum _ (fun m _ =>
        continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall
      (finiteHermiteSum_tendsto_hermiteSeries k h hbdd hl2)

/-- Gaussian weight used to identify weighted Hermite norms with ordinary `L²`. -/
private def gaussianWeight (z : ℂ) : ℝ :=
  Real.exp (-(‖z‖ ^ 2) / 2) / Real.sqrt Real.pi

/-- Gaussian rescaling into the usual `L²` space. -/
private def gaussianScale (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ((gaussianWeight z : ℝ) : ℂ) * F z

private theorem gaussianWeight_nonneg (z : ℂ) : 0 ≤ gaussianWeight z := by
  unfold gaussianWeight
  positivity

private theorem gaussianWeight_sq (z : ℂ) :
    gaussianWeight z ^ 2 = (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
  unfold gaussianWeight
  have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := by
    rw [Real.sq_sqrt hpi]
  have hexp :
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2 = Real.exp (-‖z‖ ^ 2) := by
    calc
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2
          = Real.exp (-(‖z‖ ^ 2) / 2) * Real.exp (-(‖z‖ ^ 2) / 2) := by ring
      _ = Real.exp (-(‖z‖ ^ 2) / 2 + -(‖z‖ ^ 2) / 2) := by rw [← Real.exp_add]
      _ = Real.exp (-‖z‖ ^ 2) := by congr 1; ring
  rw [div_pow, hexp, hsqrt]
  field_simp [Real.pi_ne_zero]

private theorem continuous_gaussianWeight : Continuous gaussianWeight := by
  unfold gaussianWeight
  exact
    (Real.continuous_exp.comp
      ((continuous_neg.comp (continuous_norm.pow 2)).div_const 2)).div_const _

private theorem aestronglyMeasurable_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (gaussianScale F) volume := by
  exact (Complex.continuous_ofReal.comp continuous_gaussianWeight).aestronglyMeasurable.mul hF

private theorem weightedNormSq_eq_integral_sq_norm_gaussianScale
    (G : ℂ → ℂ) :
    weightedNormSq G = ∫ z : ℂ, ‖gaussianScale G z‖ ^ 2 := by
  unfold weightedNormSq HermiteLEAN.weightedNormSq
  have hEq :
      (fun z : ℂ => ‖gaussianScale G z‖ ^ 2) =
        fun z : ℂ => (1 / Real.pi) * (‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [show ‖gaussianScale G z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖G z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ring
  rw [hEq, MeasureTheory.integral_const_mul]

private theorem memLp_two_gaussianScale_of_integrable
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    MeasureTheory.MemLp (gaussianScale F) 2 volume := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact aestronglyMeasurable_gaussianScale hF
  · refine hInt.const_mul (1 / Real.pi) |>.congr ?_
    filter_upwards with z
    rw [show ‖gaussianScale F z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖F z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ring

private theorem weightedNorm_eq_lpNorm_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (_hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
  have hmeas : AEStronglyMeasurable (gaussianScale F) volume :=
    aestronglyMeasurable_gaussianScale hF
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := volume) (p := (2 : NNReal)) (f := gaussianScale F) htwo hmeas
  change weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) (↑(2 : NNReal)) volume
  rw [hlp]
  change weightedNorm F = (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)
  have hsq :
      (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) = weightedNormSq F := by
    simpa using (weightedNormSq_eq_integral_sq_norm_gaussianScale F).symm
  rw [hsq]
  unfold weightedNorm HermiteLEAN.weightedNorm
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem integrable_weightedCross_of_memLp
    (F G : ℂ → ℂ)
    (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume)
    (hG : MeasureTheory.MemLp (gaussianScale G) 2 volume) :
    Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  let FLp : MeasureTheory.Lp ℂ 2 volume := hF.toLp (gaussianScale F)
  let GLp : MeasureTheory.Lp ℂ 2 volume := hG.toLp (gaussianScale G)
  have hscaled :
      Integrable
        (fun z : ℂ =>
          ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))) := by
    have hint :
        Integrable (fun z : ℂ => inner ℂ (GLp z) (FLp z)) := by
      simpa [FLp, GLp] using MeasureTheory.L2.integrable_inner (𝕜 := ℂ) GLp FLp
    have hEq :
        (fun z : ℂ => inner ℂ (GLp z) (FLp z)) =ᵐ[volume]
          (fun z : ℂ => inner ℂ (gaussianScale G z) (gaussianScale F z)) := by
      filter_upwards [hG.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
      rw [hzG, hzF]
    have hint' :
        Integrable (fun z : ℂ => inner ℂ (gaussianScale G z) (gaussianScale F z)) := by
      exact hint.congr hEq
    convert hint' using 1
    ext z
    rw [RCLike.inner_apply']
    unfold gaussianScale
    have hgw :
        (((gaussianWeight z : ℝ) : ℂ) * ((gaussianWeight z : ℝ) : ℂ)) =
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      have hsq := gaussianWeight_sq z
      rw [sq] at hsq
      exact_mod_cast hsq
    rw [show (starRingEnd ℂ) (↑(gaussianWeight z) * G z) * (↑(gaussianWeight z) * F z) =
      ↑(gaussianWeight z) * ↑(gaussianWeight z) * (F z * (starRingEnd ℂ) (G z)) from by
        simp [map_mul]
        ring, hgw]
    push_cast
    ring
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  simpa [hpi_ne, mul_assoc, mul_left_comm, mul_comm] using hscaled.const_mul (Real.pi : ℂ)

private theorem weightedInner_eq_l2Inner
    (F G : ℂ → ℂ)
    (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume)
    (hG : MeasureTheory.MemLp (gaussianScale G) 2 volume) :
    weightedInner F G = @inner ℂ _ _ (hG.toLp (gaussianScale G)) (hF.toLp (gaussianScale F)) := by
  let FLp : MeasureTheory.Lp ℂ 2 volume := hF.toLp (gaussianScale F)
  let GLp : MeasureTheory.Lp ℂ 2 volume := hG.toLp (gaussianScale G)
  have hEq :
      (fun z : ℂ => inner ℂ (GLp z) (FLp z)) =ᵐ[volume]
        (fun z : ℂ =>
          ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))) := by
    filter_upwards [hG.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
    rw [hzG, hzF, RCLike.inner_apply']
    unfold gaussianScale
    have hgw :
        (((gaussianWeight z : ℝ) : ℂ) * ((gaussianWeight z : ℝ) : ℂ)) =
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      have hsq := gaussianWeight_sq z
      rw [sq] at hsq
      exact_mod_cast hsq
    rw [show (starRingEnd ℂ) (↑(gaussianWeight z) * G z) * (↑(gaussianWeight z) * F z) =
      ↑(gaussianWeight z) * ↑(gaussianWeight z) * (F z * (starRingEnd ℂ) (G z)) from by
        simp [map_mul]
        ring, hgw]
    push_cast
    ring
  calc
    weightedInner F G
        = ∫ z : ℂ, ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              unfold weightedInner HermiteLEAN.weightedInner
              exact
                (MeasureTheory.integral_const_mul
                  (r := (1 / Real.pi : ℂ))
                  (f := fun z : ℂ =>
                    F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))).symm
    _ = ∫ z : ℂ, inner ℂ (GLp z) (FLp z) := by
          symm
          exact integral_congr_ae hEq
    _ = @inner ℂ _ _ GLp FLp := by
          simpa [FLp, GLp] using (MeasureTheory.L2.inner_def (𝕜 := ℂ) GLp FLp).symm

private theorem weightedInner_norm_le_of_integrable
    {F G : ℂ → ℂ}
    (hFmeas : AEStronglyMeasurable F volume)
    (hGmeas : AEStronglyMeasurable G volume)
    (hFint : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)))
    (hGint : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    ‖weightedInner F G‖ ≤ weightedNorm F * weightedNorm G := by
  let hFmem := memLp_two_gaussianScale_of_integrable hFmeas hFint
  let hGmem := memLp_two_gaussianScale_of_integrable hGmeas hGint
  calc
    ‖weightedInner F G‖
        = ‖@inner ℂ _ _ (hGmem.toLp (gaussianScale G)) (hFmem.toLp (gaussianScale F))‖ := by
            rw [weightedInner_eq_l2Inner F G hFmem hGmem]
    _ ≤ ‖hGmem.toLp (gaussianScale G)‖ * ‖hFmem.toLp (gaussianScale F)‖ := norm_inner_le_norm _ _
    _ = MeasureTheory.lpNorm (gaussianScale G) 2 volume *
          MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
            rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp,
              ← MeasureTheory.toReal_eLpNorm hGmem.1, ← MeasureTheory.toReal_eLpNorm hFmem.1]
    _ = weightedNorm G * weightedNorm F := by
          rw [← weightedNorm_eq_lpNorm_gaussianScale hGmeas hGint,
            ← weightedNorm_eq_lpNorm_gaussianScale hFmeas hFint]
    _ = weightedNorm F * weightedNorm G := by ring

/-- The Hermite series `G = hermiteSeries k h` of a square-summable bounded
sequence has integrable squared Gaussian density.  Extracted from
`hermiteSeries_mem_Hk` to respect the proof size limit. -/
private lemma hermiteSeries_integrable_sq {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2))
    (hG_aesm : AEStronglyMeasurable (hermiteSeries k h) volume) :
    Integrable (fun z : ℂ => ‖hermiteSeries k h z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  set F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) with hFdef
  let t : ℕ → ℝ := fun n => ‖h n‖ ^ 2
  have hF_tendsto :
      Filter.Tendsto (fun J => weightedNormSq (F J))
        Filter.atTop (nhds (∑' n : ℕ, t n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) :=
      (hh.hasSum_iff_tendsto_nat).1 hh.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) := by
      exact hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    have hEqFun :
        (fun J => weightedNormSq (F J)) =
          (fun J => ∑ n ∈ Finset.range (J + 1), t n) := by
      funext J
      change weightedNormSq (finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)) =
        ∑ n ∈ Finset.range (J + 1), ‖h n‖ ^ 2
      rw [show ∑ n ∈ Finset.range (J + 1), ‖h n‖ ^ 2 =
          ∑ n : Fin (J + 1), ‖h n.1‖ ^ 2 from by rw [Finset.sum_range]]
      exact finiteHermiteSum_normSq (k := k) (a := fun n : Fin (J + 1) => h n.1)
    rw [hEqFun]
    exact hshift
  have hpi_F_tendsto :
      Filter.Tendsto (fun J => Real.pi * weightedNormSq (F J))
        Filter.atTop (nhds (Real.pi * ∑' n : ℕ, t n)) :=
    Filter.Tendsto.const_mul Real.pi hF_tendsto
  have hLiminfENNR :
      Filter.liminf
          (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (F J)))
          Filter.atTop =
        ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
    have hto :
        Filter.Tendsto
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (F J)))
            Filter.atTop
            (nhds (ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpi_F_tendsto
    exact hto.liminf_eq
  have hNonnegG : ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
    exact Filter.Eventually.of_forall (fun z => by positivity)
  have hLiminfPt :
      ∀ z : ℂ,
        Filter.liminf
            (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop =
          ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    intro z
    have hFz :
        Filter.Tendsto (fun J => F J z) Filter.atTop (nhds (G z)) := by
      simpa [F, G] using finiteHermiteSum_tendsto_hermiteSeries k h hbdd hh z
    have hreal :
        Filter.Tendsto (fun J => ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          Filter.atTop (nhds (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      have hsq :
          Filter.Tendsto (fun J => ‖F J z‖ ^ 2)
            Filter.atTop (nhds (‖G z‖ ^ 2)) := by
        exact (hFz.norm.pow 2)
      exact hsq.mul_const (rexp (-‖z‖ ^ 2))
    have hto :
        Filter.Tendsto
            (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop
            (nhds (ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hreal
    exact hto.liminf_eq
  have hFatou :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        Filter.liminf
            (fun J =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := by
    have hmeas :
        ∀ J : ℕ,
          AEMeasurable
            (fun z : ℂ =>
              ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))) volume := by
      intro J
      exact ((finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => h
          n.1)).1).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hfatou_raw := MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hmeas
    have hcongr :
        (∫⁻ z : ℂ,
            Filter.liminf
              (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop) =
          ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      apply MeasureTheory.lintegral_congr_ae
      exact Filter.Eventually.of_forall hLiminfPt
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ∫⁻ z : ℂ,
              Filter.liminf
                (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                Filter.atTop := hcongr.symm
      _ ≤ Filter.liminf
            (fun J =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := hfatou_raw
  have hLinEqF :
      ∀ J : ℕ,
        ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
          ENNReal.ofReal (Real.pi * weightedNormSq (F J)) := by
    intro J
    have hIntJ :
        Integrable (fun z : ℂ => ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
      (finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => h n.1)).1
    have hNonnegJ :
        ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
      exact Filter.Eventually.of_forall (fun z => by positivity)
    have hIntEq :
        ∫ z : ℂ, ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2) = Real.pi * weightedNormSq (F J) := by
      unfold F weightedNormSq HermiteLEAN.weightedNormSq
      field_simp [Real.pi_ne_zero]
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ENNReal.ofReal (∫ z : ℂ, ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntJ hNonnegJ
      _ = ENNReal.ofReal (Real.pi * weightedNormSq (F J)) := by rw [hIntEq]
  have hBound :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := by
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          ≤ Filter.liminf
              (fun J =>
                ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop := hFatou
      _ = Filter.liminf
            (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (F J)))
            Filter.atTop := by
              congr 1
              funext J
              exact hLinEqF J
      _ = ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) := hLiminfENNR
  have hlin_lt_top :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) < ⊤ := by
    exact lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
  have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
    (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
  have hf_aesm :
      AEStronglyMeasurable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
    (hG_aesm.norm.pow 2).mul hExp_aesm
  have hfi :
      MeasureTheory.HasFiniteIntegral (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hNonnegG).2 hlin_lt_top
  exact ⟨hf_aesm, hfi⟩

/-- Per-truncation lintegral bound used in the Fatou tail estimate for the
Hermite-series truncation difference.  Extracted from
`hermiteSeries_truncation_tail_bound` to respect the proof size limit. -/
private lemma hermiteSeries_truncation_lintegral_bound {k : ℕ} (h : ℕ → ℂ)
    (hh : Summable (fun n => ‖h n‖ ^ 2)) (J : ℕ) :
    ∀ N : ℕ,
      ∫⁻ z : ℂ, ENNReal.ofReal
          (‖finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1) z -
            finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal
          (Real.pi * ∑' m : ℕ, (if m < J + 1 then 0 else ‖h m‖ ^ 2)) := by
  let GN : ℕ → ℂ → ℂ := fun N =>
    finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1)
  let SJ : ℂ → ℂ := finiteHermiteSum k (fun m : Fin (J + 1) => h m.1)
  let s : ℕ → ℝ := fun m => if m < J + 1 then 0 else ‖h m‖ ^ 2
  change ∀ N : ℕ,
      ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m)
  intro N
  have hGN_mem : GN N ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin ((N + (J + 1)) +
      1) => h m.1)
  have hSJ' :
      truncate k J (GN N) = SJ := by
    ext z
    change ∑ m : Fin (J + 1), hermiteCoeff k (GN N) m.1 * Phi k m.1 z =
      ∑ m : Fin (J + 1), h m.1 * Phi k m.1 z
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm' : (m : ℕ) < (N + (J + 1)) + 1 := by omega
    rw [hermiteCoeff_finiteHermiteSum
      (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) => h q.1) m.1, dif_pos hm']
  have hDiff_mem : (fun z : ℂ => GN N z - SJ z) ∈ Hk k := by
    simpa [hSJ'] using sub_truncate_mem_Hk hGN_mem J
  have hParseval :
      weightedNormSq (fun z : ℂ => GN N z - SJ z) =
        ∑' m : ℕ, ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 := by
    exact hermiteCoeff_parseval hDiff_mem
  have hCoeff_bound :
      ∀ m : ℕ,
        ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 ≤ s m := by
    intro m
    have hcoeff :
        hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m =
          if h : m < J + 1 then 0 else hermiteCoeff k (GN N) m := by
      simpa [hSJ'] using hermiteCoeff_sub_truncate k J (GN N) m
    rw [hcoeff]
    split_ifs with hm
    · have hm' : m ≤ J := by omega
      simp [s, hm']
    · by_cases hlt : m < (N + (J + 1)) + 1
      · rw [hermiteCoeff_finiteHermiteSum (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) =>
          h q.1) m,
          dif_pos hlt]
        have hm' : ¬ m ≤ J := by omega
        simp [s, hm']
      · rw [hermiteCoeff_finiteHermiteSum (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) =>
          h q.1) m,
          dif_neg hlt]
        have hm' : ¬ m ≤ J := by omega
        simp [s, hm']
  have hs_summ : Summable s := by
    have hs_nonneg_term : ∀ m : ℕ, 0 ≤ s m := by
      intro m
      by_cases hm : m < J + 1
      · have hm' : m ≤ J := by omega
        simp [s, hm']
      · simp only [s, if_neg hm]
        positivity
    refine Summable.of_nonneg_of_le hs_nonneg_term ?_ hh
    intro m
    by_cases hm : m < J + 1
    · have hm' : m ≤ J := by omega
      simp [s, hm']
    · have hm' : ¬ m ≤ J := by omega
      simp [s, hm']
  have hsum_le :
      ∑' m : ℕ, ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 ≤
        ∑' m : ℕ, s m := by
    exact Summable.tsum_le_tsum hCoeff_bound (summable_sq_hermiteCoeff hDiff_mem) hs_summ
  have hNonnegN :
      0 ≤ Real.pi * weightedNormSq (fun z : ℂ => GN N z - SJ z) := by
    have hnorm_nonneg : 0 ≤ weightedNormSq (fun z : ℂ => GN N z - SJ z) := by
      rw [hParseval]
      exact tsum_nonneg fun m => sq_nonneg _
    exact mul_nonneg (le_of_lt Real.pi_pos) hnorm_nonneg
  have hs_nonneg : 0 ≤ Real.pi * ∑' m : ℕ, s m := by
    have hs_nonneg_term' : ∀ m : ℕ, 0 ≤ s m := by
      intro m
      by_cases hm : m < J + 1
      · have hm' : m ≤ J := by omega
        simp [s, hm']
      · simp only [s, if_neg hm]
        positivity
    exact mul_nonneg (le_of_lt Real.pi_pos) (tsum_nonneg hs_nonneg_term')
  have hmul_le :
      Real.pi * weightedNormSq (fun z : ℂ => GN N z - SJ z) ≤ Real.pi * ∑' m : ℕ, s m := by
    rw [hParseval]
    exact mul_le_mul_of_nonneg_left hsum_le (le_of_lt Real.pi_pos)
  have hIntN :
      Integrable (fun z : ℂ => ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    simpa [hSJ'] using (sub_truncate_mem_Hk hGN_mem J).1
  have hNonnegIntN :
      ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
    exact Filter.Eventually.of_forall (fun z => by positivity)
  have hIntEq :
      ∫ z : ℂ, ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
        Real.pi * weightedNormSq (fun z : ℂ => GN N z - SJ z) := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    field_simp [Real.pi_ne_zero]
  calc
    ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))
        = ENNReal.ofReal (∫ z : ℂ, ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntN hNonnegIntN
    _ = ENNReal.ofReal (Real.pi * weightedNormSq (fun z : ℂ => GN N z - SJ z)) := by rw
        [hIntEq]
    _ ≤ ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) := by
        exact ENNReal.ofReal_le_ofReal hmul_le

/-- The tail bound for the truncation difference in the Hermite-coefficient
recovery argument: `‖G − S_J‖²_w ≤ ∑_{m≥J+1} ‖hₘ‖²`.  Extracted from
`hermiteSeries_weightedInner_eq` to respect the proof size limit. -/
private lemma hermiteSeries_truncation_tail_bound {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2)) (J : ℕ)
    (hDiff_int : Integrable (fun z : ℂ =>
      ‖hermiteSeries k h z - finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z‖ ^ 2 *
        rexp (-‖z‖ ^ 2))) :
    weightedNormSq
        (fun z : ℂ => hermiteSeries k h z -
          finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z) ≤
      ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  set SJ : ℂ → ℂ := finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) with hSJdef
  let s : ℕ → ℝ := fun m => if m < J + 1 then 0 else ‖h m‖ ^ 2
  let GN : ℕ → ℂ → ℂ := fun N =>
    finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1)
  have hPoint :
      ∀ z : ℂ,
        Filter.Tendsto
          (fun N => GN N z - SJ z)
          Filter.atTop
          (nhds (G z - SJ z)) := by
    intro z
    have hshift : Filter.Tendsto (fun N : ℕ => N + (J + 1)) Filter.atTop Filter.atTop := by
      simpa [Nat.add_assoc] using (Filter.tendsto_add_atTop_nat (J + 1))
    have hGN :
        Filter.Tendsto (fun N => GN N z) Filter.atTop (nhds (G z)) :=
      (finiteHermiteSum_tendsto_hermiteSeries k h hbdd hh z).comp hshift
    exact hGN.sub tendsto_const_nhds
  have hFatou :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        Filter.liminf
          (fun N =>
            ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
          Filter.atTop := by
    have hmeas :
        ∀ N : ℕ,
          AEMeasurable
            (fun z : ℂ =>
              ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))) volume := by
      intro N
      have hGN_mem : GN N ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin ((N + (J + 1))
          + 1) => h m.1)
      have hGN_int : Integrable (fun z : ℂ => ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        have hSJ' :
            truncate k J (GN N) = SJ := by
          ext z
          change ∑ m : Fin (J + 1), hermiteCoeff k (GN N) m.1 * Phi k m.1 z =
            ∑ m : Fin (J + 1), h m.1 * Phi k m.1 z
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hm' : (m : ℕ) < (N + (J + 1)) + 1 := by omega
          rw [hermiteCoeff_finiteHermiteSum
            (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) => h q.1) m.1, dif_pos hm']
        have hsub := (sub_truncate_mem_Hk hGN_mem J).1
        simpa [hSJ'] using hsub
      exact hGN_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hfatou_raw := MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hmeas
    have hLiminfPt :
        ∀ z : ℂ,
          Filter.liminf
              (fun N => ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop =
            ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      intro z
      have hreal :
          Filter.Tendsto (fun N => ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))
            Filter.atTop
            (nhds (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
        have hsq :
            Filter.Tendsto (fun N => ‖GN N z - SJ z‖ ^ 2)
              Filter.atTop
              (nhds (‖G z - SJ z‖ ^ 2)) := by
          exact ((hPoint z).norm.pow 2)
        exact hsq.mul_const (rexp (-‖z‖ ^ 2))
      have hto :
          Filter.Tendsto
              (fun N => ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop
              (nhds (ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp hreal
      exact hto.liminf_eq
    have hcongr :
        (∫⁻ z : ℂ,
            Filter.liminf
              (fun N => ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop) =
          ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      apply MeasureTheory.lintegral_congr_ae
      exact Filter.Eventually.of_forall hLiminfPt
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          = ∫⁻ z : ℂ,
              Filter.liminf
                (fun N => ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
                Filter.atTop := hcongr.symm
      _ ≤ Filter.liminf
            (fun N =>
              ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := hfatou_raw
  have hLinEq :
      ∀ N : ℕ,
        ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
          ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) :=
    hermiteSeries_truncation_lintegral_bound h hh J
  have hBound :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) := by
    have hbounded :
        Filter.IsBoundedUnder (fun x y => x ≥ y) Filter.atTop
          (fun N =>
            ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      refine ⟨0, Filter.Eventually.of_forall ?_⟩
      intro N
      exact zero_le
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          ≤ Filter.liminf
              (fun N =>
                ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop := hFatou
      _ ≤ ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) := by
          apply Filter.liminf_le_of_le hbounded
          intro b hb
          rw [Filter.eventually_atTop] at hb
          obtain ⟨N, hN⟩ := hb
          exact le_trans (hN N le_rfl) (hLinEq N)
  have htail_nonneg : 0 ≤ ∑' m : ℕ, s m := by
    have hs_nonneg_term : ∀ m : ℕ, 0 ≤ s m := by
      intro m
      by_cases hm : m < J + 1
      · have hm' : m ≤ J := by omega
        simp [s, hm']
      · simp only [s, if_neg hm]
        positivity
    exact tsum_nonneg hs_nonneg_term
  have hShift :
      (∑' m : ℕ, s m) = ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 := by
    have hkey :
        ∑' c : ℕ, s (c + (J + 1)) = ∑' c : ℕ, ‖h (c + (J + 1))‖ ^ 2 := by
      apply tsum_congr
      intro c
      dsimp [s]
      have hnot : ¬ (c + (J + 1) < J + 1) := by omega
      rw [if_neg hnot]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    have hsupp : Function.support s ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [s, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  have hNonnegDiff :
      ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
    exact Filter.Eventually.of_forall (fun z => by positivity)
  have hIntEq' :
      ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
        Real.pi * weightedNormSq (fun z : ℂ => G z - SJ z) := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    field_simp [Real.pi_ne_zero]
  have hlin_lt_top_diff :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) < ⊤ := by
    exact lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
  have hInt_le :
      ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) ≤
        Real.pi * ∑' m : ℕ, s m := by
    have hto :
        (∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))).toReal ≤
          (ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m)).toReal :=
      (ENNReal.toReal_le_toReal hlin_lt_top_diff.ne (by simp)).2 hBound
    have hleft :
        (∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))).toReal =
          ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
      have hint_nonneg :
          0 ≤ ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
        exact MeasureTheory.integral_nonneg (fun z => by positivity)
      have hlin :=
        congrArg ENNReal.toReal
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hDiff_int hNonnegDiff).symm
      simpa [ENNReal.toReal_ofReal hint_nonneg] using hlin
    calc
      ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)
          = (∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))).toReal := by
              rw [hleft]
      _ ≤ (ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m)).toReal := hto
      _ = Real.pi * ∑' m : ℕ, s m := by
            rw [ENNReal.toReal_ofReal (mul_nonneg (le_of_lt Real.pi_pos) htail_nonneg)]
  have hmul_le :
      Real.pi * weightedNormSq (fun z : ℂ => G z - SJ z) ≤
        Real.pi * ∑' m : ℕ, s m := by
    rwa [hIntEq'] at hInt_le
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hfinal :
      weightedNormSq (fun z : ℂ => G z - SJ z) ≤ ∑' m : ℕ, s m := by
    nlinarith [hpi_pos, hmul_le]
  simpa [hShift] using hfinal

/-- The Hermite coefficients of the series `G = hermiteSeries k h` recover the
sequence `h`: `⟨G, Φ_{k,n}⟩ = h n`.  Extracted from `hermiteSeries_mem_Hk` to
respect the proof size limit. -/
private lemma hermiteSeries_weightedInner_eq {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2))
    (hG_aesm : AEStronglyMeasurable (hermiteSeries k h) volume)
    (hIntG : Integrable (fun z : ℂ => ‖hermiteSeries k h z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    ∀ n : ℕ, weightedInner (hermiteSeries k h) (Phi k n) = h n := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  let F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)
  intro n
  have hPhi_normSq : weightedNormSq (Phi k n) = 1 := by
    rw [weightedNormSq_eq_re_weightedInner, phi_orthonormal]
    simp
  have hPhi_norm : weightedNorm (Phi k n) = 1 := by
    unfold weightedNorm HermiteLEAN.weightedNorm
    change Real.sqrt (weightedNormSq (Phi k n)) = 1
    rw [hPhi_normSq, Real.sqrt_one]
  have hPhi_aesm : AEStronglyMeasurable (Phi k n) volume :=
    (continuous_Phi k n).aestronglyMeasurable
  have hPhi_int : Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    integrable_weightedDiag k n
  have htail := tendsto_sum_nat_add (fun m => ‖h m‖ ^ 2)
  rw [Metric.tendsto_atTop] at htail
  by_contra hneq
  have hdist_pos : 0 < ‖weightedInner G (Phi k n) - h n‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  obtain ⟨J0, hJ0⟩ := htail ((‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2) (by positivity)
  let J := max J0 n
  have hJ_ge : J0 ≤ J := le_max_left _ _
  have hnJ : n < J + 1 := by
    have : n ≤ J := le_max_right _ _
    omega
  have htail_small :
      ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 <
        (‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2 := by
    have hJtail := hJ0 (J + 1) (by omega)
    rw [dist_zero_right] at hJtail
    have hnonneg : 0 ≤ ∑' m : ℕ, ‖h (m + J + 1)‖ ^ 2 := by
      exact tsum_nonneg fun m => sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using (abs_lt.mp hJtail).2
  let SJ : ℂ → ℂ := F J
  have hSJ_mem : SJ ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin (J + 1) => h m.1)
  have hSJ_int : Integrable (fun z : ℂ => ‖SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := hSJ_mem.1
  have hSJ_aesm : AEStronglyMeasurable SJ volume := by
    unfold SJ F finiteHermiteSum
    exact
      (continuous_finsetSum _ (fun m _ =>
        continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
  have hDiff_int :
      Integrable (fun z : ℂ => ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    have hbound :
        Integrable
          (fun z : ℂ =>
            (2 : ℝ) *
              (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
                ‖SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      simpa [two_mul, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using (hIntG.add hSJ_int).const_mul (2 : ℝ)
    have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
      (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
    have hmeas :
        AEStronglyMeasurable
          (fun z : ℂ => ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume := by
      exact ((hG_aesm.sub hSJ_aesm).norm.pow 2).mul hExp_aesm
    refine MeasureTheory.Integrable.mono' hbound hmeas ?_
    filter_upwards with z
    have hsub : ‖G z - SJ z‖ ≤ ‖G z‖ + ‖SJ z‖ := norm_sub_le _ _
    have hexp : 0 ≤ rexp (-‖z‖ ^ 2) := exp_nonneg _
    have hsq :
        ‖G z - SJ z‖ ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖SJ z‖ ^ 2) := by
      have hsubsq :
          ‖G z - SJ z‖ ^ 2 ≤ (‖G z‖ + ‖SJ z‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
      have hab :
          (‖G z‖ + ‖SJ z‖) ^ 2 ≤ 2 * (‖G z‖ ^ 2 + ‖SJ z‖ ^ 2) := by
        nlinarith [sq_nonneg (‖G z‖ - ‖SJ z‖)]
      exact le_trans hsubsq hab
    have hmul :
        ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) ≤
          (2 * (‖G z‖ ^ 2 + ‖SJ z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hsq hexp
    have hnonneg :
        0 ≤ ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by positivity
    rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)
          ≤ (2 * (‖G z‖ ^ 2 + ‖SJ z‖ ^ 2)) * rexp (-‖z‖ ^ 2) := hmul
      _ = (2 : ℝ) *
            (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) +
              ‖SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by ring
  have hDiff_sq_le :
      weightedNormSq (fun z : ℂ => G z - SJ z) ≤
        ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 :=
    hermiteSeries_truncation_tail_bound h hbdd hh J hDiff_int
  have hSJ_coeff : weightedInner SJ (Phi k n) = h n := by
    rw [weightedInner_finiteHermiteSum_coeff]
    simp [hnJ]
  have hG_cross :
      Integrable
        (fun z : ℂ => G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    let hG_mem := memLp_two_gaussianScale_of_integrable hG_aesm hIntG
    let hPhi_mem := memLp_two_gaussianScale_of_integrable hPhi_aesm hPhi_int
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      integrable_weightedCross_of_memLp G (Phi k n) hG_mem hPhi_mem
  have hSJ_cross :
      Integrable
        (fun z : ℂ => SJ z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    simpa [SJ, F, mul_assoc, mul_left_comm, mul_comm] using
      integrable_finiteHermiteSum_weightedCross (k := k) (a := fun m : Fin (J + 1) => h m.1) (n
          := n)
  have hDiff_cross :
      Integrable
        (fun z : ℂ =>
          (G z - SJ z) * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    refine (hG_cross.sub hSJ_cross).congr ?_
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  have hsplit :
      weightedInner G (Phi k n) =
        weightedInner SJ (Phi k n) + weightedInner (fun z : ℂ => G z - SJ z) (Phi k n) := by
    have hadd := weightedInner_add_left_of_integrable SJ (fun z : ℂ => G z - SJ z) (Phi k n)
      hSJ_cross hDiff_cross
    calc
      weightedInner G (Phi k n)
          = weightedInner (fun z : ℂ => SJ z + (G z - SJ z)) (Phi k n) := by
              congr 1
              funext z
              ring
      _ = weightedInner SJ (Phi k n) +
            weightedInner (fun z : ℂ => G z - SJ z) (Phi k n) := hadd
  have hsmall :
      ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ <
        ‖weightedInner G (Phi k n) - h n‖ := by
    have hDiff_nonneg : 0 ≤ weightedNormSq (fun z : ℂ => G z - SJ z) := by
      have hpiinv_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
      have hint_nonneg : 0 ≤ ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) := by
        exact MeasureTheory.integral_nonneg (fun z => by positivity)
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      exact mul_nonneg hpiinv_nonneg hint_nonneg
    have hnorm_le :
        ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ ≤
          weightedNorm (fun z : ℂ => G z - SJ z) * weightedNorm (Phi k n) := by
      exact weightedInner_norm_le_of_integrable
        (hFmeas := hG_aesm.sub hSJ_aesm)
        (hGmeas := hPhi_aesm)
        (hFint := hDiff_int)
        (hGint := hPhi_int)
    have hDiff_small_sq :
        weightedNormSq (fun z : ℂ => G z - SJ z) <
          (‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2 := by
      exact lt_of_le_of_lt hDiff_sq_le htail_small
    have hDiff_small :
        weightedNorm (fun z : ℂ => G z - SJ z) <
          ‖weightedInner G (Phi k n) - h n‖ / 2 := by
      unfold weightedNorm HermiteLEAN.weightedNorm
      have hhalf_nonneg : 0 ≤ ‖weightedInner G (Phi k n) - h n‖ / 2 := by positivity
      rw [← Real.sqrt_sq hhalf_nonneg]
      exact Real.sqrt_lt_sqrt hDiff_nonneg hDiff_small_sq
    have : ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ <
        ‖weightedInner G (Phi k n) - h n‖ / 2 := by
      have hnorm_le' :
          ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ ≤
            weightedNorm (fun z : ℂ => G z - SJ z) := by
        simpa [hPhi_norm] using hnorm_le
      exact lt_of_le_of_lt hnorm_le' hDiff_small
    linarith
  have hdiff_eq :
      weightedInner G (Phi k n) - h n =
        weightedInner (fun z : ℂ => G z - SJ z) (Phi k n) := by
    rw [hsplit, hSJ_coeff]
    ring
  have : ‖weightedInner G (Phi k n) - h n‖ <
      ‖weightedInner G (Phi k n) - h n‖ := by
    nth_rewrite 1 [hdiff_eq]
    exact hsmall
  exact lt_irrefl _ this

/-- A square-summable Hermite series defines an element of `H_k`. -/
theorem hermiteSeries_mem_Hk :
    ∀ {k : ℕ} (h : ℕ → ℂ),
      (∀ n, ‖h n‖ ≤ 1) →
      Summable (fun n => ‖h n‖ ^ 2) →
      hermiteSeries k h ∈ Hk k := by
  intro k h hbdd hh
  let G : ℂ → ℂ := hermiteSeries k h
  let F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)
  have hG_aesm : AEStronglyMeasurable G volume :=
    hermiteSeries_aestronglyMeasurable k h hbdd hh
  have hIntG :
      Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    hermiteSeries_integrable_sq h hbdd hh hG_aesm
  have hcoeff :
      ∀ n : ℕ, weightedInner G (Phi k n) = h n :=
    hermiteSeries_weightedInner_eq h hbdd hh hG_aesm hIntG
  refine ⟨hIntG, ?_⟩
  intro z
  have hs : Summable (fun n => h n * Phi k n z) := summable_hermite_eval_mul k h hbdd hh z
  have hsum : HasSum (fun n => h n * Phi k n z) (G z) := by
    simpa [G, hermiteSeries] using hs.hasSum
  have hterm :
      (fun n => weightedInner G (Phi k n) * Phi k n z) =
        (fun n => h n * Phi k n z) := by
    funext n
    rw [hcoeff n]
  simpa [G, hterm] using hsum

/-- The modulus defect is bounded by the perturbation norm. -/
theorem modulusDefect_le_norm (F0 G : ℂ → ℂ) (z : ℂ) :
    modulusDefect F0 G z ≤ ‖G z‖ := by
  have h := abs_norm_sub_norm_le (F0 z + G z) (F0 z)
  rw [add_sub_cancel_left] at h
  exact h

end HermitekLEAN
