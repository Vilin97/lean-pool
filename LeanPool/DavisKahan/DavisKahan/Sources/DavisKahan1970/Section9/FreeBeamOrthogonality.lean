/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import LeanPool.DavisKahan.ForTauCeti.Analysis.Calculus.FourthOrderGreensIdentity

/-!
# Free-beam eigenmodes at distinct frequencies are `L²`-orthogonal

Davis--Kahan 1970 Section 9's numerical example is stated against a self-adjoint
fourth-derivative operator on `L²(0,1)` with free-end boundary conditions.  The
classical side of that operator is already here — `FreeBeamCharacteristic.lean`
builds the four-parameter mode `u'''' = β⁴ u`, its derivative chain, and the
free-end conditions — and `ForTauCeti`'s
`integral_fourthDeriv_mul_eq_mul_fourthDeriv` supplies the symmetry of `d⁴/dx⁴`
under those conditions.

This module joins the two and gets the first genuinely *spectral* consequence:
modes at frequencies with `β⁴ ≠ γ⁴` are orthogonal in `L²(0,1)`.  That is the
statement an eigenbasis is built from, and it is what makes the operator's
spectral decomposition — and hence Section 9's angle quantities — meaningful
rather than nominal.

The argument is the classical one, in one line once the symmetry is available:
Green's identity turns `∫ v u''''` into `∫ u v''''`, the eigenvalue equation
turns those into `β⁴ ∫ v u` and `γ⁴ ∫ u v`, and `β⁴ ≠ γ⁴` forces the common
integral to vanish.

## What this does *not* yet do

It does not build the operator.  Remaining for that: completeness of the mode
family in `L²(0,1)`, and the passage from the classical modes to a densely
defined self-adjoint operator.  Both are open; this is the brick they rest on.
-/

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

noncomputable section

/-! ### Continuity of the mode and its derivative chain -/

/-- The classical mode is continuous. -/
theorem continuous_mode (beta a b c d : ℝ) : Continuous (mode beta a b c d) := by
  unfold mode; fun_prop

/-- The first derivative is continuous. -/
theorem continuous_modeD1 (beta a b c d : ℝ) : Continuous (modeD1 beta a b c d) := by
  unfold modeD1; fun_prop

/-- The second derivative is continuous. -/
theorem continuous_modeD2 (beta a b c d : ℝ) : Continuous (modeD2 beta a b c d) := by
  unfold modeD2; fun_prop

/-- The third derivative is continuous. -/
theorem continuous_modeD3 (beta a b c d : ℝ) : Continuous (modeD3 beta a b c d) := by
  unfold modeD3; fun_prop

/-- The fourth derivative is continuous. -/
theorem continuous_modeD4 (beta a b c d : ℝ) : Continuous (modeD4 beta a b c d) := by
  unfold modeD4
  exact continuous_const.mul (continuous_mode beta a b c d)

/-! ### Orthogonality -/

/-- **Free-beam modes at distinct frequencies are `L²(0,1)`-orthogonal.**

Green's identity moves the fourth derivative across the pairing; the eigenvalue
equation `u'''' = β⁴ u` turns both sides into multiples of the same integral;
and `β⁴ ≠ γ⁴` forces it to vanish.

This is the first spectral fact about the free-beam operator that does not
depend on constructing the operator itself. -/
theorem integral_mode_mul_eq_zero_of_ne
    {beta a b c d gamma a' b' c' d' : ℝ}
    (hu : FreeBoundary beta a b c d) (hv : FreeBoundary gamma a' b' c' d')
    (hne : beta ^ 4 ≠ gamma ^ 4) :
    ∫ x in (0 : ℝ)..1, mode beta a b c d x * mode gamma a' b' c' d' x = 0 := by
  set u := mode beta a b c d with hudef
  set v := mode gamma a' b' c' d' with hvdef
  obtain ⟨hu2zero, hu3zero, hu2one, hu3one⟩ := hu
  obtain ⟨hv2zero, hv3zero, hv2one, hv3one⟩ := hv
  -- Green's identity for the two modes.
  have hgreen := TauCeti.integral_fourthDeriv_mul_eq_mul_fourthDeriv
    (u := u) (u1 := modeD1 beta a b c d) (u2 := modeD2 beta a b c d)
    (u3 := modeD3 beta a b c d) (u4 := modeD4 beta a b c d)
    (v := v) (v1 := modeD1 gamma a' b' c' d') (v2 := modeD2 gamma a' b' c' d')
    (v3 := modeD3 gamma a' b' c' d') (v4 := modeD4 gamma a' b' c' d')
    (continuous_mode _ _ _ _ _) (continuous_modeD1 _ _ _ _ _)
    (continuous_modeD2 _ _ _ _ _) (continuous_modeD3 _ _ _ _ _)
    (continuous_modeD4 _ _ _ _ _)
    (continuous_mode _ _ _ _ _) (continuous_modeD1 _ _ _ _ _)
    (continuous_modeD2 _ _ _ _ _) (continuous_modeD3 _ _ _ _ _)
    (continuous_modeD4 _ _ _ _ _)
    (hasDerivAt_mode beta a b c d) (hasDerivAt_modeD1 beta a b c d)
    (hasDerivAt_modeD2 beta a b c d) (hasDerivAt_modeD3 beta a b c d)
    (hasDerivAt_mode gamma a' b' c' d') (hasDerivAt_modeD1 gamma a' b' c' d')
    (hasDerivAt_modeD2 gamma a' b' c' d') (hasDerivAt_modeD3 gamma a' b' c' d')
    hu2zero hu2one hu3zero hu3one hv2zero hv2one hv3zero hv3one
  -- Replace the fourth derivatives by their eigenvalue multiples.
  have hu4 : ∀ x, modeD4 beta a b c d x = beta ^ 4 * u x := fun x => rfl
  have hv4 : ∀ x, modeD4 gamma a' b' c' d' x = gamma ^ 4 * v x := fun x => rfl
  simp only [hu4, hv4] at hgreen
  -- Both sides are scalar multiples of `∫ u v`.
  have hleft : ∫ x in (0 : ℝ)..1, v x * (beta ^ 4 * u x) =
      beta ^ 4 * ∫ x in (0 : ℝ)..1, u x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring
  have hright : ∫ x in (0 : ℝ)..1, u x * (gamma ^ 4 * v x) =
      gamma ^ 4 * ∫ x in (0 : ℝ)..1, u x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring
  rw [hleft, hright] at hgreen
  have hfactor : (beta ^ 4 - gamma ^ 4) * ∫ x in (0 : ℝ)..1, u x * v x = 0 := by
    linarith [hgreen]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-! ### The Rayleigh identity and positivity -/

/-- **Rayleigh identity for a free-end mode**: `β⁴ ∫ u² = ∫ (u'')²`.

The quadratic form of the fourth-derivative operator evaluated on an
eigenfunction.  Read left to right it computes the form; read right to left it
says the eigenvalue is a ratio of two squares, which is where positivity comes
from. -/
theorem beta_pow_four_mul_integral_mode_sq
    {beta a b c d : ℝ} (hu : FreeBoundary beta a b c d) :
    beta ^ 4 * ∫ x in (0 : ℝ)..1, mode beta a b c d x ^ 2 =
      ∫ x in (0 : ℝ)..1, modeD2 beta a b c d x ^ 2 := by
  obtain ⟨hu2zero, hu3zero, hu2one, hu3one⟩ := hu
  have h := TauCeti.integral_mul_fourthDeriv_self_eq_integral_secondDeriv_sq
    (continuous_mode beta a b c d) (continuous_modeD1 beta a b c d)
    (continuous_modeD2 beta a b c d) (continuous_modeD3 beta a b c d)
    (continuous_modeD4 beta a b c d)
    (hasDerivAt_mode beta a b c d) (hasDerivAt_modeD1 beta a b c d)
    (hasDerivAt_modeD2 beta a b c d) (hasDerivAt_modeD3 beta a b c d)
    hu2zero hu2one hu3zero hu3one
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1 with x
  show beta ^ 4 * mode beta a b c d x ^ 2 =
    mode beta a b c d x * modeD4 beta a b c d x
  simp only [modeD4]
  ring

/-- **The free-beam operator is nonnegative on its free-end domain.**

Immediate from the Rayleigh identity, since the right-hand side integrates a
square.  This is the positivity a Friedrichs-style construction of the
self-adjoint realisation needs, and it is also why the paper's eigenvalues
`α₁ ≤ α₂ ≤ …` are indexed as nonnegative reals. -/
theorem nonneg_beta_pow_four_mul_integral_mode_sq
    {beta a b c d : ℝ} (hu : FreeBoundary beta a b c d) :
    0 ≤ beta ^ 4 * ∫ x in (0 : ℝ)..1, mode beta a b c d x ^ 2 := by
  rw [beta_pow_four_mul_integral_mode_sq hu]
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro x _
  positivity

/-! ### Normalization

Orthogonality is only half of an eigenbasis; the other half is that a nontrivial
mode has positive norm, so it can be normalized.  That is not automatic from
`FreeBoundary`, which the zero mode also satisfies. -/

/-- **A mode that is nonzero somewhere inside `(0,1)` has positive `L²` norm.**

Continuity makes `u² > 0` on a whole open neighbourhood of the witness, and an
open nonempty subset of `(0,1)` has positive Lebesgue measure; the integral
criterion then applies.  Positivity of `∫ u²` is what lets the Rayleigh identity
be read as `β⁴ = ∫(u'')² / ∫u²`, and what makes an orthogonal family of modes
normalizable. -/
theorem integral_mode_sq_pos {beta a b c d x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) (hne : mode beta a b c d x₀ ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, mode beta a b c d x ^ 2 := by
  have hcont : Continuous fun x => mode beta a b c d x ^ 2 :=
    (continuous_mode beta a b c d).pow 2
  have hnonneg : ∀ x, 0 ≤ mode beta a b c d x ^ 2 := fun x => sq_nonneg _
  have hfi : IntervalIntegrable (fun x => mode beta a b c d x ^ 2) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg) hfi]
  refine ⟨by norm_num, ?_⟩
  -- The open set where `u² > 0`, intersected with `(0,1)`, is a nonempty open subset.
  set S : Set ℝ := {x | 0 < mode beta a b c d x ^ 2} ∩ Set.Ioo (0 : ℝ) 1 with hSdef
  have hSopen : IsOpen S :=
    (isOpen_lt continuous_const hcont).inter isOpen_Ioo
  have hpos0 : 0 < mode beta a b c d x₀ ^ 2 := pow_two_pos_of_ne_zero hne
  have hSmem : x₀ ∈ S := ⟨hpos0, hx₀⟩
  have hSpos : 0 < MeasureTheory.volume S := hSopen.measure_pos _ ⟨x₀, hSmem⟩
  refine lt_of_lt_of_le hSpos (MeasureTheory.measure_mono ?_)
  rintro x ⟨hxpos, hxmem⟩
  exact ⟨ne_of_gt hxpos, Set.Ioo_subset_Ioc_self hxmem⟩

end

end FreeBeam
end DavisKahan
end TauCeti
