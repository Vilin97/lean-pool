/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection
import LeanPool.DavisKahan.DavisKahan.Sylvester.FiniteBlockReconstruction
import LeanPool.DavisKahan.ForTauCeti.Analysis.Fourier.HaagerupZsido.Kernel
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Fourier Semigroup -/


open TauCeti.DavisKahan.Sylvester

/-!
# Fourier and semigroup formulas for bounded Sylvester equations

This file supplies the analytic layer used by the infinite-dimensional
Sylvester development.  The oscillatory formula is necessarily complex: the
phase `exp (i t A)` has no same-space real-linear analogue.  Real Hilbert-space
consequences are obtained after complexification, not by assigning a fake
imaginary unit to `R`.

The reciprocal multiplier is the scaled Haagerup--Zsido kernel

`mu_d(t) = reciprocalKernel (d t)`.

With the Fourier convention used in this repository it satisfies

`integral mu_d(t) exp(i t x) dt = 1/x`,  when `d <= |x|`,

and its exact mass is `pi/(2 d)`.  The factor `pi/2` is essential; an `L1`
mass of `1/d` would assert a false general separated-spectrum estimate.

The operator reconstruction is proved by finite spectral step approximation.
Each self-adjoint operator is approximated in norm by a finite sum of its own
spectral projections, with representatives chosen from the original spectrum.
Consequently the cross-gap is preserved exactly.  The formula is first checked
block by block for the finite spectral sums and then passed to the limit by
Bochner dominated convergence.
-/

namespace TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open TauCeti
open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

section ScalarKernel

/-- Scaled Haagerup--Zsido reciprocal kernel. -/
def separatedSylvesterMultiplier (d : ℝ) (_hd : 0 < d) : ℝ → ℂ :=
  fun t => HaagerupZsido.reciprocalKernel (d * t)

/-- The scaled reciprocal kernel is Bochner integrable. -/
theorem integrable_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    Integrable (separatedSylvesterMultiplier d hd) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hbase := HaagerupZsido.integrable_reciprocalKernel
  exact hbase.comp_mul_left' hd0

/-- Exact Fourier identity for the scaled reciprocal kernel. -/
theorem separatedSylvesterMultiplier_identity
    (d : ℝ) (hd : 0 < d) (a b : ℝ) (hab : d ≤ |a - b|) :
    (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
      Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
      (((a - b)⁻¹ : ℝ) : ℂ) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hab0 : a - b ≠ 0 := by
    have : 0 < |a - b| := lt_of_lt_of_le hd hab
    exact abs_pos.mp this
  set x : ℝ := (a - b) / d with hxdef
  have hx : 1 ≤ |x| := by
    rw [hxdef, abs_div, abs_of_pos hd, le_div_iff₀ hd, one_mul]
    exact hab
  have hfourier := HaagerupZsido.reciprocalKernel_fourier x hx
  set g : ℝ → ℂ := fun s =>
    HaagerupZsido.reciprocalKernel s *
      Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) with hgdef
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g d
  have harg : ∀ t : ℝ, d * t * x = t * (a - b) := by
    intro t; rw [hxdef]; field_simp
  have hpoint : (fun t : ℝ => g (d * t)) =
      fun t : ℝ => separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I)) := by
    funext t
    simp only [hgdef, separatedSylvesterMultiplier, harg t]
  rw [← hpoint, hchange, hfourier]
  have hxc : (x : ℂ) = ((a - b : ℝ) : ℂ) / (d : ℂ) := by
    rw [hxdef]; push_cast; ring
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have habc : ((a - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab0
  rw [abs_of_pos (by positivity : (0:ℝ) < d⁻¹), Complex.real_smul, hxc]
  push_cast
  field_simp

/-- Exact `L1` mass of the scaled reciprocal kernel. -/
theorem l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) =
      Real.pi / (2 * d) := by
  let g : ℝ → ℝ := fun s => ‖HaagerupZsido.reciprocalKernel s‖
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g d
  have hpoint : (fun t : ℝ => g (d * t)) =
      fun t : ℝ => ‖separatedSylvesterMultiplier d hd t‖ := by
    funext t
    rfl
  rw [← hpoint]
  calc
    (∫ t : ℝ, g (d * t)) = d⁻¹ * ∫ s : ℝ, g s := by
      simpa [Real.norm_eq_abs, abs_of_pos hd, one_div, smul_eq_mul] using hchange
    _ = d⁻¹ * (Real.pi / 2) := by
      rw [HaagerupZsido.integral_norm_reciprocalKernel]
    _ = Real.pi / (2 * d) := by
      field_simp [hd0]

/-- A form convenient for the final Sylvester estimate. -/
theorem mul_l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    d * (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) = Real.pi / 2 := by
  rw [l1_norm_separatedSylvesterMultiplier d hd]
  field_simp [ne_of_gt hd]

end ScalarKernel

section Exponentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The unitary group `exp(i t A)` of a bounded complex operator.

Until 2026-07-29 this was Spectra's `expBounded (Complex.I • A) t`, which
Spectra itself proves equal to `NormedSpace.exp ((t : ℂ) • (Complex.I • A))`
(`expBounded_eq_exp`).  Mathlib's exponential is taken as the definition here,
so the whole `ExpBounded` layer drops out.

One casualty: `norm_semigroup_le_exp_norm` (`‖exp (tA)‖ ≤ exp (|t| ‖A‖)`) was a
one-line wrapper of the donor's `expBounded_norm_bound`, and **Mathlib has no
`‖exp x‖ ≤ Real.exp ‖x‖` for a general Banach algebra** — only for `ℂ`.  It had
no consumers anywhere in the tree, so it was dropped rather than reproved from
the exponential series. -/
noncomputable def unitaryGroup (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((t : ℂ) • (Complex.I • A))

/-- The real exponential semigroup `exp(t A)`. -/
noncomputable def semigroup (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((t : ℂ) • A)

/-- `exp (i t A)` is the identity at `t = 0`. -/
@[simp] theorem unitaryGroup_zero (A : H →L[ℂ] H) :
    unitaryGroup A 0 = 1 := by
  simp [unitaryGroup, NormedSpace.exp_zero]

/-- The Fourier semigroup is the identity at `t = 0`. -/
@[simp] theorem semigroup_zero (A : H →L[ℂ] H) :
    semigroup A 0 = 1 := by
  simp [semigroup, NormedSpace.exp_zero]

/-- Group law for `exp(i t A)`. -/
theorem unitaryGroup_add (A : H →L[ℂ] H) (s t : ℝ) :
    unitaryGroup A (s + t) = unitaryGroup A s ∘L unitaryGroup A t := by
  have hcomm : Commute (((s : ℂ)) • (Complex.I • A)) (((t : ℂ)) • (Complex.I • A)) := by
    simp [Commute, SemiconjBy, smul_smul, mul_comm, mul_left_comm]
  rw [unitaryGroup, unitaryGroup, unitaryGroup, ← ContinuousLinearMap.mul_def,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
      ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _),
    ← add_smul]
  push_cast
  rfl

/-- Semigroup/group law for `exp(t A)`. -/
theorem semigroup_add (A : H →L[ℂ] H) (s t : ℝ) :
    semigroup A (s + t) = semigroup A s ∘L semigroup A t := by
  have hcomm : Commute (((s : ℂ)) • A) (((t : ℂ)) • A) := by
    simp [Commute, SemiconjBy, smul_smul, mul_comm]
  rw [semigroup, semigroup, semigroup, ← ContinuousLinearMap.mul_def,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
      ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _),
    ← add_smul]
  push_cast
  rfl

/-- The generator commutes with its own semigroup. -/
theorem commute_semigroup (A : H →L[ℂ] H) (t : ℝ) :
    Commute A (semigroup A t) :=
  ((Commute.refl A).smul_right ((t : ℂ))).exp_right

/-- Self-adjoint generators give unitary exponentials. -/
theorem unitaryGroup_mem_unitary (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) (t : ℝ) :
    unitaryGroup A t ∈ unitary (H →L[ℂ] H) := by
  have hsa : IsSelfAdjoint ((t : ℂ) • A) :=
    IsSelfAdjoint.smul (Complex.conj_ofReal t)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)
  have hrw : (t : ℂ) • (Complex.I • A) = Complex.I • ((t : ℂ) • A) := by
    rw [smul_comm]
  rw [unitaryGroup, hrw]
  exact (selfAdjoint.expUnitary (⟨(t : ℂ) • A, hsa⟩ : selfAdjoint (H →L[ℂ] H))).2

/-- The inverse of `exp(i t A)` is `exp(-i t A)`. -/
theorem unitaryGroup_neg_mul (A : H →L[ℂ] H)
    (_hA : A.IsSymmetric) (t : ℝ) :
    unitaryGroup A (-t) ∘L unitaryGroup A t = 1 ∧
      unitaryGroup A t ∘L unitaryGroup A (-t) = 1 := by
  have hsum1 := unitaryGroup_add A (-t) t
  have hsum2 := unitaryGroup_add A t (-t)
  simpa using And.intro hsum1.symm hsum2.symm

/-- Every unitary group element is a contraction. -/
theorem norm_unitaryGroup_le_one (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) (t : ℝ) :
    ‖unitaryGroup A t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul]
  exact le_of_eq
    (ContinuousLinearMap.norm_map_of_mem_unitary (unitaryGroup_mem_unitary A hA t) x)

/-- On a nonzero Hilbert space every unitary group element has norm one. -/
theorem norm_unitaryGroup [Nontrivial H] (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) (t : ℝ) :
    ‖unitaryGroup A t‖ = 1 := by
  exact CStarRing.norm_coe_unitary
    (⟨unitaryGroup A t, unitaryGroup_mem_unitary A hA t⟩ : unitary (H →L[ℂ] H))

/-- Two-sided unitary multiplication preserves the operator norm. -/
theorem norm_unitary_left_right
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (B : E →L[ℂ] E) (hB : B.IsSymmetric)
    (t : ℝ) (C : E →L[ℂ] H) :
    ‖unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)‖ = ‖C‖ := by
  let UA := unitaryGroup A t
  let UB := unitaryGroup B (-t)
  let UAinv := unitaryGroup A (-t)
  let UBinv := unitaryGroup B t
  have hforward : ‖UA ∘L C ∘L UB‖ ≤ ‖C‖ := by
    calc
      ‖UA ∘L C ∘L UB‖ ≤ ‖UA‖ * ‖C‖ * ‖UB‖ := by
        refine (UA.opNorm_comp_le (C ∘L UB)).trans ?_
        rw [mul_assoc]
        gcongr
        exact C.opNorm_comp_le UB
      _ ≤ 1 * ‖C‖ * 1 := by
        gcongr
        · exact norm_unitaryGroup_le_one A hA t
        · exact norm_unitaryGroup_le_one B hB (-t)
      _ = ‖C‖ := by ring
  have hrecover : UAinv ∘L (UA ∘L C ∘L UB) ∘L UBinv = C := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    have hAinv := (unitaryGroup_neg_mul A hA t).1
    have hBinv := (unitaryGroup_neg_mul B hB (-t)).2
    have hBx : UB (UBinv x) = x := by
      simpa [UB, UBinv] using
        congrArg (fun T : E →L[ℂ] E => T x) hBinv
    rw [hBx]
    simpa [UA, UAinv] using
      congrArg (fun T : H →L[ℂ] H => T (C x)) hAinv
  have hbackward : ‖C‖ ≤ ‖UA ∘L C ∘L UB‖ := by
    calc
      ‖C‖ = ‖UAinv ∘L (UA ∘L C ∘L UB) ∘L UBinv‖ := by rw [hrecover]
      _ ≤ ‖UAinv‖ * ‖UA ∘L C ∘L UB‖ * ‖UBinv‖ := by
        refine (UAinv.opNorm_comp_le ((UA ∘L C ∘L UB) ∘L UBinv)).trans ?_
        rw [mul_assoc]
        gcongr
        exact (UA ∘L C ∘L UB).opNorm_comp_le UBinv
      _ ≤ 1 * ‖UA ∘L C ∘L UB‖ * 1 := by
        gcongr
        · exact norm_unitaryGroup_le_one A hA (-t)
        · exact norm_unitaryGroup_le_one B hB t
      _ = ‖UA ∘L C ∘L UB‖ := by ring
  exact le_antisymm hforward hbackward

/-- Derivative of the unitary group. -/
theorem hasDerivAt_unitaryGroup (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (unitaryGroup A)
      ((Complex.I • A) ∘L unitaryGroup A t) t := by
  have hre : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℂ) (Complex.I • A) (t : ℂ)).scomp t hre
  rw [one_smul] at h
  exact h

/-- Derivative of the real exponential group. -/
theorem hasDerivAt_semigroup (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (semigroup A) (A ∘L semigroup A t) t := by
  have hre : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℂ) A (t : ℂ)).scomp t hre
  rw [one_smul] at h
  exact h

/-- The real exponential group is norm continuous in time. -/
theorem continuous_semigroup (A : H →L[ℂ] H) :
    Continuous fun t : ℝ => semigroup A t :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup A t).continuousAt

/-- The unitary group is norm continuous in time. -/
theorem continuous_unitaryGroup (A : H →L[ℂ] H) :
    Continuous fun t : ℝ => unitaryGroup A t :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_unitaryGroup A t).continuousAt

/-- The unitary group is norm continuous in its generator. -/
theorem continuous_unitaryGroup_generator (t : ℝ) :
    Continuous fun M : H →L[ℂ] H => unitaryGroup M t := by
  have heq : (fun M : H →L[ℂ] H => unitaryGroup M t) =
      fun M => NormedSpace.exp ((t : ℂ) • (Complex.I • M)) := by
    funext M
    rfl
  rw [heq]
  have hexp : Continuous (NormedSpace.exp : (H →L[ℂ] H) → H →L[ℂ] H) :=
    continuous_iff_continuousAt.mpr fun x =>
      (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt
  exact hexp.comp ((continuous_const_smul ((t : ℂ))).comp
    (continuous_const_smul Complex.I))

end Exponentials

section SpectrumBridge

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The real spectrum of a bounded complex operator is compact. -/
theorem realSpectrum_isCompact (T : H →L[ℂ] H) :
    IsCompact (realSpectrum T) := by
  have h : realSpectrum T = Complex.ofReal ⁻¹' spectrum ℂ T := rfl
  rw [h]
  exact Complex.isometry_ofReal.isClosedEmbedding.isProperMap.isCompact_preimage
    (spectrum.isCompact T)

end SpectrumBridge

section SpectralStepApproximation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A finite spectral resolution of a bounded self-adjoint operator.

The representatives are actual points of the original spectrum.  This is the
feature that preserves any cross-gap when two such resolutions are formed. -/
structure FiniteSpectralStep (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) where
  /-- The number of cells in the finite spectral partition. -/
  n : ℕ
  /-- The measurable cells covering the real spectrum. -/
  cell : Fin n → Set ℝ
  measurable_cell : ∀ i, MeasurableSet (cell i)
  pairwise_disjoint : Set.PairwiseDisjoint Set.univ cell
  covers_spectrum : realSpectrum A ⊆ ⋃ i, cell i
  /-- A spectral value representing each cell. -/
  representative : Fin n → ℝ
  representative_mem : ∀ i, representative i ∈ realSpectrum A
  /-- A uniform bound on the distance from a cell's spectral points to its representative. -/
  diameterBound : ℝ
  diameter_nonneg : 0 ≤ diameterBound
  cell_close : ∀ i, ∀ x ∈ cell i ∩ realSpectrum A,
    |x - representative i| ≤ diameterBound

/-- Operator represented by a finite spectral step. -/
noncomputable def FiniteSpectralStep.operator
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) : H →L[ℂ] H :=
  ∑ i, (S.representative i : ℂ) •
    boundedSelfAdjointSpectralProjection A hA (S.cell i)
      (S.measurable_cell i)

/-- The spectral cells sum to the identity on the spectrum. -/
theorem FiniteSpectralStep.sum_projection_eq_one
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) :
    ∑ i, boundedSelfAdjointSpectralProjection A hA (S.cell i)
      (S.measurable_cell i) = 1 :=
  (spectralProjection_finset_sum_eq_id A hA S.cell S.measurable_cell
    S.pairwise_disjoint S.covers_spectrum).trans rfl

/-- A spectral step approximates its generator in operator norm by the cell
radius. -/
theorem FiniteSpectralStep.norm_operator_sub_le
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) :
    ‖S.operator - A‖ ≤ S.diameterBound := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · -- On a trivial space every operator is zero, so the estimate is `0 ≤ diam`.
    have : S.operator - A = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
    exact S.diameter_nonneg
  · have := hnon
    have hf := measurable_chosenFiniteStepSymbol S.cell S.measurable_cell
      S.pairwise_disjoint S.representative
    have hfb : BoundedOnSpectrum A (chosenFiniteStepSymbol S.cell S.representative) := by
      refine ⟨∑ i, |S.representative i|,
        Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (S.covers_spectrum hx)
      have hex : ∃ j, x ∈ S.cell j := ⟨i, hxi⟩
      rw [chosenFiniteStepSymbol, dite_eq_left hex]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (S.representative j))
        (Finset.mem_univ _)
    have hclose : ∀ x ∈ realSpectrum A,
        |chosenFiniteStepSymbol S.cell S.representative x - x| ≤ S.diameterBound := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (S.covers_spectrum hx)
      have hex : ∃ j, x ∈ S.cell j := ⟨i, hxi⟩
      rw [chosenFiniteStepSymbol, dite_eq_left hex]
      have hxj : x ∈ S.cell (Classical.choose hex) := Classical.choose_spec hex
      have hsame : Classical.choose hex = i := by
        by_contra hne
        exact Set.disjoint_left.mp
          (S.pairwise_disjoint (Set.mem_univ (Classical.choose hex))
            (Set.mem_univ i) hne) hxj hxi
      rw [hsame]
      simpa [abs_sub_comm] using S.cell_close i x ⟨hxi, hx⟩
    have hcalc : S.operator = boundedSelfAdjointBorelCalculus A hA
        (chosenFiniteStepSymbol S.cell S.representative) hf hfb := by
      rw [FiniteSpectralStep.operator]
      exact (boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator A hA S.cell
        S.measurable_cell S.pairwise_disjoint S.representative S.covers_spectrum).symm
    calc
      ‖S.operator - A‖
          = ‖boundedSelfAdjointBorelCalculus A hA
                (chosenFiniteStepSymbol S.cell S.representative) hf hfb -
              boundedSelfAdjointBorelCalculus A hA (fun x => x) measurable_id
                (identity_boundedOnSpectrum A)‖ := by
            rw [hcalc, boundedSelfAdjointBorelCalculus_id A hA]
      _ ≤ S.diameterBound :=
            boundedSelfAdjointBorelCalculus_norm_sub_le A hA hf measurable_id hfb
              (identity_boundedOnSpectrum A) S.diameter_nonneg hclose

/-- Finite spectral steps are self-adjoint operators. -/
theorem FiniteSpectralStep.operator_isSelfAdjoint
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) : S.operator.IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  change star S.operator = S.operator
  rw [FiniteSpectralStep.operator, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (boundedSelfAdjointSpectralProjection_isOrthogonalProjection A hA
      (S.cell i) (S.measurable_cell i)).2).star_eq

/-- Norm bound for a finite spectral step in terms of its generator. -/
theorem FiniteSpectralStep.norm_operator_le
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) :
    ‖S.operator‖ ≤ ‖A‖ + S.diameterBound := by
  have hsub := S.norm_operator_sub_le
  have hsplit : S.operator = A + (S.operator - A) := by abel
  calc
    ‖S.operator‖ = ‖A + (S.operator - A)‖ := by rw [← hsplit]
    _ ≤ ‖A‖ + ‖S.operator - A‖ := norm_add_le _ _
    _ ≤ ‖A‖ + S.diameterBound := by gcongr

/-- Every bounded self-adjoint operator has finite spectral steps with
arbitrarily small cells and representatives in its own spectrum. -/
theorem exists_finiteSpectralStep
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : FiniteSpectralStep A hA, S.diameterBound ≤ ε := by
  classical
  obtain ⟨t, hts, htfin, hcov⟩ :=
    finite_cover_balls_of_compact (realSpectrum_isCompact A) hε
  let s : Finset ℝ := htfin.toFinset
  let y : Fin s.card → ℝ := fun i => (s.equivFin.symm i : ℝ)
  have hy_mem : ∀ i, y i ∈ realSpectrum A := fun i =>
    hts (htfin.mem_toFinset.mp (s.equivFin.symm i).2)
  let g : Fin s.card → Set ℝ := fun i => Metric.ball (y i) ε
  have hg_cover : realSpectrum A ⊆ ⋃ i, g i := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
    have hcs : c ∈ s := htfin.mem_toFinset.mpr hc
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨c, hcs⟩, ?_⟩
    have hyc : y (s.equivFin ⟨c, hcs⟩) = c := by
      change ((s.equivFin.symm (s.equivFin ⟨c, hcs⟩) : ℝ)) = c
      rw [Equiv.symm_apply_apply]
    change x ∈ Metric.ball (y (s.equivFin ⟨c, hcs⟩)) ε
    rwa [hyc]
  have hcell_meas : ∀ i, MeasurableSet (disjointed g i) := by
    intro i
    rw [disjointed_apply]
    refine measurableSet_ball.diff ?_
    rw [Finset.sup_eq_iSup]
    exact (Finset.Iio i).measurableSet_biUnion fun j _ => measurableSet_ball
  refine ⟨⟨s.card, disjointed g, hcell_meas, ?_, ?_, y, hy_mem, ε, hε.le, ?_⟩, le_rfl⟩
  · intro i _ j _ hij
    exact disjoint_disjointed g hij
  · rw [iUnion_disjointed]
    exact hg_cover
  · intro i x hx
    have hxg : x ∈ g i := disjointed_le g i hx.1
    have : dist x (y i) < ε := Metric.mem_ball.mp hxg
    rw [Real.dist_eq] at this
    exact this.le

omit [CompleteSpace H] in
/-- Two finite steps whose representatives come from separated original
spectra inherit exactly the same separation. -/
theorem finiteSpectralStep_representatives_separated
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {d : ℝ} (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (SA : FiniteSpectralStep A hA) (SB : FiniteSpectralStep B hB)
    (i : Fin SA.n) (j : Fin SB.n) :
    d ≤ |SA.representative i - SB.representative j| := by
  obtain ⟨hInvA, hInvB, hgap⟩ := hsep
  exact hgap _
    ⟨hInvA, (ContinuousLinearMap.spectrum_restrict_top A hInvA).symm.subset (SA.representative_mem
      i)⟩ _
    ⟨hInvB, (ContinuousLinearMap.spectrum_restrict_top B hInvB).symm.subset (SB.representative_mem
      j)⟩

end SpectralStepApproximation

section FiniteStepReconstruction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Finite spectral block evaluation of the unitary group. -/
theorem unitaryGroup_finiteSpectralStep
    {A : F →L[ℂ] F} {hA : A.IsSymmetric}
    (S : FiniteSpectralStep A hA) (t : ℝ) :
    unitaryGroup S.operator t =
      ∑ i, Complex.exp (((t * S.representative i : ℝ) : ℂ) * Complex.I) •
        boundedSelfAdjointSpectralProjection A hA (S.cell i)
          (S.measurable_cell i) := by
  rw [unitaryGroup, smul_smul]
  exact unitaryGroup_finiteDiagonal
    (fun i => boundedSelfAdjointSpectralProjection A hA (S.cell i) (S.measurable_cell i))
    S.representative
    (fun i => (boundedSelfAdjointSpectralPVM A hA).proj_idem (S.cell i) (S.measurable_cell i))
    (spectralProjection_pairwise_orthogonal A hA S.cell S.measurable_cell S.pairwise_disjoint)
    S.sum_projection_eq_one t

/-- The reciprocal integral reconstructs a Sylvester solution for finite
spectral steps. -/
theorem finiteSpectralStep_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (SA : FiniteSpectralStep A hA) (SB : FiniteSpectralStep B hB)
    (X : E →L[ℂ] F) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup SA.operator t ∘L
        (SA.operator ∘L X - X ∘L SB.operator) ∘L
        unitaryGroup SB.operator (-t)) := by
  have hUA : ∀ s : ℝ, unitaryGroup SA.operator s =
      NormedSpace.exp (((s : ℂ) * Complex.I) • SA.operator) := fun s => by
    rw [unitaryGroup, smul_smul]
  have hUB : ∀ s : ℝ, unitaryGroup SB.operator s =
      NormedSpace.exp (((s : ℂ) * Complex.I) • SB.operator) := fun s => by
    rw [unitaryGroup, smul_smul]
  have hSAop : SA.operator = finiteDiagonalOperator
      (fun i => boundedSelfAdjointSpectralProjection A hA (SA.cell i) (SA.measurable_cell i))
      SA.representative := rfl
  have hSBop : SB.operator = finiteDiagonalOperator
      (fun j => boundedSelfAdjointSpectralProjection B hB (SB.cell j) (SB.measurable_cell j))
      SB.representative := rfl
  simp only [hUA, hUB]
  simp only [hSAop, hSBop]
  exact finiteDiagonal_sylvester_reconstruction
    (fun i => boundedSelfAdjointSpectralProjection A hA (SA.cell i) (SA.measurable_cell i))
    (fun j => boundedSelfAdjointSpectralProjection B hB (SB.cell j) (SB.measurable_cell j))
    SA.representative SB.representative
    (fun i => (boundedSelfAdjointSpectralPVM A hA).proj_idem (SA.cell i) (SA.measurable_cell i))
    (spectralProjection_pairwise_orthogonal A hA SA.cell SA.measurable_cell SA.pairwise_disjoint)
    SA.sum_projection_eq_one
    (fun j => (boundedSelfAdjointSpectralPVM B hB).proj_idem (SB.cell j) (SB.measurable_cell j))
    (spectralProjection_pairwise_orthogonal B hB SB.cell SB.measurable_cell SB.pairwise_disjoint)
    SB.sum_projection_eq_one
    (separatedSylvesterMultiplier d hd)
    (integrable_separatedSylvesterMultiplier d hd)
    (fun i j => separatedSylvesterMultiplier_identity d hd
      (SA.representative i) (SB.representative j)
      (finiteSpectralStep_representatives_separated hsep SA SB i j))
    (fun i j => abs_pos.mp
      (lt_of_lt_of_le hd (finiteSpectralStep_representatives_separated hsep SA SB i j)))
    X

end FiniteStepReconstruction

section LimitReconstruction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Pointwise norm continuity of the two-sided unitary orbit in all three
operator arguments. -/
theorem tendsto_unitary_orbit
    {A : ℕ → F →L[ℂ] F} {B : ℕ → E →L[ℂ] E}
    {C : ℕ → E →L[ℂ] F} {A0 : F →L[ℂ] F} {B0 : E →L[ℂ] E}
    {C0 : E →L[ℂ] F}
    (hA : Tendsto A atTop (nhds A0))
    (hB : Tendsto B atTop (nhds B0))
    (hC : Tendsto C atTop (nhds C0)) (t : ℝ) :
    Tendsto (fun n => unitaryGroup (A n) t ∘L C n ∘L unitaryGroup (B n) (-t))
      atTop (nhds (unitaryGroup A0 t ∘L C0 ∘L unitaryGroup B0 (-t))) := by
  have hUA : Tendsto (fun n => unitaryGroup (A n) t) atTop
      (nhds (unitaryGroup A0 t)) :=
    ((continuous_unitaryGroup_generator t).tendsto A0).comp hA
  have hUB : Tendsto (fun n => unitaryGroup (B n) (-t)) atTop
      (nhds (unitaryGroup B0 (-t))) :=
    ((continuous_unitaryGroup_generator (-t)).tendsto B0).comp hB
  have hCB : Tendsto (fun n => C n ∘L unitaryGroup (B n) (-t)) atTop
      (nhds (C0 ∘L unitaryGroup B0 (-t))) := by
    have hcont : Continuous fun p : (E →L[ℂ] F) × (E →L[ℂ] E) => p.1 ∘L p.2 :=
      isBoundedBilinearMap_comp.continuous
    exact (hcont.tendsto (C0, unitaryGroup B0 (-t))).comp (hC.prodMk_nhds hUB)
  have hcont2 : Continuous fun p : (F →L[ℂ] F) × (E →L[ℂ] F) => p.1 ∘L p.2 :=
    isBoundedBilinearMap_comp.continuous
  exact (hcont2.tendsto (unitaryGroup A0 t, C0 ∘L unitaryGroup B0 (-t))).comp
    (hUA.prodMk_nhds hCB)

/-- Dominated-convergence passage for the separated reciprocal integral. -/
theorem tendsto_separated_integral
    {An : ℕ → F →L[ℂ] F} {Bn : ℕ → E →L[ℂ] E} {Cn : ℕ → E →L[ℂ] F}
    {A0 : F →L[ℂ] F} {B0 : E →L[ℂ] E} {C0 : E →L[ℂ] F}
    (hAn : ∀ n, (An n).IsSymmetric)
    (hBn : ∀ n, (Bn n).IsSymmetric)
    {M : ℝ} (hM : ∀ n, ‖Cn n‖ ≤ M)
    (hA : Tendsto An atTop (nhds A0)) (hB : Tendsto Bn atTop (nhds B0))
    (hC : Tendsto Cn atTop (nhds C0))
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n => ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t))) atTop
      (nhds (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A0 t ∘L C0 ∘L unitaryGroup B0 (-t)))) := by
  have hμ := integrable_separatedSylvesterMultiplier d hd
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t => ‖separatedSylvesterMultiplier d hd t‖ * M) ?_ ?_ ?_ ?_
  · intro n
    have hcont : Continuous fun t : ℝ =>
        unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t) :=
      (continuous_unitaryGroup (An n)).clm_comp (continuous_const.clm_comp
        ((continuous_unitaryGroup (Bn n)).comp continuous_neg))
    exact hμ.aestronglyMeasurable.smul hcont.aestronglyMeasurable
  · exact hμ.norm.mul_const M
  · intro n
    filter_upwards with t
    rw [norm_smul]
    have horbit : ‖unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)‖ ≤
        M := by
      calc
        ‖unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)‖
            ≤ ‖unitaryGroup (An n) t‖ *
              ‖Cn n ∘L unitaryGroup (Bn n) (-t)‖ :=
          (unitaryGroup (An n) t).opNorm_comp_le _
        _ ≤ 1 * (‖Cn n‖ * ‖unitaryGroup (Bn n) (-t)‖) := by
          gcongr
          · exact norm_unitaryGroup_le_one (An n) (hAn n) t
          · exact (Cn n).opNorm_comp_le _
        _ ≤ M := by
          have hB1 := norm_unitaryGroup_le_one (Bn n) (hBn n) (-t)
          have hCle := hM n
          have h0C : (0 : ℝ) ≤ ‖Cn n‖ := norm_nonneg _
          have h0B : (0 : ℝ) ≤ ‖unitaryGroup (Bn n) (-t)‖ := norm_nonneg _
          nlinarith
    exact mul_le_mul_of_nonneg_left horbit (norm_nonneg _)
  · filter_upwards with t
    exact (tendsto_unitary_orbit hA hB hC t).const_smul
      (separatedSylvesterMultiplier d hd t)

/-- Exact separated-spectrum reconstruction on complex Hilbert spaces. -/
theorem separatedSylvester_reconstruction_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  choose SA hSA using fun n : ℕ => exists_finiteSpectralStep A hA (hpos n)
  choose SB hSB using fun n : ℕ => exists_finiteSpectralStep B hB (hpos n)
  have hone : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have honeover : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAop : Tendsto (fun n => (SA n).operator) atTop (nhds A) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (SA n).norm_operator_sub_le.trans (hSA n)) honeover
  have hBop : Tendsto (fun n => (SB n).operator) atTop (nhds B) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (SB n).norm_operator_sub_le.trans (hSB n)) honeover
  have hCn : Tendsto
      (fun n => (SA n).operator ∘L X - X ∘L (SB n).operator) atTop (nhds C) := by
    have hcomp1 : Continuous fun M : F →L[ℂ] F => M ∘L X :=
      continuous_id.clm_comp continuous_const
    have hcomp2 : Continuous fun M : E →L[ℂ] E => X ∘L M :=
      continuous_const.clm_comp continuous_id
    have h1 : Tendsto (fun n => (SA n).operator ∘L X) atTop (nhds (A ∘L X)) :=
      ((hcomp1.tendsto A).comp hAop)
    have h2 : Tendsto (fun n => X ∘L (SB n).operator) atTop (nhds (X ∘L B)) :=
      ((hcomp2.tendsto B).comp hBop)
    have := h1.sub h2
    rwa [hEq] at this
  have hM : ∀ n, ‖(SA n).operator ∘L X - X ∘L (SB n).operator‖ ≤
      (‖A‖ + 1) * ‖X‖ + ‖X‖ * (‖B‖ + 1) := by
    intro n
    have hnormA : ‖(SA n).operator‖ ≤ ‖A‖ + 1 := by
      have h1 := (SA n).norm_operator_le
      have h2 : (SA n).diameterBound ≤ 1 := (hSA n).trans (hone n)
      linarith
    have hnormB : ‖(SB n).operator‖ ≤ ‖B‖ + 1 := by
      have h1 := (SB n).norm_operator_le
      have h2 : (SB n).diameterBound ≤ 1 := (hSB n).trans (hone n)
      linarith
    calc
      ‖(SA n).operator ∘L X - X ∘L (SB n).operator‖
          ≤ ‖(SA n).operator ∘L X‖ + ‖X ∘L (SB n).operator‖ := norm_sub_le _ _
      _ ≤ ‖(SA n).operator‖ * ‖X‖ + ‖X‖ * ‖(SB n).operator‖ :=
          add_le_add ((SA n).operator.opNorm_comp_le X) (X.opNorm_comp_le _)
      _ ≤ (‖A‖ + 1) * ‖X‖ + ‖X‖ * (‖B‖ + 1) := by gcongr
  have hlim := tendsto_separated_integral
    (fun n => (SA n).operator_isSelfAdjoint)
    (fun n => (SB n).operator_isSelfAdjoint) hM hAop hBop hCn hd
  have hconst : (fun n => ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup (SA n).operator t ∘L
        ((SA n).operator ∘L X - X ∘L (SB n).operator) ∘L
        unitaryGroup (SB n).operator (-t))) = fun _ => X := by
    funext n
    exact (finiteSpectralStep_reconstruction hd hsep (SA n) (SB n) X).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- The integral in the separated reconstruction is integrable. -/
theorem separatedSylvester_integrable_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d) (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  have hμ := integrable_separatedSylvesterMultiplier d hd
  have hcont : Continuous fun t : ℝ =>
      unitaryGroup A t ∘L C ∘L unitaryGroup B (-t) :=
    (continuous_unitaryGroup A).clm_comp (continuous_const.clm_comp
      ((continuous_unitaryGroup B).comp continuous_neg))
  refine Integrable.mono' (hμ.norm.mul_const ‖C‖)
    (hμ.aestronglyMeasurable.smul hcont.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_smul, norm_unitary_left_right A hA B hB t C]


/-- The reciprocal integral is a right inverse of the Sylvester operator.

The proof uses the same finite spectral steps as the reconstruction theorem.
For each step pair the assertion is the scalar Fourier identity on every
spectral rectangle.  The step generators converge in operator norm, their
unitary orbits converge pointwise, and the reciprocal kernel supplies an
integrable dominating function. -/
theorem spectral_step_integral_right_inverse
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (C : E →L[ℂ] F) :
    A ∘L (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) -
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) ∘L B = C := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  choose SA hSA using fun n : ℕ => exists_finiteSpectralStep A hA (hpos n)
  choose SB hSB using fun n : ℕ => exists_finiteSpectralStep B hB (hpos n)
  have honeover : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAop : Tendsto (fun n => (SA n).operator) atTop (nhds A) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (SA n).norm_operator_sub_le.trans (hSA n)) honeover
  have hBop : Tendsto (fun n => (SB n).operator) atTop (nhds B) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (SB n).norm_operator_sub_le.trans (hSB n)) honeover
  -- each finite reciprocal integral solves the finite Sylvester equation
  have hsolve : ∀ n, (SA n).operator ∘L
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (SA n).operator t ∘L C ∘L
          unitaryGroup (SB n).operator (-t))) -
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (SA n).operator t ∘L C ∘L
          unitaryGroup (SB n).operator (-t))) ∘L (SB n).operator = C := by
    intro n
    have hne : ∀ (i : Fin (SA n).n) (j : Fin (SB n).n),
        (SA n).representative i - (SB n).representative j ≠ 0 := fun i j =>
      abs_pos.mp (lt_of_lt_of_le hd
        (finiteSpectralStep_representatives_separated hsep (SA n) (SB n) i j))
    set Xn : E →L[ℂ] F := ∑ i, ∑ j,
      ((((SA n).representative i - (SB n).representative j)⁻¹ : ℝ) : ℂ) •
        (boundedSelfAdjointSpectralProjection A hA ((SA n).cell i)
            ((SA n).measurable_cell i) ∘L C ∘L
          boundedSelfAdjointSpectralProjection B hB ((SB n).cell j)
            ((SB n).measurable_cell j)) with hXn
    have hdefect : (SA n).operator ∘L Xn - Xn ∘L (SB n).operator = C :=
      finiteDiagonal_sylvester_solution
        (fun i => boundedSelfAdjointSpectralProjection A hA ((SA n).cell i)
          ((SA n).measurable_cell i))
        (fun j => boundedSelfAdjointSpectralProjection B hB ((SB n).cell j)
          ((SB n).measurable_cell j))
        (SA n).representative (SB n).representative
        (fun i => (boundedSelfAdjointSpectralPVM A hA).proj_idem
          ((SA n).cell i) ((SA n).measurable_cell i))
        (spectralProjection_pairwise_orthogonal A hA (SA n).cell
          (SA n).measurable_cell (SA n).pairwise_disjoint)
        (SA n).sum_projection_eq_one
        (fun j => (boundedSelfAdjointSpectralPVM B hB).proj_idem
          ((SB n).cell j) ((SB n).measurable_cell j))
        (spectralProjection_pairwise_orthogonal B hB (SB n).cell
          (SB n).measurable_cell (SB n).pairwise_disjoint)
        (SB n).sum_projection_eq_one
        hne C
    have hXrec := finiteSpectralStep_reconstruction hd hsep (SA n) (SB n) Xn
    simp only [hdefect] at hXrec
    rw [← hXrec]
    exact hdefect
  -- the finite reciprocal integrals converge to the limit integral
  have hIlim := tendsto_separated_integral
    (fun n => (SA n).operator_isSelfAdjoint)
    (fun n => (SB n).operator_isSelfAdjoint)
    (M := ‖C‖) (fun n => le_rfl) hAop hBop
    (tendsto_const_nhds (x := C)) hd
  -- limit of the finite Sylvester identities
  have hcomp : Continuous fun p : (F →L[ℂ] F) × (E →L[ℂ] F) => p.1 ∘L p.2 :=
    isBoundedBilinearMap_comp.continuous
  have hcomp' : Continuous fun p : (E →L[ℂ] F) × (E →L[ℂ] E) => p.1 ∘L p.2 :=
    isBoundedBilinearMap_comp.continuous
  have h1 : Tendsto (fun n => (SA n).operator ∘L
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (SA n).operator t ∘L C ∘L
          unitaryGroup (SB n).operator (-t)))) atTop
      (nhds (A ∘L (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))))) :=
    (hcomp.tendsto _).comp (hAop.prodMk_nhds hIlim)
  have h2 : Tendsto (fun n =>
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (SA n).operator t ∘L C ∘L
          unitaryGroup (SB n).operator (-t))) ∘L (SB n).operator) atTop
      (nhds ((∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) ∘L B)) :=
    (hcomp'.tendsto _).comp (hIlim.prodMk_nhds hBop)
  have hL := h1.sub h2
  rw [funext hsolve] at hL
  exact (tendsto_nhds_unique hL tendsto_const_nhds).symm.symm


/-- Spectral-multiplier extensionality for the reciprocal kernel.

The proof is the finite-spectral-step argument above: equality is checked on
all spectral rectangles and then passed to norm limits.  The final scalar
premise is exposed so callers can localize any normalization or sign error to
the one-dimensional Fourier identity. -/
theorem spectralMultiplier_ext
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} {hd : 0 < d}
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {C : E →L[ℂ] F}
    (hscalar : ∀ a ∈ realSpectrum A, ∀ b ∈ realSpectrum B,
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
        (((a - b)⁻¹ : ℝ) : ℂ)) :
    A ∘L (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) -
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) ∘L B = C := by
  have hcanonical : ∀ a ∈ realSpectrum A, ∀ b ∈ realSpectrum B,
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
        (((a - b)⁻¹ : ℝ) : ℂ) := by
    intro a ha b hb
    exact hscalar a ha b hb
  exact spectral_step_integral_right_inverse hA hB hd hsep C

end LimitReconstruction

end

end DavisKahan.Sylvester
end TauCeti
