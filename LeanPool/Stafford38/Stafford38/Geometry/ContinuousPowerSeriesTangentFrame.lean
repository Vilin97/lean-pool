/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.PiTopology
import LeanPool.Stafford38.Stafford38.Geometry.FixedWitnessTangentSqueeze
import LeanPool.Stafford38.Stafford38.Geometry.SeparableResidueDerivationExtension

/-!
# Continuous derivation frames on a supplied power-series chart

Assume that the completed boundary DVR has already been identified with
`K[[t]]`.  This file constructs the two kinds of derivations used on that
chart:

* the uniformizer derivation `d/dt`;
* the coefficientwise extension of every `k`-derivation of `K`.

With the product topology on `K[[t]]` and the discrete topology on `K`, both
constructions are continuous.  A finite family is indexed by `Option κ`, with
`none` denoting `d/dt` and `some j` denoting the `j`th coefficient derivation.
Taking constant coefficients after applying the frame to the chart
coordinates gives the finite family of affine tangent vectors consumed by
`FixedWitnessTangentSqueeze`.

The first missing bridge after this file is the chart-to-component tangency
statement: the supplied completed-DVR chart must prove that every residue
frame vector annihilates the differential of every equation of the affine
component.  After that, the remaining inputs to the squeeze are independence
of the residue vectors and the tangent-dimension bound.  This file does not
construct the residue-field section or the `K[[t]]` chart.
-/

namespace Stafford38.Geometry.ContinuousPowerSeriesTangentFrame

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FixedWitnessTangentSqueeze
open Stafford38.Geometry.SeparableResidueDerivationExtension

open scoped PowerSeries.WithPiTopology

noncomputable section

universe u v

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The `k`-linear coefficientwise action underlying the extended
derivation. -/
noncomputable def coefficientwiseLinearMap (D : Derivation k K K) :
    PowerSeries K →ₗ[k] PowerSeries K where
  toFun f := PowerSeries.mk fun n ↦ D (PowerSeries.coeff n f)
  map_add' f g := by
    ext n
    simp
  map_smul' a f := by
    ext n
    simp

@[simp]
theorem coeff_coefficientwiseLinearMap (D : Derivation k K K)
    (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwiseLinearMap D f) =
      D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n
      (PowerSeries.mk fun m ↦ D (PowerSeries.coeff m f)) = _
  rw [PowerSeries.coeff_mk]

/-- Apply a derivation to every coefficient of a formal power series. -/
noncomputable def coefficientwiseDerivation (D : Derivation k K K) :
    Derivation k (PowerSeries K) (PowerSeries K) where
  toLinearMap := coefficientwiseLinearMap D
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;>
      simp [hn, D.map_one_eq_zero]
  leibniz' f g := by
    ext n
    simp only [smul_eq_mul, coeff_coefficientwiseLinearMap]
    rw [PowerSeries.coeff_mul, map_add,
      PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [map_sum]
    simp_rw [D.leibniz]
    rw [Finset.sum_add_distrib]
    simp only [coeff_coefficientwiseLinearMap, smul_eq_mul]
    congr 1
    simpa only [Prod.fst_swap, Prod.snd_swap] using
      (Finset.Nat.sum_antidiagonal_swap (n := n)
        (f := fun p ↦ PowerSeries.coeff p.1 g *
          D (PowerSeries.coeff p.2 f)))

@[simp]
theorem coeff_coefficientwiseDerivation (D : Derivation k K K)
    (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwiseDerivation D f) =
      D (PowerSeries.coeff n f) := by
  exact coeff_coefficientwiseLinearMap D f n

@[simp]
theorem coefficientwiseDerivation_C (D : Derivation k K K) (a : K) :
    coefficientwiseDerivation D (PowerSeries.C a) =
      PowerSeries.C (D a) := by
  ext n
  cases n <;> simp

@[simp]
theorem coefficientwiseDerivation_X (D : Derivation k K K) :
    coefficientwiseDerivation D (PowerSeries.X : PowerSeries K) = 0 := by
  ext n
  by_cases hn : n = 1 <;>
    simp [PowerSeries.coeff_X, hn, D.map_one_eq_zero]

/-- Coefficientwise derivations are continuous for the coefficientwise
topology when the coefficient field is discrete. -/
theorem continuous_coefficientwiseDerivation
    [TopologicalSpace K] [DiscreteTopology K]
    (D : Derivation k K K) :
    Continuous (coefficientwiseDerivation D) := by
  refine continuous_pi_iff.mpr fun d ↦ ?_
  exact (continuous_of_discreteTopology : Continuous D).comp
    (PowerSeries.WithPiTopology.continuous_coeff K (d ()))

/-- The uniformizer derivation, regarded as a `k`-derivation by restriction
along `k → K → K[[t]]`. -/
noncomputable def uniformizerDerivation :
    Derivation k (PowerSeries K) (PowerSeries K) :=
  (PowerSeries.derivative (R := K)).restrictScalars k

@[simp]
theorem uniformizerDerivation_C (a : K) :
    uniformizerDerivation (k := k) (K := K) (PowerSeries.C a) = 0 := by
  simp [uniformizerDerivation]

@[simp]
theorem uniformizerDerivation_X :
    uniformizerDerivation (k := k) (K := K)
      (PowerSeries.X : PowerSeries K) = 1 := by
  simp [uniformizerDerivation]

theorem coeff_uniformizerDerivation (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n
        (uniformizerDerivation (k := k) (K := K) f) =
      PowerSeries.coeff (n + 1) f * (n + 1) := by
  exact PowerSeries.coeff_derivative f n

/-- Formal differentiation is continuous in the coefficientwise topology. -/
theorem continuous_uniformizerDerivation
    [TopologicalSpace K] [DiscreteTopology K] :
    Continuous (uniformizerDerivation (k := k) (K := K)) := by
  refine continuous_pi_iff.mpr fun d ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n, d = Finsupp.single () n :=
    ⟨d default, Finsupp.unique_single d⟩
  show Continuous fun a : PowerSeries K ↦
    PowerSeries.coeff n (uniformizerDerivation (k := k) (K := K) a)
  rw [funext fun f ↦ coeff_uniformizerDerivation (k := k) (K := K) f n]
  exact (continuous_of_discreteTopology :
      Continuous (fun a : K ↦ a * (n + 1))).comp
    (PowerSeries.WithPiTopology.continuous_coeff K (n + 1))

/-- Index type for the uniformizer direction together with a finite family of
coefficient directions. -/
abbrev FrameIndex (κ : Type v) := Option κ

/-- The derivation frame on `K[[t]]`: `none` is `d/dt`, while `some j` acts
coefficientwise by `D j`. -/
noncomputable def powerSeriesDerivationFrame {κ : Type v}
    (D : κ → Derivation k K K) :
    FrameIndex κ → Derivation k (PowerSeries K) (PowerSeries K)
  | none => uniformizerDerivation
  | some j => coefficientwiseDerivation (D j)

/-- Every member of the finite chart frame is continuous. -/
theorem continuous_powerSeriesDerivationFrame
    [TopologicalSpace K] [DiscreteTopology K]
    {κ : Type v} (D : κ → Derivation k K K) (j : FrameIndex κ) :
    Continuous (powerSeriesDerivationFrame D j) := by
  cases j with
  | none => exact continuous_uniformizerDerivation
  | some j => exact continuous_coefficientwiseDerivation (D j)

/-- Evaluate a chart derivation on each affine coordinate and specialize at
the closed point. -/
def residueFrameVector {n : ℕ} {κ : Type v}
    (q : Fin n → PowerSeries K) (D : κ → Derivation k K K)
    (j : FrameIndex κ) : AffineTangentVector K n :=
  fun i ↦ PowerSeries.constantCoeff (powerSeriesDerivationFrame D j (q i))

@[simp]
theorem residueFrameVector_uniformizer {n : ℕ} {κ : Type v}
    (q : Fin n → PowerSeries K) (D : κ → Derivation k K K) (i : Fin n) :
    residueFrameVector q D none i = PowerSeries.coeff 1 (q i) := by
  rw [residueFrameVector, powerSeriesDerivationFrame,
    ← PowerSeries.coeff_zero_eq_constantCoeff]
  simpa using coeff_uniformizerDerivation (k := k) (K := K) (q i) 0

@[simp]
theorem residueFrameVector_coefficient {n : ℕ} {κ : Type v}
    (q : Fin n → PowerSeries K) (D : κ → Derivation k K K)
    (j : κ) (i : Fin n) :
    residueFrameVector q D (some j) i =
      D j (PowerSeries.constantCoeff (q i)) := by
  rw [residueFrameVector, powerSeriesDerivationFrame,
    ← PowerSeries.coeff_zero_eq_constantCoeff]
  exact coeff_coefficientwiseDerivation (D j) (q i) 0

/-- Exact finite-dimensional handoff to `FixedWitnessTangentSqueeze`.

The three hypotheses are precisely the geometric obligations left to the
supplied completed-DVR chart: tangency of every specialized derivation,
independence of the resulting residue vectors, and the tangent-dimension
bound. -/
theorem tangent_eq_span_residueFrame
    {n : ℕ} {κ : Type v} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin n) K))
    (q : Fin n → PowerSeries K)
    (D : κ → Derivation k K K)
    (hb : ∀ j, residueFrameVector q D j ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I)
    (hindependent : LinearIndependent K (residueFrameVector q D))
    (hfinrank : Module.finrank K
        (zariskiTangentSpace
          (fun i ↦ PowerSeries.constantCoeff (q i)) I) ≤
      Fintype.card (FrameIndex κ)) :
    zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I =
      Submodule.span K (Set.range (residueFrameVector q D)) := by
  exact fixedWitnessTangentSqueeze I _ _ hb hindependent hfinrank

/-- Reverse-inclusion form used by the conormal annihilator consumer. -/
theorem tangent_le_span_residueFrame
    {n : ℕ} {κ : Type v} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin n) K))
    (q : Fin n → PowerSeries K)
    (D : κ → Derivation k K K)
    (hb : ∀ j, residueFrameVector q D j ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I)
    (hindependent : LinearIndependent K (residueFrameVector q D))
    (hfinrank : Module.finrank K
        (zariskiTangentSpace
          (fun i ↦ PowerSeries.constantCoeff (q i)) I) ≤
      Fintype.card (FrameIndex κ)) :
    zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I ≤
      Submodule.span K (Set.range (residueFrameVector q D)) := by
  rw [tangent_eq_span_residueFrame I q D hb hindependent hfinrank]

/-- Extend a finite family of coefficient-field derivations through a
separable residue extension and then coefficientwise to the supplied
`K[[t]]` chart. -/
noncomputable def separablePowerSeriesDerivationFrame
    {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Algebra.IsSeparable E K]
    {κ : Type v} (D : κ → Derivation k E E) :
    FrameIndex κ → Derivation k (PowerSeries K) (PowerSeries K) :=
  powerSeriesDerivationFrame
    (fun j ↦ extendCoefficientDerivation k E K (D j))

@[simp]
theorem separablePowerSeriesDerivationFrame_none
    {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Algebra.IsSeparable E K]
    {κ : Type v} (D : κ → Derivation k E E) :
    separablePowerSeriesDerivationFrame (K := K) D none =
      uniformizerDerivation := by
  rfl

@[simp]
theorem separablePowerSeriesDerivationFrame_some_C
    {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Algebra.IsSeparable E K]
    {κ : Type v} (D : κ → Derivation k E E) (j : κ) (a : E) :
    separablePowerSeriesDerivationFrame (K := K) D (some j)
        (PowerSeries.C (algebraMap E K a)) =
      PowerSeries.C (algebraMap E K (D j a)) := by
  rw [separablePowerSeriesDerivationFrame, powerSeriesDerivationFrame,
    coefficientwiseDerivation_C]
  congr 1
  exact Derivation.congr_fun
    (extendCoefficientDerivation_compAlgebraMap k E K (D j)) a

/-- Continuity of the complete frame obtained from the separable residue
tower. -/
theorem continuous_separablePowerSeriesDerivationFrame
    [TopologicalSpace K] [DiscreteTopology K]
    {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Algebra.IsSeparable E K]
    {κ : Type v} (D : κ → Derivation k E E) (j : FrameIndex κ) :
    Continuous (separablePowerSeriesDerivationFrame (K := K) D j) := by
  exact continuous_powerSeriesDerivationFrame _ j


end

end Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
