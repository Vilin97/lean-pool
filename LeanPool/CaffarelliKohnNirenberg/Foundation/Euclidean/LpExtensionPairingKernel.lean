/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairing

/-!
# Lp Extension Pairing Kernel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- A function in `L^p` with compact support is integrable.

The compact support confines the function to a finite-measure set, where the
`L^p` membership with `p ≥ 1` yields integrability, and integrability on the
support is equivalent to integrability on the whole space.  This is the
integrability input for the pairing identities of `cor:CZ-harmonic`. -/
theorem integrable_of_memLp_hasCompactSupport {p : ℝ≥0∞} (hp : 1 ≤ p)
    {G : Vec3 → ℝ} (hG : MemLp G p volume) (hGc : HasCompactSupport G) :
    Integrable G volume := by
  have hfin : IsFiniteMeasure (volume.restrict (tsupport G)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hGc.measure_lt_top⟩
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp
    (MemLp.integrable hp (hG.restrict (tsupport G)))

/-- The Newtonian kernel is symmetric in its argument. -/
private lemma newtonianKernel_sub_comm (a b : Vec3) :
    newtonianKernel (a - b) = newtonianKernel (b - a) := by
  unfold newtonianKernel
  rw [show vec3EuclideanNorm (a - b) = vec3EuclideanNorm (b - a) by
    have h : a - b = (-1 : ℝ) • (b - a) := by
      rw [neg_smul, one_smul, neg_sub]
    rw [h, vec3EuclideanNorm_smul, abs_neg, abs_one, one_mul]]

/-- The derivative potential paired against a spatial derivative of a smooth
compactly supported test function equals the Newtonian potential of the mixed
second derivative paired against `G`.

The inner integral over `x` is the first-order adjoint identity of the
Newtonian kernel, and the remaining `y`-integration is the Fubini identity for
potentials against compactly supported data.  This is the pairing form of
`cor:CZ-harmonic` used to move derivatives off the pressure potential. -/
theorem pressureNewtonianDerivativePotential_pairing_potential
    {i j : Fin 3} {G ψ : Vec3 → ℝ}
    (hG : Integrable G volume) (hGc : HasCompactSupport G)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
      ∫ y, G y * pressureNewtonianPotential (mixedSecond ψ i j) y := by
  have hinner : ∀ y, ∫ x, spatialDeriv newtonianKernel i (x-y) *
      spatialDeriv ψ j x = pressureNewtonianPotential (mixedSecond ψ i j) y := by
    intro y
    rw [newtonian_derivative_kernel_adjoint hψ hψc i j]
    unfold pressureNewtonianPotential
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [newtonianKernel_sub_comm x y]
    ring
  exact pressureNewtonianDerivativePotential_pairing hG hGc
    (contDiff_spatialDeriv_smooth hψ j)
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)) hinner

end CKN.Foundation.Euclidean
