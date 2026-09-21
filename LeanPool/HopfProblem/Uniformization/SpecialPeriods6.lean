/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Foundations.TwoAffineCharts
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods5
import all LeanPool.HopfProblem.PeriodFamily.Core1

/-!
# Hopf problem: uniformization · special periods 6

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_isAdditiveSkewOver
    (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) :
    IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g)
      (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g) := by
  let H : Subgroup SpecialPeriods.TriangleGroup :=
    { carrier :=
        {g |
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g)}
      one_mem' := by
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation 1)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ 1)
        simpa only [map_one] using (isAdditiveSkewOver_one (X := ℍ))
      mul_mem' := by
        intro g h hg hh
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation (g * h))
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h))
        simpa only [map_mul] using (IsAdditiveSkewOver.mul hg hh)
      inv_mem' := by
        intro g hg
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g⁻¹)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g⁻¹)
        simpa only [map_inv] using (IsAdditiveSkewOver.inv hg) }
  have hgen :
    ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
        Set SpecialPeriods.TriangleGroup) ⊆
      H := by
    intro g hg
    rcases hg with rfl | rfl
    · change
        IsAdditiveSkewOver
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁)
      rw [SpecialPeriods.triangleGeometricRepresentation_generator₁,
        triangleAdditiveRepresentation_generator₁]
      exact isAdditiveSkewOver_skewPerm _ _
    · change
        IsAdditiveSkewOver
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂)
      rw [SpecialPeriods.triangleGeometricRepresentation_generator₂,
        triangleAdditiveRepresentation_generator₂]
      exact isAdditiveSkewOver_skewPerm _ _
  have hclosure :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      H :=
    (Subgroup.closure_le H).mpr hgen
  apply hclosure
  rw [SpecialPeriods.triangle_generators_generate]
  exact Subgroup.mem_top g

private def SpecialPeriods.BetaTorsor.triangleAdditiveShift (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : ℂ :=
  (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, 0)).2

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_apply (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (b : ℂ) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b) =
      (SpecialPeriods.triangleGeometricRepresentation g z,
        b + triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z) :=
  triangleAdditiveRepresentation_isAdditiveSkewOver φ₁ φ₂ h₁ h₂ g z b

@[simp]
private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_one (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ 1 z = 0 := by
  simp only [triangleAdditiveShift, map_one, Equiv.Perm.one_apply]

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_mul (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g h : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (g * h) z =
      triangleAdditiveShift φ₁ φ₂ h₁ h₂ g (SpecialPeriods.triangleGeometricRepresentation h z) +
        triangleAdditiveShift φ₁ φ₂ h₁ h₂ h z := by
  change (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h) (z, 0)).2 = _
  rw [map_mul, Equiv.Perm.mul_apply, triangleAdditiveRepresentation_apply,
    triangleAdditiveRepresentation_apply]
  simp only [zero_add, add_comm]

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_inv (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ g⁻¹ z =
      -triangleAdditiveShift φ₁ φ₂ h₁ h₂ g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) := by
  have h := triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂ g g⁻¹ z
  rw [mul_inv_cancel, triangleAdditiveShift_one] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

@[simp]
private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₁ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ z = φ₁ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₁, skewPerm_apply,
    zero_add]

@[simp]
private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₂ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ z = φ₂ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₂, skewPerm_apply,
    zero_add]

private theorem SpecialPeriods.BetaTorsor.additive_cocycle_holomorphic_mo1973_18030
    (b : SpecialPeriods.TriangleGroup → ℍ → ℂ) (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (h₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b SpecialPeriods.triangleGenerator₁))
    (h₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b SpecialPeriods.triangleGenerator₂))
    (g : SpecialPeriods.TriangleGroup) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g) := by
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact h₁
    · have he : g = SpecialPeriods.triangleGenerator₂ := Set.mem_singleton_iff.mp hg
      subst g
      exact h₂
  | one =>
    have he : b 1 = fun _ => 0 := funext hone
    rw [he]
    exact contMDiff_const
  | mul g h _ _ ihg
    ihh =>
    have he :
      b (g * h) = fun z => b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z :=
      funext (hmul g h)
    rw [he]
    exact (ihg.comp (SpecialPeriods.triangleGeometricRepresentation_holomorphic h)).add ihh
  | inv g _
    ihg =>
    have he : b g⁻¹ = fun z => -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) :=
      funext (hinv g)
    rw [he]
    exact (ihg.comp (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹)).neg

private def SpecialPeriods.BetaTorsor.additiveAffineCocycle_mo1973_18031
    (b : SpecialPeriods.TriangleGroup → ℍ → ℂ) (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hhol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g)) : SpecialPeriods.MuTorsor.AffineCocycle
    where
  scale _ _ := 1
  shift := b
  scale_one _ := rfl
  shift_one := hone
  scale_mul _ _ _ := by simp
  shift_mul g h z := by simpa only [Units.val_one, one_mul, add_comm] using hmul g h z
  scale_holomorphic _ := contMDiff_const
  shift_holomorphic := hhol

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_holomorphic (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, ∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z) = 0)
    (h₂ : ∀ z, ∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z) = 0)
    (hφ₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₁) (hφ₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₂)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleAdditiveShift φ₁ φ₂ h₁ h₂ g) := by
  refine
    additive_cocycle_holomorphic_mo1973_18030 (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
      (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂) (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
      (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) ?_ ?_ g
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ = φ₁ :=
      funext (triangleAdditiveShift_generator₁ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₁
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ = φ₂ :=
      funext (triangleAdditiveShift_generator₂ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₂

private def SpecialPeriods.BetaTorsor.triangleAdditiveCocycle (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, ∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z) = 0)
    (h₂ : ∀ z, ∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z) = 0)
    (hφ₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₁) (hφ₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₂) :
    SpecialPeriods.MuTorsor.AffineCocycle :=
  additiveAffineCocycle_mo1973_18031 (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂) (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_holomorphic φ₁ φ₂ h₁ h₂ hφ₁ hφ₂)

private def SpecialPeriods.BetaTorsor.covarianceSubgroup (b : SpecialPeriods.TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (β : ℍ → ℂ) : Subgroup SpecialPeriods.TriangleGroup
    where
  carrier := {g | ∀ z, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + b g z}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, hone, add_zero]
  mul_mem' := by
    intro g h hg hh z
    rw [map_mul, Equiv.Perm.mul_apply, hg, hh, hmul]
    abel
  inv_mem' := by
    intro g hg z
    have he := hg (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
    have hc :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) =
        z := by
      rw [map_inv]
      exact (SpecialPeriods.triangleGeometricRepresentation g).apply_symm_apply z
    rw [hc] at he
    rw [hinv, he]
    abel

private theorem
    SpecialPeriods.BetaTorsor.covariance_zpowers (b : SpecialPeriods.TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (β : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + b g z)
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (SpecialPeriods.triangleGeometricRepresentation h z) = β z + b h z :=
  (Subgroup.zpowers_le.mpr (show g ∈ covarianceSubgroup b hone hmul hinv β from hg)) hh z

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_product (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (hproduct : ∀ z, φ₁ (SpecialPeriods.Triangle.generatorTwoPerm z) + φ₂ z = -1) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂
        (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂) z =
      -1 := by
  rw [triangleAdditiveShift_mul, triangleAdditiveShift_generator₁,
    triangleAdditiveShift_generator₂, SpecialPeriods.triangleGeometricRepresentation_generator₂]
  exact hproduct z

private theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_cusp (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (hproduct : ∀ z, φ₁ (SpecialPeriods.Triangle.generatorTwoPerm z) + φ₂ z = -1) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleCuspGenerator z = 1 := by
  rw [SpecialPeriods.triangleCuspGenerator, triangleAdditiveShift_inv,
    triangleAdditiveShift_product φ₁ φ₂ h₁ h₂ hproduct]
  norm_num

private structure SpecialPeriods.BetaTorsor.Data where
  tau : ℍ → ℍ
  mu : ℍ → ℂ
  tau_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω tau
  mu_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω mu
  tau_covariant : SpecialPeriods.TauCovariant tau
  mu_one : ∀ z : ℍ, mu (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - mu z) / (tau z : ℂ)
  mu_two : ∀ z : ℍ, mu (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + mu z / (tau z : ℂ)

private def SpecialPeriods.BetaTorsor.Data.cocycle (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.MuTorsor.AffineCocycle :=
  SpecialPeriods.BetaTorsor.triangleAdditiveCocycle (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)
    (SpecialPeriods.BetaTorsor.phiOne_holomorphic D.tau_holomorphic D.mu_holomorphic)
    (SpecialPeriods.BetaTorsor.phiTwo_holomorphic D.tau_holomorphic D.mu_holomorphic)

private def SpecialPeriods.BetaTorsor.Data.shift (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.TriangleGroup → ℍ → ℂ :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)

@[simp]
private theorem SpecialPeriods.BetaTorsor.Data.cocycle_scale (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : D.cocycle.scale g z = 1 :=
  rfl

@[simp]
private theorem SpecialPeriods.BetaTorsor.Data.cocycle_shift (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : D.cocycle.shift g z = D.shift g z :=
  rfl

private theorem SpecialPeriods.BetaTorsor.Data.cocycle_fibreMap (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) :
    D.cocycle.fibreMap g z u = u + D.shift g z := by
  simp only [SpecialPeriods.MuTorsor.AffineCocycle.fibreMap, D.cocycle_scale, Units.val_one,
    one_mul, D.cocycle_shift]

@[simp]
private theorem
    SpecialPeriods.BetaTorsor.Data.shift_one (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    D.shift 1 z = 0 :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_one ..

private theorem SpecialPeriods.BetaTorsor.Data.shift_mul (D : SpecialPeriods.BetaTorsor.Data)
    (g h : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.shift (g * h) z =
      D.shift g (SpecialPeriods.triangleGeometricRepresentation h z) + D.shift h z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_mul ..

private theorem SpecialPeriods.BetaTorsor.Data.shift_inv (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.shift g⁻¹ z = -D.shift g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_inv ..

@[simp]
private theorem SpecialPeriods.BetaTorsor.Data.shift_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) :
    D.shift SpecialPeriods.triangleGenerator₁ z = SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₁ ..

@[simp]
private theorem SpecialPeriods.BetaTorsor.Data.shift_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) :
    D.shift SpecialPeriods.triangleGenerator₂ z = SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₂ ..

@[simp]
private theorem
    SpecialPeriods.BetaTorsor.Data.shift_cusp (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    D.shift SpecialPeriods.triangleCuspGenerator z = 1 :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_cusp
    (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu) (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)
    (SpecialPeriods.BetaTorsor.phi_product_relation D.tau_covariant D.mu_two) z

private theorem
    SpecialPeriods.BetaTorsor.Data.covariance_zpowers (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z : ℍ, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + D.shift g z)
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (SpecialPeriods.triangleGeometricRepresentation h z) = β z + D.shift h z :=
  SpecialPeriods.BetaTorsor.covariance_zpowers D.shift D.shift_one D.shift_mul D.shift_inv β g hg
    hh z

private def SpecialPeriods.BetaTorsor.Data.ellipticPrimitive (D : SpecialPeriods.BetaTorsor.Data) :
    Elliptic.Kind → ℍ → ℂ
  | .three => SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu
  | .four => SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu

private theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.ellipticPrimitive j) := by
  cases j
  · exact SpecialPeriods.BetaTorsor.primitiveOne_holomorphic D.tau_holomorphic D.mu_holomorphic
  · exact SpecialPeriods.BetaTorsor.primitiveTwo_holomorphic D.tau_holomorphic D.mu_holomorphic

private theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_generator
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) (z : ℍ) :
    D.ellipticPrimitive j
        (SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.Triangle.ellipticGenerator j) z) =
      D.ellipticPrimitive j z + D.shift (SpecialPeriods.Triangle.ellipticGenerator j) z := by
  cases j
  · change
      SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z) =
        SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu z +
          D.shift SpecialPeriods.triangleGenerator₁ z
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply, D.shift_generator₁]
    exact
      sub_eq_iff_eq_add'.mp
        (SpecialPeriods.BetaTorsor.primitiveOne_difference D.tau_covariant D.mu_one z)
  · change
      SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z) =
        SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu z +
          D.shift SpecialPeriods.triangleGenerator₂ z
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply, D.shift_generator₂]
    exact
      sub_eq_iff_eq_add'.mp
        (SpecialPeriods.BetaTorsor.primitiveTwo_difference D.tau_covariant D.mu_two z)

private theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_additive
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) {g : SpecialPeriods.TriangleGroup}
    (hg : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j) (z : ℍ) :
    D.ellipticPrimitive j (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.ellipticPrimitive j z + D.shift g z := by
  apply
    D.covariance_zpowers (D.ellipticPrimitive j) (SpecialPeriods.Triangle.ellipticGenerator j)
      (D.ellipticPrimitive_generator j)
  simpa only [SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers] using hg

private theorem SpecialPeriods.BetaTorsor.Data.cuspPrimitive_generator
    (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
        (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z) =
      SpecialPeriods.BetaTorsor.cuspPrimitive D.tau z +
        D.shift SpecialPeriods.triangleCuspGenerator z := by
  rw [D.shift_cusp]
  exact
    sub_eq_iff_eq_add'.mp (SpecialPeriods.BetaTorsor.cuspPrimitive_difference D.tau_covariant z)

private theorem
    SpecialPeriods.BetaTorsor.Data.cuspPrimitive_additive (D : SpecialPeriods.BetaTorsor.Data)
    {g : SpecialPeriods.TriangleGroup}
    (hg : g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator) (z : ℍ) :
    SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
        (SpecialPeriods.triangleGeometricRepresentation g z) =
      SpecialPeriods.BetaTorsor.cuspPrimitive D.tau z + D.shift g z :=
  D.covariance_zpowers (SpecialPeriods.BetaTorsor.cuspPrimitive D.tau)
    SpecialPeriods.triangleCuspGenerator D.cuspPrimitive_generator hg z

private def SpecialPeriods.BetaTorsor.Data.regularSeed (D : SpecialPeriods.BetaTorsor.Data)
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (SpecialPeriods.MuTorsor.Cover.regularPatch x).Seed D.cocycle
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    rw [hg, D.cocycle.fibreMap_one]

private def SpecialPeriods.BetaTorsor.Data.ellipticSeed (D : SpecialPeriods.BetaTorsor.Data)
    (j : Elliptic.Kind) : (SpecialPeriods.MuTorsor.Cover.ellipticPatch j).Seed D.cocycle
    where
  toFun := D.ellipticPrimitive j
  holomorphic := (D.ellipticPrimitive_holomorphic j).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.ellipticPrimitive_additive j g.property z

private def SpecialPeriods.BetaTorsor.Data.cuspSeed (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.MuTorsor.Cover.cuspPatch.Seed D.cocycle
    where
  toFun := SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
  holomorphic :=
    (SpecialPeriods.BetaTorsor.cuspPrimitive_holomorphic D.tau_holomorphic).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.cuspPrimitive_additive g.property z

private def SpecialPeriods.BetaTorsor.Data.seed (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    (SpecialPeriods.MuTorsor.Cover.patch i).Seed D.cocycle :=
  match i with
  | none => D.cuspSeed
  | some (.inl x) => D.regularSeed x
  | some (.inr j) => D.ellipticSeed j

private def SpecialPeriods.BetaTorsor.Data.localSection (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) : ℍ → ℂ :=
  (D.seed i).extend

private theorem SpecialPeriods.BetaTorsor.Data.localSection_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (i : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i)
      (SpecialPeriods.MuTorsor.Cover.patch i).saturation :=
  (D.seed i).extend_holomorphic

private theorem
    SpecialPeriods.BetaTorsor.Data.localSection_additive (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz : z ∈ (SpecialPeriods.MuTorsor.Cover.patch i).saturation) :
    D.localSection i (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z := by
  have he := (D.seed i).extend_equivariant g z hz
  rwa [D.cocycle_fibreMap] at he

private theorem
    SpecialPeriods.BetaTorsor.Data.localSection_cusp (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    D.localSection SpecialPeriods.MuTorsor.Cover.cuspIndex z = -(D.tau z : ℂ) :=
  D.cuspSeed.extend_eq z hz

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.patchSaturation (i : SpecialPeriods.MuTorsor.Cover.Index) :
    TopologicalSpace.Opens ℍ :=
  ⟨(SpecialPeriods.MuTorsor.Cover.patch i).saturation,
    (SpecialPeriods.MuTorsor.Cover.patch i).saturation_isOpen⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.patchSaturation_invariant
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ patchSaturation i ↔
      z ∈ patchSaturation i :=
  (SpecialPeriods.MuTorsor.Cover.patch i).saturation_invariant g z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.overlapDomain (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    TopologicalSpace.Opens ℍ :=
  patchSaturation i ⊓ patchSaturation j

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.overlapDomain_invariant
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ overlapDomain i j ↔
      z ∈ overlapDomain i j :=
  (patchSaturation_invariant i g z).and (patchSaturation_invariant j g z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_mem_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ) :
    finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ↔
      z ∈ patchSaturation i := by
  rw [SpecialPeriods.MuTorsor.Cover.finitePatch, finiteProjection_mem_pullback π hπ]
  change
    z ∈
        SpecialPeriods.triangleCompactifiedProjection ⁻¹'
          (SpecialPeriods.MuTorsor.Cover.compactPatch i :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ↔
      _
  rw [SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_projection]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteProjection_preimage_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    finiteProjection π ⁻¹' (SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ) =
      patchSaturation i := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteDescentDomain_overlap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    finiteDescentDomain π hπ (overlapDomain i j) =
      SpecialPeriods.MuTorsor.Cover.finitePatch π i ⊓
        SpecialPeriods.MuTorsor.Cover.finitePatch π j := by
  ext t
  obtain ⟨z, rfl⟩ := finiteProjection_surjective π hπ t
  change
    finiteProjection π z ∈ finiteDescentDomain π hπ (overlapDomain i j) ↔
      finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ∧
        finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π j
  rw [finiteDescentDomain_projection π hπ _ (overlapDomain_invariant i j)]
  change
    z ∈ patchSaturation i ∧ z ∈ patchSaturation j ↔
      finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ∧
        finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π j
  rw [finiteProjection_mem_patch π hπ i, finiteProjection_mem_patch π hπ j]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.Data.overlapDifference (D : SpecialPeriods.BetaTorsor.Data)
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ) : ℂ :=
  D.localSection i z - D.localSection j z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.overlapDifference_invariant
    (D : SpecialPeriods.BetaTorsor.Data) (i j : SpecialPeriods.MuTorsor.Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz : z ∈ SpecialPeriods.BetaTorsor.overlapDomain i j) :
    D.overlapDifference i j (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.overlapDifference i j z := by
  dsimp only [overlapDifference]
  rw [D.localSection_additive i g z hz.1, D.localSection_additive j g z hz.2]
  ring

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.overlapDifference_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain i j) :=
  ((D.localSection_holomorphic i).mono (fun _ hz => hz.1)).sub
    ((D.localSection_holomorphic j).mono (fun _ hz => hz.2))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.Data.overlapCocycle (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteDescent π hπ (SpecialPeriods.BetaTorsor.overlapDomain i j)
    (D.overlapDifference i j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.overlapCocycle_analytic
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    AnalyticOnNhd ℂ (D.overlapCocycle π hπ i j)
      ((SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ) ∩
        SpecialPeriods.MuTorsor.Cover.finitePatch π j) := by
  have h :=
    SpecialPeriods.BetaTorsor.finiteDescent_analytic π hπ
      (SpecialPeriods.BetaTorsor.overlapDomain i j) (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
      (D.overlapDifference_holomorphic i j)
  rw [SpecialPeriods.BetaTorsor.finiteDescentDomain_overlap] at h
  exact h

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.localSection_difference
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ)
    (hi :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π i)
    (hj :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π j) :
    D.localSection i z - D.localSection j z =
      D.overlapCocycle π hπ i j (SpecialPeriods.BetaTorsor.finiteProjection π z) :=
  (SpecialPeriods.BetaTorsor.finiteDescent_projection π hπ
      (SpecialPeriods.BetaTorsor.overlapDomain i j) (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
      ⟨(SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ i z).mp hi,
        (SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ j z).mp hj⟩).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.localSection_holomorphic_finite
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i)
      (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹'
        (SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ)) := by
  rw [SpecialPeriods.BetaTorsor.finiteProjection_preimage_patch π hπ]
  exact D.localSection_holomorphic i

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.localSection_additive_finite
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π i) :
    D.localSection i (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z :=
  D.localSection_additive i g z
    ((SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ i z).mp hz)

private theorem
    SpecialPeriods.BetaTorsorGluing.descended_difference_cocycle {X ι : Type*} {π : X → ℂ}
    (hπ : Function.Surjective π) {U : ι → Set ℂ} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k → h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hπ w
  rw [← hdiff i j z hi hj, ← hdiff j k z hj hk, ← hdiff i k z hi hk]
  ring

private def SpecialPeriods.BetaTorsorGluing.correctedGlue {X ι : Type*} (π : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (βlocal : ι → X → ℂ) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R) (z : X) : ℂ :=
  βlocal (hcover (π z)).choose z - c.localPart (hcover (π z)).choose (π z)

private theorem
    SpecialPeriods.BetaTorsorGluing.correctedGlue_eq {X ι : Type*} {π : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) {i : ι}
    {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c z = βlocal i z - c.localPart i (π z) := by
  let j := (hcover (π z)).choose
  have hj : π z ∈ U j := (hcover (π z)).choose_spec
  change βlocal j z - c.localPart j (π z) = βlocal i z - c.localPart i (π z)
  have hb := hdiff j i z hj hz
  have hc := c.equation j i (π z) hj hz
  linear_combination hb - hc

private theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_eventuallyEq {X ι : Type*}
    [TopologicalSpace X] {π : X → ℂ} (hπ : Continuous π) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) {i : ι}
    {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c =ᶠ[𝓝 z] fun w => βlocal i w - c.localPart i (π w) := by
  filter_upwards [((hU i).preimage hπ).mem_nhds hz] with w hw
  exact correctedGlue_eq c hdiff hw

private theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_holomorphic {ι : Type*} {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ} {i₀ : ι}
    {R : ℝ} (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (π z)
  have hb : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) z :=
    (hβ i).contMDiffAt (((hU i).preimage hπ.continuous).mem_nhds hi)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => c.localPart i (π w)) z :=
    (c.local_analytic i (π z) hi).contDiffAt.contMDiffAt.comp z (hπ z)
  exact (hb.sub hc).congr_of_eventuallyEq (correctedGlue_eventuallyEq hπ.continuous hU c hdiff hi)

private theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_additive_law {X ι : Type*} {G : Type*}
    {π : X → ℂ} {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z))
    (A : G → X → X) (δ : G → X → ℂ) (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z) (g : G) (z : X) :
    correctedGlue π U hcover βlocal c (A g z) = correctedGlue π U hcover βlocal c z + δ g z := by
  obtain ⟨i, hi⟩ := hcover (π z)
  have hiA : π (A g z) ∈ U i := by rwa [hπA g z]
  rw [correctedGlue_eq c hdiff hiA, correctedGlue_eq c hdiff hi, hπA g z, hβA i g z hi]
  ring

private theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_cusp {X ι : Type*} {π : X → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι}
    {R : ℝ} (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z))
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) {τ : X → ℂ} {W : Set X}
    (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) {z : X} (hz : z ∈ W) (hlarge : R < ‖π z‖) :
    correctedGlue π U hcover βlocal c z + τ z = -c.infinityPart (π z)⁻¹ := by
  have hzU : π z ∈ U i₀ :=
    hRU
      (by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq c hdiff hzU, hβ₀ z hz, c.atInfinity (π z) hlarge]
  ring

private theorem SpecialPeriods.BetaTorsorGluing.exists_corrected_gluing {ι : Type*} {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Function.Surjective π) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) (i₀ : ι)
    {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) ∧
        ∀ i,
          Set.EqOn (correctedGlue π U hcover βlocal c) (fun z => βlocal i z - c.localPart i (π z))
            (π ⁻¹' U i) := by
  obtain ⟨c⟩ :=
    HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution hU hcover hh
      (descended_difference_cocycle hπsurj hdiff) i₀ hR hRU
  exact ⟨c, correctedGlue_holomorphic hπ hU hβ c hdiff, fun _ _ hz => correctedGlue_eq c hdiff hz⟩

private theorem SpecialPeriods.BetaTorsorGluing.exists_glued_beta_with_cusp {ι : Type*} {G : Type*}
    {π : ℍ → ℂ} (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Function.Surjective π) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) (i₀ : ι)
    {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) (A : G → ℍ → ℍ) (δ : G → ℍ → ℂ)
    (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z) (τ : ℍ → ℂ) (W : Set ℍ)
    (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) :
    ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
        AnalyticOnNhd ℂ B (Metric.ball 0 R⁻¹) ∧
          B 0 = 0 ∧
            (∀ g z, β (A g z) = β z + δ g z) ∧ ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹ := by
  obtain ⟨c, hc, _⟩ := exists_corrected_gluing hπ hπsurj hU hcover hβ hh hdiff i₀ hR hRU
  refine
    ⟨correctedGlue π U hcover βlocal c, fun u => -c.infinityPart u, hc, c.infinity_analytic.neg,
      ?_, ?_, ?_⟩
  · change -c.infinityPart 0 = 0
    rw [c.infinity_zero, neg_zero]
  · exact correctedGlue_additive_law c hdiff A δ hπA hβA
  · intro z hz hlarge
    exact correctedGlue_cusp c hdiff hRU hβ₀ hz hlarge

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.Data.GeneratorLaws (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) : Prop :=
  (∀ z : ℍ,
      β (SpecialPeriods.Triangle.generatorOneSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z) ∧
    (∀ z : ℍ,
      β (SpecialPeriods.Triangle.generatorTwoSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.generatorLaws_of_all_words
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ}
    (hβ :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + D.shift g z) :
    D.GeneratorLaws β := by
  constructor
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      D.shift_generator₁] using hβ SpecialPeriods.triangleGenerator₁ z
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      D.shift_generator₂] using hβ SpecialPeriods.triangleGenerator₂ z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.GeneratorLaws.add_const
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (c : ℂ) :
    D.GeneratorLaws (fun z => β z + c) := by
  constructor
  · intro z
    dsimp only
    rw [hβ.1 z]
    ring
  · intro z
    dsimp only
    rw [hβ.2 z]
    ring

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.BetaTorsor.Data.exists_global_beta (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ R : ℝ,
      0 < R ∧
        ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
            D.GeneratorLaws β ∧
              AnalyticOnNhd ℂ B (Metric.ball 0 R⁻¹) ∧
                B 0 = 0 ∧
                  ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
                    R < ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖ →
                      β z + (D.tau z : ℂ) =
                        B (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  obtain ⟨R, hR, hRU⟩ := SpecialPeriods.MuTorsor.Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨β, B, hβ, hB, hB0, hwords, hcusp⟩ :=
    SpecialPeriods.BetaTorsorGluing.exists_glued_beta_with_cusp
      (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)
      (SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ)
      (fun i => (SpecialPeriods.MuTorsor.Cover.finitePatch π i).isOpen)
      (SpecialPeriods.MuTorsor.Cover.exists_finitePatch π)
      (D.localSection_holomorphic_finite π hπ) (D.overlapCocycle_analytic π hπ)
      (D.localSection_difference π hπ) SpecialPeriods.MuTorsor.Cover.cuspIndex hR hRU
      (fun g z => SpecialPeriods.triangleGeometricRepresentation g z) D.shift
      (SpecialPeriods.BetaTorsor.finiteProjection_invariant π)
      (D.localSection_additive_finite π hπ) (fun z => (D.tau z : ℂ))
      (SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) D.localSection_cusp
  exact ⟨R, hR, β, B, hβ, D.generatorLaws_of_all_words hwords, hB, hB0, hcusp⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.qExtension
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (B : ℂ → ℂ) (q : ℂ) : ℂ :=
  B (SpecialPeriods.MuTorsor.CuspCoordinates.t π q)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.qExtension_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (B : ℂ → ℂ) :
    qExtension π B 0 = B 0 := by
  rw [qExtension, SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.qExtension_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) : AnalyticAt ℂ (qExtension π B) 0 := by
  have ht : AnalyticAt ℂ B (SpecialPeriods.MuTorsor.CuspCoordinates.t π 0) := by
    rw [SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ]
    exact hB
  exact ht.comp (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.cusp_formula_eventually_q
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      β z + (τ z : ℂ) = qExtension π B (SpecialPeriods.Triangle.cuspQ z) := by
  filter_upwards [SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc
      SpecialPeriods.Triangle.width,
    SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R,
    SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hz hRz ht
  rw [hformula z hz hRz]
  change
    B (finiteProjection π z)⁻¹ =
      B (SpecialPeriods.MuTorsor.CuspCoordinates.t π (SpecialPeriods.Triangle.cuspQ z))
  rw [ht]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.analytic_cusp_formula_to_q_extension
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ C : ℂ → ℂ,
      AnalyticAt ℂ C 0 ∧
        C 0 = B 0 ∧
          ∃ Y : ℝ, ∀ z : ℍ, Y < z.im → β z + (τ z : ℂ) = C (SpecialPeriods.Triangle.cuspQ z) := by
  refine ⟨qExtension π B, qExtension_analyticAt_zero π hπ hB, qExtension_zero π hπ B, ?_⟩
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp (cusp_formula_eventually_q π hπ hformula)
  exact ⟨Y, fun z hz => hY z hz.le⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.tendsto_of_analytic_cusp_formula
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    Filter.Tendsto (fun z : ℍ => β z + (τ z : ℂ)) UpperHalfPlane.atImInfty (𝓝 (B 0)) := by
  have hlim :
    Filter.Tendsto (fun z : ℍ => B (finiteProjection π z)⁻¹) UpperHalfPlane.atImInfty (𝓝 (B 0)) :=
    hB.continuousAt.tendsto.comp
      ((SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_inv_tendsto_zero π hπ).mono_right
        nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc
      SpecialPeriods.Triangle.width,
    SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R] with z hz
    hRz
  exact (hformula z hz hRz).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.bounded_of_analytic_cusp_formula
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (τ z : ℂ)‖ ≤ M := by
  have hlim := (tendsto_of_analytic_cusp_formula π hπ hB hformula).norm
  have hbound : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖β z + (τ z : ℂ)‖ < ‖B 0‖ + 1 :=
    hlim.eventually (Iio_mem_nhds (lt_add_one ‖B 0‖))
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound
  exact ⟨Y, ‖B 0‖ + 1, fun z hz => (hY z hz.le).le⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private structure SpecialPeriods.BetaTorsor.Data.IsSolution (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β
  generators : D.GeneratorLaws β
  cusp_bounded : ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (D.tau z : ℂ)‖ ≤ M

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.Data.exists_solution_with_cusp_extension
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ (β : ℍ → ℂ) (C : ℂ → ℂ),
      D.IsSolution β ∧
        AnalyticAt ℂ C 0 ∧
          C 0 = 0 ∧
            ∃ Y : ℝ,
              ∀ z : ℍ, Y < z.im → β z + (D.tau z : ℂ) = C (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨R, hR, β, B, hβ, hgen, hB, hB0, hformula⟩ := D.exists_global_beta π hπ
  have hBzero : AnalyticAt ℂ B 0 := hB 0 (Metric.mem_ball_self (inv_pos.mpr hR))
  obtain ⟨Y, M, hbound⟩ :=
    SpecialPeriods.BetaTorsor.bounded_of_analytic_cusp_formula π hπ hBzero hformula
  obtain ⟨C, hC, hC0, Y', hCformula⟩ :=
    SpecialPeriods.BetaTorsor.analytic_cusp_formula_to_q_extension π hπ hBzero hformula
  exact ⟨β, C, ⟨hβ, hgen, Y, M, hbound⟩, hC, hC0.trans hB0, Y', hCformula⟩

private theorem
    SpecialPeriods.exists_compact_cutoff_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ) (hf : Filter.Tendsto f (𝓝[≠] p) Filter.atBot) :
    ∃ K : Set B,
      IsCompact K ∧ K ⊆ ({ p } : Set B)ᶜ ∧ ∀ x : B, x ∈ ({ p } : Set B)ᶜ → x ∉ K → f x < 0 := by
  obtain ⟨U, hU, hpU, hUf⟩ := mem_nhdsWithin.mp (hf.eventually_lt_atBot 0)
  refine ⟨Uᶜ, hU.isClosed_compl.isCompact, ?_, ?_⟩
  · intro x hx hp
    have hxp : x = p := by simpa only [Set.mem_singleton_iff] using hp
    exact hx (hxp ▸ hpU)
  · intro x hxp hx
    exact hUf ⟨Classical.not_not.mp hx, hxp⟩

private theorem
    SpecialPeriods.bddAbove_image_punctured_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ) (hc : ContinuousOn f ({ p } : Set B)ᶜ)
    (hf : Filter.Tendsto f (𝓝[≠] p) Filter.atBot) : BddAbove (f '' ({ p } : Set B)ᶜ) := by
  obtain ⟨K, hK, hKp, hneg⟩ := exists_compact_cutoff_of_tendsto_atBot p f hf
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.mono hKp)
  refine ⟨Max.max C 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxK : x ∈ K
  · exact (hC (Set.mem_image_of_mem f hxK)).trans (le_max_left _ _)
  · exact (hneg x hx hxK).le.trans (le_max_right _ _)

private def
    SpecialPeriods.BetaTorsor.Data.periodPoint (D : SpecialPeriods.BetaTorsor.Data) (β : ℍ → ℂ)
    (z : ℍ) : PeriodPoint :=
  ⟨(D.tau z : ℂ), D.mu z, β z⟩

private def
    SpecialPeriods.BetaTorsor.Data.periodMap (D : SpecialPeriods.BetaTorsor.Data) (β : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible) :
    HolomorphicPeriodMap ℂ ℍ
    where
  point z := ⟨D.periodPoint β z, hAdm z⟩
  holomorphic_tau := UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic
  holomorphic_mu := D.mu_holomorphic
  holomorphic_beta := hβ

private def SpecialPeriods.BetaTorsor.Data.shiftedPeriodMap (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) : HolomorphicPeriodMap ℂ ℍ :=
  D.periodMap (fun z => β z + c) (hβ.add contMDiff_const) hAdm

private def
    SpecialPeriods.triangleRealRepresentation : TriangleGroup →* (RealPlane₄ ≃ₗ[ℝ] RealPlane₄) :=
  Matrix.SpecialLinearGroup.toLin'.comp
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp triangleDualRepresentation)

/-- The real-linear equivalence induced by an element of the triangle group. -/
public
def SpecialPeriods.triangleRealEquiv (g : TriangleGroup) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄ :=
  triangleRealRepresentation g

private theorem SpecialPeriods.triangleRealEquiv_apply (g : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv g x =
      (triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x :=
  rfl

@[simp]
private theorem SpecialPeriods.triangleRealEquiv_one :
    triangleRealEquiv 1 = LinearEquiv.refl ℝ RealPlane₄ :=
  triangleRealRepresentation.map_one

private theorem SpecialPeriods.triangleRealEquiv_mul (g h : TriangleGroup) :
    triangleRealEquiv (g * h) = triangleRealEquiv g * triangleRealEquiv h :=
  triangleRealRepresentation.map_mul g h

private theorem SpecialPeriods.triangleRealEquiv_mul_apply (g h : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv (g * h) x = triangleRealEquiv g (triangleRealEquiv h x) := by
  rw [triangleRealEquiv_mul]
  rfl

@[simp]
private theorem SpecialPeriods.triangleRealEquiv_inv (g : TriangleGroup) :
    triangleRealEquiv g⁻¹ = (triangleRealEquiv g).symm :=
  triangleRealRepresentation.map_inv g

private theorem SpecialPeriods.triangleRealEquiv_realCast (g : TriangleGroup) (v : Lattice) :
    triangleRealEquiv g (Elliptic.realCast v) =
      Elliptic.realCast ((triangleDualRepresentation g : LatticeMatrix) *ᵥ v) := by
  rw [triangleRealEquiv_apply]
  ext i
  exact
    (RingHom.map_mulVec (Int.castRingHom ℝ) (triangleDualRepresentation g : LatticeMatrix) v
        i).symm

private theorem
    SpecialPeriods.triangleRealEquiv_mem_standardLattice (g : TriangleGroup) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : triangleRealEquiv g x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact
    (Elliptic.standardLattice_mem_iff _).mpr
      ⟨(triangleDualRepresentation g : LatticeMatrix) *ᵥ v, triangleRealEquiv_realCast g v⟩

private theorem SpecialPeriods.triangleRealEquiv_map_standardLattice (g : TriangleGroup) :
    standardLattice.map ((triangleRealEquiv g).restrictScalars ℤ).toLinearMap = standardLattice :=
  by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact triangleRealEquiv_mem_standardLattice g hy
  · intro hx
    refine ⟨triangleRealEquiv g⁻¹ x, triangleRealEquiv_mem_standardLattice g⁻¹ hx, ?_⟩
    change triangleRealEquiv g (triangleRealEquiv g⁻¹ x) = x
    rw [triangleRealEquiv_inv, LinearEquiv.apply_symm_apply]

private def
    SpecialPeriods.triangleTorusLinearEquiv (g : TriangleGroup) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice
    ((triangleRealEquiv g).restrictScalars ℤ) (triangleRealEquiv_map_standardLattice g)

private def SpecialPeriods.triangleTorusHomeomorph (g : TriangleGroup) : RealTorus₄ ≃ₜ RealTorus₄
    where
  toEquiv := (triangleTorusLinearEquiv g).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp (triangleRealEquiv g).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (triangleRealEquiv g).symm.toContinuousLinearEquiv.continuous

private theorem SpecialPeriods.triangleTorusHomeomorph_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    triangleTorusHomeomorph g (standardLattice.mkQ x) =
      standardLattice.mkQ (triangleRealEquiv g x) :=
  rfl

@[simp]
private theorem SpecialPeriods.triangleTorusHomeomorph_zero (g : TriangleGroup) :
    triangleTorusHomeomorph g 0 = 0 :=
  (triangleTorusLinearEquiv g).map_zero

private theorem SpecialPeriods.triangleTorusHomeomorph_add (g : TriangleGroup) (x y : RealTorus₄) :
    triangleTorusHomeomorph g (x + y) =
      triangleTorusHomeomorph g x + triangleTorusHomeomorph g y :=
  (triangleTorusLinearEquiv g).map_add x y

private theorem SpecialPeriods.triangleTorusHomeomorph_one_apply (x : RealTorus₄) :
    triangleTorusHomeomorph 1 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_one]
  rfl

@[simp]
private theorem SpecialPeriods.triangleTorusHomeomorph_one :
    triangleTorusHomeomorph 1 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_one_apply

private theorem
    SpecialPeriods.triangleTorusHomeomorph_mul_apply (g h : TriangleGroup) (x : RealTorus₄) :
    triangleTorusHomeomorph (g * h) x = triangleTorusHomeomorph g (triangleTorusHomeomorph h x) :=
  by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleTorusHomeomorph_mkQ, triangleTorusHomeomorph_mkQ,
    triangleRealEquiv_mul_apply]

private theorem SpecialPeriods.triangleTorusHomeomorph_mul (g h : TriangleGroup) :
    triangleTorusHomeomorph (g * h) =
      (triangleTorusHomeomorph h).trans (triangleTorusHomeomorph g) := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_mul_apply g h

@[simp]
private theorem SpecialPeriods.triangleTorusHomeomorph_inv (g : TriangleGroup) :
    triangleTorusHomeomorph g⁻¹ = (triangleTorusHomeomorph g).symm := by
  apply Homeomorph.ext
  intro x
  apply (triangleTorusHomeomorph g).injective
  rw [← triangleTorusHomeomorph_mul_apply, mul_inv_cancel, triangleTorusHomeomorph_one_apply,
    Homeomorph.apply_symm_apply]

@[instance_reducible]
private def SpecialPeriods.triangleTorusAction : MulAction TriangleGroup RealTorus₄
    where
  smul g x := triangleTorusHomeomorph g x
  one_smul := triangleTorusHomeomorph_one_apply
  mul_smul := triangleTorusHomeomorph_mul_apply

private theorem SpecialPeriods.triangleTorusAction_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    letI := triangleTorusAction
    g • standardLattice.mkQ x =
      standardLattice.mkQ
        ((triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x) := by
  change triangleTorusHomeomorph g (standardLattice.mkQ x) = _
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_apply]

@[simp]
private theorem SpecialPeriods.triangleTorusAction_zero (g : TriangleGroup) :
    letI := triangleTorusAction
    g • (0 : RealTorus₄) = 0 :=
  triangleTorusHomeomorph_zero g

private theorem SpecialPeriods.triangleTorusAction_continuous :
    letI := triangleTorusAction
    ContinuousConstSMul TriangleGroup RealTorus₄ := by
  let := triangleTorusAction
  exact ⟨fun g => (triangleTorusHomeomorph g).continuous⟩

private theorem SpecialPeriods.triangleTorusAction_generator₁_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₁ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .three x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₁_matrix]
  rfl

private theorem SpecialPeriods.triangleTorusAction_generator₂_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₂ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .four x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₂_matrix]
  rfl

private def SpecialPeriods.Triangle.firstSector : Set ℍ :=
  {z | z.re < -(1 / 2) ∧ 1 < ‖(z : ℂ)‖}

private def SpecialPeriods.Triangle.secondSector : Set ℍ :=
  {z | stripLeft < z.re ∧ stripRight < ‖(z : ℂ) - (stripLeft : ℂ)‖}

private def SpecialPeriods.Triangle.firstExcluded : Set ℍ :=
  {z | -(1 / 2) < z.re ∨ ‖(z : ℂ)‖ < 1}

private def SpecialPeriods.Triangle.secondExcluded : Set ℍ :=
  {z | z.re < stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ < stripRight}

private def SpecialPeriods.Triangle.circularDoubleInterior : Set ℍ :=
  firstSector ∩ secondSector

private theorem SpecialPeriods.Triangle.stripLeft_add_stripRight : stripLeft + stripRight = -1 := by
  unfold stripLeft stripRight
  ring

private theorem SpecialPeriods.Triangle.stripLeft_lt_neg_one : stripLeft < -1 := by
  linarith [stripLeft_add_stripRight, stripRight_pos]

private theorem
    SpecialPeriods.Triangle.firstExcluded_subset_pingPongOne : firstExcluded ⊆ pingPongOne := by
  intro z hz
  rcases hz with hx | hn
  · change -1 < z.re
    linarith
  · have hr := Complex.re_le_norm (-(z : ℂ))
    simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
    change -1 < z.re
    linarith

private theorem SpecialPeriods.Triangle.secondExcluded_subset_pingPongTwo :
    secondExcluded ⊆ pingPongTwo := by
  intro z hz
  rcases hz with hx | hn
  · exact hx.trans stripLeft_lt_neg_one
  · have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
    change z.re < -1
    linarith [stripLeft_add_stripRight]

private theorem
    SpecialPeriods.Triangle.pingPongTwo_subset_firstSector : pingPongTwo ⊆ firstSector := by
  intro z hz
  change z.re < -1 at hz
  refine ⟨by linarith, ?_⟩
  have hr := Complex.re_le_norm (-(z : ℂ))
  simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
  linarith

private theorem
    SpecialPeriods.Triangle.pingPongOne_subset_secondSector : pingPongOne ⊆ secondSector := by
  intro z hz
  change -1 < z.re at hz
  refine ⟨stripLeft_lt_neg_one.trans hz, ?_⟩
  have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
  simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
  linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.secondExcluded_subset_firstSector :
    secondExcluded ⊆ firstSector :=
  secondExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

private theorem SpecialPeriods.Triangle.firstExcluded_subset_secondSector :
    firstExcluded ⊆ secondSector :=
  firstExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

private theorem SpecialPeriods.Triangle.circularDoubleInterior_disjoint_firstExcluded :
    Disjoint circularDoubleInterior firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.1.1 hx
  · exact lt_asymm hz.1.2 hn

private theorem SpecialPeriods.Triangle.circularDoubleInterior_disjoint_secondExcluded :
    Disjoint circularDoubleInterior secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.2.1 hx
  · exact lt_asymm hz.2.2 hn

private theorem SpecialPeriods.Triangle.generatorOne_firstSector :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) firstSector firstExcluded := by
  intro z hz
  left
  change -(1 / 2) < (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (lt_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

private theorem SpecialPeriods.Triangle.norm_add_one_lt_norm_of_re_lt_half (z : ℍ)
    (hz : z.re < -(1 / 2)) : ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 < ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

private theorem SpecialPeriods.Triangle.generatorOne_sq_firstSector :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2) • z) firstSector firstExcluded := by
  intro z hz
  right
  change ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖ < 1
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr z.ne_zero)).mpr (norm_add_one_lt_norm_of_re_lt_half z hz.1)

private def SpecialPeriods.Triangle.secondShift_mo1973_18636 (z : ℍ) : ℂ :=
  (z : ℂ) - (stripLeft : ℂ)

private theorem SpecialPeriods.Triangle.secondShift_re_mo1973_18637 (z : ℍ) :
    (secondShift_mo1973_18636 z).re = z.re - stripLeft := by simp [secondShift_mo1973_18636]

private theorem SpecialPeriods.Triangle.secondShift_add_real_ne_zero_mo1973_18638 (z : ℍ)
    (a : ℝ) : secondShift_mo1973_18636 z + (a : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [secondShift_mo1973_18636, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    sub_zero, add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.stripLeft_eq_neg_stripRight_sub_one_mo1973_18639 :
    stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.width_eq_two_stripRight_add_one_mo1973_18640 :
    width = 2 * stripRight + 1 := by
  unfold stripRight
  ring

private theorem SpecialPeriods.Triangle.stripRight_sq_complex_mo1973_18641 :
    (stripRight : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, stripRight_sq]
  norm_num

private theorem SpecialPeriods.Triangle.generatorTwo_secondShift_mo1973_18642 (z : ℍ) :
    secondShift_mo1973_18636 (generatorTwoSL • z) =
      (stripRight : ℂ) * (secondShift_mo1973_18636 z - stripRight) /
        (secondShift_mo1973_18636 z + stripRight) := by
  have hd := secondShift_add_real_ne_zero_mo1973_18638 z stripRight
  have hs := stripRight_sq_complex_mo1973_18641
  unfold secondShift_mo1973_18636 at *
  rw [generatorTwoSL_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_18639,
    width_eq_two_stripRight_add_one_mo1973_18640] at *
  push_cast at *
  have he :
    (z : ℂ) + (2 * (stripRight : ℂ) + 1) = (z : ℂ) - (-(stripRight : ℂ) - 1) + stripRight := by
    ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.generatorTwo_sq_secondShift_mo1973_18643 (z : ℍ) :
    secondShift_mo1973_18636 ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) ^ 2 / secondShift_mo1973_18636 z := by
  have hz : secondShift_mo1973_18636 z ≠ 0 := by
    simpa using secondShift_add_real_ne_zero_mo1973_18638 z 0
  have hd := secondShift_add_real_ne_zero_mo1973_18638 z stripRight
  have hR : (stripRight : ℂ) ≠ 0 := by exact_mod_cast stripRight_pos.ne'
  rw [pow_two, SemigroupAction.mul_smul, generatorTwo_secondShift_mo1973_18642,
    generatorTwo_secondShift_mo1973_18642]
  field_simp [hz, hd, hR]
  ring

private theorem SpecialPeriods.Triangle.generatorTwo_cube_secondShift_mo1973_18644 (z : ℍ) :
    secondShift_mo1973_18636 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) * (secondShift_mo1973_18636 z + stripRight) /
        (secondShift_mo1973_18636 z - stripRight) := by
  have hd : secondShift_mo1973_18636 z - (stripRight : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_eq_add_neg] using
      secondShift_add_real_ne_zero_mo1973_18638 z (-stripRight)
  have hs := stripRight_sq_complex_mo1973_18641
  unfold secondShift_mo1973_18636 at *
  rw [generatorTwoSL_cube_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_18639,
    width_eq_two_stripRight_add_one_mo1973_18640] at *
  push_cast at *
  have he : (z : ℂ) + 1 = (z : ℂ) - (-(stripRight : ℂ) - 1) - stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.norm_sub_div_add_lt_one_mo1973_18645 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ < 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 < ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_pos hr hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_add_div_sub_pos_mo1973_18646 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : r < ‖u‖) : 0 < ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hd : u - (r : ℂ) ≠ 0 := by
    intro h
    have he : u = (r : ℂ) := sub_eq_zero.mp h
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hu
    exact lt_irrefl r hu
  have hsq : r ^ 2 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_pos ?_ (Complex.normSq_pos.mpr hd)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem SpecialPeriods.Triangle.re_neg_sq_div_neg_mo1973_18647 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : (-(r : ℂ) ^ 2 / u).re < 0 := by
  have hd : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hnum : -(r ^ 2) * u.re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hd)

private theorem SpecialPeriods.Triangle.generatorTwo_secondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inr ?_
  change ‖secondShift_mo1973_18636 (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift_mo1973_18642, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift_mo1973_18636 z).re := by
    rw [secondShift_re_mo1973_18637]
    exact sub_pos.mpr hz.1
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one_mo1973_18645 stripRight_pos hrez)
      stripRight_pos

private theorem SpecialPeriods.Triangle.generatorTwo_sq_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hrez : 0 < (secondShift_mo1973_18636 z).re := by
    rw [secondShift_re_mo1973_18637]
    exact sub_pos.mpr hz.1
  have h := re_neg_sq_div_neg_mo1973_18647 stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift_mo1973_18643 z, secondShift_re_mo1973_18637] at h
  exact sub_neg.mp h

private theorem SpecialPeriods.Triangle.generatorTwo_cube_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hnorm : stripRight < ‖secondShift_mo1973_18636 z‖ := hz.2
  have h : (secondShift_mo1973_18636 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re < 0 := by
    rw [generatorTwo_cube_secondShift_mo1973_18644, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, MulZeroClass.zero_mul, sub_zero]
    exact
      mul_neg_of_neg_of_pos (neg_neg_of_pos stripRight_pos)
        (re_add_div_sub_pos_mo1973_18646 stripRight_pos hnorm)
  rw [secondShift_re_mo1973_18637] at h
  exact sub_neg.mp h

private theorem SpecialPeriods.lift_neWord_domain_subset_mo1973_18651 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X : ι → Set α)
    (D : Set α) (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ X i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁ ih₂ =>
    calc
      Monoid.CoprodI.lift f (Monoid.CoprodI.NeWord.append w₁ hne w₂).prod • D =
          Monoid.CoprodI.lift f w₁.prod • Monoid.CoprodI.lift f w₂.prod • D := by
        simp [SemigroupAction.mul_smul]
      _ ⊆ Monoid.CoprodI.lift f w₁.prod • X k := (Set.smul_set_subset_smul_set_iff.mpr ih₂)
      _ ⊆ X i := Monoid.CoprodI.lift_word_ping_pong f X hpp w₁ hne

private theorem SpecialPeriods.tiling_cyclicPowerHom_two_mo1973_18652 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.tiling_cyclicPowerHom_three_mo1973_18653 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem SpecialPeriods.cyclicThree_domain_subset_mo1973_18654 {G α : Type*} [Group G]
    [MulAction G α] (a : G) (ha : a ^ 3 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => a • z) S T)
    (h₂ : Set.MapsTo (fun z => a ^ 2 • z) S T) (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) :
    cyclicPowerHom 3 a ha g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 3),
          x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
      g hg
  rcases hc with rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [tiling_cyclicPowerHom_two_mo1973_18652]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem SpecialPeriods.cyclicFour_domain_subset_mo1973_18655 {G α : Type*} [Group G]
    [MulAction G α] (b : G) (hb : b ^ 4 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => b • z) S T)
    (h₂ : Set.MapsTo (fun z => b ^ 2 • z) S T) (h₃ : Set.MapsTo (fun z => b ^ 3 • z) S T)
    (g : Multiplicative (ZMod 4)) (hg : g ≠ 1) : cyclicPowerHom 4 b hb g • S ⊆ T := by
  have hc :
    g = Multiplicative.ofAdd (1 : ZMod 4) ∨
      g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 4),
          x ≠ 1 →
            x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
      g hg
  rcases hc with rfl | rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [tiling_cyclicPowerHom_two_mo1973_18652]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [tiling_cyclicPowerHom_three_mo1973_18653]
    exact Set.smul_set_subset_iff.mpr h₃

private theorem
    SpecialPeriods.triangleLift_mapsTo_pingPongUnion {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (g : TriangleGroup) (hg : g ≠ 1) :
    Set.MapsTo (fun z => triangleLift a b ha hb g • z) D (X ∪ Y) := by
  classical
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i =>
      match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have hto_ne : toI g ≠ 1 := by
    intro h
    apply hg
    calc
      g = fromI (toI g) := (DFunLike.congr_fun hleft g).symm
      _ = 1 := by rw [h, map_one]
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_domain_subset_mo1973_18654 a ha Y X ha₁ ha₂ h hh
    · exact cyclicFour_domain_subset_mo1973_18655 b hb X Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ U i := by
    intro i h hh
    cases i
    · exact cyclicThree_domain_subset_mo1973_18654 a ha D X hDa₁ hDa₂ h hh
    · exact cyclicFour_domain_subset_mo1973_18655 b hb D Y hDb₁ hDb₂ hDb₃ h hh
  let : (i : Bool) → DecidableEq (H i) := fun _ => Classical.decEq _
  let r := Monoid.CoprodI.Word.equiv (M := H) (toI g)
  have hr : r.prod = toI g := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply (toI g)
  have hr_ne : r ≠ Monoid.CoprodI.Word.empty := by
    intro h
    apply hto_ne
    rw [← hr, h, Monoid.CoprodI.Word.prod_empty]
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word r hr_ne
  have hwprod : w.prod = toI g := by
    change w.toWord.prod = toI g
    rw [hw]
    exact hr
  have himage := lift_neWord_domain_subset_mo1973_18651 f U D hpp hstart w
  have hUi : U i ⊆ X ∪ Y := by
    cases i
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
    DFunLike.congr_fun hrepresentation g
  intro z hz
  rw [heval, ← hwprod]
  exact hUi (Set.smul_set_subset_iff.mp himage hz)

private theorem SpecialPeriods.triangleLift_disjoint_domain_translate {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (hDX : Disjoint D X) (hDY : Disjoint D Y) (g : TriangleGroup) (hg : g ≠ 1) :
    Disjoint D (triangleLift a b ha hb g • D) := by
  apply (hDX.sup_right hDY).mono_right
  exact
    Set.smul_set_subset_iff.mpr
      (triangleLift_mapsTo_pingPongUnion a b ha hb X Y D ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂
        hDb₃ g hg)

private theorem
    SpecialPeriods.triangleLift_eq_one_of_domain_mem {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (hDX : Disjoint D X) (hDY : Disjoint D Y) (g : TriangleGroup) {z : α} (hz : z ∈ D)
    (hgz : triangleLift a b ha hb g • z ∈ D) : g = 1 := by
  by_contra hg
  have hd :=
    triangleLift_disjoint_domain_translate a b ha hb X Y D ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂
      hDb₃ hDX hDY g hg
  exact hd.le_bot ⟨hgz, ⟨z, hz, rfl⟩⟩

private theorem SpecialPeriods.Triangle.generatorOnePerm_firstSector :
    Set.MapsTo (fun z : ℍ => generatorOnePerm z) firstSector firstExcluded :=
  generatorOne_firstSector

private theorem SpecialPeriods.Triangle.generatorOnePerm_sq_firstSector :
    Set.MapsTo (fun z : ℍ => (generatorOnePerm ^ 2) z) firstSector firstExcluded := by
  intro z hz
  change (generatorOnePerm ^ 2) z ∈ firstExcluded
  rw [generatorOnePerm_pow_apply]
  exact generatorOne_sq_firstSector hz

private theorem SpecialPeriods.Triangle.generatorTwoPerm_secondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoPerm z) secondSector secondExcluded :=
  generatorTwo_secondSector

private theorem SpecialPeriods.Triangle.generatorTwoPerm_sq_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoPerm ^ 2) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 2) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_sq_secondSector hz

private theorem SpecialPeriods.Triangle.generatorTwoPerm_cube_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoPerm ^ 3) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 3) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_cube_secondSector hz

private theorem SpecialPeriods.Triangle.eq_one_of_circularDoubleInterior_mem
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleInterior) : g = 1 :=
  by
  exact
    SpecialPeriods.triangleLift_eq_one_of_domain_mem generatorOnePerm generatorTwoPerm
      generatorOnePerm_cube generatorTwoPerm_fourth firstExcluded secondExcluded
      circularDoubleInterior
      (fun _ hw => generatorOnePerm_firstSector (secondExcluded_subset_firstSector hw))
      (fun _ hw => generatorOnePerm_sq_firstSector (secondExcluded_subset_firstSector hw))
      (fun _ hw => generatorTwoPerm_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_sq_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_cube_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorOnePerm_firstSector hw.1)
      (fun _ hw => generatorOnePerm_sq_firstSector hw.1)
      (fun _ hw => generatorTwoPerm_secondSector hw.2)
      (fun _ hw => generatorTwoPerm_sq_secondSector hw.2)
      (fun _ hw => generatorTwoPerm_cube_secondSector hw.2)
      circularDoubleInterior_disjoint_firstExcluded circularDoubleInterior_disjoint_secondExcluded
      g hz hgz

private def SpecialPeriods.Triangle.fordInterior : Set ℍ :=
  {z | stripLeft < z.re ∧ z.re < stripRight ∧ 1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖}

private theorem SpecialPeriods.Triangle.fordInterior_isOpen : IsOpen fordInterior :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
    ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const
            ((UpperHalfPlane.continuous_coe.add continuous_const).norm)).inter
        (isOpen_lt continuous_const UpperHalfPlane.continuous_coe.norm)))

private theorem
    SpecialPeriods.Triangle.fordInterior_subset_fordRegion : fordInterior ⊆ fordRegion := by
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

private theorem
    SpecialPeriods.Triangle.fordInterior_subset_secondSector : fordInterior ⊆ secondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 < stripRight * (z.re - stripLeft) := mul_pos stripRight_pos (sub_pos.mpr hz.1)
  have hs : stripRight ^ 2 < ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  nlinarith [norm_nonneg ((z : ℂ) - (stripLeft : ℂ)), stripRight_pos]

private theorem SpecialPeriods.Triangle.fordInterior_left_mem_circularDoubleInterior (z : ℍ)
    (hz : z ∈ fordInterior) (hx : z.re < -(1 / 2)) : z ∈ circularDoubleInterior :=
  ⟨⟨hx, hz.2.2.2⟩, fordInterior_subset_secondSector hz⟩

private theorem SpecialPeriods.Triangle.exists_mem_open_ne_re_and_image_re (e : ℍ ≃ₜ ℍ) (c : ℝ)
    (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) : ∃ z ∈ U, z.re ≠ c ∧ (e z).re ≠ c := by
  have hd : Dense {z : ℍ | z.re ≠ c} :=
    (dense_compl_singleton c).preimage UpperHalfPlane.isOpenMap_re
  have he : Dense {z : ℍ | (e z).re ≠ c} :=
    (dense_compl_singleton c).preimage (UpperHalfPlane.isOpenMap_re.comp e.isOpenMap)
  have ho : IsOpen {z : ℍ | z.re ≠ c} :=
    isOpen_compl_singleton.preimage UpperHalfPlane.continuous_re
  obtain ⟨z, hz⟩ :=
    he.inter_open_nonempty (U ∩ {z : ℍ | z.re ≠ c}) (hU.inter ho)
      (hd.inter_open_nonempty U hU hne)
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

private theorem SpecialPeriods.Triangle.norm_lt_norm_add_one_of_re_gt_half_mo1973_18679 (z : ℍ)
    (hx : -(1 / 2) < z.re) : ‖(z : ℂ)‖ < ‖(z : ℂ) + 1‖ := by
  have hsq : ‖(z : ℂ)‖ ^ 2 < ‖(z : ℂ) + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

private theorem SpecialPeriods.Triangle.norm_real_sub_inv_gt_mo1973_18680 {r : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 = 1 / 2) {u : ℂ} (hu : u ≠ 0) (hx : u.re < r) : r < ‖(r : ℂ) - u⁻¹‖ := by
  have he : (r : ℂ) - u⁻¹ = ((r : ℂ) * u - 1) / u := by field_simp
  have hnum : r ^ 2 * Complex.normSq u < Complex.normSq ((r : ℂ) * u - 1) := by
    simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, map_one, mul_one,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul, sub_zero]
    nlinarith [mul_lt_mul_of_pos_left hx hr]
  have hsq : r ^ 2 < ‖(r : ℂ) - u⁻¹‖ ^ 2 := by
    rw [he, Complex.sq_norm, Complex.normSq_div]
    exact (lt_div_iff₀ (Complex.normSq_pos.mpr hu)).mpr hnum
  nlinarith [norm_nonneg ((r : ℂ) - u⁻¹)]

private theorem SpecialPeriods.Triangle.fordInterior_right_mem_circularDoubleInterior (z : ℍ)
    (hz : z ∈ fordInterior) (hx : -(1 / 2) < z.re) :
    (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleInterior := by
  have hd : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.2]
  have hp : 0 < Complex.normSq (z : ℂ) := zero_lt_one.trans hd
  have hc : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hshift : 0 < Complex.normSq (z : ℂ) + 2 * z.re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hc ⊢
    nlinarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re < -(1 / 2)
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
      UpperHalfPlane.coe_re]
    have hfrac : -(1 / 2 : ℝ) < z.re / Complex.normSq (z : ℂ) :=
      (lt_div_iff₀ hp).mpr (by linarith)
    linarith
  · rw [generatorOneSL_sq_smul_coe]
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
      field_simp [z.ne_zero]
      ring
    rw [he, norm_neg, norm_div]
    exact
      (one_lt_div (norm_pos_iff.mpr z.ne_zero)).mpr
        (norm_lt_norm_add_one_of_re_gt_half_mo1973_18679 z hx)
  · change stripLeft < ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
      UpperHalfPlane.coe_re]
    have hfrac : z.re / Complex.normSq (z : ℂ) < stripRight := by
      apply (div_lt_iff₀ hp).mpr
      exact hz.2.1.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left hd stripRight_pos)
    linarith [stripLeft_add_stripRight]
  · rw [generatorOneSL_sq_smul_coe]
    have hL : stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]
    rw [hL]
    push_cast
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ - (-(stripRight : ℂ) - 1) = (stripRight : ℂ) - (z : ℂ)⁻¹ := by
      ring
    rw [he]
    exact norm_real_sub_inv_gt_mo1973_18680 stripRight_pos stripRight_sq z.ne_zero hz.2.1

private theorem SpecialPeriods.Triangle.generatorOne_not_mem_fordInterior (z : ℍ)
    (hz : z ∈ fordInterior) : generatorOneSL • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.2
  rw [generatorOneSL_smul_coe, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.1)

private theorem SpecialPeriods.Triangle.generatorOne_sq_not_mem_fordInterior (z : ℍ)
    (hz : z ∈ fordInterior) : (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.1
  have he : ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) + 1) = -(z : ℂ)⁻¹ := by
    rw [generatorOneSL_sq_smul_coe]
    ring
  rw [he, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.2)

@[instance_reducible]
private def SpecialPeriods.Triangle.instMulAction1 : MulAction SpecialPeriods.TriangleGroup ℍ :=
  SpecialPeriods.triangleGeometricAction

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.first_generator_inv_eq_sq_mo1973_18685 :
    SpecialPeriods.triangleGenerator₁⁻¹ = SpecialPeriods.triangleGenerator₁ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using SpecialPeriods.triangleGenerator₁_cube

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.first_generator_inv_apply_mo1973_18686 (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z =
      (generatorOneSL ^ 2) • z := by
  rw [first_generator_inv_eq_sq_mo1973_18685, map_pow,
    SpecialPeriods.triangleGeometricRepresentation_generator₁, generatorOnePerm_pow_apply]

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.right_mem_circularDouble_mo1973_18687 (z : ℍ)
    (hz : z ∈ fordInterior) (hx : -(1 / 2) < z.re) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z ∈
      circularDoubleInterior := by
  rw [first_generator_inv_apply_mo1973_18686]
  exact fordInterior_right_mem_circularDoubleInterior z hz hx

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.eq_one_of_fordInterior_mem_off_axis_mo1973_18688
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ fordInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ fordInterior)
    (hx : z.re ≠ -(1 / 2))
    (hgx : (SpecialPeriods.triangleGeometricRepresentation g z).re ≠ -(1 / 2)) : g = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hgx with hgx | hgx
  · exact
      eq_one_of_circularDoubleInterior_mem g
        (fordInterior_left_mem_circularDoubleInterior z hz hx)
        (fordInterior_left_mem_circularDoubleInterior _ hgz hgx)
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleGenerator₁⁻¹ * g) z ∈
        circularDoubleInterior := by
      change (SpecialPeriods.triangleGenerator₁⁻¹ * g) • z ∈ circularDoubleInterior
      simpa only [SemigroupAction.mul_smul, SpecialPeriods.triangleGeometricAction_smul] using
        right_mem_circularDouble_mo1973_18687 _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem (SpecialPeriods.triangleGenerator₁⁻¹ * g)
        (fordInterior_left_mem_circularDoubleInterior z hz hx) hm
    have hg : g = SpecialPeriods.triangleGenerator₁ := (inv_mul_eq_one.mp he).symm
    rw [hg, SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] at hgz
    exact False.elim (generatorOne_not_mem_fordInterior z hz hgz)
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation (g * SpecialPeriods.triangleGenerator₁)
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z) ∈
        circularDoubleInterior := by
      change
        (g * SpecialPeriods.triangleGenerator₁) • (SpecialPeriods.triangleGenerator₁⁻¹ • z) ∈
          circularDoubleInterior
      rw [SemigroupAction.mul_smul, smul_inv_smul, SpecialPeriods.triangleGeometricAction_smul]
      exact fordInterior_left_mem_circularDoubleInterior _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem (g * SpecialPeriods.triangleGenerator₁)
        (right_mem_circularDouble_mo1973_18687 z hz hx) hm
    have hg : g = SpecialPeriods.triangleGenerator₁⁻¹ := eq_inv_of_mul_eq_one_left he
    apply False.elim
    apply generatorOne_sq_not_mem_fordInterior z hz
    rw [hg, first_generator_inv_apply_mo1973_18686] at hgz
    exact hgz
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁)
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z) ∈
        circularDoubleInterior := by
      change
        (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁) •
            (SpecialPeriods.triangleGenerator₁⁻¹ • z) ∈
          circularDoubleInterior
      rw [SemigroupAction.mul_smul, smul_inv_smul, SemigroupAction.mul_smul]
      simpa only [SpecialPeriods.triangleGeometricAction_smul] using
        right_mem_circularDouble_mo1973_18687 _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem
        (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁)
        (right_mem_circularDouble_mo1973_18687 z hz hx) hm
    have he' :=
      congrArg
        (fun h : SpecialPeriods.TriangleGroup =>
          SpecialPeriods.triangleGenerator₁ * h * SpecialPeriods.triangleGenerator₁⁻¹)
        he
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one,
      mul_inv_cancel_left] using he'

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem
    SpecialPeriods.Triangle.eq_one_of_fordInterior_mem (g : SpecialPeriods.TriangleGroup)
    {z : ℍ} (hz : z ∈ fordInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ fordInterior) : g = 1 := by
  let U : Set ℍ :=
    fordInterior ∩ (SpecialPeriods.triangleGeometricRepresentation g) ⁻¹' fordInterior
  have hU : IsOpen U :=
    fordInterior_isOpen.inter
      (fordInterior_isOpen.preimage (SpecialPeriods.triangleGeometricBiholomorph g).continuous)
  have hne : U.Nonempty := ⟨z, hz, hgz⟩
  obtain ⟨w, hw, hx, hgx⟩ :=
    exists_mem_open_ne_re_and_image_re
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph (-(1 / 2)) U hU hne
  exact eq_one_of_fordInterior_mem_off_axis_mo1973_18688 g hw.1 hw.2 hx hgx

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.eq_one_of_fordInterior_eq (g : SpecialPeriods.TriangleGroup)
    {z w : ℍ} (hz : z ∈ fordInterior) (hw : w ∈ fordInterior)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) : g = 1 :=
  eq_one_of_fordInterior_mem g hz (hzw ▸ hw)

private def SpecialPeriods.Triangle.verticalReflection (a : ℝ) : ℍ ≃ₜ ℍ
    where
  toFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  invFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  left_inv z := by apply UpperHalfPlane.ext; simp
  right_inv z := by apply UpperHalfPlane.ext; simp
  continuous_toFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop
  continuous_invFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop

@[simp]
private theorem SpecialPeriods.Triangle.verticalReflection_re (a : ℝ) (z : ℍ) :
    (verticalReflection a z).re = a - z.re := by
  change ((a : ℂ) - conj (z : ℂ)).re = a - z.re
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, UpperHalfPlane.coe_re]

@[simp]
private theorem SpecialPeriods.Triangle.verticalReflection_im (a : ℝ) (z : ℍ) :
    (verticalReflection a z).im = z.im := by
  change ((a : ℂ) - conj (z : ℂ)).im = z.im
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.conj_im, zero_sub, neg_neg,
    UpperHalfPlane.coe_im]

private theorem SpecialPeriods.Triangle.verticalReflection_involutive (a : ℝ) :
    Function.Involutive (verticalReflection a) :=
  (verticalReflection a).left_inv

private theorem SpecialPeriods.Triangle.verticalReflection_fixed_iff (a : ℝ) (z : ℍ) :
    verticalReflection a z = z ↔ z.re = a / 2 := by
  constructor
  · intro h
    have hr := congrArg UpperHalfPlane.re h
    rw [verticalReflection_re] at hr
    linarith
  · intro h
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (verticalReflection a z).re = z.re
      rw [verticalReflection_re]
      linarith
    · exact verticalReflection_im a z

private def SpecialPeriods.Triangle.rightReflection : ℍ ≃ₜ ℍ :=
  verticalReflection (-1)

private def SpecialPeriods.Triangle.leftReflection : ℍ ≃ₜ ℍ :=
  verticalReflection (-(width + 1))

@[simp]
private theorem SpecialPeriods.Triangle.rightReflection_coe (z : ℍ) :
    (rightReflection z : ℂ) = -1 - conj (z : ℂ) := by simp [verticalReflection, rightReflection]

@[simp]
private theorem SpecialPeriods.Triangle.leftReflection_coe (z : ℍ) :
    (leftReflection z : ℂ) = -((width : ℂ) + 1) - conj (z : ℂ) := by
  simp [verticalReflection, leftReflection]

@[simp]
private theorem
    SpecialPeriods.Triangle.rightReflection_re (z : ℍ) : (rightReflection z).re = -1 - z.re :=
  by simp [rightReflection]

private theorem SpecialPeriods.Triangle.rightReflection_norm (z : ℍ) :
    ‖(rightReflection z : ℂ)‖ = ‖(z : ℂ) + 1‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj ((z : ℂ) + 1)‖ := by congr 1; simp; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

private theorem SpecialPeriods.Triangle.rightReflection_add_one_norm (z : ℍ) :
    ‖(rightReflection z : ℂ) + 1‖ = ‖(z : ℂ)‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj (z : ℂ)‖ := by congr 1; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

private theorem SpecialPeriods.Triangle.rightReflection_involutive :
    Function.Involutive rightReflection :=
  verticalReflection_involutive _

@[simp]
private theorem SpecialPeriods.Triangle.rightReflection_fixed_iff (z : ℍ) :
    rightReflection z = z ↔ z.re = -(1 / 2) := by
  simpa only [rightReflection, neg_div] using verticalReflection_fixed_iff (-1) z

@[simp]
private theorem SpecialPeriods.Triangle.leftReflection_fixed_iff (z : ℍ) :
    leftReflection z = z ↔ z.re = stripLeft :=
  verticalReflection_fixed_iff _ _

private theorem
    SpecialPeriods.Triangle.conjugate_denominatorOne_ne_zero (z : ℍ) : conj (z : ℂ) + 1 ≠ 0 :=
  by
  simpa only [map_add, map_one, map_ne_zero] using
    (map_ne_zero (starRingEnd ℂ)).mpr (denominatorOne_ne_zero z)

private def SpecialPeriods.Triangle.circleReflectionMap_mo1973_18716 (z : ℍ) : ℍ :=
  ⟨-1 + 1 / (conj (z : ℂ) + 1),
    by
    simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, zero_add,
      Complex.inv_im, Complex.conj_im, add_zero, neg_neg, UpperHalfPlane.coe_im]
    exact div_pos z.im_pos (Complex.normSq_pos.mpr (conjugate_denominatorOne_ne_zero z))⟩

private theorem SpecialPeriods.Triangle.circleReflectionMap_involutive_mo1973_18717 :
    Function.Involutive circleReflectionMap_mo1973_18716 := by
  intro z
  apply UpperHalfPlane.ext
  change -1 + 1 / (conj (-1 + 1 / (conj (z : ℂ) + 1)) + 1) = (z : ℂ)
  simp

private theorem SpecialPeriods.Triangle.circleReflectionMap_continuous_mo1973_18718 :
    Continuous circleReflectionMap_mo1973_18716 := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : ℍ => -1 + 1 / (conj (z : ℂ) + 1))
  exact
    continuous_const.add
      (continuous_const.div
        ((Complex.continuous_conj.comp UpperHalfPlane.continuous_coe).add continuous_const)
        conjugate_denominatorOne_ne_zero)

private def SpecialPeriods.Triangle.circleReflection : ℍ ≃ₜ ℍ
    where
  toFun := circleReflectionMap_mo1973_18716
  invFun := circleReflectionMap_mo1973_18716
  left_inv := circleReflectionMap_involutive_mo1973_18717
  right_inv := circleReflectionMap_involutive_mo1973_18717
  continuous_toFun := circleReflectionMap_continuous_mo1973_18718
  continuous_invFun := circleReflectionMap_continuous_mo1973_18718

@[simp]
private theorem SpecialPeriods.Triangle.circleReflection_coe (z : ℍ) :
    (circleReflection z : ℂ) = -1 + 1 / (conj (z : ℂ) + 1) :=
  rfl

private theorem SpecialPeriods.Triangle.circleReflection_involutive :
    Function.Involutive circleReflection :=
  circleReflectionMap_involutive_mo1973_18717

private theorem SpecialPeriods.Triangle.circleReflection_im (z : ℍ) :
    (circleReflection z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).im = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, zero_add,
    Complex.inv_im, Complex.normSq_conj, Complex.conj_im, add_zero, neg_neg,
    UpperHalfPlane.coe_im]

@[simp]
private theorem SpecialPeriods.Triangle.circleReflection_fixed_iff (z : ℍ) :
    circleReflection z = z ↔ ‖(z : ℂ) + 1‖ = 1 := by
  constructor
  · intro h
    have hi := congrArg UpperHalfPlane.im h
    rw [circleReflection_im] at hi
    have hd : Complex.normSq ((z : ℂ) + 1) ≠ 0 :=
      (Complex.normSq_pos.mpr (denominatorOne_ne_zero z)).ne'
    have hs : Complex.normSq ((z : ℂ) + 1) = 1 := by
      apply mul_left_cancel₀ z.im_ne_zero
      simpa only [mul_one] using ((div_eq_iff hd).mp hi).symm
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  · intro h
    apply UpperHalfPlane.ext
    rw [circleReflection_coe]
    have hs : Complex.normSq (conj (z : ℂ) + 1) = 1 := by
      rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp, Complex.normSq_conj,
        Complex.normSq_eq_norm_sq, h]
      norm_num
    simp [one_div, Complex.inv_def, hs]

@[simp]
private theorem SpecialPeriods.Triangle.rightReflection_mem_fordRegion_iff (z : ℍ) :
    rightReflection z ∈ fordRegion ↔ z ∈ fordRegion := by
  simp only [fordRegion, Set.mem_ofPred_eq, rightReflection_re, rightReflection_add_one_norm,
    rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

private theorem SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion :
    Set.MapsTo rightReflection fordRegion fordRegion := fun z hz =>
  (rightReflection_mem_fordRegion_iff z).mpr hz

private theorem SpecialPeriods.Triangle.generatorOne_reflections (z : ℍ) :
    generatorOneSL • z = rightReflection (circleReflection z) := by
  apply UpperHalfPlane.ext
  simp [generatorOne_coe, neg_div, one_div]

private theorem SpecialPeriods.Triangle.generatorTwo_reflections (z : ℍ) :
    generatorTwoSL • z = circleReflection (leftReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe, circleReflection_coe, leftReflection_coe]
  simp only [map_sub, map_neg, map_add, Complex.conj_ofReal, map_one, Complex.conj_conj]
  rw [show -((width : ℂ) + 1) - (z : ℂ) + 1 = -(z : ℂ) - width by ring]
  have hd := denominatorTwo_ne_zero z
  field_simp [hd]
  ring

private theorem SpecialPeriods.Triangle.cusp_reflections (z : ℍ) :
    cuspSL • z = leftReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [cuspSL_apply]
  simp [UpperHalfPlane.coe_vadd]

private theorem SpecialPeriods.Triangle.generatorOne_eq_rightReflection_of_norm_add_one (z : ℍ)
    (hz : ‖(z : ℂ) + 1‖ = 1) : generatorOneSL • z = rightReflection z := by
  rw [generatorOne_reflections, (circleReflection_fixed_iff z).mpr hz]

private theorem SpecialPeriods.Triangle.rightReflection_re_eq_stripRight_iff (z : ℍ) :
    (rightReflection z).re = stripRight ↔ z.re = stripLeft := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

private theorem SpecialPeriods.Triangle.rightReflection_re_eq_stripLeft_iff (z : ℍ) :
    (rightReflection z).re = stripLeft ↔ z.re = stripRight := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

private theorem SpecialPeriods.Triangle.cusp_eq_rightReflection_of_re_eq_stripRight (z : ℍ)
    (hz : z.re = stripRight) : cuspSL • z = rightReflection z := by
  rw [cusp_reflections]
  exact
    (leftReflection_fixed_iff (rightReflection z)).mpr
      ((rightReflection_re_eq_stripLeft_iff z).mpr hz)

private theorem SpecialPeriods.Triangle.generatorOne_inv_eq_rightReflection_of_norm (z : ℍ)
    (hz : ‖(z : ℂ)‖ = 1) : generatorOneSL⁻¹ • z = rightReflection z := by
  have h :=
    generatorOne_eq_rightReflection_of_norm_add_one (rightReflection z)
      (by simpa only [rightReflection_add_one_norm] using hz)
  rw [rightReflection_involutive z] at h
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

private def SpecialPeriods.Triangle.triangleInterior : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

private def SpecialPeriods.Triangle.boundaryHeight (x : ℝ) : ℝ :=
  Real.sqrt (1 - (x + 1) ^ 2)

@[fun_prop]
private theorem SpecialPeriods.Triangle.continuous_boundaryHeight : Continuous boundaryHeight := by
  unfold boundaryHeight
  fun_prop

private theorem SpecialPeriods.Triangle.boundaryHeight_le_one (x : ℝ) : boundaryHeight x ≤ 1 := by
  have h : 1 - (x + 1) ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg (x + 1)]
  simpa only [boundaryHeight, Real.sqrt_one] using Real.sqrt_le_sqrt h

private theorem SpecialPeriods.Triangle.neg_two_lt_stripLeft : -2 < stripLeft := by
  have h : width < 3 := by nlinarith [width_sq, width_pos]
  unfold stripLeft
  linarith

private theorem SpecialPeriods.Triangle.circle_epigraph_iff (z : ℂ) :
    (0 < z.im ∧ 1 < ‖z + 1‖) ↔ boundaryHeight z.re < z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_lt' hy).mpr
    have hs := (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro h
    have hy : 0 < z.im := lt_of_le_of_lt (Real.sqrt_nonneg _) h
    refine ⟨hy, ?_⟩
    apply (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_lt' hy).mp h
    nlinarith

private theorem SpecialPeriods.Triangle.mem_triangleInterior_iff_epigraph (z : ℂ) :
    z ∈ triangleInterior ↔ stripLeft < z.re ∧ z.re < -1 / 2 ∧ boundaryHeight z.re < z.im := by
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ (0 < z.im ∧ 1 < ‖z + 1‖)) ↔ _
  rw [circle_epigraph_iff]

private def SpecialPeriods.Triangle.triangleBasepoint : ℂ :=
  -1 + 2 * Complex.I

private theorem
    SpecialPeriods.Triangle.triangleBasepoint_mem : triangleBasepoint ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph]
  norm_num [triangleBasepoint, boundaryHeight, stripLeft_lt_neg_one]

private theorem SpecialPeriods.Triangle.triangleInterior_isOpen : IsOpen triangleInterior :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm))))

private theorem
    SpecialPeriods.Triangle.zero_not_mem_triangleInterior : (0 : ℂ) ∉ triangleInterior := by
  simp [triangleInterior]

private theorem SpecialPeriods.Triangle.triangleInterior_ne_univ : triangleInterior ≠ Set.univ := by
  intro h
  exact zero_not_mem_triangleInterior (h.symm ▸ Set.mem_univ (0 : ℂ))

private def SpecialPeriods.Triangle.triangleOpenStrip : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}

private theorem SpecialPeriods.Triangle.triangleOpenStrip_convex : Convex ℝ triangleOpenStrip :=
  (convex_halfSpace_re_gt stripLeft).inter
    ((convex_halfSpace_re_lt (-1 / 2)).inter (convex_halfSpace_im_gt 0))

private theorem
    SpecialPeriods.Triangle.triangleOpenStrip_nonempty : triangleOpenStrip.Nonempty := by
  refine ⟨(-1 : ℂ) + Complex.I, ?_⟩
  norm_num [triangleOpenStrip, stripLeft_lt_neg_one]

private def SpecialPeriods.Triangle.triangleHeightShift : ℂ ≃ₜ ℂ
    where
  toFun z := ⟨z.re, z.im - boundaryHeight z.re⟩
  invFun z := ⟨z.re, z.im + boundaryHeight z.re⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im - boundaryHeight z.re)) from by fun_prop)
  continuous_invFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im + boundaryHeight z.re)) from by fun_prop)

@[simp]
private theorem SpecialPeriods.Triangle.triangleHeightShift_re (z : ℂ) :
    (triangleHeightShift z).re = z.re :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.triangleHeightShift_im (z : ℂ) :
    (triangleHeightShift z).im = z.im - boundaryHeight z.re :=
  rfl

private theorem SpecialPeriods.Triangle.triangleInterior_eq_preimage_strip :
    triangleInterior = triangleHeightShift ⁻¹' triangleOpenStrip := by
  ext z
  rw [mem_triangleInterior_iff_epigraph]
  simp only [Set.mem_preimage, triangleOpenStrip, Set.mem_ofPred_eq, triangleHeightShift_re,
    triangleHeightShift_im, sub_pos]

private def SpecialPeriods.Triangle.triangleInteriorHomeomorphStrip :
    triangleInterior ≃ₜ triangleOpenStrip :=
  triangleHeightShift.sets triangleInterior_eq_preimage_strip

private instance SpecialPeriods.Triangle.triangleInterior_contractible :
    ContractibleSpace triangleInterior := by
  have : ContractibleSpace triangleOpenStrip :=
    triangleOpenStrip_convex.contractibleSpace triangleOpenStrip_nonempty
  exact triangleInteriorHomeomorphStrip.contractibleSpace

private instance SpecialPeriods.Triangle.triangleInterior_simplyConnectedSpace :
    SimplyConnectedSpace triangleInterior :=
  inferInstance

private theorem SpecialPeriods.Triangle.triangleInterior_isSimplyConnected :
    IsSimplyConnected triangleInterior := by
  change SimplyConnectedSpace triangleInterior
  infer_instance

private def SpecialPeriods.Triangle.halfFordRegion : Set ℍ :=
  fordRegion ∩ {z | z.re ≤ -(1 / 2)}

private def SpecialPeriods.Triangle.halfFordInterior : Set ℍ :=
  fordInterior ∩ {z | z.re < -(1 / 2)}

private theorem SpecialPeriods.Triangle.halfFordRegion_isClosed : IsClosed halfFordRegion :=
  fordRegion_closed.inter (isClosed_le UpperHalfPlane.continuous_re continuous_const)

private theorem SpecialPeriods.Triangle.halfFordInterior_isOpen : IsOpen halfFordInterior :=
  fordInterior_isOpen.inter (isOpen_lt UpperHalfPlane.continuous_re continuous_const)

private theorem SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion :
    halfFordInterior ⊆ halfFordRegion := by
  intro z hz
  exact ⟨fordInterior_subset_fordRegion hz.1, (show z.re < -(1 / 2) from hz.2).le⟩

private theorem SpecialPeriods.Triangle.norm_add_one_lt_norm_of_re_lt_neg_half (z : ℍ)
    (hzre : z.re < -(1 / 2)) : ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  apply (sq_lt_sq₀ (norm_nonneg ((z : ℂ) + 1)) (norm_nonneg (z : ℂ))).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith

private theorem
    SpecialPeriods.Triangle.one_lt_norm_of_re_lt_neg_half (z : ℍ) (hzre : z.re < -(1 / 2))
    (hn : 1 < ‖(z : ℂ) + 1‖) : 1 < ‖(z : ℂ)‖ :=
  hn.trans (norm_add_one_lt_norm_of_re_lt_neg_half z hzre)

private theorem SpecialPeriods.Triangle.strict_ford_left_half_iff_triangleInterior (z : ℍ) :
    ((stripLeft < z.re ∧ z.re < stripRight ∧ 1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖) ∧
        z.re < -(1 / 2)) ↔
      (z : ℂ) ∈ triangleInterior := by
  change _ ↔ stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖(z : ℂ) + 1‖
  constructor
  · rintro ⟨⟨hl, _, hn, _⟩, hm⟩
    exact ⟨hl, by linarith, z.im_pos, hn⟩
  · rintro ⟨hl, hm, _, hn⟩
    have hm' : z.re < -(1 / 2) := by linarith
    refine ⟨⟨hl, ?_, hn, one_lt_norm_of_re_lt_neg_half z hm' hn⟩, hm'⟩
    linarith [stripRight_pos]

private theorem SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior :
    halfFordInterior = ((↑) : ℍ → ℂ) ⁻¹' triangleInterior :=
  Set.ext strict_ford_left_half_iff_triangleInterior

@[simp]
private theorem SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff (z : ℍ) :
    rightReflection z ∈ fordInterior ↔ z ∈ fordInterior := by
  simp only [fordInterior, Set.mem_ofPred_eq, rightReflection_re, rightReflection_add_one_norm,
    rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

private theorem SpecialPeriods.Triangle.rightReflection_mapsTo_fordInterior :
    Set.MapsTo rightReflection fordInterior fordInterior := fun z hz =>
  (rightReflection_mem_fordInterior_iff z).mpr hz

private def SpecialPeriods.Triangle.halfFold (b : Bool) : ℍ ≃ₜ ℍ :=
  if b then rightReflection else Homeomorph.refl ℍ

private theorem SpecialPeriods.Triangle.halfFold_mapsTo_region (b : Bool) :
    Set.MapsTo (halfFold b) halfFordRegion fordRegion := by
  cases b
  · intro z hz
    exact hz.1
  · intro z hz
    exact rightReflection_mapsTo_fordRegion hz.1

private theorem SpecialPeriods.Triangle.halfFold_image_region_subset (b : Bool) :
    halfFold b '' halfFordRegion ⊆ fordRegion :=
  (halfFold_mapsTo_region b).image_subset

private theorem SpecialPeriods.Triangle.rightReflection_image_halfFordRegion :
    rightReflection '' halfFordRegion = fordRegion ∩ {z | -(1 / 2) ≤ z.re} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rightReflection_mapsTo_fordRegion hw.1, ?_⟩
    change -(1 / 2) ≤ (rightReflection w).re
    rw [rightReflection_re]
    have hcut : w.re ≤ -(1 / 2) := hw.2
    linarith
  · rintro ⟨hz, hr⟩
    refine
      ⟨rightReflection z, ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩,
        rightReflection_involutive z⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    change -(1 / 2) ≤ z.re at hr
    linarith

private theorem SpecialPeriods.Triangle.halfFordRegion_union_reflection :
    halfFordRegion ∪ rightReflection '' halfFordRegion = fordRegion := by
  rw [rightReflection_image_halfFordRegion]
  ext z
  change
    ((z ∈ fordRegion ∧ z.re ≤ -(1 / 2)) ∨ (z ∈ fordRegion ∧ -(1 / 2) ≤ z.re)) ↔ z ∈ fordRegion
  constructor
  · rintro (hz | hz) <;> exact hz.1
  · intro hz
    rcases le_total z.re (-(1 / 2)) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩

private theorem SpecialPeriods.Triangle.halfFold_closed_cover :
    (⋃ b : Bool, halfFold b '' halfFordRegion) = fordRegion := by
  ext z
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    exact halfFold_image_region_subset b hb
  · intro hz
    rw [← halfFordRegion_union_reflection] at hz
    rcases hz with hz | hz
    · exact ⟨Bool.false, z, hz, rfl⟩
    · exact ⟨Bool.true, hz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
private theorem SpecialPeriods.Triangle.compact_return_height_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ hi : ℝ,
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        SpecialPeriods.triangleGeometricRepresentation g z ∈ K → z.im ≤ hi := by
  obtain ⟨hi, hhi⟩ := hK.bddAbove_image orbitHeightBound_continuous.continuousOn
  refine ⟨hi, fun g z hz => ?_⟩
  have hb :=
    triangle_im_le_orbitHeightBound g⁻¹ (SpecialPeriods.triangleGeometricRepresentation g z)
  have he :
    SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g z) =
      z := by
    rw [map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply z
  rw [he] at hb
  exact hb.trans (hhi ⟨_, hz, rfl⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
private theorem SpecialPeriods.Triangle.fordRegion_translates_finite_inter_compact {K : Set ℍ}
    (hK : IsCompact K) :
    {g : SpecialPeriods.TriangleGroup |
        (SpecialPeriods.triangleGeometricRepresentation g '' fordRegion ∩ K).Nonempty}.Finite := by
  obtain ⟨hi, hhi⟩ := compact_return_height_bound hK
  have hf :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := SpecialPeriods.TriangleGroup)
      (truncatedFordRegion_compact hi) hK
  apply hf.subset
  rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact ⟨SpecialPeriods.triangleGeometricRepresentation g w, ⟨w, ⟨hw, hhi g w hz⟩, rfl⟩, hz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
private theorem SpecialPeriods.Triangle.fordRegion_translates_locallyFinite :
    LocallyFinite
      (fun g : SpecialPeriods.TriangleGroup =>
        SpecialPeriods.triangleGeometricRepresentation g '' fordRegion) := by
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  exact ⟨K, hKz, fordRegion_translates_finite_inter_compact hK⟩

private def
    SpecialPeriods.Triangle.halfTriangleMap (i : SpecialPeriods.TriangleGroup × Bool) : ℍ ≃ₜ ℍ :=
  (halfFold i.2).trans (SpecialPeriods.triangleGeometricBiholomorph i.1).toHomeomorph

@[simp]
private theorem
    SpecialPeriods.Triangle.halfTriangleMap_apply (i : SpecialPeriods.TriangleGroup × Bool)
    (z : ℍ) :
    halfTriangleMap i z = SpecialPeriods.triangleGeometricRepresentation i.1 (halfFold i.2 z) :=
  rfl

private def
    SpecialPeriods.Triangle.halfTriangleTile (i : SpecialPeriods.TriangleGroup × Bool) : Set ℍ :=
  halfTriangleMap i '' halfFordRegion

private def SpecialPeriods.Triangle.halfTriangleOpenTile (i : SpecialPeriods.TriangleGroup × Bool) :
    Set ℍ :=
  halfTriangleMap i '' halfFordInterior

private theorem
    SpecialPeriods.Triangle.halfTriangleTile_eq (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleTile i =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordRegion) := by
  rw [Set.image_image]
  rfl

private theorem SpecialPeriods.Triangle.halfTriangleOpenTile_eq
    (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleOpenTile i =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordInterior) := by
  rw [Set.image_image]
  rfl

private theorem SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen
    (i : SpecialPeriods.TriangleGroup × Bool) : IsOpen (halfTriangleOpenTile i) :=
  (halfTriangleMap i).isOpenMap halfFordInterior halfFordInterior_isOpen

private theorem SpecialPeriods.Triangle.halfTriangleTile_subset_fordRegion_translate
    (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleTile i ⊆ SpecialPeriods.triangleGeometricRepresentation i.1 '' fordRegion := by
  rw [halfTriangleTile_eq]
  exact Set.image_mono (halfFold_image_region_subset i.2)

private theorem SpecialPeriods.Triangle.halfTriangleTiles_cover :
    (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleTile i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hgz⟩ := SpecialPeriods.triangle_exists_fordRegion_preimage z
  have hfold : w ∈ ⋃ b : Bool, halfFold b '' halfFordRegion := by
    rw [halfFold_closed_cover]
    exact hw
  obtain ⟨b, u, hu, hwu⟩ := Set.mem_iUnion.mp hfold
  refine Set.mem_iUnion.mpr ⟨(g, b), u, hu, ?_⟩
  rw [halfTriangleMap_apply, hwu, hgz]

private theorem SpecialPeriods.Triangle.halfTriangleTiles_finite_inter_compact {K : Set ℍ}
    (hK : IsCompact K) :
    {i : SpecialPeriods.TriangleGroup × Bool | (halfTriangleTile i ∩ K).Nonempty}.Finite := by
  apply
    ((fordRegion_translates_finite_inter_compact hK).prod
        (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  rintro i ⟨z, hz, hKz⟩
  exact ⟨⟨z, halfTriangleTile_subset_fordRegion_translate i hz, hKz⟩, Set.mem_univ _⟩

private theorem SpecialPeriods.Triangle.halfTriangleTiles_locallyFinite :
    LocallyFinite halfTriangleTile := by
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  exact ⟨K, hKz, halfTriangleTiles_finite_inter_compact hK⟩

private structure TriangleUniformizationGluing.BoundaryMap where
  toFun : ℍ → ℂ
  continuousOn : ContinuousOn toFun SpecialPeriods.Triangle.halfFordRegion
  boundary_real :
    ∀ z ∈ SpecialPeriods.Triangle.halfFordRegion,
      z ∉ SpecialPeriods.Triangle.halfFordInterior → (toFun z).im = 0

private instance TriangleUniformizationGluing.instCoeFun1 : CoeFun BoundaryMap (fun _ => ℍ → ℂ) :=
  ⟨BoundaryMap.toFun⟩

private def TriangleUniformizationGluing.BoundaryMap.foldedFordMap
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ) : ℂ := by
  classical
    exact if z.re ≤ -(1 / 2) then D z else conj (D (SpecialPeriods.Triangle.rightReflection z))

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_of_left
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z := by simp only [foldedFordMap, ite_eq_left hz]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_of_right
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (SpecialPeriods.Triangle.rightReflection z)) := by
  simp only [foldedFordMap, ite_eq_right hz.not_ge]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eqOn_left
    (D : TriangleUniformizationGluing.BoundaryMap) :
    Set.EqOn D.foldedFordMap D SpecialPeriods.Triangle.halfFordRegion := fun _ hz =>
  D.foldedFordMap_of_left hz.2

private theorem TriangleUniformizationGluing.BoundaryMap.real_at_axis
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hx : z.re = -(1 / 2)) : (D z).im = 0 := by
  apply D.boundary_real z ⟨hz, hx.le⟩
  intro hi
  have hh : z.re < -(1 / 2) := hi.2
  linarith

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_reflected
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = conj (D z) := by
  by_cases hx : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2)
  · have hcut : z.re = -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re] at hx
      have hleft : z.re ≤ -(1 / 2) := hz.2
      linarith
    have hfix : SpecialPeriods.Triangle.rightReflection z = z :=
      (SpecialPeriods.Triangle.rightReflection_fixed_iff z).mpr hcut
    rw [hfix, D.foldedFordMap_of_left hz.2]
    exact (Complex.conj_eq_iff_im.mpr (D.real_at_axis hz.1 hcut)).symm
  · simp only [foldedFordMap, ite_eq_right hx]
    rw [SpecialPeriods.Triangle.rightReflection_involutive z]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eqOn_right
    (D : TriangleUniformizationGluing.BoundaryMap) :
    Set.EqOn D.foldedFordMap (fun z => conj (D (SpecialPeriods.Triangle.rightReflection z)))
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection w) =
      conj
        (D (SpecialPeriods.Triangle.rightReflection (SpecialPeriods.Triangle.rightReflection w)))
  rw [D.foldedFordMap_reflected w hw, SpecialPeriods.Triangle.rightReflection_involutive w]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_continuousOn
    (D : TriangleUniformizationGluing.BoundaryMap) :
    ContinuousOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion := by
  have hl : ContinuousOn D.foldedFordMap SpecialPeriods.Triangle.halfFordRegion :=
    D.continuousOn.congr D.foldedFordMap_eqOn_left
  have hm :
    Set.MapsTo SpecialPeriods.Triangle.rightReflection
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion)
      SpecialPeriods.Triangle.halfFordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [SpecialPeriods.Triangle.rightReflection_involutive w]
    exact hw
  have hr :
    ContinuousOn D.foldedFordMap
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion) := by
    apply
      (Complex.continuous_conj.continuousOn.comp
          (D.continuousOn.comp SpecialPeriods.Triangle.rightReflection.continuous.continuousOn hm)
          (Set.mapsTo_univ _ _)).congr
    exact D.foldedFordMap_eqOn_right
  rw [← SpecialPeriods.Triangle.halfFordRegion_union_reflection]
  exact
    hl.union_of_isClosed hr SpecialPeriods.Triangle.halfFordRegion_isClosed
      (SpecialPeriods.Triangle.rightReflection.isClosedMap _
        SpecialPeriods.Triangle.halfFordRegion_isClosed)

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_rightReflection
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = conj (D.foldedFordMap z) := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.foldedFordMap_reflected z ⟨hz, hx⟩
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re]
      linarith
    rw [D.foldedFordMap_of_left hleft, D.foldedFordMap_of_right hright, Complex.conj_conj]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_real_of_not_mem_interior
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion)
    (hi : z ∉ SpecialPeriods.Triangle.fordInterior) : (D.foldedFordMap z).im = 0 := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.boundary_real z ⟨hz, hx⟩ (fun hh => hi hh.1)
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re]
      linarith
    have hr :
      SpecialPeriods.Triangle.rightReflection z ∈ SpecialPeriods.Triangle.halfFordRegion :=
      ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz, hleft⟩
    have hn :
      SpecialPeriods.Triangle.rightReflection z ∉ SpecialPeriods.Triangle.halfFordInterior := by
      intro hh
      exact hi ((SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff z).mp hh.1)
    rw [D.foldedFordMap_of_right hright, Complex.conj_im, D.boundary_real _ hr hn, neg_zero]

private theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_rightReflection_boundary
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion)
    (hi : z ∉ SpecialPeriods.Triangle.fordInterior) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = D.foldedFordMap z := by
  rw [D.foldedFordMap_rightReflection hz]
  exact Complex.conj_eq_iff_im.mpr (D.foldedFordMap_real_of_not_mem_interior hz hi)

private structure TriangleUniformizationGluing.HalfPlaneMap extends BoundaryMap where
  injOn : Set.InjOn toFun SpecialPeriods.Triangle.halfFordRegion
  image_eq : toFun '' SpecialPeriods.Triangle.halfFordRegion = {w : ℂ | 0 ≤ w.im}
  interior_positive : ∀ z ∈ SpecialPeriods.Triangle.halfFordInterior, 0 < (toFun z).im

private instance TriangleUniformizationGluing.instCoeFun2 : CoeFun HalfPlaneMap (fun _ => ℍ → ℂ) :=
  ⟨fun D => D.toFun⟩

private abbrev TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap
    (D : TriangleUniformizationGluing.HalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.foldedFordMap

private theorem TriangleUniformizationGluing.HalfPlaneMap.im_nonneg
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) : 0 ≤ (D z).im := by
  have h : D.toFun z ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion :=
    Set.mem_image_of_mem D.toFun hz
  rw [D.image_eq] at h
  exact h

private theorem TriangleUniformizationGluing.HalfPlaneMap.im_eq_zero_iff_not_mem_halfFordInterior
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    (D z).im = 0 ↔ z ∉ SpecialPeriods.Triangle.halfFordInterior := by
  constructor
  · intro him hi
    exact (D.interior_positive z hi).ne' him
  · exact D.boundary_real z hz

private theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_of_left
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z :=
  D.toBoundaryMap.foldedFordMap_of_left hz

private theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_of_right
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (SpecialPeriods.Triangle.rightReflection z)) :=
  D.toBoundaryMap.foldedFordMap_of_right hz

private theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_surjOn
    (D : TriangleUniformizationGluing.HalfPlaneMap) :
    Set.SurjOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion Set.univ := by
  intro w _
  by_cases hw : 0 ≤ w.im
  · have hmem : w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
      rw [D.image_eq]
      exact hw
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap z = w
    rw [D.toBoundaryMap.foldedFordMap_of_left hz.2]
    exact he
  · have hmem : conj w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
      rw [D.image_eq]
      change 0 ≤ (conj w).im
      rw [Complex.conj_im]
      exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hw))
    obtain ⟨z, hz, he⟩ := hmem
    refine
      ⟨SpecialPeriods.Triangle.rightReflection z,
        SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = w
    rw [D.toBoundaryMap.foldedFordMap_reflected z hz, he, Complex.conj_conj]

private theorem
  TriangleUniformizationGluing.HalfPlaneMap.rightReflection_mem_halfFordRegion_mo1973_18870
    {z : ℍ} (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hx : -(1 / 2) < z.re) :
    SpecialPeriods.Triangle.rightReflection z ∈ SpecialPeriods.Triangle.halfFordRegion := by
  refine ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz, ?_⟩
  change (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2)
  rw [SpecialPeriods.Triangle.rightReflection_re]
  linarith

private theorem TriangleUniformizationGluing.HalfPlaneMap.cross_fibre_mo1973_18871
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion)
    (hw : w ∈ SpecialPeriods.Triangle.fordRegion) (hwr : -(1 / 2) < w.re)
    (heq : D.foldedFordMap z = D.foldedFordMap w) :
    w = SpecialPeriods.Triangle.rightReflection z ∧ z ∉ SpecialPeriods.Triangle.fordInterior := by
  have hrw : SpecialPeriods.Triangle.rightReflection w ∈ SpecialPeriods.Triangle.halfFordRegion :=
    rightReflection_mem_halfFordRegion_mo1973_18870 hw hwr
  rw [D.foldedFordMap_of_left hz.2, D.foldedFordMap_of_right hwr] at heq
  have him := congrArg Complex.im heq
  rw [Complex.conj_im] at him
  have hzpos := D.im_nonneg hz
  have hwpos := D.im_nonneg hrw
  have hzreal : (D z).im = 0 := by linarith
  have hwreal : (D (SpecialPeriods.Triangle.rightReflection w)).im = 0 := by linarith
  have hf : D z = D (SpecialPeriods.Triangle.rightReflection w) :=
    heq.trans (Complex.conj_eq_iff_im.mpr hwreal)
  have hzw : z = SpecialPeriods.Triangle.rightReflection w := D.injOn hz hrw hf
  have hwz : w = SpecialPeriods.Triangle.rightReflection z := by
    rw [hzw, SpecialPeriods.Triangle.rightReflection_involutive]
  refine ⟨hwz, ?_⟩
  have hnot : z ∉ SpecialPeriods.Triangle.halfFordInterior :=
    (D.im_eq_zero_iff_not_mem_halfFordInterior hz).mp hzreal
  intro hi
  apply hnot
  refine ⟨hi, ?_⟩
  change z.re < -(1 / 2)
  rw [hzw, SpecialPeriods.Triangle.rightReflection_re]
  linarith

private theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_eq_iff
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨
        (w = SpecialPeriods.Triangle.rightReflection z ∧
          z ∉ SpecialPeriods.Triangle.fordInterior) := by
  constructor
  · intro heq
    by_cases hzl : z.re ≤ -(1 / 2)
    · by_cases hwl : w.re ≤ -(1 / 2)
      · left
        rw [D.foldedFordMap_of_left hzl, D.foldedFordMap_of_left hwl] at heq
        exact D.injOn ⟨hz, hzl⟩ ⟨hw, hwl⟩ heq
      · exact Or.inr (D.cross_fibre_mo1973_18871 ⟨hz, hzl⟩ hw (lt_of_not_ge hwl) heq)
    · have hzr : -(1 / 2) < z.re := lt_of_not_ge hzl
      by_cases hwl : w.re ≤ -(1 / 2)
      · obtain ⟨hzw, hwnot⟩ := D.cross_fibre_mo1973_18871 ⟨hw, hwl⟩ hz hzr heq.symm
        right
        constructor
        · rw [hzw, SpecialPeriods.Triangle.rightReflection_involutive]
        · rw [hzw, SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff]
          exact hwnot
      · have hwr : -(1 / 2) < w.re := lt_of_not_ge hwl
        left
        rw [D.foldedFordMap_of_right hzr, D.foldedFordMap_of_right hwr] at heq
        have hf :
          D (SpecialPeriods.Triangle.rightReflection z) =
            D (SpecialPeriods.Triangle.rightReflection w) := by
          simpa only [Complex.conj_conj] using congrArg (fun u : ℂ => conj u) heq
        exact
          SpecialPeriods.Triangle.rightReflection.injective
            (D.injOn (rightReflection_mem_halfFordRegion_mo1973_18870 hz hzr)
              (rightReflection_mem_halfFordRegion_mo1973_18870 hw hwr) hf)
  · rintro (rfl | ⟨rfl, hi⟩)
    · rfl
    · exact (D.toBoundaryMap.foldedFordMap_rightReflection_boundary hz hi).symm

private structure TriangleUniformizationGluing.SignedHalfPlaneMap extends BoundaryMap where
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  injOn : Set.InjOn toFun SpecialPeriods.Triangle.halfFordRegion
  image_eq : toFun '' SpecialPeriods.Triangle.halfFordRegion = {w : ℂ | 0 ≤ orientation * w.im}
  interior_positive :
    ∀ z ∈ SpecialPeriods.Triangle.halfFordInterior, 0 < orientation * (toFun z).im

private instance
    TriangleUniformizationGluing.instCoeFun3 : CoeFun SignedHalfPlaneMap (fun _ => ℍ → ℂ) :=
  ⟨fun D => D.toFun⟩

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_ne_zero
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : D.orientation ≠ 0 := by
  intro h
  have hs := D.orientation_sq
  rw [h] at hs
  norm_num at hs

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_coe_ne_zero
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : (D.orientation : ℂ) ≠ 0 := by
  exact_mod_cast D.orientation_ne_zero

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_mul_self
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : D.orientation * D.orientation = 1 := by
  simpa only [pow_two] using D.orientation_sq

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_coe_mul_self
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    (D.orientation : ℂ) * (D.orientation : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, D.orientation_mul_self, Complex.ofReal_one]

private def TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) (w : ℂ) : ℂ :=
  (D.orientation : ℂ) * w

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale_involutive
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Function.Involutive D.orientationScale := by
  intro w
  change (D.orientation : ℂ) * ((D.orientation : ℂ) * w) = w
  rw [← mul_assoc, D.orientation_coe_mul_self, one_mul]

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale_injective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Function.Injective D.orientationScale :=
  D.orientationScale_involutive.injective

private abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.foldedFordMap

private def TriangleUniformizationGluing.SignedHalfPlaneMap.normalized
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    TriangleUniformizationGluing.HalfPlaneMap
    where
  toFun := fun z => (D.orientation : ℂ) * D z
  continuousOn := continuousOn_const.mul D.continuousOn
  boundary_real := by
    intro z hz hi
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero, D.boundary_real z hz hi, MulZeroClass.mul_zero]
  injOn := by
    intro z hz w hw he
    exact D.injOn hz hw ((mul_right_inj' D.orientation_coe_ne_zero).mp he)
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : D.toFun z ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion :=
        Set.mem_image_of_mem D.toFun hz
      rw [D.image_eq] at h
      simpa only [Set.mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        MulZeroClass.zero_mul, add_zero] using h
    · intro hw
      have h : (D.orientation : ℂ) * w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
        rw [D.image_eq]
        simp only [Set.mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          MulZeroClass.zero_mul, add_zero]
        rw [← mul_assoc, D.orientation_mul_self, one_mul]
        exact hw
      obtain ⟨z, hz, he⟩ := h
      refine ⟨z, hz, ?_⟩
      change (D.orientation : ℂ) * D.toFun z = w
      rw [he, ← mul_assoc, D.orientation_coe_mul_self, one_mul]
  interior_positive := by
    intro z hz
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero] using D.interior_positive z hz

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.normalized_foldedFordMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) (z : ℍ) :
    D.normalized.foldedFordMap z = (D.orientation : ℂ) * D.foldedFordMap z := by
  simp only [TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap, foldedFordMap,
    TriangleUniformizationGluing.BoundaryMap.foldedFordMap]
  split_ifs
  · rfl
  · change
      conj ((D.orientation : ℂ) * D (SpecialPeriods.Triangle.rightReflection z)) =
        (D.orientation : ℂ) * conj (D (SpecialPeriods.Triangle.rightReflection z))
    rw [map_mul, Complex.conj_ofReal]

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap_surjOn
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Set.SurjOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion Set.univ := by
  intro w _
  obtain ⟨z, hz, he⟩ := D.normalized.foldedFordMap_surjOn (Set.mem_univ ((D.orientation : ℂ) * w))
  refine ⟨z, hz, ?_⟩
  apply D.orientationScale_injective
  change (D.orientation : ℂ) * D.foldedFordMap z = (D.orientation : ℂ) * w
  rw [← D.normalized_foldedFordMap z]
  exact he

private theorem TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap_eq_iff
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨
        (w = SpecialPeriods.Triangle.rightReflection z ∧
          z ∉ SpecialPeriods.Triangle.fordInterior) := by
  have heq :
    D.normalized.foldedFordMap z = D.normalized.foldedFordMap w ↔
      D.foldedFordMap z = D.foldedFordMap w := by
    rw [D.normalized_foldedFordMap z, D.normalized_foldedFordMap w]
    constructor
    · intro h
      exact D.orientationScale_injective h
    · intro h
      exact congrArg D.orientationScale h
  exact heq.symm.trans (D.normalized.foldedFordMap_eq_iff hz hw)

private abbrev RiemannSphere.Biholomorph :=
  Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) RiemannSphere RiemannSphere ω

private def RiemannSphere.reciprocal (p : RiemannSphere) : RiemannSphere :=
  p.elim ((0 : ℂ) : RiemannSphere) infinityParametrization

@[simp]
private theorem RiemannSphere.reciprocal_coe (z : ℂ) :
    reciprocal (z : RiemannSphere) = infinityParametrization z :=
  rfl

@[simp]
private theorem RiemannSphere.reciprocal_infinityParametrization (z : ℂ) :
    reciprocal (infinityParametrization z) = (z : RiemannSphere) := by
  have hinfty : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  by_cases hz : z = 0
  · subst z
    simp [hinfty]
  · rw [infinityParametrization_of_ne hz, reciprocal_coe,
      infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]

private theorem RiemannSphere.reciprocal_involutive : Function.Involutive reciprocal := by
  have hinfty : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  intro p
  induction p using OnePoint.rec with
  | infty => simp [hinfty]
  | coe z => simp []

private theorem RiemannSphere.reciprocal_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω reciprocal := by
  apply standardCharts.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro b
  have he : reciprocal ∘ standardCharts.affineMap b = standardCharts.affineMap (!b) := by
    funext z
    cases b
    · rfl
    · exact reciprocal_infinityParametrization z
  rw [he]
  exact standardCharts.affineMap_holomorphic (!b)

private def RiemannSphere.reciprocalBiholomorph : Biholomorph
    where
  toEquiv := reciprocal_involutive.toPerm reciprocal
  contMDiff_toFun := reciprocal_holomorphic
  contMDiff_invFun := reciprocal_holomorphic

@[simp]
private theorem RiemannSphere.reciprocalBiholomorph_apply (p : RiemannSphere) :
    reciprocalBiholomorph p = reciprocal p :=
  rfl

private def RiemannSphere.affineComplexHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

private def
    RiemannSphere.affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : RiemannSphere ≃ₜ RiemannSphere :=
  (affineComplexHomeomorph a b ha).onePointCongr

@[simp]
private theorem RiemannSphere.affineHomeomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    RiemannSphere.affineHomeomorph a b ha (z : RiemannSphere) =
      ((a * z + b : ℂ) : RiemannSphere) :=
  rfl

private theorem RiemannSphere.affineHomeomorph_infinityParametrization (a b z : ℂ) (ha : a ≠ 0)
    (hz : a + b * z ≠ 0) :
    RiemannSphere.affineHomeomorph a b ha (infinityParametrization z) =
      infinityParametrization (z / (a + b * z)) := by
  have hinfty :
    RiemannSphere.affineHomeomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  by_cases hz0 : z = 0
  · subst z
    simp [hinfty]
  · rw [infinityParametrization_of_ne hz0, affineHomeomorph_coe,
      infinityParametrization_of_ne (div_ne_zero hz0 hz)]
    congr 1
    field_simp

private theorem RiemannSphere.affineHomeomorph_holomorphic (a b : ℂ) (ha : a ≠ 0) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (RiemannSphere.affineHomeomorph a b ha) := by
  apply standardCharts.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro chart
  cases chart
  · have hc : ContDiff ℂ ω (fun z : ℂ => a * z + b) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    exact (standardCharts.affineMap_holomorphic Bool.false).comp hc.contMDiff
  · intro z
    by_cases hz : z = 0
    · subst z
      have hd : ContDiffAt ℂ ω (fun w : ℂ => w / (a + b * w)) 0 :=
        contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
          (by simpa using ha)
      have hc :
        ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
          (fun w : ℂ => infinityParametrization (w / (a + b * w))) 0 :=
        (standardCharts.affineMap_holomorphic Bool.true).contMDiffAt.comp 0 hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      have hn : ∀ᶠ w : ℂ in 𝓝 0, a + b * w ≠ 0 :=
        (isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id))
              continuous_const).mem_nhds
          (by simpa using ha)
      filter_upwards [hn] with w hw
      exact affineHomeomorph_infinityParametrization a b w ha hw
    · have hd : ContDiffAt ℂ ω (fun w : ℂ => a * w⁻¹ + b) z :=
        (contDiffAt_const.mul (contDiffAt_inv ℂ hz)).add contDiffAt_const
      have hc :
        ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
          (fun w : ℂ => ((a * w⁻¹ + b : ℂ) : RiemannSphere)) z :=
        (standardCharts.affineMap_holomorphic Bool.false).contMDiffAt.comp z hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
      change w ≠ 0 at hw
      change RiemannSphere.affineHomeomorph a b ha (infinityParametrization w) = _
      rw [infinityParametrization_of_ne hw, affineHomeomorph_coe]

private theorem RiemannSphere.affineHomeomorph_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    ⇑(RiemannSphere.affineHomeomorph a b ha).symm =
      RiemannSphere.affineHomeomorph a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha) := by
  funext p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe
    z =>
    change ((a⁻¹ * (z - b) : ℂ) : RiemannSphere) = ((a⁻¹ * z + -a⁻¹ * b : ℂ) : RiemannSphere)
    congr 1
    ring

private def RiemannSphere.affineBiholomorph (a b : ℂ) (ha : a ≠ 0) : Biholomorph
    where
  toEquiv := (RiemannSphere.affineHomeomorph a b ha).toEquiv
  contMDiff_toFun := affineHomeomorph_holomorphic a b ha
  contMDiff_invFun := by
    change
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (RiemannSphere.affineHomeomorph a b ha).symm
    rw [affineHomeomorph_symm_eq]
    exact affineHomeomorph_holomorphic a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)

@[simp]
private theorem RiemannSphere.affineBiholomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha (z : RiemannSphere) = ((a * z + b : ℂ) : RiemannSphere) :=
  rfl

private theorem RiemannSphere.crossRatioScale_ne_zero (a b c : ℂ) (hab : a ≠ b) (hbc : b ≠ c) :
    (b - c) / (b - a) ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hab.symm)

private theorem RiemannSphere.crossRatioResidue_ne_zero (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : (c - a) * ((b - c) / (b - a)) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hac.symm) (crossRatioScale_ne_zero a b c hab hbc)

private def
    RiemannSphere.threePointBiholomorph (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Biholomorph :=
  ((affineBiholomorph 1 (-c) one_ne_zero).trans reciprocalBiholomorph).trans
    (affineBiholomorph ((c - a) * ((b - c) / (b - a))) ((b - c) / (b - a))
      (crossRatioResidue_ne_zero a b c hab hac hbc))

private theorem RiemannSphere.threePointBiholomorph_coe (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (z : ℂ) (hz : z ≠ c) :
    threePointBiholomorph a b c hab hac hbc (z : RiemannSphere) =
      ((((z - a) * (b - c)) / ((z - c) * (b - a)) : ℂ) : RiemannSphere) := by
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (z : RiemannSphere))) =
      _
  simp only [affineBiholomorph_coe, one_mul, ← sub_eq_add_neg, reciprocalBiholomorph_apply,
    reciprocal_coe, infinityParametrization_of_ne (sub_ne_zero.mpr hz), affineBiholomorph_coe]
  congr 1
  field_simp
  ring

@[simp]
private theorem RiemannSphere.threePointBiholomorph_third (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    threePointBiholomorph a b c hab hac hbc (c : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) := by
  have hinfty (a b : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  have hreciprocal : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (c : RiemannSphere))) =
      _
  simp [hinfty]

@[simp]
private theorem RiemannSphere.threePointBiholomorph_infty (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    threePointBiholomorph a b c hab hac hbc ((OnePoint.infty) : RiemannSphere) =
      (((b - c) / (b - a) : ℂ) : RiemannSphere) := by
  have hinfty (a b : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha ((OnePoint.infty) : RiemannSphere) =
      ((OnePoint.infty) : RiemannSphere) :=
    rfl
  have hreciprocal : reciprocal (OnePoint.infty) = ((0 : ℂ) : RiemannSphere) := rfl
  change
    affineBiholomorph _ _ _
        (reciprocalBiholomorph
          (affineBiholomorph 1 (-c) one_ne_zero ((OnePoint.infty) : RiemannSphere))) =
      _
  simp [hinfty, hreciprocal]

private def RiemannSphere.MobiusCircle.crossRatio (a b c z : ℂ) : ℂ :=
  ((z - a) * (b - c)) / ((z - c) * (b - a))

private def RiemannSphere.MobiusCircle.coefficient (a b c : ℂ) : ℂ :=
  (b - c) / (b - a)

private def RiemannSphere.MobiusCircle.orientation (a b c : ℂ) : ℝ :=
  -(coefficient a b c).im

private theorem RiemannSphere.MobiusCircle.crossRatio_eq_coefficient (a b c z : ℂ) :
    crossRatio a b c z = coefficient a b c * ((z - a) / (z - c)) := by
  simp only [crossRatio, coefficient, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem
    RiemannSphere.MobiusCircle.coefficient_ne_zero {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    coefficient a b c ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hba)

private theorem RiemannSphere.MobiusCircle.unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

private theorem RiemannSphere.MobiusCircle.coefficient_mul_eq_conj_mul {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) :
    coefficient a b c * a = conj (coefficient a b c) * c := by
  have ha0 := unit_ne_zero ha
  have hb0 := unit_ne_zero hb
  have hc0 := unit_ne_zero hc
  have hba0 := sub_ne_zero.mpr hba
  simp only [coefficient, map_div₀, map_sub, ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb,
    ← Complex.inv_eq_conj hc]
  field_simp
  ring

private theorem
    RiemannSphere.MobiusCircle.orientation_ne_zero {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) : orientation a b c ≠ 0 := by
  intro h
  have him : (coefficient a b c).im = 0 := neg_eq_zero.mp h
  have hd := coefficient_mul_eq_conj_mul ha hb hc hba
  rw [Complex.conj_eq_iff_im.mpr him] at hd
  exact hac (mul_left_cancel₀ (coefficient_ne_zero hba hbc) hd)

private theorem RiemannSphere.MobiusCircle.numerator_im {a c d : ℂ} (hc : ‖c‖ = 1)
    (hd : d * a = conj d * c) (z : ℂ) :
    (d * (z - a) * conj (z - c)).im = d.im * (Complex.normSq z - 1) := by
  have hcross : conj (d * z * conj c) = conj d * c * conj z := by
    simp only [map_mul, starRingEnd_self_apply]
    ring
  have hconst : conj d * c * conj c = conj d := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  have heq :
    d * (z - a) * conj (z - c) =
      d * (Complex.normSq z : ℂ) - (d * z * conj c + conj (d * z * conj c)) + conj d := by
    calc
      d * (z - a) * conj (z - c) =
          d * (z * conj z) - (d * z * conj c + d * a * conj z) + d * a * conj c := by
        rw [map_sub]
        ring
      _ = _ := by rw [Complex.mul_conj, hd, hconst, hcross]
  rw [heq]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_im]
  ring

private theorem RiemannSphere.MobiusCircle.crossRatio_im {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    (crossRatio a b c z).im = orientation a b c * (1 - ‖z‖ ^ 2) / Complex.normSq (z - c) := by
  have heq :
    crossRatio a b c z =
      (coefficient a b c * (z - a) * conj (z - c)) / (Complex.normSq (z - c) : ℂ) := by
    rw [crossRatio_eq_coefficient, div_eq_mul_inv, Complex.inv_def]
    simp only [div_eq_mul_inv, Complex.ofReal_inv]
    ring
  rw [heq, Complex.div_ofReal_im, numerator_im hc (coefficient_mul_eq_conj_mul ha hb hc hba),
    Complex.normSq_eq_norm_sq]
  unfold orientation
  ring

private theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    orientation a b c * (crossRatio a b c z).im =
      orientation a b c ^ 2 * (1 - ‖z‖ ^ 2) / Complex.normSq (z - c) := by
  rw [crossRatio_im ha hb hc hba]
  ring

private theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im_pos_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hzc : z ≠ c) : 0 < orientation a b c * (crossRatio a b c z).im ↔ ‖z‖ < 1 := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < Complex.normSq (z - c) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzc)
  rw [orientation_mul_crossRatio_im ha hb hc hba, div_pos_iff_of_pos_right hd,
    mul_pos_iff_of_pos_left hK, sub_pos, sq_lt_one_iff₀ (norm_nonneg z)]

private theorem RiemannSphere.MobiusCircle.orientation_mul_crossRatio_im_neg_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hzc : z ≠ c) : orientation a b c * (crossRatio a b c z).im < 0 ↔ 1 < ‖z‖ := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < Complex.normSq (z - c) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzc)
  have heq :
    -(orientation a b c * (crossRatio a b c z).im) =
      orientation a b c ^ 2 * (‖z‖ ^ 2 - 1) / Complex.normSq (z - c) := by
    rw [orientation_mul_crossRatio_im ha hb hc hba]
    ring
  rw [← neg_pos, heq, div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_left hK, sub_pos,
    one_lt_sq_iff₀ (norm_nonneg z)]

private theorem RiemannSphere.MobiusCircle.orientation_mul_coefficient_im (a b c : ℂ) :
    orientation a b c * (coefficient a b c).im = -(orientation a b c ^ 2) := by
  unfold orientation
  ring

private theorem
    RiemannSphere.MobiusCircle.orientation_mul_coefficient_im_neg {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    orientation a b c * (coefficient a b c).im < 0 := by
  rw [orientation_mul_coefficient_im]
  exact neg_neg_of_pos (sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac))

private theorem
    RiemannSphere.MobiusCircle.crossRatio_at_zero (a b c : ℂ) : crossRatio a b c a = 0 := by
  simp [crossRatio]

private theorem
    RiemannSphere.MobiusCircle.crossRatio_at_one {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    crossRatio a b c b = 1 := by
  unfold crossRatio
  rw [mul_comm (b - c) (b - a)]
  exact div_self (mul_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hbc))

private def RiemannSphere.finiteImage (s : Set ℂ) : Set RiemannSphere :=
  ((↑) : ℂ → RiemannSphere) '' s

@[simp]
private theorem RiemannSphere.coe_mem_finiteImage_iff (s : Set ℂ) (z : ℂ) :
    (z : RiemannSphere) ∈ finiteImage s ↔ z ∈ s := by simp [finiteImage]

@[simp]
private theorem RiemannSphere.infty_not_mem_finiteImage (s : Set ℂ) :
    ((OnePoint.infty) : RiemannSphere) ∉ finiteImage s := by simp [finiteImage]

private theorem
    RiemannSphere.crossRatio_holomorphicOn_disc {a b c : ℂ} (hab : a ≠ b) (hc : ‖c‖ = 1) :
    ContDiffOn ℂ ω (MobiusCircle.crossRatio a b c) {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  have hzc : z ≠ c := by
    intro he
    subst z
    exact (not_lt_of_ge hc.ge) hz
  have hden : (z - c) * (b - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hab.symm)
  have hn : ContDiffAt ℂ ω (fun w : ℂ => (w - a) * (b - c)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  have hd : ContDiffAt ℂ ω (fun w : ℂ => (w - c) * (b - a)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  exact (hn.div hd hden).contDiffWithinAt

private def RiemannSphere.closedDiscWithoutPole (c : ℂ) : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ z ≠ c}

private def RiemannSphere.closedOrientedHalfPlane (k : ℝ) : Set ℂ :=
  {w | 0 ≤ k * w.im}

private def RiemannSphere.finiteImageHomeomorph (s : Set ℂ) : s ≃ₜ finiteImage s :=
  (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.homeomorphImage s

@[simp]
private theorem RiemannSphere.finiteImageHomeomorph_symm_apply_coe (s : Set ℂ) (p : finiteImage s) :
    (((finiteImageHomeomorph s).symm p : ℂ) : RiemannSphere) = (p : RiemannSphere) := by
  exact congrArg Subtype.val ((finiteImageHomeomorph s).apply_symm_apply p)

private theorem RiemannSphere.orientation_mul_crossRatio_im_nonneg_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) {z : ℂ}
    (hzc : z ≠ c) :
    0 ≤ MobiusCircle.orientation a b c * (MobiusCircle.crossRatio a b c z).im ↔ ‖z‖ ≤ 1 := by
  have h :=
    not_congr (MobiusCircle.orientation_mul_crossRatio_im_neg_iff ha hb hc hab.symm hbc hac hzc)
  simpa only [not_lt] using h

private theorem
    RiemannSphere.threePointBiholomorph_mem_closedHalfPlane_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p ∈
        finiteImage (closedOrientedHalfPlane (MobiusCircle.orientation a b c)) ↔
      p ∈ finiteImage (closedDiscWithoutPole c) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [threePointBiholomorph_infty]
    simp only [coe_mem_finiteImage_iff, infty_not_mem_finiteImage, iff_false,
      closedOrientedHalfPlane, Set.mem_ofPred_eq]
    exact not_le_of_gt (MobiusCircle.orientation_mul_coefficient_im_neg ha hb hc hab.symm hbc hac)
  | coe z =>
    by_cases hzc : z = c
    · subst z
      simp [closedDiscWithoutPole]
    · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc]
      simp only [coe_mem_finiteImage_iff, closedOrientedHalfPlane, closedDiscWithoutPole,
        Set.mem_ofPred_eq, and_iff_left hzc]
      exact orientation_mul_crossRatio_im_nonneg_iff hab hac hbc ha hb hc hzc

private def
    RiemannSphere.closedDiscHalfPlaneSphereHomeomorph {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    finiteImage (closedDiscWithoutPole c) ≃ₜ
      finiteImage (closedOrientedHalfPlane (MobiusCircle.orientation a b c)) :=
  (threePointBiholomorph a b c hab hac hbc).toHomeomorph.subtype
    (fun p => (threePointBiholomorph_mem_closedHalfPlane_iff hab hac hbc ha hb hc p).symm)

private def RiemannSphere.closedDiscHalfPlaneHomeomorph {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    closedDiscWithoutPole c ≃ₜ closedOrientedHalfPlane (MobiusCircle.orientation a b c) :=
  ((finiteImageHomeomorph (closedDiscWithoutPole c)).trans
        (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc)).trans
    (finiteImageHomeomorph (closedOrientedHalfPlane (MobiusCircle.orientation a b c))).symm

private theorem
    RiemannSphere.closedDiscHalfPlaneHomeomorph_sphere {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (z : closedDiscWithoutPole c) :
    (((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z :
            closedOrientedHalfPlane (MobiusCircle.orientation a b c)) :
          ℂ) :
        RiemannSphere) =
      threePointBiholomorph a b c hab hac hbc ((z : ℂ) : RiemannSphere) := by
  exact
    finiteImageHomeomorph_symm_apply_coe
      (closedOrientedHalfPlane (MobiusCircle.orientation a b c))
      (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc
        (finiteImageHomeomorph (closedDiscWithoutPole c) z))

@[simp]
private theorem
    RiemannSphere.closedDiscHalfPlaneHomeomorph_apply {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (z : closedDiscWithoutPole c) :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ) =
      MobiusCircle.crossRatio a b c z := by
  apply OnePoint.coe_injective
  rw [closedDiscHalfPlaneHomeomorph_sphere,
    threePointBiholomorph_coe a b c hab hac hbc z z.property.2]
  rfl

private theorem RiemannSphere.closedDiscHalfPlaneHomeomorph_strict_iff {a b c : ℂ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (z : closedDiscWithoutPole c) :
    0 <
        MobiusCircle.orientation a b c *
          (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ).im ↔
      ‖(z : ℂ)‖ < 1 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact MobiusCircle.orientation_mul_crossRatio_im_pos_iff ha hb hc hab.symm hbc hac z.property.2

private def TriangleUniformizationGluing.halfPlaneOrientationSign (k : ℝ) : ℝ :=
  if 0 < k then 1 else -1

private theorem TriangleUniformizationGluing.halfPlaneOrientationSign_sq (k : ℝ) :
    halfPlaneOrientationSign k ^ 2 = 1 := by
  unfold halfPlaneOrientationSign
  split_ifs <;> norm_num

private theorem
    TriangleUniformizationGluing.halfPlaneOrientationSign_nonneg_iff {k : ℝ} (hk : k ≠ 0)
    (t : ℝ) : 0 ≤ halfPlaneOrientationSign k * t ↔ 0 ≤ k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_nonneg_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_nonneg]
    constructor
    · exact fun ht => mul_nonneg_of_nonpos_of_nonpos hn.le ht
    · intro ht
      by_contra h
      exact (not_le_of_gt (mul_neg_of_neg_of_pos hn (lt_of_not_ge h))) ht

private theorem TriangleUniformizationGluing.halfPlaneOrientationSign_pos_iff {k : ℝ} (hk : k ≠ 0)
    (t : ℝ) : 0 < halfPlaneOrientationSign k * t ↔ 0 < k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_pos_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_pos]
    constructor
    · exact fun ht => mul_pos_of_neg_of_neg hn ht
    · intro ht
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn.le (le_of_not_gt h))) ht

private def TriangleUniformizationGluing.halfFordHomeomorphExtension {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (z : ℍ) : ℂ := by
  classical exact if hz : z ∈ SpecialPeriods.Triangle.halfFordRegion then (e ⟨z, hz⟩ : ℂ) else 0

@[simp]
private theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_coe {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (z : SpecialPeriods.Triangle.halfFordRegion) : halfFordHomeomorphExtension e z = (e z : ℂ) := by
  simp only [halfFordHomeomorphExtension, dite_eq_left z.property]

private theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_of_mem {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    {z : ℍ} (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    halfFordHomeomorphExtension e z = (e ⟨z, hz⟩ : ℂ) :=
  halfFordHomeomorphExtension_coe e ⟨z, hz⟩

private theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_continuousOn {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k) :
    ContinuousOn (halfFordHomeomorphExtension e) SpecialPeriods.Triangle.halfFordRegion := by
  rw [continuousOn_iff_continuous_domRestrict]
  change
    Continuous (fun z : SpecialPeriods.Triangle.halfFordRegion => halfFordHomeomorphExtension e z)
  simp only [halfFordHomeomorphExtension_coe]
  exact continuous_subtype_val.comp e.continuous

private theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_isProperMap {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k) :
    IsProperMap
      (fun z : SpecialPeriods.Triangle.halfFordRegion => halfFordHomeomorphExtension e z) := by
  have hc : IsClosed (RiemannSphere.closedOrientedHalfPlane k) :=
    isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)
  simpa only [Function.comp_def, halfFordHomeomorphExtension_coe] using
    hc.isProperMap_subtypeVal.comp e.isProperMap

private def TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph {k : ℝ} (hk : k ≠ 0)
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (hinterior :
      ∀ z : SpecialPeriods.Triangle.halfFordRegion,
        0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior) :
    SignedHalfPlaneMap where
  toFun := halfFordHomeomorphExtension e
  continuousOn := halfFordHomeomorphExtension_continuousOn e
  boundary_real := by
    intro z hz hi
    rw [halfFordHomeomorphExtension_of_mem e hz]
    have hn : ¬0 < k * (e ⟨z, hz⟩ : ℂ).im := fun h => hi ((hinterior ⟨z, hz⟩).mp h)
    have he : k * (e ⟨z, hz⟩ : ℂ).im = 0 := le_antisymm (le_of_not_gt hn) (e ⟨z, hz⟩).property
    exact (mul_eq_zero.mp he).resolve_left hk
  orientation := halfPlaneOrientationSign k
  orientation_sq := halfPlaneOrientationSign_sq k
  injOn := by
    intro z hz w hw he
    rw [halfFordHomeomorphExtension_of_mem e hz, halfFordHomeomorphExtension_of_mem e hw] at he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_ofPred_eq, halfFordHomeomorphExtension_of_mem e hz,
        halfPlaneOrientationSign_nonneg_iff hk]
      exact (e ⟨z, hz⟩).property
    · intro hw
      have hwk : w ∈ RiemannSphere.closedOrientedHalfPlane k :=
        (halfPlaneOrientationSign_nonneg_iff hk w.im).mp hw
      obtain ⟨z, hz⟩ := e.surjective ⟨w, hwk⟩
      refine ⟨z, z.property, ?_⟩
      rw [halfFordHomeomorphExtension_coe]
      exact congrArg Subtype.val hz
  interior_positive := by
    intro z hz
    have hzR : z ∈ SpecialPeriods.Triangle.halfFordRegion :=
      SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz
    rw [halfFordHomeomorphExtension_of_mem e hzR, halfPlaneOrientationSign_pos_iff hk]
    exact (hinterior ⟨z, hzR⟩).mpr hz

@[simp]
private theorem
    TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph_apply {k : ℝ} (hk : k ≠ 0)
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (hinterior :
      ∀ z : SpecialPeriods.Triangle.halfFordRegion,
        0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior)
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    signedHalfPlaneMapOfHomeomorph hk e hinterior z = (e z : ℂ) :=
  halfFordHomeomorphExtension_coe e z

private def SpecialPeriods.Triangle.triangleClosedRegion : Set ℂ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖}

private theorem
    SpecialPeriods.Triangle.boundaryHeight_pos_of_closed_bounds {x : ℝ} (hl : stripLeft ≤ x)
    (hr : x ≤ -1 / 2) : 0 < boundaryHeight x := by
  have hlo : 0 < x + 2 := by linarith [neg_two_lt_stripLeft]
  have hhi : 0 < -x := by linarith
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos hlo hhi]

private theorem SpecialPeriods.Triangle.circle_closed_epigraph_iff {z : ℂ} (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ -1 / 2) : (0 < z.im ∧ 1 ≤ ‖z + 1‖) ↔ boundaryHeight z.re ≤ z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_le_left hy.le).mpr
    have hs := (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro hh
    have hy : 0 < z.im := (boundaryHeight_pos_of_closed_bounds hl hr).trans_le hh
    refine ⟨hy, ?_⟩
    apply (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_le_left hy.le).mp hh
    nlinarith

private theorem SpecialPeriods.Triangle.mem_triangleClosedRegion_iff_epigraph (z : ℂ) :
    z ∈ triangleClosedRegion ↔ stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ boundaryHeight z.re ≤ z.im := by
  constructor
  · rintro ⟨hl, hr, hi, hn⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mp ⟨hi, hn⟩⟩
  · rintro ⟨hl, hr, hh⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mpr hh⟩

private def SpecialPeriods.Triangle.triangleClosedStrip : Set ℂ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im}

private theorem SpecialPeriods.Triangle.triangleOpenStrip_eq_reProdIm :
    triangleOpenStrip = (Set.Ioo stripLeft (-1 / 2)) ×ℂ (Set.Ioi 0) := by
  ext z
  change
    (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im) ↔
      ((stripLeft < z.re ∧ z.re < -1 / 2) ∧ 0 < z.im)
  exact and_assoc.symm

private theorem SpecialPeriods.Triangle.triangleClosedStrip_eq_reProdIm :
    triangleClosedStrip = (Set.Icc stripLeft (-1 / 2)) ×ℂ (Set.Ici 0) := by
  ext z
  change
    (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im) ↔
      ((stripLeft ≤ z.re ∧ z.re ≤ -1 / 2) ∧ 0 ≤ z.im)
  exact and_assoc.symm

private theorem SpecialPeriods.Triangle.closure_triangleOpenStrip :
    closure triangleOpenStrip = triangleClosedStrip := by
  rw [triangleOpenStrip_eq_reProdIm, Complex.closure_reProdIm,
    closure_Ioo (show stripLeft ≠ -1 / 2 by linarith [stripLeft_lt_neg_one]), closure_Ioi, ←
    triangleClosedStrip_eq_reProdIm]

private theorem SpecialPeriods.Triangle.triangleClosedRegion_eq_preimage_strip :
    triangleClosedRegion = triangleHeightShift ⁻¹' triangleClosedStrip := by
  ext z
  rw [mem_triangleClosedRegion_iff_epigraph]
  simp only [Set.mem_preimage, triangleClosedStrip, Set.mem_ofPred_eq, triangleHeightShift_re,
    triangleHeightShift_im, sub_nonneg]

private theorem SpecialPeriods.Triangle.closure_triangleInterior :
    closure triangleInterior = triangleClosedRegion := by
  rw [triangleInterior_eq_preimage_strip, ← triangleHeightShift.preimage_closure,
    closure_triangleOpenStrip, ← triangleClosedRegion_eq_preimage_strip]

private theorem SpecialPeriods.Triangle.triangle_norm_add_one_le_norm {z : ℂ} (hz : z.re ≤ -1 / 2) :
    ‖z + 1‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg (z + 1)) (norm_nonneg z)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero]
  nlinarith

private theorem SpecialPeriods.Triangle.coe_mem_triangleClosedRegion_iff_halfFordRegion (z : ℍ) :
    (z : ℂ) ∈ triangleClosedRegion ↔ z ∈ halfFordRegion := by
  change
    (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖(z : ℂ) + 1‖) ↔
      ((stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ 1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖) ∧
        z.re ≤ -(1 / 2))
  constructor
  · rintro ⟨hl, hr, _, hn⟩
    refine ⟨⟨hl, ?_, hn, hn.trans (triangle_norm_add_one_le_norm hr)⟩, by linarith⟩
    linarith [stripRight_pos]
  · rintro ⟨hz, hr⟩
    exact ⟨hz.1, by linarith, z.im_pos, hz.2.2.1⟩

private theorem RiemannMapping.isCompact_discHomeomorph_preimage_closedBall {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {r : ℝ} (hr : r < 1) :
    IsCompact
      ((Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))) := by
  apply IsCompact.image _ continuous_subtype_val
  apply e.isCompact_preimage.mpr
  apply
    Topology.IsInducing.subtypeVal.isCompact_preimage' (ProperSpace.isCompact_closedBall _ _) ?_
  simpa only [Subtype.range_coe] using Metric.closedBall_subset_ball hr

private theorem RiemannMapping.tendsto_norm_discHomeomorph_of_notMem {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {α : Type*} {l : Filter α} {z : α → U} {a : ℂ} (ha : a ∉ U)
    (hz : Filter.Tendsto (fun i => (z i : ℂ)) l (𝓝 a)) :
    Filter.Tendsto (fun i => ‖(e (z i) : ℂ)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := isCompact_discHomeomorph_preimage_closedBall e hr
    have haK : a ∉ K := by
      rintro ⟨w, _, hwa⟩
      exact ha (hwa ▸ w.property)
    have hevent : ∀ᶠ i in l, (z i : ℂ) ∉ K :=
      hz.eventually (hK.isClosed.isOpen_compl.mem_nhds haK)
    filter_upwards [hevent] with i hi
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨z i, ?_, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hle
  · intro r hr
    apply Filter.Eventually.of_forall
    intro i
    have hi : ‖(e (z i) : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (e (z i)).property
    exact hi.trans hr

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_cocompact {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : D → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := RiemannMapping.isCompact_discHomeomorph_preimage_closedBall e hr
    have hesc : ∀ᶠ i in l, z i ∉ K := hz.eventually hK.compl_mem_cocompact
    filter_upwards [hesc, hmem] with i hi him
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨⟨z i, him⟩, ?_, rfl⟩
    have hh := he ⟨z i, him⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ← hh] using hle
  · intro r hr
    filter_upwards [hmem] with i hi
    have hh := he ⟨z i, hi⟩
    have hb : ‖f (z i)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, ← hh] using (e ⟨z i, hi⟩).property
    exact hb.trans hr

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_norm_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => ‖z i‖) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_cocompact e he _ hmem
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hz

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_im_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => (z i).im) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) :=
  tendsto_norm_discHomeomorph_of_norm_atTop e he
    (Filter.tendsto_atTop_mono (fun i => Complex.im_le_norm (z i)) hz) hmem

private def RiemannBoundary.logHalfStrip (a c : ℝ) (q : ℂ) : ℂ :=
  a - Complex.I * c * Complex.log q

@[simp]
private theorem RiemannBoundary.logHalfStrip_re (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).re = a + c * q.arg := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_im]

@[simp]
private theorem RiemannBoundary.logHalfStrip_im (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).im = -c * Real.log ‖q‖ := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_re]

private theorem RiemannBoundary.tendsto_logHalfStrip_im_atTop (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q).im) (𝓝[≠] 0) Filter.atTop := by
  simp only [logHalfStrip_im]
  exact
    (Filter.tendsto_const_mul_atTop_of_neg (neg_neg_of_pos hc)).mpr
      (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)

private theorem RiemannBoundary.tendsto_norm_discHomeomorph_logHalfStrip {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (a : ℝ) {c : ℝ}
    (hc : 0 < c) (hmem : ∀ᶠ q in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), logHalfStrip a c q ∈ D) :
    Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ)) (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_im_atTop e he _ hmem
  apply (tendsto_logHalfStrip_im_atTop a hc).mono_left
  apply nhdsWithin_mono
  intro z hz
  change 0 < z.im at hz
  change z ≠ 0
  intro heq
  rw [heq, Complex.zero_im] at hz
  exact (lt_irrefl 0) hz

private def RiemannBoundary.onePointLogHalfStrip (a c : ℝ) (q : ℂ) : OnePoint ℂ :=
  if q = 0 then (OnePoint.infty) else (logHalfStrip a c q : OnePoint ℂ)

@[simp]
private theorem RiemannBoundary.onePointLogHalfStrip_zero (a c : ℝ) :
    onePointLogHalfStrip a c 0 = (OnePoint.infty) := by simp [onePointLogHalfStrip]

private theorem RiemannBoundary.onePointLogHalfStrip_of_ne_zero (a c : ℝ) {q : ℂ} (hq : q ≠ 0) :
    onePointLogHalfStrip a c q = (logHalfStrip a c q : OnePoint ℂ) := by
  simp [onePointLogHalfStrip, hq]

private theorem RiemannBoundary.tendsto_logHalfStrip_cocompact (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (logHalfStrip a c) (𝓝[≠] 0) (Filter.cocompact ℂ) := by
  have hn : Filter.Tendsto (fun q : ℂ => ‖logHalfStrip a c q‖) (𝓝[≠] 0) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun q => Complex.im_le_norm (logHalfStrip a c q))
      (tendsto_logHalfStrip_im_atTop a hc)
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn

private theorem RiemannBoundary.tendsto_coe_logHalfStrip_infty (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q : OnePoint ℂ)) (𝓝[≠] 0)
      (𝓝 (OnePoint.infty)) := by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  exact hcoe.comp (tendsto_logHalfStrip_cocompact a hc)

private theorem
    RiemannBoundary.continuousAt_onePointLogHalfStrip_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (onePointLogHalfStrip a c) 0 := by
  rw [continuousAt_iff_punctured_nhds, onePointLogHalfStrip_zero]
  apply (tendsto_coe_logHalfStrip_infty a hc).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (onePointLogHalfStrip_of_ne_zero a c hq).symm

private def RiemannBoundary.onePointDomain (D : Set ℂ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' D

@[simp]
private theorem RiemannBoundary.coe_mem_onePointDomain {D : Set ℂ} {z : ℂ} :
    (z : OnePoint ℂ) ∈ onePointDomain D ↔ z ∈ D := by exact OnePoint.coe_injective.mem_set_image

@[simp]
private theorem RiemannBoundary.infty_notMem_onePointDomain (D : Set ℂ) :
    (OnePoint.infty) ∉ onePointDomain D :=
  OnePoint.infty_notMem_image_coe

private theorem RiemannBoundary.isOpen_onePointDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (onePointDomain D) :=
  OnePoint.isOpen_image_coe.mpr hD

private def RiemannBoundary.onePointDomainHomeomorph (D : Set ℂ) : D ≃ₜ onePointDomain D :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage D

@[simp]
private theorem RiemannBoundary.onePointDomainHomeomorph_apply_coe (D : Set ℂ) (z : D) :
    (onePointDomainHomeomorph D z : OnePoint ℂ) = (z : ℂ) :=
  rfl

private def
    RiemannBoundary.onePointDomainDiscHomeomorph {D : Set ℂ} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) :
    onePointDomain D ≃ₜ Metric.ball (0 : ℂ) 1 :=
  (onePointDomainHomeomorph D).symm.trans e

@[simp]
private theorem RiemannBoundary.onePointDomainDiscHomeomorph_apply {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    onePointDomainDiscHomeomorph e (onePointDomainHomeomorph D z) = e z := by
  simp [onePointDomainDiscHomeomorph]

private theorem RiemannBoundary.onePointDomainDiscHomeomorph_representative {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (b : ℂ)
    (z : onePointDomain D) : (z : OnePoint ℂ).elim b f = (onePointDomainDiscHomeomorph e z : ℂ) :=
  by
  obtain ⟨w, rfl⟩ := (onePointDomainHomeomorph D).surjective z
  simpa only [onePointDomainHomeomorph_apply_coe, OnePoint.elim_some,
    onePointDomainDiscHomeomorph_apply] using he w

private theorem
    RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact {D : Set ℂ} {α : Type*}
    {l : Filter α} [Filter.NeBot l] {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : ((OnePoint.infty) : OnePoint ℂ) ∈ frontier (onePointDomain D) :=
  by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  have hcl : ((OnePoint.infty) : OnePoint ℂ) ∈ closure (onePointDomain D) := by
    apply isClosed_closure.mem_of_tendsto (hcoe.comp hz)
    filter_upwards [hmem] with i hi
    exact subset_closure (coe_mem_onePointDomain.mpr hi)
  exact ⟨hcl, fun hi => infty_notMem_onePointDomain D (interior_subset hi)⟩

private def SpecialPeriods.Triangle.triangleVerticalRay (t : ℝ) : ℂ :=
  -1 + ((t : ℂ) + 2) * Complex.I

@[simp]
private theorem SpecialPeriods.Triangle.triangleVerticalRay_re (t : ℝ) :
    (triangleVerticalRay t).re = -1 := by simp [triangleVerticalRay]

@[simp]
private theorem SpecialPeriods.Triangle.triangleVerticalRay_im (t : ℝ) :
    (triangleVerticalRay t).im = t + 2 := by simp [triangleVerticalRay]

private theorem SpecialPeriods.Triangle.triangleVerticalRay_mem {t : ℝ} (ht : 0 ≤ t) :
    triangleVerticalRay t ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph, triangleVerticalRay_re, triangleVerticalRay_im]
  refine ⟨stripLeft_lt_neg_one, by norm_num, ?_⟩
  linarith [boundaryHeight_le_one (-1)]

private theorem SpecialPeriods.Triangle.triangleVerticalRay_eventually_mem :
    ∀ᶠ t : ℝ in Filter.atTop, triangleVerticalRay t ∈ triangleInterior :=
  (Filter.eventually_ge_atTop (0 : ℝ)).mono fun _ ht => triangleVerticalRay_mem ht

private theorem SpecialPeriods.Triangle.triangleVerticalRay_im_tendsto :
    Filter.Tendsto (fun t : ℝ => (triangleVerticalRay t).im) Filter.atTop Filter.atTop := by
  simpa only [triangleVerticalRay_im, id_eq] using
    (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) Filter.tendsto_id)

private theorem SpecialPeriods.Triangle.triangleVerticalRay_norm_tendsto :
    Filter.Tendsto (fun t : ℝ => ‖triangleVerticalRay t‖) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun t => Complex.im_le_norm (triangleVerticalRay t))
    triangleVerticalRay_im_tendsto

private theorem SpecialPeriods.Triangle.triangleVerticalRay_tendsto_cocompact :
    Filter.Tendsto triangleVerticalRay Filter.atTop (Filter.cocompact ℂ) := by
  simpa only [Metric.cobounded_eq_cocompact] using
    tendsto_norm_atTop_iff_cobounded.mp triangleVerticalRay_norm_tendsto

private theorem SpecialPeriods.Triangle.triangle_infty_mem_frontier :
    ((OnePoint.infty) : OnePoint ℂ) ∈
      frontier (RiemannBoundary.onePointDomain triangleInterior) :=
  RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact
    triangleVerticalRay_tendsto_cocompact triangleVerticalRay_eventually_mem

private theorem SpecialPeriods.Triangle.triangle_infty_mem_closure :
    ((OnePoint.infty) : OnePoint ℂ) ∈ closure (RiemannBoundary.onePointDomain triangleInterior) :=
  frontier_subset_closure triangle_infty_mem_frontier

private theorem RiemannMapping.uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ι → E → F} {s U : Set E} {r : ℝ} (hr₀ : 0 < r)
    (hU : Metric.thickening r s ⊆ U) (hfd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) : UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (Metric.self_subset_thickening hr₀ _).trans hU
  rw [(Metric.uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff
      Metric.uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use Min.min δ r, by positivity
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Set.prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [Metric.thickening_eq_biUnion_ball, Set.iUnion₂_subset_iff] at hU
  calc
    Dist.dist (f i x) (f i y) ≤ (2 * C / r) * Dist.dist x y := by
      apply Complex.dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [Metric.mem_closedBall, two_mul]
        exact
          dist_le_norm_add_norm _ _ |>.trans <|
            add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

private theorem
    RiemannMapping.equicontinuousAt_of_forall_norm_le {ι E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ι → E → F} {U : Set E} {x : E}
    (hU : U ∈ 𝓝 x) (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    EquicontinuousAt f x := by
  rcases Metric.nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have : Metric.thickening (r / 2) (Metric.ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have :=
    uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le (by positivity) this hfd
        hf |>.equicontinuousOn
      x (by simpa)
  rwa [EquicontinuousWithinAt,
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ (by positivity))] at this

private def RiemannMapping.compactSubsets (U : Set ℂ) : Set (Set ℂ) :=
  {K | K ⊆ U ∧ IsCompact K}

private abbrev RiemannMapping.FunctionSpace (U : Set ℂ) :=
  ℂ →ᵤ[compactSubsets U] ℂ

private def RiemannMapping.evaluation {U : Set ℂ} (f : FunctionSpace U) : ℂ → ℂ :=
  UniformOnFun.toFun (compactSubsets U) f

private theorem RiemannMapping.uniformity_isCountablyGenerated {U : Set ℂ} (hUo : IsOpen U) :
    (𝓤 (FunctionSpace U)).IsCountablyGenerated := by
  have := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let φ : CompactExhaustion U := Inhabited.default
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' φ n)
  · intro n
    exact ⟨Set.image_val_subset, (φ.isCompact n).image continuous_subtype_val⟩
  · exact Set.monotone_image.comp φ.subset
  · rintro K ⟨hKU, hKc⟩
    lift K to Set U using hKU
    rw [← Subtype.isCompact_iff] at hKc
    exact (φ.exists_superset_of_isCompact hKc).imp fun n hn => by gcongr

private theorem RiemannMapping.evaluation_tendstoLocallyUniformlyOn {U : Set ℂ} (hUo : IsOpen U)
    {f : FunctionSpace U} {s : Set (FunctionSpace U)} :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[s] f) U := by
  have h : Filter.Tendsto id (𝓝[s] f) (𝓝 f) := Filter.tendsto_id'.mpr nhdsWithin_le_nhds
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp h) K ⟨hKU, hK⟩

private theorem RiemannMapping.isCompact_closure_of_bounded_holomorphic {U : Set ℂ} (hUo : IsOpen U)
    {s : Set (FunctionSpace U)} (hsd : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    (hsb : ∃ C : ℝ, ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C) : IsCompact (closure s) := by
  obtain ⟨C, hC⟩ := hsb
  apply
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (𝔖 := compactSubsets U) (fun K hK => hK.2)
      (F := evaluation) .id
  · rintro K ⟨hKU, _⟩ z hz
    exact
      (equicontinuousAt_of_forall_norm_le (hUo.mem_nhds (hKU hz))
            (fun f : s => hsd f.val f.property)
            ⟨C, fun f z hz => hC f.val f.property z hz⟩).equicontinuousWithinAt
        K
  · intro K hK x hx
    exact
      ⟨Metric.closedBall 0 C, ProperSpace.isCompact_closedBall _ _, fun f hf => by
        simpa only [mem_closedBall_zero_iff] using hC f hf x (hK.1 hx)⟩

private def RiemannMapping.normalizedClass (U : Set ℂ) (x₀ : ℂ) : Set (FunctionSpace U) :=
  {f |
    Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
      Set.InjOn (evaluation f) U ∧
        DifferentiableOn ℂ (evaluation f) U ∧
          (∀ z ∈ U, deriv (evaluation f) z ≠ 0) ∧ evaluation f x₀ = 0}

private theorem
    RiemannMapping.normalizedClass_compact_closure {U : Set ℂ} (hUo : IsOpen U) (x₀ : ℂ) :
    IsCompact (closure (normalizedClass U x₀)) := by
  apply isCompact_closure_of_bounded_holomorphic hUo (fun f hf => hf.2.2.1)
  exact ⟨1, fun f hf z hz => (mem_ball_zero_iff.mp (hf.1 hz)).le⟩

end Mathoverflow1973

end
