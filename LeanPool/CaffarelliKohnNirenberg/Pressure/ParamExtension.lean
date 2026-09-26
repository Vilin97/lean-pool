/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Param Extension

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The scalar pairing of a parameterized test family with zeroth, first, and
second order slice data on a fixed compact set. -/
@[expose]
def parametricPairing {X : Type} (Ψ : X → Vec3 → ℝ)
    (g₀ : Vec3 → ℝ) (g₁ : Vec3 → Vec3)
    (g₂ : Vec3 → Fin 3 → Fin 3 → ℝ) (x : X) : ℝ :=
  (∫ y, g₀ y * Ψ x y) +
    ∑ i, (∫ y, g₁ y i * spatialDeriv (Ψ x) i y) +
    ∑ i, ∑ j, (∫ y, g₂ y i j * mixedSecond (Ψ x) i j y)

/-- A fixed compact support and joint continuity through second order make the
parameterized slice pairing continuous. -/
theorem continuous_parametricPairing {X : Type} [TopologicalSpace X]
    {K : Set Vec3} (hK : IsCompact K) (Ψ : X → Vec3 → ℝ)
    (g₀ : Vec3 → ℝ) (g₁ : Vec3 → Vec3)
    (g₂ : Vec3 → Fin 3 → Fin 3 → ℝ)
    (hΨ₀ : Continuous (fun z : X × Vec3 => Ψ z.1 z.2))
    (hΨ₁ : ∀ i : Fin 3,
      Continuous (fun z : X × Vec3 => spatialDeriv (Ψ z.1) i z.2))
    (hΨ₂ : ∀ i j : Fin 3,
      Continuous (fun z : X × Vec3 => mixedSecond (Ψ z.1) i j z.2))
    (hK₀ : ∀ x y, y ∉ K → Ψ x y = 0)
    (hK₁ : ∀ x y i, y ∉ K → spatialDeriv (Ψ x) i y = 0)
    (hK₂ : ∀ x y i j, y ∉ K → mixedSecond (Ψ x) i j y = 0)
    (hg₀ : IntegrableOn g₀ K volume)
    (hg₁ : IntegrableOn g₁ K volume)
    (hg₂ : IntegrableOn g₂ K volume) :
    Continuous (parametricPairing Ψ g₀ g₁ g₂) := by
  have h₁ : ∀ i : Fin 3, IntegrableOn (fun y => g₁ y i) K volume := by
    intro i
    have hi :=
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrableOn_comp hg₁
    convert hi using 1
    ext y
    rfl
  have h₂ : ∀ i j : Fin 3,
      IntegrableOn (fun y => g₂ y i j) K volume := by
    intro i j
    have hi : IntegrableOn (fun y => g₂ y i) K volume := by
      have hi' :=
        (ContinuousLinearMap.proj i :
          (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)).integrableOn_comp hg₂
      convert hi' using 1
      ext y
      rfl
    have hij :=
      (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).integrableOn_comp hi
    convert hij using 1
    ext y
    rfl
  have h₀c : Continuous (fun x => ∫ y, g₀ y * Ψ x y) := by
    apply continuousOn_univ.mp
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (ContinuousLinearMap.lsmul ℝ ℝ) hK hΨ₀.continuousOn
          (fun x y _ hy => hK₀ x y hy) hg₀)
  have h₁c : ∀ i : Fin 3,
      Continuous (fun x => ∫ y, g₁ y i * spatialDeriv (Ψ x) i y) := by
    intro i
    apply continuousOn_univ.mp
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (ContinuousLinearMap.lsmul ℝ ℝ) hK (hΨ₁ i).continuousOn
          (fun x y _ hy => hK₁ x y i hy) (h₁ i))
  have h₂c : ∀ i j : Fin 3,
      Continuous (fun x => ∫ y, g₂ y i j * mixedSecond (Ψ x) i j y) := by
    intro i j
    apply continuousOn_univ.mp
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (ContinuousLinearMap.lsmul ℝ ℝ) hK (hΨ₂ i j).continuousOn
          (fun x y _ hy => hK₂ x y i j hy) (h₂ i j))
  unfold parametricPairing
  have hsum₁ : Continuous (fun x => ∑ i, ∫ y, g₁ y i * spatialDeriv (Ψ x) i y) :=
    continuous_finsetSum _ (fun i _ => h₁c i)
  have hsum₂ : Continuous (fun x => ∑ i, ∑ j,
      ∫ y, g₂ y i j * mixedSecond (Ψ x) i j y) :=
    continuous_finsetSum _ (fun i _ =>
      continuous_finsetSum _ (fun j _ => h₂c i j))
  convert (h₀c.add hsum₁).add hsum₂ using 1

/-- A continuous scalar pairing which vanishes on a dense parameter set
vanishes for every parameter. -/
theorem parametricPairing_eq_zero_of_dense {X : Type} [TopologicalSpace X]
    {Ψ : X → Vec3 → ℝ}
    {g₀ : Vec3 → ℝ} {g₁ : Vec3 → Vec3}
    {g₂ : Vec3 → Fin 3 → Fin 3 → ℝ} {D : Set X}
    (hD : Dense D)
    (hcont : Continuous (parametricPairing Ψ g₀ g₁ g₂))
    (hzero : ∀ x ∈ D, parametricPairing Ψ g₀ g₁ g₂ x = 0) :
    ∀ x, parametricPairing Ψ g₀ g₁ g₂ x = 0 := by
  have heq : parametricPairing Ψ g₀ g₁ g₂ = fun _ => 0 :=
    Continuous.ext_on hD hcont continuous_const hzero
  intro x
  exact congrFun heq x

/-- A continuous scalar pairing which vanishes on a countable dense parameter
set vanishes for every parameter. -/
theorem parametricPairing_eq_zero_of_countable_dense
    {X : Type} [TopologicalSpace X]
    {Ψ : X → Vec3 → ℝ}
    {g₀ : Vec3 → ℝ} {g₁ : Vec3 → Vec3}
    {g₂ : Vec3 → Fin 3 → Fin 3 → ℝ} {D : Set X}
    (_ : D.Countable) (hD : Dense D)
    (hcont : Continuous (parametricPairing Ψ g₀ g₁ g₂))
    (hzero : ∀ x ∈ D, parametricPairing Ψ g₀ g₁ g₂ x = 0) :
    ∀ x, parametricPairing Ψ g₀ g₁ g₂ x = 0 := by
  exact parametricPairing_eq_zero_of_dense hD hcont hzero

end CKN
