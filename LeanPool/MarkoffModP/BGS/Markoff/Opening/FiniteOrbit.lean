/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Dynamics.FiniteForwardOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Core.NormalizedOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Opening.ParabolicPeriodicity
import LeanPool.MarkoffModP.BGS.Markoff.Opening.PeriodicSemisimple
import LeanPool.MarkoffModP.BGS.Markoff.Opening.TorsionTraces

namespace BGS.Markoff

universe u

theorem normalizedRotate1Surface_injective
    {R : Type u} [CommRing R] [Invertible (3 : R)] :
    Function.Injective (normalizedRotate1Surface (R := R)) := by
  intro x y hxy
  have hx : normalizedGammaPerm R (gammaRotate1 R) x = normalizedRotate1Surface x := by
    change gammaRotate1 R • x = normalizedRotate1Surface x
    exact gammaRotate1_smul_normalizedSurface x
  have hy : normalizedGammaPerm R (gammaRotate1 R) y = normalizedRotate1Surface y := by
    change gammaRotate1 R • y = normalizedRotate1Surface y
    exact gammaRotate1_smul_normalizedSurface y
  apply (normalizedGammaPerm R (gammaRotate1 R)).injective
  exact hx.trans (hxy.trans hy.symm)

theorem coe_iterate_normalizedRotate1Surface
    {R : Type u} [CommRing R] (x : NormalizedMarkoffSurface R) (n : ℕ) :
    ((normalizedRotate1Surface^[n]) x).1 = (normalizedRotate1^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change normalizedRotate1 ((normalizedRotate1Surface^[n]) x).1 =
        normalizedRotate1 ((normalizedRotate1^[n]) x.1)
      rw [ih]

theorem exists_positive_normalizedRotate1Surface_return_of_finite_component
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    {x y : NormalizedMarkoffSurface R}
    (hfinite : (normalizedGammaOrbit x).Finite)
    (hxy : SameNormalizedComponent x y) :
    ∃ n : ℕ, 0 < n ∧ (normalizedRotate1Surface^[n]) y = y := by
  apply BGS.exists_positive_iterate_eq_self_of_forwardOrbit_subset
    normalizedRotate1Surface_injective hfinite
  rintro _ ⟨n, rfl⟩
  apply (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
  exact sameNormalizedComponent_trans hxy
    (sameNormalizedComponent_iterate_normalizedRotate1Surface y n)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Invertible (3 : K)]

omit [CharZero K] [Invertible (3 : K)] in
private theorem exists_root_neg_one : ∃ i : K, i ^ 2 = -1 := by
  exact IsAlgClosed.exists_pow_nat_eq (-1 : K) (by norm_num)

theorem finite_component_coordinate1_has_torsion_trace
    {x y : NormalizedMarkoffSurface K}
    (hfinite : (normalizedGammaOrbit x).Finite)
    (hxy : SameNormalizedComponent x y) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ y.1.u1 = splitTorusTrace w := by
  obtain ⟨n, hn, hreturn⟩ :=
    exists_positive_normalizedRotate1Surface_return_of_finite_component hfinite hxy
  have hpointReturn : (normalizedRotate1^[n]) y.1 = y.1 := by
    rw [← coe_iterate_normalizedRotate1Surface]
    exact congrArg Subtype.val hreturn
  have hyFiber : y.1 ∈ normalizedFiber1 y.1.u1 := ⟨y.property, rfl⟩
  by_cases hsemisimple : y.1.u1 ^ 2 ≠ 4
  · exact periodic_nonparabolic_fiber_has_torsion_eigenvalue
      hsemisimple hyFiber hn hpointReturn
  · exfalso
    obtain ⟨i, hi⟩ := exists_root_neg_one (K := K)
    have hsq : y.1.u1 ^ 2 = 4 := not_ne_iff.mp hsemisimple
    have hfactor : (y.1.u1 - 2) * (y.1.u1 + 2) = 0 := by
      calc
        (y.1.u1 - 2) * (y.1.u1 + 2) = y.1.u1 ^ 2 - 4 := by ring
        _ = 0 := sub_eq_zero.mpr hsq
    rcases mul_eq_zero.mp hfactor with htwo | hnegTwo
    · have ht : y.1.u1 = 2 := sub_eq_zero.mp htwo
      exact (iterate_normalizedRotate1_ne_self_of_mem_fiber1_two i hi
        (by simpa [ht] using hyFiber) n hn) hpointReturn
    · have ht : y.1.u1 = -2 := by linear_combination hnegTwo
      exact (iterate_normalizedRotate1_ne_self_of_mem_fiber1_neg_two i hi
        (by simpa [ht] using hyFiber) n hn) hpointReturn

theorem finite_normalizedGammaOrbit_has_torsion_traces
    (x : NormalizedMarkoffSurface K)
    (hfinite : (normalizedGammaOrbit x).Finite) :
    ∃ w₁ w₂ w₃ : Kˣ,
      IsOfFinOrder w₁ ∧ IsOfFinOrder w₂ ∧ IsOfFinOrder w₃ ∧
      x.1.u1 = splitTorusTrace w₁ ∧ x.1.u2 = splitTorusTrace w₂ ∧
      x.1.u3 = splitTorusTrace w₃ := by
  obtain ⟨w₁, hw₁, htrace₁⟩ := finite_component_coordinate1_has_torsion_trace
    hfinite (sameNormalizedComponent_refl x)
  obtain ⟨w₂, hw₂, htrace₂⟩ := finite_component_coordinate1_has_torsion_trace
    hfinite (sameNormalizedComponent_swap12Surface x)
  let x₃ := normalizedSwap12Surface (normalizedSwap23Surface x)
  have hx₃ : SameNormalizedComponent x x₃ :=
    sameNormalizedComponent_trans (sameNormalizedComponent_swap23Surface x)
      (sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x))
  obtain ⟨w₃, hw₃, htrace₃⟩ := finite_component_coordinate1_has_torsion_trace
    hfinite hx₃
  refine ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, htrace₁, ?_, ?_⟩
  · simpa [normalizedSwap12Surface, normalizedSwap12] using htrace₂
  · simpa [x₃, normalizedSwap12Surface, normalizedSwap23Surface,
      normalizedSwap12, normalizedSwap23] using htrace₃

theorem complex_normalizedPoint_eq_origin_of_finite_normalizedGammaOrbit
    (x : NormalizedMarkoffSurface ℂ)
    (hfinite : (normalizedGammaOrbit x).Finite) :
    x.1 = normalizedOrigin := by
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, h₁, h₂, h₃⟩ :=
    finite_normalizedGammaOrbit_has_torsion_traces x hfinite
  exact complex_normalizedMarkoff_eq_origin_of_torsion_traces x.1 x.property
    ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩ ⟨w₃, hw₃, h₃⟩

theorem complex_normalizedGammaOrbit_infinite_of_ne_origin
    (x : NormalizedMarkoffSurface ℂ) (hx : x.1 ≠ normalizedOrigin) :
    (normalizedGammaOrbit x).Infinite := by
  intro hfinite
  exact hx (complex_normalizedPoint_eq_origin_of_finite_normalizedGammaOrbit x hfinite)

end BGS.Markoff
