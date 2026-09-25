/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Slice Selected Gradient Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-! The pressure-gradient section of the paper controls `∇p` through the weak pairing
against a compactly supported test function, as in display (3.5).  The Newtonian
derivative potential of a source field is the kernel representation of that weak
gradient.  This file records the integrability input that display (3.5) assumes, the
local integrability of a finite sum of such potentials, and the passage from a
per-coordinate Calderón–Zygmund bound to the corresponding bound for the potential of
a vector-valued source. -/

/-- A function in `L^{6/5}` with compact support is integrable.  This is the
integrability input that display (3.5) of the pressure-gradient section takes for
granted: the source of the Newtonian derivative potential is supported on a compact
set of finite measure, so membership in `L^{6/5}` may be lowered to membership in
`L^1`. -/
theorem memLp_six_fifths_integrable_of_hasCompactSupport {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume) (hGc : HasCompactSupport G) :
    Integrable G volume := by
  rw [← memLp_one_iff_integrable]
  refine hG.mono_exponent_of_measure_support_ne_top (s := tsupport G) ?_ ?_ ?_
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  · exact hGc.isCompact.measure_lt_top.ne
  · exact ENNReal.one_le_ofReal.2 (by norm_num)

/-- The sum over coordinates of the Newtonian derivative potentials of the components
of a compactly supported vector field in `L^{6/5}` is locally integrable.  This is the
weak gradient field appearing on the left-hand side of display (3.5) of the
pressure-gradient section, assembled coordinate by coordinate from its per-coordinate
kernel representation. -/
theorem newtonianDerivativeSum_locallyIntegrable {V : Vec3 → Vec3}
    (hV : ∀ i : Fin 3, MemLp (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i)) :
    LocallyIntegrable
      (fun x => ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) volume := by
  have hterm : ∀ i : Fin 3,
      LocallyIntegrable (fun x => pressureNewtonianDerivativePotential i (fun y => V y i) x)
        volume :=
    fun i => pressureNewtonianDerivativePotential_locallyIntegrable i
      (memLp_six_fifths_integrable_of_hasCompactSupport (hV i) (hVc i)) (hVc i)
  have hsum := locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
    (μ := volume)
    (f := fun i x => pressureNewtonianDerivativePotential i (fun y => V y i) x)
    (fun i _ => hterm i)
  simpa using hsum

/-- Display (3.5) of the pressure-gradient section for a vector-valued source: given a
per-coordinate Calderón–Zygmund selection producing, for each scalar source `G` in
`L^{6/5}` with compact support, a weak gradient `D` together with its pairing identity
and its `L^{6/5}` bound against `G`, the coordinate sum of the Newtonian derivative
potentials of the components of `V` has a weak gradient `D` satisfying the same
pairing identity against every smooth compactly supported test function, with the
`L^{6/5}` bound controlled by the sum of the component norms of `V`. -/
theorem newtonian_derivative_sum_weak_gradient_of_extension
    (C_CZ : ℝ)
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {V : Vec3 → Vec3}
    (hV : ∀ i : Fin 3, MemLp (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i)) :
    ∃ D : Vec3 → Vec3,
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x, (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) *
            spatialDeriv ψ j x) = -(∫ x, D x j * ψ x)) ∧
      eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ENNReal.ofReal C_CZ *
          ∑ i : Fin 3, eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ) := ENNReal.one_le_ofReal.2 (by norm_num)
  choose D hDmem hDrest using fun i => hP1 i (fun y => V y i) (hV i) (hVc i)
  have hDpair : ∀ (i : Fin 3) (j : Fin 3) (ψ : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i (fun y => V y i) x * spatialDeriv ψ j x) =
        -(∫ x, D i x j * ψ x) := fun i => (hDrest i).1
  have hDbound : ∀ i : Fin 3,
      eLpNorm (D i) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ENNReal.ofReal C_CZ * eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    fun i => (hDrest i).2
  let Dsum : Vec3 → Vec3 := fun x j => ∑ i : Fin 3, D i x j
  have hDsum_def : Dsum = (fun x j => ∑ i : Fin 3, D i x j) := rfl
  have hDsum_mem : MemLp Dsum (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    have h := memLp_finsetSum (Finset.univ : Finset (Fin 3)) (μ := volume)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (f := D) (fun i _ => hDmem i)
    have heq : (fun a => ∑ i ∈ (Finset.univ : Finset (Fin 3)), D i a) = Dsum := by
      rw [hDsum_def]
      funext x j
      simp only [Finset.sum_apply]
    rwa [heq] at h
  have hfin : (∑ i : Fin 3, D i) = Dsum := by
    rw [hDsum_def]
    funext x j
    simp only [Finset.sum_apply]
  have hpair : ∀ (j : Fin 3) (ψ : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) *
          spatialDeriv ψ j x) = -(∫ x, Dsum x j * ψ x) := by
    intro j ψ hψ hψc
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ j) := contDiff_spatialDeriv_smooth hψ j
    have hpdc : HasCompactSupport (spatialDeriv ψ j) := by
      change HasCompactSupport (fun x : Vec3 => (fderiv ℝ ψ x) (basisVec j))
      exact hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)
    have hintN : ∀ i : Fin 3, Integrable (fun x =>
        pressureNewtonianDerivativePotential i (fun y => V y i) x * spatialDeriv ψ j x)
        volume :=
      fun i => pressureNewtonianDerivativePotential_mul_smooth_integrable
        (i := i) (g := fun y => V y i) (φ := spatialDeriv ψ j)
        (memLp_six_fifths_integrable_of_hasCompactSupport (hV i) (hVc i)) (hVc i) hcont hpdc
    have hintD : ∀ i : Fin 3, Integrable (fun x => D i x j * ψ x) volume := fun i => by
      have hcomp : MemLp (fun x => D i x j) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        (hDmem i).continuousLinearMap_comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)
      have hli : LocallyIntegrable (fun x => D i x j) volume := hcomp.locallyIntegrable hp1
      simpa only [smul_eq_mul] using
        hli.integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
    calc
      (∫ x, (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) *
            spatialDeriv ψ j x)
          = ∫ x, ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x *
              spatialDeriv ψ j x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Finset.sum_mul]
      _ = ∑ i, ∫ x, pressureNewtonianDerivativePotential i (fun y => V y i) x *
              spatialDeriv ψ j x :=
            integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hintN i)
      _ = ∑ i, -(∫ x, D i x j * ψ x) :=
            Finset.sum_congr rfl (fun i _ => hDpair i j ψ hψ hψc)
      _ = -(∑ i, ∫ x, D i x j * ψ x) := by
            rw [Finset.sum_neg_distrib]
      _ = -(∫ x, ∑ i, D i x j * ψ x) := by
            rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hintD i)]
      _ = -(∫ x, (∑ i, D i x j) * ψ x) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with x
            rw [Finset.sum_mul]
      _ = -(∫ x, Dsum x j * ψ x) := by
            simp only [hDsum_def]
  have hDsum_bound : eLpNorm Dsum (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      ENNReal.ofReal C_CZ *
        ∑ i : Fin 3, eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    have h1 : eLpNorm Dsum (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ∑ i ∈ (Finset.univ : Finset (Fin 3)),
          eLpNorm (D i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      have h := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal (6 / 5 : ℝ))
        (f := D) (s := Finset.univ) hp1
      rwa [hfin] at h
    calc
      eLpNorm Dsum (ENNReal.ofReal (6 / 5 : ℝ)) volume
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)),
              eLpNorm (D i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := h1
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)),
              ENNReal.ofReal C_CZ *
                eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
            Finset.sum_le_sum (fun i _ => hDbound i)
      _ = ENNReal.ofReal C_CZ *
              ∑ i ∈ (Finset.univ : Finset (Fin 3)),
                eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal C_CZ *
              ∑ i : Fin 3, eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
            rfl
  exact ⟨Dsum, hDsum_mem, hpair, hDsum_bound⟩

end CKN.Core.Step4
