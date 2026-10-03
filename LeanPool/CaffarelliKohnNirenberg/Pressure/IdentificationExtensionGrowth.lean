/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtension
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpP8

/-!
# Growth of the indexed pressure-extension residual

The global pressure operator used here is the indexed `L^(3/2)` extension.  The
ordinary kernel formula is not used.  The first theorem is the residual
bookkeeping in a form independent of the construction of the operator; the
second supplies its local hypotheses from the global `MemLp` statement of the
indexed extension.  The last two declarations expose the pressure-decomposition
shape consumed by the CZ identification argument.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

theorem pressure_residual_local_linear_growth_of_bounds
    {p₁ T : Vec3 → ℝ} {C₁ C₂ p : ℝ} (hp : 1 ≤ p)
    (hP1mem : ∀ ρ : ℝ, 0 < ρ →
      MemLp p₁ (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hTmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp T (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hP1bound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm p₁ (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C₁ * (1 + ρ))
    (hTbound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm T (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C₂ * (1 + ρ)) :
    ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - T x) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ∧
      lpNorm (fun x => p₁ x - T x) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (C₁ + C₂) * (1 + ρ) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  intro ρ hρ
  have hP := hP1mem ρ hρ
  have hT := hTmem ρ hρ
  refine ⟨hP.sub hT, ?_⟩
  calc
    lpNorm (fun x => p₁ x - T x) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        lpNorm p₁ (ENNReal.ofReal p)
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) +
        lpNorm T (ENNReal.ofReal p)
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
      lpNorm_sub_le hP hp'
    _ ≤ C₁ * (1 + ρ) + C₂ * (1 + ρ) :=
      add_le_add (hP1bound ρ hρ) (hTbound ρ hρ)
    _ = (C₁ + C₂) * (1 + ρ) := by ring

theorem pressureSecondExtension_residual_growth_of_decomposition
    {p₁ T P H J : Vec3 → ℝ} {C₀ C_H C_J C_T : ℝ}
    (hdecomp : p₁ = P - (H + J))
    (hPmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hPbound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm P (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C₀ * (1 + ρ))
    (hHmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hHbound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C_H * (1 + ρ))
    (hJmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp J (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hJbound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm J (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C_J * (1 + ρ))
    (hTmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp T (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hTbound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm T (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C_T * (1 + ρ)) :
    ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - T x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ∧
      lpNorm (fun x => p₁ x - T x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (C₀ + C_H + C_J + C_T) * (1 + ρ) := by
  have hP1mem : ∀ ρ : ℝ, 0 < ρ →
      MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    rw [hdecomp]
    exact (hPmem ρ hρ).sub ((hHmem ρ hρ).add (hJmem ρ hρ))
  have hP1bound : ∀ ρ : ℝ, 0 < ρ →
      lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (C₀ + C_H + C_J) * (1 + ρ) := by
    intro ρ hρ
    rw [hdecomp]
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) :=
      ENNReal.one_le_ofReal.2 (by norm_num)
    calc
      lpNorm (P - (H + J)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          lpNorm P (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) ρ)) +
          lpNorm (H + J) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
        lpNorm_sub_le (hPmem ρ hρ) hp1
      _ ≤ C₀ * (1 + ρ) + (C_H + C_J) * (1 + ρ) := by
        exact add_le_add (hPbound ρ hρ)
          (lpNorm_euclideanBall_growth_add hHmem hHbound hJbound hρ)
      _ = (C₀ + C_H + C_J) * (1 + ρ) := by ring
  exact pressure_residual_local_linear_growth_of_bounds (p := (3 / 2 : ℝ))
    (by norm_num) hP1mem hTmem hP1bound hTbound

end CKN
