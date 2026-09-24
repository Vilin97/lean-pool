/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWS

/-!
# Identification

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/- The tensor pairing is kept explicit so that the distributional pressure
   identity and the eventual singular-integral identity have the same target. -/
/-- Pairing of a tensor source with the Hessian of a scalar test function. -/
def pressureSecondPairing (G : Fin 3 → Fin 3 → Vec3 → ℝ)
    (ψ : Vec3 → ℝ) : ℝ :=
  ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x

private lemma pressureSecondPairing_sub_cancel
    {p₁ Tg : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hT : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume →
      ∫ x, Tg x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ (Set.univ : Set Vec3))
    (hP1Int : Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hTInt : Integrable (fun x => Tg x * spatialLaplacian ψ x) volume) :
    ∫ x, (p₁ x - Tg x) * spatialLaplacian ψ x = 0 := by
  rw [show (fun x => (p₁ x - Tg x) * spatialLaplacian ψ x) =
      (fun x => p₁ x * spatialLaplacian ψ x -
        Tg x * spatialLaplacian ψ x) by funext x; ring]
  rw [integral_sub hP1Int hTInt]
  rw [hP1 ψ hψ hψc hψU hP1Int, hT ψ hψ hψc hψU hTInt]
  ring

/-- The difference between a pressure term and a candidate second-order
    Newtonian operator is weakly harmonic when the two distributional
    identities have the same tensor source. -/
theorem pressureP1_residual_weaklyHarmonic
    {p₁ Tg : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hT : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume →
      ∫ x, Tg x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hTInt : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume) :
    WeaklyHarmonicOn (Set.univ : Set Vec3) (p₁ - Tg) := by
  intro ψ hψ hψc hψU
  rw [Measure.restrict_univ]
  exact pressureSecondPairing_sub_cancel hP1 hT hψ hψc hψU
    (hP1Int ψ hψ hψc hψU) (hTInt ψ hψ hψc hψU)

/-- Identification of the leading pressure term from the residual growth and
    the distributional identities. The residual hypotheses are the analytic
    decay-at-infinity input for the compactly supported pressure data. -/
theorem pressureP1_eq_of_distributional_identity_and_linear_growth
    {p₁ Tg : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hT : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume →
      ∫ x, Tg x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hTInt : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ (Set.univ : Set Vec3) →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (p₁ - Tg) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (p₁ - Tg) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    p₁ =ᵐ[volume] Tg := by
  have hzero := weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth hC hmem
    (pressureP1_residual_weaklyHarmonic hP1 hT hP1Int hTInt) hgrowth
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/-- The operator-bound part of the pressure identification, isolated from the
    distributional argument so the eventual singular-integral theorem can be
    substituted without changing downstream consumers. -/
theorem pressure_lpNorm_le_of_operator_bound
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {p₁ g : Vec3 → ℝ} {C_CZ : ℝ}
    (hT : ∀ f, MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) volume →
      HasCompactSupport f →
      lpNorm (T f) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        C_CZ *
          lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hgc : HasCompactSupport g) (hident : p₁ =ᵐ[volume] T g) :
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      C_CZ *
        lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  calc
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume =
        lpNorm (T g) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hident)
    _ ≤ C_CZ * lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume := hT g hg hgc

/-- Discharge the exact global `hCZ_p1` shape used by the `lpNorm` pressure
    consumers from the singular-integral estimate and a source norm bound. -/
theorem hCZ_p1_of_operator_bound
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {p₁ g : Vec3 → ℝ}
    {C_CZ C₁₁ E : ℝ}
    (hT : ∀ f, MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) volume →
      HasCompactSupport f →
      lpNorm (T f) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        C_CZ *
          lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hgc : HasCompactSupport g) (hident : p₁ =ᵐ[volume] T g)
    (hsource : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      E ^ (2 / 3 : ℝ))
    (hC_CZ : 0 ≤ C_CZ) (hconst : C_CZ ≤ C₁₁)
    (hE : 0 ≤ E) :
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hpow : 0 ≤ E ^ (2 / 3 : ℝ) := Real.rpow_nonneg hE _
  have hoperator := pressure_lpNorm_le_of_operator_bound hT hg hgc hident
  have hmul : C_CZ *
      lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      C_CZ * E ^ (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_left hsource hC_CZ
  have hconstant : C_CZ * E ^ (2 / 3 : ℝ) ≤
      C₁₁ * E ^ (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hconst hpow
  calc
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        C_CZ *
          lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume := hoperator
    _ ≤ C_CZ * E ^ (2 / 3 : ℝ) := hmul
    _ ≤ C₁₁ * E ^ (2 / 3 : ℝ) := hconstant

end CKN
