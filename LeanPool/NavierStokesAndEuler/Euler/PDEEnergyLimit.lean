/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WeightedSobolevEnergy
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpPairing
public import LeanPool.NavierStokesAndEuler.Euler.SobolevEnergyPaths

@[expose] public section

/-! The actual finite-Sobolev viscous PDE energy estimate passes to strong limits without a time
  derivative of a zero norm. -/

noncomputable section

namespace EulerPDEEnergyLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp EulerTimeLpPairing EulerPacketWeights
open scoped Topology

/-- Equality of an actual scalar integrand with three continuous weighted paths identifies its interval integral. -/
theorem integral_eq_three_paths (T : ℝ) (hT : 0 ≤ T)
    (a b c X Y Z : C(Icc (0 : ℝ) T, ℝ)) (f : ℝ → ℝ)
    (hf : ∀ r ∈ Icc 0 T, f r = extendPath T hT a r * extendPath T hT X r +
      extendPath T hT b r * extendPath T hT Y r + extendPath T hT c r * extendPath T hT Z r) :
    (∫ r in (0 : ℝ)..T, f r) =
      (∫ r in (0 : ℝ)..T, extendPath T hT a r * extendPath T hT X r) +
      (∫ r in (0 : ℝ)..T, extendPath T hT b r * extendPath T hT Y r) +
      ∫ r in (0 : ℝ)..T, extendPath T hT c r * extendPath T hT Z r := by
  rw [← integral_three_paths T hT a b c X Y Z]
  apply intervalIntegral.integral_congr
  intro r hr
  exact hf r (by simpa only [uIcc_of_le hT] using hr)

variable (period : ℝ) [Fact (0 < period)]

/-- Actual smooth-in-time finite-Sobolev PDE approximations imply the limiting signed integral energy bound.
The premises include their literal PDEs and strong convergence, never an assumed energy inequality.
  -/
theorem weighted_pde_energy_limit {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq : 3 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (order : α → ℕ) (ρ ρ' : ℝ → ℝ)
    (κ : ℝ) (m : Vector3) (K G : ℝ → SmoothCoefficient period)
    (e : ℕ → α → β → ℝ → SobolevSpace period 2)
    (e' p forcing : ℕ → α → β → ℝ → LiftL2 period) (z : ℝ → SobolevSpace period q)
    (c ν : ℝ) (K' : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (B : ℝ → NNReal)
    (hc : 0 < c) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Icc 0 T)) (hρpos : ∀ r ∈ Icc 0 T, 0 < ρ r)
    (hρd : ∀ r ∈ Ioo 0 T, HasDerivAt ρ (ρ' r) r)
    (hKc : ContinuousOn (fun r => (K r).operator) (Icc 0 T))
    (hec : ∀ n i j, ContinuousOn (fun r => value period (e n i j r)) (Icc 0 T))
    (hKt : ∀ r ∈ Ioo 0 T, HasDerivAt (fun v => (K v).operator) (K' r) r)
    (het : ∀ n i j r, r ∈ Ioo 0 T → HasDerivAt (fun v => value period (e n i j v)) (e' n i j r) r)
    (hsym : ∀ r ∈ Ioo 0 T, ∀ x v w, ⟪(K r).coefficient x v, w⟫_ℝ = ⟪v, (K r).coefficient x w⟫_ℝ)
    (hpos : ∀ r ∈ Icc 0 T, ∀ x v, c^2*‖v‖^2 ≤ ⟪(K r).coefficient x v, v⟫_ℝ)
    (hKG : ∀ r ∈ Ioo 0 T, ∀ x v, (K r).coefficient x ((G r).coefficient x v) = v)
    (hediv : ∀ n i j r, r ∈ Ioo 0 T → value period (e n i j r) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ n i j r, r ∈ Ioo 0 T → p n i j r ∈ gradientSpace period κ m)
    (hz : ∀ r ∈ Ioo 0 T, value period (z r) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ r ∈ Ioo 0 T, ∀ᵐ x ∂liftMeasure period, ‖value period (z r) x‖ ≤ B r)
    (heq : ∀ n i j r, r ∈ Ioo 0 T → e' n i j r +
      transportOperator period hq κ m (z r) (restrictOperator period (by norm_num : 1 ≤ 2) (e n i j
        r)) +
        (G r).operator (p n i j r) = forcing n i j r + ν • jetLaplacian period (toJet period (e n i
          j r)))
    (hAint : ∀ i, IntegrableOn (fun r => weight (ρ r) (order i) *
      viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) +
      (ρ' r / ρ r) * (order i : ℝ) * weight (ρ r) (order i)) (Icc 0 T))
    (hFint : ∀ n i, IntegrableOn (fun r => weight (ρ r) (order i) *
      ((((K r).bound : ℝ) / c) * familyNorm (fun j => forcing n i j r))) (Icc 0 T))
    (a b d : C(Icc (0 : ℝ) T, ℝ))
    (ha : ∀ r ∈ Icc 0 T, viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) = extendPath T
      hT a r)
    (hb : ∀ r ∈ Icc 0 T, ρ' r / ρ r = extendPath T hT b r)
    (hd : ∀ r ∈ Icc 0 T, ((K r).bound : ℝ) / c = extendPath T hT d r)
    (X Y Z : ℕ → C(Icc (0 : ℝ) T, ℝ))
    (hXdef : ∀ n r, r ∈ Icc 0 T → weightedMetricSum (ρ r) order (K r).operator
      (fun i j => value period (e n i j r)) = extendPath T hT (X n) r)
    (hYdef : ∀ n r, r ∈ Icc 0 T → weightedMetricLoss (ρ r) order (K r).operator
      (fun i j => value period (e n i j r)) = extendPath T hT (Y n) r)
    (hZdef : ∀ n r, r ∈ Icc 0 T → weightedForcingSum (ρ r) order
      (fun i j => forcing n i j r) = extendPath T hT (Z n) r)
    (x y : C(Icc (0 : ℝ) T, ℝ)) (f : TimeLp T ℝ)
    (hX : Filter.Tendsto X Filter.atTop (𝓝 x)) (hY : Filter.Tendsto Y Filter.atTop (𝓝 y))
    (hZ : Filter.Tendsto (fun n => pathLp T hT (Z n)) Filter.atTop (𝓝 f)) :
    x ⟨T, hT, le_rfl⟩ - x ⟨0, le_rfl, hT⟩ ≤
      (∫ r in (0 : ℝ)..T, extendPath T hT a r * extendPath T hT x r) +
      (∫ r in (0 : ℝ)..T, extendPath T hT b r * extendPath T hT y r) +
      ∫ r, pathLp T hT d r * f r ∂timeMeasure T := by
  apply integral_energy_limit T hT a b (pathLp T hT d) X Y (fun n => pathLp T hT (Z n)) x y f hX hY
    hZ
  intro n
  have h := weighted_sobolev_energy_integral period hq order ρ ρ' κ m K G
    (e n) (e' n) (p n) (forcing n) z 0 T c ν K' B hT hc hν hρc hρpos hρd hKc (hec n) hKt (het n)
    hsym hpos hKG (hediv n) (hp n) hz hzB (heq n) hAint (hFint n)
  rw [hXdef n T ⟨hT, le_rfl⟩, hXdef n 0 ⟨le_rfl, hT⟩] at h
  have hevalT : extendPath T hT (X n) T = X n ⟨T, hT, le_rfl⟩ := congrArg (X n) (projIcc_of_mem hT
    ⟨hT, le_rfl⟩)
  have heval0 : extendPath T hT (X n) 0 = X n ⟨0, le_rfl, hT⟩ := congrArg (X n) (projIcc_of_mem hT
    ⟨le_rfl, hT⟩)
  rw [hevalT, heval0] at h
  have hi := integral_eq_three_paths T hT a b d (X n) (Y n) (Z n)
    (fun r => viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) *
      weightedMetricSum (ρ r) order (K r).operator (fun i j => value period (e n i j r)) +
      (ρ' r / ρ r) * weightedMetricLoss (ρ r) order (K r).operator (fun i j => value period (e n i
        j r)) +
      (((K r).bound : ℝ) / c) * weightedForcingSum (ρ r) order (fun i j => forcing n i j r))
    (fun r hr => by rw [ha r hr, hb r hr, hd r hr, hXdef n r hr, hYdef n r hr, hZdef n r hr])
  rw [hi] at h
  rw [← inner_eq_integral, path_inner_eq_integral]
  exact h

end EulerPDEEnergyLimit
