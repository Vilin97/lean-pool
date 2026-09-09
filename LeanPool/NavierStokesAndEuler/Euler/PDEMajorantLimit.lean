/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PDESubintervalEnergyLimit
public import LeanPool.NavierStokesAndEuler.Euler.WeightedSobolevMajorant

@[expose] public section

/-! Actual PDE energy passage with continuous scalar majorants on every time subinterval. -/

noncomputable section

namespace EulerPDEMajorantLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevMajorant EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp EulerTimeLpPairing EulerPacketWeights EulerTimeLpSubinterval
  EulerPDESubintervalEnergyLimit
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual smooth-in-time finite-Sobolev PDE approximations imply the limiting signed integral energy bound.
The premises include their literal PDEs and strong convergence, never an assumed energy inequality.
  -/
theorem weighted_pde_majorized_subinterval_limit {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq
  : 3 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (order : α → ℕ) (a b d
      : C(Icc (0 : ℝ) T, ℝ)) (ρ ρ' : ℝ → ℝ)
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
    (hAint : ∀ i, IntegrableOn (fun r => weight (ρ r) (order i) * extendPath T hT a r +
      (ρ' r / ρ r) * (order i : ℝ) * weight (ρ r) (order i)) (Icc 0 T))
    (hFint : ∀ n i, IntegrableOn (fun r => weight (ρ r) (order i) *
      (extendPath T hT d r * familyNorm (fun j => forcing n i j r))) (Icc 0 T))
    (ha : ∀ r ∈ Icc 0 T, viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) ≤ extendPath T
      hT a r)
    (hb : ∀ r ∈ Icc 0 T, ρ' r / ρ r = extendPath T hT b r)
    (hd : ∀ r ∈ Icc 0 T, ((K r).bound : ℝ) / c ≤ extendPath T hT d r)
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
    x ⟨t, h0s.trans hst, htT⟩ - x ⟨s, h0s, hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT x r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT y r) +
      ∫ r in Icc s t, pathLp T hT d r * f r ∂timeMeasure T := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := fun _ hr => ⟨h0s.trans hr.1, hr.2.trans htT⟩
  have hsubo : Ioo s t ⊆ Ioo (0 : ℝ) T := fun _ hr => ⟨lt_of_le_of_lt h0s hr.1, lt_of_lt_of_le hr.2
    htT⟩
  apply integral_energy_subinterval_limit T hT s t h0s hst htT a b (pathLp T hT d)
    X Y (fun n => pathLp T hT (Z n)) x y f hX hY hZ
  intro n
  have h := weighted_sobolev_energy_majorized period hq order ρ ρ' κ m K G
    (e n) (e' n) (p n) (forcing n) z s t c ν K' B (extendPath T hT a) (extendPath T hT d) hst hc hν
    (fun r hr => ha r (hsub ⟨hr.1.le,hr.2.le⟩)) (fun r hr => hd r (hsub ⟨hr.1.le,hr.2.le⟩))
    (hρc.mono hsub) (fun r hr => hρpos r (hsub hr)) (fun r hr => hρd r (hsubo hr))
    (hKc.mono hsub) (fun i j => (hec n i j).mono hsub) (fun r hr => hKt r (hsubo hr))
    (fun i j r hr => het n i j r (hsubo hr)) (fun r hr => hsym r (hsubo hr))
    (fun r hr => hpos r (hsub hr)) (fun r hr => hKG r (hsubo hr))
    (fun i j r hr => hediv n i j r (hsubo hr)) (fun i j r hr => hp n i j r (hsubo hr))
    (fun r hr => hz r (hsubo hr)) (fun r hr => hzB r (hsubo hr))
    (fun i j r hr => heq n i j r (hsubo hr))
    (fun i => (hAint i).mono_set hsub) (fun i => (hFint n i).mono_set hsub)
  rw [hXdef n t ⟨h0s.trans hst, htT⟩, hXdef n s ⟨h0s, hst.trans htT⟩] at h
  have hevalt : extendPath T hT (X n) t = X n ⟨t, h0s.trans hst, htT⟩ :=
    congrArg (X n) (projIcc_of_mem hT ⟨h0s.trans hst, htT⟩)
  have hevals : extendPath T hT (X n) s = X n ⟨s, h0s, hst.trans htT⟩ :=
    congrArg (X n) (projIcc_of_mem hT ⟨h0s, hst.trans htT⟩)
  rw [hevalt, hevals] at h
  have hi := integral_eq_three_subinterval_paths T hT s t hst a b d (X n) (Y n) (Z n)
    (fun r => extendPath T hT a r *
      weightedMetricSum (ρ r) order (K r).operator (fun i j => value period (e n i j r)) +
      (ρ' r / ρ r) * weightedMetricLoss (ρ r) order (K r).operator (fun i j => value period (e n i
        j r)) +
      extendPath T hT d r * weightedForcingSum (ρ r) order (fun i j => forcing n i j r))
    (fun r hr => by rw [hb r (hsub hr), hXdef n r (hsub hr), hYdef n r (hsub hr), hZdef n r (hsub
      hr)])
  rw [hi] at h
  rw [← subinterval_inner_eq, subinterval_path_inner T hT s t h0s hst htT]
  exact h

end EulerPDEMajorantLimit
