/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy
import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubinterval
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedEnergy
import LeanPool.NavierStokesAndEuler.Euler.SobolevViscousEnergy
import LeanPool.NavierStokesAndEuler.Euler.WeightedRootLimit
import Mathlib.Algebra.Order.Star.Real

/-! Genuine finite-Sobolev PDE energy passage on every time subinterval. -/

section

/-! Exact signed Gevrey integral energy for actual finite-Sobolev viscous solutions. -/

@[expose] public section

noncomputable section

namespace EulerWeightedSobolevEnergy

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
      EulerMetricEnergyEvolution
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerWeightedRootLimit
  EulerPacketWeights EulerWeightedEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerSobolevViscousEnergy
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The finite Gevrey-weighted integral energy inequality derived from the actual viscous PDE.
The signed radius term is retained exactly, and no differentiability of the unregularized norm is
assumed. -/
theorem weighted_sobolev_energy_integral {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq : 3 ≤ q)
    (order : α → ℕ) (ρ ρ' : ℝ → ℝ)
    (κ : ℝ) (m : Vector3) (K G : ℝ → SmoothCoefficient period)
    (e : α → β → ℝ → SobolevSpace period 2) (e' p forcing : α → β → ℝ → LiftL2 period)
    (z : ℝ → SobolevSpace period q)
    (s t c ν : ℝ) (K' : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (B : ℝ → ℝ≥0)
    (hst : s ≤ t) (hc : 0 < c) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Icc s t)) (hρpos : ∀ u ∈ Icc s t, 0 < ρ u)
    (hρd : ∀ u ∈ Ioo s t, HasDerivAt ρ (ρ' u) u)
    (hKc : ContinuousOn (fun u => (K u).operator) (Icc s t))
    (hec : ∀ i j, ContinuousOn (fun u => value period (e i j u)) (Icc s t))
    (hKt : ∀ u ∈ Ioo s t, HasDerivAt (fun v => (K v).operator) (K' u) u)
    (het : ∀ i j u, u ∈ Ioo s t → HasDerivAt (fun v => value period (e i j v)) (e' i j u) u)
    (hsym : ∀ u ∈ Ioo s t, ∀ x v w,
      ⟪(K u).coefficient x v, w⟫_ℝ = ⟪v, (K u).coefficient x w⟫_ℝ)
    (hpos : ∀ u ∈ Icc s t, ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K u).coefficient x v, v⟫_ℝ)
    (hKG : ∀ u ∈ Ioo s t, ∀ x v, (K u).coefficient x ((G u).coefficient x v) = v)
    (hediv : ∀ i j u, u ∈ Ioo s t → value period (e i j u) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ i j u, u ∈ Ioo s t → p i j u ∈ gradientSpace period κ m)
    (hz : ∀ u ∈ Ioo s t, value period (z u) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ u ∈ Ioo s t, ∀ᵐ x ∂liftMeasure period, ‖value period (z u) x‖ ≤ B u)
    (heq : ∀ i j u, u ∈ Ioo s t → e' i j u +
      transportOperator period hq κ m (z u) (restrictOperator period (by
          norm_num : 1 ≤ 2) (e i j u)) +
        (G u).operator (p i j u) = forcing i j u + ν • jetLaplacian period (toJet period (e i j u)))
    (hAint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
        viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u) +
      (ρ' u / ρ u) * (order i : ℝ) * weight (ρ u) (order i)) (Icc s t))
    (hFint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
      ((((K u).bound : ℝ) / c) * familyNorm (fun j => forcing i j u))) (Icc s t)) :
    weightedMetricSum (ρ t) order (K t).operator (fun i j => value period (e i j t)) -
      weightedMetricSum (ρ s) order (K s).operator (fun i j => value period (e i j s)) ≤
      ∫ u in s..t,
        viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u) *
          weightedMetricSum (ρ u) order (K u).operator (fun i j => value period (e i j u)) +
        (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => value period (e i
            j u)) +
        (((K u).bound : ℝ) / c) * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
  let Q := fun i u => familyEnergy (K u).operator (fun j => value period (e i j u))
  let a := fun u => viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u)
  let F := fun i u => (((K u).bound : ℝ) / c) * familyNorm (fun j => forcing i j u)
  let w := fun i u => weight (ρ u) (order i)
  let w' := fun i u => (ρ' u / ρ u) * (order i : ℝ) * weight (ρ u) (order i)
  let A := fun i u => w i u * a u + w' i u
  let Ψ := fun i u => A i u * √(Q i u) + w i u * F i u
  have hQ (i : α) : ContinuousOn (Q i) (Icc s t) :=
    continuousOn_finsetSum Finset.univ (fun j _ => (hKc.clm_apply (hec i j)).inner (hec i j))
  have hQ0 (i : α) (u : ℝ) (hu : u ∈ Icc s t) : 0 ≤ Q i u := by
    have hcoer : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K u).operator v, v⟫_ℝ :=
      coefficientOperator_coercive (K u).coefficient (K u).measurable (K u).bound
        (K u).norm_bound (c ^ 2) (hpos u hu)
    exact (mul_nonneg (sq_nonneg c) (familySquaredNorm_nonneg _)).trans
      (familyEnergy_coercive (K u).operator (fun j => value period (e i j u)) c hcoer)
  have hregd (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      DifferentiableAt ℝ (fun v => √(Q i v + δ ^ 2)) u := by
    have hsymL : ∀ v w, ⟪(K u).operator v, w⟫_ℝ = ⟪v, (K u).operator w⟫_ℝ :=
      coefficientOperator_inner_swap (K u).coefficient (K u).measurable
        (K u).bound (K u).norm_bound (hsym u hu)
    have hd : HasDerivAt (Q i) (∑ j, (⟪K' u (value period (e i j u)), value period (e i j u)⟫_ℝ +
        2 * ⟪(K u).operator (value period (e i j u)), e' i j u⟫_ℝ)) u :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        metric_energy_hasDerivAt (fun v => (K v).operator) (fun v => value period (e i j v)) u (K'
            u) (e' i j u)
          (hKt u hu) (het i j u hu) hsymL)
    have hq := hQ0 i u ⟨hu.1.le, hu.2.le⟩
    exact (HasDerivAt.sqrt (hd.add_const (δ ^ 2)) (by
        nlinarith : Q i u + δ ^ 2 ≠ 0)).differentiableAt
  have hreg (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      deriv (fun v => √(Q i v + δ ^ 2)) u ≤ a u * √(Q i u + δ ^ 2) + F i u := by
    exact finite_sobolev_viscous_energy period hq κ m K (G u) (e i) u δ c ν (K' u)
      (fun j => e' i j u) (fun j => p i j u) (fun j => forcing i j u) (z u)
      hδ hc hν (hKt u hu) (fun j => het i j u hu)
      (hsym u hu) (hpos u ⟨hu.1.le, hu.2.le⟩) (hKG u hu) (fun j => hediv i j u hu)
      (fun j => hp i j u hu) (hz u hu) (B u) (hzB u hu) (fun j => heq i j u hu)
  have hi (i : α) : w i t * √(Q i t) - w i s * √(Q i s) ≤ ∫ u in s..t, Ψ i u := by
    apply weighted_root_integral_of_deriv_bound (Q i) a (F i) (w i) (w' i) s t
      hst (hQ i) (hQ0 i) ?_ ?_ ?_ (hregd i) (hreg i) (hAint i) (hFint i)
    · exact (hρc.pow (order i)).div_const (((order i).factorial : ℝ) ^ 2)
    · intro u hu
      exact (weight_pos (hρpos u ⟨hu.1.le, hu.2.le⟩) (order i)).le
    · intro u hu
      exact weight_hasDerivAt ρ (ρ' u) u (hρd u hu) (hρpos u ⟨hu.1.le, hu.2.le⟩) (order i)
  have hΨ (i : α) : IntervalIntegrable (Ψ i) volume s t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
    exact ((hAint i).mul_continuousOn (hQ i).sqrt isCompact_Icc).add (hFint i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset α)) => hi i)
  rw [Finset.sum_sub_distrib] at hsum
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hΨ i)] at hsum
  have halg (u : ℝ) : (∑ i, Ψ i u) =
      a u * weightedMetricSum (ρ u) order (K u).operator (fun i j => value period (e i j u)) +
      (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => value period (e i j
          u)) +
      (((K u).bound : ℝ) / c) * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
    simp only [Ψ, A, w, w', F, Q, weightedMetricSum, weightedMetricLoss, weightedForcingSum,
      familyMetricNorm, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  simpa only [halg, w, Q, a, weightedMetricSum, familyMetricNorm] using hsum

end EulerWeightedSobolevEnergy

end
end

end

@[expose] public section

noncomputable section

namespace EulerPDESubintervalEnergyLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp  EulerPacketWeights EulerTimeLpSubinterval
open scoped Topology

/-- Three continuous weighted paths identify the actual scalar integral on an arbitrary time
subinterval. -/
theorem integral_eq_three_subinterval_paths (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (hst : s ≤ t)
    (a b c X Y Z : C(Icc (0 : ℝ) T, ℝ)) (f : ℝ → ℝ)
    (hf : ∀ r ∈ Icc s t, f r = extendPath T hT a r * extendPath T hT X r +
      extendPath T hT b r * extendPath T hT Y r + extendPath T hT c r * extendPath T hT Z r) :
    (∫ r in s..t, f r) =
      (∫ r in s..t, extendPath T hT a r * extendPath T hT X r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT Y r) +
      ∫ r in s..t, extendPath T hT c r * extendPath T hT Z r := by
  have ha := ((extendPath_continuous T hT a).mul (extendPath_continuous T hT X)).intervalIntegrable
      (μ := volume) s t
  have hb := ((extendPath_continuous T hT b).mul (extendPath_continuous T hT Y)).intervalIntegrable
      (μ := volume) s t
  have hc := ((extendPath_continuous T hT c).mul (extendPath_continuous T hT Z)).intervalIntegrable
      (μ := volume) s t
  change IntervalIntegrable (fun r => extendPath T hT a r * extendPath T hT X r) volume s t at ha
  change IntervalIntegrable (fun r => extendPath T hT b r * extendPath T hT Y r) volume s t at hb
  change IntervalIntegrable (fun r => extendPath T hT c r * extendPath T hT Z r) volume s t at hc
  rw [← intervalIntegral.integral_add ha hb, ← intervalIntegral.integral_add (ha.add hb) hc]
  apply intervalIntegral.integral_congr
  intro r hr
  exact hf r (by simpa only [uIcc_of_le hst] using hr)

variable (period : ℝ) [Fact (0 < period)]

/-- Actual smooth-in-time finite-Sobolev PDE approximations imply the limiting signed integral
energy bound.
The premises include their literal PDEs and strong convergence, never an assumed energy inequality.
-/
theorem weighted_pde_energy_subinterval_limit {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq : 3
    ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (order : α → ℕ) (ρ ρ'
        : ℝ → ℝ)
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
    (hpos : ∀ r ∈ Icc 0 T, ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K r).coefficient x v, v⟫_ℝ)
    (hKG : ∀ r ∈ Ioo 0 T, ∀ x v, (K r).coefficient x ((G r).coefficient x v) = v)
    (hediv : ∀ n i j r, r ∈ Ioo 0 T → value period (e n i j r) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ n i j r, r ∈ Ioo 0 T → p n i j r ∈ gradientSpace period κ m)
    (hz : ∀ r ∈ Ioo 0 T, value period (z r) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ r ∈ Ioo 0 T, ∀ᵐ x ∂liftMeasure period, ‖value period (z r) x‖ ≤ B r)
    (heq : ∀ n i j r, r ∈ Ioo 0 T → e' n i j r +
      transportOperator period hq κ m (z r) (restrictOperator period (by
          norm_num : 1 ≤ 2) (e n i j r)) +
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
  have h := weighted_sobolev_energy_integral period hq order ρ ρ' κ m K G
    (e n) (e' n) (p n) (forcing n) z s t c ν K' B hst hc hν
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
    (fun r => viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) *
      weightedMetricSum (ρ r) order (K r).operator (fun i j => value period (e n i j r)) +
      (ρ' r / ρ r) * weightedMetricLoss (ρ r) order (K r).operator (fun i j => value period (e n i
          j r)) +
      (((K r).bound : ℝ) / c) * weightedForcingSum (ρ r) order (fun i j => forcing n i j r))
    (fun r hr => by rw [ha r (hsub hr), hb r (hsub hr), hd r (hsub hr),
      hXdef n r (hsub hr), hYdef n r (hsub hr), hZdef n r (hsub hr)])
  rw [hi] at h
  rw [← subinterval_inner_eq, subinterval_path_inner T hT s t h0s hst htT]
  exact h

end EulerPDESubintervalEnergyLimit
