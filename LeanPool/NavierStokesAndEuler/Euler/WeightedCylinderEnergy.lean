/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WeightedRootLimit

@[expose] public section

/-! Actual Gevrey-weighted cylinder energy with signed radius derivative and no zero-norm
  differentiation. -/

noncomputable section

namespace EulerWeightedCylinderEnergy

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerSpatialSobolevInverse EulerCylinderSobolev EulerMetricEnergyEvolution
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerWeightedRootLimit
  EulerPacketWeights EulerWeightedEnergy
open scoped ContDiff ENNReal NNReal Topology

section WeightedNorms

variable {α β H : Type*} [Fintype α] [Fintype β]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The finite external-word Gevrey sum of the source's base-word metric roots. -/
def weightedMetricSum (ρ : ℝ) (order : α → ℕ) (K : H →L[ℝ] H) (e : α → β → H) : ℝ :=
  ∑ i, weight ρ (order i) * familyMetricNorm K (e i)

/-- The same metric sum with the external derivative count, giving the radius-loss term. -/
def weightedMetricLoss (ρ : ℝ) (order : α → ℕ) (K : H →L[ℝ] H) (e : α → β → H) : ℝ :=
  ∑ i, (order i : ℝ) * weight ρ (order i) * familyMetricNorm K (e i)

/-- The actual finite weighted sum of base-word Hilbert forcing norms. -/
def weightedForcingSum (ρ : ℝ) (order : α → ℕ) (f : α → β → H) : ℝ :=
  ∑ i, weight ρ (order i) * familyNorm (f i)

end WeightedNorms

variable (period : ℝ) [Fact (0 < period)]

/-- The explicit common coefficient in the actual viscous metric-root estimate. -/
def viscousGrowthCoefficient (K : SmoothCoefficient period)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (κ : ℝ) (m : Vector3) (c ν : ℝ) (B : ℝ≥0) : ℝ :=
  (‖K'‖ + 2 * transportEnergyConstant period K κ m B +
    2 * ν * heatEnergyConstant period K c) / (2 * c ^ 2)

/-- The finite Gevrey-weighted integral energy inequality derived from the actual viscous PDE.
The signed radius term is retained exactly, and no differentiability of the unregularized norm is
  assumed. -/
theorem weighted_cylinder_energy_integral {α β : Type*} [Fintype α] [Fintype β]
    (order : α → ℕ) (ρ ρ' : ℝ → ℝ)
    (κ : ℝ) (m : Vector3) (K G : ℝ → SmoothCoefficient period)
    (e e' p forcing : α → β → ℝ → LiftL2 period) (z : ℝ → LiftL2 period)
    (s t c ν : ℝ) (K' : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (B : ℝ → ℝ≥0)
    (J : ∀ i j u, u ∈ Ioo s t → SpatialJet period standardDirection 2 (e i j u))
    (g : α → β → ℝ → LiftDomain period → Vector3)
    (hrep : ∀ i j u, u ∈ Ioo s t → (e i j u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g
      i j u)
    (hg : ∀ i j u, u ∈ Ioo s t → ∀ x, ContDiff ℝ ∞ (localFieldLift period (g i j u) x))
    (hDg : ∀ i j u, u ∈ Ioo s t → MemLp (fun x => fderiv ℝ (localFieldLift period (g i j u) x) 0)
      2 (liftMeasure period))
    (hst : s ≤ t) (hc : 0 < c) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Icc s t)) (hρpos : ∀ u ∈ Icc s t, 0 < ρ u)
    (hρd : ∀ u ∈ Ioo s t, HasDerivAt ρ (ρ' u) u)
    (hKc : ContinuousOn (fun u => (K u).operator) (Icc s t))
    (hec : ∀ i j, ContinuousOn (e i j) (Icc s t))
    (hKt : ∀ u ∈ Ioo s t, HasDerivAt (fun v => (K v).operator) (K' u) u)
    (het : ∀ i j u, u ∈ Ioo s t → HasDerivAt (e i j) (e' i j u) u)
    (hsym : ∀ u ∈ Ioo s t, ∀ x v w,
      ⟪(K u).coefficient x v, w⟫_ℝ = ⟪v, (K u).coefficient x w⟫_ℝ)
    (hpos : ∀ u ∈ Icc s t, ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K u).coefficient x v, v⟫_ℝ)
    (hKG : ∀ u ∈ Ioo s t, ∀ x v, (K u).coefficient x ((G u).coefficient x v) = v)
    (hediv : ∀ i j u, u ∈ Ioo s t → e i j u ∈ divergenceFreeSpace period κ m)
    (hp : ∀ i j u, u ∈ Ioo s t → p i j u ∈ gradientSpace period κ m)
    (hz : ∀ u ∈ Ioo s t, z u ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ u ∈ Ioo s t, ∀ᵐ x ∂liftMeasure period, ‖z u x‖ ≤ B u)
    (heq : ∀ i j u (hu : u ∈ Ioo s t), e' i j u +
      EulerRepresentativeMetricEvolution.liftedTransport period κ m (g i j u) (z u)
        (hDg i j u hu) (B u) (hzB u hu) + (G u).operator (p i j u) =
      forcing i j u + ν • jetLaplacian period (J i j u hu))
    (hAint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
        viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u) +
      (ρ' u / ρ u) * (order i : ℝ) * weight (ρ u) (order i)) (Icc s t))
    (hFint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
      ((((K u).bound : ℝ) / c) * familyNorm (fun j => forcing i j u))) (Icc s t)) :
    weightedMetricSum (ρ t) order (K t).operator (fun i j => e i j t) -
      weightedMetricSum (ρ s) order (K s).operator (fun i j => e i j s) ≤
      ∫ u in s..t,
        viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u) *
          weightedMetricSum (ρ u) order (K u).operator (fun i j => e i j u) +
        (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => e i j u) +
        (((K u).bound : ℝ) / c) * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
  let Q := fun i u => familyEnergy (K u).operator (fun j => e i j u)
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
      (familyEnergy_coercive (K u).operator (fun j => e i j u) c hcoer)
  have hregd (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      DifferentiableAt ℝ (fun v => √(Q i v + δ ^ 2)) u := by
    have hsymL : ∀ v w, ⟪(K u).operator v, w⟫_ℝ = ⟪v, (K u).operator w⟫_ℝ :=
      coefficientOperator_inner_swap (K u).coefficient (K u).measurable
        (K u).bound (K u).norm_bound (hsym u hu)
    have hd : HasDerivAt (Q i) (∑ j, (⟪K' u (e i j u), e i j u⟫_ℝ +
        2 * ⟪(K u).operator (e i j u), e' i j u⟫_ℝ)) u :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        metric_energy_hasDerivAt (fun v => (K v).operator) (e i j) u (K' u) (e' i j u)
          (hKt u hu) (het i j u hu) hsymL)
    have hq := hQ0 i u ⟨hu.1.le, hu.2.le⟩
    exact (HasDerivAt.sqrt (hd.add_const (δ ^ 2)) (by nlinarith : Q i u + δ ^ 2 ≠
      0)).differentiableAt
  have hreg (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      deriv (fun v => √(Q i v + δ ^ 2)) u ≤ a u * √(Q i u + δ ^ 2) + F i u := by
    exact finite_cylinder_viscous_energy period κ m K (G u) (e i) u δ c ν (K' u)
      (fun j => e' i j u) (fun j => p i j u) (fun j => forcing i j u) (z u)
      (fun j => J i j u hu) (fun j => g i j u) (fun j => hrep i j u hu) (fun j => hg i j u hu)
      (fun j => hDg i j u hu) hδ hc hν (hKt u hu) (fun j => het i j u hu)
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
      a u * weightedMetricSum (ρ u) order (K u).operator (fun i j => e i j u) +
      (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => e i j u) +
      (((K u).bound : ℝ) / c) * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
    simp only [Ψ, A, w, w', F, Q, weightedMetricSum, weightedMetricLoss, weightedForcingSum,
      familyMetricNorm, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  simpa only [halg, w, Q, a, weightedMetricSum, familyMetricNorm] using hsum

end EulerWeightedCylinderEnergy
