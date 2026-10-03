/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinEvolution

/-! Energy estimates for a finite family of coupled derivative paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

variable {ι E G : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The ℓ² carrier for a family of copies of a real Hilbert space. -/
abbrev EnergyFamily (ι : Type*) (E : Type*) :=
  PiLp 2 (fun _ : ι => E)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Componentwise interval integrability assembles into integrability of a finite Hilbert product
forcing path. -/
theorem intervalIntegrable_energyFamily_of_components
    (f : ℝ → ι → E)
    (hf : ∀ i : ι, IntervalIntegrable (fun t => f t i) volume 0 1) :
    IntervalIntegrable (fun t => WithLp.toLp 2 (f t)) volume 0 1 := by
  apply intervalIntegrable_iff.mpr
  change Integrable (fun t => WithLp.toLp 2 (f t))
    (volume.restrict (uIoc 0 1))
  rw [integrable_piLp_iff]
  intro i
  change Integrable (fun t => f t i) (volume.restrict (uIoc 0 1))
  exact intervalIntegrable_iff.mp (hf i)

/-- Apply one continuous linear map in every coordinate of a finite Hilbert product. -/
def energyFamilyMap (L : E →L[ℝ] G) :
    EnergyFamily ι E →L[ℝ] EnergyFamily ι G := by
  let eE : EnergyFamily ι E ≃L[ℝ] (ι → E) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)
  let eG : EnergyFamily ι G ≃L[ℝ] (ι → G) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => G)
  let p : (ι → E) →L[ℝ] (ι → G) :=
    ContinuousLinearMap.pi (fun i => L.comp (ContinuousLinearMap.proj i))
  exact eG.symm.toContinuousLinearMap.comp (p.comp eE.toContinuousLinearMap)

omit [Fintype ι] [CompleteSpace E] [CompleteSpace G] in
@[simp]
theorem energyFamilyMap_apply (L : E →L[ℝ] G) (u : EnergyFamily ι E) (i : ι) :
    (energyFamilyMap (ι := ι) L u).ofLp i = L (u.ofLp i) := by
  simp [energyFamilyMap]

omit [CompleteSpace E] [CompleteSpace G] in
/-- The diagonal family map does not increase the operator norm. -/
theorem energyFamilyMap_norm_le (L : E →L[ℝ] G) :
    ‖energyFamilyMap (ι := ι) L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro u
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  calc
    Real.sqrt (∑ i : ι, ‖(energyFamilyMap (ι := ι) L u).ofLp i‖ ^ 2) ≤
        Real.sqrt (‖L‖ ^ 2 * ∑ i : ι, ‖u.ofLp i‖ ^ 2) :=
      Real.sqrt_le_sqrt (calc
        ∑ i : ι, ‖(energyFamilyMap (ι := ι) L u).ofLp i‖ ^ 2 ≤
        ∑ i : ι, (‖L‖ * ‖u.ofLp i‖) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [energyFamilyMap_apply]
          exact (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (norm_nonneg L) (norm_nonneg _))).2
              (L.le_opNorm (u.ofLp i))
        _ = ‖L‖ ^ 2 * ∑ i : ι, ‖u.ofLp i‖ ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.mul_sum])
    _ = ‖L‖ * Real.sqrt (∑ i : ι, ‖u.ofLp i‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg ‖L‖), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg L)]

/-- Lift a continuous linear map to finite energy families, linearly in the map. -/
def FamilyEnergy.energyFamilyMapLinear :
    (E →L[ℝ] G) →ₗ[ℝ]
      (EnergyFamily ι E →L[ℝ] EnergyFamily ι G) where
  toFun := fun L => energyFamilyMap (ι := ι) (E := E) (G := G) L
  map_add' := by
    intro L₁ L₂
    ext u i
    simp [energyFamilyMap_apply]
  map_smul' := by
    intro a L
    ext u i
    simp [energyFamilyMap_apply]

omit [CompleteSpace E] [CompleteSpace G] in
theorem FamilyEnergy.energyFamilyMapLinear_apply (L : E →L[ℝ] G) :
    FamilyEnergy.energyFamilyMapLinear (ι := ι) L = energyFamilyMap (ι := ι) L := rfl

/-- The diagonal product construction depends continuously on the original linear map. -/
def energyFamilyMapCLM :
    (E →L[ℝ] G) →L[ℝ] (EnergyFamily ι E →L[ℝ] EnergyFamily ι G) := by
  let f : (E →L[ℝ] G) →ₗ[ℝ]
      (EnergyFamily ι E →L[ℝ] EnergyFamily ι G) :=
    FamilyEnergy.energyFamilyMapLinear (ι := ι) (E := E) (G := G)
  have hf : ∀ L, ‖f L‖ ≤ 1 * ‖L‖ := by
    intro L
    change ‖FamilyEnergy.energyFamilyMapLinear (ι := ι) (E := E) (G := G) L‖ ≤ 1 * ‖L‖
    rw [FamilyEnergy.energyFamilyMapLinear_apply]
    simpa using energyFamilyMap_norm_le (ι := ι) (E := E) (G := G) L
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E →L[ℝ] G)
    (F := EnergyFamily ι E →L[ℝ] EnergyFamily ι G) f 1 hf

omit [CompleteSpace E] [CompleteSpace G] in
@[simp]
theorem energyFamilyMapCLM_apply (L : E →L[ℝ] G) :
    energyFamilyMapCLM (ι := ι) L = energyFamilyMap (ι := ι) L := by
  simp [energyFamilyMapCLM, LinearMap.mkContinuous_apply,
    FamilyEnergy.energyFamilyMapLinear_apply]

/-- Sum the component energy identities and drift forms on a finite Hilbert product. -/
def EnergyWeakFormData.family (W : EnergyWeakFormData E G) :
    EnergyWeakFormData (EnergyFamily ι E) (EnergyFamily ι G) where
  coefficient := fun t => energyFamilyMapCLM (ι := ι) (W.coefficient t)
  coefficientBound := W.coefficientBound
  coefficientBound_nonneg := W.coefficientBound_nonneg
  coefficient_aestronglyMeasurable :=
    (energyFamilyMapCLM (ι := ι)).continuous.comp_aestronglyMeasurable
      W.coefficient_aestronglyMeasurable
  coefficient_norm_le := by
    intro t
    rw [energyFamilyMapCLM_apply]
    exact (energyFamilyMap_norm_le (ι := ι) (W.coefficient t)).trans
      (W.coefficient_norm_le t)
  diffusivity := W.diffusivity
  diffusivity_pos := W.diffusivity_pos
  gradient := energyFamilyMap (ι := ι) W.gradient
  driftBound := max W.driftBound 0
  driftForm := fun t u => ∑ i : ι, W.driftForm t (u.ofLp i)
  weakForm_energy := by
    change ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ u,
      2 * inner ℝ u (energyFamilyMapCLM (ι := ι) (W.coefficient t) u) =
        -2 * (∑ i : ι, W.driftForm t (u.ofLp i)) -
          2 * W.diffusivity *
            ‖energyFamilyMap (ι := ι) W.gradient u‖ ^ 2
    filter_upwards [W.weakForm_energy] with t ht u
    have hsum : ∑ i : ι, (2 * inner ℝ (u.ofLp i)
        (W.coefficient t (u.ofLp i))) =
        ∑ i : ι, (-2 * W.driftForm t (u.ofLp i) -
          2 * W.diffusivity * ‖W.gradient (u.ofLp i)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ht (u.ofLp i)
    have hgradSq :
        ‖energyFamilyMap (ι := ι) W.gradient u‖ ^ 2 =
          ∑ i : ι, ‖W.gradient (u.ofLp i)‖ ^ 2 := by
      rw [PiLp.norm_eq_of_L2]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        sq_nonneg ‖(energyFamilyMap (ι := ι) W.gradient u).ofLp i‖)]
      simp [energyFamilyMap_apply]
    rw [energyFamilyMapCLM_apply, PiLp.inner_apply]
    simp only [energyFamilyMap_apply]
    calc
      2 * ∑ i : ι, inner ℝ (u.ofLp i) (W.coefficient t (u.ofLp i)) =
          ∑ i : ι, 2 * inner ℝ (u.ofLp i) (W.coefficient t (u.ofLp i)) := by
        rw [Finset.mul_sum]
      _ = ∑ i : ι, (-2 * W.driftForm t (u.ofLp i) -
          2 * W.diffusivity * ‖W.gradient (u.ofLp i)‖ ^ 2) := hsum
      _ = -2 * (∑ i : ι, W.driftForm t (u.ofLp i)) -
          2 * W.diffusivity * (∑ i : ι, ‖W.gradient (u.ofLp i)‖ ^ 2) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = -2 * (∑ i : ι, W.driftForm t (u.ofLp i)) -
          2 * W.diffusivity * ‖energyFamilyMap (ι := ι) W.gradient u‖ ^ 2 := by
        rw [hgradSq]
  drift_bound := by
    change ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ u,
      |∑ i : ι, W.driftForm t (u.ofLp i)| ≤
        max W.driftBound 0 *
          ‖energyFamilyMap (ι := ι) W.gradient u‖ * ‖u‖
    filter_upwards [W.drift_bound] with t ht u
    have hcomponent := fun i : ι => ht (u.ofLp i)
    have hsumAbs :
        |∑ i : ι, W.driftForm t (u.ofLp i)| ≤
          ∑ i : ι, |W.driftForm t (u.ofLp i)| := Finset.abs_sum_le_sum_abs _ _
    have hsumDriftPointwise (i : ι) :
        |W.driftForm t (u.ofLp i)| ≤
          max W.driftBound 0 *
            (‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖) := by
      calc
        |W.driftForm t (u.ofLp i)| ≤
            W.driftBound * ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ := hcomponent i
        _ = W.driftBound *
              (‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖) := by ring
        _ ≤ max W.driftBound 0 *
              (‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg
            (norm_nonneg _) (norm_nonneg _))
    have hsumDrift :
        ∑ i : ι, |W.driftForm t (u.ofLp i)| ≤
          max W.driftBound 0 * ∑ i : ι,
            ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ := by
      calc
        _ ≤ ∑ i : ι, max W.driftBound 0 *
              (‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖) :=
          Finset.sum_le_sum fun i _ => hsumDriftPointwise i
        _ = max W.driftBound 0 *
              ∑ i : ι, ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ := by
          rw [Finset.mul_sum]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : ι => ‖W.gradient (u.ofLp i)‖) (fun i => ‖u.ofLp i‖)
    have hsumNonneg : 0 ≤ ∑ i : ι,
        ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hnormG : ‖energyFamilyMap (ι := ι) W.gradient u‖ ^ 2 =
        ∑ i : ι, ‖W.gradient (u.ofLp i)‖ ^ 2 := by
      rw [PiLp.norm_eq_of_L2]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        sq_nonneg ‖(energyFamilyMap (ι := ι) W.gradient u).ofLp i‖)]
      simp [energyFamilyMap_apply]
    have hnormU : ‖u‖ ^ 2 = ∑ i : ι, ‖u.ofLp i‖ ^ 2 := by
      rw [PiLp.norm_eq_of_L2]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖u.ofLp i‖)]
    have hprod :
        (∑ i : ι, ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖) ^ 2 ≤
          (‖energyFamilyMap (ι := ι) W.gradient u‖ * ‖u‖) ^ 2 := by
      rw [mul_pow, hnormG, hnormU]
      exact hCS
    have hsumBound :
        ∑ i : ι, ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ ≤
          ‖energyFamilyMap (ι := ι) W.gradient u‖ * ‖u‖ :=
      (sq_le_sq₀ hsumNonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 hprod
    calc
      |∑ i : ι, W.driftForm t (u.ofLp i)| ≤
          ∑ i : ι, |W.driftForm t (u.ofLp i)| := hsumAbs
      _ ≤ max W.driftBound 0 *
          ∑ i : ι, ‖W.gradient (u.ofLp i)‖ * ‖u.ofLp i‖ := hsumDrift
      _ ≤ max W.driftBound 0 *
          (‖energyFamilyMap (ι := ι) W.gradient u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hsumBound (le_max_right _ _)
      _ = max W.driftBound 0 *
          ‖energyFamilyMap (ι := ι) W.gradient u‖ * ‖u‖ := by ring

/-- A forced Galerkin equation with a specified weak energy structure. -/
def ForcedGalerkinData.ofWeak (W : EnergyWeakFormData E G) (initial : E)
    (forcing : ℝ → E) (hforcing : IntervalIntegrable forcing volume 0 1) :
    ForcedGalerkinData E G :=
  { weak := W
    initial := initial
    forcing := forcing
    forcing_integrable := hforcing }

/-- The continuous path whose value is the finite Hilbert product of the component paths. -/
def energyFamilyPath (u : ι → ContinuousMap (Icc (0 : ℝ) 1) E) :
    ContinuousMap (Icc (0 : ℝ) 1) (EnergyFamily ι E) := by
  let e : EnergyFamily ι E ≃L[ℝ] (ι → E) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)
  exact ⟨fun t => WithLp.toLp 2 (fun i => u i t),
    e.symm.continuous.comp (continuous_pi fun i => (u i).continuous)⟩

/-- Combine finitely many forced paths with a common weak energy structure. -/
def ForcedGalerkinData.family (W : EnergyWeakFormData E G)
    (initial : ι → E) (forcing : ℝ → ι → E)
    (hforcing : IntervalIntegrable (fun t => WithLp.toLp 2 (forcing t)) volume 0 1) :
    ForcedGalerkinData (EnergyFamily ι E) (EnergyFamily ι G) :=
  { weak := W.family
    initial := WithLp.toLp 2 initial
    forcing := fun t => WithLp.toLp 2 (forcing t)
    forcing_integrable := hforcing }

omit [CompleteSpace G] in
/-- If every coordinate path solves its forced equation, their finite Hilbert product solves the
diagonal product equation. -/
theorem ForcedGalerkinData.familyPath_isSolution
    (W : EnergyWeakFormData E G) (initial : ι → E) (forcing : ℝ → ι → E)
    (hforcing : IntervalIntegrable
      (fun t => WithLp.toLp 2 (forcing t)) volume 0 1)
    (hforcing_i : ∀ i, IntervalIntegrable (fun t => forcing t i) volume 0 1)
    (u : ι → ContinuousMap (Icc (0 : ℝ) 1) E)
    (hu : ∀ i, (ForcedGalerkinData.ofWeak W (initial i)
      (fun t => forcing t i) (hforcing_i i)).ode.IsSolution (u i)) :
    (ForcedGalerkinData.family W initial forcing hforcing).ode.IsSolution
      (energyFamilyPath u) := by
  let D := ForcedGalerkinData.family W initial forcing hforcing
  let v := energyFamilyPath u
  apply (D.ode.isSolution_iff_integralSolution v).2
  intro t ht
  let e : EnergyFamily ι E ≃L[ℝ] (ι → E) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)
  apply e.injective
  ext i
  let π : EnergyFamily ι E →L[ℝ] E :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) i
  have hvcoord (s : Icc (0 : ℝ) 1) : π (v s) = u i s := by
    change (WithLp.toLp 2 (fun j => u j s)).ofLp i = u i s
    rw [PiLp.toLp_apply]
  have hvext : (fun s => π (AVenhance.Infra.ODE.extendCurve (by norm_num) v s)) =
      AVenhance.Infra.ODE.extendCurve (by norm_num) (u i) := by
    funext s
    rw [AVenhance.Infra.ODE.extendCurve, AVenhance.Infra.ODE.extendCurve]
    exact hvcoord (AVenhance.Infra.ODE.clampPoint 0 1 (by norm_num) s)
  have hsubset : Set.uIcc 0 t ⊆ Set.uIcc 0 1 := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hRhsInt := D.ode.rhs_intervalIntegrable v
  have hRhsIntT := hRhsInt.mono_set hsubset
  have hmap := π.intervalIntegral_comp_comm hRhsIntT
  have hcomponent :
      (fun s => π (D.ode.rhs v s)) =
        fun s => (ForcedGalerkinData.ofWeak W (initial i)
          (fun r => forcing r i) (hforcing_i i)).ode.rhs (u i) s := by
    funext s
    change π ((W.family.coefficient s) (AVenhance.Infra.ODE.extendCurve
        (by norm_num) v s) + WithLp.toLp 2 (forcing s)) =
      W.coefficient s (AVenhance.Infra.ODE.extendCurve (by norm_num) (u i) s) +
        forcing s i
    rw [map_add]
    simp only [EnergyWeakFormData.family, energyFamilyMapCLM_apply]
    simp only [π, PiLp.proj_apply]
    rw [energyFamilyMap_apply]
    change W.coefficient s (π (AVenhance.Infra.ODE.extendCurve
        (by norm_num) v s)) + forcing s i =
      W.coefficient s (AVenhance.Infra.ODE.extendCurve (by norm_num) (u i) s) +
        forcing s i
    rw [congrFun hvext s]
  have hsol := (hu i).integralSolution
    (ForcedGalerkinData.ofWeak W (initial i) (fun r => forcing r i)
      (hforcing_i i)).ode
  have hsolT := hsol t ht
  have hinitial : π D.initial = initial i := by
    simp [D, ForcedGalerkinData.family, π]
  have hleft : π (AVenhance.Infra.ODE.extendCurve (by norm_num) v t) =
      AVenhance.Infra.ODE.extendCurve (by norm_num) (u i) t := by
    exact congrFun hvext t
  change π (AVenhance.Infra.ODE.extendCurve (by norm_num) v t) =
    π (D.initial + ∫ s in 0..t, D.ode.rhs v s)
  rw [hleft, map_add, hinitial]
  rw [← hmap]
  rw [intervalIntegral.integral_congr (fun s _ => congrFun hcomponent s)]
  exact hsolT

/-- The diagonal finite-family ODE for the ordered derivatives of one Fourier Galerkin path.
Each component uses the original weak operator, with its derivative commutator included in the
component forcing. -/
noncomputable def ForcedGalerkinData.wordDerivativeFamilyData
    {N : ℕ} (D : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G)
    (u : ContinuousMap (Icc (0 : ℝ) 1) (Coefficients (RealFourierDimension N)))
    (word : ι → List (Fin 2)) :
    ForcedGalerkinData (EnergyFamily ι (Coefficients (RealFourierDimension N)))
      (EnergyFamily ι G) := by
  let initial : ι → Coefficients (RealFourierDimension N) := fun i =>
    realFourierWordDerivativeMap N (word i) D.initial
  let forcing : ℝ → ι → Coefficients (RealFourierDimension N) := fun t i =>
    D.transformedForcing (realFourierWordDerivativeMap N (word i))
      (AVenhance.Infra.ODE.extendCurve (by norm_num) u) t
  have hcomponents : ∀ i, IntervalIntegrable (fun t => forcing t i) volume 0 1 := by
    intro i
    exact D.transformedForcing_intervalIntegrable u
      (realFourierWordDerivativeMap N (word i))
  have hforcing := intervalIntegrable_energyFamily_of_components forcing hcomponents
  exact ForcedGalerkinData.family D.weak initial forcing hforcing

omit [CompleteSpace G] in
/-- Differentiated Galerkin paths form a solution of the diagonal finite-family ODE. -/
theorem ForcedGalerkinData.wordDerivativeFamilyPath_isSolution
    {N : ℕ} (D : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G)
    (u : ContinuousMap (Icc (0 : ℝ) 1) (Coefficients (RealFourierDimension N)))
    (hu : D.ode.IsSolution u) (word : ι → List (Fin 2)) :
    (D.wordDerivativeFamilyData u word).ode.IsSolution
      (energyFamilyPath (fun i => ForcedGalerkinData.mapPath
        (realFourierWordDerivativeMap N (word i)) u)) := by
  let initial : ι → Coefficients (RealFourierDimension N) := fun i =>
    realFourierWordDerivativeMap N (word i) D.initial
  let forcing : ℝ → ι → Coefficients (RealFourierDimension N) := fun t i =>
    D.transformedForcing (realFourierWordDerivativeMap N (word i))
      (AVenhance.Infra.ODE.extendCurve (by norm_num) u) t
  have hcomponents : ∀ i, IntervalIntegrable (fun t => forcing t i) volume 0 1 := by
    intro i
    exact D.transformedForcing_intervalIntegrable u
      (realFourierWordDerivativeMap N (word i))
  have hforcing := intervalIntegrable_energyFamily_of_components forcing hcomponents
  have hsolution : ∀ i,
      (ForcedGalerkinData.ofWeak D.weak (initial i) (fun t => forcing t i)
        (hcomponents i)).ode.IsSolution
        (ForcedGalerkinData.mapPath
          (realFourierWordDerivativeMap N (word i)) u) := by
    intro i
    exact D.wordDerivativeTransform_isSolution u hu (word i)
  change (ForcedGalerkinData.family D.weak initial forcing hforcing).ode.IsSolution
    (energyFamilyPath (fun i => ForcedGalerkinData.mapPath
      (realFourierWordDerivativeMap N (word i)) u))
  exact ForcedGalerkinData.familyPath_isSolution D.weak initial forcing hforcing
    hcomponents (fun i => ForcedGalerkinData.mapPath
      (realFourierWordDerivativeMap N (word i)) u) hsolution

end AVenhance.Infra.Classical

end
