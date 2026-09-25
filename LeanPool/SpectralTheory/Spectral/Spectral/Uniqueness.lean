/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.Stone.Theorem
public import LeanPool.SpectralTheory.Spectral.Spectral.FuncCalc
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars


/-!
# Spectral theorem: measurable uniqueness

This file proves that PVMs representing the same self-adjoint operator agree on every measurable
set. It compares their phase unitary groups through their common generator, recovers scalar
measures from characteristic functions, and then recovers projections. It also shows that every
representing PVM computes the selected measurable functional calculus.
-/

@[expose] public section

open Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem phaseGroup_norm (U : StrongContUnitary E) (t : ℝ) (x : E) :
    ‖U.toFun t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (U.isUnitary t) x

private theorem generator_domain_invariant (U : StrongContUnitary E)
    (s : ℝ) (x : U.generator.domain) :
    U.toFun s (x : E) ∈ U.generator.domain := by
  rw [U.mem_generator_domain_iff]
  refine ⟨U.toFun s (U.generator x), ?_⟩
  convert Tendsto.comp (U.toFun s).continuous.continuousAt
    (U.tendsto_generator x) using 1
  funext t
  change (Complex.I * (t : ℂ))⁻¹ •
      (U.toFun t (U.toFun s (x : E)) - U.toFun s (x : E)) =
    U.toFun s ((Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
  rw [map_smul, map_sub]
  congr 1
  rw [← mul_apply_eq_comp, ← U.add]
  rw [add_comm, U.add, mul_apply_eq_comp]

private theorem orbit_hasDerivAt (U : StrongContUnitary E)
    (x : U.generator.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ U.toFun t (x : E))
      (Complex.I • U.toFun s (U.generator x)) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hscaled := (U.tendsto_generator x).const_smul Complex.I
  have hmapped := Tendsto.comp (U.toFun s).continuous.continuousAt hscaled
  convert hmapped using 1
  · funext t
    change (t⁻¹ : ℝ) • (U.toFun (s + t) (x : E) - U.toFun s (x : E)) =
      U.toFun s (Complex.I • ((Complex.I * (t : ℂ))⁻¹ •
        (U.toFun t (x : E) - (x : E))))
    rw [U.add, mul_apply_eq_comp]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [← map_sub, ← map_smul]
    congr 1
    rw [smul_smul]
    congr 1
    rw [mul_inv_rev, Complex.inv_I]
    ring_nf
    rw [Complex.I_sq]
    rw [neg_mul, one_mul, neg_neg]
    change ((t⁻¹ : ℝ) : ℂ) = ((t : ℝ) : ℂ)⁻¹
    exact Complex.ofReal_inv t
  · rw [map_smul]

private theorem tendsto_phaseGroup_apply
    (U : StrongContUnitary E) {α : Type*} {l : Filter α}
    {t : α → ℝ} {t₀ : ℝ} {y : α → E} {y₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hy : Tendsto y l (nhds y₀)) :
    Tendsto (fun a => U.toFun (t a) (y a)) l (nhds (U.toFun t₀ y₀)) := by
  have hzero : Tendsto (fun a => U.toFun (t a) (y a - y₀)) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, sub_self, phaseGroup_norm, norm_zero] using
      (hy.sub (tendsto_const_nhds :
        Tendsto (fun _ : α => y₀) l (nhds y₀))).norm
  have hfixed : Tendsto (fun a => U.toFun (t a) y₀) l
      (nhds (U.toFun t₀ y₀)) :=
    (U.stronglyContinuous y₀).continuousAt.tendsto.comp ht
  convert hzero.add hfixed using 1
  · funext a
    rw [map_sub, sub_add_cancel]
  · rw [zero_add]

private theorem relativeOrbit_hasDerivAt_zero
    (U V : StrongContUnitary E) (y : E)
    (hUy : y ∈ U.generator.domain) (hVy : y ∈ V.generator.domain)
    (hAy : U.generator ⟨y, hUy⟩ = V.generator ⟨y, hVy⟩) :
    HasDerivAt (fun h : ℝ => U.toFun (-h) (V.toFun h y)) 0 0 := by
  let yu : U.generator.domain := ⟨y, hUy⟩
  let yv : V.generator.domain := ⟨y, hVy⟩
  have hVslope : Tendsto
      (fun h : ℝ => h⁻¹ • (V.toFun h y - y))
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I • V.generator yv)) := by
    simpa only [zero_add, V.zero, one_apply_eq_self] using
      (orbit_hasDerivAt V yv 0).tendsto_slope_zero
  have hUneg := (orbit_hasDerivAt U yu 0).scomp_of_eq
    (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp only [neg_zero])
  have hUslope : Tendsto
      (fun h : ℝ => h⁻¹ • (U.toFun (-h) y - y))
      (nhdsWithin 0 {0}ᶜ) (nhds (-Complex.I • U.generator yu)) := by
    convert hUneg.tendsto_slope_zero using 1
    · funext h
      dsimp only [yu, Function.comp_apply]
      rw [zero_add, neg_zero, U.zero, one_apply_eq_self]
    · congr 1
      rw [U.zero, one_apply_eq_self]
      module
  have htneg : Tendsto (fun h : ℝ => -h)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hle : nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 := inf_le_left
    simpa only [neg_zero] using
      ((continuous_neg : Continuous fun h : ℝ => -h).tendsto 0).mono_left hle
  have hfirst : Tendsto
      (fun h : ℝ => U.toFun (-h) (h⁻¹ • (V.toFun h y - y)))
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I • V.generator yv)) := by
    simpa only [U.zero, one_apply_eq_self] using
      tendsto_phaseGroup_apply U htneg hVslope
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hsum := hfirst.add hUslope
  convert hsum using 1
  · funext h
    simp only [zero_add, neg_zero, U.zero, V.zero, one_apply_eq_self]
    simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [map_smul, map_sub]
    module
  · congr 1
    rw [← hAy]
    module

private theorem relativeOrbit_hasDerivAt
    (U V : StrongContUnitary E) (hgen : U.generator = V.generator)
    (x : U.generator.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ => U.toFun (-t) (V.toFun t (x : E))) 0 s := by
  have hdomain : U.generator.domain = V.generator.domain :=
    congrArg LinearPMap.domain hgen
  have hxV : (x : E) ∈ V.generator.domain := by
    rw [← hdomain]
    exact x.property
  let xv : V.generator.domain := ⟨(x : E), hxV⟩
  let y : E := V.toFun s (x : E)
  have hyV : y ∈ V.generator.domain :=
    generator_domain_invariant V s xv
  have hyU : y ∈ U.generator.domain := by
    rw [hdomain]
    exact hyV
  have hAy : U.generator ⟨y, hyU⟩ = V.generator ⟨y, hyV⟩ := by
    apply (LinearPMap.ext_iff.mp hgen).2
  have hrel := relativeOrbit_hasDerivAt_zero U V y hyU hyV hAy
  have hmapped : HasDerivAt
      (fun h : ℝ => U.toFun (-s) (U.toFun (-h) (V.toFun h y))) 0 0 := by
    have hconst := hasDerivAt_const (x := (0 : ℝ))
      (c := (U.toFun (-s)).restrictScalars ℝ)
    simpa only [ContinuousLinearMap.coe_restrictScalars', zero_apply, zero_add,
      map_zero] using hconst.clm_apply hrel
  have hshift := hmapped.scomp_of_eq s ((hasDerivAt_id s).sub_const s)
    (by simp only [id_eq, sub_self])
  convert hshift using 1
  · funext t
    simp only [Function.comp_apply, id_eq]
    dsimp only [y]
    symm
    calc
      U.toFun (-s) (U.toFun (-(t - s))
          (V.toFun (t - s) (V.toFun s (x : E)))) =
          (U.toFun (-s) * U.toFun (-(t - s)))
            ((V.toFun (t - s) * V.toFun s) (x : E)) := by
        rw [mul_apply_eq_comp, mul_apply_eq_comp]
      _ = U.toFun (-s + -(t - s)) (V.toFun ((t - s) + s) (x : E)) := by
        rw [← U.add, ← V.add]
      _ = U.toFun (-t) (V.toFun t (x : E)) := by
        congr 2 <;> ring_nf
  · simp only [one_smul]

private theorem phaseGroups_apply_eq_of_generator_eq
    (U V : StrongContUnitary E) (hgen : U.generator = V.generator)
    (x : U.generator.domain) (t : ℝ) :
    U.toFun t (x : E) = V.toFun t (x : E) := by
  let F : ℝ → E := fun s => U.toFun (-s) (V.toFun s (x : E))
  have hderiv (s : ℝ) : HasDerivAt F 0 s :=
    relativeOrbit_hasDerivAt U V hgen x s
  have hconst : F t = F 0 := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  dsimp only [F] at hconst
  rw [neg_zero, U.zero, V.zero, one_apply_eq_self] at hconst
  have hmapped := congrArg (fun y : E => U.toFun t y) hconst
  rw [← mul_apply_eq_comp, ← U.add, add_neg_cancel, U.zero,
    one_apply_eq_self] at hmapped
  exact hmapped.symm

private theorem phaseGroups_eq_of_generator_eq
    (U V : StrongContUnitary E) (hgen : U.generator = V.generator)
    (hdense : DenseRange (fun x : U.generator.domain => (x : E))) :
    U = V := by
  have htoFun : U.toFun = V.toFun := by
    funext t
    apply ContinuousLinearMap.ext
    intro x
    have hfun : (fun y : E => U.toFun t y) = fun y : E => V.toFun t y :=
      hdense.equalizer (U.toFun t).continuous (V.toFun t).continuous (by
        funext y
        exact phaseGroups_apply_eq_of_generator_eq U V hgen y t)
    exact congrFun hfun x
  cases U with
  | mk u hu hz ha hc =>
      cases V with
      | mk v hv vz va vc =>
          dsimp only at htoFun
          subst v
          rfl

private theorem inner_proj (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    @inner ℂ E _ x (E_pvm.proj S x) =
      (E_pvm.scalarContent x S : ℂ) := by
  have hproj := E_pvm.isOrthogonalProjection S hS
  have hid : E_pvm.proj S (E_pvm.proj S x) = E_pvm.proj S x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x) hproj.2.eq
    simpa only [mul_apply_eq_comp] using h
  have hfix : (E_pvm.proj S).adjoint (E_pvm.proj S x) = E_pvm.proj S x := by
    rw [hproj.1.adjoint_eq, hid]
  calc
    @inner ℂ E _ x (E_pvm.proj S x) =
        @inner ℂ E _ (E_pvm.proj S x) x := by
      calc
        _ = @inner ℂ E _ x ((E_pvm.proj S).adjoint x) := by
          rw [hproj.1.adjoint_eq]
        _ = _ := ContinuousLinearMap.adjoint_inner_right (E_pvm.proj S) x x
    _ = @inner ℂ E _ (E_pvm.proj S x) (E_pvm.proj S x) := by
      calc
        _ = @inner ℂ E _ ((E_pvm.proj S).adjoint (E_pvm.proj S x)) x := by
          rw [hfix]
        _ = _ := ContinuousLinearMap.adjoint_inner_left
          (E_pvm.proj S) x (E_pvm.proj S x)
    _ = (‖E_pvm.proj S x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
    _ = (E_pvm.scalarContent x S : ℂ) := by
      rw [E_pvm.scalarContent_eq_norm_sq x S hS, Complex.ofReal_pow]

private theorem inner_proj_left (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    @inner ℂ E _ (E_pvm.proj S x) x =
      (E_pvm.scalarContent x S : ℂ) := by
  calc
    @inner ℂ E _ (E_pvm.proj S x) x =
        starRingEnd ℂ (@inner ℂ E _ x (E_pvm.proj S x)) :=
      (inner_conj_symm (E_pvm.proj S x) x).symm
    _ = starRingEnd ℂ (E_pvm.scalarContent x S : ℂ) := by
      rw [inner_proj E_pvm x S hS]
    _ = (E_pvm.scalarContent x S : ℂ) := Complex.conj_ofReal _

private theorem proj_eq_of_scalarMeasure_eq (E₁ E₂ : PVM E)
    (hmeasure : ∀ x : E, E₁.scalarMeasure x = E₂.scalarMeasure x)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S := by
  have hcontent (x : E) : E₁.scalarContent x S = E₂.scalarContent x S := by
    have h := congrArg (fun μ : Measure ℝ => μ S) (hmeasure x)
    rw [E₁.scalarMeasure_apply x S hS, E₂.scalarMeasure_apply x S hS] at h
    exact (ENNReal.ofReal_eq_ofReal_iff
      (E₁.scalarContent_nonneg x S hS)
      (E₂.scalarContent_nonneg x S hS)).mp h
  have hlinear : (E₁.proj S).toLinearMap = (E₂.proj S).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro x
    change @inner ℂ E _ (E₁.proj S x) x = @inner ℂ E _ (E₂.proj S x) x
    rw [inner_proj_left E₁ x S hS, inner_proj_left E₂ x S hS, hcontent]
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun hlinear x

private noncomputable def characteristicPhase (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))

private theorem characteristicPhase_measurable (t : ℝ) :
    Measurable (characteristicPhase t) := by
  unfold characteristicPhase
  fun_prop

private theorem characteristicPhase_bounded (t : ℝ) :
    ∀ r, ‖characteristicPhase t r‖ ≤ 1 := by
  intro r
  rw [characteristicPhase, mul_assoc, ← Complex.ofReal_mul,
    Complex.norm_exp_I_mul_ofReal]

private theorem inner_phaseUnitaryGroup (E_pvm : PVM E) (x : E) (t : ℝ) :
    @inner ℂ E _ x (E_pvm.phaseUnitaryGroup.toFun t x) =
      charFun (E_pvm.scalarMeasure x) t := by
  rw [charFun_apply_real]
  change @inner ℂ E _ x
    (E_pvm.integral (characteristicPhase t) (characteristicPhase_measurable t)
      ⟨1, characteristicPhase_bounded t⟩ x) = _
  have hinner := PVM.inner_integral_self E_pvm (characteristicPhase t)
    (characteristicPhase_measurable t) ⟨1, characteristicPhase_bounded t⟩ x
  rw [hinner]
  congr 1
  funext r
  unfold characteristicPhase
  congr 1
  ring

private theorem scalarMeasure_eq_of_phaseGroup_eq (E₁ E₂ : PVM E)
    (hgroup : E₁.phaseUnitaryGroup = E₂.phaseUnitaryGroup) (x : E) :
    E₁.scalarMeasure x = E₂.scalarMeasure x := by
  apply Measure.ext_of_charFun
  funext t
  rw [← inner_phaseUnitaryGroup E₁ x t,
    ← inner_phaseUnitaryGroup E₂ x t, hgroup]

/-- Two PVM representations of the same self-adjoint operator agree on every measurable set.

This is the extensional uniqueness statement supported by the current `PVM` definition, whose
axioms constrain `proj` only on measurable sets. -/
theorem spectral_theorem_uniqueness_on_measurable
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S := by
  have hgen : E₁.phaseUnitaryGroup.generator =
      E₂.phaseUnitaryGroup.generator := by
    rw [E₁.phaseUnitaryGroup_generator, E₂.phaseUnitaryGroup_generator, h₁, h₂]
  have hdense : DenseRange
      (fun x : E₁.phaseUnitaryGroup.generator.domain => (x : E)) := by
    apply Dense.denseRange_val
    rw [E₁.phaseUnitaryGroup_generator, h₁]
    exact hA.dense_domain
  have hgroup : E₁.phaseUnitaryGroup = E₂.phaseUnitaryGroup :=
    phaseGroups_eq_of_generator_eq
      E₁.phaseUnitaryGroup E₂.phaseUnitaryGroup hgen hdense
  apply proj_eq_of_scalarMeasure_eq E₁ E₂
  · intro x
    exact scalarMeasure_eq_of_phaseGroup_eq E₁ E₂ hgroup x
  · exact hS

/-- Literal PVM uniqueness follows once both PVMs use the conventional zero value outside the
measurable sets. -/
private theorem spectral_theorem_uniqueness_of_zero_nonmeasurable
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (h₁_nonmeasurable : ∀ S, ¬ MeasurableSet S → E₁.proj S = 0)
    (h₂_nonmeasurable : ∀ S, ¬ MeasurableSet S → E₂.proj S = 0) :
    E₁ = E₂ := by
  have hproj : E₁.proj = E₂.proj := by
    funext S
    by_cases hS : MeasurableSet S
    · exact spectral_theorem_uniqueness_on_measurable A hA E₁ E₂ h₁ h₂ S hS
    · rw [h₁_nonmeasurable S hS, h₂_nonmeasurable S hS]
  cases E₁
  cases E₂
  congr

/-- Two PVM representations of the same self-adjoint operator agree on every measurable set.

Literal equality of the `PVM` structures is not implied because their laws intentionally leave
`proj S` unconstrained when `S` is nonmeasurable. -/
theorem spectral_theorem_uniqueness
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S :=
  spectral_theorem_uniqueness_on_measurable A hA E₁ E₂ h₁ h₂ S hS

/-- Every PVM representing a self-adjoint operator computes the selected spectral functional
calculus. -/
theorem spectralFuncCalc_eq_unboundedIntegral_of_representation
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E_pvm : PVM E)
    (hE : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (f : ℝ → ℂ) (hf : Measurable f) :
    spectralFuncCalc A hA f hf = E_pvm.unboundedIntegral f hf := by
  apply PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
  intro S hS
  exact spectral_theorem_uniqueness A hA
    (Classical.choose (spectral_theorem_existence A hA)) E_pvm
    (Classical.choose_spec (spectral_theorem_existence A hA)) hE S hS
