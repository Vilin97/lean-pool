/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Instances.Matrix

/-!
# The AKL a.e.-quotient coefficient-field kernel

The high-moment manuscript uses uniformly elliptic, measurable coefficient
fields modulo equality almost everywhere.  This module gives its fixed-`Θ`
carrier and its integral-only local sigma-algebras.
-/

@[expose] public section

namespace Homogenization.Source.AKL

open MeasureTheory

noncomputable section

local instance matMeasurableSpace {d : ℕ} : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

local instance matBorelSpace {d : ℕ} : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

abbrev Field (d : ℕ) := Vec d →ₘ[volume] Mat d

def Carrier (d : ℕ) (Θ : ℝ) : Type _ :=
  {a : Field d // ∀ᵐ x ∂volume, IsEllipticMatrix 1 Θ (a x)}

abbrev BorelRegion (d : ℕ) :=
  {U : Set (Vec d) // MeasurableSet U}

variable {d : ℕ} {Θ : ℝ}

private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (η : Vec d) :
    vecNormSq (matVecMul A η) ≤ Lam * vecDot η (matVecMul (symmPart A) η) := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  set ξ := matVecMul A η with hξ
  have hAinv : matVecMul A⁻¹ ξ = η := by
    rw [hξ, matVecMul_mul, Matrix.nonsing_inv_mul A hdet, matVecMul_one]
  have hident :
      vecDot ξ (matVecMul A⁻¹ ξ) = vecDot η (matVecMul (symmPart A) η) := by
    rw [hAinv, vecDot_comm, vecDot_matVecMul_symmPart, hξ]
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hA.1 hA.2.1
  have hsecond : Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hA.2.2.2 ξ
  rw [hident] at hsecond
  have hscaled := mul_le_mul_of_nonneg_left hsecond hLam_pos.le
  have hcancel : Lam * (Lam⁻¹ * vecNormSq ξ) = vecNormSq ξ := by
    field_simp [hLam_pos.ne']
  rw [hcancel] at hscaled
  exact hscaled

private def IsEllipticEntry (Θ : ℝ) (A : Mat d) : Prop :=
  (∀ ξ : Vec d, vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ η : Vec d, vecNormSq (matVecMul A η) ≤ Θ * vecDot η (matVecMul A η))

private theorem isEllipticMatrix_one_iff (A : Mat d) :
    IsEllipticMatrix 1 Θ A ↔ 1 ≤ Θ ∧ IsEllipticEntry Θ A := by
  constructor
  · intro hA
    refine ⟨hA.2.1, fun ξ => by simpa using hA.2.2.1 ξ, fun η => ?_⟩
    have h := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hA η
    rwa [vecDot_matVecMul_symmPart] at h
  · rintro ⟨hΘ, hc, himg⟩
    have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘ
    have hlin : ∀ x y : Vec d, matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
      intro x y
      funext i
      simp [matVecMul, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]
    have hinj : Function.Injective (matVecMul A) := by
      intro x y hxy
      have hz : matVecMul A (x - y) = 0 := by rw [hlin, hxy]; simp
      have hcz := hc (x - y)
      rw [hz, vecDot_zero_right] at hcz
      have hzero : vecNormSq (x - y) = 0 := le_antisymm hcz (vecNormSq_nonneg _)
      exact sub_eq_zero.mp (vecNormSq_eq_zero hzero)
    have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    refine ⟨one_pos, hΘ, fun ξ => by simpa using hc ξ, fun ξ => ?_⟩
    set η := matVecMul A⁻¹ ξ with hη
    have hAη : matVecMul A η = ξ := by
      rw [hη, matVecMul_mul, Matrix.mul_nonsing_inv A hdet, matVecMul_one]
    have himgη := himg η
    rw [hAη] at himgη
    have hdot : vecDot η ξ = vecDot ξ (matVecMul A⁻¹ ξ) := by rw [hη, vecDot_comm]
    rw [hdot] at himgη
    have hthis := mul_le_mul_of_nonneg_left himgη (le_of_lt (inv_pos.mpr hΘpos))
    rw [← mul_assoc, inv_mul_cancel₀ hΘpos.ne', one_mul] at hthis
    simpa using hthis

private theorem isClosed_isEllipticEntry :
    IsClosed {A : Mat d | IsEllipticEntry Θ A} := by
  have h₁ : IsClosed
      {A : Mat d | ∀ ξ : Vec d, vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun ξ => ?_
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le continuous_const (by fun_prop)
  have h₂ : IsClosed
      {A : Mat d | ∀ η : Vec d,
        vecNormSq (matVecMul A η) ≤ Θ * vecDot η (matVecMul A η)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun η => ?_
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le (by fun_prop) (by fun_prop)
  exact h₁.inter h₂

private instance instMeasurableSpaceMat : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

private instance instBorelSpaceMat : BorelSpace (Mat d) :=
  ⟨BorelSpace.measurable_eq (α := Fin d → Fin d → ℝ)⟩

private instance instPseudoMetrizableSpaceMat : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))

private theorem measurableSet_isEllipticMatrix :
    MeasurableSet {A : Mat d | IsEllipticMatrix 1 Θ A} := by
  by_cases hΘ : 1 ≤ Θ
  · have hset :
        {A : Mat d | IsEllipticMatrix 1 Θ A} = {A : Mat d | IsEllipticEntry Θ A} := by
      ext A
      simp only [Set.mem_ofPred_eq]
      exact (isEllipticMatrix_one_iff A).trans (and_iff_right hΘ)
    rw [hset]
    exact isClosed_isEllipticEntry.measurableSet
  · have hempty : {A : Mat d | IsEllipticMatrix 1 Θ A} = ∅ := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hA
      exact hΘ hA.2.1
    rw [hempty]
    exact MeasurableSet.empty

private theorem isEllipticMatrix_one_one (hΘ : 1 ≤ Θ) :
    IsEllipticMatrix 1 Θ (1 : Mat d) := by
  have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘ
  refine ⟨one_pos, hΘ, ?_, ?_⟩
  · intro ξ
    simp [matVecMul_one, vecNormSq]
  · intro ξ
    rw [inv_one, matVecMul_one]
    have hinv : Θ⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hΘpos]
      exact hΘ
    have hmul : Θ⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ :=
      mul_le_mul_of_nonneg_right hinv (vecNormSq_nonneg ξ)
    simpa [vecNormSq] using hmul

theorem field_ae_elliptic_iff_exists_pointwise_representative
    {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) (a : Field d) :
    (∀ᵐ x ∂volume, IsEllipticMatrix 1 Θ (a x)) ↔
      ∃ f : Vec d → Mat d, Measurable f ∧
        (∀ x, IsEllipticMatrix 1 Θ (f x)) ∧ a =ᵐ[volume] f := by
  constructor
  · intro ha
    classical
    let f : Vec d → Mat d := fun x =>
      if IsEllipticMatrix 1 Θ (a x) then a x else 1
    have hpred : MeasurableSet {x : Vec d | IsEllipticMatrix 1 Θ (a x)} :=
      measurableSet_isEllipticMatrix.preimage a.measurable
    have hf : Measurable f := by
      exact a.measurable.ite hpred measurable_const
    refine ⟨f, hf, ?_, ?_⟩
    · intro x
      by_cases hx : IsEllipticMatrix 1 Θ (a x)
      · simp [f, hx]
      · simpa [f, hx] using isEllipticMatrix_one_one (d := d) hΘ
    · filter_upwards [ha] with x hx
      simp [f, hx]
  · rintro ⟨f, _hf, hfell, hae⟩
    filter_upwards [hae] with x hx
    rw [hx]
    exact hfell x

theorem carrier_exists_pointwise_elliptic_measurable_representative
    {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) (a : Carrier d Θ) :
    ∃ f : Vec d → Mat d, Measurable f ∧
      (∀ x, IsEllipticMatrix 1 Θ (f x)) ∧ a.1 =ᵐ[volume] f :=
  (field_ae_elliptic_iff_exists_pointwise_representative hΘ a.1).mp a.2

def rawGenerator {d : ℕ} (U : BorelRegion d) (e e' : Vec d)
    (φ : Vec d → ℝ) (a : Vec d → Mat d) : ℝ :=
  ∫ x in U.1, vecDot e' (matVecMul (a x) e) * φ x

def generator {d : ℕ} {Θ : ℝ} (U : BorelRegion d) (e e' : Vec d)
    (φ : Vec d → ℝ) (a : Carrier d Θ) : ℝ :=
  rawGenerator U e e' φ a.1

theorem generator_mk_eq_raw {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) (e e' : Vec d) (φ : Vec d → ℝ)
    (f : Vec d → Mat d) (hf : AEStronglyMeasurable f volume)
    (hEll : ∀ᵐ x ∂volume,
      IsEllipticMatrix 1 Θ ((AEEqFun.mk f hf) x)) :
    generator U e e' φ ⟨AEEqFun.mk f hf, hEll⟩ =
      rawGenerator U e e' φ f := by
  unfold generator rawGenerator
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (AEEqFun.coeFn_mk f hf)] with x hx
  rw [hx]
def localSigma {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) : MeasurableSpace (Carrier d Θ) :=
  MeasurableSpace.generateFrom
    {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = generator U e e' φ ⁻¹' t}
def globalSigma (d : ℕ) (Θ : ℝ) : MeasurableSpace (Carrier d Θ) :=
  localSigma (Θ := Θ)
    (⟨Set.univ, MeasurableSet.univ⟩ : BorelRegion d)

abbrev Law (d : ℕ) (Θ : ℝ) :=
  @Measure (Carrier d Θ) (globalSigma d Θ)

def IsSourceLocal {d : ℕ} {Θ : ℝ} {E : Type*}
    [MeasurableSpace E] (U : BorelRegion d)
    (X : Carrier d Θ → E) : Prop :=
  @Measurable (Carrier d Θ) E (localSigma U) _ X

private def density {d : ℕ} (e e' : Vec d) (a : Carrier d Θ) : Vec d → ℝ :=
  fun x => vecDot e' (matVecMul (a.1 x) e)

private def densityBound {d : ℕ} (Θ : ℝ) (e e' : Vec d) : ℝ :=
  ∑ i, ∑ j, |e' i| * max Θ 0 * |e j|

private theorem ae_abs_density_le_densityBound {d : ℕ} {Θ : ℝ}
    (e e' : Vec d) (a : Carrier d Θ) :
    ∀ᵐ x ∂volume, |density e e' a x| ≤ densityBound Θ e e' := by
  filter_upwards [a.2] with x hx
  simp only [density, densityBound, vecDot, matVecMul]
  calc
    |∑ i, e' i * ∑ j, a.1 x i j * e j| ≤
        ∑ i, |e' i * ∑ j, a.1 x i j * e j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |e' i| * |∑ j, a.1 x i j * e j| := by
      simp only [abs_mul]
    _ ≤ ∑ i, |e' i| * ∑ j, |a.1 x i j * e j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ i, ∑ j, |e' i| * |a.1 x i j| * |e j| := by
      simp only [abs_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, |e' i| * max Θ 0 * |e j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hentry : |a.1 x i j| ≤ max Θ 0 :=
        (abs_apply_le_of_isEllipticMatrix hx i j).trans (le_max_left _ _)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hentry (abs_nonneg (e j))) (abs_nonneg (e' i))

private theorem aestronglyMeasurable_density {d : ℕ} {Θ : ℝ}
    (e e' : Vec d) (a : Carrier d Θ) :
    AEStronglyMeasurable (density e e' a) volume := by
  unfold density
  rw [show (fun x => vecDot e' (matVecMul (a.1 x) e)) =
      ∑ i : Fin d, ∑ j : Fin d, fun x => e' i * (a.1 x i j * e j) by
        funext x
        simp only [vecDot, matVecMul, Finset.mul_sum, Finset.sum_apply]]
  apply Finset.aestronglyMeasurable_sum
  intro i hi
  apply Finset.aestronglyMeasurable_sum
  intro j hj
  have hentry : AEStronglyMeasurable (fun x => a.1 x i j) volume := by
    have hcont : Continuous (fun M : Mat d => M i j) := continuous_apply_apply i j
    simpa [Function.comp_def] using!
      (hcont.measurable.comp a.1.measurable).aestronglyMeasurable
  exact (hentry.mul_const (e j)).const_mul (e' i)

private theorem memLp_top_density {d : ℕ} {Θ : ℝ}
    (e e' : Vec d) (a : Carrier d Θ) :
    MemLp (density e e' a) ⊤ volume := by
  apply memLp_top_of_bound (aestronglyMeasurable_density e e' a)
    (densityBound Θ e e')
  simpa [Real.norm_eq_abs] using ae_abs_density_le_densityBound e e' a

private theorem exists_smoothCompactSupport_L1_sequence {d : ℕ}
    (f : Vec d → ℝ) (hf : MemLp f 1 volume) :
    ∃ ψ : ℕ → Vec d → ℝ,
      (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      Filter.Tendsto (fun n => eLpNorm (f - ψ n) 1 volume) Filter.atTop (nhds 0) := by
  choose ψ hψcompact hψsmooth hψerr using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le (p := (1 : ENNReal)) ENNReal.one_ne_top le_rfl
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  refine ⟨ψ, hψcompact, hψsmooth, ?_⟩
  have hbound : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (ENNReal.ofReal 0)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
  have hzero := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun n => by simp)
    (fun n => hψerr n)
  simpa using hzero

private theorem tendsto_density_mul_of_L1 {d : ℕ} {Θ : ℝ}
    (e e' : Vec d) (a : Carrier d Θ) (f : Vec d → ℝ)
    (ψ : ℕ → Vec d → ℝ)
    (hψ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n))
    (hf : MemLp f 1 volume)
    (hψtend : Filter.Tendsto (fun n => eLpNorm (f - ψ n) 1 volume)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n =>
      eLpNorm (fun x => density e e' a x * (ψ n x - f x)) 1 volume)
      Filter.atTop (nhds 0) := by
  have hdiff : Filter.Tendsto (fun n => eLpNorm (ψ n - f) 1 volume)
      Filter.atTop (nhds 0) := by
    apply hψtend.congr
    intro n
    rw [eLpNorm_sub_comm]
  have hbound : ∀ n,
      eLpNorm (fun x => density e e' a x * (ψ n x - f x)) 1 volume ≤
        eLpNorm (density e e' a) ⊤ volume * eLpNorm (ψ n - f) 1 volume := by
    intro n
    simpa only [ENNReal.coe_one, one_mul, Pi.sub_apply] using
      MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm
      (p := (1 : ENNReal)) (g := ψ n - f) (fun u v : ℝ => u * v) 1
      (continuous_fst.mul continuous_snd) (memLp_top_density e e' a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  have hconst : eLpNorm (density e e' a) ⊤ volume ≠ ⊤ :=
    (memLp_top_density e e' a).eLpNorm_lt_top.ne
  have hscaled : Filter.Tendsto (fun n =>
      eLpNorm (density e e' a) ⊤ volume * eLpNorm (ψ n - f) 1 volume)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hdiff (Or.inr hconst)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
    (fun n => by simp) hbound

private theorem integrable_density_mul {d : ℕ} {Θ : ℝ}
    (e e' : Vec d) (a : Carrier d Θ) (f : Vec d → ℝ)
    (hf : MemLp f 1 volume) :
    Integrable (fun x => density e e' a x * f x) volume := by
  rw [← memLp_one_iff_integrable]
  exact ((memLp_top_density e e' a).mul hf :
    MemLp (fun x => density e e' a x * f x) 1 volume)

private theorem integral_density_indicator_eq {d : ℕ} {Θ : ℝ}
    {U V : BorelRegion d} (hUV : U.1 ⊆ V.1)
    (e e' : Vec d) (φ : Vec d → ℝ) (a : Carrier d Θ) :
    ∫ x in V.1, density e e' a x * U.1.indicator φ x =
      generator U e e' φ a := by
  let F : Vec d → ℝ := fun x => density e e' a x * φ x
  have hindicator : (fun x => density e e' a x * U.1.indicator φ x) = U.1.indicator F := by
    funext x
    by_cases hx : x ∈ U.1 <;> simp [F, hx]
  rw [hindicator, ← integral_indicator V.2, Set.indicator_indicator,
    Set.inter_eq_right.mpr hUV, integral_indicator U.2]
  rfl

private theorem measurable_generator_localSigma {d : ℕ} {Θ : ℝ}
    (V : BorelRegion d) (e e' : Vec d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcompact : HasCompactSupport ψ) :
    @Measurable (Carrier d Θ) ℝ (localSigma V) _ (generator V e e' ψ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', ψ, hψ, hψcompact, t, ht, rfl⟩

private theorem measurable_generator_of_subset {d : ℕ} {Θ : ℝ}
    {U V : BorelRegion d} (hUV : U.1 ⊆ V.1)
    (e e' : Vec d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ) :
    @Measurable (Carrier d Θ) ℝ (localSigma V) _ (generator U e e' φ) := by
  let f : Vec d → ℝ := U.1.indicator φ
  have hfint : Integrable f volume := by
    exact (hφ.continuous.integrable_of_hasCompactSupport hφcompact).indicator U.2
  have hf : MemLp f 1 volume := memLp_one_iff_integrable.mpr hfint
  obtain ⟨ψ, hψcompact, hψsmooth, hψtend⟩ :=
    exists_smoothCompactSupport_L1_sequence f hf
  let : MeasurableSpace (Carrier d Θ) := localSigma V
  apply measurable_of_tendsto_metrizable
  · intro n
    exact measurable_generator_localSigma V e e' (ψ n) (hψsmooth n) (hψcompact n)
  · rw [tendsto_pi_nhds]
    intro a
    have hprod : Filter.Tendsto (fun n =>
        eLpNorm (fun x => density e e' a x * (ψ n x - f x)) 1 volume)
        Filter.atTop (nhds 0) :=
      tendsto_density_mul_of_L1 e e' a f ψ hψsmooth hf hψtend
    have htarget : Integrable (fun x => density e e' a x * f x) volume :=
      integrable_density_mul e e' a f hf
    have hseqint : ∀ n, Integrable (fun x => density e e' a x * ψ n x) volume := by
      intro n
      apply integrable_density_mul e e' a (ψ n)
      rw [memLp_one_iff_integrable]
      exact (hψsmooth n).continuous.integrable_of_hasCompactSupport (hψcompact n)
    have hL1 : Filter.Tendsto (fun n =>
        eLpNorm ((fun x => density e e' a x * ψ n x) -
          fun x => density e e' a x * f x) 1 volume)
        Filter.atTop (nhds 0) := by
      apply hprod.congr
      intro n
      congr 1
      funext x
      simp only [Pi.sub_apply]
      ring
    have hint := tendsto_setIntegral_of_L1' (fun x => density e e' a x * f x)
      (Filter.Eventually.of_forall hseqint) hL1 V.1
    have htarget_eq : (∫ x in V.1, density e e' a x * f x) =
        generator U e e' φ a := by
      simpa [f] using integral_density_indicator_eq hUV e e' φ a
    rw [htarget_eq] at hint
    simpa [generator, rawGenerator, density] using hint

theorem localSigma_mono {d : ℕ} {Θ : ℝ} {U V : BorelRegion d} (hUV : U.1 ⊆ V.1) :
    localSigma (Θ := Θ) U ≤ localSigma (Θ := Θ) V := by
  unfold localSigma
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨e, e', φ, hφ, hφcompact, t, ht, rfl⟩
  exact measurable_generator_of_subset hUV e e' φ hφ hφcompact ht

def intTranslation {d : ℕ} (z : Fin d → ℤ) : Vec d :=
  fun i => z i

def translateField {d : ℕ} (z : Fin d → ℤ) (a : Field d) : Field d :=
  a.compMeasurePreserving (fun x : Vec d => x + intTranslation z)
    (measurePreserving_add_right
      (volume : Measure (Vec d)) (intTranslation z))

theorem translateField_ae {d : ℕ} (z : Fin d → ℤ) (a : Field d) :
    translateField z a =ᵐ[volume]
      fun x => a (x + intTranslation z) :=
  AEEqFun.coeFn_compMeasurePreserving _ _

def translate {d : ℕ} {Θ : ℝ} (z : Fin d → ℤ) :
    Carrier d Θ → Carrier d Θ :=
  fun a => ⟨translateField z a.1, by
    filter_upwards [translateField_ae z a.1,
      (measurePreserving_add_right
        (volume : Measure (Vec d)) (intTranslation z)).quasiMeasurePreserving.tendsto_ae
          a.2] with x hfield hell
    rw [hfield]
    exact hell⟩

private theorem generator_translate_global {d : ℕ} {Θ : ℝ}
    (z : Fin d → ℤ) (e e' : Vec d) (φ : Vec d → ℝ) (a : Carrier d Θ) :
    generator (⟨Set.univ, MeasurableSet.univ⟩ : BorelRegion d) e e' φ
        (translate z a) =
      generator (⟨Set.univ, MeasurableSet.univ⟩ : BorelRegion d) e e'
        (fun y => φ (y - intTranslation z)) a := by
  unfold generator rawGenerator
  simp only [Measure.restrict_univ]
  have hcomp := (measurePreserving_add_right
      (volume : Measure (Vec d)) (intTranslation z)).integral_comp
      (Homeomorph.addRight (intTranslation z)).measurableEmbedding
      (fun y => vecDot e' (matVecMul (a.1 y) e) * φ (y - intTranslation z))
  rw [← hcomp]
  refine integral_congr_ae ?_
  filter_upwards [translateField_ae z a.1] with x hx
  change vecDot e' (matVecMul (translateField z a.1 x) e) * φ x = _
  rw [hx]
  congr 2
  abel

theorem measurable_translate_global {d : ℕ} {Θ : ℝ}
    (z : Fin d → ℤ) :
    @Measurable (Carrier d Θ) (Carrier d Θ)
      (globalSigma d Θ) (globalSigma d Θ) (translate (Θ := Θ) z) := by
  let U : BorelRegion d := ⟨Set.univ, MeasurableSet.univ⟩
  let : MeasurableSpace (Carrier d Θ) := localSigma U
  change @Measurable (Carrier d Θ) (Carrier d Θ) (localSigma U)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ∃ t : Set ℝ, MeasurableSet t ∧ s = generator U e e' φ ⁻¹' t})
      (translate z)
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, hφcompact, t, ht, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (y - intTranslation z)
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y - intTranslation z) :=
    contDiff_id.sub contDiff_const
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, Function.comp_def] using hφ.comp hsub
  have hψcompact : HasCompactSupport ψ := by
    simpa [ψ, Function.comp_def] using
      hφcompact.comp_homeomorph (Homeomorph.subRight (intTranslation z))
  have hset :
      translate (Θ := Θ) z ⁻¹' (generator
          U e e' φ ⁻¹' t) = generator U e e' ψ ⁻¹' t := by
    ext a
    change generator U e e' φ (translate z a) ∈ t ↔ generator U e e' ψ a ∈ t
    rw [generator_translate_global]
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', ψ, hψ, hψcompact, t, ht, rfl⟩

def supDist {d : ℕ} (x y : Vec d) : ℝ :=
  ‖x - y‖

end

end Homogenization.Source.AKL
