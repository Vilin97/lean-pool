/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.WeakForm
import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Pointwise
import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.Basic
import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.MatchedTrace
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity
import Mathlib.Algebra.Order.Chebyshev

/-!
# The coupled level-energy estimate

Derivation of the generic De Giorgi core's *level-energy hypothesis* from the
coupled weak form.  Given the representation package `(v, v*)` solving `CoupledWeakForm`
on a cube `U`, the measurable representatives `w₁ ≈ v − ½p·x`,
`w₂ ≈ −v* + ½p·x` share a trace and satisfy, for every median level `m₀` and
every `k ≥ 0`,
`∑ᵢ‖1_{A_k¹}∂ᵢw₁‖₂ + ∑ᵢ‖1_{A_k²}∂ᵢw₂‖₂ ≤ E₀·√(|A_k¹|+|A_k²|)`,
with `E₀ = 2√d·M`, `M = √(Θ|p|²+|q|²)`.

The core mechanism: testing `CoupledWeakForm` at the truncation pair
`(f_k, −g_k)` (D1/D4) produces the level energy identity
`E_k = ∫_{A¹}(q−½ap)·∇w₁ + ∫_{A²}(½aᵗp)·∇w₂`, which the `s`-metric Young
inequality (`symmForm_young`, `t = 1`) and the coefficient bounds
(`symmPartInv_bulkV_le`, `symmPartInv_bulkVstar_le`) drive to
`E_k ≤ 2M²|A_k|`; then `s ≥ 1` and a Cauchy–Schwarz on the `2d`
coordinate norms give the `√`-shaped conclusion.
-/

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Measurable representative of an `H¹` function -/

/-- Every `H¹` function has a **measurable representative**: an `H¹` function with
the same weak gradient and a measurable value function almost everywhere equal to
the original.  This is the swap needed to feed the De Giorgi core, whose
truncation toolbox requires `Measurable toFun`. -/
theorem exists_measurableRep {U : Set (Vec d)} (u : H1Function U) :
    ∃ w : H1Function U, Measurable w.toFun ∧
      w.toFun =ᵐ[volume.restrict U] u.toFun ∧ w.grad = u.grad := by
  classical
  set f : Vec d → ℝ := u.memL2.1.mk u.toFun with hf_def
  have hf_meas : Measurable f := u.memL2.1.stronglyMeasurable_mk.measurable
  have hae : u.toFun =ᵐ[volume.restrict U] f := u.memL2.1.ae_eq_mk
  have hf_memL2 : MemL2On U f := (MeasureTheory.memLp_congr_ae hae).mp u.memL2
  have hf_weak : HasWeakGradientOn U f u.grad := by
    intro i φ hφ hφc hφsub
    have hu := u.hasWeakGradient i φ hφ hφc hφsub
    have hcongr :
        ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) ∂volume
          = ∫ x in U, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    rw [hcongr, hu]
  refine ⟨⟨f, u.grad, hf_memL2, u.gradMemL2, hf_weak⟩, hf_meas, hae.symm, rfl⟩

/-! ## `H¹₀` membership transfers along a.e.-equality -/

/-- Uniqueness of weak gradients under a.e.-equal values (open domain). -/
theorem h1grad_ae_eq_of_toFun_ae_eq {U : Set (Vec d)} (hU : IsOpen U)
    {u v : H1Function U}
    (huv : u.toFun =ᵐ[volume.restrict U] v.toFun) :
    u.grad =ᵐ[volume.restrict U] v.grad := by
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      MeasureTheory.LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord : ∀ i : Fin d,
      (fun x => u.grad x i) =ᵐ[volume.restrict U] fun x => v.grad x i := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU (hloc u i) (hloc v i) (u.hasWeakGradient i) ?_
    intro φ hφ hφc hφsub
    have hv := v.hasWeakGradient i φ hφ hφc hφsub
    have hcongr :
        ∫ x in U, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume
          = ∫ x in U, v.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [huv] with x hx
      rw [hx]
    rw [hcongr, hv]
  have hall : ∀ᵐ x ∂volume.restrict U, ∀ i : Fin d, u.grad x i = v.grad x i :=
    MeasureTheory.ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  ext i; exact hx i

/-- **`H¹₀` a.e.-transfer.**  If `h : H¹(U)` is a.e. equal to the value function
of an `H¹₀(U)` witness `W`, then `h.toFun ∈ H¹₀(U)`.  (Constant-sequence
application of the `H¹₀`-limit closure.) -/
theorem memH10_of_ae_eq_h10 {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (h : H1Function U) (W : H10Function U)
    (hae : h.toFun =ᵐ[volume.restrict U] W.toH1Function.toFun) :
    MemH10 U h.toFun := by
  have hgrad : h.grad =ᵐ[volume.restrict U] W.toH1Function.grad :=
    h1grad_ae_eq_of_toFun_ae_eq hU.isOpen hae
  refine memH10_of_tendsto_H1 hU h (fun _ => W.toH1Function) (fun _ => ⟨W, rfl⟩) ?_ ?_
  · have hz : (fun _ : ℕ => eLpNorm (fun x => h.toFun x - W.toH1Function.toFun x) 2
        (volumeMeasureOn U)) = fun _ => 0 := by
      funext n
      refine (eLpNorm_eq_zero_of_ae_zero ?_)
      filter_upwards [hae] with x hx
      simp [hx]
    rw [hz]; exact tendsto_const_nhds
  · intro i
    have hz : (fun _ : ℕ => eLpNorm (fun x => h.grad x i - W.toH1Function.grad x i) 2
        (volumeMeasureOn U)) = fun _ => 0 := by
      funext n
      refine (eLpNorm_eq_zero_of_ae_zero ?_)
      have hgi : (fun x => h.grad x i) =ᵐ[volume.restrict U] fun x => W.toH1Function.grad x i := by
        filter_upwards [hgrad] with x hx; rw [hx]
      filter_upwards [hgi] with x hx
      simp [hx]
    rw [hz]; exact tendsto_const_nhds

/-! ## Sign flip of the coupled weak form -/

/-- The coupled weak form is odd in `(q, v, v*)`. -/
theorem coupledWeakForm_neg {a : CoeffField d} {U : Set (Vec d)} {q : Vec d}
    {v vstar : H1Function U} (h : CoupledWeakForm a U q v vstar) :
    CoupledWeakForm a U (-q) (-v) (-vstar) := by
  intro φ φstar hsum
  have hbase := h φ φstar hsum
  have e1 : ∀ x, vecDot (φ.grad x) (matVecMul (a x) ((-v).grad x))
      = -vecDot (φ.grad x) (matVecMul (a x) (v.grad x)) := by
    intro x
    simp only [Homogenization.H1Function.neg_grad]
    rw [matVecMul_neg, vecDot_neg_right]
  have e2 : ∀ x, vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) ((-vstar).grad x))
      = -vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x)) := by
    intro x
    simp only [Homogenization.H1Function.neg_grad]
    rw [matVecMul_neg, vecDot_neg_right]
  have e3 : ∀ x, vecDot (-q) (φ.grad x) = -vecDot q (φ.grad x) := by
    intro x; rw [vecDot_neg_left]
  simp only [e1, e2, e3]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg, MeasureTheory.integral_neg,
    ← neg_add]
  rw [hbase]

/-! ## The affine `H¹` function `x ↦ ½ p·x` on a bounded domain -/

/-- `x ↦ ½ p·x` as an `H¹` function on a bounded measurable domain, assembled from
the coordinate `H¹` functions.  Constant gradient `½ p`. -/
def affineHalfOn {U : Set (Vec d)} (hUm : MeasurableSet U) (hUb : IsBoundedDomain U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (p : Vec d) : H1Function U :=
  ∑ i : Fin d, ((1 / 2 : ℝ) * p i) • H1Function.coordOnIsBoundedDomain hUm hUb i

@[simp] theorem affineHalfOn_grad {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (p : Vec d) :
    (affineHalfOn hUm hUb p).grad = fun _ => (1 / 2 : ℝ) • p := by
  rw [affineHalfOn, H1Function.sum_grad]
  funext x
  simp only [Homogenization.H1Function.smul_grad, H1Function.coordOnIsBoundedDomain_grad]
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVec, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => (1 / 2 : ℝ) * p i)]
  simp

@[simp] theorem affineHalfOn_toFun {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (p : Vec d) :
    (affineHalfOn hUm hUb p).toFun = fun x => (1 / 2 : ℝ) * vecDot p x := by
  rw [affineHalfOn, H1Function.sum_toFun]
  funext x
  simp only [Homogenization.H1Function.smul_toFun, H1Function.coordOnIsBoundedDomain_apply]
  rw [vecDot]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ## A subset-restricted indicator integral -/

/-- For `A ⊆ U` measurable, integrating `A.indicator f` over `U` is the same as
integrating `f` over `A`. -/
theorem setIntegral_indicator_subset {U A : Set (Vec d)}
    (hAm : MeasurableSet A) (hAU : A ⊆ U) (f : Vec d → ℝ) :
    ∫ x in U, A.indicator f x ∂volume = ∫ x in A, f x ∂volume := by
  rw [MeasureTheory.integral_indicator hAm, MeasureTheory.Measure.restrict_restrict hAm,
    Set.inter_eq_left.mpr hAU]

/-! ## The level-energy identity -/

/-- **Level-energy identity.**  Testing the coupled weak form at the truncation
pair `(f_k, −g_k)` yields
`E_k = ∫_{A₁}(q−½ap)·∇w₁ + ∫_{A₂}(½aᵗp)·∇w₂`, where
`E_k = ∫_{A₁}∇w₁·s∇w₁ + ∫_{A₂}∇w₂·s∇w₂` and `Aᵢ = {wᵢ > m₀+k}`. -/
theorem levelEnergy_identity {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {Θ : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn 1 Θ U a)
    {p q : Vec d} {v vstar : H1Function U}
    (hCWF : CoupledWeakForm a U q v vstar)
    {w₁ w₂ : H1Function U} (hw1meas : Measurable w₁.toFun) (hw2meas : Measurable w₂.toFun)
    (hw1g : ∀ x, w₁.grad x = v.grad x - (1 / 2 : ℝ) • p)
    (hw2g : ∀ x, w₂.grad x = -vstar.grad x + (1 / 2 : ℝ) • p)
    (hmatch : MemH10 U (fun x => w₁.toFun x - w₂.toFun x))
    (m₀ k : ℝ) :
    (∫ x in {x | x ∈ U ∧ m₀ + k < w₁.toFun x},
        vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x)) ∂volume)
      + (∫ x in {x | x ∈ U ∧ m₀ + k < w₂.toFun x},
        vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x)) ∂volume)
      = (∫ x in {x | x ∈ U ∧ m₀ + k < w₁.toFun x},
          vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x) ∂volume)
        + (∫ x in {x | x ∈ U ∧ m₀ + k < w₂.toFun x},
          vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x) ∂volume) := by
  classical
  have vsubr : ∀ (u y z : Vec d), vecDot u (y - z) = vecDot u y - vecDot u z := by
    intro u y z; rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, ← sub_eq_add_neg]
  have vsubl : ∀ (y z u : Vec d), vecDot (y - z) u = vecDot y u - vecDot z u := by
    intro y z u; rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  set A₁ : Set (Vec d) := {x | x ∈ U ∧ m₀ + k < w₁.toFun x} with hA1_def
  set A₂ : Set (Vec d) := {x | x ∈ U ∧ m₀ + k < w₂.toFun x} with hA2_def
  have hA1m : MeasurableSet A₁ :=
    hUmeas.inter (measurableSet_lt measurable_const hw1meas)
  have hA2m : MeasurableSet A₂ :=
    hUmeas.inter (measurableSet_lt measurable_const hw2meas)
  have hA1U : A₁ ⊆ U := fun x hx => hx.1
  have hA2U : A₂ ⊆ U := fun x hx => hx.1
  -- gradient dictionaries
  have hvg : ∀ x, v.grad x = w₁.grad x + (1 / 2 : ℝ) • p := by
    intro x; rw [hw1g x]; module
  have hvsg : ∀ x, vstar.grad x = (1 / 2 : ℝ) • p - w₂.grad x := by
    intro x; rw [hw2g x]; module
  -- L² memberships
  have hw1L2 : MemVectorL2 U w₁.grad := w₁.grad_memVectorL2
  have hw2L2 : MemVectorL2 U w₂.grad := w₂.grad_memVectorL2
  have hsw1 : MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (w₁.grad x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hw1L2
  have hsw2 : MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (w₂.grad x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hw2L2
  have hAp : MemVectorL2 U (fun x => matVecMul (a x) p) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll (memVectorL2_const p)
  have hATp : MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) p) := by
    have heq : (fun x => matVecMul (matTranspose (a x)) p)
        = fun x => matVecMul (symmPart (a x)) p - matVecMul (skewPart (a x)) p := by
      funext x; exact matVecMul_matTranspose_eq (a x) p
    rw [heq]
    exact (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll (memVectorL2_const p)).sub
      (memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll (memVectorL2_const p))
  have hqc : MemVectorL2 U (fun _ => q) := memVectorL2_const q
  -- IntegrableOn shortcuts over `A₁`, `A₂`
  have iE1 : MeasureTheory.IntegrableOn
      (fun x => vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x))) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hw1L2 hsw1).mono_set hA1U
  have iE2 : MeasureTheory.IntegrableOn
      (fun x => vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x))) A₂ :=
    (integrableOn_vecDot_of_memVectorL2 hw2L2 hsw2).mono_set hA2U
  have iAp : MeasureTheory.IntegrableOn (fun x => vecDot (w₁.grad x) (matVecMul (a x) p)) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hw1L2 hAp).mono_set hA1U
  have iATp : MeasureTheory.IntegrableOn
      (fun x => vecDot (w₂.grad x) (matVecMul (matTranspose (a x)) p)) A₂ :=
    (integrableOn_vecDot_of_memVectorL2 hw2L2 hATp).mono_set hA2U
  have iq : MeasureTheory.IntegrableOn (fun x => vecDot q (w₁.grad x)) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hqc hw1L2).mono_set hA1U
  -- truncations `f_k`, `g_k`
  obtain ⟨fk, hfk_tf, hfk_grad⟩ := exists_h1_max_sub_const hU w₁ (m₀ + k)
  obtain ⟨gk, hgk_tf, hgk_grad⟩ := exists_h1_max_sub_const hU w₂ (m₀ + k)
  have hsum : MemH10 U (fun x => fk.toFun x + (-gk).toFun x) := by
    have hD4 := memH10_max_sub_matched hU w₁ w₂ hmatch (m₀ + k)
    have heq : (fun x => fk.toFun x + (-gk).toFun x)
        = (fun x => max (w₁.toFun x - (m₀ + k)) 0 - max (w₂.toFun x - (m₀ + k)) 0) := by
      funext x
      rw [Homogenization.H1Function.neg_toFun]
      show fk.toFun x + -gk.toFun x = _
      rw [congrFun hfk_tf x, congrFun hgk_tf x]; ring
    rw [heq]; exact hD4
  have hkey := hCWF fk (-gk) hsum
  -- first CWF integral as `∫_{A₁}(∇w₁·s∇w₁ + ½ ∇w₁·ap)`
  have hT1 : (∫ x in U, vecDot (fk.grad x) (matVecMul (a x) (v.grad x)) ∂volume)
      = ∫ x in A₁,
          (vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x))
            + (1 / 2 : ℝ) * vecDot (w₁.grad x) (matVecMul (a x) p)) ∂volume := by
    rw [← setIntegral_indicator_subset hA1m hA1U]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hfk_grad, MeasureTheory.ae_restrict_mem hUmeas] with x hgx hxU
    rw [hgx, hvg x]
    by_cases hc : m₀ + k < w₁.toFun x
    · rw [Set.indicator_of_mem (show x ∈ {y | m₀ + k < w₁.toFun y} from hc),
        Set.indicator_of_mem (show x ∈ A₁ from ⟨hxU, hc⟩)]
      have hs := vecDot_matVecMul_eq_symmPart (a x) (w₁.grad x)
      rw [matVecMul_add, matVecMul_smul, vecDot_add_right, vecDot_smul_right, hs]
    · rw [Set.indicator_of_notMem (show x ∉ {y | m₀ + k < w₁.toFun y} from hc),
        Set.indicator_of_notMem (show x ∉ A₁ from fun h => hc h.2)]
      simp [vecDot_zero_left]
  have hT1split : (∫ x in U, vecDot (fk.grad x) (matVecMul (a x) (v.grad x)) ∂volume)
      = (∫ x in A₁, vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x)) ∂volume)
        + (1 / 2 : ℝ) * ∫ x in A₁, vecDot (w₁.grad x) (matVecMul (a x) p) ∂volume := by
    rw [hT1, MeasureTheory.integral_add iE1 (iAp.const_mul _),
      MeasureTheory.integral_const_mul]
  -- second CWF integral as `∫_{A₂}(∇w₂·s∇w₂ − ½ ∇w₂·aᵗp)`
  have hT2 : (∫ x in U, vecDot ((-gk).grad x)
        (matVecMul (matTranspose (a x)) (vstar.grad x)) ∂volume)
      = ∫ x in A₂,
          (vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x))
            - (1 / 2 : ℝ) * vecDot (w₂.grad x) (matVecMul (matTranspose (a x)) p)) ∂volume := by
    rw [← setIntegral_indicator_subset hA2m hA2U]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgk_grad, MeasureTheory.ae_restrict_mem hUmeas] with x hgx hxU
    rw [Homogenization.H1Function.neg_grad]
    show vecDot (-gk.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x)) = _
    rw [hgx, hvsg x]
    by_cases hc : m₀ + k < w₂.toFun x
    · rw [Set.indicator_of_mem (show x ∈ {y | m₀ + k < w₂.toFun y} from hc),
        Set.indicator_of_mem (show x ∈ A₂ from ⟨hxU, hc⟩)]
      have hs := vecDot_matVecMul_eq_symmPart (matTranspose (a x)) (w₂.grad x)
      rw [symmPart_matTranspose] at hs
      rw [matVecMul_sub_vec, matVecMul_smul, vecDot_neg_left, vsubr, vecDot_smul_right, hs]
      ring
    · rw [Set.indicator_of_notMem (show x ∉ {y | m₀ + k < w₂.toFun y} from hc),
        Set.indicator_of_notMem (show x ∉ A₂ from fun h => hc h.2)]
      simp [vecDot_zero_left]
  have hT2split : (∫ x in U, vecDot ((-gk).grad x)
        (matVecMul (matTranspose (a x)) (vstar.grad x)) ∂volume)
      = (∫ x in A₂, vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x)) ∂volume)
        - (1 / 2 : ℝ) * ∫ x in A₂, vecDot (w₂.grad x) (matVecMul (matTranspose (a x)) p) ∂volume := by
    rw [hT2, MeasureTheory.integral_sub iE2 (iATp.const_mul _),
      MeasureTheory.integral_const_mul]
  -- RHS integral as `∫_{A₁} q·∇w₁`
  have hR : (∫ x in U, vecDot q (fk.grad x) ∂volume)
      = ∫ x in A₁, vecDot q (w₁.grad x) ∂volume := by
    rw [← setIntegral_indicator_subset hA1m hA1U]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hfk_grad, MeasureTheory.ae_restrict_mem hUmeas] with x hgx hxU
    rw [hgx]
    by_cases hc : m₀ + k < w₁.toFun x
    · rw [Set.indicator_of_mem (show x ∈ {y | m₀ + k < w₁.toFun y} from hc),
        Set.indicator_of_mem (show x ∈ A₁ from ⟨hxU, hc⟩)]
    · rw [Set.indicator_of_notMem (show x ∉ {y | m₀ + k < w₁.toFun y} from hc),
        Set.indicator_of_notMem (show x ∉ A₁ from fun h => hc h.2)]
      simp [vecDot_zero_right]
  rw [hT1split, hT2split, hR] at hkey
  -- convert the two target integrals
  have hxi1 : (∫ x in A₁, vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x) ∂volume)
      = (∫ x in A₁, vecDot q (w₁.grad x) ∂volume)
        - (1 / 2 : ℝ) * ∫ x in A₁, vecDot (w₁.grad x) (matVecMul (a x) p) ∂volume := by
    have hpt : ∀ x, vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x)
        = vecDot q (w₁.grad x) - (1 / 2 : ℝ) * vecDot (w₁.grad x) (matVecMul (a x) p) := by
      intro x
      rw [vsubl, vecDot_smul_left, vecDot_comm (matVecMul (a x) p) (w₁.grad x)]
    simp only [hpt]
    rw [MeasureTheory.integral_sub iq (iAp.const_mul _), MeasureTheory.integral_const_mul]
  have hxi2 : (∫ x in A₂, vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x) ∂volume)
      = (1 / 2 : ℝ) * ∫ x in A₂, vecDot (w₂.grad x) (matVecMul (matTranspose (a x)) p) ∂volume := by
    have hpt : ∀ x, vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x)
        = (1 / 2 : ℝ) * vecDot (w₂.grad x) (matVecMul (matTranspose (a x)) p) := by
      intro x
      rw [vecDot_smul_left, vecDot_comm (matVecMul (matTranspose (a x)) p) (w₂.grad x)]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul]
  rw [hxi1, hxi2]
  linarith [hkey]

/-! ## The squared level-energy bound -/

/-- **Squared level-energy bound.**  `E_k ≤ 2M²·|A_k|`, obtained from the identity
by the `s`-metric Young inequality (`t = 1`) and the coefficient bounds. -/
theorem levelEnergy_sq_bound {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) {a : CoeffField d} (hEll : IsEllipticFieldOn 1 Θ U a)
    {p q : Vec d} {v vstar : H1Function U}
    (hCWF : CoupledWeakForm a U q v vstar)
    {w₁ w₂ : H1Function U} (hw1meas : Measurable w₁.toFun) (hw2meas : Measurable w₂.toFun)
    (hw1g : ∀ x, w₁.grad x = v.grad x - (1 / 2 : ℝ) • p)
    (hw2g : ∀ x, w₂.grad x = -vstar.grad x + (1 / 2 : ℝ) • p)
    (hmatch : MemH10 U (fun x => w₁.toFun x - w₂.toFun x))
    (m₀ k : ℝ) :
    (∫ x in {x | x ∈ U ∧ m₀ + k < w₁.toFun x},
        vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x)) ∂volume)
      + (∫ x in {x | x ∈ U ∧ m₀ + k < w₂.toFun x},
        vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x)) ∂volume)
      ≤ 2 * (Θ * vecNormSq p + vecNormSq q)
          * ((volume {x | x ∈ U ∧ m₀ + k < w₁.toFun x}).toReal
            + (volume {x | x ∈ U ∧ m₀ + k < w₂.toFun x}).toReal) := by
  classical
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := by
    have h := measure_ne_top (volumeMeasureOn U) Set.univ
    rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter] at h
  set A₁ : Set (Vec d) := {x | x ∈ U ∧ m₀ + k < w₁.toFun x} with hA1_def
  set A₂ : Set (Vec d) := {x | x ∈ U ∧ m₀ + k < w₂.toFun x} with hA2_def
  have hA1m : MeasurableSet A₁ := hUmeas.inter (measurableSet_lt measurable_const hw1meas)
  have hA2m : MeasurableSet A₂ := hUmeas.inter (measurableSet_lt measurable_const hw2meas)
  have hA1U : A₁ ⊆ U := fun x hx => hx.1
  have hA2U : A₂ ⊆ U := fun x hx => hx.1
  set M2 : ℝ := Θ * vecNormSq p + vecNormSq q with hM2_def
  have hM2 : 0 ≤ M2 := by
    rw [hM2_def]; have := vecNormSq_nonneg p; have := vecNormSq_nonneg q; positivity
  -- L² memberships
  have hw1L2 : MemVectorL2 U w₁.grad := w₁.grad_memVectorL2
  have hw2L2 : MemVectorL2 U w₂.grad := w₂.grad_memVectorL2
  have hsw1 : MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (w₁.grad x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hw1L2
  have hsw2 : MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (w₂.grad x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hw2L2
  have hAp : MemVectorL2 U (fun x => matVecMul (a x) p) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll (memVectorL2_const p)
  have hATp : MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) p) := by
    have heq : (fun x => matVecMul (matTranspose (a x)) p)
        = fun x => matVecMul (symmPart (a x)) p - matVecMul (skewPart (a x)) p := by
      funext x; exact matVecMul_matTranspose_eq (a x) p
    rw [heq]
    exact (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll (memVectorL2_const p)).sub
      (memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll (memVectorL2_const p))
  have hξ1L2 : MemVectorL2 U (fun x => q - (1 / 2 : ℝ) • matVecMul (a x) p) :=
    (memVectorL2_const q).sub (hAp.const_smul (1 / 2 : ℝ))
  have hξ2L2 : MemVectorL2 U (fun x => (1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) :=
    hATp.const_smul (1 / 2 : ℝ)
  have hsinv1 : MemVectorL2 U
      (fun x => matVecMul ((symmPart (a x))⁻¹) (q - (1 / 2 : ℝ) • matVecMul (a x) p)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hξ1L2
  have hsinv2 : MemVectorL2 U (fun x =>
      matVecMul ((symmPart (a x))⁻¹) ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hξ2L2
  -- IntegrableOn on the two level sets
  have iJ1 : MeasureTheory.IntegrableOn
      (fun x => vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x)) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hξ1L2 hw1L2).mono_set hA1U
  have iJ2 : MeasureTheory.IntegrableOn
      (fun x => vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x)) A₂ :=
    (integrableOn_vecDot_of_memVectorL2 hξ2L2 hw2L2).mono_set hA2U
  have iE1 : MeasureTheory.IntegrableOn
      (fun x => vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x))) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hw1L2 hsw1).mono_set hA1U
  have iE2 : MeasureTheory.IntegrableOn
      (fun x => vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x))) A₂ :=
    (integrableOn_vecDot_of_memVectorL2 hw2L2 hsw2).mono_set hA2U
  have iK1 : MeasureTheory.IntegrableOn (fun x => vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p)
      (matVecMul ((symmPart (a x))⁻¹) (q - (1 / 2 : ℝ) • matVecMul (a x) p))) A₁ :=
    (integrableOn_vecDot_of_memVectorL2 hξ1L2 hsinv1).mono_set hA1U
  have iK2 : MeasureTheory.IntegrableOn (fun x => vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p)
      (matVecMul ((symmPart (a x))⁻¹) ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p))) A₂ :=
    (integrableOn_vecDot_of_memVectorL2 hξ2L2 hsinv2).mono_set hA2U
  set E1 : ℝ := ∫ x in A₁, vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x)) ∂volume
    with hE1_def
  set E2 : ℝ := ∫ x in A₂, vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x)) ∂volume
    with hE2_def
  set J1 : ℝ := ∫ x in A₁, vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x) ∂volume
    with hJ1_def
  set J2 : ℝ := ∫ x in A₂, vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x) ∂volume
    with hJ2_def
  set K1 : ℝ := ∫ x in A₁, vecDot (q - (1 / 2 : ℝ) • matVecMul (a x) p)
    (matVecMul ((symmPart (a x))⁻¹) (q - (1 / 2 : ℝ) • matVecMul (a x) p)) ∂volume with hK1_def
  set K2 : ℝ := ∫ x in A₂, vecDot ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p)
    (matVecMul ((symmPart (a x))⁻¹) ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p)) ∂volume
    with hK2_def
  -- identity `E1 + E2 = J1 + J2`
  have hid : E1 + E2 = J1 + J2 :=
    levelEnergy_identity hU hEll hCWF hw1meas hw2meas hw1g hw2g hmatch m₀ k
  -- Young: `J1 ≤ ½K1 + ½E1`, `J2 ≤ ½K2 + ½E2`
  have hyoung1 : J1 ≤ (2 * (1 : ℝ))⁻¹ * K1 + (1 / 2 : ℝ) * E1 := by
    rw [hJ1_def, hK1_def, hE1_def, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add
        (iK1.const_mul _) (iE1.const_mul _)]
    refine MeasureTheory.setIntegral_mono_ae_restrict iJ1
      ((iK1.const_mul _).add (iE1.const_mul _)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hA1m] with x hx
    exact symmForm_young (hEll.2 x hx.1) one_pos (q - (1 / 2 : ℝ) • matVecMul (a x) p) (w₁.grad x)
  have hyoung2 : J2 ≤ (2 * (1 : ℝ))⁻¹ * K2 + (1 / 2 : ℝ) * E2 := by
    rw [hJ2_def, hK2_def, hE2_def, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add
        (iK2.const_mul _) (iE2.const_mul _)]
    refine MeasureTheory.setIntegral_mono_ae_restrict iJ2
      ((iK2.const_mul _).add (iE2.const_mul _)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hA2m] with x hx
    exact symmForm_young (hEll.2 x hx.1) one_pos
      ((1 / 2 : ℝ) • matVecMul (matTranspose (a x)) p) (w₂.grad x)
  -- coefficient bounds `K1 ≤ 2M²·vol A₁`, `K2 ≤ M²·vol A₂`
  have hvol1 : (0 : ℝ) ≤ (volume A₁).toReal := ENNReal.toReal_nonneg
  have hvol2 : (0 : ℝ) ≤ (volume A₂).toReal := ENNReal.toReal_nonneg
  have hK1bd : K1 ≤ 2 * M2 * (volume A₁).toReal := by
    have hle : K1 ≤ ∫ _ in A₁, (2 * M2) ∂volume := by
      refine MeasureTheory.setIntegral_mono_ae_restrict iK1
        (MeasureTheory.integrableOn_const
          (lt_of_le_of_lt (measure_mono hA1U) hUtop.lt_top).ne) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hA1m] with x hx
      simpa [hM2_def] using symmPartInv_bulkV_le (hEll.2 x hx.1) p q
    rwa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm] at hle
  have hK2bd : K2 ≤ M2 * (volume A₂).toReal := by
    have hle : K2 ≤ ∫ _ in A₂, M2 ∂volume := by
      refine MeasureTheory.setIntegral_mono_ae_restrict iK2
        (MeasureTheory.integrableOn_const
          (lt_of_le_of_lt (measure_mono hA2U) hUtop.lt_top).ne) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hA2m] with x hx
      simpa [hM2_def] using symmPartInv_bulkVstar_le (hEll.2 x hx.1) p q
    rwa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm] at hle
  have hc : (2 * (1 : ℝ))⁻¹ = 1 / 2 := by norm_num
  rw [hc] at hyoung1 hyoung2
  nlinarith [hid, hyoung1, hyoung2, hK1bd, hK2bd, hM2, hvol1, hvol2,
    mul_nonneg hM2 hvol2]

/-! ## From the squared bound to the `√`-shaped level-energy estimate -/

/-- **Coordinate-norm packaging.**  Given `E_k ≤ 2M²·|A_k|`, the sum of the
coordinate `L²` norms of the truncated gradients is bounded by `2√d·M·√|A_k|`,
via `s ≥ 1` and a Cauchy–Schwarz on the `2d` coordinate norms. -/
theorem sumCoordNorm_le {U : Set (Vec d)}
    {Θ : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn 1 Θ U a)
    (w₁ w₂ : H1Function U) {A₁ A₂ : Set (Vec d)}
    (hA1m : MeasurableSet A₁) (hA2m : MeasurableSet A₂) (hA1U : A₁ ⊆ U) (hA2U : A₂ ⊆ U)
    {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hEbound : (∫ x in A₁, vecDot (w₁.grad x) (matVecMul (symmPart (a x)) (w₁.grad x)) ∂volume)
        + (∫ x in A₂, vecDot (w₂.grad x) (matVecMul (symmPart (a x)) (w₂.grad x)) ∂volume)
        ≤ 2 * M2 * ((volume A₁).toReal + (volume A₂).toReal)) :
    (∑ i : Fin d, (eLpNorm (A₁.indicator (fun x => w₁.grad x i)) 2 (volumeMeasureOn U)).toReal)
      + (∑ i : Fin d, (eLpNorm (A₂.indicator (fun x => w₂.grad x i)) 2 (volumeMeasureOn U)).toReal)
      ≤ 2 * Real.sqrt d * Real.sqrt M2
          * Real.sqrt ((volume A₁).toReal + (volume A₂).toReal) := by
  classical
  -- `∑ᵢ ‖1_A ∂ᵢw‖² ≤ ∫_A ∇w·s∇w`
  have key : ∀ (A : Set (Vec d)) (w : H1Function U), MeasurableSet A → A ⊆ U →
      (∑ i : Fin d, ((eLpNorm (A.indicator (fun x => w.grad x i)) 2 (volumeMeasureOn U)).toReal) ^ 2)
        ≤ ∫ x in A, vecDot (w.grad x) (matVecMul (symmPart (a x)) (w.grad x)) ∂volume := by
    intro A w hAm hAU
    have hsq : ∀ i : Fin d,
        ((eLpNorm (A.indicator (fun x => w.grad x i)) 2 (volumeMeasureOn U)).toReal) ^ 2
          = ∫ x in A, (w.grad x i) ^ 2 ∂volume := by
      intro i
      rw [toReal_eLpNorm_two_sq_eq_integral_sq ((w.gradMemL2 i).indicator hAm)]
      have hind : (fun x => (A.indicator (fun y => w.grad y i) x) ^ 2)
          = A.indicator (fun x => (w.grad x i) ^ 2) := by
        funext x
        by_cases h : x ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      show ∫ x, (A.indicator (fun y => w.grad y i) x) ^ 2 ∂(volumeMeasureOn U) = _
      rw [hind]
      exact setIntegral_indicator_subset hAm hAU (fun x => (w.grad x i) ^ 2)
    have hsum : (∑ i : Fin d,
          ((eLpNorm (A.indicator (fun x => w.grad x i)) 2 (volumeMeasureOn U)).toReal) ^ 2)
        = ∫ x in A, vecNormSq (w.grad x) ∂volume := by
      rw [Finset.sum_congr rfl (fun i _ => hsq i), ← MeasureTheory.integral_finsetSum]
      · refine MeasureTheory.setIntegral_congr_fun hAm ?_
        intro x hx
        simp only [vecNormSq, vecDot, pow_two]
      · intro i _
        have hint : MeasureTheory.IntegrableOn
            (fun x => w.grad x i * w.grad x i) U volume :=
          (w.gradMemL2 i).integrable_mul (w.gradMemL2 i)
        refine (hint.mono_set hAU).congr ?_
        filter_upwards with x; rw [pow_two]
    rw [hsum]
    refine MeasureTheory.setIntegral_mono_ae_restrict
      ((integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2 w.grad_memVectorL2).mono_set hAU)
      ((integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll w.grad_memVectorL2)).mono_set hAU)
      ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hAm] with x hx
    have hle := (matLoewnerLE_iff (1 : Mat d) (symmPart (a x))).1
      (one_matLoewnerLE_symmPart_of_isThetaElliptic (hEll.2 x (hAU hx))) (w.grad x)
    rw [matVecMul_one] at hle
    exact hle
  -- the two squared-norm sums
  have ha2E := key A₁ w₁ hA1m hA1U
  have hb2E := key A₂ w₂ hA2m hA2U
  set Sa : ℝ := ∑ i : Fin d,
    (eLpNorm (A₁.indicator (fun x => w₁.grad x i)) 2 (volumeMeasureOn U)).toReal with hSa_def
  set Sb : ℝ := ∑ i : Fin d,
    (eLpNorm (A₂.indicator (fun x => w₂.grad x i)) 2 (volumeMeasureOn U)).toReal with hSb_def
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hSa2 : Sa ^ 2 ≤ (d : ℝ) *
      (∑ i : Fin d, ((eLpNorm (A₁.indicator (fun x => w₁.grad x i)) 2 (volumeMeasureOn U)).toReal) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (eLpNorm (A₁.indicator (fun x => w₁.grad x i)) 2 (volumeMeasureOn U)).toReal)
    simpa [hSa_def, Finset.card_univ, Fintype.card_fin] using h
  have hSb2 : Sb ^ 2 ≤ (d : ℝ) *
      (∑ i : Fin d, ((eLpNorm (A₂.indicator (fun x => w₂.grad x i)) 2 (volumeMeasureOn U)).toReal) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (eLpNorm (A₂.indicator (fun x => w₂.grad x i)) 2 (volumeMeasureOn U)).toReal)
    simpa [hSb_def, Finset.card_univ, Fintype.card_fin] using h
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hV : (0 : ℝ) ≤ (volume A₁).toReal + (volume A₂).toReal := by positivity
  have hcomb : (Sa + Sb) ^ 2 ≤ 4 * (d : ℝ) * M2 * ((volume A₁).toReal + (volume A₂).toReal) := by
    nlinarith [hSa2, hSb2, ha2E, hb2E, hEbound, sq_nonneg (Sa - Sb), hd0, hM2, hV,
      mul_le_mul_of_nonneg_left hEbound hd0]
  have hstep : Sa + Sb ≤ Real.sqrt (4 * (d : ℝ) * M2 * ((volume A₁).toReal + (volume A₂).toReal)) := by
    rw [show Sa + Sb = Real.sqrt ((Sa + Sb) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hcomb
  refine le_trans hstep (le_of_eq ?_)
  rw [show (4 : ℝ) * (d : ℝ) * M2 * ((volume A₁).toReal + (volume A₂).toReal)
      = (2 : ℝ) ^ 2 * ((d : ℝ) * (M2 * ((volume A₁).toReal + (volume A₂).toReal))) from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
    Real.sqrt_mul hd0, Real.sqrt_mul hM2]
  ring

/-! ## Part C deliverable — the coupled level-energy estimate -/

/-- **Coupled level-energy estimate.**  From the coupled weak form, the measurable representatives
`w₁ ≈ v − ½p·x`, `w₂ ≈ −v* + ½p·x` share a trace and satisfy the De Giorgi core's
level-energy hypothesis with `E₀ = 2√d·√(Θ|p|²+|q|²)`. -/
theorem coupled_levelEnergy {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) {a : CoeffField d} (hEll : IsEllipticFieldOn 1 Θ U a)
    {p q : Vec d} {v vstar : H1Function U}
    (hCWF : CoupledWeakForm a U q v vstar)
    (htrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot p x)) :
    ∃ (w₁ w₂ : H1Function U),
      Measurable w₁.toFun ∧ Measurable w₂.toFun ∧
      (w₁.toFun =ᵐ[volume.restrict U] fun x => v.toFun x - (1 / 2 : ℝ) * vecDot p x) ∧
      (w₂.toFun =ᵐ[volume.restrict U] fun x => -vstar.toFun x + (1 / 2 : ℝ) * vecDot p x) ∧
      MemH10 U (fun x => w₁.toFun x - w₂.toFun x) ∧
      ∀ (m₀ k : ℝ), 0 ≤ k →
        (∑ i : Fin d, (eLpNorm ({x | x ∈ U ∧ m₀ + k < w₁.toFun x}.indicator
            (fun x => w₁.grad x i)) 2 (volumeMeasureOn U)).toReal)
          + (∑ i : Fin d, (eLpNorm ({x | x ∈ U ∧ m₀ + k < w₂.toFun x}.indicator
            (fun x => w₂.grad x i)) 2 (volumeMeasureOn U)).toReal)
          ≤ (2 * Real.sqrt d * Real.sqrt (Θ * vecNormSq p + vecNormSq q)) * Real.sqrt
              ((volume {x | x ∈ U ∧ m₀ + k < w₁.toFun x}).toReal
                + (volume {x | x ∈ U ∧ m₀ + k < w₂.toFun x}).toReal) := by
  classical
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hUm : MeasurableSet U := hU.isOpen.measurableSet
  obtain ⟨w₁, hw1meas, hw1ae, hw1grad⟩ :=
    exists_measurableRep (v - affineHalfOn hUm hU.isBoundedDomain p)
  obtain ⟨w₂, hw2meas, hw2ae, hw2grad⟩ :=
    exists_measurableRep (-vstar + affineHalfOn hUm hU.isBoundedDomain p)
  have hw1g : ∀ x, w₁.grad x = v.grad x - (1 / 2 : ℝ) • p := by
    intro x; rw [hw1grad]
    simp only [Homogenization.H1Function.sub_grad, affineHalfOn_grad]
  have hw2g : ∀ x, w₂.grad x = -vstar.grad x + (1 / 2 : ℝ) • p := by
    intro x; rw [hw2grad]
    simp only [Homogenization.H1Function.add_grad, Homogenization.H1Function.neg_grad,
      affineHalfOn_grad]
  have hw1ae' : w₁.toFun =ᵐ[volume.restrict U] fun x => v.toFun x - (1 / 2 : ℝ) * vecDot p x := by
    refine hw1ae.trans (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Homogenization.H1Function.sub_toFun, affineHalfOn_toFun]
  have hw2ae' : w₂.toFun =ᵐ[volume.restrict U] fun x => -vstar.toFun x + (1 / 2 : ℝ) * vecDot p x := by
    refine hw2ae.trans (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Homogenization.H1Function.add_toFun, Homogenization.H1Function.neg_toFun,
      affineHalfOn_toFun]
  obtain ⟨W, hW⟩ := htrace
  have hmatch : MemH10 U (fun x => w₁.toFun x - w₂.toFun x) := by
    have hae : (w₁ - w₂).toFun =ᵐ[volume.restrict U] W.toH1Function.toFun := by
      filter_upwards [hw1ae', hw2ae'] with x hx1 hx2
      rw [Homogenization.H1Function.sub_toFun]
      show w₁.toFun x - w₂.toFun x = W.toH1Function.toFun x
      rw [hx1, hx2, congrFun hW x]; ring
    have hmem := memH10_of_ae_eq_h10 hU (w₁ - w₂) W hae
    rwa [Homogenization.H1Function.sub_toFun] at hmem
  refine ⟨w₁, w₂, hw1meas, hw2meas, hw1ae', hw2ae', hmatch, ?_⟩
  intro m₀ k _hk
  have hEbound := levelEnergy_sq_bound hU hΘ hEll hCWF hw1meas hw2meas hw1g hw2g hmatch m₀ k
  exact sumCoordNorm_le hEll w₁ w₂
    (hUm.inter (measurableSet_lt measurable_const hw1meas))
    (hUm.inter (measurableSet_lt measurable_const hw2meas))
    (fun x hx => hx.1) (fun x hx => hx.1)
    (add_nonneg (mul_nonneg hΘ (vecNormSq_nonneg p)) (vecNormSq_nonneg q)) hEbound

end

end Homogenization
