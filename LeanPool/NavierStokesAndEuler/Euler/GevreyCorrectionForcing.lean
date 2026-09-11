/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.WeightedForcingAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureEnergy
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricComparison
public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordLevel
import LeanPool.NavierStokesAndEuler.Euler.SobolevTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.HeatAllOrders
public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.FunctionalVelocity
public import LeanPool.NavierStokesAndEuler.Euler.H6TransportSource
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
public import LeanPool.NavierStokesAndEuler.Euler.ExternalTransportCommutator
import LeanPool.NavierStokesAndEuler.Euler.LowerTransportSource

/-! The actual differentiated correction forcing and its cutoff-independent nonlinear bound. -/

section

/-! The genuine base transport commutator on finite Sobolev fields, with an H⁶-only bound. -/

section

/-! The fixed-base transport commutator estimate with only H⁶ velocity norms. -/

@[expose] public section

noncomputable section

namespace EulerBaseTransportL2

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev EulerMetricTransport
    EulerTransportDerivatives
  EulerH6Nonlinear EulerVectorCylinder EulerBaseTransportCommutator EulerExternalTransportCommutator
  EulerFunctionalVelocity EulerMixedH5Product
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The base transport constant depends only on the fixed Sobolev index and cylinder period. -/
def baseTransportConstant : ℝ := (4*63*5460*1365 : ℝ)*mixedConstant period

theorem baseTransportConstant_nonneg : 0 ≤ baseTransportConstant period :=
  mul_nonneg (by norm_num) (mixedConstant_nonneg period)

/-- The gradient H⁵ sum is controlled by the actual H⁶ norm with a fixed combinatorial factor. -/
theorem gradientFive_le_six {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F) : gradientFiveNorm period f ≤ 5460*liftSobolevNorm period 6 f := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => derivative_H5_le_H6
      period i f)
  exact h.trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)

/-- Summing actual L² fields respects the sum of their finite L² norms. -/
theorem fieldL2_sum_le {ι F : Type*} [NormedAddCommGroup F] (S : Finset ι)
    (f : ι → LiftDomain period → F) (hf : ∀ i ∈ S, MemLp (f i) 2 (liftMeasure period)) :
    (eLpNorm (∑ i ∈ S, f i) 2 (liftMeasure period)).toReal ≤
      ∑ i ∈ S, (eLpNorm (f i) 2 (liftMeasure period)).toReal := by
  have he := eLpNorm_sum_le (fun i hi => (hf i hi).aestronglyMeasurable) (by
      norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin : (∑ i ∈ S, eLpNorm (f i) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i hi => (hf i hi).eLpNorm_ne_top)
  have h := ENNReal.toReal_mono hfin he
  rw [ENNReal.toReal_sum (fun i hi => (hf i hi).eLpNorm_ne_top)] at h
  exact h

/-- The literal transport commutator through six base derivatives is in L² and bounded using only
the two H⁶ norms. -/
theorem transport_base_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a g) 2 (liftMeasure
        period)) :
    MemLp (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period) ∧
    (eLpNorm (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period)).toReal ≤
      baseTransportConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  let h := fun i : Fin 4 => scalarCommutator period w (L i ∘ f) (fieldDerivative period
      (standardDirection i) g)
  have hs (i : Fin 4) := scalarCommutator_bound period hn w (L i ∘ f) (fieldDerivative period
      (standardDirection i) g)
    (postcomp_smooth period (L i) f hf) (fieldDerivative_smooth period _ g hg)
    (fun j hj a => postcomp_word_memLp period hj (L i) f hf (fun r _ b => hfL r b) a)
    (fun j _ a => derivative_all_memLp period g hgL i j a)
  have hgrad (i : Fin 4) : gradientFiveNorm period (L i ∘ f) ≤ 5460*liftSobolevNorm period 6 f :=
    (gradientFive_le_six period (L i ∘ f)).trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 6 (L i) (hL i) f hf (fun j _ a => hfL j a)) (by norm_num))
  have hp : (2 : ℝ)^n-1 ≤ 63 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h
    linarith
  have hcoef := mul_le_mul_of_nonneg_right hp (mixedConstant_nonneg period)
  have hb (i : Fin 4) : (eLpNorm (h i) 2 (liftMeasure period)).toReal ≤
      (63*5460*1365*mixedConstant period)*liftSobolevNorm period 6 f*liftSobolevNorm period 6 g :=
          by
    have h1 := mul_le_mul hcoef (hgrad i) (gradientFiveNorm_nonneg period (L i ∘ f))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 63) (mixedConstant_nonneg period))
    have h2 := mul_le_mul h1 (derivative_H5_le_H6 period i g) (liftSobolevNorm_nonneg period 5 _)
      (mul_nonneg (mul_nonneg (by norm_num) (mixedConstant_nonneg period))
        (mul_nonneg (by norm_num) (liftSobolevNorm_nonneg period 6 f)))
    exact (hs i).2.trans (h2.trans_eq (by ring))
  have heq : transportCommutator period w (velocityMap L ∘ f) g = ∑ i : Fin 4, h i := by
    rw [transportCommutator_eq_sum period w (velocityMap L ∘ f) g (postcomp_smooth period
        (velocityMap L) f hf) hg]
    rfl
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => (hs i).1), ?_⟩
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => hb i)
  exact (fieldL2_sum_le period Finset.univ h (fun i _ => (hs i).1)).trans
    (hsum.trans_eq (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; unfold
            baseTransportConstant; ring))

end EulerBaseTransportL2

end
end

end

section

/-! Genuine transport as a bounded bilinear map from Sobolev velocity and an H¹ transported field
into L². -/

@[expose] public section

noncomputable section

namespace EulerTransportL2Bilinear

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerTransportDerivatives EulerSobolevL2Product EulerSobolevTransport
  EulerFunctionalVelocity EulerH6Nonlinear EulerSobolevMetricTransport
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual product of a bounded Sobolev velocity with the genuine first derivatives of an H¹
field. -/
def transportL2Bilinear {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ) :
    SobolevSpace period q →L[ℝ] SobolevSpace period 1 →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, (scalarProductBilinear period hq (L i)).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period q)) ((valueOperator period 0).comp
        (derivativeOperator period 0 i))

/-- Transport is the sum of its four literal scalar-times-derivative L² products. -/
theorem transportL2Bilinear_apply {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) :
    transportL2Bilinear period hq L u e = ∑ i : Fin 4,
      scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e)) := by
  simp only [transportL2Bilinear, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, scalarProductBilinear_apply]
  rfl

/-- On the actual lifted velocity coefficients, this is exactly the operator used in metric
transport cancellation. -/
theorem transportL2Bilinear_eq_metric {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) :
    transportL2Bilinear period hq (velocityComponents κ m) u e = transportOperator period hq κ m u
        e := by
  rw [transportL2Bilinear_apply, transportOperator_apply]

/-- The bilinear L² transport agrees almost everywhere with the actual classical directional
transport. -/
theorem transportL2Bilinear_ae {q : ℕ} (hq : 3 ≤ q) (L : Fin 4 → Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (e : SobolevSpace period 1) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (he : (value period e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (transportL2Bilinear period hq L u e : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportField period 3 (velocityMap L ∘ f) g := by
  rw [transportL2Bilinear_apply]
  have hi (i : Fin 4) :
      (scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e)) :
          LiftDomain period → Vector3) =ᵐ[liftMeasure period]
        (fun x => L i (f x) • fieldDerivative period (standardDirection i) g x) := by
    have hd := EulerStrongSmoothJet.translation_derivative_ae period (standardDirection i)
      (value period e) (value period (derivativeOperator period 0 i e)) g he hg
      (derivativeOperator_hasDerivAt period i e)
    filter_upwards [scalarProduct_ae period hq (L i) u (value period (derivativeOperator period 0 i
        e)), hu, hd]
      with x hx hux hdx
    exact hx.trans (by rw [hux,hdx])
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 =>
    scalarProduct period hq (L i) u (value period (derivativeOperator period 0 i e))),
        ae_all_iff.mpr hi]
    with x hx hall
  simp only [Finset.sum_apply] at hx
  change _ = ∑ i : Fin 4, L i (f x) • fieldDerivative period (standardDirection i) g x
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hall i))

end EulerTransportL2Bilinear

end
end

end

section

/-! Transfer of continuous real inequalities from actual smooth H∞ representatives to finite Sobolev
fields. -/

@[expose] public section

noncomputable section

namespace EulerSmoothInequalityTransfer

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerSobolevHeat
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every continuous inequality proved for actual smooth H∞ representatives passes to the genuine
finite Sobolev space. -/
theorem binary_le_of_smooth {q : ℕ}
    (F G : SobolevSpace period q × SobolevSpace period q → ℝ) (hF : Continuous F) (hG : Continuous
        G)
    (hbound : ∀ (u v : SobolevSpace period q) (f g : LiftDomain period → Vector3),
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f →
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g →
      (∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) →
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) →
      (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
          →
      (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period))
          →
      F (u,v) ≤ G (u,v)) (u v : SobolevSpace period q) : F (u,v) ≤ G (u,v) := by
  let U : ℕ → SobolevSpace period q := fun n => restrictOperator period (by
      omega : q ≤ q+3) (smoothApprox period q n u)
  let V : ℕ → SobolevSpace period q := fun n => restrictOperator period (by
      omega : q ≤ q+3) (smoothApprox period q n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hp : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hleft : Filter.Tendsto (fun n => F (U n,V n)) Filter.atTop (𝓝 (F (u,v))) := (hF.tendsto
      (u,v)).comp hp
  have hright : Filter.Tendsto (fun n => G (U n,V n)) Filter.atTop (𝓝 (G (u,v))) := (hG.tendsto
      (u,v)).comp hp
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  exact hbound (U n) (V n) f g hf hg hfs hgs hfL hgL

end EulerSmoothInequalityTransfer

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevBaseCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerTransportDerivatives EulerSobolevL2Product EulerSobolevTransport
  EulerFunctionalVelocity EulerH6Nonlinear EulerSobolevTransportCommutator EulerSobolevWordLevel
  EulerTransportL2Bilinear EulerBaseTransportL2 EulerSmoothInequalityTransfer
      EulerExternalTransportCommutator
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance baseCommGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance baseCommSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual base derivative commutator, evaluated in L² on its genuine H⁷ domain. -/
def baseCommutator (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period 7 →L[ℝ] SobolevSpace period 7 →L[ℝ] LiftL2 period :=
  ((ContinuousLinearMap.compL ℝ (SobolevSpace period 7) (SobolevSpace period 6) (LiftL2 period)
    ((valueOperator period 0).comp (wordAtLevel period 0 r w (by omega : r+0 ≤ 6)))).comp
      (transportBilinear period (by norm_num : 6 ≤ 6) L hL)) -
  (transportL2Bilinear period (by norm_num : 3 ≤ 7) L).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period 7)) (wordAtLevel period 1 r w (by
        omega : r+1 ≤ 7))

/-- The actual operands of the finite-Sobolev base commutator. -/
theorem baseCommutator_apply (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) :
    baseCommutator period r hr w L hL u v =
      value period (wordAtLevel period 0 r w (by
          omega : r+0 ≤ 6) (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v)) -
        transportL2Bilinear period (by
            norm_num : 3 ≤ 7) L u (wordAtLevel period 1 r w (by omega : r+1 ≤ 7) v) := rfl

/-- Its actual L² representative is the literal classical base derivative commutator. -/
theorem baseCommutator_ae (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (baseCommutator period r hr w L hL u v : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportCommutator period w (velocityMap L ∘ f) g := by
  let b := velocityMap L ∘ f
  have hb := EulerVectorCylinder.postcomp_smooth period (velocityMap L) f hf
  have ht := transport_ae_velocityMap period (by norm_num : 6 ≤ 6) L hL u v f g hu hv hg
  have hfirst := wordAtLevel_ae period 0 r w (by omega : r+0 ≤ 6)
    (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v) (transportField period 3 b g) ht
    (transportField_smooth period b g hb hg)
  have hw := wordAtLevel_ae period 1 r w (by omega : r+1 ≤ 7) v g hv hg
  have hsecond := transportL2Bilinear_ae period (by norm_num : 3 ≤ 7) L u
    (wordAtLevel period 1 r w (by omega) v) f (iteratedFieldDerivative period w g) hu hw
    (iteratedFieldDerivative_smooth period w g hg)
  rw [baseCommutator_apply]
  filter_upwards [Lp.coeFn_sub
    (value period (wordAtLevel period 0 r w (by
        omega) (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v)))
    (transportL2Bilinear period (by
        norm_num : 3 ≤ 7) L u (wordAtLevel period 1 r w (by omega) v)), hfirst,hsecond]
    with x hx h1 h2
  simp only [Pi.sub_apply] at hx
  exact hx.trans (by rw [h1,h2]; rfl)

/-- On actual smooth representatives, the base commutator has the H⁶-only norm bound. -/
theorem baseCommutator_smooth_bound (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a g) 2 (liftMeasure
        period)) :
    ‖baseCommutator period r hr w L hL u v‖ ≤ baseTransportConstant period *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) u) *
        sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) v) := by
  have heq : ‖baseCommutator period r hr w L hL u v‖ =
      (eLpNorm (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period)).toReal
          := by
    simpa only [Lp.norm_def] using congrArg ENNReal.toReal
      (eLpNorm_congr_ae (p := (2 : ℝ≥0∞)) (baseCommutator_ae period r hr w L hL u v f g hu hv hf
          hg))
  have h := (transport_base_L2 period hr w L hL f g hf hg hfL hgL).2
  rw [heq]
  conv_rhs => rw [sumNorm_eq_classical period (restrictOperator period (by
      norm_num : 6 ≤ 7) u) f hu hf,
    sumNorm_eq_classical period (restrictOperator period (by norm_num : 6 ≤ 7) v) g hv hg]
  exact h

/-- The genuine finite-Sobolev base commutator satisfies the same H⁶-only estimate, with no
smoothness hypothesis. -/
theorem baseCommutator_bound (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) :
    ‖baseCommutator period r hr w L hL u v‖ ≤ baseTransportConstant period *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) u) *
        sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) v) := by
  have hS : Continuous (fun u : SobolevSpace period 7 => sumNorm period (restrictOperator period (by
      norm_num : 6 ≤ 7) u)) :=
    (continuous_sumNorm period 6).comp (restrictOperator period (by norm_num : 6 ≤ 7)).continuous
  exact binary_le_of_smooth period
    (fun p => ‖baseCommutator period r hr w L hL p.1 p.2‖)
    (fun p => baseTransportConstant period * sumNorm period (restrictOperator period (by
        norm_num : 6 ≤ 7) p.1) *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) p.2))
    (baseCommutator period r hr w L hL).continuous₂.norm
    (((hS.comp continuous_fst).const_mul (baseTransportConstant period)).mul (hS.comp
        continuous_snd))
    (fun a b f g ha hb hf hg hfL hgL => baseCommutator_smooth_bound period r hr w L hL a b f g ha
        hb hf hg hfL hgL) u v

end EulerSobolevBaseCommutator

end
end

end

section

/-! Summation of the actual base transport commutators with no external-cutoff constant. -/

@[expose] public section

noncomputable section

namespace EulerGevreyBaseTransport

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators EulerBaseWordMetric
      EulerFiniteMetricEnergy
  EulerWeightedCylinderEnergy EulerGevreyMetricComparison EulerSobolevWordLevel
      EulerSobolevBaseCommutator
  EulerBaseTransportL2

variable (period : ℝ) [Fact (0 < period)]

/-- Restriction commutes with taking an actual derivative word at a lower Sobolev level. -/
theorem restrict_wordAtLevel {s p q n : ℕ} (hq : q ≤ p) (w : Fin n → Fin 4) (hp : n + p ≤ s)
    (u : SobolevSpace period s) :
    restrictOperator period hq (wordAtLevel period p n w hp u) = wordAtLevel period q n w (by
        omega) u := by
  apply value_injective period
  rw [value_restrictOperator, wordAtLevel_value, wordAtLevel_value]

/-- The exact base derivative sum is contained in every truncated actual Gevrey norm. -/
theorem sumNorm_restrict_le_weighted {s q : ℕ} (hq : q ≤ s) (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (u : SobolevSpace period s) :
    sumNorm period (restrictOperator period hq u) ≤ weightedNorm period q N ρ u := by
  have he : sumNorm period (restrictOperator period hq u) = blockNorm period (toJet period u) q 0
      := by
    rw [blockNorm_zero_eq_size (toJet period u) hq]
    rw [sumNorm_eq_jet, ← sobolevSize_eq period (toJet period (restrictOperator period hq u)),
        value_restrictOperator]
  rw [he]
  have hsum := Finset.single_le_sum (s := Finset.range (N+1))
    (fun n _ => mul_nonneg (weight_pos hρ n).le (show 0 ≤ blockNorm period (toJet period u) q n
        from blockNorm_nonneg _))
    (show 0 ∈ Finset.range (N+1) by simp)
  simpa [weight, weightedNorm] using hsum

/-- Exact external-word expansion of the actual Gevrey Sobolev sum. -/
theorem weighted_word_sums {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (u : SobolevSpace period s) :
    (∑ I : ExternalWord N, weight ρ I.1.val * sumNorm period
      (wordAtLevel period q I.1.val I.2 (by
          have := I.1.isLt; omega) u)) = weightedNorm period q N ρ u := by
  rw [Fintype.sum_sigma, weightedNorm, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [blockNorm_baseWords period u (by have := n.isLt; omega : n.val+q ≤ s), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [sumNorm_wordAtLevel]

/-- The literal base transport forcing at every external and base derivative word. -/
def baseTransportForcing {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) : ExternalWord N → BaseWord 6 → LiftL2 period := fun I a =>
  baseCommutator period a.1.val (by have := a.1.isLt; omega) a.2 L hL
    (restrictOperator period (by omega : 7 ≤ s+1) u)
    (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+7 ≤ s+1) v)

/-- Each base-word forcing family is controlled by the fixed H⁶ norms, with the fixed word-count
factor 5461. -/
theorem baseTransportForcing_family_bound {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (I : ExternalWord N) :
    familyNorm (baseTransportForcing period N hN L hL u v I) ≤
      (5461*baseTransportConstant period) * sumNorm period (restrictOperator period (by
          omega : 6 ≤ s+1) u) *
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by
            have := I.1.isLt; omega : I.1.val+6 ≤ s+1) v) := by
  have hb (a : BaseWord 6) : ‖baseTransportForcing period N hN L hL u v I a‖ ≤
      baseTransportConstant period * sumNorm period (restrictOperator period (by
          omega : 6 ≤ s+1) u) *
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by
            have := I.1.isLt; omega : I.1.val+6 ≤ s+1) v) := by
    have h := baseCommutator_bound period a.1.val (by have := a.1.isLt; omega) a.2 L hL
      (restrictOperator period (by omega : 7 ≤ s+1) u)
      (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+7 ≤ s+1) v)
    rw [restrictOperator_comp, restrict_wordAtLevel] at h
    exact h
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (BaseWord 6))) (fun a _ => hb a)
  exact (familyNorm_le_sum_norm _).trans (hsum.trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, card_baseWord_six, nsmul_eq_mul]; ring))

/-- The actual weighted base transport forcing has no external derivative loss or cutoff-dependent
coefficient. -/
theorem baseTransportForcing_weighted_bound {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (baseTransportForcing period N hN L hL
        u v) ≤
      (5461*baseTransportConstant period)*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v
          := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ExternalWord N))) (fun I _ =>
    mul_le_mul_of_nonneg_left (baseTransportForcing_family_bound period N hN L hL u v I)
        (weight_pos hρ I.1.val).le)
  have he : (∑ I : ExternalWord N, weight ρ I.1.val *
      ((5461*baseTransportConstant period)*sumNorm period (restrictOperator period (by
          omega : 6 ≤ s+1) u) *
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) v))) =
      (5461*baseTransportConstant period)*sumNorm period (restrictOperator period (by
          omega : 6 ≤ s+1) u)*weightedNorm period 6 N ρ v := by
    rw [← weighted_word_sums period 6 N (by omega : N+6 ≤ s+1) ρ v, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun I _ => by ring)
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sumNorm_restrict_le_weighted period (by omega : 6 ≤ s+1) N ρ hρ u)
    (mul_nonneg (by
        norm_num) (baseTransportConstant_nonneg period))) (weightedNorm_nonneg period 6 N ρ hρ v))

end EulerGevreyBaseTransport

end
end

end

section

/-! Literal differentiated forcing arrays and their actual finite Gevrey norms. -/

@[expose] public section

noncomputable section

namespace EulerGevreyForcingComponents

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
      EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
      EulerBasePressureCommutator
  EulerGevreyBaseTransport

variable (period : ℝ) [Fact (0 < period)]

/-- A finite family of actual base-word derivatives is controlled by its genuine derivative-sum
norm. -/
theorem forcing_le_jetSum {ι : Type*} [Fintype ι] (order : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ι → LiftL2 period) (J : ∀ i, EulerSpatialSobolevInverse.SpatialJet period
        standardDirection 6 (f i)) :
    weightedForcingSum ρ order (fun i => baseWordValues period (J i)) ≤
      ∑ i, weight ρ (order i)*(J i).sobolevNorm := by
  apply Finset.sum_le_sum
  intro i _
  have h := familyNorm_le_sum_norm (baseWordValues period (J i))
  rw [sum_baseWordValues_norm] at h
  exact mul_le_mul_of_nonneg_left h (weight_pos hρ (order i)).le

/-- The actual differentiated order-zero source is controlled by its finite weighted Sobolev norm.
-/
theorem sourceForcing_weighted_bound {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (energyValues period 6 N hN f) ≤
        weightedNorm period 6 N ρ f := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ
    (fun I => (toJet period f).word I.2)
    (fun I => EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period f) I.2 (by
        have := I.1.isLt; omega))
  have he : (∑ I : ExternalWord N, weight ρ I.1.val *
      (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period f) I.2 (by
          have := I.1.isLt; omega)).sobolevNorm) =
      ∑ I : ExternalWord N, weight ρ I.1.val * sumNorm period
        (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) f) := by
    apply Finset.sum_congr rfl
    intro I _
    rw [sumNorm_wordAtLevel]
  exact h.trans_eq (he.trans (weighted_word_sums period 6 N hN ρ f))

/-- The literal base derivatives of the external transport commutator. -/
def externalTransportForcing {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) : ExternalWord N → BaseWord 6 → LiftL2 period := fun I =>
  baseWordValues period (toJet period (externalCommutator period hs I.1.val I.2 (by
      have := I.1.isLt; omega) L hL u v))

/-- The actual external transport forcing is bounded by the already proved commutator norm. -/
theorem externalTransportForcing_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (externalTransportForcing period hs N
        hN L hL u v) ≤
      weightedCommutatorNorm period hs N hN ρ L hL u v := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ _
    (fun I => toJet period (externalCommutator period hs I.1.val I.2 (by
        have := I.1.isLt; omega) L hL u v))
  simp only [← sumNorm_eq_jet] at h
  exact h.trans_eq (by simp only [Fintype.sum_sigma, weightedCommutatorNorm, Finset.mul_sum])

/-- The literal base derivatives of the actual external coefficient-pressure commutator. -/
def externalPressureForcing {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) : ExternalWord N → BaseWord 6 → LiftL2
        period := fun I =>
  baseWordValues period (commutatorJet K (toJet period p) I.2 (by
      have := I.1.isLt; omega : I.1.val+6 ≤ s))

/-- The actual differentiated external pressure forcing is controlled by its proved H⁶ commutator
sum. -/
theorem externalPressureForcing_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (externalPressureForcing period K N hN
        p) ≤
      externalPressureNorm period K N ρ p := by
  have h := forcing_le_jetSum period (fun I : ExternalWord N => I.1.val) ρ hρ _
    (fun I => commutatorJet K (toJet period p) I.2 (by have := I.1.isLt; omega : I.1.val+6 ≤ s))
  apply h.trans_eq
  rw [Fintype.sum_sigma, externalPressureNorm, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [commutatorBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [sobolevSize_eq period (commutatorJet K (toJet period p) w (by
      have := n.isLt; omega : n.val+6 ≤ s))]

/-- At order zero the genuine Sobolev size is exactly the L² norm. -/
theorem sobolevSize_order_zero (f : LiftL2 period) :
    sobolevSize period (directions := standardDirection) 0 f = ‖f‖ := by
  exact sobolevSize_eq period (EulerSpatialSobolevInverse.SpatialJet.zero f)

/-- The literal base derivative commutator of G with each external pressure derivative. -/
def basePressureForcing {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) : ExternalWord N → BaseWord 6 → LiftL2
        period := fun I a =>
  (EulerSpatialSobolevInverse.SpatialJet.multiply K
    (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
        have := I.1.isLt; omega))).word a.2 -
    A.operator ((EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
        have := I.1.isLt; omega)).word a.2)

/-- At each external word, summing the actual base commutator norms gives the base-pressure block
expression. -/
theorem basePressureForcing_family_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (p : SobolevSpace period s) (I : ExternalWord N) :
    familyNorm (basePressureForcing period K N hN p I) ≤
      ∑ r ∈ Finset.range 7, commutatorBlock K
        (EulerH6Pressure.SpatialJet.derivativeJet (q := 6) (toJet period p) I.2 (by
            have := I.1.isLt; omega)) 0 r := by
  apply (familyNorm_le_sum_norm _).trans_eq
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  simp only [commutatorBlock, sobolevSize_order_zero, basePressureForcing]

/-- The actual base pressure forcing is controlled by the previously proved lower-order pressure
commutator norm. -/
theorem basePressureForcing_bound {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (p : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (basePressureForcing period K N hN p) ≤
      basePressureNorm period K N hN ρ p := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ExternalWord N))) (fun I _ =>
    mul_le_mul_of_nonneg_left (basePressureForcing_family_bound period K N hN p I) (weight_pos hρ
        I.1.val).le)
  exact h.trans_eq (by
      simp only [Fintype.sum_sigma, basePressureNorm, basePressureBlock, Finset.mul_sum])

end EulerGevreyForcingComponents

end
end

end

@[expose] public section

noncomputable section

namespace EulerGevreyCorrectionForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
      EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
      EulerBasePressureCommutator
  EulerGevreyBaseTransport EulerGevreyForcingComponents EulerWeightedForcingAlgebra
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerH6Nonlinear EulerBaseTransportL2

variable (period : ℝ) [Fact (0 < period)]

/-- The seven literal commutator/source terms after external and base differentiation of equation
(17).
The two pressure arguments are the positive projected inverses; the PDE pressure has the opposite
sign. -/
def correctionForcing {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f p0 p1 : SobolevSpace period s) : ExternalWord N →
        BaseWord
        6 → LiftL2 period :=
  -energyValues period 6 N hN f + -externalTransportForcing period hs N hN L hL u v +
    -baseTransportForcing period N hN L hL u v + externalPressureForcing period K N hN p0 +
    basePressureForcing period K0 N hN p0 + externalPressureForcing period K N hN p1 +
    basePressureForcing period K0 N hN p1

/-- The triangle inequality for seven actual forcing arrays has coefficient one. -/
theorem forcing_seven_le {α β H : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup H]
    (ρ : ℝ) (hρ : 0 < ρ) (order : α → ℕ) (a b c d e f g : α → β → H) :
    weightedForcingSum ρ order (a+b+c+d+e+f+g) ≤ weightedForcingSum ρ order a + weightedForcingSum
        ρ order b +
      weightedForcingSum ρ order c + weightedForcingSum ρ order d + weightedForcingSum ρ order e +
      weightedForcingSum ρ order f + weightedForcingSum ρ order g := by
  have h1 := weightedForcingSum_add_le ρ hρ order a b
  have h2 := weightedForcingSum_add_le ρ hρ order (a+b) c
  have h3 := weightedForcingSum_add_le ρ hρ order (a+b+c) d
  have h4 := weightedForcingSum_add_le ρ hρ order (a+b+c+d) e
  have h5 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e) f
  have h6 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e+f) g
  linarith

/-- All actual forcing components satisfy their derived bounds on finite Sobolev fields. -/
theorem correctionForcing_raw_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f p0 p1 : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (correctionForcing period hs K K0 N hN
        L hL u v f p0 p1) ≤
      weightedNorm period 6 N ρ f + (4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ
          u*weightedLoss period 6 N ρ v +
      (5461*baseTransportConstant period)*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 +
      externalPressureNorm period K N ρ p1 + basePressureNorm period K0 N hN ρ p1 := by
  have h := forcing_seven_le ρ hρ (fun I : ExternalWord N => I.1.val)
    (-energyValues period 6 N hN f) (-externalTransportForcing period hs N hN L hL u v)
    (-baseTransportForcing period N hN L hL u v) (externalPressureForcing period K N hN p0)
    (basePressureForcing period K0 N hN p0) (externalPressureForcing period K N hN p1)
    (basePressureForcing period K0 N hN p1)
  simp only [weightedForcingSum_neg] at h
  have hS := sourceForcing_weighted_bound period N hN ρ hρ f
  have hE := (externalTransportForcing_bound period hs N hN ρ hρ L hL u v).trans
    (weightedCommutator_bound period hs N hN ρ hρ L hL u v)
  have hB := baseTransportForcing_weighted_bound period N hN ρ hρ L hL u v
  have hP0 := externalPressureForcing_bound period K N hN ρ hρ p0
  have hQ0 := basePressureForcing_bound period K0 N hN ρ hρ p0
  have hP1 := externalPressureForcing_bound period K N hN ρ hρ p1
  have hQ1 := basePressureForcing_bound period K0 N hN ρ hρ p1
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hS hE) hB)
      hP0) hQ0) hP1) hQ1)

/-- The full actual forcing with both genuine projected pressure solves obeys the spatial part of
equation (19).
Every velocity derivative in the bound lies at or below the chosen cutoff. -/
theorem correctionForcing_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
            hpos L hL u v)) ≤
      (1+2*M*(weightedCoefficient period K 6 N ρ + 448*baseCoefficientSum period K0))*weightedNorm
          period 6 N ρ f +
      (5461*baseTransportConstant period + (448*baseCoefficientSum period
          K0)*(8*M*(5460*lowerProductConstant period 3))) *
        weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      ((4*productConstant period 3)*ρ⁻¹ + 32*Rc*M*productConstant period 3) *
        weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v := by
  let p0 := pressureSobolevOperator period K κ m c hc hpos f
  let p1 := transportPressure period hs K κ m c hc hpos L hL u v
  have h := correctionForcing_raw_bound period hs K K0 N hN ρ hρ L hL u v f p0 p1
  have hp0 := source_pressure_commutators period K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase6
      hsmall hcoeff f
  have hp1e := nonlinear_externalPressure_bound_all period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase6 hsmall hcoeff L hL u v
  have hp1b := nonlinear_basePressure_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase5 hsmall hcoeff L hL u v
  change externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 ≤ _ at hp0
  change externalPressureNorm period K N ρ p1 ≤ _ at hp1e
  change basePressureNorm period K0 N hN ρ p1 ≤ _ at hp1b
  linarith only [h, hp0, hp1e, hp1b]

end EulerGevreyCorrectionForcing
