/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothApproximation
public import LeanPool.NavierStokesAndEuler.Euler.GeneralCylinderAlgebra
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.RealCylinder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import LeanPool.NavierStokesAndEuler.Euler.SobolevL2Product
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
import Mathlib.Analysis.Calculus.Deriv.Prod

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual pointwise multiplication on the complete cylinder Sobolev spaces Hq, q≥6. -/

section

/-! The genuine smooth product bound expressed in the complete cylinder Sobolev norm. -/

section

/-! Actual strong product jets from the genuine Sobolev-to-L² bilinear multiplication. -/

section

/-! Translation is strongly differentiable in the actual Sobolev topology with one more derivative.
-/

@[expose] public section

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Differentiating cylinder translation in Hq costs precisely one Sobolev derivative. -/
theorem sobolevTranslation_hasDerivAt {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1)) :
    HasDerivAt (fun t => sobolevTranslation period q (translationPath period (standardDirection i)
        t)
      (truncateOperator period q u)) (derivativeOperator period q i u) 0 := by
  let f : ℝ → SobolevSpace period q := fun t =>
    sobolevTranslation period q (translationPath period (standardDirection i) t) (truncateOperator
        period q u)
  let d : SobolevWord q → LiftL2 period := fun w =>
    u.val ⟨⟨w.1.val+1, Nat.succ_lt_succ w.1.isLt⟩, Fin.cons i w.2⟩
  have hd : HasDerivAt (fun t => (f t).val) d 0 := by
    apply hasDerivAt_pi.mpr
    intro w
    exact word_hasDerivAt period u w.1.isLt w.2 i
  have hdmem : d ∈ sobolevSubspace period q := by
    apply (sobolevSubspace period q).isClosed.mem_of_tendsto hd.tendsto_slope
    apply Filter.Eventually.of_forall
    intro t
    change (t-0)⁻¹ • ((f t).val - (f 0).val) ∈ sobolevSubspace period q
    exact (sobolevSubspace period q).smul_mem _ ((sobolevSubspace period q).sub_mem (f t).property
        (f 0).property)
  let v : SobolevSpace period q := ⟨d, hdmem⟩
  have hv : HasDerivAt f v 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    rw [tendsto_subtype_rng]
    exact hd.tendsto_slope
  have hval : HasDerivAt (fun t => value period (f t)) (value period v) 0 :=
    (valueOperator period q).hasFDerivAt.comp_hasDerivAt 0 hv
  have he : v = derivativeOperator period q i u := by
    apply value_injective period
    exact hval.unique (derivativeOperator_hasDerivAt period i u)
  rw [he] at hv
  exact hv

end EulerCylinderSobolevSpace

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse
open scoped Topology ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Genuine L² differentiation of a pointwise product, with one Sobolev derivative on its
coefficient. -/
theorem scalarProduct_hasDerivAt (L : Vector3 →L[ℝ] ℝ) (i : Fin 4)
    (u : SobolevSpace period 4) (v v' : LiftL2 period)
    (hv : HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
        v) v' 0) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
      (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v))
      (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v' +
        scalarProduct period (le_refl 3) L (derivativeOperator period 3 i u) v) 0 := by
  let B := scalarProductBilinear period (le_refl 3) L
  have hU := sobolevTranslation_hasDerivAt period i u
  have h := B.hasDerivAt_of_bilinear (fun _ => hU) (fun _ => hv)
  have hzero : sobolevTranslation period 3 (translationPath period (standardDirection i) 0)
      (truncateOperator period 3 u) = truncateOperator period 3 u := by
    apply value_injective period
    change translation period (translationPath period (standardDirection i) 0) (value period u) =
        value period u
    rw [translationPath_zero, translation_zero]
  have he : (fun t => B (sobolevTranslation period 3 (translationPath period (standardDirection i)
      t)
      (truncateOperator period 3 u)) (translation period (translationPath period (standardDirection
          i) t) v)) =
      fun t => translation period (translationPath period (standardDirection i) t)
        (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v) := by
    funext t
    exact scalarProduct_translation period (le_refl 3) L _ _ _
  change HasDerivAt (fun t => B (sobolevTranslation period 3 (translationPath period
      (standardDirection i) t)
      (truncateOperator period 3 u)) (translation period (translationPath period (standardDirection
          i) t) v))
      (B (sobolevTranslation period 3 (translationPath period (standardDirection i) 0)
          (truncateOperator period 3 u)) v' +
        B (derivativeOperator period 3 i u) (translation period (translationPath period
            (standardDirection i) 0) v)) 0 at h
  rw [he, hzero, translationPath_zero, translation_zero] at h
  exact h

/-- Pointwise multiplication with q+3 coefficient derivatives produces a genuine q-jet. -/
def productJet (L : Vector3 →L[ℝ] ℝ) {q : ℕ} (u : SobolevSpace period (q + 3))
    {v : LiftL2 period} (J : SpatialJet period standardDirection q v) :
    SpatialJet period standardDirection q
      (scalarProduct period (le_refl 3) L (restrictOperator period (by omega : 3 ≤ q+3) u) v) := by
  induction q generalizing v with
  | zero => exact .zero _
  | succ q ih =>
    cases J with
    | succ dv lower hd =>
      let u0 : SobolevSpace period (q+3) := truncateOperator period (q+3) u
      let du : Fin 4 → SobolevSpace period (q+3) := fun i => derivativeOperator period (q+3) i u
      let u3 : SobolevSpace period 3 := restrictOperator period (by omega : 3 ≤ q+1+3) u
      let d : Fin 4 → LiftL2 period := fun i =>
        scalarProduct period (le_refl 3) L (restrictOperator period (by
            omega : 3 ≤ q+3) u0) (dv i) +
        scalarProduct period (le_refl 3) L (restrictOperator period (by omega : 3 ≤ q+3) (du i)) v
      have hbase : restrictOperator period (by omega : 3 ≤ q+3) u0 = u3 := by
        apply value_injective period
        rfl
      have hlower (i : Fin 4) : SpatialJet period standardDirection q (d i) :=
        (ih u0 (lower i)).add (ih (du i) (SpatialJet.succ dv lower hd).truncate)
      refine .succ d hlower ?_
      intro i
      let u4 : SobolevSpace period 4 := restrictOperator period (by omega : 4 ≤ q+1+3) u
      have h0 : truncateOperator period 3 u4 = u3 := by
        apply value_injective period
        rfl
      have h1 : derivativeOperator period 3 i u4 =
          restrictOperator period (by omega : 3 ≤ q+3) (du i) := by
        apply value_injective period
        rfl
      have h := scalarProduct_hasDerivAt period L i u4 v (dv i) (hd i)
      rw [h0, h1, ← hbase] at h
      exact h

/-- The output Sobolev array of an actual pointwise scalar-vector product. -/
def productHighLow (L : Vector3 →L[ℝ] ℝ) {q : ℕ}
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q) : SobolevSpace period q :=
  ofJet period (productJet period L u (toJet period v))

@[simp] theorem productHighLow_value (L : Vector3 →L[ℝ] ℝ) {q : ℕ}
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q) :
    value period (productHighLow period L u v) =
      scalarProduct period (le_refl 3) L (restrictOperator period (by
          omega : 3 ≤ q+3) u) (value period v) :=
  value_ofJet period _

end EulerSobolevL2Product

end
end

end

section

/-! Actual real and scalar-vector cylinder multiplication at every fixed Sobolev order q≥6. -/

@[expose] public section

noncomputable section

namespace EulerGeneralCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerRealCylinder EulerVectorCylinder
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual real cylinder algebra estimate at every fixed order q≥6. -/
theorem real_cylinder_Hq_algebra {q : ℕ} (hq : 6 ≤ q) (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    liftSobolevNorm period q (f * g) ≤
      algebraConstant period q * liftSobolevNorm period q f * liftSobolevNorm period q g := by
  have h := cylinder_Hq_algebra period hq (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj w => by
        rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w))
    (fun j hj w => by
        rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2 j hj w))
  have he : complexField period f * complexField period g = complexField period (f * g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period q (f * g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period q f hf, complexField_sobolevNorm period q g hg] at h
  exact h

/-- Every real product derivative through order q is genuinely square-integrable. -/
theorem real_product_word_memLp {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period w (f * g)) 2 (liftMeasure period) := by
  have h := product_word_memLp period hq hn w (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj v => by
        rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2 j hj v))
    (fun j hj v => by
        rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2 j hj v))
  have he : complexField period f * complexField period g = complexField period (f * g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_word period w (f * g) (fun x => (hf x).mul (hg x))] at h
  apply h.of_le
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f * g)
      (fun x => (hf x).mul (hg x)))).aestronglyMeasurable)
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

/-- Every scalar-vector product derivative through order q is genuinely in L². -/
theorem scalar_vector_product_word_memLp {q n : ℕ} (hq : 6 ≤ q) (hn : n ≤ q) (d : ℕ)
    (w : Fin n → Fin 4) (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    MemLp (iteratedFieldDerivative period w (fun x => f x • g x)) 2 (liftMeasure period) := by
  apply MemLp.of_eval_piLp
  intro i
  have h := real_product_word_memLp period hq hn w f (coordinate d i ∘ g) hf
    (postcomp_smooth period _ g hg) hfL2
    (fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v)
  rw [← coordinate_smul period d i f g] at h
  have he : (fun x => iteratedFieldDerivative period w (fun x => f x • g x) x i) =
      iteratedFieldDerivative period w (coordinate d i ∘ (fun x => f x • g x)) := by
    funext x
    exact (coordinate_word period d i w (fun x => f x • g x) (fun x => (hf x).smul (hg x)) x).symm
  rw [he]
  exact h

/-- Multiplication of an actual vector field by a scalar field is bounded in every Hq, q≥6. -/
theorem cylinder_Hq_scalar_vector_product {q : ℕ} (hq : 6 ≤ q) (d : ℕ)
    (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (hgL2 : ∀ j ≤ q, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure
        period)) :
    liftSobolevNorm period q (fun x => f x • g x) ≤
      ((d : ℝ) * algebraConstant period q) * liftSobolevNorm period q f * liftSobolevNorm period q
          g := by
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => f x • g x) x) :=
    fun x => (hf x).smul (hg x)
  have hcomp (i : Fin d) : ∀ j ≤ q, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate d i ∘ g)) 2 (liftMeasure period) :=
    fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v
  have hA := vector_sobolevNorm_le_sum_coordinates period d q (fun x => f x • g x) hs
    (fun i j hj v => by
      rw [coordinate_smul]
      exact real_product_word_memLp period hq hj v f (coordinate d i ∘ g) hf
        (postcomp_smooth period _ g hg) hfL2 (hcomp i))
  have hB (i : Fin d) : liftSobolevNorm period q (coordinate d i ∘ (fun x => f x • g x)) ≤
      algebraConstant period q * liftSobolevNorm period q f * liftSobolevNorm period q g := by
    rw [coordinate_smul]
    have h := real_cylinder_Hq_algebra period hq f (coordinate d i ∘ g) hf
      (postcomp_smooth period _ g hg) hfL2 (hcomp i)
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period q _ (coordinate_norm_le d i) g hg hgL2)
      (mul_nonneg (algebraConstant_nonneg period q) (liftSobolevNorm_nonneg period q f)))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  exact hA.trans (hC.trans_eq (by ring))

end EulerGeneralCylinderAlgebra

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerStrongSmoothJet EulerVectorCylinder
  EulerMetricTransport EulerGeneralCylinderAlgebra
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The derivative sum of a complete Sobolev element agrees with its smooth representative. -/
theorem sumNorm_eq_classical {q : ℕ} (u : SobolevSpace period q)
    (f : LiftDomain period → Vector3)
    (hrep : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    sumNorm period u = liftSobolevNorm period q f := by
  rw [sumNorm_eq_jet]
  exact jet_sobolevNorm_eq period (value period u) (toJet period u) f hrep hf

/-- Actual pointwise multiplication has the same representative at every Sobolev order. -/
theorem scalarProduct_of_value_eq {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (u : SobolevSpace period p) (w : SobolevSpace period q)
    (he : value period u = value period w) (v : LiftL2 period) :
    scalarProduct period hp L u v = scalarProduct period hq L w v := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hp L u v, scalarProduct_ae period hq L w v] with x h1 h2
  rw [h1, h2, he]

/-- A fixed Sobolev-order algebra constant for the complete-array norm. -/
def sobolevProductConstant (q : ℕ) : ℝ :=
  (3 * algebraConstant period q) * (Fintype.card (SobolevWord q) : ℝ)^2

theorem sobolevProductConstant_nonneg (q : ℕ) : 0 ≤ sobolevProductConstant period q :=
  mul_nonneg (mul_nonneg (by norm_num) (algebraConstant_nonneg period q)) (sq_nonneg _)

/-- Exact smooth product representative of the actual strong product jet. -/
theorem productHighLow_representative {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q)
    (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    (value period (productHighLow period L u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      (fun x => L (f x) • g x) := by
  rw [productHighLow_value]
  filter_upwards [scalarProduct_ae period (le_refl 3) L
    (restrictOperator period (by omega : 3 ≤ q+3) u) (value period v), hu, hv] with x h1 h2 h3
  exact h1.trans (by rw [value_restrictOperator, h2, h3])

/-- The actual product jet satisfies the low-order algebra bound whenever the inputs are smooth. -/
theorem productHighLow_bound_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q)
    (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ‖productHighLow period L u v‖ ≤ sobolevProductConstant period q *
      ‖restrictOperator period (by omega : q ≤ q+3) u‖ * ‖v‖ := by
  let U : SobolevSpace period q := restrictOperator period (by omega : q ≤ q+3) u
  have hU : (value period U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f := hu
  have hfL : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2
      (liftMeasure period) :=
    fun j hj w => jet_classical_memLp period hj (value period U) (toJet period U) w f hU hf
  have hgL : ∀ j ≤ q, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2
      (liftMeasure period) :=
    fun j hj w => jet_classical_memLp period hj (value period v) (toJet period v) w g hv hg
  have hP := cylinder_Hq_scalar_vector_product period hq 3 (L ∘ f) g
    (postcomp_smooth period L f hf) hg (fun j hj w => postcomp_word_memLp period hj L f hf hfL w)
        hgL
  have hPs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => L (f x) • g x) x) :=
    fun x => (postcomp_smooth period L f hf x).smul (hg x)
  have hpr := productHighLow_representative period L u v f g hu hv
  have hN := norm_le_sumNorm period (productHighLow period L u v)
  rw [sumNorm_eq_classical period _ _ hpr hPs] at hN
  have hLF := postcomp_sobolevNorm_le period q L hL f hf hfL
  have hFn : liftSobolevNorm period q f ≤ (Fintype.card (SobolevWord q) : ℝ) * ‖U‖ := by
    rw [← sumNorm_eq_classical period U f hU hf]
    exact sumNorm_le_card_norm period U
  have hGn : liftSobolevNorm period q g ≤ (Fintype.card (SobolevWord q) : ℝ) * ‖v‖ := by
    rw [← sumNorm_eq_classical period v g hv hg]
    exact sumNorm_le_card_norm period v
  have hpos : 0 ≤ 3 * algebraConstant period q := mul_nonneg (by
      norm_num) (algebraConstant_nonneg period q)
  calc
    ‖productHighLow period L u v‖ ≤ liftSobolevNorm period q (fun x => L (f x) • g x) := hN
    _ ≤ (3 * algebraConstant period q) * liftSobolevNorm period q (L ∘ f) * liftSobolevNorm period
        q g := hP
    _ ≤ (3 * algebraConstant period q) * liftSobolevNorm period q f * liftSobolevNorm period q g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLF hpos) (liftSobolevNorm_nonneg
          period q g)
    _ ≤ (3 * algebraConstant period q) * ((Fintype.card (SobolevWord q) : ℝ) * ‖U‖) *
        ((Fintype.card (SobolevWord q) : ℝ) * ‖v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hFn hpos) hGn (liftSobolevNorm_nonneg period q g)
        (mul_nonneg hpos (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg U)))
    _ = sobolevProductConstant period q * ‖U‖ * ‖v‖ := by unfold sobolevProductConstant; ring

/-- The high-low product is additive in its first argument. -/
theorem productHighLow_add_left {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u w : SobolevSpace period (q + 3)) (v : SobolevSpace period q) :
    productHighLow period L (u+w) v = productHighLow period L u v + productHighLow period L w v :=
        by
  apply value_injective period
  change value period (productHighLow period L (u+w) v) = value period (productHighLow period L u
      v) + value period (productHighLow period L w v)
  simp only [productHighLow_value, map_add, scalarProduct_add_left]

/-- The high-low product is additive in its second argument. -/
theorem productHighLow_add_right {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period (q + 3)) (v w : SobolevSpace period q) :
    productHighLow period L u (v+w) = productHighLow period L u v + productHighLow period L u w :=
        by
  apply value_injective period
  change value period (productHighLow period L u (v+w)) = value period (productHighLow period L u
      v) + value period (productHighLow period L u w)
  simp only [productHighLow_value]
  exact scalarProduct_add_right period (le_refl 3) L _ _ _

/-- Exact product difference decomposition. -/
theorem productHighLow_sub {q : ℕ} (L : Vector3 →L[ℝ] ℝ)
    (u w : SobolevSpace period (q + 3)) (v z : SobolevSpace period q) :
    productHighLow period L u v - productHighLow period L w z =
      productHighLow period L (u-w) v + productHighLow period L w (v-z) := by
  apply value_injective period
  change value period (productHighLow period L u v) - value period (productHighLow period L w z) =
    value period (productHighLow period L (u-w) v) + value period (productHighLow period L w (v-z))
  simp only [productHighLow_value, map_sub]
  rw [show value period (v-z) = value period v - value period z from map_sub (valueOperator period
      q) v z]
  change scalarProductBilinear period (le_refl 3) L _ _ - scalarProductBilinear period (le_refl 3)
      L _ _ =
    scalarProductBilinear period (le_refl 3) L _ _ + scalarProductBilinear period (le_refl 3) L _ _
  simp only [map_sub, sub_apply]
  abel

end EulerSobolevL2Product

end
end

end

section

/-! Cauchy convergence of actual smooth cylinder products in the complete Sobolev space. -/

@[expose] public section

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse
  EulerMetricTransport EulerCylinderMollifier EulerMollifierRepresentative
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Differences of actual smooth representatives remain actual smooth representatives. -/
theorem smooth_representative_sub {q : ℕ} (u v : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ g : LiftDomain period → Vector3,
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∃ f : LiftDomain period → Vector3,
      (value period (u-v) : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x) := by
  obtain ⟨f, hfu, hf⟩ := hu
  obtain ⟨g, hgv, hg⟩ := hv
  refine ⟨f-g, ?_, fun x => (hf x).sub (hg x)⟩
  filter_upwards [Lp.coeFn_sub (value period u) (value period v), hfu, hgv] with x h1 h2 h3
  exact h1.trans (by simp only [Pi.sub_apply, h2, h3])

/-- The smooth product bound only needs the existence of the actual smooth representatives. -/
theorem productHighLow_bound_of_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ g : LiftDomain period → Vector3,
      (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ‖productHighLow period L u v‖ ≤ sobolevProductConstant period q *
      ‖restrictOperator period (by omega : q ≤ q+3) u‖ * ‖v‖ := by
  obtain ⟨f, hfu, hf⟩ := hu
  obtain ⟨g, hgv, hg⟩ := hv
  exact productHighLow_bound_smooth period hq L hL u v f g hfu hgv hf hg

/-- The genuine product difference is controlled solely in the original Sobolev topology. -/
theorem productHighLow_dist_of_smooth {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u w : SobolevSpace period (q + 3)) (v z : SobolevSpace period q)
    (hu : ∃ f : LiftDomain period → Vector3, (value period u : LiftDomain period → Vector3)
        =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hw : ∃ f : LiftDomain period → Vector3, (value period w : LiftDomain period → Vector3)
        =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hv : ∃ f : LiftDomain period → Vector3, (value period v : LiftDomain period → Vector3)
        =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hz : ∃ f : LiftDomain period → Vector3, (value period z : LiftDomain period → Vector3)
        =ᵐ[liftMeasure period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    dist (productHighLow period L u v) (productHighLow period L w z) ≤
      sobolevProductConstant period q * dist (restrictOperator period (by omega : q ≤ q+3) u)
        (restrictOperator period (by omega : q ≤ q+3) w) * ‖v‖ +
      sobolevProductConstant period q * ‖restrictOperator period (by
          omega : q ≤ q+3) w‖ * dist v z := by
  rw [dist_eq_norm, productHighLow_sub]
  have h1 := productHighLow_bound_of_smooth period hq L hL (u-w) v
    (smooth_representative_sub period u w hu hw) hv
  have h2 := productHighLow_bound_of_smooth period hq L hL w (v-z) hw
    (smooth_representative_sub period v z hv hz)
  simpa only [map_sub, ← dist_eq_norm] using (norm_add_le _ _).trans (add_le_add h1 h2)

/-- A quantitative difference estimate transfers Cauchy convergence through a bilinear operation. -/
theorem cauchySeq_of_product_control {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] (u : ℕ → X) (v : ℕ → Y) (p : ℕ → Z) (A B : ℝ)
    (hu : CauchySeq u) (hv : CauchySeq v)
    (h : ∀ n m, dist (p n) (p m) ≤ A * dist (u n) (u m) + B * dist (v n) (v m)) :
    CauchySeq p := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0] at hu hv ⊢
  apply squeeze_zero (fun nm : ℕ × ℕ => (dist_nonneg : 0 ≤ dist (p nm.1) (p nm.2))) (fun nm => h
      nm.1 nm.2)
  simpa only [mul_zero, add_zero] using (hu.const_mul A).add (hv.const_mul B)

/-- Smooth products of the concrete approximations. -/
def productApprox (q n : ℕ) (L : Vector3 →L[ℝ] ℝ) (u v : SobolevSpace period q) : SobolevSpace
    period q :=
  productHighLow period L (smoothApprox period q n u) (sobolevMollifier period q n v)

/-- The actual product approximations satisfy a bound independent of the smoothing scale. -/
theorem productApprox_bound {q : ℕ} (hq : 6 ≤ q) (n : ℕ)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    ‖productApprox period q n L u v‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ := by
  have hv : ∃ g : LiftDomain period → Vector3,
      (value period (sobolevMollifier period q n v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
          period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := ⟨smoothMollifier period n (value period v),
          sobolevMollifier_representative period n v,
    smoothMollifier_smooth period n (value period v)⟩
  have h := productHighLow_bound_of_smooth period hq L hL _ _ (smoothApprox_representative period n
      u) hv
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (smoothApprox_bound period n u) (sobolevProductConstant_nonneg
        period q))
    (sobolevMollifier_bound period n v) (norm_nonneg _) (mul_nonneg (sobolevProductConstant_nonneg
        period q) (norm_nonneg u)))

/-- Actual smooth products converge in the complete Hq topology. -/
theorem productApprox_cauchy {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    CauchySeq (fun n => productApprox period q n L u v) := by
  let U := fun n => restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)
  let V := fun n => sobolevMollifier period q n v
  have hU : CauchySeq U := (smoothApprox_tendsto period u).cauchySeq
  have hV : CauchySeq V := (sobolevMollifier_tendsto period v).cauchySeq
  apply cauchySeq_of_product_control U V _ (sobolevProductConstant period q * ‖v‖)
    (sobolevProductConstant period q * ‖u‖) hU hV
  intro n m
  have hsm (k : ℕ) : ∃ g : LiftDomain period → Vector3,
      (value period (sobolevMollifier period q k v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
          period] g ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := ⟨smoothMollifier period k (value period v),
          sobolevMollifier_representative period k v,
    smoothMollifier_smooth period k (value period v)⟩
  have h := productHighLow_dist_of_smooth period hq L hL _ _ _ _
    (smoothApprox_representative period n u) (smoothApprox_representative period m u) (hsm n) (hsm
        m)
  have h1 := mul_le_mul_of_nonneg_left (sobolevMollifier_bound period n v)
    (mul_nonneg (sobolevProductConstant_nonneg period q) (dist_nonneg : 0 ≤ dist (U n) (U m)))
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (smoothApprox_bound period m u) (sobolevProductConstant_nonneg
        period q))
    (dist_nonneg : 0 ≤ dist (V n) (V m))
  exact h.trans ((add_le_add h1 h2).trans_eq (by dsimp [U, V]; ring))

end EulerSobolevL2Product

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerMetricTransport
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The L² values of the genuine approximating products converge to the actual pointwise product. -/
theorem productApprox_value_tendsto {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (u v : SobolevSpace period q) :
    Filter.Tendsto (fun n => value period (productApprox period q n L u v)) Filter.atTop
      (𝓝 (scalarProduct period (by omega : 3 ≤ q) L u (value period v))) := by
  let U := fun n => restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto (fun n => value period (sobolevMollifier period q n v)) Filter.atTop (𝓝
      (value period v)) :=
    (valueOperator period q).continuous.tendsto v |>.comp (sobolevMollifier_tendsto period v)
  have h := (scalarProductBilinear period (by
      omega : 3 ≤ q) L).continuous₂.tendsto (u, value period v) |>.comp (hU.prodMk_nhds hV)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  change scalarProduct period (by
      omega : 3 ≤ q) L (U n) (value period (sobolevMollifier period q n v)) =
    value period (productApprox period q n L u v)
  rw [productApprox, productHighLow_value]
  exact scalarProduct_of_value_eq period (by omega : 3 ≤ q) (le_refl 3) L _ _ rfl _

/-- The actual pointwise product lies in Hq and satisfies the proved fixed-order algebra bound. -/
theorem exists_sobolev_product {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    ∃ p : SobolevSpace period q,
      value period p = scalarProduct period (by omega : 3 ≤ q) L u (value period v) ∧
      ‖p‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ := by
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (productApprox_cauchy period hq L hL u v)
  refine ⟨p, ?_, ?_⟩
  · exact tendsto_nhds_unique ((valueOperator period q).continuous.tendsto p |>.comp hp)
      (productApprox_value_tendsto period hq L u v)
  · exact le_of_tendsto hp.norm (Filter.Eventually.of_forall (fun n => productApprox_bound period
      hq n L hL u v))

/-- The genuine product in the complete Sobolev space, uniquely determined by its L² value. -/
def productHq {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) : SobolevSpace period q :=
  Classical.choose (exists_sobolev_product period hq L hL u v)

@[simp] theorem productHq_value {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    value period (productHq period hq L hL u v) = scalarProduct period (by
        omega : 3 ≤ q) L u (value period v) :=
  (Classical.choose_spec (exists_sobolev_product period hq L hL u v)).1

/-- The algebra bound for the genuine Sobolev product. -/
theorem productHq_norm {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    ‖productHq period hq L hL u v‖ ≤ sobolevProductConstant period q * ‖u‖ * ‖v‖ :=
  (Classical.choose_spec (exists_sobolev_product period hq L hL u v)).2

/-- The product is exactly pointwise multiplication almost everywhere. -/
theorem productHq_ae {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    (value period (productHq period hq L hL u v) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      (fun x => L (value period u x) • value period v x) := by
  rw [productHq_value]
  exact scalarProduct_ae period (by omega : 3 ≤ q) L u (value period v)

theorem productHq_add_left {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u w v : SobolevSpace period q) :
    productHq period hq L hL (u+w) v = productHq period hq L hL u v + productHq period hq L hL w v
        := by
  apply value_injective period
  change value period (productHq period hq L hL (u+w) v) = value period (productHq period hq L hL u
      v) + value period (productHq period hq L hL w v)
  simp only [productHq_value, scalarProduct_add_left]

theorem productHq_smul_left {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (r : ℝ) (u v : SobolevSpace period q) :
    productHq period hq L hL (r • u) v = r • productHq period hq L hL u v := by
  apply value_injective period
  change value period (productHq period hq L hL (r • u) v) = r • value period (productHq period hq
      L hL u v)
  simp only [productHq_value, scalarProduct_smul_left]

theorem productHq_add_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v w : SobolevSpace period q) :
    productHq period hq L hL u (v+w) = productHq period hq L hL u v + productHq period hq L hL u w
        := by
  apply value_injective period
  change value period (productHq period hq L hL u (v+w)) = value period (productHq period hq L hL u
      v) + value period (productHq period hq L hL u w)
  simp only [productHq_value]
  exact scalarProduct_add_right period (by omega : 3 ≤ q) L u (value period v) (value period w)

theorem productHq_smul_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) (r : ℝ) (v : SobolevSpace period q) :
    productHq period hq L hL u (r • v) = r • productHq period hq L hL u v := by
  apply value_injective period
  change value period (productHq period hq L hL u (r • v)) = r • value period (productHq period hq
      L hL u v)
  simp only [productHq_value]
  exact scalarProduct_smul_right period (by omega : 3 ≤ q) L u r (value period v)

/-- Multiplication by a Sobolev scalar component, as an actual bounded Sobolev operator. -/
def productHqRight {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  LinearMap.mkContinuous
    { toFun := productHq period hq L hL u
      map_add' := productHq_add_right period hq L hL u
      map_smul' := productHq_smul_right period hq L hL u }
    (sobolevProductConstant period q * ‖u‖) (productHq_norm period hq L hL u)

theorem productHqRight_norm {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u : SobolevSpace period q) : ‖productHqRight period hq L hL u‖ ≤ sobolevProductConstant period
        q * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sobolevProductConstant_nonneg period q)
      (norm_nonneg u))
    (productHq_norm period hq L hL u)

/-- The actual complete Sobolev algebra multiplication is a continuous bilinear map. -/
def productHqBilinear {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  LinearMap.mkContinuous
    { toFun := productHqRight period hq L hL
      map_add' := by
        intro u w
        apply ContinuousLinearMap.ext
        intro v
        exact productHq_add_left period hq L hL u w v
      map_smul' := by
        intro r u
        apply ContinuousLinearMap.ext
        intro v
        exact productHq_smul_left period hq L hL r u v }
    (sobolevProductConstant period q) (productHqRight_norm period hq L hL)

@[simp] theorem productHqBilinear_apply {q : ℕ} (hq : 6 ≤ q)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period q) :
    productHqBilinear period hq L hL u v = productHq period hq L hL u v := rfl

end EulerSobolevL2Product
