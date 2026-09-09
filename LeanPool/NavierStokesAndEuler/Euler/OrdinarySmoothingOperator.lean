/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySobolevTower
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldScaling
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordConstraints

/-! Actual smooth regularizers of ordinary solenoidal L². Their maps
into every complete Sobolev space are bounded by the closed graph
theorem, rather than by an assumed derivative estimate. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanOrdinaryLift EulerCylinderSobolevSpace
  EulerParameterWordGevrey EulerSmoothSobolev Finset
open scoped ContDiff Topology

local instance instOrdinarySmoothingOperator1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Smoothing operator data, collecting `op`, `smooth`, `translation`, `symmetric`,
`contraction`, `solenoidal`. -/
structure SmoothingOperator where
  /-- Op of `SmoothingOperator`, of type `L2 →L[ℝ] L2`. -/
  op : L2 →L[ℝ] L2
  smooth : ∀ u, SmoothOrbit (op u)
  translation : ∀ a u, EulerMeanSolenoidal.translation a (op u) =
    op (EulerMeanSolenoidal.translation a u)
  symmetric : ∀ u v, ⟪op u,v⟫_ℝ=⟪u,op v⟫_ℝ
  contraction : ∀ u, ‖op u‖ ≤ ‖u‖
  solenoidal : ∀ u, op u ∈ solenoidalSpace

namespace SmoothingOperator

variable (S : SmoothingOperator)

/-- Field, given by `smoothL2Field (S.op u) (S.smooth u)`. -/
def field (u : L2) : SmoothL2Field Space := smoothL2Field (S.op u) (S.smooth u)

@[simp] theorem field_toLp (u : L2) : (S.field u).toLp=S.op u := smoothL2Field_toLp _ _

private theorem valueOperator_ordinary (q : ℕ) (u : L2) (hu : SmoothOrbit u) :
    valueOperator 1 q (ordinarySobolev q u hu)=ordinaryLift u :=
  ordinarySobolev_value q u hu

/-- Lift linear, bundling `toFun`, `map_add`, `map_smul`. -/
def liftLinear (q : ℕ) : L2 →ₗ[ℝ] SobolevSpace 1 q where
  toFun u := ordinarySobolev q (S.op u) (S.smooth u)
  map_add' u v := by
    apply value_injective 1
    change valueOperator 1 q (ordinarySobolev q (S.op (u+v)) _) =
      valueOperator 1 q (ordinarySobolev q (S.op u) _ + ordinarySobolev q (S.op v) _)
    rw [(valueOperator 1 q).map_add]
    simp only [valueOperator_ordinary,map_add]
  map_smul' c u := by
    apply value_injective 1
    change valueOperator 1 q (ordinarySobolev q (S.op (c • u)) _) =
      valueOperator 1 q (c • ordinarySobolev q (S.op u) _)
    rw [(valueOperator 1 q).map_smul]
    simp only [valueOperator_ordinary,map_smul]

@[simp] theorem liftLinear_value (q : ℕ) (u : L2) :
    value 1 (S.liftLinear q u)=ordinaryLift (S.op u) := ordinarySobolev_value _ _ _

/-- Lift, constructed using `ContinuousLinearMap.ofSeqClosedGraph`. -/
def lift (q : ℕ) : L2 →L[ℝ] SobolevSpace 1 q :=
  ContinuousLinearMap.ofSeqClosedGraph (g := S.liftLinear q) (by
    intro u x y hu hy
    apply value_injective 1
    rw [liftLinear_value]
    have hl := ((valueOperator 1 q).continuous.tendsto y).comp hy
    have hr := ((ordinaryLift.toContinuousLinearMap.comp S.op).continuous.tendsto x).comp hu
    have hv (z : L2) : valueOperator 1 q (S.liftLinear q z)=ordinaryLift (S.op z) :=
      S.liftLinear_value q z
    simp only [Function.comp_def,hv] at hl
    change Tendsto (fun n => ordinaryLift (S.op (u n))) atTop (𝓝 (ordinaryLift (S.op x))) at hr
    exact tendsto_nhds_unique hl hr)

@[simp] theorem lift_apply (q : ℕ) (u : L2) :
    S.lift q u=ordinarySobolev q (S.op u) (S.smooth u) := rfl

/-- Jet map, given by `(ordinaryTensorOperator n).comp (S.lift n)`. -/
def jetMap (n : ℕ) : L2 →L[ℝ] Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space) :=
  (ordinaryTensorOperator n).comp (S.lift n)

theorem field_jetLp (u : L2) (n : ℕ) : (S.field u).jetLp n=S.jetMap n u := by
  rw [jetMap,ContinuousLinearMap.comp_apply,lift_apply]
  have h := ordinaryTensorOperator_apply (S.field u) n
  simpa only [field_toLp] using h.symm

theorem field_jet_continuous {K : Type*} [TopologicalSpace K]
    (u : K → L2) (hu : Continuous u) (n : ℕ) :
    Continuous (fun t => (S.field (u t)).jetLp n) := by
  simp only [field_jetLp]
  exact (S.jetMap n).continuous.comp hu

theorem field_jet_norm (u : L2) (n : ℕ) :
    ‖(S.field u).jetLp n‖ ≤ ‖S.jetMap n‖*‖u‖ := by
  rw [field_jetLp]
  exact (S.jetMap n).le_opNorm u

theorem field_add (u v : L2) : S.field (u+v)=addField (S.field u) (S.field v) := by
  apply smoothField_eq_of_toLp_eq
  simp only [field_toLp,toLp_addField,map_add]

theorem field_smul (c : ℝ) (u : L2) : S.field (c • u)=scaleField c (S.field u) := by
  apply smoothField_eq_of_toLp_eq
  simp only [field_toLp,scaleField_toLp,map_smul]

theorem field_word (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField (S.field A.toLp) w).toLp=S.op (wordField A w).toLp := by
  rw [word_toLp_eq_orbit,field_toLp,word_toLp_eq_orbit,
    ← wordDerivative_comp_clm axis S.op _ A.translation_contDiff]
  congr 2
  exact funext (fun a => S.translation a A.toLp)

theorem field_word_norm (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ‖(wordField (S.field A.toLp) w).toLp‖ ≤ ‖(wordField A w).toLp‖ := by
  rw [field_word]
  exact S.contraction _

theorem field_wordBound (A : SmoothL2Field Space) (q : ℕ) (N : ℝ) (hN : WordBound q N A) :
    WordBound q N (S.field A.toLp) :=
  fun n hn w => (S.field_word_norm A w).trans (hN n hn w)

theorem field_energy_le (A : SmoothL2Field Space) (q : ℕ) :
    wordEnergy q (S.field A.toLp) ≤ wordEnergy q A :=
  sum_le_sum (fun _ _ => sum_le_sum (fun w _ =>
    pow_le_pow_left₀ (norm_nonneg _) (S.field_word_norm A w) 2))

/-- Pointwise cost, given by `smoothEmbeddingConstant*(∑ n ∈ range 3, ‖S.jetMap n‖)`. -/
def pointwiseCost : ℝ := smoothEmbeddingConstant*(∑ n ∈ range 3, ‖S.jetMap n‖)

theorem pointwiseCost_nonneg : 0 ≤ S.pointwiseCost :=
  mul_nonneg smoothEmbeddingConstant_nonneg
    (sum_nonneg (fun n _ => (S.jetMap n).opNorm_nonneg))

theorem field_pointwise (u : L2) (x : Space) : ‖(S.field u).field x‖ ≤ S.pointwiseCost*‖u‖ := by
  apply (real_pointwise_H2 (S.field u) x).trans
  calc
    _ ≤ smoothEmbeddingConstant*(∑ n ∈ range 3, ‖S.jetMap n‖*‖u‖) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun n _ => S.field_jet_norm u n))
        smoothEmbeddingConstant_nonneg
    _ = _ := by rw [← sum_mul]; exact (mul_assoc _ _ _).symm

end SmoothingOperator
end EulerOrdinarySobolev
