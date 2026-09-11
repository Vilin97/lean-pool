/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTameEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerHigherEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerL2Stability
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordConstraints
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTransportCancellation
public import Mathlib.Analysis.InnerProductSpace.Defs
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketExistence
import Mathlib.Analysis.InnerProductSpace.Calculus
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySobolevTower
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldScaling

/-! General smooth local Euler existence in ordinary R³. The datum
has all actual spatial L² derivatives; no Gevrey radius is assumed.
The solution is the strong Sobolev limit of genuine symmetric
regularized Euler evolutions on one common positive interval. -/

section

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

end
end

end

section

/-! The regularized L² flow has genuine smooth spatial representatives,
continuous jets of every order, and its true time derivative. -/

section

/-! A bounded quadratic vector field whose radial energy vanishes has
a genuine global flow on a real Hilbert space. Radial normalization
first gives a globally Lipschitz equation; its conserved norm then
removes the normalization by a constant rescaling of time. -/

@[expose] public section

noncomputable section

namespace EulerHilbertQuadraticFlow

open Filter ContinuousLinearMap InnerProductSpace
open scoped Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial, given by `(1+‖x‖)⁻¹ • x`. -/
def radial (x : E) : E := (1+‖x‖)⁻¹ • x

theorem radial_norm (x : E) : ‖radial x‖ ≤ 1 := by
  rw [radial,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)),← div_eq_inv_mul]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg x])

theorem radial_sub_norm (x y : E) : ‖radial x-radial y‖ ≤ 2*‖x-y‖ := by
  have hx : 0 < 1+‖x‖ := by positivity
  have hy : 0 < 1+‖y‖ := by positivity
  have ha : 0 ≤ (1+‖x‖)⁻¹ := (inv_pos.mpr hx).le
  have ha1 : (1+‖x‖)⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr (by linarith [norm_nonneg x])
  have he : (1+‖x‖)⁻¹-(1+‖y‖)⁻¹ =
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖))*(1+‖y‖)⁻¹ := by
    field_simp
    ring
  have hv : radial x-radial y = (1+‖x‖)⁻¹ • (x-y) +
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖)) • radial y := by
    calc
      _ = (1+‖x‖)⁻¹ • (x-y)+((1+‖x‖)⁻¹-(1+‖y‖)⁻¹) • y := by
        dsimp [radial]
        module
      _ = _ := by rw [he,radial,smul_smul]
  have hd : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
  rw [hv]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,norm_mul,
    Real.norm_of_nonneg ha,Real.norm_eq_abs]
  have h1 : (1+‖x‖)⁻¹*‖x-y‖ ≤ ‖x-y‖ :=
    mul_le_of_le_one_left (norm_nonneg _) ha1
  have h2 : ((1+‖x‖)⁻¹*|‖y‖-‖x‖|)*‖radial y‖ ≤ ‖x-y‖ := by
    calc
      _ ≤ ((1+‖x‖)⁻¹*‖x-y‖)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd ha) (radial_norm y)
          (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))
      _ ≤ _ := by simpa only [mul_one] using h1
  linarith

theorem radial_lipschitz : LipschitzWith 2 (radial : E → E) :=
  lipschitzWith_iff_norm_sub_le.mpr radial_sub_norm

/-- Normalized, given by `B (radial x) (radial x)`. -/
def normalized (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E := B (radial x) (radial x)

theorem bilinear_bound (B : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖B x y‖ ≤ ‖B‖*‖x‖*‖y‖ :=
  ((B x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

theorem normalized_lipschitz (B : E →L[ℝ] E →L[ℝ] E) :
    LipschitzWith (4*‖B‖₊) (normalized B) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have he : normalized B x-normalized B y =
      B (radial x-radial y) (radial x)+B (radial y) (radial x-radial y) := by
    simp only [normalized,map_sub,sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have h1 : ‖B (radial x-radial y) (radial x)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_sub_norm x y) (norm_nonneg B))
      (radial_norm x) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2 : ‖B (radial y) (radial x-radial y)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_norm y) (norm_nonneg B))
      (radial_sub_norm x y) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  exact (add_le_add h1 h2).trans_eq (by
      simp only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm]; ring)

theorem normalized_eq (B : E →L[ℝ] E →L[ℝ] E) (x : E) :
    normalized B x=((1+‖x‖)⁻¹)^2 • B x x := by
  simp only [normalized,radial,map_smul,smul_apply,smul_smul,pow_two]

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_global_quadratic (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x, ⟪x, B x x⟫_ℝ = 0) (x : E) :
    ∃ u : ℝ → E, u 0=x ∧ (∀ t, HasDerivAt u (B (u t) (u t)) t) ∧
      ∀ t, ‖u t‖=‖x‖ := by
  have hc : Continuous (Function.uncurry (fun _t : ℝ => normalized B)) :=
    (normalized_lipschitz B).continuous.comp continuous_snd
  obtain ⟨v,hv0,hv⟩ := EulerPacketExistence.exists_global_solution hc
    (fun _t => normalized_lipschitz B) x
  have hd (t : ℝ) : HasDerivAt (fun s => ‖v s‖^2) 0 t := by
    have h := (hv t).norm_sq
    simpa only [normalized_eq,real_inner_smul_right,hB,mul_zero] using h
  have hn (t : ℝ) : ‖v t‖=‖x‖ := by
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    rw [hv0] at he
    nlinarith [norm_nonneg (v t),norm_nonneg x]
  let c := (1+‖x‖)^2
  refine ⟨fun t => v (c*t),by simpa only [mul_zero] using hv0,?_,fun t => hn (c*t)⟩
  intro t
  have hi : HasDerivAt (fun r : ℝ => c*r) c t := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul c
  have h := (hv (c*t)).scomp t hi
  have he : c • normalized B (v (c*t))=B (v (c*t)) (v (c*t)) := by
    rw [normalized_eq,hn,smul_smul]
    have hp : c*((1+‖x‖)⁻¹)^2=1 := by
      dsimp [c]
      field_simp
    rw [hp,one_smul]
  simpa only [he,Function.comp_def] using h

end Hilbert
end EulerHilbertQuadraticFlow

end
end

end

section

/-! A genuine global L² solution of the symmetric regularized Euler
equation. The vector field is a bounded bilinear map and its actual
L² energy vanishes by noncompact transport cancellation. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical Finset
open scoped ContDiff Topology

theorem advection_add_left (A B C : SmoothL2Field Space) :
    advectionField (addField A B) C=addField (advectionField A C) (advectionField B C) := by
  apply field_ext
  exact funext (fun x => by simp only [advectionField_field,addField_field,map_add])

theorem advection_add_right (A B C : SmoothL2Field Space) :
    advectionField A (addField B C)=addField (advectionField A B) (advectionField A C) := by
  apply field_ext
  funext x
  have he : (addField B C).field=B.field+C.field := rfl
  simp only [advectionField_field,addField_field,he,
    fderiv_add (B.smooth.differentiable (by
        simp) x) (C.smooth.differentiable (by simp) x),add_apply]

theorem advection_smul_left (c : ℝ) (A B : SmoothL2Field Space) :
    advectionField (scaleField c A) B=scaleField c (advectionField A B) := by
  apply field_ext
  exact funext (fun x => by simp only [advectionField_field,scaleField_field,map_smul])

theorem advection_smul_right (c : ℝ) (A B : SmoothL2Field Space) :
    advectionField A (scaleField c B)=scaleField c (advectionField A B) := by
  apply field_ext
  exact funext (fun x => by
    simp only [advectionField_field,scaleField_field,scaleField_fderiv,smul_apply])

namespace SmoothingOperator

variable (S : SmoothingOperator)

/-- Advection linear, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
def advectionLinear : L2 →ₗ[ℝ] L2 →ₗ[ℝ] L2 where
  toFun u :=
    { toFun v := (advectionField (S.field u) (S.field v)).toLp
      map_add' v w := by rw [S.field_add,advection_add_right,toLp_addField]
      map_smul' c v := by rw [S.field_smul,advection_smul_right,scaleField_toLp]; rfl }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (advectionField (S.field (u+v)) (S.field w)).toLp =
      (advectionField (S.field u) (S.field w)).toLp +
        (advectionField (S.field v) (S.field w)).toLp
    rw [S.field_add,advection_add_left,toLp_addField]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change (advectionField (S.field (c • u)) (S.field v)).toLp =
      c • (advectionField (S.field u) (S.field v)).toLp
    rw [S.field_smul,advection_smul_left,scaleField_toLp]

/-- Advection cost, given by `S.pointwiseCost*‖S.jetMap 1‖`. -/
def advectionCost : ℝ := S.pointwiseCost*‖S.jetMap 1‖

theorem advectionLinear_bound (u v : L2) :
    ‖S.advectionLinear u v‖ ≤ S.advectionCost*‖u‖*‖v‖ := by
  change ‖(advectionField (S.field u) (S.field v)).toLp‖ ≤ _
  apply (advection_norm_velocity (S.field u) (S.field v) _ (S.field_pointwise u)).trans
  rw [← (S.field v).derivative.norm_jetLp_zero,(S.field v).norm_derivative_jetLp]
  apply (mul_le_mul_of_nonneg_left (S.field_jet_norm v 1)
    (mul_nonneg S.pointwiseCost_nonneg (norm_nonneg u))).trans_eq
  dsimp [advectionCost]
  ring

/-- Advection, given by `S.advectionLinear.mkContinuous₂ S.advectionCost
S.advectionLinear_bound`. -/
def advection : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  S.advectionLinear.mkContinuous₂ S.advectionCost S.advectionLinear_bound

@[simp] theorem advection_apply (u v : L2) :
    S.advection u v=(advectionField (S.field u) (S.field v)).toLp := rfl

/-- Quadratic, given by `(ContinuousLinearMap.compL ℝ L2 L2 L2 (-S.op)).comp S.advection`. -/
def quadratic : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  (ContinuousLinearMap.compL ℝ L2 L2 L2 (-S.op)).comp S.advection

@[simp] theorem quadratic_apply (u v : L2) :
    S.quadratic u v= -S.op (advectionField (S.field u) (S.field v)).toLp := rfl

theorem field_divergence (u : L2) (x : Space) : divergence (S.field u).field x=0 :=
  solenoidal_representative_divergence _ (S.solenoidal u) _ (S.field u).smooth
    (by simpa only [field_toLp] using (S.field u).toLp_ae) x

theorem quadratic_energy (u : L2) : ⟪u,S.quadratic u u⟫_ℝ=0 := by
  rw [quadratic_apply,inner_neg_right,← S.symmetric,← field_toLp]
  rw [real_inner_comm,advection_inner_zero (S.field u) (S.field u) (S.field_divergence u),neg_zero]

theorem exists_global (u₀ : L2) :
    ∃ u : ℝ → L2, u 0=u₀ ∧ (∀ t, HasDerivAt u (S.quadratic (u t) (u t)) t) ∧
      ∀ t, ‖u t‖=‖u₀‖ :=
  EulerHilbertQuadraticFlow.exists_global_quadratic S.quadratic S.quadratic_energy u₀

end SmoothingOperator
end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
   EulerVolterraConvolution EulerContinuousTimeIntegral Finset
open scoped ContDiff Topology

namespace SmoothingOperator

variable (S : SmoothingOperator)

/-- Rhs, given by `fieldNeg (S.field (advectionField (S.field u) (S.field u)).toLp)`. -/
def rhs (u : L2) : SmoothL2Field Space :=
  fieldNeg (S.field (advectionField (S.field u) (S.field u)).toLp)

theorem rhs_toLp (u : L2) : (S.rhs u).toLp=S.quadratic u u := by
  simp only [rhs,toLp_fieldNeg,field_toLp,quadratic_apply]

theorem rhs_continuous {K : Type*} [TopologicalSpace K] (u : K → L2)
    (hu : Continuous u) (n : ℕ) : Continuous (fun t => (S.rhs (u t)).jetLp n) := by
  apply continuous_jetLp_mapField
  apply S.field_jet_continuous
  exact (S.advection.continuous.comp hu).clm_apply hu

end SmoothingOperator

/-- Regularized evolution data, collecting `velocity`, `velocity_continuous`, `solenoidal`,
`time_law`. -/
structure RegularizedEvolution (S : SmoothingOperator) (T : ℝ) (hT : 0 ≤ T) where
  /-- Velocity field of `RegularizedEvolution`, of type `Icc (0 : ℝ) T → SmoothL2Field Space`. -/
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).toLp)
      (S.quadratic (velocity ⟨t,ht.1.le,ht.2.le⟩).toLp (velocity ⟨t,ht.1.le,ht.2.le⟩).toLp) t

namespace RegularizedEvolution

variable {S : SmoothingOperator} {T : ℝ} {hT : 0 ≤ T} (U : RegularizedEvolution S T hT)

/-- Derivative, given by `S.rhs (U.velocity t).toLp`. -/
def derivative (t : Icc (0 : ℝ) T) : SmoothL2Field Space := S.rhs (U.velocity t).toLp

theorem derivative_continuous (n : ℕ) : Continuous (fun t => (U.derivative t).jetLp n) :=
  S.rhs_continuous _ (fieldPath U.velocity U.velocity_continuous).continuous n

theorem pointwise_time (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun r => (U.velocity (projIcc 0 T hT r)).field x)
      ((U.derivative t).field x) (Icc (0 : ℝ) T) t := by
  apply pointwise_derivative_of_l2 T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous _ t x
  intro r hr
  simpa only [derivative,SmoothingOperator.rhs_toLp] using U.time_law r hr

theorem l2_time (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (U.velocity (projIcc 0 T hT r)).toLp)
      (U.derivative t).toLp (Icc (0 : ℝ) T) t := by
  have h := ordinaryWord_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
    (fun r hr x => (U.pointwise_time ⟨r,hr.1.le,hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
    (n := 0) Fin.elim0 t
  simpa only [wordField_zero] using h

end RegularizedEvolution

namespace SmoothingOperator

variable (S : SmoothingOperator) (T : ℝ) (hT : 0 ≤ T)

theorem exists_smooth (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ U : RegularizedEvolution S T hT, U.velocity ⟨0,le_rfl,hT⟩=A := by
  obtain ⟨u,hu0,hu,_huNorm⟩ := S.exists_global A.toLp
  have huc : Continuous u := (show Differentiable ℝ u from fun t => (hu
      t).differentiableAt).continuous
  let a : C(Icc (0 : ℝ) T,L2) :=
    ⟨fun t => S.advection (u t) (u t),
      (S.advection.continuous.comp (huc.comp continuous_subtype_val)).clm_apply
        (huc.comp continuous_subtype_val)⟩
  let z : C(Icc (0 : ℝ) T,L2) := -integral T hT a
  let v : Icc (0 : ℝ) T → SmoothL2Field Space := fun t => addField A (S.field (z t))
  have hv : ∀ t, (v t).toLp=u t := by
    intro t
    have he := eq_initial_add_integral T hT
      ((-S.op).compLeftContinuous ℝ (Icc (0 : ℝ) T) a) u
      (fun s => by
        change HasDerivWithinAt u (-S.op (S.advection (u s) (u s))) _ _
        exact (hu (s : ℝ)).hasDerivWithinAt) t
    have hi : integral T hT ((-S.op).compLeftContinuous ℝ (Icc (0 : ℝ) T) a) t =
        S.op (z t) := by
      change (∫ r in (0 : ℝ)..(t : ℝ), (-S.op) (extendPath T hT a r))=S.op (z t)
      rw [(-S.op).intervalIntegral_comp_comm
        ((extendPath_continuous T hT a).intervalIntegrable 0 t)]
      change -S.op (realIntegral T hT a t)=S.op (-realIntegral T hT a t)
      rw [map_neg]
    rw [hu0,hi] at he
    simpa only [v,toLp_addField,field_toLp] using he.symm
  have hvcont : ∀ n, Continuous (fun t => (v t).jetLp n) :=
    fun n => continuous_jetLp_addField _ _ (fun _ => continuous_const)
      (S.field_jet_continuous z z.continuous) n
  have hv0 : v ⟨0,le_rfl,hT⟩=A := by
    apply smoothField_eq_of_toLp_eq
    rw [hv,hu0]
  refine ⟨{ velocity := v
            velocity_continuous := hvcont
            solenoidal := fun t => ?_
            time_law := fun t ht => ?_ },hv0⟩
  · simpa only [v,toLp_addField,field_toLp] using solenoidalSpace.add_mem hA (S.solenoidal (z t))
  · simp only [hv]
    have he : (fun r => u (projIcc 0 T hT r : ℝ)) =ᶠ[𝓝 t] u := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      simp only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1.le,hr.2.le⟩)]
    exact (hu t).congr_of_eventuallyEq he

end SmoothingOperator
end EulerOrdinarySobolev

end
end

end

section

/-! Actual symmetric, solenoidal smoothing operators. They converge
to Helmholtz projection, with an explicit H¹ approximation error. -/

section

/-! Symmetric compact smooth approximate identities on ordinary spatial L². -/

section

/-! A true orbit derivative gives a global increment bound for a linear isometric action. -/

@[expose] public section

noncomputable section

namespace EulerIsometricAction

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sub_le_of_hasFDerivAt (τ : P → E →ₗᵢ[ℝ] E)
    (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u) (hzero : ∀ u, τ 0 u = u)
    (u : E) (D : P →L[ℝ] E) (h : HasFDerivAt (fun a => τ a u) D 0) (a : P) :
    ‖τ a u-u‖ ≤ ‖D‖*‖a‖ := by
  have hb (b : P) : ‖(τ b).toContinuousLinearMap.comp D‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] using D.le_opNorm v
  have hh := (convex_univ : Convex ℝ (Set.univ : Set
      P)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun b _ => (hasFDerivAt_all τ hadd u D h b).hasFDerivWithinAt)
    (fun b _ => hb b) (Set.mem_univ (0 : P)) (Set.mem_univ a)
  simpa only [hzero, sub_zero] using hh

end EulerIsometricAction

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinaryMollifier

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerNoncompactTransport EulerLpTranslation.SmoothL2Field
open scoped ContDiff Topology Convolution

/-- Bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
def bump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := cutoffScale n
  rOut := 2*cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

/-- Kernel, given by `(bump n).normed volume`. -/
def kernel (n : ℕ) : Space → ℝ := (bump n).normed volume

theorem kernel_smooth (n : ℕ) : ContDiff ℝ ∞ (kernel n) := (bump n).contDiff_normed
theorem kernel_compact (n : ℕ) : HasCompactSupport (kernel n) := (bump n).hasCompactSupport_normed
theorem kernel_nonneg (n : ℕ) (x : Space) : 0 ≤ kernel n x := (bump n).nonneg_normed x
theorem kernel_integral (n : ℕ) : ∫ x, kernel n x = 1 := (bump n).integral_normed
theorem kernel_integrable (n : ℕ) : Integrable (kernel n) := (bump n).integrable_normed
theorem kernel_neg (n : ℕ) (x : Space) : kernel n (-x)=kernel n x := (bump n).normed_neg x

/-- Smooth orbit, given by `convolution (kernel n) (fun a => translation a u)
(ContinuousLinearMap.lsmul ℝ ℝ) volume`. -/
def smoothOrbit (n : ℕ) (u : L2) : Space → L2 :=
  convolution (kernel n) (fun a => translation a u) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Mollify, given by `smoothOrbit n u 0`. -/
def mollify (n : ℕ) (u : L2) : L2 := smoothOrbit n u 0

theorem smoothOrbit_contDiff (n : ℕ) (u : L2) : ContDiff ℝ ∞ (smoothOrbit n u) :=
  (kernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_smooth n) (EulerMeanTimeTranslation.translation_continuous u).locallyIntegrable

theorem mollify_tendsto (u : L2) : Tendsto (fun n => mollify n u) atTop (𝓝 u) := by
  have hr : Tendsto (fun n => (bump n).rOut) atTop (𝓝 (0 : ℝ)) := by
    simpa only [bump,mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Space)) hr (EulerMeanTimeTranslation.translation_continuous u) 0
  simpa only [translation_zero,mollify,smoothOrbit,kernel] using h

theorem mollify_eq_integral (n : ℕ) (u : L2) :
    mollify n u=∫ y : Space, kernel n y • translation (-y) u := by
  simp only [mollify,smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply,zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (u : L2) :
    Integrable (fun y : Space => kernel n y • translation (-y) u) :=
  ((kernel_smooth n).continuous.smul
    ((EulerMeanTimeTranslation.translation_continuous u).comp
        continuous_neg)).integrable_of_hasCompactSupport
      (kernel_compact n).smul_right

theorem mollify_norm_le (n : ℕ) (u : L2) : ‖mollify n u‖ ≤ ‖u‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le ((kernel_integrable n).mul_const ‖u‖)
    (f := fun y : Space => kernel n y • translation (-y) u) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  exact Eventually.of_forall (fun y => by
    rw [norm_smul,LinearIsometry.norm_map,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)])

theorem mollify_add (n : ℕ) (u v : L2) : mollify n (u+v)=mollify n u+mollify n v := by
  simp only [mollify_eq_integral,map_add,smul_add]
  exact integral_add (kernel_orbit_integrable n u) (kernel_orbit_integrable n v)

theorem mollify_smul (n : ℕ) (c : ℝ) (u : L2) : mollify n (c • u)=c • mollify n u := by
  simp only [mollify_eq_integral,map_smul]
  simp_rw [smul_comm (kernel n _) c]
  exact integral_smul c _

/-- Mollifier linear, bundling `toFun`, `map_add`, `map_smul`. -/
def mollifierLinear (n : ℕ) : L2 →ₗ[ℝ] L2 where
  toFun := mollify n
  map_add' := mollify_add n
  map_smul' := mollify_smul n

/-- Mollifier, given by `(mollifierLinear n).mkContinuous 1 (fun u => by change ‖mollify n u‖ ≤
1*‖u‖ simpa only [one_mul] using mollify_norm_le n u)`. -/
def mollifier (n : ℕ) : L2 →L[ℝ] L2 :=
  (mollifierLinear n).mkContinuous 1 (fun u => by
    change ‖mollify n u‖ ≤ 1*‖u‖
    simpa only [one_mul] using mollify_norm_le n u)

@[simp] theorem mollifier_apply (n : ℕ) (u : L2) : mollifier n u=mollify n u := rfl

theorem mollify_translation (n : ℕ) (a : Space) (u : L2) :
    translation a (mollify n u)=mollify n (translation a u) := by
  rw [mollify_eq_integral,mollify_eq_integral]
  change (translation a).toContinuousLinearMap
    (∫ y : Space, kernel n y • translation (-y) u)=_
  rw [← (translation a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap]
    rw [translation_add,translation_add,add_comm a])

theorem smoothOrbit_eq (n : ℕ) (u : L2) (x : Space) :
    smoothOrbit n u x=translation x (mollify n u) := by
  rw [mollify_eq_integral]
  change _=(translation x).toContinuousLinearMap
    (∫ y : Space, kernel n y • translation (-y) u)
  rw [← (translation x).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  simp only [smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap,translation_add,sub_eq_add_neg])

theorem mollify_smooth (n : ℕ) (u : L2) :
    ContDiff ℝ ∞ (fun a => translation a (mollify n u)) := by
  convert smoothOrbit_contDiff n u using 1
  exact funext (fun a => (smoothOrbit_eq n u a).symm)

theorem translation_inner_shift (a : Space) (u v : L2) :
    ⟪translation a u,v⟫_ℝ=⟪u,translation (-a) v⟫_ℝ := by
  calc
    _=⟪translation a u,translation a (translation (-a) v)⟫_ℝ := by
      rw [translation_add,add_neg_cancel,translation_zero]
    _=_ := (translation a).inner_map_map _ _

theorem mollify_symmetric (n : ℕ) (u v : L2) :
    ⟪mollify n u,v⟫_ℝ=⟪u,mollify n v⟫_ℝ := by
  rw [mollify_eq_integral,mollify_eq_integral]
  rw [real_inner_comm v _,← integral_inner (kernel_orbit_integrable n u) v,
    ← integral_inner (kernel_orbit_integrable n v) u]
  rw [← integral_neg_eq_self (fun y : Space => ⟪v,kernel n y • translation (-y) u⟫_ℝ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [kernel_neg,neg_neg,real_inner_smul_right,real_inner_smul_right,
      real_inner_comm _ v,translation_inner_shift])

theorem translation_increment (A : EulerLpTranslation.SmoothL2Field Space) (a : Space) :
    ‖translation a A.toLp-A.toLp‖ ≤ ‖A.derivative.toLp‖*‖a‖ := by
  have h := A.translation_hasFDerivAt 0
  simp only [EulerLpTranslation.translation_zero] at h
  exact (EulerIsometricAction.norm_sub_le_of_hasFDerivAt translation translation_add
      translation_zero
    A.toLp _ h a).trans (mul_le_mul_of_nonneg_right
      (EulerLpDerivative.derivativeMap_norm_le _ _) (norm_nonneg _))

theorem mollify_error (n : ℕ) (A : EulerLpTranslation.SmoothL2Field Space) :
    ‖mollify n A.toLp-A.toLp‖ ≤ (2*cutoffScale n)*‖A.derivative.toLp‖ := by
  have he : mollify n A.toLp-A.toLp =
      ∫ y : Space, kernel n y • (translation (-y) A.toLp-A.toLp) := by
    simp only [smul_sub,integral_sub (kernel_orbit_integrable n A.toLp)
      ((kernel_integrable n).smul_const A.toLp),integral_smul_const,kernel_integral,
      one_smul,mollify_eq_integral]
  rw [he]
  have h := norm_integral_le_of_norm_le
    ((kernel_integrable n).mul_const ((2*cutoffScale n)*‖A.derivative.toLp‖))
    (f := fun y : Space => kernel n y • (translation (-y) A.toLp-A.toLp)) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  apply Eventually.of_forall
  intro y
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)]
  by_cases hy : kernel n y=0
  · simp only [hy,zero_mul,le_refl]
  apply mul_le_mul_of_nonneg_left _ (kernel_nonneg n y)
  apply (translation_increment A (-y)).trans
  rw [norm_neg,mul_comm (2*cutoffScale n)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hs : y ∈ Function.support ((bump n).normed volume) := hy
  rw [(bump n).support_normed_eq,Metric.mem_ball,dist_zero_right] at hs
  exact hs.le

end EulerOrdinaryMollifier

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerOrdinaryMollifier
open scoped ContDiff Topology

theorem projection_inner (u v : L2) :
    ⟪solenoidalProjection u,v⟫_ℝ=⟪u,solenoidalProjection v⟫_ℝ :=
  solenoidalSpace.inner_starProjection_left_eq_right u v

theorem projection_idempotent (u : L2) :
    solenoidalProjection (solenoidalProjection u)=solenoidalProjection u :=
  solenoidalSpace.starProjection_eq_self_iff.mpr (solenoidalProjection_mem u)

/-- Regularizer map, given by `solenoidalProjection.comp ((mollifier n).comp
solenoidalProjection)`. -/
def regularizerMap (n : ℕ) : L2 →L[ℝ] L2 :=
  solenoidalProjection.comp ((mollifier n).comp solenoidalProjection)

@[simp] theorem regularizerMap_apply (n : ℕ) (u : L2) :
    regularizerMap n u=solenoidalProjection (mollify n (solenoidalProjection u)) := rfl

theorem regularizerMap_translation (n : ℕ) (a : Space) (u : L2) :
    EulerMeanSolenoidal.translation a (regularizerMap n u) =
      regularizerMap n (EulerMeanSolenoidal.translation a u) := by
  simp only [regularizerMap_apply,solenoidalProjection_translation,mollify_translation]

theorem regularizerMap_smooth (n : ℕ) (u : L2) : SmoothOrbit (regularizerMap n u) := by
  have h := solenoidalProjection.contDiff.comp (mollify_smooth n (solenoidalProjection u))
  simpa only [Function.comp_def,← solenoidalProjection_translation,← regularizerMap_apply] using h

theorem regularizerMap_symmetric (n : ℕ) (u v : L2) :
    ⟪regularizerMap n u,v⟫_ℝ=⟪u,regularizerMap n v⟫_ℝ := by
  simp only [regularizerMap_apply,projection_inner,mollify_symmetric]

theorem regularizerMap_contract (n : ℕ) (u : L2) : ‖regularizerMap n u‖ ≤ ‖u‖ :=
  (solenoidalProjection_apply_norm_le _).trans
    ((mollify_norm_le n _).trans (solenoidalProjection_apply_norm_le u))

/-- Regularizer, bundling `op`, `smooth`, `translation`, `symmetric` and the required
compatibility proofs. -/
def regularizer (n : ℕ) : SmoothingOperator where
  op := regularizerMap n
  smooth := regularizerMap_smooth n
  translation := regularizerMap_translation n
  symmetric := regularizerMap_symmetric n
  contraction := regularizerMap_contract n
  solenoidal _u := solenoidalProjection_mem _

theorem regularizer_tendsto (u : L2) :
    Tendsto (fun n => (regularizer n).op u) atTop (𝓝 (solenoidalProjection u)) := by
  change Tendsto (fun n => solenoidalProjection (mollify n (solenoidalProjection u)))
    atTop (𝓝 (solenoidalProjection u))
  have h := solenoidalProjection.continuous.tendsto (solenoidalProjection u)
  simpa only [Function.comp_def,projection_idempotent] using h.comp (mollify_tendsto
      (solenoidalProjection u))

theorem regularizer_error (n : ℕ) (A : SmoothL2Field Space) :
    ‖(regularizer n).op A.toLp-solenoidalProjection A.toLp‖ ≤
      (2*EulerNoncompactTransport.cutoffScale n)*‖(solenoidalField A).derivative.toLp‖ := by
  change ‖solenoidalProjection (mollify n (solenoidalProjection A.toLp)) -
    solenoidalProjection A.toLp‖ ≤ _
  have he : solenoidalProjection (mollify n (solenoidalProjection A.toLp)) -
      solenoidalProjection A.toLp=solenoidalProjection
        (mollify n (solenoidalProjection A.toLp)-solenoidalProjection A.toLp) := by
    rw [map_sub,projection_idempotent]
  rw [he]
  apply (solenoidalProjection_apply_norm_le _).trans
  simpa only [solenoidalField_toLp] using mollify_error n (solenoidalField A)

theorem solenoidalField_wordBound (A : SmoothL2Field Space) (q : ℕ) (M : ℝ)
    (hM : WordBound q M A) : WordBound q M (solenoidalField A) := by
  intro k hk w
  rw [solenoidalField_word]
  exact (solenoidalProjection_apply_norm_le _).trans (hM k hk w)

/-- Regularizer error, given by `6*EulerNoncompactTransport.cutoffScale n`. -/
def regularizerError (n : ℕ) : ℝ := 6*EulerNoncompactTransport.cutoffScale n

theorem regularizerError_nonneg (n : ℕ) : 0 ≤ regularizerError n :=
  mul_nonneg (by norm_num) (EulerNoncompactTransport.cutoffScale_pos n).le

theorem regularizerError_tendsto : Tendsto regularizerError atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n => 6*EulerNoncompactTransport.cutoffScale n) atTop (𝓝 (0 : ℝ))
  simpa only [regularizerError,mul_zero] using
      EulerNoncompactTransport.cutoffScale_tendsto.const_mul 6

theorem regularizer_error_wordBound (n : ℕ) (A : SmoothL2Field Space) (M : ℝ)
    (hM : WordBound 1 M A) :
    ‖(regularizer n).op A.toLp-solenoidalProjection A.toLp‖ ≤ regularizerError n*M := by
  apply (regularizer_error n A).trans
  have hb := wordBound_jet_norm (solenoidalField_wordBound A 1 M hM) (le_refl 1)
  rw [← (solenoidalField A).derivative.norm_jetLp_zero,(solenoidalField A).norm_derivative_jetLp]
  exact (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by norm_num) (EulerNoncompactTransport.cutoffScale_pos n).le)).trans_eq (by
      simp only [regularizerError,pow_one]
      ring)

end EulerOrdinarySobolev

end
end

end

section

/-! The true smooth regularized Euler flows are Cauchy in continuous
L² on the common energy-controlled interval. -/

section

/-! The actual regularized Euler right-hand side converges to the
projected Euler right-hand side, uniformly on bounded H⁴ sets. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev Finset
open scoped ContDiff Topology

theorem regularizer_error_words (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (q : ℕ) (M : ℝ) (hM : WordBound (q + 1) M A) :
    WordBound q (regularizerError n*M) (fieldSub ((regularizer n).field A.toLp) A) := by
  intro k hk w
  simp only [fieldSub,wordField_add,wordField_neg,toLp_addField,toLp_fieldNeg,
    SmoothingOperator.field_word,← sub_eq_add_neg]
  have hp : solenoidalProjection (wordField A w).toLp=(wordField A w).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr (word_solenoidal A hA w)
  have h := regularizer_error_wordBound n (wordField A w) M
    (wordBound_wordField (wordBound_mono hM (by omega : k+1 ≤ q+1)) w)
  simpa only [hp] using h

theorem wordBound_gradient {A : SmoothL2Field Space} {M : ℝ} (hM : WordBound 3 M A)
    (x : Space) : ‖fderiv ℝ A.field x‖ ≤ (360*smoothEmbeddingConstant)*M := by
  have h := real_smooth_fderiv_le_H3 3 A.field A.smooth (fun j _ => A.integrable j) x
  rw [← tensorNorm_eq] at h
  exact (h.trans (mul_le_mul_of_nonneg_left (tensorNorm_three_le A M hM)
    (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))).trans_eq (by ring)

theorem advection_low_words (A : SmoothL2Field Space) (M : ℝ) (hM : WordBound 4 M A) :
    WordBound 1 (6*h3ProductConstant*M^2) (advectionField A A) := by
  intro k hk w
  apply (source_advection_outer A A M M (wordBound_mono hM (by omega)) hM (by omega) w).trans
  have hcoef : 3*(2 : ℝ)^k ≤ 6 := by interval_cases k <;> norm_num
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef h3ProductConstant_nonneg) (wordBound_nonneg hM))
    (wordBound_nonneg hM)).trans_eq (by ring)

/-- Regularization cost, given by `(6*h3ProductConstant+399*smoothEmbeddingConstant)*M^2`. -/
def regularizationCost (M : ℝ) : ℝ := (6*h3ProductConstant+399*smoothEmbeddingConstant)*M^2

theorem regularizationCost_nonneg (M : ℝ) : 0 ≤ regularizationCost M := by
  have := h3ProductConstant_nonneg
  have := smoothEmbeddingConstant_nonneg
  unfold regularizationCost
  positivity

theorem regularized_rhs_error (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (M : ℝ) (hM : WordBound 4 M A) :
    ‖((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp‖ ≤
      regularizerError n*regularizationCost M := by
  let S := regularizer n
  let B := S.field A.toLp
  have hB : WordBound 4 M B := S.field_wordBound A 4 M hM
  have he := regularizer_error_words n A hA 1 M (wordBound_mono hM (by omega))
  have he0 : ‖B.toLp-A.toLp‖ ≤ regularizerError n*M := by
    simpa only [toLp_fieldSub] using wordBound_toLp he
  have he1 : ‖B.jetLp 1-A.jetLp 1‖ ≤ 3*(regularizerError n*M) := by
    simpa only [jetLp_fieldSub,pow_one] using wordBound_jet_norm he (le_refl 1)
  have hadv : ‖(advectionField B B).toLp-(advectionField A A).toLp‖ ≤
      ((360*smoothEmbeddingConstant)*M)*(regularizerError n*M) +
      ((13*smoothEmbeddingConstant)*M)*(3*(regularizerError n*M)) := by
    apply (advection_sub_norm B A _ _ (wordBound_gradient (wordBound_mono hB (by omega)))
      (wordBound_pointwise (wordBound_mono hM (by omega)))).trans
    exact add_le_add (mul_le_mul_of_nonneg_left he0
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
      (mul_le_mul_of_nonneg_left he1
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
  have hp := regularizer_error_wordBound n (advectionField B B) _ (advection_low_words B M hB)
  have hq : ‖solenoidalProjection (advectionField B B).toLp -
      solenoidalProjection (advectionField A A).toLp‖ ≤
      ‖(advectionField B B).toLp-(advectionField A A).toLp‖ := by
    rw [← map_sub]
    exact solenoidalProjection_apply_norm_le _
  have heq : ((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp =
      -(S.op (advectionField B B).toLp-solenoidalProjection (advectionField A A).toLp) := by
    simp only [SmoothingOperator.rhs_toLp,SmoothingOperator.quadratic_apply,projectedRhs_toLp,S,B]
    abel
  rw [heq,norm_neg]
  apply (norm_sub_le_norm_sub_add_norm_sub (S.op (advectionField B B).toLp)
    (solenoidalProjection (advectionField B B).toLp)
    (solenoidalProjection (advectionField A A).toLp)).trans
  exact (add_le_add hp (hq.trans hadv)).trans_eq (by unfold regularizationCost; ring)

end EulerOrdinarySobolev

end
end

end

section

/-! Actual L² stability of projected Euler with a small additive
defect. The reference gradient is the only solution coefficient. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution Finset
open scoped ContDiff Topology

theorem projected_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (K : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) :
    2*⟪B.toLp-A.toLp,(projectedRhs B).toLp-(projectedRhs A).toLp⟫_ℝ ≤
      2*K*‖B.toLp-A.toLp‖^2 := by
  let W := fieldSub B A
  let P := fieldSub (pressureField B) (pressureField A)
  have he : fieldSub (projectedRhs B) (projectedRhs A)=differenceRhs A W P := by
    apply field_ext
    funext x
    have hw : W.field=B.field-A.field := funext (fieldSub_field B A)
    simp only [fieldSub_field,projectedRhs_field,differenceRhs_field,hw,P]
    rw [fderiv_sub (B.smooth.differentiable (by simp) x) (A.smooth.differentiable (by simp) x)]
    simp only [Pi.sub_apply,sub_apply,map_sub]
    abel_nf
  have hd : ∀ x, divergence (addField A W).field x=0 := by
    have hw : (addField A W).field=B.field := by
      funext x
      simp only [addField_field,W,fieldSub_field]
      abel
    rw [hw]
    exact solenoidal_representative_divergence _ hB _ B.smooth B.toLp_ae
  have hs : W.toLp ∈ solenoidalSpace := by
    rw [toLp_fieldSub]
    exact solenoidalSpace.sub_mem hB hA
  have hp : P.toLp ∈ gradientSpace := by
    rw [toLp_fieldSub]
    exact gradientSpace.sub_mem (pressureField_mem_gradient B) (pressureField_mem_gradient A)
  have h := differenceRhs_l2_bound A W P K hK hd hs hp
  rw [← he] at h
  simpa only [toLp_fieldSub,W] using h

theorem perturbed_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (RA RB : L2) (K ea eb : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (ha : ‖RA - (projectedRhs A).toLp‖ ≤ ea)
    (hb : ‖RB - (projectedRhs B).toLp‖ ≤ eb) :
    2*⟪B.toLp-A.toLp,RB-RA⟫_ℝ ≤ (2*K+1)*‖B.toLp-A.toLp‖^2+(ea+eb)^2 := by
  let W := B.toLp-A.toLp
  let e := (RB-(projectedRhs B).toLp)-(RA-(projectedRhs A).toLp)
  have he : RB-RA=((projectedRhs B).toLp-(projectedRhs A).toLp)+e := by dsimp [e]; abel
  have hn : ‖e‖ ≤ ea+eb := by
    exact (norm_sub_le _ _).trans ((add_le_add hb ha).trans_eq (add_comm eb ea))
  have he0 : 0 ≤ ea+eb := (norm_nonneg e).trans hn
  have hpair : 2*⟪W,e⟫_ℝ ≤ ‖W‖^2+(ea+eb)^2 := by
    have hi : ⟪W,e⟫_ℝ ≤ ‖W‖*(ea+eb) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg W))
    nlinarith [sq_nonneg (‖W‖-(ea+eb))]
  rw [he,inner_add_right,mul_add]
  exact (add_le_add (projected_difference_energy A B hA hB K hK) hpair).trans_eq (by
      dsimp [W]; ring)

theorem forced_linear_zero_bound (T C E : ℝ) (hC : 1 ≤ C)
    (X X' : ℝ → ℝ) (hX : ContinuousOn X (Icc 0 T)) (hX0 : X 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, X' t ≤ C * X t + E ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : X t ≤ E^2*Real.exp (C*T) := by
  have hh := linear_stability_within (fun r => X r+E^2) X' C T
    (hX.add continuousOn_const)
    (fun r hr => (hd r ⟨hr.1,hr.2.le⟩).add_const _)
    (fun r hr => (hb r ⟨hr.1,hr.2.le⟩).trans (by nlinarith [sq_nonneg E])) t ht
  rw [hX0,zero_add] at hh
  have he : E^2*Real.exp (C*t) ≤ E^2*Real.exp (C*T) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg E)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))
  linarith [sq_nonneg E]

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev EulerVolterraConvolution Finset
open scoped ContDiff Topology

/-- Regularized comparison cost, given by `regularizationCost M*Real.sqrt (Real.exp
((2*((360*smoothEmbeddingConstant)*M)+1)*T))`. -/
def regularizedComparisonCost (T M : ℝ) : ℝ :=
  regularizationCost M*Real.sqrt (Real.exp ((2*((360*smoothEmbeddingConstant)*M)+1)*T))

theorem regularizedComparisonCost_nonneg (T M : ℝ) : 0 ≤ regularizedComparisonCost T M :=
  mul_nonneg (regularizationCost_nonneg M) (Real.sqrt_nonneg _)

theorem regularized_l2_comparison {T : ℝ} {hT : 0 ≤ T} {j k : ℕ}
    (U : RegularizedEvolution (regularizer j) T hT)
    (V : RegularizedEvolution (regularizer k) T hT)
    (M : ℝ) (hU : ∀ t, WordBound 4 M (U.velocity t))
    (hV : ∀ t, WordBound 4 M (V.velocity t))
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp) :
    ‖fieldPath V.velocity V.velocity_continuous-fieldPath U.velocity U.velocity_continuous‖ ≤
      (regularizerError j+regularizerError k)*regularizedComparisonCost T M := by
  let G := (360*smoothEmbeddingConstant)*M
  let C := 2*G+1
  let E := (regularizerError j+regularizerError k)*regularizationCost M
  have hM : 0 ≤ M := wordBound_nonneg (hU ⟨0,le_rfl,hT⟩)
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hE : 0 ≤ E := mul_nonneg (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
    (regularizationCost_nonneg M)
  let X (r : ℝ) := ‖(V.velocity (projIcc 0 T hT r)).toLp-(U.velocity (projIcc 0 T hT r)).toLp‖^2
  let X' (r : ℝ) := 2*⟪(V.velocity (projIcc 0 T hT r)).toLp-(U.velocity (projIcc 0 T hT r)).toLp,
    (V.derivative (projIcc 0 T hT r)).toLp-(U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ
  have hc : ContinuousOn X (Icc 0 T) := by
    exact ((((fieldPath V.velocity V.velocity_continuous).continuous.sub
      (fieldPath U.velocity U.velocity_continuous).continuous).comp continuous_projIcc).norm.pow
          2).continuousOn
  have hx0 : X 0=0 := by
    simp only [X,projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
      hinit,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt X (X' r) (Icc 0 T) r := by
    have h := ((V.l2_time ⟨r,hr⟩).sub (U.l2_time ⟨r,hr⟩)).norm_sq
    simpa only [X,X',Pi.sub_apply,projIcc_of_mem hT hr] using h
  have hb (r : ℝ) (_hr : r ∈ Icc 0 T) : X' r ≤ C*X r+E^2 := by
    have h := perturbed_difference_energy (U.velocity (projIcc 0 T hT r))
      (V.velocity (projIcc 0 T hT r)) (U.solenoidal _) (V.solenoidal _)
      (U.derivative (projIcc 0 T hT r)).toLp (V.derivative (projIcc 0 T hT r)).toLp
      G (regularizerError j*regularizationCost M) (regularizerError k*regularizationCost M)
      (wordBound_gradient (wordBound_mono (hU _) (by omega)))
      (regularized_rhs_error j _ (U.solenoidal _) M (hU _))
      (regularized_rhs_error k _ (V.solenoidal _) M (hV _))
    simpa only [X,X',C,E,add_mul] using h
  have hnorm (t : Icc (0 : ℝ) T) :
      ‖(V.velocity t).toLp-(U.velocity t).toLp‖ ≤ E*Real.sqrt (Real.exp (C*T)) := by
    have h := forced_linear_zero_bound T C E hC X X' hc hx0 hd hb t t.property
    simp only [X,projIcc_of_mem hT t.property] at h
    have hs := Real.sq_sqrt ((Real.exp_pos (C*T)).le)
    have he : 0 ≤ E*Real.sqrt (Real.exp (C*T)) := mul_nonneg hE (Real.sqrt_nonneg _)
    nlinarith [norm_nonneg ((V.velocity t).toLp-(U.velocity t).toLp)]
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
    (regularizedComparisonCost_nonneg T M))).mpr
  intro t
  exact (hnorm t).trans_eq (by dsimp [E,C,G,regularizedComparisonCost]; ring)

theorem regularized_cauchy {T : ℝ} {hT : 0 ≤ T}
    (U : ∀ n, RegularizedEvolution (regularizer n) T hT)
    (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (hinit : ∀ j k, ((U k).velocity ⟨0, le_rfl, hT⟩).toLp = ((U j).velocity ⟨0, le_rfl, hT⟩).toLp) :
    CauchySeq (fun n => fieldPath (U n).velocity (U n).velocity_continuous) := by
  have he : Tendsto (fun n => regularizerError n*regularizedComparisonCost T M) atTop (𝓝 (0 : ℝ))
      := by
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (regularizedComparisonCost T M)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, regularizerError n*regularizedComparisonCost T M < ε/2 :=
    (tendsto_order.mp he).2 _ (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun j hj k hk => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  apply (regularized_l2_comparison (U j) (U k) M (hM j) (hM k) (hinit j k)).trans_lt
  have hj' := hN j hj
  have hk' := hN k hk
  nlinarith

end EulerOrdinarySobolev

end
end

end

section

/-! Uniform energy bounds for the actual regularized flows. Symmetry
and translation commutation transfer the exact energy production to
the smoothed velocity, where the checked Euler cancellations apply. -/

section

/-! A uniform short-time bound for a nonnegative genuine energy with
a quadratic differential upper bound. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set

theorem quadratic_energy_bound (T C : ℝ) (hT : 0 ≤ T)
    (X X' : ℝ → ℝ) (hX : ContinuousOn X (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ X t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, X' t ≤ C * (1 + X t) ^ 2)
    (hC : 0 ≤ C) (hsmall : C * T ≤ (1 + X 0)⁻¹ / 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : X t ≤ 2*X 0+1 := by
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
  have hp (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < 1+X r := by linarith [hpos r hr]
  let f (r : ℝ) := (1+X r)⁻¹+C*r
  let f' (r : ℝ) := -(X' r)/(1+X r)^2+C
  have hc : ContinuousOn f (Icc 0 T) :=
    ((continuousOn_const.add hX).inv₀ (fun r hr => (hp r hr).ne')).add
      (continuous_const.mul continuous_id).continuousOn
  have hfd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt f (f' r) (Icc 0 T) r := by
    have hi := ((hd r hr).const_add 1).inv (hp r hr).ne'
    have hl := ((hasDerivAt_id r).const_mul C).hasDerivWithinAt (s := Icc 0 T)
    simpa only [f,f',id_eq,mul_one,Pi.inv_apply] using hi.fun_add hl
  have hfn (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ f' r := by
    have hdv : X' r/(1+X r)^2 ≤ C := (div_le_iff₀ (sq_pos_of_pos (hp r hr))).mpr (by
      simpa only [mul_comm C] using hb r hr)
    dsimp [f']
    rw [neg_div]
    linarith
  have hm : MonotoneOn f (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc
      (fun r hr => (hfd r (interior_subset hr)).mono interior_subset)
      (fun r hr => hfn r (interior_subset hr))
  have hmono := hm hz ht ht.1
  dsimp [f] at hmono
  have hCt : C*t ≤ (1+X 0)⁻¹/2 :=
    (mul_le_mul_of_nonneg_left ht.2 hC).trans hsmall
  have hi : (1 : ℝ)/(2*(1+X 0)) ≤ 1/(1+X t) := by
    have he : (1 : ℝ)/(2*(1+X 0))=(1+X 0)⁻¹/2 := by
      rw [mul_comm 2,div_mul_eq_div_div,one_div]
    rw [he,one_div]
    linarith
  have hcross := (div_le_div_iff₀ (mul_pos (by norm_num) (hp 0 hz)) (hp t ht)).mp hi
  nlinarith

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
   EulerVolterraConvolution Finset
open scoped ContDiff Topology

namespace SmoothingOperator

variable (S : SmoothingOperator)

theorem rhs_pairing (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp,(wordField (S.rhs A.toLp) w).toLp⟫_ℝ =
      ⟪(wordField (S.field A.toLp) w).toLp,
        (wordField (fieldNeg (advectionField (S.field A.toLp) (S.field A.toLp))) w).toLp⟫_ℝ := by
  simp only [rhs,wordField_neg,toLp_fieldNeg,inner_neg_right,field_word,← S.symmetric]

theorem rhs_energy (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) :
    integerEnergyProduction m A (S.rhs A.toLp) ≤ tameEnergyConstant m*M*wordEnergy m A := by
  let B := S.field A.toLp
  have he : fieldNeg (advectionField B B)=eulerRhs B (fieldSub B B) := by
    apply field_ext
    funext x
    simp only [fieldNeg_field,advectionField_field,eulerRhs_field,fieldSub_field,sub_self,sub_zero]
  have hp : (fieldSub B B).toLp ∈ gradientSpace := by
    rw [toLp_fieldSub,sub_self]
    exact gradientSpace.zero_mem
  have hb : B.toLp ∈ solenoidalSpace := by
    rw [field_toLp]
    exact S.solenoidal _
  have hx : integerEnergyProduction m A (S.rhs A.toLp) =
      integerEnergyProduction m B (eulerRhs B (fieldSub B B)) := by
    simp only [integerEnergyProduction,S.rhs_pairing,← he,B]
  rw [hx]
  apply (integer_energy_tame B (fieldSub B B) m hm M
    (S.field_wordBound A 3 M hM) (S.field_divergence A.toLp) hb hp).trans
  exact mul_le_mul_of_nonneg_left (S.field_energy_le A m)
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg hM))

end SmoothingOperator

namespace RegularizedEvolution

variable {S : SmoothingOperator} {T : ℝ} {hT : 0 ≤ T} (U : RegularizedEvolution S T hT)

/-- Energy, given by `⟨fun t => wordEnergy m (U.velocity t),wordEnergy_continuous U.velocity
U.velocity_continuous m⟩`. -/
def energy (m : ℕ) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => wordEnergy m (U.velocity t),wordEnergy_continuous U.velocity U.velocity_continuous m⟩

/-- Energy derivative, given by `integerEnergyProduction m (U.velocity t) (U.derivative t)`. -/
def energyDerivative (m : ℕ) (t : Icc (0 : ℝ) T) : ℝ :=
  integerEnergyProduction m (U.velocity t) (U.derivative t)

theorem energy_time (m : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energy m)) (U.energyDerivative m t) (Icc (0 : ℝ) T) t := by
  apply wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
  intro r hr x
  exact (U.pointwise_time ⟨r,hr.1.le,hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem energy_tame (m : ℕ) (hm : 3 ≤ m) (M : ℝ) (t : Icc (0 : ℝ) T)
    (hM : WordBound 3 M (U.velocity t)) :
    U.energyDerivative m t ≤ tameEnergyConstant m*M*U.energy m t :=
  S.rhs_energy (U.velocity t) m hm M hM

theorem energy_quadratic (t : Icc (0 : ℝ) T) :
    U.energyDerivative 3 t ≤ tameEnergyConstant 3*(1+U.energy 3 t)^2 := by
  have h := U.energy_tame 3 (le_refl 3) _ t (wordBound_sqrt_energy 3 (U.velocity t))
  change U.energyDerivative 3 t ≤ tameEnergyConstant 3*Real.sqrt (U.energy 3 t)*U.energy 3 t at h
  apply h.trans
  have hx : 0 ≤ U.energy 3 t := wordEnergy_nonneg 3 _
  have hr : 0 ≤ Real.sqrt (U.energy 3 t) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hx
  have hsq : Real.sqrt (U.energy 3 t)*U.energy 3 t ≤ (1+U.energy 3 t)^2 := by
    have hl : Real.sqrt (U.energy 3 t) ≤ 1+U.energy 3 t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hl hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq (tameEnergyConstant_nonneg 3)

theorem short_energy (hsmall : tameEnergyConstant 3 * T ≤ (1 + U.energy 3 ⟨0, le_rfl, hT⟩)⁻¹ / 2)
    (t : Icc (0 : ℝ) T) : U.energy 3 t ≤ 2*U.energy 3 ⟨0,le_rfl,hT⟩+1 := by
  have hp (r : ℝ) (hr : r ∈ Icc 0 T) : projIcc 0 T hT r=⟨r,hr⟩ := projIcc_of_mem hT hr
  have h := quadratic_energy_bound T (tameEnergyConstant 3) hT
    (extendPath T hT (U.energy 3)) (fun r => U.energyDerivative 3 (projIcc 0 T hT r))
    ((U.energy 3).continuous.comp continuous_projIcc).continuousOn
    (fun r _hr => wordEnergy_nonneg 3 (U.velocity (projIcc 0 T hT r)))
    (fun r hr => by simpa only [hp r hr] using U.energy_time 3 ⟨r,hr⟩)
    (fun r _hr => U.energy_quadratic (projIcc 0 T hT r)) (tameEnergyConstant_nonneg 3)
    (by simpa only [extendPath,hp 0 ⟨le_rfl,hT⟩] using hsmall) t t.property
  simpa only [extendPath,hp (t : ℝ) t.property,hp 0 ⟨le_rfl,hT⟩] using h

theorem energy_uniform (m : ℕ) (hm : 3 ≤ m) (M : ℝ)
    (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩) *
      Real.exp (tameEnergyConstant m*M*T) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.energy m))
        (U.energyDerivative m (projIcc 0 T hT r)) (Icc 0 T) r := by
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using
      U.energy_time m ⟨r,hr.1,hr.2.le⟩
  have he := linear_stability_within (extendPath T hT (U.energy m))
    (fun r => U.energyDerivative m (projIcc 0 T hT r)) (tameEnergyConstant m*M) T
    ((U.energy m).continuous.comp continuous_projIcc).continuousOn hd
    (fun r _hr => U.energy_tame m hm M (projIcc 0 T hT r) (hM _)) t t.property
  have hi : wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩) *
      Real.exp (tameEnergyConstant m*M*t) := by
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),energy,ContinuousMap.coe_mk]
          using he
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg m _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left t.property.2
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg (hM t)))

end RegularizedEvolution

/-- Regularized time, given by `(2*(1+tameEnergyConstant 3)*(1+wordEnergy 3 A))⁻¹`. -/
def regularizedTime (A : SmoothL2Field Space) : ℝ :=
  (2*(1+tameEnergyConstant 3)*(1+wordEnergy 3 A))⁻¹

theorem regularizedTime_pos (A : SmoothL2Field Space) : 0 < regularizedTime A := by
  have := tameEnergyConstant_nonneg 3
  have := wordEnergy_nonneg 3 A
  unfold regularizedTime
  positivity

/-- Regularized H3, given by `Real.sqrt (2*wordEnergy 3 A+1)`. -/
def regularizedH3 (A : SmoothL2Field Space) : ℝ := Real.sqrt (2*wordEnergy 3 A+1)

theorem regularized_h3 (A : SmoothL2Field Space) {S : SmoothingOperator}
    (U : RegularizedEvolution S (regularizedTime A) (regularizedTime_pos A).le)
    (hinit : U.velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = A)
    (t : Icc (0 : ℝ) (regularizedTime A)) : WordBound 3 (regularizedH3 A) (U.velocity t) := by
  have he : U.energy 3 ⟨0,le_rfl,(regularizedTime_pos A).le⟩=wordEnergy 3 A := congrArg (wordEnergy
      3) hinit
  have hc : 0 < 1+tameEnergyConstant 3 := by linarith [tameEnergyConstant_nonneg 3]
  have ha : 0 < 1+wordEnergy 3 A := by linarith [wordEnergy_nonneg 3 A]
  have hs : tameEnergyConstant 3*regularizedTime A ≤ (1+wordEnergy 3 A)⁻¹/2 := by
    calc
      _ ≤ (1+tameEnergyConstant 3)*regularizedTime A := by
        nlinarith [regularizedTime_pos A]
      _ = _ := by unfold regularizedTime; field_simp [hc.ne',ha.ne']
  have hu := U.short_energy (by simpa only [he] using hs) t
  rw [he] at hu
  intro n hn w
  exact (wordBound_sqrt_energy 3 (U.velocity t) n hn w).trans (Real.sqrt_le_sqrt hu)

theorem regularized_all_order (A : SmoothL2Field Space) (q : ℕ) :
    ∃ C : ℝ, ∀ (S : SmoothingOperator)
      (U : RegularizedEvolution S (regularizedTime A) (regularizedTime_pos A).le),
      U.velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A →
      ∀ t, tensorNorm q (U.velocity t) ≤ C := by
  let m := max 3 q
  refine ⟨wordCount q*Real.sqrt (wordEnergy m A *
    Real.exp (tameEnergyConstant m*regularizedH3 A*regularizedTime A)),?_⟩
  intro S U hinit t
  have hu := U.energy_uniform m (le_max_left 3 q) (regularizedH3 A)
    (regularized_h3 A U hinit) t
  rw [hinit] at hu
  apply tensorNorm_le_wordCount
  intro n hn w
  exact (wordBound_sqrt_energy m (U.velocity t) n (hn.trans (le_max_right 3 q)) w).trans
    (Real.sqrt_le_sqrt hu)

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral Finset
open scoped ContDiff Topology

namespace RegularizedEvolution

variable {T : ℝ} {hT : 0 ≤ T} {S : SmoothingOperator} (U : RegularizedEvolution S T hT)

/-- Derivative path, given by `fieldPath U.derivative U.derivative_continuous`. -/
def derivativePath : C(Icc (0 : ℝ) T,L2) := fieldPath U.derivative U.derivative_continuous

theorem integral_equation (t : Icc (0 : ℝ) T) :
    (U.velocity t).toLp=(U.velocity ⟨0,le_rfl,hT⟩).toLp +
      integral T hT U.derivativePath t := by
  have h := eq_initial_add_integral T hT U.derivativePath
    (fun r => (U.velocity (projIcc 0 T hT r)).toLp) U.l2_time t
  simpa only [projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using h

end RegularizedEvolution

namespace SmoothLimitData

variable {T : ℝ} {hT : 0 ≤ T} {U : ∀ n, RegularizedEvolution (regularizer n) T hT}
  (L : SmoothLimitData (fun n => (U n).velocity) (fun n => (U n).velocity_continuous))

theorem regularized_solenoidal (t : Icc (0 : ℝ) T) : (L.field t).toLp ∈ solenoidalSpace :=
  gradientSpace.isClosed_orthogonal.mem_of_tendsto (L.toLp_convergence t)
    (Eventually.of_forall (fun n => (U n).solenoidal t))

theorem regularized_derivative_convergence (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    Tendsto (fun n => (U n).derivativePath) atTop
      (𝓝 (projectedRhsPath L.field L.field_continuous)) := by
  have hp := L.projectedRhsPath_convergence hT (40*M)
    (fun n t => tensorNorm_three_le _ M (wordBound_mono (hM n t) (by omega)))
  have he (n : ℕ) :
      ‖(U n).derivativePath-projectedRhsPath (U n).velocity (U n).velocity_continuous‖ ≤
        regularizerError n*regularizationCost M := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (regularizerError_nonneg n)
      (regularizationCost_nonneg M))).mpr
    intro t
    exact regularized_rhs_error n _ ((U n).solenoidal t) M (hM n t)
  have hz : Tendsto (fun n => (U n).derivativePath -
      projectedRhsPath (U n).velocity (U n).velocity_continuous) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) he
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (regularizationCost M)
  have h := hz.add hp
  simpa only [sub_add_cancel,zero_add] using h

theorem regularized_integral_equation (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) (t : Icc (0 : ℝ) T) :
    (L.field t).toLp=(L.field ⟨0,le_rfl,hT⟩).toLp +
      integral T hT (projectedRhsPath L.field L.field_continuous) t := by
  have hi := (ContinuousMap.evalCLM ℝ t).continuous.tendsto
    (integral T hT (projectedRhsPath L.field L.field_continuous)) |>.comp
      (((integral (E := L2) T hT).continuous.tendsto _).comp
        (L.regularized_derivative_convergence M hM))
  have hs := (L.toLp_convergence ⟨0,le_rfl,hT⟩).add hi
  exact tendsto_nhds_unique (L.toLp_convergence t)
    (hs.congr (fun n => ((U n).integral_equation t).symm))

theorem regularized_time (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (L.field (projIcc 0 T hT r)).toLp)
      (projectedRhs (L.field t)).toLp (Icc (0 : ℝ) T) t := by
  have he : (fun r => (L.field (projIcc 0 T hT r)).toLp) =
      fun r => (L.field ⟨0,le_rfl,hT⟩).toLp +
        extendPath T hT (integral T hT (projectedRhsPath L.field L.field_continuous)) r := by
    funext r
    exact L.regularized_integral_equation M hM (projIcc 0 T hT r)
  rw [he]
  exact (integral_hasDerivWithinAt T hT (projectedRhsPath L.field L.field_continuous) t).const_add _

/-- Regularized evolution, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def regularizedEvolution (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    Evolution T hT where
  velocity := L.field
  pressureForce t := pressureField (L.field t)
  velocity_continuous := L.field_continuous
  pressure_continuous := pressureField_continuous L.field L.field_continuous
  solenoidal := L.regularized_solenoidal
  gradient t := pressureField_mem_gradient (L.field t)
  time_law t ht x := by
    have hd : ∀ r (hr : r ∈ Ioo 0 T),
        HasDerivAt (fun s => (L.field (projIcc 0 T hT s)).toLp)
          (projectedRhs (L.field ⟨r,hr.1.le,hr.2.le⟩)).toLp r := by
      intro r hr
      exact (L.regularized_time M hM ⟨r,hr.1.le,hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have h := pointwise_derivative_of_l2 T hT L.field (fun s => projectedRhs (L.field s))
      L.field_continuous (projectedRhs_continuous L.field L.field_continuous) hd
      ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end SmoothLimitData

/-- Regularized solution, given by `Classical.choose ((regularizer n).exists_smooth
(regularizedTime A) (regularizedTime_pos A).le A hA)`. -/
def regularizedSolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (n : ℕ) :
    RegularizedEvolution (regularizer n) (regularizedTime A) (regularizedTime_pos A).le :=
  Classical.choose ((regularizer n).exists_smooth (regularizedTime A) (regularizedTime_pos A).le A
      hA)

theorem regularizedSolution_initial (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (n :
    ℕ) :
    (regularizedSolution A hA n).velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A :=
  Classical.choose_spec ((regularizer n).exists_smooth (regularizedTime A) (regularizedTime_pos
      A).le A hA)

theorem regularizedSolution_bounds (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∀ q, ∃ M : ℝ, ∀ n t, tensorNorm q ((regularizedSolution A hA n).velocity t) ≤ M := by
  intro q
  obtain ⟨M,hM⟩ := regularized_all_order A q
  exact ⟨M,fun n t => hM _ _ (regularizedSolution_initial A hA n) t⟩

theorem regularizedSolution_cauchy (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    CauchySeq (fun n => fieldPath (regularizedSolution A hA n).velocity
      (regularizedSolution A hA n).velocity_continuous) := by
  obtain ⟨M,hM⟩ := regularizedSolution_bounds A hA 4
  apply regularized_cauchy (regularizedSolution A hA) M
    (fun n t k hk w => (wordBound_tensorNorm 4 _ k hk w).trans (hM n t))
  intro j k
  simp only [regularizedSolution_initial]

/-- Local limit, given by `smoothLimitData (regularizedTime_pos A).le _ _
(regularizedSolution_bounds A hA) (regularizedSolution_cauchy A hA)`. -/
def localLimit (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    SmoothLimitData (fun n => (regularizedSolution A hA n).velocity)
      (fun n => (regularizedSolution A hA n).velocity_continuous) :=
  smoothLimitData (regularizedTime_pos A).le _ _
    (regularizedSolution_bounds A hA) (regularizedSolution_cauchy A hA)

/-- Local evolution, choosing the witness provided by `regularizedSolution_bounds`. -/
def localEvolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    Evolution (regularizedTime A) (regularizedTime_pos A).le :=
  (localLimit A hA).regularizedEvolution (Classical.choose (regularizedSolution_bounds A hA 4))
    (fun n t k hk w => (wordBound_tensorNorm 4 _ k hk w).trans
      (Classical.choose_spec (regularizedSolution_bounds A hA 4) n t))

theorem localEvolution_initial (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    (localEvolution A hA).velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A := by
  apply smoothField_eq_of_toLp_eq
  have h := (localLimit A hA).toLp_convergence ⟨0,le_rfl,(regularizedTime_pos A).le⟩
  simp only [regularizedSolution_initial] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem exists_local_evolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ (T : ℝ) (hT : 0 < T), ∃ U : Evolution T hT.le,
      U.velocity ⟨0,le_rfl,hT.le⟩=A :=
  ⟨regularizedTime A,regularizedTime_pos A,localEvolution A hA,localEvolution_initial A hA⟩

end EulerOrdinarySobolev
