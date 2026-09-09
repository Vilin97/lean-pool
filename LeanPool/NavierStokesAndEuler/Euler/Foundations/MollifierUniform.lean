/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierRepresentative
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

/-! Uniform control of every classical derivative word by actual strong Sobolev jets. -/

@[expose] public section

noncomputable section

namespace EulerMollifierUniform

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerSpatialSobolevInverse
  EulerStrongSmoothJet EulerCylinderMollifier EulerMollifierRepresentative
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An arbitrary derivative word has H³ norm controlled by the full norm three orders higher. -/
theorem word_H3_le_higher {m : ℕ} (w : Fin m → Fin 4) (f : LiftDomain period → Vector3) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period (m + 3) f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period (m + 3) f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

/-- Every actual smooth derivative word is uniformly controlled by its genuine strong jet. -/
theorem jet_word_pointwise_bound {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (f : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * J.sobolevNorm) := by
  have hLp : ∀ j ≤ m + 3, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period) :=
    fun j hj u => jet_classical_memLp period hj U J u f hrep hf
  have hA := vector_cylinder_pointwise_le_H3 period 3 (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ m+3) v w f hLp) x
  have hB := word_H3_le_higher period w f
  rw [← jet_sobolevNorm_eq period U J f hrep hf] at hB
  exact hA.trans (mul_le_mul_of_nonneg_left hB
    (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))

omit [Fact (0 < period)] in
theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    fieldDerivative period a (fun y => f y - g y) x =
      fieldDerivative period a f x - fieldDerivative period a g x := by
  have h := ((((hf x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)).sub
    (((hg x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0))).fderiv
  have h' := congrArg (fun L : LiftTangent →L[ℝ] Vector3 => L a) h
  simpa +unfoldPartialApp [fieldDerivative, localFieldLift, Pi.sub_def] using h'

omit [Fact (0 < period)] in
theorem word_sub {m : ℕ} (w : Fin m → Fin 4) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    iteratedFieldDerivative period w (fun y => f y - g y) =
      fun x => iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w)]
    funext x
    exact fieldDerivative_sub period (standardDirection (w 0)) _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)
      (iteratedFieldDerivative_smooth period (Fin.tail w) g hg) x

/-- Uniform derivative differences are controlled by the actual L² Sobolev difference jet. -/
theorem jet_word_difference_bound {m : ℕ} (U V : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U)
    (K : SpatialJet period standardDirection (m + 3) V) (w : Fin m → Fin 4)
    (f g : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hrepG : (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * (J.sub K).sobolevNorm) := by
  have hrepD : ((U - V : LiftL2 period) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      fun x => f x - g x := by
    filter_upwards [Lp.coeFn_sub U V, hrep, hrepG] with y hy hfy hgy
    simpa [hfy, hgy] using hy
  have h := jet_word_pointwise_bound period (U - V) (J.sub K) w (fun x => f x - g x)
    hrepD (fun x => (hf x).sub (hg x)) x
  simpa only [word_sub period w f g hf hg] using h

/-- A genuine Sobolev difference is bounded through any third jet at the same order. -/
theorem jet_sub_triangle {s : ℕ} {U V W : LiftL2 period}
    (J : SpatialJet period standardDirection s U) (K : SpatialJet period standardDirection s V)
    (L : SpatialJet period standardDirection s W) :
    (J.sub K).sobolevNorm ≤ (J.sub L).sobolevNorm + (K.sub L).sobolevNorm := by
  simp only [SpatialJet.sobolevNorm_eq_sum_words, sub_word]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  calc
    ‖J.word w - K.word w‖ = ‖(J.word w - L.word w) + (L.word w - K.word w)‖ := by congr 1; abel
    _ ≤ ‖J.word w - L.word w‖ + ‖L.word w - K.word w‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (L.word w) (K.word w)]

/-- Every actual classical derivative word of the mollifiers is uniformly Cauchy. -/
theorem smoothMollifier_word_uniformCauchy {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    UniformCauchySeqOn (fun n x => iteratedFieldDerivative period w (smoothMollifier period n U) x)
      Filter.atTop Set.univ := by
  let C : ℝ := (3 * cylinderEmbeddingConstant period) * 85
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by
        norm_num) (cylinderEmbeddingConstant_nonneg period)) (by norm_num)
  have hlim : Filter.Tendsto (fun n => C * ((mollifyJet period J n).sub J).sobolevNorm)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (mollifyJet_sobolevNorm_tendsto period J).const_mul C
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, fun a ha b hb x _ => ?_⟩
  have hab := jet_word_difference_bound period (mollify period a U) (mollify period b U)
    (mollifyJet period J a) (mollifyJet period J b) w
    (smoothMollifier period a U) (smoothMollifier period b U)
    (mollify_ae_smoothMollifier period a U) (mollify_ae_smoothMollifier period b U)
    (smoothMollifier_smooth period a U) (smoothMollifier_smooth period b U) x
  have htri := jet_sub_triangle period (mollifyJet period J a) (mollifyJet period J b) J
  have hna := hN a ha
  have hnb := hN b hb
  calc
    _ = ‖iteratedFieldDerivative period w (smoothMollifier period a U) x -
        iteratedFieldDerivative period w (smoothMollifier period b U) x‖ := dist_eq_norm _ _
    _ ≤ (3 * cylinderEmbeddingConstant period) *
        (85 * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm) := hab
    _ = C * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm := by dsimp [C]; ring
    _ ≤ C * (((mollifyJet period J a).sub J).sobolevNorm +
        ((mollifyJet period J b).sub J).sobolevNorm) := mul_le_mul_of_nonneg_left htri hC
    _ < ε := by linarith

/-- Completeness produces a uniform limit for every actual derivative word. -/
theorem exists_smoothMollifier_word_uniform_limit {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    ∃ g : LiftDomain period → Vector3,
      TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n U))
        g Filter.atTop := by
  have hC := smoothMollifier_word_uniformCauchy period U J w
  have hex : ∀ x : LiftDomain period, ∃ v : Vector3,
      Filter.Tendsto (fun n => iteratedFieldDerivative period w (smoothMollifier period n U) x)
        Filter.atTop (𝓝 v) := fun x => cauchySeq_tendsto_of_complete (hC.cauchySeq (Set.mem_univ x))
  choose g hg using hex
  exact ⟨g, tendstoUniformlyOn_univ.mp (hC.tendstoUniformlyOn_of_tendsto (fun x _ => hg x))⟩

/-- The uniform classical word limit represents the actual strong L² derivative word. -/
theorem smoothMollifier_word_limit_ae {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (g : LiftDomain period → Vector3)
    (hlim : TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n
        U))
      g Filter.atTop) : (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  obtain ⟨index, hindex, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (mollify_tendsto period (J.word w))).exists_seq_tendsto_ae'
  have hrep : ∀ᵐ x ∂liftMeasure period, ∀ n : ℕ,
      mollify period (index n) (J.word w) x =
        iteratedFieldDerivative period w (smoothMollifier period (index n) U) x :=
    ae_all_iff.mpr (fun n => smoothMollifier_word_ae period (by omega) U J (index n) w)
  filter_upwards [hsub, hrep] with x hx hxr
  have heq : (fun n => mollify period (index n) (J.word w) x) =
      fun n => iteratedFieldDerivative period w (smoothMollifier period (index n) U) x := funext hxr
  rw [heq] at hx
  exact tendsto_nhds_unique hx ((hlim.tendsto_at x).comp hindex)

/-- Strong H³ cylinder jets have genuine continuous representatives. -/
theorem exists_continuous_representative (U : LiftL2 period)
    (J : SpatialJet period standardDirection 3 U) :
    ∃ g : LiftDomain period → Vector3, Continuous g ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U J w
  refine ⟨g, ?_, ?_⟩
  · apply hg.continuous
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall fun n =>
      smoothField_continuous period _ (smoothMollifier_smooth period n U)
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U J w g hg

end EulerMollifierUniform
