/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.EuclideanSphere
public import LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Foundations.EuclideanSphere
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition

/-!
# Hopf problem: recognition · smale 7

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def Smale.StripCoordinates.reverse (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, p.2)

private theorem Smale.StripCoordinates.contDiff_reverse : ContDiff ℝ ∞ reverse :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

private theorem Smale.StripCoordinates.reverse_one_zero : reverse (1, 0) = (0, 0) := by
  simp only [reverse, sub_self]

private theorem
    Smale.StripCoordinates.vertical_derivative_reverse {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} (hH : DifferentiableAt ℝ H (0, 0)) :
    fderiv ℝ (H ∘ reverse) (1, 0) (0, 1) = fderiv ℝ H (0, 0) (0, 1) := by
  have houter : DifferentiableAt ℝ H (reverse (1, 0)) := by
    rw [reverse_one_zero]
    exact hH
  have hcomp : DifferentiableAt ℝ (H ∘ reverse) (1, 0) :=
    houter.comp (1, 0) (contDiff_reverse.contDiffAt.differentiableAt (by simp))
  have hleft := hasDerivAt_verticalSlice hcomp
  have hright := hasDerivAt_verticalSlice hH
  have heq : (fun s : ℝ => (H ∘ reverse) (1, s)) = fun s => H (0, s) := by
    funext s
    simp only [Function.comp_apply, reverse, sub_self]
  rw [heq] at hleft
  exact hleft.unique hright

private def Smale.WhitneyPairModel.cornerTransition (t : ℝ) : ℝ :=
  Real.smoothTransition (3 * t - 1)

private def Smale.WhitneyPairModel.cornerScale (t : ℝ) : ℝ :=
  (1 - cornerTransition t) * (1 - t) + cornerTransition t * t

private def Smale.WhitneyPairModel.cornerSign (t : ℝ) : ℝ :=
  2 * cornerTransition t - 1

private theorem
    Smale.WhitneyPairModel.contDiff_cornerTransition : ContDiff ℝ ∞ cornerTransition := by
  unfold cornerTransition
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem Smale.WhitneyPairModel.cornerTransition_zero {t : ℝ} (ht : t ≤ 1 / 3) :
    cornerTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem Smale.WhitneyPairModel.cornerTransition_one {t : ℝ} (ht : 2 / 3 ≤ t) :
    cornerTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem Smale.WhitneyPairModel.cornerScale_pos (t : ℝ) : 0 < cornerScale t := by
  by_cases hlo : t ≤ 1 / 3
  · simp only [cornerScale, cornerTransition_zero hlo, sub_zero, one_mul, MulZeroClass.zero_mul,
      add_zero]
    linarith
  by_cases hhi : 2 / 3 ≤ t
  · simp only [cornerScale, cornerTransition_one hhi, sub_self, MulZeroClass.zero_mul, one_mul,
      zero_add]
    linarith
  have h0 : 0 ≤ cornerTransition t := Real.smoothTransition.nonneg _
  have h1 : cornerTransition t ≤ 1 := Real.smoothTransition.le_one _
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  by_cases hβ : cornerTransition t = 0
  · simp only [cornerScale, hβ, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero]
    exact ht1
  · exact
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr h1) ht1.le)
        (mul_pos (lt_of_le_of_ne h0 (Ne.symm hβ)) ht0)

private theorem Smale.WhitneyPairModel.contDiff_cornerScale : ContDiff ℝ ∞ cornerScale := by
  exact
    ((contDiff_const.sub contDiff_cornerTransition).mul (contDiff_const.sub contDiff_id)).add
      (contDiff_cornerTransition.mul contDiff_id)

private theorem Smale.WhitneyPairModel.contDiff_cornerSign : ContDiff ℝ ∞ cornerSign :=
  (contDiff_const.mul contDiff_cornerTransition).sub contDiff_const

private def Smale.WhitneyPairModel.exchangeEdges (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, h * (1 - p.1 ^ 2) - p.2)

private theorem
    Smale.WhitneyPairModel.contDiff_exchangeEdges (h : ℝ) : ContDiff ℝ ∞ (exchangeEdges h) := by
  unfold exchangeEdges
  fun_prop

private theorem Smale.WhitneyPairModel.exchangeEdges_involutive (h : ℝ) :
    Function.Involutive (exchangeEdges h) := by
  intro p
  apply Prod.ext <;> dsimp [exchangeEdges]
  ring

private def Smale.WhitneyPairModel.lowerStripCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p + cornerSign (arcTime p) * (p.2 / (4 * h * cornerScale (arcTime p))),
    p.2 / (4 * h * cornerScale (arcTime p)))

private def Smale.WhitneyPairModel.upperStripCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  lowerStripCoordinates h ∘ exchangeEdges h

private theorem Smale.WhitneyPairModel.contDiff_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (lowerStripCoordinates h) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 / (4 * h * cornerScale (arcTime p))) :=
    contDiff_snd.div (contDiff_const.mul (contDiff_cornerScale.comp contDiff_arcTime))
      (fun p => mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne')
  exact (contDiff_arcTime.add ((contDiff_cornerSign.comp contDiff_arcTime).mul hd)).prodMk hd

private theorem Smale.WhitneyPairModel.contDiff_upperStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (upperStripCoordinates h) :=
  (contDiff_lowerStripCoordinates hh).comp (contDiff_exchangeEdges h)

private theorem Smale.WhitneyPairModel.lowerStripCoordinates_lower (h t : ℝ) :
    lowerStripCoordinates h (2 * t - 1, 0) = (t, 0) := by
  simp only [lowerStripCoordinates, arcTime, zero_div, MulZeroClass.mul_zero, add_zero]
  congr 1
  ring

private theorem Smale.WhitneyPairModel.upperStripCoordinates_upper (h t : ℝ) :
    upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = (t, 0) := by
  simp only [upperStripCoordinates, Function.comp_apply, exchangeEdges, sub_self]
  exact lowerStripCoordinates_lower h t

private theorem Smale.WhitneyPairModel.lowerStripCoordinates_left (h : ℝ) {p : ℝ × ℝ}
    (hp : arcTime p ≤ 1 / 3) : lowerStripCoordinates h p = leftCornerCoordinates h p := by
  simp [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_zero hp,
    leftCornerCoordinates, sub_eq_add_neg]

private theorem Smale.WhitneyPairModel.upperStripCoordinates_left {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≤ 1 / 3) : upperStripCoordinates h p = (leftCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  have hp' : arcTime p ≠ 1 := by linarith
  change lowerStripCoordinates h (exchangeEdges h p) = _
  rw [lowerStripCoordinates_left h (htime ▸ hp)]
  exact leftCornerCoordinates_exchange hh hp'

private theorem Smale.WhitneyPairModel.lowerStripCoordinates_right (h : ℝ) {p : ℝ × ℝ}
    (hp : 2 / 3 ≤ arcTime p) :
    Smale.StripCoordinates.reverse (lowerStripCoordinates h p) = rightCornerCoordinates h p := by
  have hden : 1 - arcTime (bigonReflection p) = arcTime p := by
    rw [arcTime_bigonReflection]
    ring
  simp only [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_one hp, sub_self,
    MulZeroClass.zero_mul, one_mul, zero_add]
  norm_num only [mul_one, sub_self, sub_zero]
  change
    (1 - (arcTime p + 1 * (p.2 / (4 * h * arcTime p))), p.2 / (4 * h * arcTime p)) =
      leftCornerCoordinates h (bigonReflection p)
  simp only [leftCornerCoordinates]
  rw [hden, arcTime_bigonReflection]
  simp only [bigonReflection_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

private theorem Smale.WhitneyPairModel.upperStripCoordinates_right {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : 2 / 3 ≤ arcTime p) :
    Smale.StripCoordinates.reverse (upperStripCoordinates h p) =
      (rightCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  change Smale.StripCoordinates.reverse (lowerStripCoordinates h (exchangeEdges h p)) = _
  rw [lowerStripCoordinates_right h (htime ▸ hp)]
  have heq :
    bigonReflection (exchangeEdges h p) =
      ((bigonReflection p).1, h * (1 - (bigonReflection p).1 ^ 2) - (bigonReflection p).2) := by
    simp only [bigonReflection_apply, exchangeEdges, neg_sq]
  change leftCornerCoordinates h (bigonReflection (exchangeEdges h p)) = _
  rw [heq]
  apply leftCornerCoordinates_exchange hh
  rw [arcTime_bigonReflection]
  linarith

private def Smale.TransverseCoordinates.cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) :
    (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

private theorem Smale.TransverseCoordinates.cornerLinear_apply {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) :=
  rfl

private theorem
    Smale.TransverseCoordinates.injective_cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Function.Injective (cornerLinear u v) := by
  intro p q hpq
  exact
    Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
      ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

private def
    Smale.TransverseCoordinates.cornerMap {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) : (ℝ × ℝ) → M :=
  Φ ∘ cornerLinear u v

private theorem
    Smale.TransverseCoordinates.contMDiffOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

private theorem Smale.TransverseCoordinates.injOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Set.InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

private theorem Smale.TransverseCoordinates.injective_mfderiv_cornerMap {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap,
    mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp) (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (Smale.PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

private theorem Smale.exists_native_clean_corner_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (c 0) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (c (s • u))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (d (t • v))) := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy hdim ht hO
      hxO
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  refine
    ⟨W, Φ.open_source.preimage L.continuous, h0W, k,
      TransverseCoordinates.contMDiffOn_cornerMap Φ u v,
      TransverseCoordinates.injOn_cornerMap Φ hu hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · change Φ (L 0) = F (c 0)
    rw [map_zero]
    exact hcenter
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using him
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at ht
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

private structure Smale.CleanCornerPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) where
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_zero : (0 : ℝ × ℝ) ∈ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  sheets : ∀ p ∈ domain, (map p ∈ S ↔ p.2 = 0) ∧ (map p ∈ T ↔ p.1 = 0)
  axis_first : ∀ t, (t, 0) ∈ domain → map (t, 0) = a t
  axis_second : ∀ t, (0, t) ∈ domain → map (0, t) = b t

private def Smale.CleanCornerPatch.swap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    (c : Smale.CleanCornerPatch (E := E) S T a b) : Smale.CleanCornerPatch (E := E) T S b a := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e : (ℝ × ℝ) → ℝ × ℝ) := e.contDiff.contMDiff
  refine
    { domain := e ⁻¹' c.domain
      open_domain := c.open_domain.preimage e.continuous
      contains_zero := ?_
      map := c.map ∘ e
      smooth := c.smooth.comp he.contMDiffOn (fun _ hp => hp)
      injective := ?_
      derivative_injective := ?_
      sheets := fun p hp => ⟨(c.sheets (e p) hp).2, (c.sheets (e p) hp).1⟩
      axis_first := fun t ht => c.axis_second t ht
      axis_second := fun t ht => c.axis_first t ht }
  · change e 0 ∈ c.domain
    rw [map_zero]
    exact c.contains_zero
  · intro p hp q hq hpq
    exact e.injective (c.injective hp hq hpq)
  · intro p hp
    have hc := c.smooth.contMDiffAt (c.open_domain.mem_nhds hp)
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact
      (c.derivative_injective (e p) hp).comp
        (Smale.PartialChart.bijective_mfderiv e.toDiffeomorph.toPartialDiffeomorph
            (Set.mem_univ p)).1

private structure Smale.CleanStripPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a : ℝ → M) (k₀ k₁ : (ℝ × ℝ) → M) where
  width : ℝ
  width_pos : 0 < width
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_strip : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width ⊆ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  closed_embedding :
    Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width => map p)
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  first_sheet : ∀ p ∈ domain, map p ∈ S ↔ p.2 = 0
  second_sheet : ∀ p ∈ domain, map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1
  center : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (t, 0) = a t
  left_germ : map =ᶠ[𝓝 (0, 0)] k₀
  right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse

private theorem
    Smale.bigon_strip_maps_left_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (-1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 0 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 0 using 1
    norm_num
  have hk :=
    k.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hx]
        exact (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt)
  have hl :=
    l.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hy]
        exact (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt)
  have hnear : ∀ᶠ p in 𝓝 ((-1 : ℝ), (0 : ℝ)), WhitneyPairModel.arcTime p ≤ 1 / 3 := by
    have ht : WhitneyPairModel.arcTime (-1, 0) < 1 / 3 := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_lt_const ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp, WhitneyPairModel.lowerStripCoordinates_left h hp,
    WhitneyPairModel.upperStripCoordinates_left hh hp]
  change
    c₀.map (WhitneyPairModel.leftCornerCoordinates h p) =
      c₀.map ((WhitneyPairModel.leftCornerCoordinates h p).swap.swap)
  rw [Prod.swap_swap]

private theorem
    Smale.bigon_strip_maps_right_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 1 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 1 using 1
    norm_num
  have hk :=
    k.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hx] at ht
        exact ht)
  have hl :=
    l.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hy] at ht
        exact ht)
  have hnear : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 2 / 3 ≤ WhitneyPairModel.arcTime p := by
    have ht : 2 / 3 < WhitneyPairModel.arcTime (1, 0) := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_const_lt ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp]
  change
    c₁.map (StripCoordinates.reverse (WhitneyPairModel.lowerStripCoordinates h p)) =
      c₁.map ((StripCoordinates.reverse (WhitneyPairModel.upperStripCoordinates h p)).swap)
  rw [WhitneyPairModel.lowerStripCoordinates_right h hp,
    WhitneyPairModel.upperStripCoordinates_right hh hp, Prod.swap_swap]

private theorem
    Smale.exists_smooth_open_gluing {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y] [ChartedSpace F Y] {f g : X → Y} {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g V) (hfg : Set.EqOn f g (U ∩ V)) :
    ∃ k : X → Y, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k (U ∪ V) ∧ Set.EqOn k f U ∧ Set.EqOn k g V := by
  classical
  let k := U.piecewise f g
  have hkf : Set.EqOn k f U := fun x hx => Set.piecewise_eq_of_mem U f g hx
  have hkg : Set.EqOn k g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hkf hxU).trans (hfg ⟨hxU, hx⟩)
    · exact Set.piecewise_eq_of_notMem U f g hxU
  exact
    ⟨k, (hf.congr (fun _ hx => hkf hx)).union_of_isOpen (hg.congr (fun _ hx => hkg hx)) hU hV,
      hkf, hkg⟩

private theorem Smale.exists_smooth_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                  Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain ∧
                    Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain ∧
                      ∃ f : (ℝ × ℝ) → M,
                        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V) ∧
                          Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U ∧
                            Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                  f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) := by
  let Dlo := WhitneyPairModel.lowerStripCoordinates h ⁻¹' k.domain
  let Dhi := WhitneyPairModel.upperStripCoordinates h ⁻¹' l.domain
  have hDlo : IsOpen Dlo :=
    k.open_domain.preimage (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').continuous
  have hDhi : IsOpen Dhi :=
    l.open_domain.preimage (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').continuous
  have hkl :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) Dlo :=
    k.smooth.comp (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  have hlu :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (l.map ∘ WhitneyPairModel.upperStripCoordinates h) Dhi :=
    l.smooth.comp (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp (bigon_strip_maps_left_germ hh.ne' c₀ c₁ k l)
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_right_germ hh.ne' c₀ c₁ k l)
  have hlowD : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) Dlo := by
    intro t ht
    change WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0) ∈ k.domain
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have huppD :
    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) Dhi := by
    intro t ht
    change
      WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ l.domain
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  obtain ⟨U, V, hU, hV, hUD, hVD, hover, hlowU, huppV, hfront⟩ :=
    WhitneyPairModel.exists_bigon_boundary_cover hh hDlo hDhi (hO₀.union hO₁) (Or.inl hleft)
      (Or.inr hright) hlowD huppD
  have hfg :
    Set.EqOn (k.map ∘ WhitneyPairModel.lowerStripCoordinates h)
      (l.map ∘ WhitneyPairModel.upperStripCoordinates h) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨f, hf, hflo, hfhi⟩ := exists_smooth_open_gluing hU hV (hkl.mono hUD) (hlu.mono hVD) hfg
  refine
    ⟨U, V, hU, hV, hfront, hlowU, huppV, fun _ hp => hUD hp, fun _ hp => hVD hp, f, hf, hflo,
      hfhi, ?_, ?_⟩
  · intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  · intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht

private theorem Smale.StripCoordinates.injective_plane_of_horizontal_and_normal
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hh : L (1, 0) = (1, 0)) (hn : (L (0, 1)).2 ≠ 0) :
    Function.Injective L := by
  let i : (ℝ × ℝ) →L[ℝ] Space ℝ ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hh' : (i.comp L) (1, 0) = Smale.StripCoordinates.center 1 := by
    change i (L (1, 0)) = Smale.StripCoordinates.center 1
    rw [hh]
    rfl
  have hi := injective_of_horizontal_and_normal (i.comp L) hh' hn
  intro p q hpq
  exact hi (congrArg i hpq)

private def
    Smale.StripCoordinates.detector {A B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (v : ℝ → B) (F : (ℝ × ℝ) → Space A B) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪v p.1, (F p).2⟫_ℝ)

private theorem Smale.StripCoordinates.contDiff_detector {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (detector v F) :=
  contDiff_fst.prodMk ((hv.comp contDiff_fst).inner ℝ hF.snd)

private theorem Smale.StripCoordinates.detector_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hc : ∀ t, F (t, 0) = Smale.StripCoordinates.center t) (t : ℝ) :
    detector v F (t, 0) = (t, 0) := by
  simp only [detector, hc, Smale.StripCoordinates.center, inner_zero_right]

private theorem
    Smale.StripCoordinates.detector_vertical_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hn : ∀ t, normalDerivative F t = v t) (t : ℝ) :
    fderiv ℝ (detector v F) (t, 0) (0, 1) = (0, ⟪v t, v t⟫_ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => (F (t, s)).2) (v t) 0 := by
    have h :=
      hasDerivAt_verticalSlice (t := t) (s := 0) (hF.snd.contDiffAt.differentiableAt (by simp))
    change HasDerivAt _ (normalDerivative F t) 0 at h
    rwa [hn t] at h
  have hinner : HasDerivAt (fun s : ℝ => ⟪v t, (F (t, s)).2⟫_ℝ) (⟪v t, v t⟫_ℝ) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (v t)).inner ℝ hd
  have hslice : HasDerivAt (fun s : ℝ => detector v F (t, s)) (0, ⟪v t, v t⟫_ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk hinner
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_detector hv hF).contDiffAt.differentiableAt (by simp))).unique
      hslice

private theorem Smale.StripCoordinates.injective_fderiv_detector_at_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    {v : ℝ → B} {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = Smale.StripCoordinates.center t) (hn : ∀ t, normalDerivative F t = v t)
    {t : ℝ} (ht : v t ≠ 0) : Function.Injective (fderiv ℝ (detector v F) (t, 0)) := by
  have hQ : DifferentiableAt ℝ (detector v F) (t, 0) :=
    (contDiff_detector hv hF).contDiffAt.differentiableAt (by simp)
  have hh : fderiv ℝ (detector v F) (t, 0) (1, 0) = (1, 0) := by
    have hd := hasDerivAt_horizontalSlice hQ
    have heq : (fun s : ℝ => detector v F (s, 0)) = fun s => (s, 0) := funext (detector_zero hc)
    rw [heq] at hd
    exact hd.unique ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
  apply injective_plane_of_horizontal_and_normal _ hh
  rw [detector_vertical_derivative hv hF hn t]
  exact inner_self_ne_zero.mpr ht

private theorem
    Smale.WhitneyPairModel.lowerStripCoordinates_horizontal_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0) = (1 / 2, 0) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := Smale.StripCoordinates.hasDerivAt_horizontalSlice hf
  have heq : (fun x : ℝ => lowerStripCoordinates h (x, 0)) = fun x => ((x + 1) / 2, 0) := by
    funext x
    simp [lowerStripCoordinates, arcTime]
  rw [heq] at hd
  exact
    hd.unique (((hasDerivAt_id s).add_const 1).div_const 2 |>.prodMk (hasDerivAt_const s (0 : ℝ)))

private theorem
    Smale.WhitneyPairModel.lowerStripCoordinates_vertical_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1) =
      (cornerSign ((s + 1) / 2) * (1 / (4 * h * cornerScale ((s + 1) / 2))),
        1 / (4 * h * cornerScale ((s + 1) / 2))) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := Smale.StripCoordinates.hasDerivAt_verticalSlice hf
  have hdiv :
    HasDerivAt (fun u : ℝ => u / (4 * h * cornerScale ((s + 1) / 2)))
      (1 / (4 * h * cornerScale ((s + 1) / 2))) 0 :=
    (hasDerivAt_id 0).div_const _
  have hfirst := (HasDerivAt.const_mul (cornerSign ((s + 1) / 2)) hdiv).const_add ((s + 1) / 2)
  exact hd.unique (hfirst.prodMk hdiv)

private theorem Smale.WhitneyPairModel.injective_fderiv_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (lowerStripCoordinates h) (s, 0)) := by
  let L := fderiv ℝ (lowerStripCoordinates h) (s, 0)
  have hhor : ((2 : ℝ) • L) (1, 0) = (1, 0) := by
    change (2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0)) = (1, 0)
    rw [lowerStripCoordinates_horizontal_derivative hh]
    norm_num
  have hnorm : (((2 : ℝ) • L) (0, 1)).2 ≠ 0 := by
    change ((2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1))).2 ≠ 0
    rw [lowerStripCoordinates_vertical_derivative hh]
    change (2 : ℝ) * (1 / (4 * h * cornerScale ((s + 1) / 2))) ≠ 0
    exact
      mul_ne_zero (by norm_num)
        (one_div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne'))
  have hi :=
    Smale.StripCoordinates.injective_plane_of_horizontal_and_normal ((2 : ℝ) • L) hhor hnorm
  intro x y hxy
  exact hi (congrArg (fun z : ℝ × ℝ => (2 : ℝ) • z) hxy)

private theorem Smale.WhitneyPairModel.injective_fderiv_exchangeEdges (h : ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (exchangeEdges h) p) := by
  have heq : exchangeEdges h ∘ exchangeEdges h = id := funext (exchangeEdges_involutive h)
  have hd :
    (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [←
      fderiv_comp p ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))
        ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp)),
      heq, fderiv_id]
  intro x y hxy
  have he := congrArg (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)) hxy
  change
    ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p)) x =
      ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p))
        y at he
  rw [hd] at he
  exact he

private theorem Smale.WhitneyPairModel.injective_fderiv_upperStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (upperStripCoordinates h) (s, h * (1 - s ^ 2))) := by
  rw [upperStripCoordinates,
    fderiv_comp _ ((contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp))
      ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))]
  have heq : exchangeEdges h (s, h * (1 - s ^ 2)) = (s, 0) := by
    simp only [exchangeEdges, sub_self]
  rw [heq]
  exact (injective_fderiv_lowerStripCoordinates hh s).comp (injective_fderiv_exchangeEdges h _)

private theorem Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time {h : ℝ} (hh : 0 < h)
    (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (2 * t - 1, 0) ∨ p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
  constructor
  · intro hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    refine ⟨t, ht, ?_⟩
    rcases hpedge with hpzero | hpupper
    · exact Or.inl (Prod.ext hbase hpzero)
    · right
      apply Prod.ext hbase
      rw [← hbase]
      exact hpupper
  · rintro ⟨t, ht, rfl | rfl⟩
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨lowerArc_mem_bigon hh.le ?_, Or.inl rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨upperArc_mem_bigon hh.le ?_, Or.inr rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]

private theorem Smale.WhitneyPairModel.injOn_frontier_bigon_of_arcs {M : Type*} {h : ℝ} (hh : 0 < h)
    {f : (ℝ × ℝ) → M} {a b : ℝ → M} (ha : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hb : Set.InjOn b (Set.Icc (0 : ℝ) 1))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    Set.InjOn f (frontier (bigon h)) := by
  have hcross {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : a t = b s) : (2 * t - 1, (0 : ℝ)) = (2 * s - 1, h * (1 - (2 * s - 1) ^ 2)) := by
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro p hp q hq heq
  obtain ⟨t, ht, hp'⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  obtain ⟨s, hs, hq'⟩ := (mem_frontier_bigon_iff_exists_time hh q).mp hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · rw [hlower t ht, hlower s hs] at heq
    rw [ha ht hs heq]
  · rw [hlower t ht, hupper s hs] at heq
    exact hcross ht hs heq
  · rw [hupper t ht, hlower s hs] at heq
    exact (hcross hs ht heq.symm).symm
  · rw [hupper t ht, hupper s hs] at heq
    rw [hb ht hs heq]

private theorem
    Smale.CleanStripPatch.center_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : Smale.CleanStripPatch (E := E) S T a k₀ k₁) : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  have h0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have htK : (t, 0) ∈ k.domain := k.contains_strip ⟨ht, h0⟩
  have hsK : (s, 0) ∈ k.domain := k.contains_strip ⟨hs, h0⟩
  have hmaps : k.map (t, 0) = k.map (s, 0) := by
    rw [k.center t ht, k.center s hs]
    exact heq
  exact congrArg Prod.fst (k.injective htK hsK hmaps)

private theorem
    Smale.strip_center_coincidences_of_corner_overlap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  intro t ht s hs heq
  have hk0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hl0 : (0 : ℝ) ∈ Set.Icc (-l.width) l.width :=
    ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hmaps : k.map (t, 0) = l.map (s, 0) := by rw [k.center t ht, l.center s hs]; exact heq
  rcases hover (t, 0) (k.contains_strip ⟨ht, hk0⟩) (s, 0) (l.contains_strip ⟨hs, hl0⟩) hmaps with
    hleft | hright
  · exact Or.inl ⟨congrArg Prod.fst hleft, (congrArg Prod.snd hleft).symm⟩
  · right
    have ht' : 1 - t = 0 := congrArg Prod.fst hright
    have hs' : 0 = 1 - s := congrArg Prod.snd hright
    constructor <;> linarith

private theorem Smale.injective_nativeDerivative_of_strip_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {r : (ℝ × ℝ) → ℝ × ℝ}
    (hr : ContDiff ℝ ∞ r) {f : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (heq : Set.EqOn f (k.map ∘ r) U) (hmap : Set.MapsTo r U k.domain) {p : ℝ × ℝ} (hp : p ∈ U)
    (hi : Function.Injective (fderiv ℝ r p)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hgerm : f =ᶠ[𝓝 p] k.map ∘ r := Filter.mem_of_superset (hU.mem_nhds hp) (fun _ hx => heq hx)
  rw [hgerm.mfderiv_eq]
  have hk := k.smooth.contMDiffAt (k.open_domain.mem_nhds (hmap hp))
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp)) (hr.contMDiff.mdifferentiableAt (by simp))]
  have hri : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r p) := by
    rw [mfderiv_eq_fderiv]
    exact hi
  exact (k.derivative_injective (r p) (hmap hp)).comp hri

private theorem Smale.injective_nativeDerivative_bigon_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∀ p ∈ frontier (WhitneyPairModel.bigon h),
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  intro p hp
  obtain ⟨t, ht, rfl | rfl⟩ := (WhitneyPairModel.mem_frontier_bigon_iff_exists_time hh p).mp hp
  · exact
      injective_nativeDerivative_of_strip_germ k
        (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne') hU hflo hmapU (hlowU ht)
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates hh.ne' _)
  · exact
      injective_nativeDerivative_of_strip_germ l
        (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne') hV hfhi hmapV (huppV ht)
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates hh.ne' _)

private theorem
    Smale.exists_embedded_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hfront : frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V))
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
          W ⊆ U ∪ V ∧
            Set.InjOn f W ∧ ∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t := by
    intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  have hupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t := by
    intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht
  have hinj :=
    WhitneyPairModel.injOn_frontier_bigon_of_arcs hh k.center_injOn l.center_injOn hlow hupp
      (strip_center_coincidences_of_corner_overlap k l hover)
  have hi :=
    injective_nativeDerivative_bigon_boundary hh k l hU hV hlowU huppV hmapU hmapV hflo hfhi
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  exact
    ManifoldImmersion.exists_open_embedded_immersive_neighborhood (hU.union hV) hf hcompact hfront
      hinj hi

private theorem Smale.WhitneyPairModel.interpolated_strip_time_mem_Ioo {h t β z J : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 < J)
    (hJdef : J = (1 - β) * (1 - t) + β * t) (hz : 0 < z) (hzupper : z < 4 * h * t * (1 - t)) :
    t + (2 * β - 1) * (z / (4 * h * J)) ∈ Set.Ioo (0 : ℝ) 1 := by
  let H := 4 * h * t * (1 - t)
  have hH : 0 < H := mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
  let θ := z / H
  let e := t * β / J
  have hθ0 : 0 < θ := div_pos hz hH
  have hθ1 : θ < 1 := (div_lt_one hH).mpr hzupper
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg ht.1.le hβ.1) hJ.le
  have he1 : e ≤ 1 := by
    apply (div_le_one hJ).mpr
    rw [hJdef]
    have hr := mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr ht.2.le)
    nlinarith
  have hid : t + (2 * β - 1) * (z / (4 * h * J)) = (1 - θ) * t + θ * e := by
    dsimp [θ, e, H]
    field_simp [hh.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', hJ.ne']
    rw [hJdef]
    ring
  rw [hid]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) ht.1) (mul_nonneg hθ0.le he0)
  · have hpos : 0 < (1 - θ) * (1 - t) + θ * (1 - e) :=
      add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht.2))
        (mul_nonneg hθ0.le (sub_nonneg.mpr he1))
    nlinarith

private theorem
    Smale.WhitneyPairModel.lowerStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (lowerStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (lowerStripCoordinates h p).2 := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  have hheight : 0 < h * (1 - p.1 ^ 2) := hp0.trans hphi
  have hsq : p.1 ^ 2 < 1 := by
    have hpos : 0 < 1 - p.1 ^ 2 := (mul_pos_iff_of_pos_left hh).mp hheight
    linarith
  have ht : arcTime p ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [arcTime]
    constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  have hβ : cornerTransition (arcTime p) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hheight_eq : h * (1 - p.1 ^ 2) = 4 * h * arcTime p * (1 - arcTime p) := by
    dsimp [arcTime]
    ring
  have hzupper : p.2 < 4 * h * arcTime p * (1 - arcTime p) := hheight_eq ▸ hphi
  refine ⟨?_, ?_⟩
  · exact interpolated_strip_time_mem_Ioo hh ht hβ (cornerScale_pos _) rfl hp0 hzupper
  · exact div_pos hp0 (mul_pos (mul_pos (by norm_num) hh) (cornerScale_pos _))

private theorem Smale.WhitneyPairModel.exchangeEdges_mem_interior {h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) : exchangeEdges h p ∈ interior (bigon h) := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h * (1 - p.1 ^ 2) - p.2 ∧ h * (1 - p.1 ^ 2) - p.2 < h * (1 - p.1 ^ 2)
  constructor <;> linarith

private theorem
    Smale.WhitneyPairModel.upperStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (upperStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (upperStripCoordinates h p).2 :=
  lowerStripCoordinates_interior hh (exchangeEdges_mem_interior hp)

private theorem
    Smale.CleanStripPatch.avoids_sheets {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : Smale.CleanStripPatch (E := E) S T a k₀ k₁) {p : ℝ × ℝ} (hp : p ∈ k.domain)
    (ht : p.1 ∈ Set.Ioo (0 : ℝ) 1) (hn : p.2 ≠ 0) : k.map p ∉ S ∪ T := by
  rintro (hS | hT)
  · exact hn ((k.first_sheet p hp).mp hS)
  · rcases (k.second_sheet p hp).mp hT with h0 | h1
    · exact ht.1.ne' h0
    · exact ht.2.ne h1

private theorem Smale.bigon_boundary_map_avoids_sheets {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) {p : ℝ × ℝ}
    (hp : p ∈ U ∪ V) (hpi : p ∈ interior (WhitneyPairModel.bigon h)) : f p ∉ S ∪ T := by
  rcases hp with hpU | hpV
  · rw [hflo hpU]
    have hc := WhitneyPairModel.lowerStripCoordinates_interior hh hpi
    exact k.avoids_sheets (hmapU hpU) hc.1 hc.2.ne'
  · rw [hfhi hpV]
    have hc := WhitneyPairModel.upperStripCoordinates_interior hh hpi
    change l.map (WhitneyPairModel.upperStripCoordinates h p) ∉ S ∪ T
    rw [Set.union_comm]
    exact l.avoids_sheets (hmapV hpV) hc.1 hc.2.ne'

private structure Smale.CleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) where
  height_pos : 0 < h
  map : (ℝ × ℝ) → M
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ domain ∩ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  closed_neighborhood : Set (ℝ × ℝ)
  compact_neighborhood : IsCompact closed_neighborhood
  closed_closed_neighborhood : IsClosed closed_neighborhood
  boundary_covered : frontier (WhitneyPairModel.bigon h) ⊆ interior closed_neighborhood
  neighborhood_subset : closed_neighborhood ⊆ domain
  closed_embedding : Topology.IsClosedEmbedding (fun p : closed_neighborhood => map p)
  clean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ closed_neighborhood,
      p ∉ frontier (WhitneyPairModel.bigon h) → map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h

private theorem Smale.exists_clean_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∃ f : (ℝ × ℝ) → M,
      ∃ W : Set (ℝ × ℝ),
        IsOpen W ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W ∧
            Set.InjOn f W ∧
              (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
                (∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
                  ∃ C : Set (ℝ × ℝ),
                    IsCompact C ∧
                      IsClosed C ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ interior C ∧
                          C ⊆ W ∧
                            Topology.IsClosedEmbedding (fun p : C => f p) ∧
                              (∀ p ∈ WhitneyPairModel.bigon h ∩ C,
                                  p ∉ frontier (WhitneyPairModel.bigon h) → f p ∉ S ∪ T) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                      f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, 0)]
                                          k.map ∘ WhitneyPairModel.lowerStripCoordinates h) ∧
                                      (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
                                          l.map ∘ WhitneyPairModel.upperStripCoordinates h) := by
  obtain ⟨U, V, hU, hV, hfront, hlowU, huppV, hmapU, hmapV, f, hf, hflo, hfhi, hlow, hupp⟩ :=
    exists_smooth_bigon_boundary_neighborhood hh c₀ c₁ k l
  obtain ⟨W, hW, hfrontW, hWUV, hinj, hi⟩ :=
    exists_embedded_bigon_boundary_neighborhood hh k l hover hU hV hfront hlowU huppV hmapU hmapV
      hf hflo hfhi
  have hclean : ∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T := fun p hp =>
    bigon_boundary_map_avoids_sheets hh k l hmapU hmapV hflo hfhi (hWUV hp.1) hp.2
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCclosed, hfrontC, hCW⟩ := exists_compact_closed_between hcompact hW hfrontW
  have hemb : Topology.IsClosedEmbedding (fun p : C => f p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hc : Continuous (fun p : C => f p) :=
      continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono (hCW.trans hWUV))
    apply hc.isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hCW p.property) (hCW q.property) hpq)
  refine
    ⟨f, W, hW, hf.mono hWUV, hinj, hi, hclean, C, hC, hCclosed, hfrontC, hCW, hemb, ?_, hlow,
      hupp, ?_, ?_⟩
  · intro p hp hnot
    apply hclean p ⟨hCW hp.2, ?_⟩
    by_contra hni
    apply hnot
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlowU ht)) (fun _ hp => hflo hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (huppV ht)) (fun _ hp => hfhi hp)

private theorem
    Smale.nonempty_cleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀) (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    Nonempty (CleanBigonBoundary (E := E) S T a b k.map l.map h) := by
  obtain
    ⟨f, W, hW, hf, hinj, hi, havoid, C, hC, hCc, hfront, hCW, hemb, hclean, hlow, hupp, hlowg,
      huppg⟩ :=
    exists_clean_bigon_boundary_neighborhood hh c₀ c₁ k l hover
  exact
    ⟨{  height_pos := hh
        map := f
        domain := W
        open_domain := hW
        smooth := hf
        injective := hinj
        derivative_injective := hi
        interior_avoids := havoid
        closed_neighborhood := C
        compact_neighborhood := hC
        closed_closed_neighborhood := hCc
        boundary_covered := hfront
        neighborhood_subset := hCW
        closed_embedding := hemb
        clean := hclean
        lower := hlow
        upper := hupp
        lower_germ := hlowg
        upper_germ := huppg }⟩

private def Smale.DiskCone.point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : Metric.closedBall (0 : E) 1 :=
  ⟨(1 - (p.1 : ℝ)) • (p.2 : E),
    by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr p.1.2.2), mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    linarith [p.1.2.1]⟩

private theorem Smale.DiskCone.norm_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : ‖(point p : E)‖ = 1 - (p.1 : ℝ) := by
  change ‖(1 - (p.1 : ℝ)) • (p.2 : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.2.2),
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]

private theorem
    Smale.DiskCone.continuous_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (point (E := E)) := by
  apply Continuous.subtype_mk
  exact
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)

private theorem Smale.DiskCone.point_fibers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : unitInterval × Metric.sphere (0 : E) 1} (hpq : point p = point q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have hnorm := congrArg (fun x : Metric.closedBall (0 : E) 1 => ‖(x : E)‖) hpq
  rw [norm_point, norm_point] at hnorm
  have ht : p.1 = q.1 := Subtype.ext (by linarith)
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases htop : t = 1
  · exact Or.inr ⟨htop, htop⟩
  · have htval : (t : ℝ) ≠ 1 := fun heq => htop (Subtype.ext heq)
    have hnonzero : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htval)
    have hvec : (1 - (t : ℝ)) • (x : E) = (1 - (t : ℝ)) • (y : E) := congrArg Subtype.val hpq
    have hxy : x = y := Subtype.ext ((smul_right_injective E hnonzero) hvec)
    exact Or.inl (congrArg (fun z => (t, z)) hxy)

private theorem Smale.DiskCone.surjective_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] : Function.Surjective (point (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · refine ⟨(1, Classical.choice inferInstance), ?_⟩
    apply Subtype.ext
    change (1 - (1 : ℝ)) • _ = (x : E)
    rw [sub_self, zero_smul, hx]
  · have hxnorm : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    let t : unitInterval :=
      ⟨1 - ‖(x : E)‖, sub_nonneg.mpr hxnorm, by linarith [norm_nonneg (x : E)]⟩
    refine ⟨(t, Smale.RadialExtension.direction (x : E) hx), ?_⟩
    apply Subtype.ext
    change (1 - (1 - ‖(x : E)‖)) • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

private theorem
    Smale.DiskCone.isQuotientMap_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] [FiniteDimensional ℝ E] :
    Topology.IsQuotientMap (point (E := E)) := by
  let : CompactSpace (Metric.sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact .of_surjective_continuous surjective_point continuous_point

private theorem Smale.DiskCone.homotopy_eq_of_point_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] (f : C(Metric.sphere (0 : E) 1, M)) (c : M)
    (H : f.Homotopy (ContinuousMap.const _ c)) {p q : unitInterval × Metric.sphere (0 : E) 1}
    (hpq : point p = point q) : H p = H q := by
  rcases point_fibers hpq with h | ⟨hp, hq⟩
  · exact congrArg H h
  · have hp' : p = (1, p.2) := Prod.ext hp rfl
    have hq' : q = (1, q.2) := Prod.ext hq rfl
    rw [hp', hq', H.apply_one, H.apply_one]
    rfl

private def Smale.DiskCone.extensionFun {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) (x : Metric.closedBall (0 : E) 1) : M :=
  H (Function.surjInv surjective_point x)

private theorem
    Smale.DiskCone.extensionFun_point {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c))
    (p : unitInterval × Metric.sphere (0 : E) 1) : extensionFun f c H (point p) = H p :=
  homotopy_eq_of_point_eq f c H (Function.surjInv_eq surjective_point (point p))

private def Smale.DiskCone.extension {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    C(Metric.closedBall (0 : E) 1, M)
    where
  toFun := extensionFun f c H
  continuous_toFun := by
    apply isQuotientMap_point.continuous_iff.mpr
    have heq : extensionFun f c H ∘ point = H := funext (extensionFun_point f c H)
    rw [heq]
    exact H.continuous

private theorem
    Smale.DiskCone.extension_boundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E]
    (x : Metric.sphere (0 : E) 1) :
    extension f c H ⟨x, Metric.sphere_subset_closedBall x.property⟩ = f x := by
  have heq :
    (⟨(x : E), Metric.sphere_subset_closedBall x.property⟩ : Metric.closedBall (0 : E) 1) =
      point (0, x) := by
    apply Subtype.ext
    change (x : E) = (1 - (0 : ℝ)) • (x : E)
    rw [sub_zero, one_smul]
  change extensionFun f c H _ = f x
  rw [heq, extensionFun_point, H.apply_zero]

private theorem Smale.DiskCone.extension_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    extension f c H ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = c := by
  let x : Metric.sphere (0 : E) 1 := Classical.choice inferInstance
  have heq :
    (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Metric.closedBall (0 : E) 1) = point (1, x) := by
    apply Subtype.ext
    change (0 : E) = (1 - (1 : ℝ)) • (x : E)
    rw [sub_self, zero_smul]
  change extensionFun f c H _ = c
  rw [heq, extensionFun_point, H.apply_one]
  rfl

private def
    Smale.AnnularExtension.unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  (Max.max a ‖x‖)⁻¹ • x

private theorem Smale.AnnularExtension.max_radius_pos {E : Type*} [NormedAddCommGroup E] {a : ℝ}
    (ha : 0 < a) (x : E) : 0 < Max.max a ‖x‖ :=
  ha.trans_le (le_max_left _ _)

private theorem Smale.AnnularExtension.continuous_unitClamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (unitClamp (E := E) a) :=
  ((continuous_const.max continuous_norm).inv₀ (fun x => (max_radius_pos ha x).ne')).smul
    continuous_id

private theorem
    Smale.AnnularExtension.norm_unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ = ‖x‖ / Max.max a ‖x‖ := by
  rw [unitClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (max_radius_pos ha x)),
    div_eq_mul_inv, mul_comm]

private theorem Smale.AnnularExtension.norm_unitClamp_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ ≤ 1 := by
  rw [norm_unitClamp ha]
  exact (div_le_one (max_radius_pos ha x)).mpr (le_max_right _ _)

private def
    Smale.AnnularExtension.innerDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨unitClamp a x, mem_closedBall_zero_iff.mpr (norm_unitClamp_le ha x)⟩
  continuous_toFun := (continuous_unitClamp ha).subtype_mk _

private theorem Smale.AnnularExtension.unitClamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} {x : E} (hx : ‖x‖ ≤ a) : unitClamp a x = a⁻¹ • x := by
  rw [unitClamp, max_eq_left hx]

private def
    Smale.AnnularExtension.clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  a • unitClamp a x

private theorem Smale.AnnularExtension.continuous_clamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (clamp (E := E) a) :=
  continuous_const.smul (continuous_unitClamp ha)

private theorem Smale.AnnularExtension.clamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ ≤ a) : clamp a x = x := by
  rw [clamp, unitClamp_of_norm_le hx, smul_inv_smul₀ ha.ne']

private theorem
    Smale.AnnularExtension.norm_clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖clamp a x‖ = Min.min a ‖x‖ := by
  by_cases hx : ‖x‖ ≤ a
  · rw [clamp_of_norm_le ha hx, min_eq_right hx]
  · have hx' : a ≤ ‖x‖ := le_of_not_ge hx
    have hnorm : ‖x‖ ≠ 0 := (ha.trans_le hx').ne'
    rw [clamp, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_unitClamp ha, max_eq_right hx',
      div_self hnorm, mul_one, min_eq_left hx']

private theorem Smale.AnnularExtension.clamp_mem_annulus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} (hb : 0 < b) (hab : a ≤ b) {x : E} (hx : a ≤ ‖x‖) :
    a ≤ ‖clamp b x‖ ∧ ‖clamp b x‖ ≤ b := by
  rw [norm_clamp hb]
  exact ⟨le_min hab hx, min_le_left _ _⟩

private def
    Smale.AnnularExtension.exteriorFactor {E : Type*} [NormedAddCommGroup E] (a : ℝ) (x : E) :
    ℝ :=
  Min.min 1 (Max.max 0 (2 - ‖x‖ / a))

private theorem
    Smale.AnnularExtension.exteriorFactor_nonneg {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : 0 ≤ exteriorFactor a x :=
  le_min zero_le_one (le_max_left _ _)

private theorem
    Smale.AnnularExtension.exteriorFactor_le_one {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : exteriorFactor a x ≤ 1 :=
  min_le_left _ _

private def
    Smale.AnnularExtension.exteriorVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (x : E) : E :=
  exteriorFactor a x • unitClamp a x

private theorem Smale.AnnularExtension.continuous_exteriorVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (exteriorVector (E := E) a) := by
  have hf : Continuous (exteriorFactor (E := E) a) := by unfold exteriorFactor; fun_prop
  exact hf.smul (continuous_unitClamp ha)

private theorem Smale.AnnularExtension.norm_exteriorVector_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖exteriorVector a x‖ ≤ 1 := by
  rw [exteriorVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (exteriorFactor_nonneg a x)]
  calc
    _ ≤ 1 * 1 :=
      mul_le_mul (exteriorFactor_le_one a x) (norm_unitClamp_le ha x) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

private def Smale.AnnularExtension.exteriorDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨exteriorVector a x, mem_closedBall_zero_iff.mpr (norm_exteriorVector_le ha x)⟩
  continuous_toFun := (continuous_exteriorVector ha).subtype_mk _

private theorem Smale.AnnularExtension.exteriorVector_on_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ = a) :
    exteriorVector a x = unitClamp a x := by
  have hf : exteriorFactor a x = 1 := by
    unfold exteriorFactor
    rw [hx, div_self ha.ne']
    norm_num
  rw [exteriorVector, hf, one_smul]

private theorem Smale.AnnularExtension.exteriorVector_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : 2 * a ≤ ‖x‖) : exteriorVector a x = 0 := by
  have hdiv : 2 ≤ ‖x‖ / a := (le_div_iff₀ ha).mpr hx
  have hf : exteriorFactor a x = 0 := by
    unfold exteriorFactor
    rw [max_eq_left (by linarith : 2 - ‖x‖ / a ≤ 0), min_eq_right zero_le_one]
  rw [exteriorVector, hf, zero_smul]

private theorem Smale.AnnularExtension.disk_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (innerDisk ha x) = g x := by
  let v : Metric.sphere (0 : E) 1 :=
    ⟨unitClamp a x, by
      rw [mem_sphere_zero_iff_norm, norm_unitClamp ha, hx, max_self, div_self ha.ne']⟩
  have heq : innerDisk ha x = ⟨(v : E), Metric.sphere_subset_closedBall v.property⟩ := rfl
  rw [heq, hF]
  change g (clamp a x) = g x
  rw [clamp_of_norm_le ha hx.le]

private theorem
    Smale.AnnularExtension.exterior_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (exteriorDisk ha x) = g x := by
  have heq : exteriorDisk ha x = innerDisk ha x := Subtype.ext (exteriorVector_on_sphere ha hx)
  rw [heq]
  exact disk_extension_on_radius ha F hF hx

private theorem Smale.AnnularExtension.exists_continuous_annular_extension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {g : E → M} (hg : ContinuousOn g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b})
    (F₀ F₁ : C(Metric.closedBall (0 : E) 1, M))
    (hF₀ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₀ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    (hF₁ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₁ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (b • (v : E))) :
    ∃ G : C(E, M),
      Set.EqOn G g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
        ∀ x, 2 * b ≤ ‖x‖ → G x = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
  classical
  have hb : 0 < b := ha.trans hab
  let inner : C(E, M) := F₀.comp (innerDisk ha)
  let outer : C(E, M) := F₁.comp (exteriorDisk hb)
  let middle : E → M := g ∘ clamp b
  have houtside : closure (Metric.closedBall (0 : E) a)ᶜ ⊆ {x : E | a ≤ ‖x‖} := by
    apply closure_minimal
    · intro x hx
      have hn : ¬‖x‖ ≤ a := by simpa only [Set.mem_compl_iff, mem_closedBall_zero_iff] using hx
      exact le_of_lt (lt_of_not_ge hn)
    · exact isClosed_le continuous_const continuous_norm
  have hmiddle : ContinuousOn middle (closure (Metric.closedBall (0 : E) a)ᶜ) :=
    hg.comp (continuous_clamp hb).continuousOn
      (fun _ hx => clamp_mem_annulus hb hab.le (houtside hx))
  have hjoin₀ : ∀ x ∈ frontier (Metric.closedBall (0 : E) a), inner x = middle x := by
    intro x hx
    rw [frontier_closedBall _ ha.ne'] at hx
    have hnorm : ‖x‖ = a := mem_sphere_zero_iff_norm.mp hx
    change F₀ (innerDisk ha x) = g (clamp b x)
    rw [disk_extension_on_radius ha F₀ hF₀ hnorm, clamp_of_norm_le hb (hnorm.le.trans hab.le)]
  let G₀ : E → M := (Metric.closedBall (0 : E) a).piecewise inner middle
  have hG₀ : Continuous G₀ := continuous_piecewise hjoin₀ inner.continuous.continuousOn hmiddle
  have hG₀eq : Set.EqOn G₀ g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    intro x hx
    by_cases hxa : x ∈ Metric.closedBall (0 : E) a
    · have hnorm : ‖x‖ = a := le_antisymm (mem_closedBall_zero_iff.mp hxa) hx.1
      change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_mem _ _ _ hxa]
      exact disk_extension_on_radius ha F₀ hF₀ hnorm
    · change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_notMem _ _ _ hxa]
      change g (clamp b x) = g x
      rw [clamp_of_norm_le hb hx.2]
  have hjoin₁ : ∀ x ∈ frontier (Metric.closedBall (0 : E) b), G₀ x = outer x := by
    intro x hx
    rw [frontier_closedBall _ hb.ne'] at hx
    have hnorm : ‖x‖ = b := mem_sphere_zero_iff_norm.mp hx
    rw [hG₀eq (show a ≤ ‖x‖ ∧ ‖x‖ ≤ b by rw [hnorm]; exact ⟨hab.le, le_rfl⟩)]
    exact (exterior_extension_on_radius hb F₁ hF₁ hnorm).symm
  let G : C(E, M) :=
    ⟨(Metric.closedBall (0 : E) b).piecewise G₀ outer, hG₀.piecewise hjoin₁ outer.continuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = g x
    rw [Set.piecewise_eq_of_mem _ _ _ (mem_closedBall_zero_iff.mpr hx.2)]
    exact hG₀eq hx
  · intro x hx
    have hxb : x ∉ Metric.closedBall (0 : E) b := by
      rw [mem_closedBall_zero_iff]
      linarith
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = _
    rw [Set.piecewise_eq_of_notMem _ _ _ hxb]
    change F₁ (exteriorDisk hb x) = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    apply congrArg F₁
    exact Subtype.ext (exteriorVector_eq_zero hb hx)

private theorem
    Smale.AnnularExtension.dist_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : Dist.dist x (Smale.RadialExtension.direction x hx : E) = |‖x‖ - 1| := by
  let v := Smale.RadialExtension.direction x hx
  have hvec : ‖x‖ • (v : E) = x := smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  change Dist.dist x (v : E) = _
  calc
    _ = ‖(‖x‖ - 1) • (v : E)‖ := by rw [dist_eq_norm, sub_smul, one_smul, hvec]
    _ = |‖x‖ - 1| := by rw [norm_smul, Real.norm_eq_abs, hn, mul_one]

private theorem
    Smale.AnnularExtension.exists_closed_annulus_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {W : Set E} (hW : IsOpen W)
    (hSW : Metric.sphere (0 : E) 1 ⊆ W) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_sphere (0 : E) 1).exists_cthickening_subset_open hW hSW
  let ε := Min.min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεsmall : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (by linarith)
  refine ⟨1 - ε, 1 + ε, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro heq
    have hxlo := hx.1
    rw [heq, norm_zero] at hxlo
    linarith
  have hdist : Dist.dist x (Smale.RadialExtension.direction x hx0 : E) ≤ δ := by
    rw [dist_direction]
    apply le_trans (abs_le.mpr ?_) hεδ
    constructor <;> linarith [hx.1, hx.2]
  exact
    hδW
      (Metric.mem_cthickening_of_dist_le x (Smale.RadialExtension.direction x hx0) δ
        (Metric.sphere (0 : E) 1) (Smale.RadialExtension.direction x hx0).property hdist)

private abbrev Smale.SixSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

private theorem Smale.simplyConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : SimplyConnectedSpace M := by
  let : SimplyConnectedSpace Smale.SixSphere := EuclideanSphere.simplyConnectedSpace 4
  exact e.simplyConnectedSpace

private theorem Smale.pathConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : PathConnectedSpace M := by
  let : SimplyConnectedSpace M := simplyConnectedSpace_of_homotopySixSphere e
  infer_instance

private abbrev NoExotic.UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

private theorem NoExotic.ClosedHemisphere.unit_norm {E : Type*} [NormedAddCommGroup E]
    (x : NoExotic.UnitSphere E) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

private abbrev NoExotic.Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

private noncomputable def NoExotic.normalizedSphereMap {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : C(X, E)) (hg : ∀ x, g x ≠ 0) :
    C(X, UnitSphere E) := by
  let gN : X → E := fun x ↦ NormedSpace.normalize (g x)
  have hm : ∀ x, gN x ∈ UnitSphere E := by
    intro x
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hg x)
  have hc : Continuous gN :=
    (g.continuous.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hg x))).smul g.continuous
  exact ⟨fun x ↦ ⟨gN x, hm x⟩, hc.subtype_mk hm⟩

private theorem
    NoExotic.nearby_unit_ne_zero {E : Type*} [NormedAddCommGroup E] (a : UnitSphere E) (b : E)
    (h : Dist.dist b (a : E) < 1) : b ≠ 0 := by
  intro hb
  rw [hb, dist_zero_left, ClosedHemisphere.unit_norm] at h
  exact (lt_irrefl 1) h

private theorem
    NoExotic.nearby_segment_dist_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    Dist.dist ((a : E) + (t : ℝ) • (b - (a : E))) (a : E) < 1 := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖b - (a : E)‖ ≤ ‖b - (a : E)‖ := mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ < 1 := by simpa only [dist_eq_norm] using h

private theorem
    NoExotic.nearby_segment_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    (a : E) + (t : ℝ) • (b - (a : E)) ≠ 0 :=
  nearby_unit_ne_zero a _ (nearby_segment_dist_lt a b h t)

private noncomputable def NoExotic.nearbyNormalizationHomotopy {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : C(X, UnitSphere E)) (g : C(X, E))
    (h : ∀ x, Dist.dist (g x) (f x : E) < 1) :
    f.Homotopy (normalizedSphereMap g (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x)))
    where
  toFun
    p :=
    ⟨NormedSpace.normalize ((f p.2 : E) + (p.1 : ℝ) • (g p.2 - (f p.2 : E))), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1)⟩
  continuous_toFun := by
    have hf : Continuous (fun p : (unitInterval) × X ↦ (f p.2 : E)) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg := g.continuous.comp (continuous_snd : Continuous (Prod.snd : (unitInterval) × X → X))
    have ht : Continuous (fun p : (unitInterval) × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hb := hf.add (ht.smul (hg.sub hf))
    exact
      ((hb.norm.inv₀
                (fun p ↦
                  norm_ne_zero_iff.mpr (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1))).smul
            hb).subtype_mk
        _
  map_zero_left
    x := by
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (0 : ℝ) • (g x - (f x : E))) = (f x : E)
    simpa only [zero_smul, add_zero] using
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))
  map_one_left
    x := by
    apply Subtype.ext
    change
      NormedSpace.normalize ((f x : E) + (1 : ℝ) • (g x - (f x : E))) =
        NormedSpace.normalize (g x)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

private theorem
    NoExotic.contMDiff_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M] {g : M → E}
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hn : ∀ x, g x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ NormedSpace.normalize (g x)) := by
  intro x
  have hN : ContDiffAt ℝ ∞ (NormedSpace.normalize : E → E) (g x) :=
    ((contDiffAt_norm ℝ (hn x)).inv (norm_ne_zero_iff.mpr (hn x))).smul contDiffAt_id
  exact hN.comp_contMDiffAt (f := g) (x := x) (hg x)

private theorem NoExotic.exists_smoothSphereRepresentative {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M]
    [ChartedSpace H M] [FiniteDimensional ℝ B] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.Homotopic g := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  obtain ⟨g, hg, _⟩ :=
    hf.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ 1) continuous_const (fun _ ↦ zero_lt_one)
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hg x)
  refine ⟨normalizedSphereMap gC hn, ?_, ⟨nearbyNormalizationHomotopy f gC hg⟩⟩
  exact
    (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n)
      (fun x ↦ (normalizedSphereMap gC hn x).2)

private noncomputable def NoExotic.chartContractionHomotopy {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(X, Y))
    (c : OpenPartialHomeomorph Y E) (ht : c.target = Set.univ) (hf : ∀ x, f x ∈ c.source) :
    f.Homotopy (ContinuousMap.const _ (c.symm 0))
    where
  toFun p := c.symm ((1 - (p.1 : ℝ)) • c (f p.2))
  continuous_toFun := by
    have hc : Continuous (fun x ↦ c (f x)) := c.continuousOn.comp_continuous f.continuous hf
    have hci : Continuous c.symm := by
      apply continuousOn_univ.mp
      rw [← ht]
      exact c.symm.continuousOn
    exact
      hci.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (hc.comp continuous_snd))
  map_zero_left
    x := by
    change c.symm ((1 - (0 : ℝ)) • c (f x)) = f x
    rw [sub_zero, one_smul]
    exact c.left_inv (hf x)
  map_one_left
    x := by
    change c.symm ((1 - (1 : ℝ)) • c (f x)) = c.symm 0
    rw [sub_self, zero_smul]

private theorem
    NoExotic.sphereMap_nullhomotopic_of_omitted_point {X : Type*} [TopologicalSpace X] (n : ℕ)
    (f : C(X, Sphere n)) (p : Sphere n) (hp : ∀ x, f x ≠ p) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let c := stereographic' n p
  have hf : ∀ x, f x ∈ c.source := by
    intro x
    simpa only [c, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hp x
  exact ⟨c.symm 0, ⟨chartContractionHomotopy f c (stereographic'_target (n := n) p) hf⟩⟩

private theorem NoExotic.sphereMap_nullhomotopic_of_dim_lt {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) (hd : Module.finrank ℝ B < n) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  classical
  obtain ⟨g, hg, hfg⟩ := exists_smoothSphereRepresentative (I := I) n f
  let : Nonempty (Sphere n) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hn : ¬Function.Surjective g :=
    not_surjective_contMDiff_of_dim_lt hg (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨p, hp⟩ : ∃ p, ∀ x, g x ≠ p := by
    simpa only [Function.Surjective, Classical.not_forall, not_exists] using hn
  obtain ⟨c, hgc⟩ := sphereMap_nullhomotopic_of_omitted_point n g p hp
  exact ⟨c, hfg.trans hgc⟩

private theorem
    NoExotic.sphere_sphere_nullhomotopic {m n : ℕ} (hmn : m < n) (f : C(Sphere m, Sphere n)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  sphereMap_nullhomotopic_of_dim_lt (I := 𝓡 m) n f
    (by simpa only [finrank_euclideanSpace_fin] using hmn)

private theorem Smale.nullhomotopic_of_homotopySixSphere_comp {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] (e : M ≃ₕ Smale.SixSphere) (g : C(X, M))
    (h : ∃ c, (e.toFun.comp g).Homotopic (ContinuousMap.const X c)) :
    ∃ c, g.Homotopic (ContinuousMap.const X c) := by
  obtain ⟨c, hnull⟩ := h
  have h₀ : (e.invFun.comp (e.toFun.comp g)).Homotopic g :=
    e.left_inv.comp (ContinuousMap.Homotopic.refl g)
  have h₁ : (e.invFun.comp (e.toFun.comp g)).Homotopic (ContinuousMap.const X (e.invFun c)) :=
    (ContinuousMap.Homotopic.refl e.invFun).comp hnull
  exact ⟨e.invFun c, h₀.symm.trans h₁⟩

private theorem
    Smale.manifoldMap_nullhomotopic_of_homotopySixSphere {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace H] (I : ModelWithCorners ℝ B H) [I.Boundaryless]
    [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ B < 6) (g : C(X, M)) : ∃ c, g.Homotopic (ContinuousMap.const _ c) :=
  nullhomotopic_of_homotopySixSphere_comp e g
    (NoExotic.sphereMap_nullhomotopic_of_dim_lt (I := I) 6 (e.toFun.comp g) hdim)

private theorem Smale.exists_circle_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {g : Hemisphere.Ambient 2 → M} {W : Set (Hemisphere.Ambient 2)} (hW : IsOpen W)
    (hg : ContinuousOn g W) (hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W) :
    ∃ G : C(Hemisphere.Ambient 2, M),
      ∃ c : M,
        ∃ K : Set (Hemisphere.Ambient 2),
          IsCompact K ∧
            (∀ x ∉ K, G x = c) ∧
              ∃ U : Set (Hemisphere.Ambient 2),
                IsOpen U ∧
                  Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ U ∧ U ⊆ W ∧ Set.EqOn G g U := by
  obtain ⟨a, b, ha, ha1, h1b, hAW⟩ := AnnularExtension.exists_closed_annulus_subset hW hSW
  have hab : a < b := ha1.trans h1b
  have hb : 0 < b := ha.trans hab
  let A : Set (Hemisphere.Ambient 2) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hgA : ContinuousOn g A := hg.mono hAW
  have hscale (r : ℝ) (hr : r ∈ Set.Icc a b) (v : Hemisphere.Sphere 1) :
    r • (v : Hemisphere.Ambient 2) ∈ A := by
    have hr0 : 0 < r := ha.trans_le hr.1
    have hnorm : ‖r • (v : Hemisphere.Ambient 2)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, mem_sphere_zero_iff_norm.mp v.property,
        mul_one]
    change a ≤ ‖r • (v : Hemisphere.Ambient 2)‖ ∧ ‖r • (v : Hemisphere.Ambient 2)‖ ≤ b
    rw [hnorm]
    exact hr
  have hcontinuous (r : ℝ) :
    Continuous (fun v : Hemisphere.Sphere 1 => r • (v : Hemisphere.Ambient 2)) := by fun_prop
  let f₀ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (a • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous a) (hscale a ⟨le_rfl, hab.le⟩)⟩
  let f₁ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (b • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous b) (hscale b ⟨hab.le, le_rfl⟩)⟩
  obtain ⟨c₀, ⟨H₀⟩⟩ := hnull f₀
  obtain ⟨c₁, ⟨H₁⟩⟩ := hnull f₁
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty (Metric.sphere (0 : Hemisphere.Ambient 2) 1) := ⟨⟨v, hv⟩⟩
  let F₀ := DiskCone.extension f₀ c₀ H₀
  let F₁ := DiskCone.extension f₁ c₁ H₁
  obtain ⟨G, hGeq, hGconst⟩ :=
    AnnularExtension.exists_continuous_annular_extension ha hab hgA F₀ F₁
      (DiskCone.extension_boundary f₀ c₀ H₀) (DiskCone.extension_boundary f₁ c₁ H₁)
  let U : Set (Hemisphere.Ambient 2) := {x | a < ‖x‖ ∧ ‖x‖ < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hUA : U ⊆ A := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  refine
    ⟨G, c₁, Metric.closedBall 0 (2 * b), ProperSpace.isCompact_closedBall _ _, ?_, U, hU, ?_,
      hUA.trans hAW, hGeq.mono hUA⟩
  · intro x hx
    have hn : 2 * b < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
    rw [hGconst x hn.le]
    exact DiskCone.extension_zero f₁ c₁ H₁
  · intro x hx
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change a < ‖x‖ ∧ ‖x‖ < b
    rw [hn]
    exact ⟨ha1, h1b⟩

private theorem Smale.WhitneyPairModel.convex_bigon {h : ℝ} (hh : 0 ≤ h) : Convex ℝ (bigon h) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x.2 + b * y.2 ∧ h * (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ≤ h
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
  have hsq : (a * x.1 + b * y.1) ^ 2 = a * x.1 ^ 2 + b * y.1 ^ 2 - a * b * (x.1 - y.1) ^ 2 := by
    calc
      _ = (a + b) * (a * x.1 ^ 2 + b * y.1 ^ 2) - a * b * (x.1 - y.1) ^ 2 := by ring
      _ = _ := by rw [hab, one_mul]
  calc
    _ = a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) - h * a * b * (x.1 - y.1) ^ 2 := by
      rw [hsq]; ring
    _ ≤ a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) :=
      (sub_le_self _ (mul_nonneg (mul_nonneg (mul_nonneg hh ha) hb) (sq_nonneg _)))
    _ ≤ a * h + b * h :=
      (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb))
    _ = h := by rw [← add_mul, hab, one_mul]

private theorem Smale.WhitneyPairModel.bigon_center_mem_interior {h : ℝ} (hh : 0 < h) :
    (0, h / 2) ∈ interior (bigon h) := by
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h / 2 ∧ h / 2 < h * (1 - 0 ^ 2)
  norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
  constructor <;> linarith

private theorem Smale.WhitneyPairModel.interior_bigon_nonempty {h : ℝ} (hh : 0 < h) :
    (interior (bigon h)).Nonempty :=
  ⟨(0, h / 2), bigon_center_mem_interior hh⟩

private theorem Smale.WhitneyPairModel.exists_bigon_disk_homeomorph {h : ℝ} (hh : 0 < h) :
    ∃ e : (ℝ × ℝ) ≃ₜ Smale.Hemisphere.Ambient 2,
      e '' bigon h = Metric.closedBall 0 1 ∧
        e '' interior (bigon h) = Metric.ball 0 1 ∧ e '' frontier (bigon h) = Metric.sphere 0 1 :=
  by
  let L : (ℝ × ℝ) ≃L[ℝ] Smale.Hemisphere.Ambient 2 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Smale.Hemisphere.Ambient, Module.finrank_prod])
  let K : Set (Smale.Hemisphere.Ambient 2) := L '' bigon h
  have hK : IsCompact K := (isCompact_bigon hh).image L.continuous
  have hc : Convex ℝ K := (convex_bigon hh.le).linear_image L.toLinearEquiv.toLinearMap
  have hLint : L '' interior (bigon h) = interior K := L.toHomeomorph.image_interior (bigon h)
  have hLfront : L '' frontier (bigon h) = frontier K := L.toHomeomorph.image_frontier (bigon h)
  have hne : (interior K).Nonempty := by
    rw [← hLint]
    exact (interior_bigon_nonempty hh).image L
  obtain ⟨e, heint, heclosed, hefront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hK.isBounded
  refine ⟨L.toHomeomorph.trans e, ?_, ?_, ?_⟩
  · calc
      _ = e '' (L '' bigon h) := (Set.image_image e L (bigon h)).symm
      _ = Metric.closedBall 0 1 := by
        change e '' K = _
        rwa [hK.isClosed.closure_eq] at heclosed
  · calc
      _ = e '' (L '' interior (bigon h)) := (Set.image_image e L (interior (bigon h))).symm
      _ = Metric.ball 0 1 := by rw [hLint]; exact heint
  · calc
      _ = e '' (L '' frontier (bigon h)) := (Set.image_image e L (frontier (bigon h))).symm
      _ = Metric.sphere 0 1 := by rw [hLfront]; exact hefront

private theorem Smale.exists_bigon_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hf : ContinuousOn f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ∃ c : M,
        ∃ K : Set (ℝ × ℝ),
          IsCompact K ∧
            (∀ x ∉ K, F x = c) ∧
              ∃ U : Set (ℝ × ℝ),
                IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨φ, _, _, hφfront⟩ := WhitneyPairModel.exists_bigon_disk_homeomorph hh
  let W' : Set (Hemisphere.Ambient 2) := φ.symm ⁻¹' W
  let g : Hemisphere.Ambient 2 → M := f ∘ φ.symm
  have hW' : IsOpen W' := hW.preimage φ.symm.continuous
  have hg : ContinuousOn g W' := hf.comp φ.symm.continuous.continuousOn (fun _ hx => hx)
  have hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W' := by
    intro y hy
    have hy' : y ∈ φ '' frontier (WhitneyPairModel.bigon h) := by rw [hφfront]; exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    change φ.symm (φ x) ∈ W
    rw [φ.symm_apply_apply]
    exact hfrontW hx
  obtain ⟨G, c, K', hK', hconst, U', hU', hSU', hU'W', heq⟩ :=
    exists_circle_neighborhood_extension_of_circle_nullhomotopies hnull hW' hg hSW
  let F : C(ℝ × ℝ, M) := G.comp ⟨φ, φ.continuous⟩
  let K := φ.symm '' K'
  let U := φ ⁻¹' U'
  refine ⟨F, c, K, hK'.image φ.symm.continuous, ?_, U, hU'.preimage φ.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : φ x ∉ K' := fun hmem => hx ⟨φ x, hmem, φ.symm_apply_apply x⟩
    exact hconst (φ x) hx'
  · intro x hx
    apply hSU'
    rw [← hφfront]
    exact Set.mem_image_of_mem φ hx
  · intro x hx
    have hx' : φ.symm (φ x) ∈ W := hU'W' hx
    rwa [φ.symm_apply_apply] at hx'
  · intro x hx
    change G (φ x) = f x
    rw [heq hx]
    change f (φ.symm (φ x)) = f x
    rw [φ.symm_apply_apply]

private theorem
    Smale.exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨G, c, K, hK, hconst, V, hV, hfrontV, hVW, hGeq⟩ :=
    exists_bigon_neighborhood_extension_of_circle_nullhomotopies hnull hh hW hf.continuousOn
      hfrontW
  have hfrontCompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, _, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV hfrontV
  have hGV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G V := (hf.mono hVW).congr (fun _ hx => hGeq hx)
  have hGK : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G Kᶜ :=
    (contMDiff_const (c := c)).contMDiffOn.congr (fun x hx => hconst x hx)
  obtain ⟨F, hF, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact G hK hC hV hCV hGV hGK
  refine ⟨F, hF, interior C, isOpen_interior, hfrontC, interior_subset.trans (hCV.trans hVW), ?_⟩
  intro x hx
  exact (hrel.fst_eq_snd (interior_subset hx)).symm.trans (hGeq (hCV (interior_subset hx)))

private structure Smale.TubularBigon {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) (n : ℕ := 4) where
  height_pos : 0 < h
  map : C(ℝ × ℝ, M)
  smooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map
  closed_embedding : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => map p)
  derivative_injective :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
      ((ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = map p

private def Smale.WhitneyPairModel.lowerBoundaryArc (t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, 0)

private def Smale.WhitneyPairModel.upperBoundaryArc (h t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))

private theorem Smale.WhitneyPairModel.hasDerivAt_lowerBoundaryArc (t : ℝ) :
    HasDerivAt lowerBoundaryArc (2, 0) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  exact hs.prodMk (hasDerivAt_const t (0 : ℝ))

private theorem Smale.WhitneyPairModel.hasDerivAt_upperBoundaryArc (h t : ℝ) :
    HasDerivAt (upperBoundaryArc h) (2, -4 * h * (2 * t - 1)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hy : HasDerivAt (fun s : ℝ => h * (1 - (2 * s - 1) ^ 2)) (-4 * h * (2 * t - 1)) t := by
    convert HasDerivAt.const_mul h ((hasDerivAt_const t (1 : ℝ)).sub (hs.pow 2)) using 1 <;>
      first
      | rfl
      | ring
  exact hs.prodMk hy

private theorem Smale.TubularBigon.lowerBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Smale.WhitneyPairModel.lowerBoundaryArc t ∈ Smale.WhitneyPairModel.bigon h := by
  have hf :
    Smale.WhitneyPairModel.lowerBoundaryArc t ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
    (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  exact ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

private theorem Smale.TubularBigon.upperBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Smale.WhitneyPairModel.upperBoundaryArc h t ∈ Smale.WhitneyPairModel.bigon h := by
  have hf :
    Smale.WhitneyPairModel.upperBoundaryArc h t ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
    (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

private theorem
    Smale.TubularBigon.lowerBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Smale.WhitneyPairModel.lowerBoundaryArc t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.lowerBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

private theorem
    Smale.TubularBigon.upperBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Smale.WhitneyPairModel.upperBoundaryArc h t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.upperBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

private theorem
    Smale.TubularBigon.lower_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (Smale.StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.lower_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [Smale.WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hg
  have hp := tube.chart.map_source' (tube.lowerBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, Smale.WhitneyPairModel.lowerBoundaryArc, hg] at hp
  exact hp

private theorem
    Smale.TubularBigon.upper_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (Smale.StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.upper_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [Smale.WhitneyPairModel.upperStripCoordinates_upper, d.center t] at hg
  have hp := tube.chart.map_source' (tube.upperBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, Smale.WhitneyPairModel.upperBoundaryArc, hg] at hp
  exact hp

private theorem Smale.TubularBigon.lower_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (Smale.WhitneyPairModel.lowerBoundaryArc s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (Smale.WhitneyPairModel.hasDerivAt_lowerBoundaryArc t).continuousAt
    (tube.lowerBoundaryArc_zero_mem_source ht)
    (Smale.WhitneyPairModel.lowerStripCoordinates_lower h) (tube.lower_germ t ht)

private theorem Smale.TubularBigon.upper_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (Smale.WhitneyPairModel.upperBoundaryArc h s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (Smale.WhitneyPairModel.hasDerivAt_upperBoundaryArc h t).continuousAt
    (tube.upperBoundaryArc_zero_mem_source ht)
    (Smale.WhitneyPairModel.upperStripCoordinates_upper h) (tube.upper_germ t ht)

private theorem
    Smale.TubularBigon.lower_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, 0), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.lower_chart_center_mem_target d ht)
    (Smale.WhitneyPairModel.hasDerivAt_lowerBoundaryArc t)
    (tube.lower_sheetTransition_center_germ d ht)

private theorem
    Smale.TubularBigon.upper_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l h n)
    (d : Smale.StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, -4 * h * (2 * t - 1)), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.upper_chart_center_mem_target d ht)
    (Smale.WhitneyPairModel.hasDerivAt_upperBoundaryArc h t)
    (tube.upper_sheetTransition_center_germ d ht)

private theorem Smale.FrameField.det_of_zero_lower_left {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, (T (u, 0)).2 = 0) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.fst ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inl ℝ D Z))).toLinearMap.det *
        ((ContinuousLinearMap.snd ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let A := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inl ℝ D Z))
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bD bD A.toLinearMap)
        (LinearMap.toMatrix bZ bD B.toLinearMap) 0 (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hT, A, B, K]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

private theorem Smale.FrameField.det_of_fixed_first_factor {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, T (u, 0) = (u, 0)) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.snd ℝ D Z).comp
          (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix bZ bD B.toLinearMap) 0
        (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, hT, B, K, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul, LinearMap.det_toMatrix]

private theorem Smale.FrameField.det_frame_eq_det_split_mul_det_coefficient {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).toLinearMap.det *
        ((complementQuotient G C).comp L).toLinearMap.det := by
  let T := G.coprod C
  let R := G.coprod L
  let A := T.inverse.comp R
  have hA : ∀ u : D, A (u, 0) = (u, 0) := by
    intro u
    change T.inverse (G u + L 0) = (u, 0)
    rw [map_zero, add_zero]
    have hi := h.inverse_apply_self (u, 0)
    change T.inverse (G u + C 0) = (u, 0) at hi
    simpa only [map_zero, add_zero] using hi
  have hblock :
    (ContinuousLinearMap.snd ℝ D Z).comp (A.comp (ContinuousLinearMap.inr ℝ D Z)) =
      (complementQuotient G C).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change (T.inverse (G 0 + L v)).2 = (T.inverse (L v)).2
    rw [map_zero, zero_add]
  have hdetA : A.toLinearMap.det = ((complementQuotient G C).comp L).toLinearMap.det := by
    rw [det_of_fixed_first_factor A hA, hblock]
  have hfactor :
    j.symm.toContinuousLinearMap.comp R = (j.symm.toContinuousLinearMap.comp T).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change j.symm (R v) = j.symm (T (T.inverse (R v)))
    rw [h.self_apply_inverse]
  change (j.symm.toContinuousLinearMap.comp R).toLinearMap.det = _
  rw [hfactor]
  have hmul :
    ((j.symm.toContinuousLinearMap.comp T).comp A).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp T).toLinearMap.det * A.toLinearMap.det :=
    map_mul LinearMap.det _ _
  rw [hmul, hdetA]

private def Smale.PlanarFrame.area (u v : Smale.PlaneImmersion.Plane) : ℝ :=
  u.1 * v.2 - u.2 * v.1

private def Smale.PlanarFrame.squareLength (u : Smale.PlaneImmersion.Plane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

private def
    Smale.PlanarFrame.quarterTurn (u : Smale.PlaneImmersion.Plane) : Smale.PlaneImmersion.Plane :=
  (-u.2, u.1)

private def Smale.PlanarFrame.parallelCoeff (u v : Smale.PlaneImmersion.Plane) : ℝ :=
  (u.1 * v.1 + u.2 * v.2) / squareLength u

private def Smale.PlanarFrame.transverseCoeff (u v : Smale.PlaneImmersion.Plane) : ℝ :=
  area u v / squareLength u

private def Smale.PlanarFrame.determinant
    (L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) : ℝ :=
  area (L (1, 0)) (L (0, 1))

private theorem Smale.PlanarFrame.squareLength_pos {u : Smale.PlaneImmersion.Plane} (hu : u ≠ 0) :
    0 < squareLength u := by
  have hsq₁ := sq_nonneg u.1
  have hsq₂ := sq_nonneg u.2
  by_contra h
  have hz : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hu₁ : u.1 = 0 := by nlinarith
  have hu₂ : u.2 = 0 := by nlinarith
  exact hu (Prod.ext hu₁ hu₂)

private theorem
    Smale.PlanarFrame.decompose_second_column {u : Smale.PlaneImmersion.Plane} (hu : u ≠ 0)
    (v : Smale.PlaneImmersion.Plane) :
    parallelCoeff u v • u + transverseCoeff u v • quarterTurn u = v := by
  have hnorm := (squareLength_pos hu).ne'
  ext <;> dsimp [parallelCoeff, transverseCoeff, area, quarterTurn]
  · field_simp
    simp only [squareLength]
    ring
  · field_simp
    simp only [squareLength]
    ring

private theorem Smale.PlanarFrame.area_transverse (u : Smale.PlaneImmersion.Plane) (a b : ℝ) :
    area u (a • u + b • quarterTurn u) = b * squareLength u := by
  dsimp [area, quarterTurn, squareLength]
  ring

private theorem Smale.PlanarFrame.linearMap_first (u v : Smale.PlaneImmersion.Plane) :
    Smale.PlaneImmersion.linearMap (u, v) (1, 0) = u := by
  simp [Smale.PlaneImmersion.linearMap_apply]

private theorem Smale.PlanarFrame.linearMap_second (u v : Smale.PlaneImmersion.Plane) :
    Smale.PlaneImmersion.linearMap (u, v) (0, 1) = v := by
  simp [Smale.PlaneImmersion.linearMap_apply]

private theorem Smale.PlanarFrame.linearMap_columns
    (L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) :
    Smale.PlaneImmersion.linearMap (L (1, 0), L (0, 1)) = L := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
  rw [Smale.PlaneImmersion.linearMap_apply, ← map_smul, ← map_smul, ← map_add, ← hp]

private theorem Smale.PlanarFrame.determinant_linearMap (u v : Smale.PlaneImmersion.Plane) :
    determinant (Smale.PlaneImmersion.linearMap (u, v)) = area u v := by
  rw [determinant, linearMap_first, linearMap_second]

private theorem Smale.PlanarFrame.determinant_eq_det
    (L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) :
    determinant L = L.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, determinant, area, mul_comm]

private theorem Smale.PlanarFrame.bijective_of_determinant_ne_zero
    (L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (hL : determinant L ≠ 0) :
    Function.Bijective L := by
  have hdet : L.toLinearMap.det ≠ 0 := by rwa [determinant_eq_det] at hL
  have hker : L.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

private theorem Smale.PlanarFrame.continuous_determinant : Continuous determinant := by
  have h₁ :
    Continuous
      (fun L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane => L (1, 0)) :=
    continuous_id.clm_apply continuous_const
  have h₂ :
    Continuous
      (fun L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane => L (0, 1)) :=
    continuous_id.clm_apply continuous_const
  exact (h₁.fst.mul h₂.snd).sub (h₁.snd.mul h₂.fst)

private theorem Smale.PlanarFrame.continuous_quarterTurn : Continuous quarterTurn :=
  continuous_snd.neg.prodMk continuous_fst

private theorem Smale.PlanarFrame.continuous_linearMap :
    Continuous
      (Smale.PlaneImmersion.linearMap :
        (Smale.PlaneImmersion.Plane × Smale.PlaneImmersion.Plane) →
          (Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane)) := by
  exact
    ((ContinuousLinearMap.smulRightL ℝ Smale.PlaneImmersion.Plane Smale.PlaneImmersion.Plane
              (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp
          continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ Smale.PlaneImmersion.Plane Smale.PlaneImmersion.Plane
            (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp
        continuous_snd)

private def Smale.IntersectionCoordinates.jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (Smale.PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (Smale.PlaneImmersion.Plane × F)) :
    (Smale.PlaneImmersion.Plane × (A × B)) →L[ℝ] (Smale.PlaneImmersion.Plane × (A × B)) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Smale.PlaneImmersion.Plane)
        j.symm).toContinuousLinearMap.comp
    ((P.coprod Q).comp
      (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).symm.toContinuousLinearMap)

private theorem
    Smale.IntersectionCoordinates.jointBlock_apply {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (Smale.PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (Smale.PlaneImmersion.Plane × F))
    (p : Smale.PlaneImmersion.Plane × (A × B)) :
    jointBlock j P Q p =
      ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).1,
        j.symm ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).2)) :=
  rfl

private theorem Smale.IntersectionCoordinates.map_first_axis {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : (ℝ × A) →L[ℝ] (Smale.PlaneImmersion.Plane × F)) (s : ℝ) : P (s, 0) = s • P (1, 0) := by
  have hs : (s, (0 : A)) = s • ((1 : ℝ), 0) := by ext <;> simp
  rw [hs, map_smul]

private theorem Smale.IntersectionCoordinates.det_jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Smale.PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (Smale.PlaneImmersion.Plane × F)) {u v : Smale.PlaneImmersion.Plane}
    (hP : P (1, 0) = (u, 0)) (hQ : Q (1, 0) = (v, 0)) :
    (jointBlock j P Q).toLinearMap.det =
      (Smale.PlaneImmersion.linearMap (u, v)).toLinearMap.det *
        (j.symm.toContinuousLinearMap.comp
            (((ContinuousLinearMap.snd ℝ Smale.PlaneImmersion.Plane F).comp
                  (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
              ((ContinuousLinearMap.snd ℝ Smale.PlaneImmersion.Plane F).comp
                (Q.comp (ContinuousLinearMap.inr ℝ ℝ B))))).toLinearMap.det := by
  have hzero : ∀ w : Smale.PlaneImmersion.Plane, (jointBlock j P Q (w, 0)).2 = 0 := by
    intro w
    rw [jointBlock_apply]
    change j.symm ((P (w.1, 0) + Q (w.2, 0)).2) = 0
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    simp
  have hfirst :
    (ContinuousLinearMap.fst ℝ Smale.PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inl ℝ Smale.PlaneImmersion.Plane (A × B))) =
      Smale.PlaneImmersion.linearMap (u, v) := by
    apply ContinuousLinearMap.ext
    intro w
    change (jointBlock j P Q (w, 0)).1 = w.1 • u + w.2 • v
    rw [jointBlock_apply]
    change (P (w.1, 0) + Q (w.2, 0)).1 = w.1 • u + w.2 • v
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    rfl
  have hsecond :
    (ContinuousLinearMap.snd ℝ Smale.PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inr ℝ Smale.PlaneImmersion.Plane (A × B))) =
      j.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.snd ℝ Smale.PlaneImmersion.Plane F).comp
              (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
          ((ContinuousLinearMap.snd ℝ Smale.PlaneImmersion.Plane F).comp
            (Q.comp (ContinuousLinearMap.inr ℝ ℝ B)))) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [Smale.FrameField.det_of_zero_lower_left _ hzero, hfirst, hsecond]

private theorem Smale.FrameField.bijective_coprod_of_orthogonal_range {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F)
    (B : Z →L[ℝ] F) (hL : Function.Injective L) (hB : Function.Injective B)
    (hr : B.range = L.rangeᗮ) : Function.Bijective (L.coprod B) := by
  have hd : Disjoint L.range B.range := by
    rw [hr]
    exact L.range.orthogonal_disjoint
  constructor
  · change Function.Injective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  · change Function.Surjective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact L.range.isCompl_orthogonal.sup_eq_top

private theorem Smale.FrameField.exists_smooth_complement_near_starConvex_on {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} {O : Set E} (hO : IsOpen O) (hL : ContDiffOn ℝ ∞ L O) {K : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hKO : K ⊆ O)
    (hi : ∀ x ∈ K, Function.Injective (L x)) (n : ℕ)
    (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)) ≃L[ℝ] D :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let A (x : E) := (L x).comp φ.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A O := hL.clm_comp contDiffOn_const
  have hAr (x : E) : (A x).range = (L x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
  let U : Set E := O ∩ {x | Function.Injective (L x)}
  have hU : IsOpen U :=
    hL.continuousOn.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_injective
  have hKU : K ⊆ U := fun x hx => ⟨hKO hx, hi x hx⟩
  let P (x : E) : F →L[ℝ] F := 1 - NoExotic.gramProjection (A x)
  have hP (x : E) (hx : x ∈ U) : P x = ((L x).rangeᗮ).starProjection := by
    dsimp only [P]
    rw [NoExotic.gramProjection_eq_starProjection _ (hx.2.comp φ.injective)]
    simp only [hAr]
    exact (Submodule.starProjection_orthogonal' (L x).range).symm
  have hsP : ContDiffOn ℝ ∞ P U := by
    intro x hx
    have hg : ContDiffAt ℝ ∞ (fun y => NoExotic.gramProjection (A y)) x :=
      (NoExotic.contMDiffAt_gramProjection (hA.contDiffAt (hO.mem_nhds hx.1)).contMDiffAt
          (hx.2.comp φ.injective)).contDiffAt
    exact (contDiffAt_const.sub hg).contDiffWithinAt
  have hidem : ∀ x ∈ K, IsIdempotentElem (P x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact ((L x).rangeᗮ).isIdempotentElem_starProjection
  obtain ⟨W, hW, hKW, B₀, hB₀, hB₀i⟩ :=
    Smale.DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU P hidem hsP
  have hr (x : E) (hx : x ∈ K) : (P x).range = (L x).rangeᗮ := by
    rw [hP x (hKU hx), Submodule.range_starProjection]
  have hcenter : Module.finrank ℝ (P 0).range = n := by
    have hrank : Module.finrank ℝ (L 0).range = Module.finrank ℝ D :=
      LinearMap.finrank_range_of_inj (hi 0 h0)
    have hs := (L 0).range.finrank_add_finrank_orthogonal
    rw [hrank] at hs
    rw [hr 0 h0]
    omega
  let ψ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (P 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  let B (x : E) := (B₀ x).comp ψ.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ B (W ∩ O) := (hB₀.clm_comp contDiffOn_const).mono Set.inter_subset_left
  have hBr : ∀ x ∈ K, (B x).range = (L x).rangeᗮ := by
    intro x hx
    calc
      (B x).range = (B₀ x).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ψ.surjective)
      _ = (P x).range := (hB₀i x hx).2
      _ = (L x).rangeᗮ := hr x hx
  have hBi : ∀ x ∈ K, Function.Injective (B x) := fun x hx => (hB₀i x hx).1.comp ψ.injective
  let T (x : E) := (L x).coprod (B x)
  have hT : ContDiffOn ℝ ∞ T (W ∩ O) := by
    have hs :=
      ((hL.mono Set.inter_subset_right).clm_comp
            (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin n))))).add
        (hB.clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin n)))))
    exact hs
  have hTi : ∀ x ∈ K, Function.Bijective (T x) := fun x hx =>
    bijective_coprod_of_orthogonal_range (L x) (B x) (hi x hx) (hBi x hx) (hBr x hx)
  let V : Set E := (W ∩ O) ∩ {x | Function.Injective (T x)}
  have hV : IsOpen V :=
    hT.continuousOn.isOpen_inter_preimage (hW.inter hO) ContinuousLinearMap.isOpen_injective
  refine
    ⟨V, hV, fun x hx => ⟨⟨hKW hx, hKO hx⟩, (hTi x hx).1⟩, B, hB.mono Set.inter_subset_left, hBr,
      ?_⟩
  intro x hx
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hx.2⟩

private theorem Smale.FrameField.exists_smooth_complement_near_starConvex {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} (hL : ContDiff ℝ ∞ L) {K : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hi : ∀ x ∈ K, Function.Injective (L x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) :=
  exists_smooth_complement_near_starConvex_on isOpen_univ hL.contDiffOn hK hstar h0
    (Set.subset_univ K) hi n hdim

private theorem Smale.TubularBigon.lower_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : (ℝ × ℝ) → M} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k.map l h n)
    (d : Smale.StripNormalData A B (E := E) S k.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ Smale.WhitneyPairModel.bigon h := by
    intro t ht
    have hf : (2 * t - 1, 0) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, 0), 0) ∈ tube.chart.source := fun t ht =>
    tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.lower t ht] at hp
    rw [← d.center t, k.center t ht]
    exact hp
  · intro t ht
    have hkt : (t, (0 : ℝ)) ∈ k.domain :=
      k.contains_strip ⟨ht, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (Smale.WhitneyPairModel.lowerStripCoordinates h) (2 * t - 1, 0)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (Smale.WhitneyPairModel.injective_fderiv_lowerStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt)) tube.zero_section (hsource t ht)
        (Smale.WhitneyPairModel.contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
        (Smale.WhitneyPairModel.lowerStripCoordinates_lower h t) hcs (tube.lower_germ t ht)

private theorem Smale.TubularBigon.upper_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {l : Smale.CleanStripPatch (E := E) T S b k₀ k₁}
    {k : (ℝ × ℝ) → M} {n : ℕ} (tube : Smale.TubularBigon (E := E) S T a b k l.map h n)
    (d : Smale.StripNormalData A B (E := E) T l.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ Smale.WhitneyPairModel.bigon h := by
    intro t ht
    have hf :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    exact ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, h * (1 - (2 * t - 1) ^ 2)), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.upper t ht] at hp
    rw [← d.center t, l.center t ht]
    exact hp
  · intro t ht
    have hlt : (t, (0 : ℝ)) ∈ l.domain :=
      l.contains_strip ⟨ht, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (Smale.WhitneyPairModel.upperStripCoordinates h)
          (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (Smale.WhitneyPairModel.injective_fderiv_upperStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section (hsource t ht)
        (Smale.WhitneyPairModel.contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
        (Smale.WhitneyPairModel.upperStripCoordinates_upper h t) hcs (tube.upper_germ t ht)

private theorem Smale.TubularBigon.upper_sheetFrame_complement_of_finrank {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} [FiniteDimensional ℝ A]
    {l : Smale.CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k l.map h n)
    (d : Smale.StripNormalData A B (E := E) T l.map) (m : ℕ) (hdim : Module.finrank ℝ A + m = n) :
    ∃ V : Set ℝ,
      IsOpen V ∧
        Set.Icc (0 : ℝ) 1 ⊆ V ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
            ∃ C : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)),
              ContDiffOn ℝ ∞ C V ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
                  ∀ t ∈ V, Function.Bijective ((d.normalFrame tube.chart t).coprod (C t)) := by
  obtain ⟨⟨U, hU, hIU, hs⟩, hi⟩ := tube.upper_sheetFrame d
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  have hdim' : Module.finrank ℝ A + m = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨W, hW, hIW, C, hC, hr, hc⟩ :=
    Smale.FrameField.exists_smooth_complement_near_starConvex_on hU hs
      CompactIccSpace.isCompact_Icc hstar (by simp) hIU hi m hdim'
  exact
    ⟨W ∩ U, hW.inter hU, fun t ht => ⟨hIW ht, hIU ht⟩, hs.mono Set.inter_subset_right, C,
      hC.mono Set.inter_subset_left, hr, fun t ht => hc t ht.1⟩

private def Smale.DiskFraming.puncturedModel (B : Type*) [NormedAddCommGroup B] :
    TopologicalSpace.Opens B :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

private theorem Smale.DiskFraming.exists_smooth_punctured_curve_with_germ {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ≠ 0) :
    ∃ f : C(ℝ, puncturedModel B),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → puncturedModel B := fun t => if h : a t = 0 then ⟨a t₀, ha0⟩ else ⟨a t, h⟩
  let V := U ∩ a ⁻¹' ({0}ᶜ : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hs0 : a s ≠ 0 := hs.2
    simp only [Function.comp_apply, A, dite_eq_right hs0]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ a t :=
      (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff (puncturedModel B) A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, hfgerm⟩ := Smale.exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfgerm, hval htV] with t ht htval
  exact (congrArg Subtype.val ht).trans htval

public
theorem Smale.DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ≠ 0) (hb1 : b 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ v : ℝ → B, ContDiff ℝ ∞ v ∧ (∀ t, v t ≠ 0) ∧ (v =ᶠ[𝓝 (0 : ℝ)] a) ∧ (v =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_punctured_curve_with_germ ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_punctured_curve_with_germ hb hV h1V hb1
  have hrank : 1 < Module.rank ℝ B := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ B by omega)
  let : PathConnectedSpace (puncturedModel B) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : B))
  let γ := PathConnectedSpace.somePath (a' 0) (b' 1)
  obtain ⟨f, hf, hfa, hfb⟩ := Smale.exists_smooth_curve_with_endpoint_germs a' b' ha' hb' γ
  let v : ℝ → B := fun t => (f t : B)
  have hv : ContDiff ℝ ∞ v :=
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := puncturedModel B)).comp hf).contDiff
  refine ⟨v, hv, fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

private def Smale.PlanarFrame.determinantComponent (σ : ℝ) :
    TopologicalSpace.Opens (Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) :=
  ⟨{L | 0 < σ * determinant L},
    isOpen_lt continuous_const (continuous_const.mul continuous_determinant)⟩

private theorem Smale.PlanarFrame.first_column_ne_zero {σ : ℝ} (L : determinantComponent σ) :
    (L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0) ≠ 0 := by
  intro hz
  have h := L.property
  change
    0 <
      σ *
        area ((L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
          ((L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1)) at h
  rw [hz] at h
  simp [area] at h

private theorem Smale.PlanarFrame.signed_transverseCoeff_pos {σ : ℝ} (L : determinantComponent σ) :
    0 <
      σ *
        transverseCoeff ((L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
          ((L : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1)) := by
  rw [transverseCoeff, ← mul_div_assoc]
  exact div_pos L.property (squareLength_pos (first_column_ne_zero L))

private theorem Smale.PlanarFrame.nonempty_path_determinantComponent {σ : ℝ}
    (a b : determinantComponent σ) : Nonempty (Path a b) := by
  have hrank : 1 < Module.rank ℝ Smale.PlaneImmersion.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
  let : PathConnectedSpace (Smale.DiskFraming.puncturedModel Smale.PlaneImmersion.Plane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : Smale.PlaneImmersion.Plane))
  let a₁ : Smale.DiskFraming.puncturedModel Smale.PlaneImmersion.Plane :=
    ⟨(a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero a⟩
  let b₁ : Smale.DiskFraming.puncturedModel Smale.PlaneImmersion.Plane :=
    ⟨(b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero b⟩
  let γ := PathConnectedSpace.somePath a₁ b₁
  let v : unitInterval → Smale.PlaneImmersion.Plane := fun t => (γ t : Smale.PlaneImmersion.Plane)
  have hv : Continuous v := continuous_subtype_val.comp γ.continuous
  have hvne (t : unitInterval) : v t ≠ 0 := (γ t).property
  let α₀ :=
    parallelCoeff ((a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
      ((a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1))
  let α₁ :=
    parallelCoeff ((b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
      ((b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1))
  let β₀ :=
    transverseCoeff ((a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
      ((a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1))
  let β₁ :=
    transverseCoeff ((b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0))
      ((b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (0, 1))
  let α (t : unitInterval) : ℝ := (1 - (t : ℝ)) * α₀ + (t : ℝ) * α₁
  let β (t : unitInterval) : ℝ := (1 - (t : ℝ)) * β₀ + (t : ℝ) * β₁
  have hα : Continuous α :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβ : Continuous β :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβpos (t : unitInterval) : 0 < σ * β t := by
    have hpos : 0 < (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) :=
      (convex_Ioi (0 : ℝ)) (signed_transverseCoeff_pos a) (signed_transverseCoeff_pos b)
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : σ * β t = (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) := by
      dsimp only [β]
      ring
    rwa [heq]
  let F (t : unitInterval) : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane :=
    Smale.PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t))
  have hF : Continuous F :=
    continuous_linearMap.comp
      (hv.prodMk ((hα.smul hv).add (hβ.smul (continuous_quarterTurn.comp hv))))
  have hcomponent (t : unitInterval) : F t ∈ determinantComponent σ := by
    change
      0 <
        σ *
          determinant (Smale.PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t)))
    rw [determinant_linearMap, area_transverse, ← mul_assoc]
    exact mul_pos (hβpos t) (squareLength_pos (hvne t))
  have hv0 : v 0 = (a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.source
  have hv1 : v 1 = (b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.target
  have hF0 : F 0 = (a : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) := by
    change Smale.PlaneImmersion.linearMap (v 0, α 0 • v 0 + β 0 • quarterTurn (v 0)) = _
    have hα0 : α 0 = α₀ := by simp [α]
    have hβ0 : β 0 = β₀ := by simp [β]
    rw [hv0, hα0, hβ0, decompose_second_column (first_column_ne_zero a)]
    exact linearMap_columns a
  have hF1 : F 1 = (b : Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane) := by
    change Smale.PlaneImmersion.linearMap (v 1, α 1 • v 1 + β 1 • quarterTurn (v 1)) = _
    have hα1 : α 1 = α₁ := by simp [α]
    have hβ1 : β 1 = β₁ := by simp [β]
    rw [hv1, hα1, hβ1, decompose_second_column (first_column_ne_zero b)]
    exact linearMap_columns b
  exact
    ⟨{  toFun := fun t => ⟨F t, hcomponent t⟩
        continuous_toFun := hF.subtype_mk hcomponent
        source' := Subtype.ext hF0
        target' := Subtype.ext hF1 }⟩

private theorem Smale.PlanarFrame.exists_smooth_join_of_same_determinant_sign
    {a b : ℝ → (Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (Smale.PlaneImmersion.Plane →L[ℝ] Smale.PlaneImmersion.Plane),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (a 0)
    rw [determinant_eq_det]
    exact mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (b 1)
    rw [determinant_eq_det]
    exact hsign
  obtain ⟨γ⟩ :=
    nonempty_path_determinantComponent (⟨a 0, ha0⟩ : determinantComponent σ)
      (⟨b 1, hb1⟩ : determinantComponent σ)
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs (determinantComponent σ) ha hb hU hV h0U
      h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have h := hmem t
    change 0 < (a 0).toLinearMap.det * determinant (L t) at h
    rwa [determinant_eq_det] at h
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  apply bijective_of_determinant_ne_zero (L t)
  intro hz
  rw [determinant_eq_det] at hz
  have h := hpositive t
  rw [hz, MulZeroClass.mul_zero] at h
  exact lt_irrefl _ h

private theorem Smale.FrameField.exists_smooth_invertible_join_of_finrank_two {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 2) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  have hdim' : Module.finrank ℝ Smale.PlaneImmersion.Plane = Module.finrank ℝ D := by
    simp [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self, hdim]
  let e : Smale.PlaneImmersion.Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq hdim'
  let a' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((a t).comp e.toContinuousLinearMap)
  let b' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((b t).comp e.toContinuousLinearMap)
  have ha' : ContDiffOn ℝ ∞ a' U := contDiffOn_const.clm_comp (ha.clm_comp contDiffOn_const)
  have hb' : ContDiffOn ℝ ∞ b' V := contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const)
  have hadet (t : ℝ) : (a' t).toLinearMap.det = (a t).toLinearMap.det :=
    LinearMap.det_conj (a t).toLinearMap e.symm.toLinearEquiv
  have hbdet (t : ℝ) : (b' t).toLinearMap.det = (b t).toLinearMap.det :=
    LinearMap.det_conj (b t).toLinearMap e.symm.toLinearEquiv
  have hsign' : 0 < (a' 0).toLinearMap.det * (b' 1).toLinearMap.det := by
    rw [hadet, hbdet]
    exact hsign
  obtain ⟨L', hL', hi', hdet', hleft, hright⟩ :=
    Smale.PlanarFrame.exists_smooth_join_of_same_determinant_sign ha' hb' hU hV h0U h1V hsign'
  let L (t : ℝ) := e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp (hL'.clm_comp contDiff_const)
  have hi (t : ℝ) : Function.Bijective (L t) := e.bijective.comp ((hi' t).comp e.symm.bijective)
  have hdet (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have heq : (L t).toLinearMap.det = (L' t).toLinearMap.det :=
      LinearMap.det_conj (L' t).toLinearMap e.toLinearEquiv
    rw [heq, ← hadet 0]
    exact hdet' t
  refine ⟨L, hL, hi, hdet, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = a t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (a t (e (e.symm v)))) = a t v
    simp only [e.apply_symm_apply]
  · filter_upwards [hright] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = b t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (b t (e (e.symm v)))) = b t v
    simp only [e.apply_symm_apply]

private theorem
    Smale.FrameField.exists_global_field_with_closed_germ {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : Smale.PlaneImmersion.Plane → F} {U C : Set Smale.PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) :
    ∃ L₀ : Smale.PlaneImmersion.Plane → F, ContDiff ℝ ∞ L₀ ∧ L₀ =ᶠ[𝓝ˢ C] L := by
  have hdisj : Disjoint Uᶜ C := Set.disjoint_left.mpr (fun _ hxU hxC => hxU (hCU hxC))
  obtain ⟨β, hβ0, hβ1, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, Smale.PlaneImmersion.Plane)
      hU.isClosed_compl hC hdisj (n := ⊤)
  let L₀ : Smale.PlaneImmersion.Plane → F := fun x => β x • L x
  have hβ : ContDiff ℝ ∞ (β : Smale.PlaneImmersion.Plane → ℝ) := β.contMDiff.contDiff
  have hL₀ : ContDiff ℝ ∞ L₀ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hx))
    · apply
        (contDiffAt_const :
            ContDiffAt ℝ ∞ (fun _ : Smale.PlaneImmersion.Plane => (0 : F))
              x).congr_of_eventuallyEq
      have hβx : ∀ᶠ y in 𝓝 x, β y = 0 := hβ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hβx] with y hy
      change β y • L y = 0
      rw [hy, zero_smul]
  refine ⟨L₀, hL₀, ?_⟩
  filter_upwards [hβ1] with x hx
  change β x • L x = L x
  rw [hx, one_smul]

private theorem
    Smale.FrameField.exists_nonzero_field_rel_closed {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {v : P → F} (hv : ContDiff ℝ ∞ v)
    (hdim : Module.finrank ℝ P < Module.finrank ℝ F) {K C : Set P} (hK : IsCompact K)
    (hC : IsClosed C) (hne : ∀ x ∈ K ∩ C, v x ≠ 0) :
    ∃ v' : P → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  let B : Set P := K ∩ v ⁻¹' {0}
  have hB : IsCompact B := hK.inter_right (isClosed_singleton.preimage hv.continuous)
  have hdisj : Disjoint C B := Set.disjoint_left.mpr (fun x hxC hxB => hne x ⟨hxB.1, hxC⟩ hxB.2)
  obtain ⟨β, hβ0, hβ1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, P) hC hB.isClosed hdisj (n := ⊤)
  have hfixed : ∀ x ∈ K, β x = 0 → v x ≠ 0 := by
    intro x hx hβx hvx
    have heq : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hvx⟩
    exact zero_ne_one (hβx.symm.trans heq)
  let Z := EuclideanSpace ℝ (Fin 0)
  let g : Z → F := fun _ => 0
  have hg : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ g := contMDiff_const
  have hdim' : Module.finrank ℝ P + Module.finrank ℝ Z < Module.finrank ℝ F := by
    simpa only [Z, finrank_euclideanSpace_fin, add_zero] using hdim
  obtain ⟨a, -, ha⟩ :=
    Smale.exists_small_localized_image_avoidance hv.contMDiff hg β.contMDiff hdim'
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => v x + β x • a, hv.add (β.contMDiff.contDiff.smul contDiff_const), ?_, ?_⟩
  · filter_upwards [hβ0] with x hx
    rw [hx, zero_smul, add_zero]
  · intro x hx
    by_cases hβx : β x = 0
    · simpa only [hβx, zero_smul, add_zero] using hfixed x hx hβx
    · exact ha x hβx (0 : Z)

private theorem Smale.FrameField.exists_nonzero_extension_of_local_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {v : Smale.PlaneImmersion.Plane → F} {U C K : Set Smale.PlaneImmersion.Plane} (hU : IsOpen U)
    (hv : ContDiffOn ℝ ∞ v U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ v' : Smale.PlaneImmersion.Plane → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  obtain ⟨v₀, hv₀, heq⟩ := exists_global_field_with_closed_germ hU hv hC hCU
  have hne₀ : ∀ x ∈ K ∩ C, v₀ x ≠ 0 := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hne x hx
  have hdim' : Module.finrank ℝ Smale.PlaneImmersion.Plane < Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ F
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v', hv', hgerm, hne'⟩ := exists_nonzero_field_rel_closed hv₀ hdim' hK hC hne₀
  exact ⟨v', hv', hgerm.trans heq, hne'⟩

private theorem
    Smale.FrameField.injective_iff_ne_zero_of_finrank_one {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) (L : A →L[ℝ] F) : Function.Injective L ↔ L ≠ 0 := by
  constructor
  · intro hi hzero
    let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply hi
    rw [hzero]
    rfl
  · intro hne
    have hr : L.range ≠ ⊥ := by
      intro hbot
      have hz : L.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
      apply hne
      ext x
      exact congrArg (fun f : A →ₗ[ℝ] F => f x) hz
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    have hpos : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr hr
    have hk : Module.finrank ℝ L.ker = 0 := by
      rw [hA] at hrank
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

private theorem
    Smale.FrameField.finrank_one_column {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) : Module.finrank ℝ (A →L[ℝ] F) = Module.finrank ℝ F := by
  rw [← (LinearMap.toContinuousLinearMap : (A →ₗ[ℝ] F) ≃ₗ[ℝ] (A →L[ℝ] F)).finrank_eq,
    Module.finrank_linearMap, hA, one_mul]

private theorem Smale.FrameField.exists_one_column_extension_of_local_field {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : Smale.PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set Smale.PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Function.Injective (L x)) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ L' : Smale.PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧ ∀ x ∈ K, Function.Injective (L' x) := by
  have hne : ∀ x ∈ K ∩ C, L x ≠ 0 := fun x hx =>
    (injective_iff_ne_zero_of_finrank_one hA (L x)).mp (hi x hx)
  have hdim' : 3 ≤ Module.finrank ℝ (A →L[ℝ] F) := by rwa [finrank_one_column hA]
  obtain ⟨L', hL', heq, hne'⟩ := exists_nonzero_extension_of_local_field hU hL hC hCU hK hne hdim'
  exact
    ⟨L', hL', heq, fun x hx => (injective_iff_ne_zero_of_finrank_one hA (L' x)).mpr (hne' x hx)⟩

private theorem
    Smale.FrameField.exists_completed_one_column_frame {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : Smale.PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set Smale.PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : Smale.PlaneImmersion.Plane) K)
    (h0 : (0 : Smale.PlaneImmersion.Plane) ∈ K) (hi : ∀ x ∈ K ∩ C, Function.Injective (L x))
    (hdim : Module.finrank ℝ F = 3) :
    ∃ L' : Smale.PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧
        L' =ᶠ[𝓝ˢ C] L ∧
          ∃ V : Set Smale.PlaneImmersion.Plane,
            IsOpen V ∧
              K ⊆ V ∧
                ∃ B : Smale.PlaneImmersion.Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
                  ContDiffOn ℝ ∞ B V ∧
                    (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
                      ∀ x ∈ V, Function.Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_one_column_extension_of_local_field hA hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ A + 2 = Module.finrank ℝ F := by rw [hA, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

private theorem Smale.FrameField.eq_det_smul_id_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A : D →L[ℝ] D) :
    A.toLinearMap = A.toLinearMap.det • LinearMap.id := by
  obtain ⟨a, ha, -⟩ := A.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hdet : A.toLinearMap.det = a := by
    rw [ha, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]
  rw [hdet]
  exact ha

private theorem Smale.FrameField.det_smul_add_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A B : D →L[ℝ] D) (a b : ℝ) :
    (a • A + b • B).toLinearMap.det = a * A.toLinearMap.det + b * B.toLinearMap.det := by
  have hlin :
    (a • A + b • B).toLinearMap =
      (a * A.toLinearMap.det + b * B.toLinearMap.det) • LinearMap.id := by
    calc
      _ = a • (A.toLinearMap.det • LinearMap.id) + b • (B.toLinearMap.det • LinearMap.id) :=
        congrArg₂ (fun L K : D →ₗ[ℝ] D => a • L + b • K) (eq_det_smul_id_of_finrank_one hdim A)
          (eq_det_smul_id_of_finrank_one hdim B)
      _ = _ := by rw [smul_smul, smul_smul, ← add_smul]
  rw [hlin, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]

private theorem Smale.FrameField.exists_smooth_invertible_join_of_finrank_one {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 1) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S : TopologicalSpace.Opens (D →L[ℝ] D) :=
    ⟨{L | 0 < σ * L.toLinearMap.det},
      isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hpos : 0 < σ * (a 0).toLinearMap.det := mul_self_pos.mpr ha0ne
  have ha0 : a 0 ∈ S := hpos
  have hb1 : b 1 ∈ S := hsign
  let γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S) :=
    { toFun := fun t =>
        ⟨(1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1,
          by
          change 0 < σ * ((1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1).toLinearMap.det
          rw [det_smul_add_of_finrank_one hdim]
          have heq :
            σ * ((1 - (t : ℝ)) * (a 0).toLinearMap.det + (t : ℝ) * (b 1).toLinearMap.det) =
              (1 - (t : ℝ)) * (σ * (a 0).toLinearMap.det) +
                (t : ℝ) * (σ * (b 1).toLinearMap.det) := by ring
          rw [heq]
          by_cases ht : (t : ℝ) = 0
          · simpa only [ht, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero] using hpos
          · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
            exact
              add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hpos.le)
                (mul_pos htpos hsign)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      source' := by
        apply Subtype.ext
        simp
      target' := by
        apply Subtype.ext
        simp }
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

private theorem Smale.FrameField.mul_endpoints_pos_of_continuous_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) :
    0 < f 0 * f 1 := by
  by_contra h
  rcases mul_nonpos_iff.mp (le_of_not_gt h) with h | h
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf ⟨h.2, h.1⟩
    exact hne t ht hft
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf h
    exact hne t ht hft

private theorem Smale.FrameField.det_mul_endpoints_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {T : ℝ → (E →L[ℝ] E)}
    (hT : ContinuousOn T (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t)) :
    0 < (T 0).toLinearMap.det * (T 1).toLinearMap.det := by
  apply
    mul_endpoints_pos_of_continuous_nonzero
      (ContinuousLinearMap.continuous_det.comp_continuousOn hT)
  intro t ht hz
  have hker : (T t).toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hker (LinearMap.ker_eq_bot.mpr (hi t ht).1)

private theorem
    Smale.FrameField.same_sign_frames_iff_coefficients {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible) :
    (0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) ↔
      (0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  have hs : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hT : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t) := fun t ht =>
    j.symm.bijective.comp (hi t ht).bijective
  have hpositive := det_mul_endpoints_pos hs.continuousOn hT
  have h0 := det_frame_eq_det_split_mul_det_coefficient j (G 0) (C 0) (L 0) (hi 0 (by simp))
  have h1 := det_frame_eq_det_split_mul_det_coefficient j (G 1) (C 1) (L 1) (hi 1 (by simp))
  rw [h0, h1]
  have heq :
    ((T 0).toLinearMap.det * ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det) *
        ((T 1).toLinearMap.det * ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) =
      ((T 0).toLinearMap.det * (T 1).toLinearMap.det) *
        (((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by ring
  change (0 < ((T 0).toLinearMap.det * _) * ((T 1).toLinearMap.det * _)) ↔ _
  rw [heq]
  exact mul_pos_iff_of_pos_left hpositive

private theorem Smale.FrameField.exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (h1U : (1 : ℝ) ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ U, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective (G t) (C t) (hi t ht)
  let K (t : ℝ) := (complementQuotient (G t) (C t)).comp (L t)
  have hK : ContDiffOn ℝ ∞ K U := (contDiffOn_complementQuotient hU hG hC hinv).clm_comp hL
  have hjoin :=
    hdim.elim
      (fun hd => exists_smooth_invertible_join_of_finrank_one hd hK hK hU hU h0U h1U hsign)
      (fun hd => exists_smooth_invertible_join_of_finrank_two hd hK hK hU hU h0U h1U hsign)
  obtain ⟨K', hK', hiK', _, hleft, hright⟩ := hjoin
  let H (t : ℝ) := correctedComplement (G t) (C t) (L t) (K' t)
  have hH : ContDiffOn ℝ ∞ H U := contDiffOn_correctedComplement hU hG hC hL hK'.contDiffOn hinv
  refine
    ⟨H, hH, fun t ht =>
      bijective_coprod_correctedComplement (G t) (C t) (L t) (K' t) (hinv t ht) (hiK' t), ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)
  · filter_upwards [hright] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)

private theorem
    Smale.FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    (j : (D × Z) ≃L[ℝ] F) {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ ∞ G U)
    (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective _ _ (hi t (hIU ht))
  have hcoeff := (same_sign_frames_iff_coefficients j (hG.mono hIU) (hC.mono hIU) hinv).mp hsign
  exact
    exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two hdim hU (hIU (by simp))
      (hIU (by simp)) hG hC hL hi hcoeff

private theorem Smale.WhitneyPairModel.exists_smooth_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ} (hh : 0 < h) {L H : ℝ → F} {D : Set ℝ}
    (hD : IsOpen D) (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D)
    (hH : ContDiffOn ℝ ∞ H D) (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L) :
    ∃ U V : Set (ℝ × ℝ),
      IsOpen U ∧
        IsOpen V ∧
          frontier (bigon h) ⊆ U ∪ V ∧
            Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                ∃ W : (ℝ × ℝ) → F,
                  ContDiffOn ℝ ∞ W (U ∪ V) ∧
                    Set.EqOn W (L ∘ arcTime) U ∧ Set.EqOn W (H ∘ arcTime) V := by
  let P := arcTime ⁻¹' D
  have hP : IsOpen P := hD.preimage contDiff_arcTime.continuous
  have hLP : ContDiffOn ℝ ∞ (L ∘ arcTime) P :=
    hL.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have hHP : ContDiffOn ℝ ∞ (H ∘ arcTime) P :=
    hH.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have htime0 : Filter.Tendsto arcTime (𝓝 ((-1 : ℝ), (0 : ℝ))) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((-1 : ℝ), (0 : ℝ))))
  have htime1 : Filter.Tendsto arcTime (𝓝 ((1 : ℝ), (0 : ℝ))) (𝓝 (1 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((1 : ℝ), (0 : ℝ))))
  have hg0 : (L ∘ arcTime) =ᶠ[𝓝 ((-1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h0.symm.comp_tendsto htime0
  have hg1 : (L ∘ arcTime) =ᶠ[𝓝 ((1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h1.symm.comp_tendsto htime1
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp hg0
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ := mem_nhds_iff.mp hg1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have hlowP : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) P := by
    intro t ht
    change arcTime (2 * t - 1, 0) ∈ D
    rw [htime]
    exact hID ht
  have huppP : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) P :=
    by
    intro t ht
    change arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ D
    rw [htime]
    exact hID ht
  obtain ⟨U, V, hU, hV, hUP, hVP, hover, hlowU, huppV, hfront⟩ :=
    exists_bigon_boundary_cover hh hP hP (hO₀.union hO₁) (Or.inl hleft) (Or.inr hright) hlowP
      huppP
  have hLH : Set.EqOn (L ∘ arcTime) (H ∘ arcTime) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨W, hW, hWL, hWH⟩ :=
    Smale.exists_smooth_open_gluing hU hV (hLP.mono hUP).contMDiffOn (hHP.mono hVP).contMDiffOn
      hLH
  exact ⟨U, V, hU, hV, hfront, hlowU, huppV, W, hW.contDiffOn, hWL, hWH⟩

private theorem Smale.WhitneyPairModel.exists_injective_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {h : ℝ} (hh : 0 < h) {L H : ℝ → (A →L[ℝ] F)} {D : Set ℝ} (hD : IsOpen D)
    (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D) (hH : ContDiffOn ℝ ∞ H D)
    (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L)
    (hiL : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (L t))
    (hiH : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (A →L[ℝ] F),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, W =ᶠ[𝓝 (2 * t - 1, 0)] (L ∘ arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    W =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] (H ∘ arcTime)) ∧
                  ∀ p ∈ frontier (bigon h), Function.Injective (W p) := by
  obtain ⟨U, V, hU, hV, hfront, hlow, hupp, W, hW, hWL, hWH⟩ :=
    exists_smooth_bigon_boundary_field hh hD hID hL hH h0 h1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  refine ⟨U ∪ V, hU.union hV, hfront, W, hW, ?_, ?_, ?_⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlow ht)) (fun _ hp => hWL hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (hupp ht)) (fun _ hp => hWH hp)
  · intro p hp
    obtain ⟨t, ht, rfl | rfl⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
    · rw [hWL (hlow ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiL t ht
    · rw [hWH (hupp ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiH t ht

private def Smale.FrameField.rankThreePairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

private def Smale.FrameField.rankThreePairDet
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (rankThreePairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

private theorem Smale.TubularBigon.exists_rankThree_boundary_complement_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        Set.Icc (0 : ℝ) 1 ⊆ U ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
            ∃ H : ℝ → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
              ContDiffOn ℝ ∞ H U ∧
                (∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
                  (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
                    (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, -⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, -, hRC⟩ :=
    tube.upper_sheetFrame_complement_of_finrank e 1 (by simp only [finrank_euclideanSpace_fin])
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Set.Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from Set.inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from Set.inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from Set.inter_subset_right)
  have hsplit : ∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    Smale.FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
      (Or.inl finrank_euclideanSpace_fin) Smale.FrameField.rankThreePairCoordinates hU hIU hRU hCU
      hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

private theorem
    Smale.TubularBigon.exists_rankThree_planar_boundary_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (Smale.WhitneyPairModel.bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                  W =ᶠ[𝓝 (2 * t - 1, 0)]
                    (d.normalFrame tube.chart ∘ Smale.WhitneyPairModel.arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    Function.Bijective
                      ((e.normalFrame tube.chart t).coprod
                        (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
                  ∀ p ∈ frontier (Smale.WhitneyPairModel.bigon h), Function.Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_rankThree_boundary_complement_of_normal_sign d e hsign
  have hHi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t) := by
    intro t ht u v huv
    have heq :
      ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  obtain ⟨O, hO, hfront, W, hW, hlo, hhi, hinj⟩ :=
    Smale.WhitneyPairModel.exists_injective_bigon_boundary_field tube.height_pos hD hID hL hH h0
      h1 (tube.lower_sheetFrame d).2 hHi
  refine ⟨O, hO, hfront, W, hW, hlo, ?_, hinj⟩
  intro t ht
  rw [(hhi t ht).eq_of_nhds]
  have htime : Smale.WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = t := by
    dsimp [Smale.WhitneyPairModel.arcTime]
    ring
  change
    Function.Bijective
      ((e.normalFrame tube.chart t).coprod
        (H (Smale.WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))))
  rw [htime]
  exact hcomp t (hID ht)

private theorem Smale.TubularBigon.exists_rankThree_planar_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ Smale.WhitneyPairModel.arcTime)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
              Function.Bijective
                ((e.normalFrame tube.chart t).coprod
                  (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
            ∃ V : Set (ℝ × ℝ),
              IsOpen V ∧
                Smale.WhitneyPairModel.bigon h ⊆ V ∧
                  ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                    ContDiffOn ℝ ∞ B V ∧
                      (∀ p ∈ Smale.WhitneyPairModel.bigon h, (B p).range = (W p).rangeᗮ) ∧
                        ∀ p ∈ V, Function.Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_rankThree_planar_boundary_frame_of_normal_sign d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    Smale.FrameField.exists_completed_one_column_frame finrank_euclideanSpace_fin hO hW₀
      isClosed_frontier hfront (Smale.WhitneyPairModel.isCompact_bigon tube.height_pos)
      (Smale.WhitneyPairModel.starConvex_bigon tube.height_pos.le)
      (Smale.WhitneyPairModel.zero_mem_bigon tube.height_pos.le) (fun p hp => hinj p hp.2)
      finrank_euclideanSpace_fin
  refine ⟨W, hW, ?_, ?_, V, hV, hKV, B, hB, hr, hb⟩
  · intro t ht
    have hp : (2 * t - 1, 0) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact (heq.filter_mono (nhds_le_nhdsSet hp)).trans (hlo t ht)
  · intro t ht
    have hp :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    rw [heq.self_of_nhdsSet hp]
    exact hhi t ht

private theorem Smale.FrameField.bijective_coprod_comm {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (H : Z →L[ℝ] F) (hi : Function.Bijective (H.coprod W)) :
    Function.Bijective (W.coprod H) := by
  have heq :
    W.coprod H = (H.coprod W).comp (ContinuousLinearEquiv.prodComm ℝ D Z).toContinuousLinearMap :=
    by
    apply ContinuousLinearMap.ext
    intro p
    change W p.1 + H p.2 = H p.2 + W p.1
    exact add_comm _ _
  rw [heq]
  exact hi.comp (ContinuousLinearEquiv.prodComm ℝ D Z).bijective

private def
    Smale.FrameField.transportComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F) : Z →L[ℝ] F :=
  (W.coprod B).comp ((W₀.coprod B₀).inverse.comp H)

private theorem Smale.FrameField.transportComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B H : Z →L[ℝ] F) (h : (W.coprod B).IsInvertible) :
    transportComplement W B W B H = H := by
  apply ContinuousLinearMap.ext
  intro z
  exact h.self_apply_inverse (H z)

private theorem Smale.FrameField.coprod_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h₀ : (W₀.coprod B₀).IsInvertible) :
    W.coprod (transportComplement W B W₀ B₀ H) =
      ((W.coprod B).comp (W₀.coprod B₀).inverse).comp (W₀.coprod H) := by
  have hfirst (u : D) : (W₀.coprod B₀).inverse (W₀ u) = (u, 0) := by
    simpa only [ContinuousLinearMap.coprod_apply, map_zero, add_zero] using
      h₀.inverse_apply_self (u, 0)
  apply ContinuousLinearMap.ext
  intro p
  simp only [transportComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, map_add, hfirst, map_zero, add_zero]

private theorem
    Smale.FrameField.bijective_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h : (W.coprod B).IsInvertible) (h₀ : (W₀.coprod B₀).IsInvertible)
    (hH : Function.Bijective (W₀.coprod H)) :
    Function.Bijective (W.coprod (transportComplement W B W₀ B₀ H)) := by
  rw [coprod_transportComplement W B W₀ B₀ H h₀]
  exact (h.bijective.comp h₀.inverse.bijective).comp hH

private theorem
    Smale.FrameField.contDiffOn_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {W W₀ : X → (D →L[ℝ] F)} {B B₀ H : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U) (hB : ContDiffOn ℝ ∞ B U)
    (hW₀ : ContDiffOn ℝ ∞ W₀ U) (hB₀ : ContDiffOn ℝ ∞ B₀ U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : ∀ x ∈ U, ((W₀ x).coprod (B₀ x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => transportComplement (W x) (B x) (W₀ x) (B₀ x) (H x)) U := by
  have hT₀ := contDiffOn_coprod hW₀ hB₀
  have hInv : ContDiffOn ℝ ∞ (fun x => ((W₀ x).coprod (B₀ x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT₀.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact (contDiffOn_coprod hW hB).clm_comp (hInv.clm_comp hH)

private theorem Smale.TubularBigon.exists_rankThree_adapted_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ Smale.WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              Smale.WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (Smale.WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) := by
  obtain ⟨W, hW, hlo, hhi, V, hV, hKV, B, hB, -, hb⟩ :=
    tube.exists_rankThree_planar_frame_of_normal_sign d e hsign
  obtain ⟨⟨D, hD, hID, hG⟩, -⟩ := tube.upper_sheetFrame e
  let r : (ℝ × ℝ) → (ℝ × ℝ) :=
    Smale.WhitneyPairModel.upperBoundaryArc h ∘ Smale.WhitneyPairModel.arcTime
  have hq : ContDiff ℝ ∞ (Smale.WhitneyPairModel.upperBoundaryArc h) := by
    unfold Smale.WhitneyPairModel.upperBoundaryArc; fun_prop
  have hr : ContDiff ℝ ∞ r := hq.comp Smale.WhitneyPairModel.contDiff_arcTime
  have htime (t y : ℝ) : Smale.WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [Smale.WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    Smale.WhitneyPairModel.arcTime (Smale.WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have hrq (t : ℝ) :
    r (Smale.WhitneyPairModel.upperBoundaryArc h t) =
      Smale.WhitneyPairModel.upperBoundaryArc h t := by
    dsimp only [r, Function.comp_apply]
    rw [htq]
  have htimeK :
    Set.MapsTo Smale.WhitneyPairModel.arcTime (Smale.WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have hrK : Set.MapsTo r (Smale.WhitneyPairModel.bigon h) (Smale.WhitneyPairModel.bigon h) :=
    fun _ hp => tube.upperBoundaryArc_mem_bigon (htimeK hp)
  let O₀ := V ∩ (r ⁻¹' V ∩ Smale.WhitneyPairModel.arcTime ⁻¹' D)
  have hO₀ : IsOpen O₀ :=
    hV.inter
      ((hV.preimage hr.continuous).inter
        (hD.preimage Smale.WhitneyPairModel.contDiff_arcTime.continuous))
  have hKO₀ : Smale.WhitneyPairModel.bigon h ⊆ O₀ := fun p hp =>
    ⟨hKV hp, hKV (hrK hp), hID (htimeK hp)⟩
  let C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := fun p =>
    Smale.FrameField.transportComplement (W p) (B p) (W (r p)) (B (r p))
      (e.normalFrame tube.chart (Smale.WhitneyPairModel.arcTime p))
  have hC : ContDiffOn ℝ ∞ C O₀ := by
    apply
      Smale.FrameField.contDiffOn_transportComplement hO₀ hW.contDiffOn
        (hB.mono Set.inter_subset_left) (hW.comp hr).contDiffOn
        (hB.comp hr.contDiffOn (fun _ hp => hp.2.1))
        (hG.comp Smale.WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
    intro p hp
    exact Smale.FrameField.isInvertible_coprod_of_bijective (W (r p)) (B (r p)) (hb _ hp.2.1)
  have hcompK : ∀ p ∈ Smale.WhitneyPairModel.bigon h, Function.Bijective ((W p).coprod (C p)) := by
    intro p hp
    have ht := htimeK hp
    have hupper :
      Function.Bijective
        ((W (r p)).coprod (e.normalFrame tube.chart (Smale.WhitneyPairModel.arcTime p))) :=
      Smale.FrameField.bijective_coprod_comm _ _ (hhi (Smale.WhitneyPairModel.arcTime p) ht)
    exact
      Smale.FrameField.bijective_transportComplement (W p) (B p) (W (r p)) (B (r p)) _
        (Smale.FrameField.isInvertible_coprod_of_bijective _ _ (hb p (hKV hp)))
        (Smale.FrameField.isInvertible_coprod_of_bijective _ _ (hb _ (hKV (hrK hp)))) hupper
  have hTC : ContDiffOn ℝ ∞ (fun p => (W p).coprod (C p)) O₀ :=
    Smale.FrameField.contDiffOn_coprod hW.contDiffOn hC
  let O := O₀ ∩ {p | Function.Injective ((W p).coprod (C p))}
  have hO : IsOpen O :=
    hTC.continuousOn.isOpen_inter_preimage hO₀ ContinuousLinearMap.isOpen_injective
  have hKO : Smale.WhitneyPairModel.bigon h ⊆ O := fun p hp => ⟨hKO₀ hp, (hcompK p hp).1⟩
  refine ⟨W, hW, hlo, O, hO, hKO, C, hC.mono Set.inter_subset_left, ?_, ?_⟩
  · intro t ht
    dsimp only [C]
    rw [hrq, htq]
    exact
      Smale.FrameField.transportComplement_self _ _ _
        (Smale.FrameField.isInvertible_coprod_of_bijective _ _
          (hb _ (hKV (tube.upperBoundaryArc_mem_bigon ht))))
  · intro p hp
    have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact ⟨hp.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp.2⟩

private def Smale.TubularBigon.rankThreeSheetPairJacobian {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) :
    ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) →L[ℝ]
      ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :=
  Smale.IntersectionCoordinates.jointBlock Smale.FrameField.rankThreePairCoordinates
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)

private def Smale.TubularBigon.rankThreeSheetPairDet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) : ℝ :=
  (tube.rankThreeSheetPairJacobian d e t).toLinearMap.det

private theorem Smale.TubularBigon.rankThree_corner_sheet_charts_coincide {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t = 0 ∨ t = 1) :
    d.chart (Smale.StripCoordinates.center t) = e.chart (Smale.StripCoordinates.center t) := by
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hd := (tube.lower_germ t htI).eq_of_nhds
  have he := (tube.upper_germ t htI).eq_of_nhds
  dsimp only [Function.comp_apply] at hd he
  rw [Smale.WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hd
  rw [Smale.WhitneyPairModel.upperStripCoordinates_upper, e.center t, hheight] at he
  exact hd.symm.trans he

private theorem Smale.TubularBigon.rankThreeSheetPairDet_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tube.rankThreeSheetPairDet d e t =
      (8 * h * (2 * t - 1)) *
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart t)
          (d.normalFrame tube.chart t) := by
  rw [rankThreeSheetPairDet, rankThreeSheetPairJacobian,
    Smale.IntersectionCoordinates.det_jointBlock Smale.FrameField.rankThreePairCoordinates
      (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
      (tube.upper_sheetDifferential_arc e ht) (tube.lower_sheetDifferential_arc d ht),
    e.normal_sheetDifferential tube.chart ht (tube.upper_chart_center_mem_target e ht),
    d.normal_sheetDifferential tube.chart ht (tube.lower_chart_center_mem_target d ht)]
  have hplane :
    (Smale.PlaneImmersion.linearMap ((2, -4 * h * (2 * t - 1)), (2, 0))).toLinearMap.det =
      8 * h * (2 * t - 1) := by
    rw [← Smale.PlanarFrame.determinant_eq_det, Smale.PlanarFrame.determinant_linearMap]
    dsimp [Smale.PlanarFrame.area]
    ring
  rw [hplane]
  rfl

private theorem
    Smale.TubularBigon.opposite_rankThree_corner_determinants_iff_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (0 <
        Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) := by
  let n :=
    Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      Smale.FrameField.rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)
  have hprod :
    tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 = -((8 * h) ^ 2 * n) := by
    rw [tube.rankThreeSheetPairDet_eq d e (t := 0) (by simp),
      tube.rankThreeSheetPairDet_eq d e (t := 1) (by simp)]
    dsimp only [n]
    ring
  have hscale : 0 < (8 * h) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) tube.height_pos)
  change (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔ 0 < n
  rw [hprod]
  constructor
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := by linarith
    exact (mul_pos_iff_of_pos_left hscale).mp hp
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := mul_pos hscale hn
    linarith

private theorem
    Smale.TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ Smale.WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              Smale.WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (Smale.WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) :=
  tube.exists_rankThree_adapted_frame_of_normal_sign d e
    ((tube.opposite_rankThree_corner_determinants_iff_normal_sign d e).mp hsign)

private def Smale.IntersectionCoordinates.pairCoordinates {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) :
    ((ℝ × A) × (ℝ × B)) ≃L[ℝ] (Smale.PlaneImmersion.Plane × F) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Smale.PlaneImmersion.Plane) j)

private theorem Smale.IntersectionCoordinates.det_jointBlock_eq_tangentSum {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Smale.PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (Smale.PlaneImmersion.Plane × F)) :
    (jointBlock j P Q).det =
      ((pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)).det := by
  let k := ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B
  let T := (pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)
  have heq :
    (jointBlock j P Q).toLinearMap =
      k.toLinearEquiv.toLinearMap.comp (T.toLinearMap.comp k.symm.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro z
    rfl
  change (jointBlock j P Q).toLinearMap.det = T.toLinearMap.det
  rw [heq]
  exact LinearMap.det_conj T.toLinearMap k.toLinearEquiv

private theorem
    Smale.FrameField.normalDetector_eq_comp_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    Q = (Q.comp C).comp (complementQuotient G C) := by
  apply ContinuousLinearMap.ext
  intro v
  let w := (G.coprod C).inverse v
  have hv : G w.1 + C w.2 = v := hi.self_apply_inverse v
  have hzero : Q (G w.1) = 0 := congrArg (fun L : D →L[ℝ] Z => L w.1) hQG
  change Q v = Q (C w.2)
  rw [← hv, map_add, hzero, zero_add]

private theorem Smale.FrameField.det_intersection_mul_normalComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det * (Q.comp C).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det * (Q.comp L).det := by
  have hnormal : Q.comp L = (Q.comp C).comp ((complementQuotient G C).comp L) := by
    have h := normalDetector_eq_comp_quotient G C Q hi hQG
    exact congrArg (fun R : F →L[ℝ] Z => R.comp L) h
  have hdet : (Q.comp L).det = (Q.comp C).det * ((complementQuotient G C).comp L).det := by
    rw [hnormal]
    exact LinearMap.det_comp _ _
  have hframe :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det *
        ((complementQuotient G C).comp L).det :=
    det_frame_eq_det_split_mul_det_coefficient j G C L hi
  rw [hframe, hdet]
  ring

private theorem Smale.FrameField.opposite_intersectionDet_iff_normalDet {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : ℝ → (D →L[ℝ] F)) (C L : ℝ → (Z →L[ℝ] F)) (Q : ℝ → (F →L[ℝ] Z))
    (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1)) (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible)
    (hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t))
    (hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0) :
    ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det <
        0) ↔
      ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det < 0 := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  let K (t : ℝ) := (Q t).comp (C t)
  have hT : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hK : ContDiffOn ℝ ∞ K (Set.Icc (0 : ℝ) 1) := hQ.clm_comp hC
  have hTpos :=
    det_mul_endpoints_pos hT.continuousOn (fun t ht => j.symm.bijective.comp (hi t ht).bijective)
  have hKpos :=
    det_mul_endpoints_pos hK.continuousOn
      (fun t ht =>
        Smale.TransverseCoordinates.bijective_normal_comp (Q t) (G t) (C t) (hQs t ht)
          (hi t ht).surjective (hQG t ht) rfl)
  have h₀ :=
    det_intersection_mul_normalComplement j (G 0) (C 0) (L 0) (Q 0) (hi 0 (by simp))
      (hQG 0 (by simp))
  have h₁ :=
    det_intersection_mul_normalComplement j (G 1) (C 1) (L 1) (Q 1) (hi 1 (by simp))
      (hQG 1 (by simp))
  let a :=
    (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det
  let b := ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det
  have heq : a * ((K 0).det * (K 1).det) = ((T 0).det * (T 1).det) * b := by
    dsimp [a, b, T, K]
    calc
      _ =
          ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
              ((Q 0).comp (C 0)).det) *
            ((j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det *
              ((Q 1).comp (C 1)).det) := by ring
      _ = _ := by rw [h₀, h₁]; ring
  change a < 0 ↔ b < 0
  constructor
  · intro ha
    have hn : ((T 0).det * (T 1).det) * b < 0 := heq ▸ mul_neg_of_neg_of_pos ha hKpos
    rcases mul_neg_iff.mp hn with ⟨_, hb⟩ | ⟨ht, _⟩
    · exact hb
    · exact (not_lt_of_gt hTpos ht).elim
  · intro hb
    have hn : a * ((K 0).det * (K 1).det) < 0 := heq.symm ▸ mul_neg_of_pos_of_neg hTpos hb
    rcases mul_neg_iff.mp hn with ⟨_, hk⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hKpos hk).elim
    · exact ha

private def Smale.StripNormalData.sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    A →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Z).comp
    ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A))

private theorem Smale.StripNormalData.contDiffOn_sheetDifferential {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetDifferential Ψ)
      {t |
        Smale.StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (Smale.StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hs : ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
    htransition.comp (t, 0) (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, (0 : A))) := contDiff_id.prodMk contDiff_const
  exact ((hs.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

private theorem
    Smale.StripNormalData.contDiffOn_sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ)
      {t |
        Smale.StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target} :=
  contDiffOn_const.clm_comp ((d.contDiffOn_sheetDifferential Ψ).clm_comp contDiffOn_const)

private theorem Smale.StripNormalData.exists_open_sheetBaseFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ) U := by
  have hc : Continuous (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact
    ⟨Smale.StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target), hO.preimage hc,
      fun t ht => ⟨d.line ht, htarget t ht⟩, d.contDiffOn_sheetBaseFrame Ψ⟩

private theorem Smale.StripNormalData.sheetDifferential_transverse_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (u : A) : d.sheetDifferential Ψ t (0, u) = (d.sheetBaseFrame Ψ t u, d.normalFrame Ψ t u) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun L : A →L[ℝ] Z => L u) (d.normal_sheetDifferential Ψ ht htarget)

private def
    Smale.StripNormalData.tubularTransitionDerivative {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    Smale.StripCoordinates.Space A B →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t)

private def Smale.StripNormalData.sheetComplement {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    B →L[ℝ] ((ℝ × ℝ) × Z) :=
  (d.tubularTransitionDerivative Ψ t).comp (ContinuousLinearMap.inr ℝ (ℝ × A) B)

private theorem Smale.StripNormalData.contDiffOn_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.tubularTransitionDerivative Ψ)
      {t |
        Smale.StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (Smale.StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hc : ContDiff ℝ ∞ (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact ((htransition.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

private theorem Smale.StripNormalData.contDiffOn_sheetComplement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetComplement Ψ)
      {t |
        Smale.StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target} :=
  (d.contDiffOn_tubularTransitionDerivative Ψ).clm_comp contDiffOn_const

private theorem Smale.StripNormalData.bijective_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    Function.Bijective (d.tubularTransitionDerivative Ψ t) := by
  unfold tubularTransitionDerivative
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (Smale.StripCoordinates.center t) (Ψ.symm.mdifferentiableAt (by simp) htarget)
      (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  exact
    (Smale.PartialChart.bijective_mfderiv Ψ.symm htarget).comp
      (Smale.PartialChart.bijective_mfderiv d.chart (d.line ht))

private theorem Smale.StripNormalData.sheet_coprod_complement_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t) =
      d.tubularTransitionDerivative Ψ t := by
  rw [d.sheetDifferential_eq Ψ ht htarget]
  apply ContinuousLinearMap.ext
  intro z
  change
    d.tubularTransitionDerivative Ψ t (z.1, 0) + d.tubularTransitionDerivative Ψ t (0, z.2) =
      d.tubularTransitionDerivative Ψ t z
  rw [← map_add]
  simp

private theorem Smale.StripNormalData.isInvertible_sheet_coprod_complement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) [FiniteDimensional ℝ A]
    [FiniteDimensional ℝ B] {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    ((d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t)).IsInvertible := by
  apply Smale.FrameField.isInvertible_coprod_of_bijective
  rw [d.sheet_coprod_complement_eq Ψ ht htarget]
  exact d.bijective_tubularTransitionDerivative Ψ ht htarget

private def Smale.StripNormalData.normalDetector {A B Z E M N : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) (t : ℝ) :
    ((ℝ × ℝ) × Z) →L[ℝ] N :=
  fderiv ℝ (q ∘ Ψ) (Ψ.symm (d.chart (Smale.StripCoordinates.center t)))

private theorem Smale.StripNormalData.contDiffAt_normalMap_in_tube {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (Smale.StripCoordinates.center t))) :
    ContDiffAt ℝ ∞ (q ∘ Ψ) (Ψ.symm (d.chart (Smale.StripCoordinates.center t))) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (Smale.StripCoordinates.center t))) =
      d.chart (Smale.StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (Ψ (Ψ.symm (d.chart (Smale.StripCoordinates.center t)))) :=
    hinv.symm ▸ hq
  exact
    (hq'.comp _
        (Ψ.contMDiffOn_toFun.contMDiffAt
          (Ψ.open_source.mem_nhds (Ψ.map_target' htarget)))).contDiffAt

private theorem Smale.StripNormalData.contDiffOn_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (Smale.StripCoordinates.center t) ∈ O) :
    ContDiffOn ℝ ∞ (d.normalDetector Ψ q) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hqΨ :=
    d.contDiffAt_normalMap_in_tube Ψ q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht)))
  have hc : ContDiff ℝ ∞ (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  have hx : ContDiffAt ℝ ∞ (fun s => Ψ.symm (d.chart (Smale.StripCoordinates.center s))) t :=
    (d.contDiffAt_tubularTransition Ψ ht (htarget t ht)).comp t hc.contDiffAt
  exact ((hqΨ.fderiv_right (by simp)).comp t hx).contDiffWithinAt

private theorem Smale.StripNormalData.normalDetector_eq_native {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (Smale.StripCoordinates.center t))) :
    d.normalDetector Ψ q t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (Smale.StripCoordinates.center t)) : E →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ
            (Ψ.symm (d.chart (Smale.StripCoordinates.center t))) :
          ((ℝ × ℝ) × Z) →L[ℝ] E) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (Smale.StripCoordinates.center t))) =
      d.chart (Smale.StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (Ψ (Ψ.symm (d.chart (Smale.StripCoordinates.center t)))) :=
    hinv.symm ▸ hq.mdifferentiableAt (by simp)
  unfold normalDetector
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp _ hq' (Ψ.mdifferentiableAt (by simp) (Ψ.map_target' htarget)), hinv]

private theorem Smale.StripNormalData.surjective_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (Smale.StripCoordinates.center t)))
    (hqs :
      Function.Surjective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (Smale.StripCoordinates.center t)))) :
    Function.Surjective (d.normalDetector Ψ q t) := by
  rw [d.normalDetector_eq_native Ψ q htarget hq]
  exact hqs.comp (Smale.PartialChart.bijective_mfderiv Ψ (Ψ.map_target' htarget)).surjective

private theorem Smale.StripNormalData.normalDetector_comp_sheet_eq_zero {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O) (hzero : ∀ y ∈ S ∩ O, q y = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : d.chart (Smale.StripCoordinates.center t) ∈ O) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) = 0 := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnearS : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), i w ∈ d.chart.source :=
    hi.preimage_mem_nhds (d.chart.open_source.mem_nhds (d.line ht))
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target ∩ O :=
    hd.preimage_mem_nhds ((Ψ.open_target.inter hO).mem_nhds ⟨htarget, hcenter⟩)
  have hvanish : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun _ => 0) := by
    filter_upwards [hnearS, hnear] with w hw hwo
    change q (Ψ (Ψ.symm (d.chart (i w)))) = 0
    have hinv : Ψ (Ψ.symm (d.chart (i w))) = d.chart (i w) := Ψ.right_inv' hwo.1
    rw [hinv]
    exact hzero _ ⟨(d.sheet _ hw).mpr rfl, hwo.2⟩
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget (hq.contMDiffAt (hO.mem_nhds hcenter))
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  have hder : fderiv ℝ ((q ∘ Ψ) ∘ d.sheetTransition Ψ) (t, (0 : A)) = 0 := by
    rw [hvanish.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : N) (t, (0 : A))).fderiv
  exact hchain.symm.trans hder

private theorem Smale.StripNormalData.normalDetector_comp_sheet {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (Smale.StripCoordinates.center t))) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) =
      fderiv ℝ (fun w : ℝ × A => q (d.chart (w, 0))) (t, 0) := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target :=
    hd.preimage_mem_nhds (Ψ.open_target.mem_nhds htarget)
  have heq :
    ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun w : ℝ × A => q (d.chart (w, 0))) := by
    filter_upwards [hnear] with w hw
    exact congrArg q (Ψ.right_inv' hw)
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget hq
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  exact hchain.symm.trans heq.fderiv_eq

private theorem
    Smale.TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : Smale.TubularBigon (E := E) S T a b k l h 3)
    (d : Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 1))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (Smale.StripCoordinates.center t) ∈ O)
    (hqs :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.Surjective
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) q
            (e.chart (Smale.StripCoordinates.center t)))) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (1, 0)).det <
        0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := Smale.IntersectionCoordinates.pairCoordinates Smale.FrameField.rankThreePairCoordinates
  let G := e.sheetDifferential tube.chart
  let L := d.sheetDifferential tube.chart
  let C (t : ℝ) := (e.sheetComplement tube.chart t).comp i.toContinuousLinearMap
  let Q := e.normalDetector tube.chart q
  have htarget :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (Smale.StripCoordinates.center t) ∈ tube.chart.target :=
    fun _ ht => tube.upper_chart_center_mem_target e ht
  have hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1) :=
    (e.contDiffOn_sheetDifferential tube.chart).mono (fun t ht => ⟨e.line ht, htarget t ht⟩)
  have hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1) :=
    ((e.contDiffOn_sheetComplement tube.chart).mono
          (fun t ht => ⟨e.line ht, htarget t ht⟩)).clm_comp
      contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1) :=
    e.contDiffOn_normalDetector tube.chart q hO hq htarget hcenter
  have hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := by
    intro t ht
    let p :=
      ContinuousLinearEquiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) i
    have heq :
      (G t).coprod (C t) =
        ((e.sheetDifferential tube.chart t).coprod (e.sheetComplement tube.chart t)).comp
          p.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    apply Smale.FrameField.isInvertible_coprod_of_bijective
    rw [heq]
    exact
      (e.isInvertible_sheet_coprod_complement tube.chart ht (htarget t ht)).bijective.comp
        p.bijective
  have hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t) := fun t ht =>
    e.surjective_normalDetector tube.chart q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht))) (hqs t ht)
  have hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0 := fun t ht =>
    e.normalDetector_comp_sheet_eq_zero tube.chart q hO hq hzero ht (htarget t ht) (hcenter t ht)
  have hsign :=
    Smale.FrameField.opposite_intersectionDet_iff_normalDet j G C L Q hG hC hQ hi hQs hQG
  have hdet (t : ℝ) :
    tube.rankThreeSheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    Smale.IntersectionCoordinates.det_jointBlock_eq_tangentSum
      Smale.FrameField.rankThreePairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.rankThree_corner_sheet_charts_coincide d e ht
    have hqD :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q
        (d.chart (Smale.StripCoordinates.center t)) :=
      hpoint.symm ▸ hq.contMDiffAt (hO.mem_nhds (hcenter t htI))
    have hQeq : Q t = d.normalDetector tube.chart q t := by
      change e.normalDetector tube.chart q t = d.normalDetector tube.chart q t
      unfold Smale.StripNormalData.normalDetector
      rw [hpoint]
    rw [hQeq]
    exact
      d.normalDetector_comp_sheet tube.chart q htI (tube.lower_chart_center_mem_target d htI) hqD
  rw [hdet 0, hdet 1]
  exact hsign.trans (by rw [hcoeff 0 (Or.inl rfl), hcoeff 1 (Or.inr rfl)])

private def
    Smale.ManifoldMorse.MorseSurgeryData.beltSheetNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) :
    D.UpperLevel → (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  j.symm ∘ D.beltNormal

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.opposite_belt_corners_iff_normal_sheet_determinants
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) {S : Set D.UpperLevel}
    {a b : ℝ → D.UpperLevel} {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∀
      (tube :
        Smale.TubularBigon (E := Smale.RegularLevel.Model E) S (Set.range D.surgery.beltSphere) a
          b k l h 3)
      (d :
        Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          Smale.RegularLevel.Model E) S k)
      (e :
        Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          Smale.RegularLevel.Model E) (Set.range D.surgery.beltSphere) l),
      (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (0, 0)).det *
            (fderiv ℝ
                (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (1, 0)).det <
          0 := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  intro tube d e
  have hq :
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞
      (D.beltSheetNormal j) D.beltNormalDomain :=
    j.symm.contDiff.contMDiff.comp_contMDiffOn (D.contMDiffOn_beltNormal hf)
  have hcenter (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (Smale.StripCoordinates.center t) ∈ Set.range D.surgery.beltSphere :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (Smale.StripCoordinates.center t) ∈ D.beltNormalDomain := by
    obtain ⟨v, hv⟩ := hcenter t ht
    exact hv ▸ D.belt_mem_normalDomain v
  apply
    tube.opposite_rankThree_corners_iff_normal_sheet_determinants d e (D.beltSheetNormal j)
      D.isOpen_beltNormalDomain hq
  · rintro y ⟨⟨v, rfl⟩, _⟩
    change j.symm (D.beltNormal (D.surgery.beltSphere v)) = 0
    rw [D.beltNormal_belt, map_zero]
  · exact hcenterO
  · intro t ht
    obtain ⟨v, hv⟩ := hcenter t ht
    rw [← hv]
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt
        (D.isOpen_beltNormalDomain.mem_nhds (D.belt_mem_normalDomain v))
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (D.surgery.beltSphere v)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hjSmooth :
      ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
      j.symm.contDiff.contMDiff
    rw [beltSheetNormal,
      mfderiv_comp _ (hjSmooth.mdifferentiableAt (by simp)) (hnormal.mdifferentiableAt (by simp)),
      hJ]
    exact j.symm.surjective.comp (D.surjective_beltNormal_derivative hf v)

private def Smale.NativeSheetCoordinates.projection {D B E M N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) (x : N) : D :=
  (Φ.symm (F x)).1

private theorem Smale.NativeSheetCoordinates.contMDiffOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) : ContMDiffOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hcoord : ContMDiffOn I 𝓘(ℝ, D × B) ∞ (Φ.symm ∘ F) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoord

private theorem Smale.NativeSheetCoordinates.injective_mfderiv_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) (hiF : Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, D) (projection Φ F) x) := by
  let C : N → (D × B) := Φ.symm ∘ F
  let T : G →L[ℝ] (D × B) := mfderiv I 𝓘(ℝ, D × B) C x
  have hC : ContMDiffAt I 𝓘(ℝ, D × B) ∞ C x :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hTi : Function.Injective T := by
    change Function.Injective (mfderiv I 𝓘(ℝ, D × B) (Φ.symm ∘ F) x)
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx) (hF.mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv Φ.symm hx).injective.comp hiF
  have hfst :
    (mfderiv I 𝓘(ℝ, D) (projection Φ F) x : G →L[ℝ] D) = (ContinuousLinearMap.fst ℝ D B).comp T :=
    by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) := contDiff_fst.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (C x) = ContinuousLinearMap.fst ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.fst ℝ D B).fderiv
    change mfderiv I 𝓘(ℝ, D) (Prod.fst ∘ C) x = _
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)), hd]
    rfl
  have hzero : (Prod.snd ∘ C) =ᶠ[𝓝 x] (fun _ => (0 : B)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with
      y hy
    exact (hclean _ (Φ.map_target' hy)).mp ⟨y, (Φ.right_inv' hy).symm⟩
  have hsnd : (ContinuousLinearMap.snd ℝ D B).comp T = 0 := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (C x) = ContinuousLinearMap.snd ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.snd ℝ D B).fderiv
    have hz : (mfderiv I 𝓘(ℝ, B) (Prod.snd ∘ C) x : G →L[ℝ] B) = 0 := by
      rw [hzero.mfderiv_eq, mfderiv_const]
      rfl
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)),
      hd] at hz
    exact hz
  intro u v huv
  apply hTi
  apply Prod.ext
  · exact
      (congrArg (fun L : G →L[ℝ] D => L u) hfst).symm.trans
        (huv.trans (congrArg (fun L : G →L[ℝ] D => L v) hfst))
  · have hz (w : G) : (T w).2 = 0 := congrArg (fun L : G →L[ℝ] B => L w) hsnd
    rw [hz u, hz v]

private theorem Smale.NativeSheetCoordinates.isLocalDiffeomorphOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ G] [I.Boundaryless] [IsManifold I ∞ N] (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    IsLocalDiffeomorphOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hU : IsOpen (F ⁻¹' Φ.target) := Φ.open_target.preimage hF.continuous
  intro x
  let A : G →L[ℝ] D := mfderiv I 𝓘(ℝ, D) (projection Φ F) x.1
  have hi : Function.Injective A := injective_mfderiv_projection Φ F hF hclean x.2 (hiF x.1)
  have hb : Function.Bijective A :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hA : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact Smale.isLocalDiffeomorphAt_boundaryless hU x.2 (contMDiffOn_projection Φ F hF) hA

private theorem Smale.NativeSheetCoordinates.exists_induced_sheet_chart {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [Nonempty N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hinjF : Function.Injective F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, D) I D N ∞,
      c.source = {u | (u, (0 : B)) ∈ Φ.source} ∧
        c.target = F ⁻¹' Φ.target ∧
          (∀ u ∈ c.source, F (c u) = Φ (u, 0)) ∧ ∀ x, c.symm x = projection Φ F x := by
  let U := F ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hF.continuous
  have hzero (x : N) (hx : x ∈ U) : (Φ.symm (F x)).2 = 0 :=
    (hclean _ (Φ.map_target' hx)).mp ⟨x, (Φ.right_inv' hx).symm⟩
  have hinj : Set.InjOn (projection Φ F) U := by
    intro x hx y hy heq
    have hc : Φ.symm (F x) = Φ.symm (F y) := Prod.ext heq ((hzero x hx).trans (hzero y hy).symm)
    apply hinjF
    exact (Φ.right_inv' hx).symm.trans ((congrArg Φ hc).trans (Φ.right_inv' hy))
  let p :=
    Smale.partialDiffeomorphOfInjectiveLocal hU hinj
      (isLocalDiffeomorphOn_projection Φ F hF hclean hdim hiF)
  have htarget : p.target = {u | (u, (0 : B)) ∈ Φ.source} := by
    change projection Φ F '' U = _
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have heq : (projection Φ F x, (0 : B)) = Φ.symm (F x) := Prod.ext rfl (hzero x hx).symm
      change (projection Φ F x, (0 : B)) ∈ Φ.source
      rw [heq]
      exact Φ.map_target' hx
    · intro hu
      obtain ⟨x, hx⟩ := (hclean (u, 0) hu).mpr rfl
      have hxU : x ∈ U := by
        change F x ∈ Φ.target
        rw [hx]
        exact Φ.map_source' hu
      refine ⟨x, hxU, ?_⟩
      change (Φ.symm (F x)).1 = u
      rw [hx]
      exact congrArg Prod.fst (Φ.left_inv' hu)
  refine ⟨p.symm, htarget, rfl, ?_, fun _ => rfl⟩
  intro u hu
  have hx : p.symm u ∈ U := p.map_target' hu
  have hp : projection Φ F (p.symm u) = u := p.right_inv' hu
  have heq : Φ.symm (F (p.symm u)) = (u, (0 : B)) := Prod.ext hp (hzero (p.symm u) hx)
  exact (Φ.right_inv' hx).symm.trans (congrArg Φ heq)

private def Smale.SphereNormalCoordinates.radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp C)

private theorem Smale.SphereNormalCoordinates.normalFrame_comp_normalDerivative {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (normalFrame x A).comp ((ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)) = radialFrame x C := by
  apply ContinuousLinearMap.ext
  intro z
  change
    z.1 • (x : V) + inclusionDerivative x (A.inverse (A (C z.2))) =
      z.1 • (x : V) + inclusionDerivative x (C z.2)
  rw [hA.inverse_apply_self]

private theorem
    Smale.SphereNormalCoordinates.bijective_radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) (hC : C.IsInvertible) :
    Function.Bijective (radialFrame x C) := by
  have heq : radialFrame x C = normalFrame x C.inverse := by
    apply ContinuousLinearMap.ext
    intro z
    change
      z.1 • (x : V) + inclusionDerivative x (C z.2) =
        z.1 • (x : V) + inclusionDerivative x (C.inverse.inverse z.2)
    rw [hC.inverse_inverse]
  rw [heq]
  exact bijective_normalFrame x C.inverse hC.inverse

private theorem Smale.SphereNormalCoordinates.normalJacobian_mul_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    normalJacobian j x A * (A.comp C).det =
      ((radialFrame x C).comp j.symm.toContinuousLinearMap).det := by
  let R : (ℝ × N) →L[ℝ] (ℝ × N) := (ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (R.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = (A.comp C).det := by
    have hconj : T.det = R.det := LinearMap.det_conj R.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (A.comp C).toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T =
      (radialFrame x C).comp j.symm.toContinuousLinearMap := by
    have h := normalFrame_comp_normalDerivative x A hA C
    ext v
    change normalFrame x A (j.symm (j (R (j.symm v)))) = radialFrame x C (j.symm v)
    rw [j.symm_apply_apply]
    exact congrArg (fun L : (ℝ × N) →L[ℝ] V => L (j.symm v)) h
  calc
    normalJacobian j x A * (A.comp C).det =
        (((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T).det := by
      rw [← hdetT]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := congrArg ContinuousLinearMap.det hfactor

private def Smale.SphereNormalCoordinates.chartRadialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) (z : N) :
    (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (c z : V)).coprod (fderiv ℝ (fun w => (c w : V)) z)

private theorem
    Smale.SphereNormalCoordinates.chartRadialFrame_eq {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) {z : N}
    (hz : z ∈ c.source) :
    chartRadialFrame c z =
      radialFrame (N := N) (c z) (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  by
  have hchain :
    fderiv ℝ (fun w => (c w : V)) z =
      (inclusionDerivative (c z)).comp
        (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    have h :=
      mfderiv_comp z ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  unfold chartRadialFrame radialFrame
  rw [hchain]
  rfl

private theorem Smale.SphereNormalCoordinates.contDiffOn_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) :
    ContDiffOn ℝ ∞ (chartRadialFrame c) c.source := by
  have hc : ContDiffOn ℝ ∞ (fun w => (c w : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact
    Smale.FrameField.contDiffOn_coprod (contDiffOn_const.smulRight hc)
      (hc.fderiv_of_isOpen c.open_source (m := ∞) (by simp))

private theorem Smale.SphereNormalCoordinates.bijective_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    {z : N} (hz : z ∈ c.source) : Function.Bijective (chartRadialFrame c z) := by
  rw [chartRadialFrame_eq c hz]
  let C : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c z
  have hC : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (Smale.PartialChart.bijective_mfderiv c hz)).toContinuousLinearEquiv,
      rfl⟩
  exact bijective_radialFrame (c z) C hC

private theorem Smale.SphereNormalCoordinates.chartRadialFrame_det_mul_endpoints_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source) :
    0 <
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det *
        ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
  have hF := (contDiffOn_chartRadialFrame c).continuousOn.comp ha haS
  exact
    Smale.FrameField.det_mul_endpoints_pos (hF.clm_comp continuousOn_const)
      (fun t ht => (bijective_chartRadialFrame c (haS ht)).comp j.symm.bijective)

private theorem Smale.SphereNormalCoordinates.opposite_normalJacobians_iff_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B < 0 ↔
      (A.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det *
          (B.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det <
        0 := by
  let C₀ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0)
  let C₁ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1)
  have h₀ :
    normalJacobian j (c (a 0)) A * (A.comp C₀).det =
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 0)) A hA C₀
  have h₁ :
    normalJacobian j (c (a 1)) B * (B.comp C₁).det =
      ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 1)) B hB C₁
  have hp :
    0 <
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
        ((A.comp C₀).det * (B.comp C₁).det) := by
    have heq :
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
          ((A.comp C₀).det * (B.comp C₁).det) =
        (normalJacobian j (c (a 0)) A * (A.comp C₀).det) *
          (normalJacobian j (c (a 1)) B * (B.comp C₁).det) := by ring
    rw [heq, h₀, h₁]
    exact chartRadialFrame_det_mul_endpoints_pos c j a ha haS
  change _ ↔ (A.comp C₀).det * (B.comp C₁).det < 0
  rcases mul_pos_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact iff_of_false (not_lt_of_gt hp) (not_lt_of_gt hq)
  · exact iff_of_true hp hq

private theorem Smale.SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet
    {V A B E M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) 𝓘(ℝ, E) ((ℝ × A) × B) M ∞)
    (F : Metric.sphere (0 : V) 1 → M) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ F)
    (hinjF : Function.Injective F) (hiF : ∀ x, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) F x))
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hline : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t, (0 : A)), (0 : B)) ∈ Φ.source)
    (hdim : Module.finrank ℝ (ℝ × A) = n) (q : M → (ℝ × A)) (r : (ℝ × (ℝ × A)) ≃L[ℝ] V)
    (x₀ x₁ : Metric.sphere (0 : V) 1) (hx₀ : F x₀ = Φ ((0, 0), 0)) (hx₁ : F x₁ = Φ ((1, 0), 0))
    (hq₀ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₀))
    (hq₁ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₁))
    (hi₀ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀).IsInvertible)
    (hi₁ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁).IsInvertible) :
    normalJacobian r x₀ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀) *
          normalJacobian r x₁ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁) <
        0 ↔
      (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0)).det <
        0 := by
  let _ : Nonempty (Metric.sphere (0 : V) 1) := ⟨x₀⟩
  obtain ⟨c, hcS, _, hFc, _⟩ :=
    Smale.NativeSheetCoordinates.exists_induced_sheet_chart Φ F hF hinjF hclean
      (by simpa only [finrank_euclideanSpace_fin] using hdim.symm) hiF
  let a : ℝ → (ℝ × A) := fun t => (t, 0)
  have ha : ContinuousOn a (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source := by
    intro t ht
    rw [hcS]
    exact hline t ht
  have h₀ : c (a 0) = x₀ := hinjF ((hFc _ (haS (by simp))).trans hx₀.symm)
  have h₁ : c (a 1) = x₁ := hinjF ((hFc _ (haS (by simp))).trans hx₁.symm)
  let A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀
  let A₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁
  have hsign := opposite_normalJacobians_iff_chartDet c r a ha haS A₀ A₁ hi₀ hi₁
  have hcoeff (t : ℝ) (x : Metric.sphere (0 : V) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : c (a t) = x) (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x)) :
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)).comp
        (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (t, 0) := by
    have hqF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ × A) ∞ (q ∘ F) (c (a t)) := by
      rw [hx]
      exact hq.comp x hF.contMDiffAt
    have hchain :=
      mfderiv_comp (a t) (hqF.mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) (haS ht))
    have heq : ((q ∘ F) ∘ c) =ᶠ[𝓝 (a t)] (fun w => q (Φ (w, 0))) := by
      filter_upwards [c.open_source.mem_nhds (haS ht)] with w hw
      exact congrArg q (hFc w hw)
    have hpoint :
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) (c (a t)) : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)) =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x := by rw [hx]
    rw [mfderiv_eq_fderiv] at hchain
    have h := hchain.symm.trans heq.fderiv_eq
    exact
      (congrArg
            (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) =>
              L.comp (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)))
            hpoint).symm.trans
        h
  rw [h₀, h₁] at hsign
  let C₀ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 0)
  let C₁ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 1)
  have hc₀ : A₀.comp C₀ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0) :=
    hcoeff 0 x₀ (by simp) h₀ hq₀
  have hc₁ : A₁.comp C₁ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0) :=
    hcoeff 1 x₁ (by simp) h₁ hq₁
  change
    normalJacobian r x₀ A₀ * normalJacobian r x₁ A₁ < 0 ↔
      (A₀.comp C₀).det * (A₁.comp C₁).det < 0 at hsign
  rw [hc₀, hc₁] at hsign
  exact hsign

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : Smale.Hemisphere.Sphere 2 → D.UpperLevel) {a b : ℝ → D.UpperLevel}
    {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (tube :
        Smale.TubularBigon (E := Smale.RegularLevel.Model E) (Set.range g)
          (Set.range D.surgery.beltSphere) a b k l h 3)
      (d :
        Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          Smale.RegularLevel.Model E) (Set.range g) k)
      (e :
        Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          Smale.RegularLevel.Model E) (Set.range D.surgery.beltSphere) l)
      (x₀ x₁ : Smale.Hemisphere.Sphere 2),
      g x₀ = d.chart (Smale.StripCoordinates.center 0) →
        g x₁ = d.chart (Smale.StripCoordinates.center 1) →
          ((D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1) ↔
            tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht tube d e x₀ x₁ hx₀ hx₁
  let j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hindex])
  let q := D.beltSheetNormal j
  let r' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r
  have hjSmooth :
    ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
    j.symm.contDiff.contMDiff
  have hdata (x : Smale.Hemisphere.Sphere 2) (hx : g x ∈ Set.range D.surgery.beltSphere) :
    ContMDiffAt 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) ∧
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x).IsInvertible ∧
        Smale.SphereNormalCoordinates.normalJacobian r' x
            (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x) =
          D.beltIntersectionJacobian 2 r g x := by
    obtain ⟨v, hv⟩ := hx
    have hxO : g x ∈ D.beltNormalDomain := hv ▸ D.belt_mem_normalDomain v
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt (D.isOpen_beltNormalDomain.mem_nhds hxO)
    have hq :
      ContMDiffAt 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) :=
      hjSmooth.contMDiffAt.comp _ hnormal
    let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates :=
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x
    let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x
    have hAb : Function.Bijective A :=
      D.bijective_beltNormal_comp_of_transverse hf 3 2 hindex g hg x v hv (ht x v hv)
    have hA : A.IsInvertible :=
      ⟨(LinearEquiv.ofBijective A.toLinearMap hAb).toContinuousLinearEquiv, rfl⟩
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (g x)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hBA : B = j.symm.toContinuousLinearMap.comp A := by
      change mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (j.symm ∘ (D.beltNormal ∘ g)) x = _
      rw [mfderiv_comp x (hjSmooth.mdifferentiableAt (by simp))
          ((hnormal.comp x hg.contMDiffAt).mdifferentiableAt (by simp))]
      change
        (mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
                  (D.beltNormal (g x)) :
                D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1))).comp
            A =
          _
      exact
        congrArg
          (fun L : D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) => L.comp A)
          hJ
    refine ⟨hq, ?_, ?_⟩
    · change B.IsInvertible
      rw [hBA]
      exact (show j.symm.toContinuousLinearMap.IsInvertible from ⟨j.symm, rfl⟩).comp hA
    · change
        Smale.SphereNormalCoordinates.normalJacobian r' x B =
          Smale.SphereNormalCoordinates.normalJacobian r x A
      rw [hBA]
      exact Smale.SphereNormalCoordinates.normalJacobian_change_normal_model r j x A hA
  have hcross (t : ℝ) (ht' : t = 0 ∨ t = 1) (x : Smale.Hemisphere.Sphere 2)
    (hx : g x = d.chart (Smale.StripCoordinates.center t)) :
    g x ∈ Set.range D.surgery.beltSphere := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht' with rfl | rfl <;> simp
    rw [hx, tube.rankThree_corner_sheet_charts_coincide d e ht']
    exact (e.sheet _ (e.line htI)).mpr rfl
  obtain ⟨hq₀, hi₀, hJ₀⟩ := hdata x₀ (hcross 0 (Or.inl rfl) x₀ hx₀)
  obtain ⟨hq₁, hi₁, hJ₁⟩ := hdata x₁ (hcross 1 (Or.inr rfl) x₁ hx₁)
  have hsign :=
    Smale.SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet d.chart g hg hinj hi
      d.sheet d.line (by simp [Module.finrank_prod]) q r' x₀ x₁ hx₀ hx₁ hq₀ hq₁ hi₀ hi₁
  rw [hJ₀, hJ₁] at hsign
  exact
    (D.beltIntersectionSigns_opposite_iff 2 r g x₀ x₁).trans
      (hsign.trans (D.opposite_belt_corners_iff_normal_sheet_determinants hf j tube d e).symm)

private def Smale.WhitneyPairModel.innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

private theorem
    Smale.WhitneyPairModel.innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

private theorem Smale.WhitneyPairModel.contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

private def Smale.WhitneyPairModel.innerBigonDiffeomorph (h r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞
    where
  toEquiv :=
    { toFun := innerBigonMap h r
      invFun := fun p => r⁻¹ • (p - (1 - r) • (0, h / 2))
      left_inv := by
        intro p
        simp only [innerBigonMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      right_inv := by
        intro p
        simp only [innerBigonMap, smul_smul, mul_inv_cancel₀ hr, one_smul]
        abel }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r)
    apply ContDiff.contMDiff
    unfold innerBigonMap
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun p : ℝ × ℝ => r⁻¹ • (p - (1 - r) • (0, h / 2)))
    apply ContDiff.contMDiff
    fun_prop

private theorem Smale.WhitneyPairModel.bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0)
    (p : ℝ × ℝ) : Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) :=
  Smale.PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (Set.mem_univ p)

private theorem Smale.WhitneyPairModel.innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh) hp
    (sub_pos.mpr hr.2) hr.1.le (by ring)

private def Smale.WhitneyPairModel.innerBigonCollar (h r : ℝ) : Set (ℝ × ℝ) :=
  bigon h \ innerBigonMap h r '' interior (bigon h)

private def Smale.WhitneyPairModel.inverseInnerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  r⁻¹ • (p - (1 - r) • (0, h / 2))

private theorem Smale.WhitneyPairModel.inverseInnerBigonMap_one (h : ℝ) (p : ℝ × ℝ) :
    inverseInnerBigonMap h 1 p = p := by
  simp only [inverseInnerBigonMap, inv_one, sub_self, zero_smul, sub_zero, one_smul]

private theorem
    Smale.WhitneyPairModel.inner_inverseInnerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    innerBigonMap h r (inverseInnerBigonMap h r p) = p :=
  (innerBigonDiffeomorph h r hr).apply_symm_apply p

private theorem Smale.WhitneyPairModel.continuousAt_inverseInnerBigonMap (h : ℝ) (p : ℝ × ℝ) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => inverseInnerBigonMap h z.1 z.2) (1, p) := by
  unfold inverseInnerBigonMap
  fun_prop (disch := norm_num)

private theorem
    Smale.WhitneyPairModel.isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) :
    IsCompact (innerBigonCollar h r) := by
  have ho : IsOpen (innerBigonMap h r '' interior (bigon h)) :=
    (innerBigonDiffeomorph h r hr).toHomeomorph.isOpenMap _ isOpen_interior
  exact (isCompact_bigon hh).inter_right ho.isClosed_compl

private theorem Smale.WhitneyPairModel.innerBigonMap_mem_collar_iff {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ innerBigonCollar h r ↔ p ∈ frontier (bigon h) := by
  rw [frontier, (isClosed_bigon h).closure_eq]
  constructor
  · intro hx
    exact ⟨hp, fun hi => hx.2 (Set.mem_image_of_mem _ hi)⟩
  · intro hx
    refine ⟨interior_subset (innerBigonMap_mem_interior hh hr hp), ?_⟩
    rintro ⟨q, hq, heq⟩
    have hqp : q = p := (innerBigonDiffeomorph h r hr.1.ne').injective heq
    exact hx.2 (hqp ▸ hq)

private theorem Smale.WhitneyPairModel.exists_inner_bigon_collar_in_open {h : ℝ} (hh : 0 < h)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hfrontU : frontier (bigon h) ⊆ U) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        innerBigonCollar h r ⊆ U ∧
          Set.MapsTo (innerBigonMap h r) (frontier (bigon h)) (U ∩ interior (bigon h)) := by
  let bad : Set (ℝ × ℝ) := bigon h \ U
  have hbad : IsCompact bad := (isCompact_bigon hh).inter_right hU.isClosed_compl
  have hbadInterior : bad ⊆ interior (bigon h) := by
    intro p hp
    by_contra hi
    apply hp.2
    apply hfrontU
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hi⟩
  have hnearInv : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bad, inverseInnerBigonMap h r p ∈ interior (bigon h) :=
    by
    apply hbad.eventually_forall_of_forall_eventually
    intro p hp
    apply (continuousAt_inverseInnerBigonMap h p).preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    simpa only [inverseInnerBigonMap_one] using hbadInterior hp
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  have hnearFront : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ frontier (bigon h), innerBigonMap h r p ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((contDiff_innerBigonMap h).continuous.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [innerBigonMap_one] using hfrontU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hnearInv.and hnearFront)
  let δ : ℝ := Min.min ε 1 / 2
  have hδpos : 0 < δ := half_pos (lt_min hε zero_lt_one)
  have hδε : δ < ε := by
    dsimp [δ]
    have hm := min_le_left ε 1
    linarith
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hm := min_le_right ε 1
    linarith
  have hr : 1 - δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrball : 1 - δ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : 1 - δ - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδpos]
    exact hδε
  have hretained := hball hrball
  refine ⟨1 - δ, hr, ?_, fun p hp => ⟨hretained.2 p hp, ?_⟩⟩
  · intro p hp
    by_contra hpU
    exact
      hp.2
        ⟨inverseInnerBigonMap h (1 - δ) p, hretained.1 p ⟨hp.1, hpU⟩,
          inner_inverseInnerBigonMap h (1 - δ) hr.1.ne' p⟩
  · exact innerBigonMap_mem_interior hh hr ((mem_frontier_bigon_iff h p).mp hp).1

private theorem Smale.CleanBigonBoundary.exists_inner_clean_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) S T a b k l h) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        Smale.WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ V : Set (ℝ × ℝ),
            IsOpen V ∧
              frontier (Smale.WhitneyPairModel.bigon h) ⊆ V ∧
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
                    (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) V ∧
                  Set.InjOn (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) V ∧
                    (∀ p ∈ V,
                        Function.Injective
                          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E)
                            (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) p)) ∧
                      Set.MapsTo (Smale.WhitneyPairModel.innerBigonMap h r) V
                          (d.domain ∩ interior (Smale.WhitneyPairModel.bigon h)) ∧
                        ∀ p ∈ V, d.map (Smale.WhitneyPairModel.innerBigonMap h r p) ∉ S ∪ T := by
  have hfrontD : frontier (Smale.WhitneyPairModel.bigon h) ⊆ d.domain :=
    d.boundary_covered.trans (interior_subset.trans d.neighborhood_subset)
  obtain ⟨r, hr, hcollar, hfront⟩ :=
    Smale.WhitneyPairModel.exists_inner_bigon_collar_in_open d.height_pos d.open_domain hfrontD
  let c := Smale.WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let V : Set (ℝ × ℝ) :=
    Smale.WhitneyPairModel.innerBigonMap h r ⁻¹'
      (d.domain ∩ interior (Smale.WhitneyPairModel.bigon h))
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (Smale.WhitneyPairModel.innerBigonMap h r) :=
    c.contMDiff
  have hV : IsOpen V := (d.open_domain.inter isOpen_interior).preimage hc.continuous
  have hsmooth :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) V :=
    d.smooth.comp hc.contMDiffOn (fun _ hp => hp.1)
  have hinj : Set.InjOn (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) V := by
    intro p hp q hq hpq
    exact c.injective (d.injective hp.1 hq.1 hpq)
  refine ⟨r, hr, hcollar, V, hV, hfront, hsmooth, hinj, ?_, fun _ hp => hp, ?_⟩
  · intro p hp
    have hdf := (d.smooth.contMDiffAt (d.open_domain.mem_nhds hp.1)).mdifferentiableAt (by simp)
    rw [mfderiv_comp p hdf (hc.mdifferentiableAt (by simp))]
    exact
      (d.derivative_injective _ hp.1).comp
        (Smale.WhitneyPairModel.bijective_mfderiv_innerBigonMap h r hr.1.ne' p).injective
  · intro p hp
    exact d.interior_avoids _ hp

private theorem Smale.CleanBigonBoundary.exists_smooth_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) S T a b k l h) (U : TopologicalSpace.Opens M)
    (hU : (S ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        Smale.WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              ∃ W : Set (ℝ × ℝ),
                IsOpen W ∧
                  frontier (Smale.WhitneyPairModel.bigon h) ⊆ W ∧
                    Set.EqOn (Subtype.val ∘ F) (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r)
                        W ∧
                      Set.InjOn F W ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                          ∀ p ∈ W, (F p : M) ∉ S ∪ T := by
  classical
  obtain ⟨r, hr, hcollar, V, hV, hfrontV, hsmooth, hinj, hderiv, -, havoid⟩ :=
    d.exists_inner_clean_neighborhood
  have hzero : (0 : ℝ × ℝ) ∈ frontier (Smale.WhitneyPairModel.bigon h) := by
    rw [Smale.WhitneyPairModel.mem_frontier_bigon_iff]
    refine ⟨?_, Or.inl rfl⟩
    change 0 ≤ (0 : ℝ) ∧ h * 0 ^ 2 + 0 ≤ h
    simpa only [zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero, add_zero] using
      And.intro le_rfl d.height_pos.le
  let c : U := ⟨d.map (Smale.WhitneyPairModel.innerBigonMap h r 0), hU (havoid 0 (hfrontV hzero))⟩
  let f : (ℝ × ℝ) → U := fun p =>
    if hp : p ∈ V then ⟨d.map (Smale.WhitneyPairModel.innerBigonMap h r p), hU (havoid p hp)⟩
    else c
  have hval (p : ℝ × ℝ) (hp : p ∈ V) :
    (f p : M) = d.map (Smale.WhitneyPairModel.innerBigonMap h r p) := by
    dsimp [f]
    rw [dite_eq_left hp]
  have hfval : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ f) V :=
    hsmooth.congr (fun p hp => hval p hp)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f V := by
    intro p hp
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U f V p).mp (hfval p hp)
  obtain ⟨F, hF, W, hW, hfrontW, hWV, hEq⟩ :=
    Smale.exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies hnull d.height_pos
      hV hf hfrontV
  have hEqval : Set.EqOn (Subtype.val ∘ F) (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) W :=
    by
    intro p hp
    exact (congrArg Subtype.val (hEq hp)).trans (hval p (hWV hp))
  have hinjF : Set.InjOn F W := by
    intro p hp q hq hpq
    apply hinj (hWV hp) (hWV hq)
    exact (hEqval hp).symm.trans ((congrArg Subtype.val hpq).trans (hEqval hq))
  refine ⟨r, hr, hcollar, F, hF, W, hW, hfrontW, hEqval, hinjF, ?_, ?_⟩
  · intro p hp
    have heq : (Subtype.val ∘ F) =ᶠ[𝓝 p] (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) :=
      Filter.mem_of_superset (hW.mem_nhds hp) (fun _ hq => hEqval hq)
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p) := by
      rw [heq.mfderiv_eq]
      exact hderiv p (hWV hp)
    have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))] at hi
    intro v w hvw
    apply hi
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) (F p)) hvw
  · intro p hp
    change (Subtype.val ∘ F) p ∉ S ∪ T
    rw [hEqval hp]
    exact havoid p (hWV hp)

private theorem Smale.CleanBigonBoundary.exists_embedded_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {D Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        Smale.WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : Smale.WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ Smale.WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ Smale.WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    ∃ W : Set (ℝ × ℝ),
                      IsOpen W ∧
                        frontier (Smale.WhitneyPairModel.bigon h) ⊆ W ∧
                          Set.EqOn (Subtype.val ∘ F)
                            (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, V, hV, hfrontV, hEq, hinj, hderiv, havoid⟩ :=
    d.exists_smooth_inner_extension_in_open U hU hnull
  have hcompact : IsCompact (frontier (Smale.WhitneyPairModel.bigon h)) :=
    (Smale.WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hcompact hV hfrontV
  have hinjC : Set.InjOn F (Smale.WhitneyPairModel.bigon h ∩ C) :=
    hinj.mono (Set.inter_subset_right.trans hCV)
  have hiC :
    ∀ p ∈ Smale.WhitneyPairModel.bigon h ∩ C,
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p) :=
    fun p hp => hderiv p (hCV hp.2)
  have hclean :
    ∀ p ∈ Smale.WhitneyPairModel.bigon h ∩ C, p ∉ (∅ : Set (ℝ × ℝ)) → (F p : M) ∉ Set.range g := by
    intro p hp _ hmem
    exact havoid p (hCV hp.2) (Or.inl hmem)
  obtain ⟨G, hG, hhom, hemb, hiG, havoidG⟩ :=
    Smale.ManifoldImmersion.exists_relative_embedded_avoidance_in_open U F g hF hg
      (by simp [Module.finrank_prod]) hdim (by simpa [Module.finrank_prod] using hobstacle)
      (Smale.WhitneyPairModel.isCompact_bigon d.height_pos) hC (Set.empty_subset _) hinjC hiC
      hclean
  refine ⟨r, hr, hcollar, G, hG, hemb, hiG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp
    exact havoidG p ⟨hp, Set.notMem_empty p⟩
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC))

private theorem
    Smale.CleanBigonBoundary.exists_collar_disjoint_inner_extension_in_open {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        Smale.WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : Smale.WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ Smale.WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ Smale.WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    (∀ p ∈ interior (Smale.WhitneyPairModel.bigon h),
                        (F p : M) ∉ d.map '' Smale.WhitneyPairModel.innerBigonCollar h r) ∧
                      ∃ W : Set (ℝ × ℝ),
                        IsOpen W ∧
                          frontier (Smale.WhitneyPairModel.bigon h) ⊆ W ∧
                            Set.EqOn (Subtype.val ∘ F)
                              (d.map ∘ Smale.WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_embedded_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let Q : TopologicalSpace.Opens (ℝ × ℝ) := ⟨d.domain, d.open_domain⟩
  let q : C(Q, M) :=
    ⟨fun p => d.map p, continuousOn_iff_continuous_domRestrict.mp d.smooth.continuousOn⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ q := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact d.smooth.contMDiffAt (d.open_domain.mem_nhds p.property)
  let A : Set Q := Subtype.val ⁻¹' Smale.WhitneyPairModel.innerBigonCollar h r
  have himage : q '' A = d.map '' Smale.WhitneyPairModel.innerBigonCollar h r := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hcollar hp⟩, hp, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact
      ((Smale.WhitneyPairModel.isCompact_innerBigonCollar d.height_pos
              hr.1.ne').image_of_continuousOn
          (d.smooth.continuousOn.mono hcollar)).isClosed
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (Smale.WhitneyPairModel.innerBigonMap h r) :=
    (Smale.WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne').contMDiff
  let V' : Set (ℝ × ℝ) := V ∩ Smale.WhitneyPairModel.innerBigonMap h r ⁻¹' d.domain
  have hV' : IsOpen V' := hV.inter (d.open_domain.preimage hs.continuous)
  have hfrontV' : frontier (Smale.WhitneyPairModel.bigon h) ⊆ V' := by
    intro p hp
    refine ⟨hfrontV hp, hcollar ?_⟩
    exact
      (Smale.WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr
            ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1).mpr
        hp
  have hfrontCompact : IsCompact (frontier (Smale.WhitneyPairModel.bigon h)) :=
    (Smale.WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((Smale.WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV' hfrontV'
  have hinj : Set.InjOn F (Smale.WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  have hclean :
    ∀ p ∈ Smale.WhitneyPairModel.bigon h ∩ C,
      p ∉ frontier (Smale.WhitneyPairModel.bigon h) → (F p : M) ∉ q '' A := by
    intro p hp hpB hmem
    rw [himage] at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have hzp : z = Smale.WhitneyPairModel.innerBigonMap h r p :=
      d.injective (hcollar hz) (hCV hp.2).2 (heq.trans (hEq (hCV hp.2).1))
    exact
      hpB
        ((Smale.WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp.1).mp (hzp ▸ hz))
  let O : Set U := (Subtype.val : U → M) ⁻¹' (Set.range g)ᶜ
  have hO : IsOpen O :=
    (isCompact_range g.continuous).isClosed.isOpen_compl.preimage continuous_subtype_val
  have hmaps : Set.MapsTo F (Smale.WhitneyPairModel.bigon h) O := fun p hp => havoid p hp
  have hdim' : 2 * Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hobstacle' : Module.finrank ℝ (ℝ × ℝ) + Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨G, hG, hhom, hembG, hiG, hmapsG, havoidG⟩ :=
    Smale.ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open U F q A
      hF hq hclosed hdim' hobstacle' (Smale.WhitneyPairModel.isCompact_bigon d.height_pos) hC
      hfrontC hinj hi hclean hO hmaps
  refine ⟨r, hr, hcollar, G, hG, hembG, hiG, hmapsG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp hmem
    have hpB : p ∉ frontier (Smale.WhitneyPairModel.bigon h) := by
      intro hfront
      rw [frontier] at hfront
      exact hfront.2 hp
    exact havoidG p ⟨interior_subset hp, hpB⟩ (by rwa [himage])
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC).1)

private theorem Smale.exists_filled_clean_bigon_of_collar_disjoint_inner {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hcollar : WhitneyPairModel.innerBigonCollar h r ⊆ d.domain) (F : C(ℝ × ℝ, M))
    (hF : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F) (hinjF : Set.InjOn F (WhitneyPairModel.bigon h))
    (hiF : ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p))
    (havoidF : ∀ p ∈ WhitneyPairModel.bigon h, F p ∉ S ∪ T)
    (hcollarF :
      ∀ p ∈ interior (WhitneyPairModel.bigon h),
        F p ∉ d.map '' WhitneyPairModel.innerBigonCollar h r)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W)
    (hEq : Set.EqOn F (d.map ∘ WhitneyPairModel.innerBigonMap h r) W) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let c := WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let core : Set (ℝ × ℝ) := c '' WhitneyPairModel.bigon h
  let P : Set (ℝ × ℝ) := c '' (interior (WhitneyPairModel.bigon h) ∪ W)
  let Q : Set (ℝ × ℝ) := d.domain \ c '' (WhitneyPairModel.bigon h \ W)
  let G : (ℝ × ℝ) → M := F ∘ c.symm
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G := hF.comp c.symm.contMDiff
  have hP : IsOpen P := c.toHomeomorph.isOpenMap _ (isOpen_interior.union hW)
  have hQ : IsOpen Q :=
    d.open_domain.inter
      (((WhitneyPairModel.isCompact_bigon d.height_pos).inter_right hW.isClosed_compl).image
          c.continuous).isClosed.isOpen_compl
  have hfront (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h)
    (hi : p ∉ interior (WhitneyPairModel.bigon h)) : p ∈ frontier (WhitneyPairModel.bigon h) := by
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp, hi⟩
  have hcoreP : core ⊆ P := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact Or.inl hi
    · exact Or.inr (hfrontW (hfront p hp hi))
  have hcollarQ : WhitneyPairModel.innerBigonCollar h r ⊆ Q := by
    intro p hp
    refine ⟨hcollar hp, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact
      hz.2 (hfrontW ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hz.1).mp hp))
  have hnotCore (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (hn : p ∉ core) :
    p ∈ WhitneyPairModel.innerBigonCollar h r :=
    ⟨hp, fun hi => hn (Set.image_mono interior_subset hi)⟩
  have hcover : WhitneyPairModel.bigon h ⊆ P ∪ Q := by
    intro p hp
    by_cases hc : p ∈ core
    · exact Or.inl (hcoreP hc)
    · exact Or.inr (hcollarQ (hnotCore p hp hc))
  have hfrontQ : frontier (WhitneyPairModel.bigon h) ⊆ Q := by
    intro p hp
    apply hcollarQ
    refine ⟨((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hi : p ∈ interior (WhitneyPairModel.bigon h) :=
      heq ▸ WhitneyPairModel.innerBigonMap_mem_interior d.height_pos hr (interior_subset hz)
    rw [frontier] at hp
    exact hp.2 hi
  have hmatch : Set.EqOn G d.map (P ∩ Q) := by
    rintro p ⟨hp, hq⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hzW : z ∈ W := by
      rcases hz with hz | hz
      · by_contra hn
        exact hq.2 ⟨z, ⟨interior_subset hz, hn⟩, rfl⟩
      · exact hz
    change F (c.symm (c z)) = d.map (c z)
    rw [c.symm_apply_apply]
    exact hEq hzW
  obtain ⟨j, hj, hjG, hjd⟩ :=
    exists_smooth_open_gluing hP hQ hG.contMDiffOn (d.smooth.mono Set.inter_subset_left) hmatch
  have hjInner (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) : j (c p) = F p :=
    (hjG (hcoreP ⟨p, hp, rfl⟩)).trans (congrArg F (c.symm_apply_apply p))
  have hjCollar (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.innerBigonCollar h r) : j p = d.map p :=
    hjd (hcollarQ hp)
  have hcross (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (z : ℝ × ℝ)
    (hz : z ∈ WhitneyPairModel.innerBigonCollar h r) (heq : F p = d.map z) : c p = z := by
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact False.elim (hcollarF p hi ⟨z, hz, heq.symm⟩)
    · have hpf := hfront p hp hi
      apply
        d.injective
          (hcollar ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp).mpr hpf))
          (hcollar hz)
      exact (hEq (hfrontW hpf)).symm.trans heq
  have hinj : Set.InjOn j (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    by_cases hpCore : p ∈ core
    · obtain ⟨p', hp', rfl⟩ := hpCore
      rw [hjInner p' hp'] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact congrArg c (hinjF hp' hz' heq)
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact hcross p' hp' z hzC heq
    · have hpC := hnotCore p hp hpCore
      rw [hjCollar p hpC] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact (hcross z' hz' p hpC heq.symm).symm
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact d.injective (hcollar hpC) (hcollar hzC) heq
  have hi :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) j p) := by
    intro p hp
    by_cases hpCore : p ∈ core
    · have heq : j =ᶠ[𝓝 p] G :=
        Filter.mem_of_superset (hP.mem_nhds (hcoreP hpCore)) (fun _ hx => hjG hx)
      rw [heq.mfderiv_eq]
      change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (F ∘ c.symm) p)
      rw [mfderiv_comp p (hF.mdifferentiableAt (by simp))
          (c.symm.contMDiff.mdifferentiableAt (by simp))]
      have hpin : c.symm p ∈ WhitneyPairModel.bigon h := by
        obtain ⟨z, hz, rfl⟩ := hpCore
        rwa [c.symm_apply_apply]
      exact
        (hiF _ hpin).comp
          (PartialChart.bijective_mfderiv c.symm.toPartialDiffeomorph (Set.mem_univ p)).injective
    · have hpC := hnotCore p hp hpCore
      have heq : j =ᶠ[𝓝 p] d.map :=
        Filter.mem_of_superset (hQ.mem_nhds (hcollarQ hpC)) (fun _ hx => hjd hx)
      rw [heq.mfderiv_eq]
      exact d.derivative_injective p (hcollar hpC)
  have havoid : ∀ p ∈ interior (WhitneyPairModel.bigon h), j p ∉ S ∪ T := by
    intro p hp
    by_cases hpCore : p ∈ core
    · obtain ⟨z, hz, rfl⟩ := hpCore
      rw [hjInner z hz]
      exact havoidF z hz
    · have hpC := hnotCore p (interior_subset hp) hpCore
      rw [hjCollar p hpC]
      exact d.interior_avoids p ⟨hcollar hpC, hp⟩
  obtain ⟨f, hf, V, hV, hKV, -, hfj⟩ :=
    exists_smooth_extension_near_starConvex (WhitneyPairModel.isCompact_bigon d.height_pos)
      (WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (WhitneyPairModel.starConvex_bigon d.height_pos.le) (hP.union hQ) hcover hj
  have hinjf : Set.InjOn f (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    apply hinj hp hz
    exact (hfj (hKV hp)).symm.trans (heq.trans (hfj (hKV hz)))
  have hembf : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) := by
    let : CompactSpace (WhitneyPairModel.bigon h) :=
      isCompact_iff_compactSpace.mp (WhitneyPairModel.isCompact_bigon d.height_pos)
    apply (hf.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p z heq
    exact Subtype.ext (hinjf p.property z.property heq)
  refine ⟨⟨f, hf.continuous⟩, hf, hembf, ?_, ?_, V ∩ Q, hV.inter hQ, ?_, ?_⟩
  · intro p hp
    have heq : f =ᶠ[𝓝 p] j := Filter.mem_of_superset (hV.mem_nhds (hKV hp)) (fun _ hx => hfj hx)
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)
    rw [heq.mfderiv_eq]
    exact hi p hp
  · intro p hp
    change f p ∉ S ∪ T
    rw [hfj (hKV (interior_subset hp))]
    exact havoid p hp
  · intro p hp
    exact ⟨hKV ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, hfrontQ hp⟩
  · intro p hp
    exact (hfj hp.1).trans (hjd hp.2)

private theorem
    Smale.CleanBigonBoundary.exists_filled_bigon_of_complement_contractions {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Smale.Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : Smale.WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ Smale.WhitneyPairModel.bigon h,
              Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (Smale.WhitneyPairModel.bigon h), f p ∉ Set.range g ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (Smale.WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let U : TopologicalSpace.Opens M := ⟨Tᶜ, hT.isOpen_compl⟩
  have hU : (Set.range g ∪ T)ᶜ ⊆ U := fun _ hp ht => hp (Or.inr ht)
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, havoidCollar, W, hW, hfrontW, hEq⟩ :=
    d.exists_collar_disjoint_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let F' : C(ℝ × ℝ, M) := ⟨Subtype.val ∘ F, continuous_subtype_val.comp F.continuous⟩
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hF' : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F' := hv.comp hF
  have hinjF' : Set.InjOn F' (Smale.WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    have hFval : F p = F z := Subtype.ext heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) hFval)
  have hiF' :
    ∀ p ∈ Smale.WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F' p) :=
    by
    intro p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p)
    rw [mfderiv_comp p (hv.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (Smale.NativeOpenSubmanifold.injective_mfderiv_subtype_val U (F p)).comp (hi p hp)
  have havoidF' : ∀ p ∈ Smale.WhitneyPairModel.bigon h, F' p ∉ Set.range g ∪ T := by
    intro p hp hmem
    rcases hmem with hmem | hmem
    · exact havoid p hp hmem
    · exact (F p).property hmem
  exact
    Smale.exists_filled_clean_bigon_of_collar_disjoint_inner d hr hcollar F' hF' hinjF' hiF'
      havoidF' havoidCollar hW hfrontW hEq

private theorem Smale.CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions
    {E M D Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : Smale.CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Smale.Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E)
    (n : ℕ) (hcodim : 2 + n = Module.finrank ℝ E) :
    Nonempty (Smale.TubularBigon (E := E) (Set.range g) T a b k l h n) := by
  obtain ⟨f, hf, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_filled_bigon_of_complement_contractions g hg hT hnull hdim hobstacle
  have hinj : Set.InjOn f (Smale.WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  obtain ⟨ε, hε, Φ, hsource, hzero, -⟩ :=
    Smale.exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      (Smale.WhitneyPairModel.isCompact_bigon d.height_pos)
      (Smale.WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (Smale.WhitneyPairModel.starConvex_bigon d.height_pos.le) hinj hi n
      (by simpa only [Module.finrank_prod, Module.finrank_self] using hcodim) isOpen_univ
      (Set.mapsTo_univ _ _)
  have hgerm : ∀ p ∈ frontier (Smale.WhitneyPairModel.bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map :=
    fun _ hp => Filter.mem_of_superset (hV.mem_nhds (hfrontV hp)) (fun _ hx => hEq hx)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
    fun t ht =>
    (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (Smale.WhitneyPairModel.bigon h) :=
    fun t ht =>
    (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact
    ⟨{  height_pos := d.height_pos
        map := f
        smooth := hf
        closed_embedding := hemb
        derivative_injective := hi
        interior_avoids := havoid
        lower := fun t ht => (hEq (hfrontV (hlow t ht))).trans (d.lower t ht)
        upper := fun t ht => (hEq (hfrontV (hupp t ht))).trans (d.upper t ht)
        lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
        upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := hzero }⟩

private theorem Smale.ManifoldImmersion.exists_weighted_immersive_patch_with_property
    {B E G F H H' X N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ B H}
    {J : ModelWithCorners ℝ G H'} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {β χ : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {S : Set X}
    (hplateau : ∀ x ∈ S, b x ∈ interior {y | χ y = 1})
    (hcommon : ∀ x ∈ S, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F) (Q : (E → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (Smale.ChartMapPerturbation.perturb c f β a)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Q g ∧
          f.HomotopicRel g {y | β y = 0} ∧
            ∀ x ∈ S, Function.Injective (mfderiv 𝓘(ℝ, E) J g (b x)) := by
  let k := Smale.ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k := fun _ =>
      Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  have hQmem : {a : F | Q (Smale.ChartMapPerturbation.perturb c f β a)} ∈ 𝓝 0 := hQ
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨a, ha, -, hkernel⟩ :=
    Smale.WeightedPerturbation.exists_small_parameter_with_common_kernel hb hk hβ hdim
      (lt_min hε hδ)
  have haε : ‖a‖ < ε := (lt_min_iff.mp ha).1
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).2
  have hv := hvalid a haε
  have hsmooth := Smale.ChartMapPerturbation.contMDiff_perturb c hf hβ.contMDiff hsupport hv
  let g : C(E, N) := ⟨Smale.ChartMapPerturbation.perturb c f β a, hsmooth.continuous⟩
  have hQg : Q g :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine
    ⟨g, hsmooth, hQg,
      ⟨Smale.ChartMapPerturbation.homotopyRel c hf hβ.contMDiff hsupport hvalid haε⟩, ?_⟩
  intro x hx
  have hxplateau := hplateau x hx
  have hsource (y : E) (hy : χ y = 1) : f y ∈ c.source :=
    hχsupport (subset_tsupport χ (by change χ y ≠ 0; rw [hy]; exact one_ne_zero))
  have hxone : χ (b x) = 1 := interior_subset (s := {y | χ y = 1}) hxplateau
  have hfx := hsource (b x) hxone
  have hgx : g (b x) ∈ c.source := Smale.ChartMapPerturbation.perturb_mem_source c f β hv hfx
  have heqold : k =ᶠ[𝓝 (b x)] (c ∘ f) := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    exact
      Smale.ChartMapPerturbation.cutoffCoordinates_eq_of_one c f χ
        (interior_subset (s := {y | χ y = 1}) hy)
  have heqnew : (c ∘ g) =ᶠ[𝓝 (b x)] Smale.WeightedPerturbation.perturb k β a := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    have hyone : χ y = 1 := interior_subset (s := {y | χ y = 1}) hy
    change c (Smale.ChartMapPerturbation.perturb c f β a y) = _
    rw [Smale.ChartMapPerturbation.chart_perturb c f β hv (hsource y hyone)]
    simp only [Smale.ChartMapPerturbation.coordinateFamily, Smale.WeightedPerturbation.perturb, k,
      Smale.ChartMapPerturbation.cutoffCoordinates, hyone, one_smul]
  apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgx).mp
  change Function.Injective (fderiv ℝ (c ∘ g) (b x))
  rw [heqnew.fderiv_eq]
  intro v w hvw
  have hzero : fderiv ℝ (Smale.WeightedPerturbation.perturb k β a) (b x) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  obtain ⟨hkzero, hβzero⟩ := (hkernel x (v - w)).mp hzero
  have hnative : mfderiv 𝓘(ℝ, E) J f (b x) (v - w) = 0 := by
    apply (fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hfx (v - w)).mp
    rw [← heqold.fderiv_eq]
    exact hkzero
  exact sub_eq_zero.mp (hcommon x hx (v - w) hnative hβzero)

private theorem Smale.ChartMapPerturbation.derivative_eq_zero_iff_of_weight_derivative_eq_zero
    {E G F H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (ha : Valid c f β a) {x v : E} (hweight : fderiv ℝ β x v = 0) :
    mfderiv 𝓘(ℝ, E) J (perturb c f β a) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  by_cases hx : f x ∈ c.source
  · have hsmooth := contMDiff_perturb c hf hβ.contMDiff hsupport ha
    have hgx := perturb_mem_source c f β ha hx
    have hcf : ContDiffAt ℝ ∞ (c ∘ f) x :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp x
          hf.contMDiffAt) |>.contDiffAt
    have hcd :
      HasFDerivAt (fun y => c (f y) + β y • a) (fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a)
        x :=
      (hcf.differentiableAt (by simp)).hasFDerivAt.add
        ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)
    have heq : (c ∘ perturb c f β a) =ᶠ[𝓝 x] (fun y => c (f y) + β y • a) := by
      filter_upwards [(c.open_source.preimage hf.continuous).mem_nhds hx] with y hy
      exact chart_perturb c f β ha hy
    have hderiv :
      fderiv ℝ (c ∘ perturb c f β a) x = fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a :=
      heq.fderiv_eq.trans hcd.fderiv
    rw [←
      Smale.ManifoldImmersion.fderiv_chart_eq_zero_iff c (hsmooth.mdifferentiableAt (by simp)) hgx
        v,
      ← Smale.ManifoldImmersion.fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hx v,
      hderiv]
    change fderiv ℝ (c ∘ f) x v + fderiv ℝ β x v • a = 0 ↔ fderiv ℝ (c ∘ f) x v = 0
    rw [hweight, zero_smul, add_zero]
  · have hn : x ∉ tsupport β := fun ht => hx (hsupport ht)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hn
    have heq : perturb c f β a =ᶠ[𝓝 x] f := by
      filter_upwards [hzero] with y hy
      exact perturb_eq_of_zero c f β a hy
    rw [heq.mfderiv_eq]
    rfl

end Mathoverflow1973

end
