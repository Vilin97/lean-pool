/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core3
public import LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all Mathlib.Topology.Homotopy.Lifting

/-!
# Hopf problem: cusp fibre · cusp positive retraction

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

private def CuspRetraction.realToComplex : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ)
    where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [Complex.real_smul]

@[simp]
private theorem CuspRetraction.realToComplex_apply (v : Fin 2 → ℝ) (i : Fin 2) :
    realToComplex v i = (v i : ℂ) :=
  rfl

private theorem CuspRetraction.realToComplex_continuous : Continuous realToComplex := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_apply i)

@[simp]
private theorem CuspRetraction.norm_realToComplex (v : Fin 2 → ℝ) : ‖realToComplex v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using norm_le_pi_norm (realToComplex v) i

private def CuspRetraction.expFibreUnits (a : Fin 2 → ℂ) : Fin 2 → ℂˣ := fun i =>
  Units.mk0 (CuspUniformization.exponential (a i)) (CuspUniformization.exponential_ne_zero _)

@[simp]
private theorem CuspRetraction.expFibreUnits_coe (a : Fin 2 → ℂ) (i : Fin 2) :
    (expFibreUnits a i : ℂ) = CuspUniformization.exponential (a i) :=
  rfl

@[simp]
private theorem CuspRetraction.expFibreUnits_zero : expFibreUnits 0 = 1 := by
  ext i
  simp [expFibreUnits]

private theorem CuspRetraction.expFibreUnits_add (a b : Fin 2 → ℂ) :
    expFibreUnits (a + b) = expFibreUnits a * expFibreUnits b := by
  ext i
  simp [expFibreUnits, CuspUniformization.exponential_add]

private theorem CuspRetraction.expFibreUnits_continuous : Continuous expFibreUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun a : Fin 2 → ℂ => CuspUniformization.exponential (a i)) :=
    CuspUniformization.exponential_holomorphic.continuous.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun a => CuspUniformization.exponential_ne_zero (a i))⟩

private def
    CuspRetraction.expFibreAction (a : Fin 2 → ℂ) (x : ToricSpace.Space) : ToricSpace.Space :=
  ToricSpace.torusAction (ToricSpace.fibreMultiplier (expFibreUnits a)) x

@[simp]
private theorem
    CuspRetraction.expFibreAction_zero (x : ToricSpace.Space) : expFibreAction 0 x = x := by
  simp [expFibreAction]

private theorem CuspRetraction.expFibreAction_add (a b : Fin 2 → ℂ) (x : ToricSpace.Space) :
    expFibreAction a (expFibreAction b x) = expFibreAction (a + b) x := by
  simp only [expFibreAction, ToricSpace.torusAction_mul, expFibreUnits_add,
    ToricSpace.fibreMultiplier_mul]

@[simp]
private theorem CuspRetraction.time_expFibreAction (a : Fin 2 → ℂ) (x : ToricSpace.Space) :
    ToricSpace.time (expFibreAction a x) = ToricSpace.time x :=
  ToricSpace.time_fibreMultiplier _ _

private theorem CuspRetraction.expFibreAction_continuous :
    Continuous (fun p : (Fin 2 → ℂ) × ToricSpace.Space => expFibreAction p.1 p.2) := by
  have h :
    Continuous
      (fun p : (Fin 2 → ℂ) × ToricSpace.Space =>
        (ToricSpace.fibreMultiplier (expFibreUnits p.1), p.2)) :=
    ((ToricSpace.fibreMultiplier_continuous.comp expFibreUnits_continuous).comp
          continuous_fst).prodMk
      continuous_snd
  change
    Continuous
      ((fun p : ToricSpace.ActingTorus × ToricSpace.Space => ToricSpace.torusAction p.1 p.2) ∘
        (fun p : (Fin 2 → ℂ) × ToricSpace.Space =>
          (ToricSpace.fibreMultiplier (expFibreUnits p.1), p.2)))
  exact Continuous.comp ToricSpace.torusAction_joint_continuous h

private theorem CuspRetraction.expFibreAction_translate (a : Fin 2 → ℂ) (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    expFibreAction a (ToricSpace.translate v x) = ToricSpace.translate v (expFibreAction a x) :=
  ToricSpace.fibreMultiplier_translate _ _ _

private theorem
    CuspRetraction.torusCoordinates_expFibreAction (a : Fin 2 → ℂ) {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) (i : Fin 2) :
    ToricSpace.torusCoordinates (expFibreAction a x) i.castSucc =
      CuspUniformization.exponential (a i) * ToricSpace.torusCoordinates x i.castSucc := by
  rw [expFibreAction, ToricSpace.torusCoordinates_action _ hx]
  fin_cases i <;> rfl

private theorem CuspRetraction.position_expFibreAction (a : Fin 2 → ℂ) {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) :
    ToricSpace.position (expFibreAction a x) =
      ToricSpace.position x +
        (Real.log ‖ToricSpace.time x‖)⁻¹ • (fun i => -2 * Real.pi * (a i).im) := by
  ext i
  simp only [ToricSpace.position, time_expFibreAction, ToricSpace.logCoordinates,
    ToricSpace.logNorm, torusCoordinates_expFibreAction a hx, norm_mul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr (CuspUniformization.exponential_ne_zero _))
      (norm_ne_zero_iff.mpr (ToricSpace.torusCoordinates_nonzero hx _)),
    CuspUniformization.log_norm_exponential]
  ring

private theorem CuspRetraction.twistedTranslate_eq_expFibreAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate C v x =
      expFibreAction (C (ToricSpace.time x) *ᵥ (fun i => (v i : ℂ)))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) := by
  unfold ToricSpace.twistedTranslate ToricSpace.variableMultiplier
  rw [ToricSpace.time_translate]
  rfl

@[simp]
private theorem
    CuspRetraction.position_of_time_zero {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ToricSpace.position x = 0 := by
  ext i
  simp [ToricSpace.position, hx]

private def CuspRetraction.frozen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (_t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  C 0

private def CuspRetraction.correction (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : ToricSpace.Space) :
    Fin 2 → ℂ :=
  (D (ToricSpace.time x) - C (ToricSpace.time x)) *ᵥ
    realToComplex (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x))

private def CuspRetraction.changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : ToricSpace.Space) :
    ToricSpace.Space :=
  expFibreAction (correction C D x) x

@[simp]
private theorem CuspRetraction.time_changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ToricSpace.Space) : ToricSpace.time (changeTwist C D x) = ToricSpace.time x :=
  time_expFibreAction _ _

@[simp]
private theorem CuspRetraction.correction_of_time_zero (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) : correction C D x = 0 := by
  rw [correction, position_of_time_zero hx, map_zero, map_zero, Matrix.mulVec_zero]

@[simp]
private theorem CuspRetraction.changeTwist_of_time_zero (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) : changeTwist C D x = x := by
  rw [changeTwist, correction_of_time_zero C D hx, expFibreAction_zero]

private def CuspRetraction.tubeChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : ToricSpace.Tube (CuspQuotient.disc ε)) : ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨changeTwist C D x,
    by
    change ToricSpace.time (changeTwist C D x) ∈ CuspQuotient.disc ε
    rw [time_changeTwist]
    exact x.2⟩

private abbrev CuspRetraction.ClosedTube (η : ℝ) :=
  { x : ToricSpace.Space // ‖ToricSpace.time x‖ ≤ η }

private def CuspRetraction.closedTubeChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : ClosedTube η) : ClosedTube η :=
  ⟨changeTwist C D x, by
    rw [time_changeTwist]
    exact x.2⟩

private def CuspRetraction.complexEntryNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

private theorem CuspRetraction.complexEntryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ complexEntryNorm A :=
  norm_nonneg _

private theorem
    CuspRetraction.norm_complex_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ‖A *ᵥ v‖ ≤ 2 * complexEntryNorm A * ‖v‖ := by
  apply
    (pi_norm_le_iff_of_nonneg
        (by
          have := complexEntryNorm_nonneg A
          positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, complexEntryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul
          ((norm_le_pi_norm (A i) j).trans
            (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * complexEntryNorm A * ‖v‖ := by simp; ring

private theorem CuspRetraction.correction_norm_le (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    ‖correction C D x‖ ≤
      4 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
        ‖ToricSpace.position x‖ := by
  have hA := complexEntryNorm_nonneg (D (ToricSpace.time x) - C (ToricSpace.time x))
  calc
    ‖correction C D x‖ ≤
        2 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          ‖ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)‖ := by
      simpa only [correction, norm_realToComplex] using
        norm_complex_mulVec_le (D (ToricSpace.time x) - C (ToricSpace.time x))
          (realToComplex
            (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)))
    _ ≤
        2 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          (2 * ‖ToricSpace.position x‖) := by
      exact
        mul_le_mul_of_nonneg_left (ToricSpace.inverseDisplacement_norm_le C ht hR _)
          (by positivity)
    _ =
        4 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          ‖ToricSpace.position x‖ := by ring

private theorem CuspRetraction.correction_continuousAt_central (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0)
    (hD : ∀ i j, ContinuousAt (fun t => D t i j) 0) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ContinuousAt (correction C D) x := by
  obtain ⟨B, hB, hbound⟩ :=
    ToricSpace.position_locally_bounded hε hε1 (x := x) (by simpa only [hx, norm_zero] using hε)
  have htime : Filter.Tendsto ToricSpace.time (𝓝 x) (𝓝 0) := by
    simpa only [hx] using (ToricSpace.time_holomorphic.continuous.continuousAt (x := x)).tendsto
  have hdelta :
    ContinuousAt (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 => D t i j - C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (hD i j).sub (hC i j)
  have hnorm :
    Filter.Tendsto
      (fun y : ToricSpace.Space =>
        complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)))
      (𝓝 x) (𝓝 0) := by
    have hz : (fun i : Fin 2 => fun j : Fin 2 => D 0 i j - C 0 i j) = 0 := by
      ext i j
      simp only [hzero, sub_self, Pi.zero_apply]
    have h := hdelta.norm.tendsto.comp htime
    rw [hz, norm_zero] at h
    exact h
  have hlim :
    Filter.Tendsto
      (fun y : ToricSpace.Space =>
        4 * complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)) * B)
      (𝓝 x) (𝓝 0) := by
    simpa only [MulZeroClass.mul_zero, MulZeroClass.zero_mul] using
      (tendsto_const_nhds.mul hnorm).mul (tendsto_const_nhds (x := B))
  have hb :
    ∀ᶠ y in 𝓝 x,
      ‖correction C D y‖ ≤
        4 * complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)) * B := by
    filter_upwards [hbound] with y hy
    by_cases hy0 : ToricSpace.time y = 0
    · rw [correction_of_time_zero C D hy0, norm_zero]
      have := complexEntryNorm_nonneg (D (ToricSpace.time y) - C (ToricSpace.time y))
      positivity
    · have hn : 0 < ‖ToricSpace.time y‖ := norm_pos_iff.mpr hy0
      exact
        (correction_norm_le C D (Real.log_neg hn (hy.1.trans hε1)) (hR _ hn hy.1)).trans
          (mul_le_mul_of_nonneg_left hy.2
            (by
              have := complexEntryNorm_nonneg (D (ToricSpace.time y) - C (ToricSpace.time y))
              positivity))
  change Filter.Tendsto (correction C D) (𝓝 x) (𝓝 (correction C D x))
  rw [correction_of_time_zero C D hx]
  exact squeeze_zero_norm' hb hlim

private theorem CuspRetraction.correction_continuousAt_of_time_ne_zero
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hx0 : ToricSpace.time x ≠ 0)
    (hxε : ‖ToricSpace.time x‖ < ε) : ContinuousAt (correction C D) x := by
  have hmem : ToricSpace.time x ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have hC' (i j) : ContinuousAt (fun t => C t i j) (ToricSpace.time x) :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hD' (i j) : ContinuousAt (fun t => D t i j) (ToricSpace.time x) :=
    (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hn : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
  have ht : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg hn (hxε.trans hε1)
  have htime : ContinuousAt ToricSpace.time x :=
    ToricSpace.time_holomorphic.continuous.continuousAt
  have hi :
    ContinuousAt
      (fun y : ToricSpace.Space =>
        ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y))
      x := by
    exact
      ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        (ToricSpace.time y, ToricSpace.position y)) (g := fun p : ℂ × (Fin 2 → ℝ) =>
        ToricSpace.inverseDisplacement C p.1 p.2)
        (ToricSpace.inverseDisplacement_continuousAt C hC' ht (hR _ hn hxε)
          (ToricSpace.position x))
        (htime.prodMk (ToricSpace.position_continuousAt hx0 ht.ne))
  have hv :
    ContinuousAt
      (fun y : ToricSpace.Space =>
        realToComplex
          (ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)))
      x := by
    exact
      ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)) (g :=
        fun u : Fin 2 → ℝ => realToComplex u) realToComplex_continuous.continuousAt hi
  have hm :
    ContinuousAt (fun y : ToricSpace.Space => D (ToricSpace.time y) - C (ToricSpace.time y)) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact ((hD' i j).comp htime).sub ((hC' i j).comp htime)
  have hmul : Continuous (fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  change
    ContinuousAt
      ((fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) ∘
        (fun y : ToricSpace.Space =>
          (D (ToricSpace.time y) - C (ToricSpace.time y),
            realToComplex
              (ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)))))
      x
  exact ContinuousAt.comp hmul.continuousAt (hm.prodMk hv)

private theorem CuspRetraction.correction_continuousAt (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hxε : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (correction C D) x := by
  by_cases hx0 : ToricSpace.time x = 0
  · have hmem : (0 : ℂ) ∈ Metric.ball 0 ε := by simpa using hε
    exact
      correction_continuousAt_central C D hε hε1
        (fun i j => (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem))
        (fun i j => (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)) hzero hR hx0
  · exact correction_continuousAt_of_time_ne_zero C D hε1 hC hD hR hx0 hxε

private theorem CuspRetraction.changeTwist_continuousAt (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hxε : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (changeTwist C D) x := by
  change
    ContinuousAt
      ((fun p : (Fin 2 → ℂ) × ToricSpace.Space => expFibreAction p.1 p.2) ∘
        (fun y : ToricSpace.Space => (correction C D y, y)))
      x
  exact
    ContinuousAt.comp expFibreAction_continuous.continuousAt
      ((correction_continuousAt C D hε hε1 hC hD hzero hR hxε).prodMk continuousAt_id)

private theorem CuspRetraction.changeTwist_continuousOn (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) :
    ContinuousOn (changeTwist C D) (ToricSpace.time ⁻¹' Metric.ball 0 ε) := by
  intro x hx
  have hxε : ‖ToricSpace.time x‖ < ε := by
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx
  exact (changeTwist_continuousAt C D hε hε1 hC hD hzero hR hxε).continuousWithinAt

private theorem
    CuspRetraction.tubeChangeTwist_continuous (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) : Continuous (tubeChangeTwist C D ε) :=
  (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).domRestrict.subtype_mk _

private theorem
    CuspRetraction.displacement_change_matrix (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (u : Fin 2 → ℝ) :
    ToricSpace.displacement C t u +
        (fun i => (-2 * Real.pi) * (((D t - C t) *ᵥ (fun j => (u j : ℂ))) i).im / Real.log ‖t‖) =
      ToricSpace.displacement D t u := by
  ext i
  simp only [ToricSpace.displacement, LinearMap.add_apply, LinearMap.smul_apply,
    Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.sub_apply, Complex.add_im, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.mul_zero,
    ToricSpace.driftMatrix, div_eq_mul_inv]
  ring

private theorem CuspRetraction.position_changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    ToricSpace.position (changeTwist C D x) =
      ToricSpace.displacement D (ToricSpace.time x)
        (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) := by
  rw [changeTwist, position_expFibreAction _ hx]
  have h :=
    displacement_change_matrix C D (ToricSpace.time x)
      (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x))
  rw [ToricSpace.displacement_inverseDisplacement C ht hC] at h
  convert h using 1
  congr 1
  ext i
  have hu :
    realToComplex (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) =
      (fun j =>
        ((ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) j : ℂ)) :=
    by
    ext j
    rfl
  simp only [correction, hu, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem CuspRetraction.correction_reverse (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4)
    (hD :
      ToricSpace.entryNorm (ToricSpace.driftMatrix D (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    correction D C (changeTwist C D x) = -correction C D x := by
  unfold correction
  rw [time_changeTwist, position_changeTwist C D hx ht hC,
    ToricSpace.inverseDisplacement_displacement D ht hD]
  rw [show
      C (ToricSpace.time x) - D (ToricSpace.time x) =
        -(D (ToricSpace.time x) - C (ToricSpace.time x))
      by abel,
    Matrix.neg_mulVec]

private theorem CuspRetraction.changeTwist_inverse_on_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4)
    (hD :
      ToricSpace.entryNorm (ToricSpace.driftMatrix D (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    changeTwist D C (changeTwist C D x) = x := by
  change expFibreAction (correction D C (changeTwist C D x)) (changeTwist C D x) = x
  rw [correction_reverse C D hx ht hC hD]
  change expFibreAction (-correction C D x) (expFibreAction (correction C D x) x) = x
  rw [expFibreAction_add, neg_add_cancel, expFibreAction_zero]

private theorem
    CuspRetraction.changeTwist_inverse_on_disc (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (hD : ToricSpace.SmallDrift D ε)
    {x : ToricSpace.Space} (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist D C (changeTwist C D x) = x := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [changeTwist_of_time_zero C D hx0, changeTwist_of_time_zero D C hx0]
  · have hp : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
    exact
      changeTwist_inverse_on_torus C D ((ToricSpace.mem_openTorus_iff x).mpr hx0)
        (Real.log_neg hp (hx.trans hε)) (hC _ hp hx) (hD _ hp hx)

private theorem CuspRetraction.correction_twistedTranslate (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus)
    (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    correction C D (ToricSpace.twistedTranslate C v x) =
      correction C D x +
        (D (ToricSpace.time x) - C (ToricSpace.time x)) *ᵥ (fun i => (v i : ℂ)) := by
  unfold correction
  rw [ToricSpace.time_twistedTranslate,
    ToricSpace.position_twistedTranslate_displacement C v hx ht.ne,
    ToricSpace.inverseDisplacement_add, ToricSpace.inverseDisplacement_displacement C ht hC,
    map_add, Matrix.mulVec_add]
  congr 2

private theorem CuspRetraction.changeTwist_equivariant_on_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus)
    (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    changeTwist C D (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (changeTwist C D x) := by
  change
    expFibreAction (correction C D (ToricSpace.twistedTranslate C v x))
        (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (expFibreAction (correction C D x) x)
  rw [correction_twistedTranslate C D v hx ht hC, twistedTranslate_eq_expFibreAction C v x,
    twistedTranslate_eq_expFibreAction D v (expFibreAction (correction C D x) x),
    time_expFibreAction, ← expFibreAction_translate, expFibreAction_add, expFibreAction_add]
  congr 1
  rw [Matrix.sub_mulVec]
  abel

private theorem CuspRetraction.changeTwist_equivariant_on_disc (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (h₀ : C 0 = D 0) {ε : ℝ} (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (v : Fin 2 → ℤ)
    {x : ToricSpace.Space} (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist C D (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (changeTwist C D x) := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [changeTwist_of_time_zero C D (by simpa only [ToricSpace.time_twistedTranslate] using hx0),
      changeTwist_of_time_zero C D hx0, twistedTranslate_eq_expFibreAction C v x,
      twistedTranslate_eq_expFibreAction D v x, hx0, h₀]
  · have hp : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
    exact
      changeTwist_equivariant_on_torus C D v ((ToricSpace.mem_openTorus_iff x).mpr hx0)
        (Real.log_neg hp (hx.trans hε)) (hC _ hp hx)

private theorem
    CuspRetraction.changeTwist_frozen_equivariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (v : Fin 2 → ℤ) {x : ToricSpace.Space}
    (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist C (frozen C) (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate (frozen C) v (changeTwist C (frozen C) x) :=
  changeTwist_equivariant_on_disc C (frozen C) rfl hε hC v hx

private theorem
    CuspRetraction.position_unit_fibreAction (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : ToricSpace.Space) :
    ToricSpace.position (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) =
      ToricSpace.position x := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [position_of_time_zero (by simpa only [ToricSpace.time_fibreMultiplier] using hx0),
      position_of_time_zero hx0]
  · have hx := (ToricSpace.mem_openTorus_iff x).mpr hx0
    ext i
    simp only [ToricSpace.position, ToricSpace.time_fibreMultiplier, ToricSpace.logCoordinates,
      ToricSpace.logNorm, ToricSpace.torusCoordinates_action _ hx, Pi.mul_apply]
    fin_cases i <;> simp [ToricSpace.fibreMultiplier, hu]

private theorem CuspRetraction.changeTwist_unit_fibreAction (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ToricSpace.Space) :
    changeTwist C D (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) =
      ToricSpace.torusAction (ToricSpace.fibreMultiplier u) (changeTwist C D x) := by
  have hc :
    correction C D (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) = correction C D x :=
    by simp only [correction, ToricSpace.time_fibreMultiplier, position_unit_fibreAction u hu]
  simp only [changeTwist, hc, expFibreAction, ToricSpace.torusAction_mul]
  rw [mul_comm]

private def CuspRetraction.tubeHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) :
    ToricSpace.Tube (CuspQuotient.disc ε) ≃ₜ ToricSpace.Tube (CuspQuotient.disc ε)
    where
  toFun := tubeChangeTwist C D ε
  invFun := tubeChangeTwist D C ε
  left_inv
    x := by
    apply Subtype.ext
    exact
      changeTwist_inverse_on_disc C D hε1 hRC hRD
        (by
          have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
          simpa only [Metric.mem_ball, dist_zero_right] using hx)
  right_inv
    x := by
    apply Subtype.ext
    exact
      changeTwist_inverse_on_disc D C hε1 hRD hRC
        (by
          have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
          simpa only [Metric.mem_ball, dist_zero_right] using hx)
  continuous_toFun := tubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC
  continuous_invFun := tubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD

private theorem CuspRetraction.closedTubeChangeTwist_continuous (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) (hηε : η < ε) : Continuous (closedTubeChangeTwist C D η) := by
  have h : ContinuousOn (changeTwist C D) {x : ToricSpace.Space | ‖ToricSpace.time x‖ ≤ η} :=
    (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).mono
      (fun x hx => by
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx.trans_lt hηε)
  exact h.domRestrict.subtype_mk _

private def CuspRetraction.closedTubeHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε) :
    ClosedTube η ≃ₜ ClosedTube η
    where
  toFun := closedTubeChangeTwist C D η
  invFun := closedTubeChangeTwist D C η
  left_inv x := Subtype.ext (changeTwist_inverse_on_disc C D hε1 hRC hRD (x.2.trans_lt hηε))
  right_inv x := Subtype.ext (changeTwist_inverse_on_disc D C hε1 hRD hRC (x.2.trans_lt hηε))
  continuous_toFun := closedTubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC hηε
  continuous_invFun := closedTubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD hηε

private def
    CuspRetraction.closedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (v : Fin 2 → ℤ)
    (x : ClosedTube η) : ClosedTube η :=
  ⟨ToricSpace.twistedTranslate C v x, by simpa only [ToricSpace.time_twistedTranslate] using x.2⟩

private def
    CuspRetraction.closedFibreAction (η : ℝ) (u : Fin 2 → ℂˣ) (x : ClosedTube η) : ClosedTube η :=
  ⟨ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x, by
    simpa only [ToricSpace.time_fibreMultiplier] using x.2⟩

private theorem
    CuspRetraction.closedTubeHomeomorph_base (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (x : ClosedTube η) :
    ToricSpace.time
        (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x : ToricSpace.Space) =
      ToricSpace.time x :=
  time_changeTwist C D x

private theorem
    CuspRetraction.closedTubeHomeomorph_fixes_central (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (x : ClosedTube η) (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x = x :=
  Subtype.ext (changeTwist_of_time_zero C D hx)

private theorem CuspRetraction.closedTubeHomeomorph_equivariant (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (v : Fin 2 → ℤ) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedTranslate C η v x) =
      closedTranslate D η v (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_equivariant_on_disc C D hzero hε1 hRC v (x.2.trans_lt hηε))

private theorem CuspRetraction.closedTubeHomeomorph_fibre_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedFibreAction η u x) =
      closedFibreAction η u (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_unit_fibreAction C D u hu x)

private theorem
    CuspRetraction.exists_common_frozen_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ}
    (hr : 0 < r) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧ ε < r ∧ ε < 1 ∧ ToricSpace.SmallDrift C ε ∧ ToricSpace.SmallDrift (frozen C) ε := by
  have hC0 (i j) : ContinuousAt (fun t => C t i j) 0 :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hRδ⟩ := ToricSpace.exists_smallDrift_radius C hC0
  obtain ⟨δ₀, hδ₀, _, hRδ₀⟩ :=
    ToricSpace.exists_smallDrift_radius (frozen C) (fun _ _ => continuousAt_const)
  refine
    ⟨Min.min (r / 2) (Min.min δ δ₀), lt_min (half_pos hr) (lt_min hδ hδ₀),
      (min_le_left _ _).trans_lt (half_lt_self hr),
      ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hδ1,
      hRδ.mono ((min_le_right _ _).trans (min_le_left _ _)),
      hRδ₀.mono ((min_le_right _ _).trans (min_le_right _ _))⟩

private abbrev CuspRetraction.ClosedQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ) :=
  { x : CuspQuotient.QuotientSpace C ε // ‖CuspQuotient.projection C ε x‖ ≤ η }

private def
    CuspRetraction.closedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (x : ClosedTube η) : ClosedQuotient C ε η :=
  ⟨CuspQuotient.quotientMap C ε
      ⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩,
    x.2⟩

@[simp]
private theorem
    CuspRetraction.closedQuotientMap_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (x : ClosedTube η) :
    CuspQuotient.projection C ε (closedQuotientMap C hηε x) =
      ToricSpace.time (x : ToricSpace.Space) :=
  rfl

private theorem
    CuspRetraction.closedQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) : Function.Surjective (closedQuotientMap C hηε) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨⟨x, hq⟩, rfl⟩

private def CuspRetraction.closedTubePreimageHomeomorph_mo1973_10381
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) :
    ClosedTube η ≃ₜ
      (CuspQuotient.quotientMap C ε ⁻¹'
        {q : CuspQuotient.QuotientSpace C ε | ‖CuspQuotient.projection C ε q‖ ≤ η})
    where
  toFun
    x :=
    ⟨⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩,
      x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

private theorem
    CuspRetraction.closedQuotientMap_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (closedQuotientMap C hηε) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let := CuspQuotient.continuous_action C ε hC
  have hq : IsOpenQuotientMap (CuspQuotient.quotientMap C ε) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact
    (hq.restrictPreimage
          {q : CuspQuotient.QuotientSpace C ε | ‖CuspQuotient.projection C ε q‖ ≤ η}).comp
      (closedTubePreimageHomeomorph_mo1973_10381 C hηε).isOpenQuotientMap

private theorem CuspRetraction.closedQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (x y : ClosedTube η) :
    closedQuotientMap C hηε x = closedQuotientMap C hηε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) at hrel
    obtain ⟨g, hg⟩ := hrel
    exact ⟨g.toAdd, congrArg Subtype.val hg⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply Quotient.sound
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε))
    exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩

private theorem CuspCentralHomology.cuspQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (δ : ℝ) : Function.Surjective (CuspQuotient.quotientMap C δ) :=
  Quotient.mk_surjective

private abbrev CuspCentralHomology.OpenQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) :=
  { q : CuspQuotient.QuotientSpace C r // ‖CuspQuotient.projection C r q‖ < δ }

private def
    CuspCentralHomology.openQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (x : ToricSpace.Tube (CuspQuotient.disc δ)) : OpenQuotient C r δ :=
  ⟨CuspQuotient.quotientMap C r
      ⟨x, by
        have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
        exact Metric.ball_subset_ball hδr hx⟩,
    by
    change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ
    have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx⟩

private theorem CuspCentralHomology.openQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r δ : ℝ} (hδr : δ ≤ r) : Function.Surjective (openQuotientMap C hδr) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ at hq
  refine ⟨⟨x, ?_⟩, rfl⟩
  change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ
  simpa only [Metric.mem_ball, dist_zero_right] using hq

private def CuspCentralHomology.openTubePreimageHomeomorph_mo1973_10400
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r) :
    ToricSpace.Tube (CuspQuotient.disc δ) ≃ₜ
      (CuspQuotient.quotientMap C r ⁻¹'
        {q : CuspQuotient.QuotientSpace C r | ‖CuspQuotient.projection C r q‖ < δ})
    where
  toFun
    x :=
    ⟨⟨x, Metric.ball_subset_ball hδr x.2⟩,
      by
      change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ
      have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
      simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  invFun
    x :=
    ⟨x.1.1, by
      change ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 δ
      have hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ < δ := x.2
      simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

private theorem
    CuspCentralHomology.openQuotientMap_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r δ : ℝ} (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (openQuotientMap C hδr) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc r)
  let := CuspQuotient.continuous_action C r hC
  have hq : IsOpenQuotientMap (CuspQuotient.quotientMap C r) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact
    (hq.restrictPreimage
          {q : CuspQuotient.QuotientSpace C r | ‖CuspQuotient.projection C r q‖ < δ}).comp
      (openTubePreimageHomeomorph_mo1973_10400 C hδr).isOpenQuotientMap

private theorem
    CuspCentralHomology.openQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ}
    (hδr : δ ≤ r) (x y : ToricSpace.Tube (CuspQuotient.disc δ)) :
    openQuotientMap C hδr x = openQuotientMap C hδr y ↔
      CuspQuotient.quotientMap C δ x = CuspQuotient.quotientMap C δ y := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc r)
  let := ToricSpace.tubeAction C (CuspQuotient.disc δ)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' :
      ToricSpace.twistedTranslate C g.toAdd (y : ToricSpace.Space) = (x : ToricSpace.Space) :=
      congrArg (fun z : ToricSpace.Tube (CuspQuotient.disc r) => (z : ToricSpace.Space)) hg
    apply Quotient.sound
    change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y
    exact ⟨g, Subtype.ext hg'⟩
  · intro h
    have hrel := Quotient.exact h
    change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' :
      ToricSpace.twistedTranslate C g.toAdd (y : ToricSpace.Space) = (x : ToricSpace.Space) :=
      congrArg (fun z : ToricSpace.Tube (CuspQuotient.disc δ) => (z : ToricSpace.Space)) hg
    apply Subtype.ext
    apply Quotient.sound
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r))
    exact ⟨g, Subtype.ext hg'⟩

private def
    CuspCentralHomology.openQuotientRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ}
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    CuspQuotient.QuotientSpace C δ ≃ₜ OpenQuotient C r δ
    where
  toFun :=
    CuspHoneycombHexagon.CommonFibres.descend (CuspQuotient.quotientMap C δ)
      (openQuotientMap C hδr) (cuspQuotientMap_surjective C δ)
  invFun :=
    CuspHoneycombHexagon.CommonFibres.descend (openQuotientMap C hδr)
      (CuspQuotient.quotientMap C δ) (openQuotientMap_surjective C hδr)
  left_inv
    q := by
    obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr),
      CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)]
  right_inv
    q := by
    obtain ⟨x, rfl⟩ := openQuotientMap_surjective C hδr q
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mp),
      CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)]
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _ isQuotientMap_quotient_mk'
      (openQuotientMap_isOpenQuotientMap C hδr hC).continuous
      (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)
  continuous_invFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _
      (openQuotientMap_isOpenQuotientMap C hδr hC).isQuotientMap
      (CuspQuotient.quotientMap_continuous C δ) (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)

@[simp]
private theorem CuspCentralHomology.openQuotientRadiusHomeomorph_quotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (x : ToricSpace.Tube (CuspQuotient.disc δ)) :
    openQuotientRadiusHomeomorph C hδr hC (CuspQuotient.quotientMap C δ x) =
      openQuotientMap C hδr x :=
  CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
    (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr) x

private theorem CuspCentralHomology.openQuotientRadiusHomeomorph_projection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (q : CuspQuotient.QuotientSpace C δ) :
    CuspQuotient.projection C r (openQuotientRadiusHomeomorph C hδr hC q) =
      CuspQuotient.projection C δ q := by
  obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
  rw [openQuotientRadiusHomeomorph_quotientMap]
  rfl

private abbrev CuspPositiveRetraction.Orthant :=
  { r : Fin 3 → ℝ // ∀ i, 0 ≤ r i }

private theorem
    CuspPositiveRetraction.orthant_isClosed : IsClosed {r : Fin 3 → ℝ | ∀ i, 0 ≤ r i} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

private instance CuspPositiveRetraction.instLocal1 : ProperSpace Orthant :=
  ProperSpace.of_isClosed orthant_isClosed

private def CuspPositiveRetraction.height (r : Orthant) : ℝ :=
  ∏ i, r.1 i

private theorem CuspPositiveRetraction.height_nonneg (r : Orthant) : 0 ≤ height r :=
  Finset.prod_nonneg fun i _ => r.2 i

private theorem
    CuspPositiveRetraction.height_eq_zero_iff (r : Orthant) : height r = 0 ↔ ∃ i, r.1 i = 0 :=
  by simp only [height, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

private def CuspPositiveRetraction.minimum (r : Orthant) : ℝ :=
  Min.min (r.1 0) (Min.min (r.1 1) (r.1 2))

private theorem CuspPositiveRetraction.minimum_nonneg (r : Orthant) : 0 ≤ minimum r :=
  le_min (r.2 0) (le_min (r.2 1) (r.2 2))

private theorem
    CuspPositiveRetraction.minimum_le (r : Orthant) (i : Fin 3) : minimum r ≤ r.1 i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private theorem CuspPositiveRetraction.minimum_eq_coordinate (r : Orthant) :
    ∃ i : Fin 3, minimum r = r.1 i := by
  rcases min_choice (r.1 0) (Min.min (r.1 1) (r.1 2)) with h | h
  · exact ⟨0, h⟩
  · rcases min_choice (r.1 1) (r.1 2) with h' | h'
    · exact ⟨1, h.trans h'⟩
    · exact ⟨2, h.trans h'⟩

private theorem
    CuspPositiveRetraction.minimum_eq_zero_iff (r : Orthant) : minimum r = 0 ↔ height r = 0 :=
  by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := minimum_eq_coordinate r
    exact (height_eq_zero_iff r).mpr ⟨i, hi.symm.trans h⟩
  · intro h
    obtain ⟨i, hi⟩ := (height_eq_zero_iff r).mp h
    exact le_antisymm (by simpa only [hi] using minimum_le r i) (minimum_nonneg r)

private theorem CuspPositiveRetraction.minimum_continuous : Continuous minimum :=
  ((continuous_apply 0).comp continuous_subtype_val).min
    (((continuous_apply 1).comp continuous_subtype_val).min
      ((continuous_apply 2).comp continuous_subtype_val))

private def CuspPositiveRetraction.shrink (s : unitInterval) (r : Orthant) : Orthant :=
  ⟨fun i => r.1 i - (s : ℝ) * minimum r, fun i =>
    sub_nonneg.mpr ((mul_le_of_le_one_left (minimum_nonneg r) s.2.2).trans (minimum_le r i))⟩

@[simp]
private theorem CuspPositiveRetraction.shrink_apply (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i = r.1 i - (s : ℝ) * minimum r :=
  rfl

private theorem CuspPositiveRetraction.shrink_continuous :
    Continuous (fun p : unitInterval × Orthant => shrink p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).sub
      ((continuous_subtype_val.comp continuous_fst).mul (minimum_continuous.comp continuous_snd))

@[simp]
private theorem CuspPositiveRetraction.shrink_zero (r : Orthant) : shrink 0 r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, Set.Icc.coe_zero, MulZeroClass.zero_mul, sub_zero]

private theorem
    CuspPositiveRetraction.shrink_one_height (r : Orthant) : height (shrink 1 r) = 0 := by
  obtain ⟨i, hi⟩ := minimum_eq_coordinate r
  apply (height_eq_zero_iff _).mpr
  refine ⟨i, ?_⟩
  simp only [shrink_apply, Set.Icc.coe_one, one_mul, hi, sub_self]

private theorem
    CuspPositiveRetraction.shrink_fixed (s : unitInterval) {r : Orthant} (hr : height r = 0) :
    shrink s r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, (minimum_eq_zero_iff r).mpr hr, MulZeroClass.mul_zero, sub_zero]

private theorem
    CuspPositiveRetraction.shrink_coordinate_le (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i ≤ r.1 i :=
  sub_le_self _ (mul_nonneg s.2.1 (minimum_nonneg r))

private theorem CuspPositiveRetraction.shrink_height_le (s : unitInterval) (r : Orthant) :
    height (shrink s r) ≤ height r :=
  Finset.prod_le_prod (fun i _ => (shrink s r).2 i) (fun i _ => shrink_coordinate_le s r i)

private theorem CuspPositiveRetraction.shrink_dist_eq (s : unitInterval) (r : Orthant) :
    Dist.dist (shrink s r) r = (s : ℝ) * minimum r := by
  rw [Subtype.dist_eq, dist_eq_norm]
  have he : (shrink s r).1 - r.1 = fun _ : Fin 3 => -((s : ℝ) * minimum r) := by
    funext i
    simp only [Pi.sub_apply, shrink_apply]
    ring
  rw [he, pi_norm_const, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg s.2.1 (minimum_nonneg r))]

private theorem CuspPositiveRetraction.shrink_dist_le_minimum (s : unitInterval) (r : Orthant) :
    Dist.dist (shrink s r) r ≤ minimum r := by
  rw [shrink_dist_eq]
  exact mul_le_of_le_one_left (minimum_nonneg r) s.2.2

private theorem
    CuspPositiveRetraction.minimum_le_dist_of_height_eq_zero (r : Orthant) {r₀ : Orthant}
    (hr₀ : height r₀ = 0) : minimum r ≤ Dist.dist r r₀ := by
  obtain ⟨i, hi⟩ := (height_eq_zero_iff r₀).mp hr₀
  calc
    minimum r ≤ r.1 i := minimum_le r i
    _ = ‖(r.1 - r₀.1) i‖ := by
      simp only [Pi.sub_apply, hi, sub_zero, Real.norm_eq_abs, abs_of_nonneg (r.2 i)]
    _ ≤ ‖r.1 - r₀.1‖ := (norm_le_pi_norm _ i)
    _ = Dist.dist r r₀ := (dist_eq_norm _ _).symm

private theorem CuspPositiveRetraction.shrink_dist_le_twice_dist (s : unitInterval) (r : Orthant)
    {r₀ : Orthant} (hr₀ : height r₀ = 0) : Dist.dist (shrink s r) r₀ ≤ 2 * Dist.dist r r₀ := by
  calc
    Dist.dist (shrink s r) r₀ ≤ Dist.dist (shrink s r) r + Dist.dist r r₀ := dist_triangle _ _ _
    _ ≤ minimum r + Dist.dist r r₀ := (add_le_add (shrink_dist_le_minimum s r) le_rfl)
    _ ≤ Dist.dist r r₀ + Dist.dist r r₀ :=
      (add_le_add (minimum_le_dist_of_height_eq_zero r hr₀) le_rfl)
    _ = 2 * Dist.dist r r₀ := (two_mul _).symm

private def CuspPositiveRetraction.cutoff (r₀ : Orthant) (R : ℝ) (r : Orthant) : ℝ :=
  Max.max 0 (Min.min 1 (4 - 12 * Dist.dist r r₀ / R))

private theorem CuspPositiveRetraction.cutoff_nonneg (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    0 ≤ cutoff r₀ R r :=
  le_max_left _ _

private theorem CuspPositiveRetraction.cutoff_le_one (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    cutoff r₀ R r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem CuspPositiveRetraction.cutoff_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (cutoff r₀ R) :=
  continuous_const.max
    (continuous_const.min
      (continuous_const.sub
        ((continuous_const.mul (continuous_id.dist continuous_const)).div_const R)))

private theorem CuspPositiveRetraction.cutoff_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) : cutoff r₀ R r = 1 := by
  have hdiv : 12 * Dist.dist r r₀ / R ≤ 3 := (div_le_iff₀ hR).mpr (by linarith)
  have h : 1 ≤ 4 - 12 * Dist.dist r r₀ / R := by linarith
  exact (congrArg (Max.max (0 : ℝ)) (min_eq_left h)).trans (max_eq_right zero_le_one)

private theorem CuspPositiveRetraction.cutoff_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : cutoff r₀ R r = 0 := by
  have hdiv : 4 ≤ 12 * Dist.dist r r₀ / R := (le_div_iff₀ hR).mpr (by linarith)
  have h : 4 - 12 * Dist.dist r r₀ / R ≤ 0 := by linarith
  exact (congrArg (Max.max (0 : ℝ)) (min_eq_right (h.trans zero_le_one))).trans (max_eq_left h)

private def
    CuspPositiveRetraction.cutoffParameter (r₀ : Orthant) (R : ℝ) (r : Orthant) : unitInterval :=
  ⟨cutoff r₀ R r, cutoff_nonneg r₀ R r, cutoff_le_one r₀ R r⟩

private theorem CuspPositiveRetraction.cutoffParameter_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) : cutoffParameter r₀ R r = 1 :=
  Subtype.ext (cutoff_eq_one_of_dist_le r₀ hR hr)

private theorem CuspPositiveRetraction.cutoffParameter_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : cutoffParameter r₀ R r = 0 :=
  Subtype.ext (cutoff_eq_zero_of_le_dist r₀ hR hr)

private def
    CuspPositiveRetraction.localShrink (r₀ : Orthant) (R : ℝ) (s : unitInterval) (r : Orthant) :
    Orthant :=
  shrink (s * cutoffParameter r₀ R r) r

private theorem CuspPositiveRetraction.localShrink_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (fun p : unitInterval × Orthant => localShrink r₀ R p.1 p.2) := by
  have hp : Continuous (fun p : unitInterval × Orthant => p.1 * cutoffParameter r₀ R p.2) := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        ((cutoff_continuous r₀ R).comp continuous_snd)
  exact shrink_continuous.comp (hp.prodMk continuous_snd)

@[simp]
private theorem CuspPositiveRetraction.localShrink_zero (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    localShrink r₀ R 0 r = r := by simp only [localShrink, MulZeroClass.zero_mul, shrink_zero]

private theorem CuspPositiveRetraction.localShrink_fixed (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    {r : Orthant} (hr : height r = 0) : localShrink r₀ R s r = r :=
  shrink_fixed _ hr

private theorem
    CuspPositiveRetraction.localShrink_height_le (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    (r : Orthant) : height (localShrink r₀ R s r) ≤ height r :=
  shrink_height_le _ r

private theorem
    CuspPositiveRetraction.localShrink_dist_le_twice_dist {r₀ : Orthant} (hr₀ : height r₀ = 0)
    (R : ℝ) (s : unitInterval) (r : Orthant) :
    Dist.dist (localShrink r₀ R s r) r₀ ≤ 2 * Dist.dist r r₀ :=
  shrink_dist_le_twice_dist _ r hr₀

private theorem
    CuspPositiveRetraction.localShrink_eq_self_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    (s : unitInterval) {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : localShrink r₀ R s r = r := by
  rw [localShrink, cutoffParameter_eq_zero_of_le_dist r₀ hR hr, MulZeroClass.mul_zero,
    shrink_zero]

private theorem
    CuspPositiveRetraction.localShrink_eq_self_of_not_mem_closedBall (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) (s : unitInterval) {r : Orthant} (hr : r ∉ Metric.closedBall r₀ (R / 3)) :
    localShrink r₀ R s r = r :=
  localShrink_eq_self_of_le_dist r₀ hR s (not_le.mp hr).le

private theorem CuspPositiveRetraction.localShrink_one_height_of_dist_le (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) :
    height (localShrink r₀ R 1 r) = 0 := by
  rw [localShrink, cutoffParameter_eq_one_of_dist_le r₀ hR hr, one_mul]
  exact shrink_one_height r

private theorem CuspPositiveRetraction.localShrink_one_height_of_mem_ball (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : r ∈ Metric.ball r₀ (R / 4)) :
    height (localShrink r₀ R 1 r) = 0 :=
  localShrink_one_height_of_dist_le r₀ hR hr.le

private theorem CuspPositiveRetraction.localShrink_mapsTo_ball {r₀ : Orthant} (hr₀ : height r₀ = 0)
    {R : ℝ} (hR : 0 < R) (s : unitInterval) :
    Set.MapsTo (localShrink r₀ R s) (Metric.ball r₀ R) (Metric.ball r₀ R) := by
  intro r hr
  by_cases hd : Dist.dist r r₀ < R / 3
  · have hb := localShrink_dist_le_twice_dist hr₀ R s r
    change Dist.dist (localShrink r₀ R s r) r₀ < R
    linarith
  · rw [localShrink_eq_self_of_le_dist r₀ hR s (le_of_not_gt hd)]
    exact hr

private theorem
    CuspPositiveRetraction.localShrink_map_ball {r₀ : Orthant} (hr₀ : height r₀ = 0) {R : ℝ}
    (hR : 0 < R) (s : unitInterval) {r : Orthant} (hr : r ∈ Metric.ball r₀ R) :
    localShrink r₀ R s r ∈ Metric.ball r₀ R :=
  localShrink_mapsTo_ball hr₀ hR s hr

private noncomputable def
    CuspPositiveRetraction.Supported.extend {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (p : S × Y) : Y := by
  classical exact if hy : p.2 ∈ e.target then e (H (p.1, ⟨e.symm p.2, e.map_target hy⟩)) else p.2

private theorem CuspPositiveRetraction.Supported.extend_target {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∈ e.target) :
    CuspPositiveRetraction.Supported.extend e H (s, y) = e (H (s, ⟨e.symm y, e.map_target hy⟩)) :=
  by exact dite_eq_left hy

private theorem CuspPositiveRetraction.Supported.extend_not_mem_target {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∉ e.target) :
    CuspPositiveRetraction.Supported.extend e H (s, y) = y := by exact dite_eq_right hy

private theorem CuspPositiveRetraction.Supported.extend_chart {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (x : e.source) :
    CuspPositiveRetraction.Supported.extend e H (s, e x) = e (H (s, x)) := by
  rw [extend_target e H s (e x) (e.map_source x.2)]
  exact congrArg (fun z : e.source => e (H (s, z))) (Subtype.ext (e.left_inv x.2))

private theorem
    CuspPositiveRetraction.Supported.extend_not_mem_image {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) (s : S) (y : Y)
    (hyK : y ∉ e '' K) : CuspPositiveRetraction.Supported.extend e H (s, y) = y := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy]
    have hxK : e.symm y ∉ K := fun hx => hyK ⟨e.symm y, hx, e.right_inv hy⟩
    rw [hfix s ⟨e.symm y, e.map_target hy⟩ hxK]
    exact e.right_inv hy
  · exact extend_not_mem_target e H s y hy

private theorem CuspPositiveRetraction.Supported.extend_continuousOn_target {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) :
    ContinuousOn (CuspPositiveRetraction.Supported.extend e H) (Prod.snd ⁻¹' e.target) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g : (Prod.snd ⁻¹' e.target : Set (S × Y)) → S × e.source := fun p =>
    (p.1.1, e.toHomeomorphSourceTarget.symm ⟨p.1.2, p.2⟩)
  have hg : Continuous g :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (e.toHomeomorphSourceTarget.symm.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hc :=
    continuous_subtype_val.comp
      (e.toHomeomorphSourceTarget.continuous.comp (H.continuous.comp hg))
  apply hc.congr
  intro p
  exact (extend_target e H p.1.1 p.1.2 p.2).symm

private theorem
    CuspPositiveRetraction.Supported.extend_continuous {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) :
    Continuous (CuspPositiveRetraction.Supported.extend e H) := by
  have hclosed : IsClosed (e '' K) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed
  have hout :
    ContinuousOn (CuspPositiveRetraction.Supported.extend e H) (Prod.snd ⁻¹' (e '' K)ᶜ) :=
    continuous_snd.continuousOn.congr fun p hp => extend_not_mem_image e H K hfix p.1 p.2 hp
  have hcover : (Prod.snd ⁻¹' e.target : Set (S × Y)) ∪ (Prod.snd ⁻¹' (e '' K)ᶜ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : p.2 ∈ e.target
    · exact Or.inl hp
    · right
      rintro ⟨x, hx, hxy⟩
      exact hp (hxy ▸ e.map_source (hKs hx))
  rw [← continuousOn_univ, ← hcover]
  exact
    (extend_continuousOn_target e H).union_of_isOpen hout (e.open_target.preimage continuous_snd)
      (hclosed.isOpen_compl.preimage continuous_snd)

private noncomputable def CuspPositiveRetraction.Supported.embeddingLocalMap_mo1973_10473
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) :
    C(S × (he.toOpenPartialHomeomorph e).source, (he.toOpenPartialHomeomorph e).source)
    where
  toFun p := ⟨H (p.1, p.2.1), Set.mem_univ _⟩
  continuous_toFun :=
    (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

private noncomputable def CuspPositiveRetraction.Supported.embeddingExtend {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) : S × Y → Y :=
  CuspPositiveRetraction.Supported.extend (he.toOpenPartialHomeomorph e)
    (embeddingLocalMap_mo1973_10473 e he H)

private theorem CuspPositiveRetraction.Supported.embeddingExtend_chart {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (x : X) :
    embeddingExtend e he H (s, e x) = e (H (s, x)) := by
  let x' : (he.toOpenPartialHomeomorph e).source := ⟨x, Set.mem_univ _⟩
  simpa only [embeddingExtend, embeddingLocalMap_mo1973_10473, ContinuousMap.coe_mk,
    he.toOpenPartialHomeomorph_apply e] using
    extend_chart (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) s x'

private theorem CuspPositiveRetraction.Supported.embeddingExtend_not_mem_range {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (y : Y) (hy : y ∉ Set.range e) :
    embeddingExtend e he H (s, y) = y := by
  exact
    extend_not_mem_target (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) s
      y (by simpa only [he.toOpenPartialHomeomorph_target e] using hy)

private theorem CuspPositiveRetraction.Supported.embeddingExtend_continuous {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [T2Space Y]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) : Continuous (embeddingExtend e he H) := by
  apply
    extend_continuous (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) K hK
  · rw [he.toOpenPartialHomeomorph_source e]
    exact Set.subset_univ K
  · intro s x hx
    exact Subtype.ext (hfix s x hx)

private noncomputable def CuspPositiveRetraction.Supported.embeddingMap {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [T2Space Y]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) : C(S × Y, Y) :=
  ⟨embeddingExtend e he H, embeddingExtend_continuous e he H K hK hfix⟩

private theorem
    CuspPositiveRetraction.Supported.embeddingExtend_id {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (hs : ∀ x : X, H (s, x) = x)
    (y : Y) : embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hs]
  · exact embeddingExtend_not_mem_range e he H s y hy

private theorem CuspPositiveRetraction.Supported.embeddingExtend_fixed {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (A : Set Y)
    (hfix : ∀ (s : S) (x : X), e x ∈ A → H (s, x) = x) (s : S) (y : Y) (hyA : y ∈ A) :
    embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hfix s x hyA]
  · exact embeddingExtend_not_mem_range e he H s y hy

private theorem
    CuspPositiveRetraction.Supported.embeddingExtend_rel {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (R : Y → Y → Prop) (hrefl : ∀ y, R y y)
    (hlocal : ∀ (s : S) (x : X), R (e x) (e (H (s, x)))) (s : S) (y : Y) :
    R y (embeddingExtend e he H (s, y)) := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H]
    exact hlocal s x
  · rw [embeddingExtend_not_mem_range e he H s y hy]
    exact hrefl y

private theorem CuspPositiveRetraction.Supported.embeddingExtend_height_nonincrease {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : X), f (e (H (s, x))) ≤ f (e x)) (s : S) (y : Y) :
    f (embeddingExtend e he H (s, y)) ≤ f y :=
  embeddingExtend_rel e he H (fun y z => f z ≤ f y) (fun _ => le_rfl) hlocal s y

private theorem
    CuspRetraction.Patching.zeroSet_isCompact {X : Type*} [TopologicalSpace X] (f : C(X, ℝ))
    {r : ℝ} (hr : 0 < r) (hc : IsCompact {x : X | f x ≤ r}) : IsCompact {x : X | f x = 0} := by
  apply hc.of_isClosed_subset (isClosed_eq f.continuous continuous_const)
  intro x hx
  change f x ≤ r
  rw [show f x = 0 from hx]
  exact hr.le

public
theorem CuspRetraction.Patching.exists_positive_sublevel_subset_open {X : Type*}
    [TopologicalSpace X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r}) {U : Set X} (hU : IsOpen U) (hS : {x : X | f x = 0} ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ {x : X | f x ≤ η} ⊆ U := by
  have hK : IsCompact (f '' ({x : X | f x ≤ r} \ U)) := (hc.diff hU).image f.continuous
  have hzero : (0 : ℝ) ∈ (f '' ({x : X | f x ≤ r} \ U))ᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx.2 (hS hfx)
  obtain ⟨a, b, hab, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hK.isClosed.isOpen_compl.mem_nhds hzero)
  refine ⟨Min.min r (b / 2), lt_min hr (half_pos hab.2), min_le_left _ _, ?_⟩
  intro x hx
  change f x ≤ Min.min r (b / 2) at hx
  by_contra hxu
  have hfx : f x < b := (hx.trans (min_le_right r (b / 2))).trans_lt (half_lt_self hab.2)
  apply hsub ⟨hab.1.trans_le (hf x), hfx⟩
  exact ⟨x, ⟨hx.trans (min_le_left r (b / 2)), hxu⟩, rfl⟩

private structure CuspRetraction.Patching.LocalCollapse {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) where
  homotopy : C(unitInterval × X, X)
  map_zero : ∀ x, homotopy (0, x) = x
  fixes_zero : ∀ s x, f x = 0 → homotopy (s, x) = x
  nonincreasing : ∀ s x, f (homotopy (s, x)) ≤ f x
  collapseSet : Set X
  isOpen_collapseSet : IsOpen collapseSet
  map_one_zero : ∀ x ∈ collapseSet, f (homotopy (1, x)) = 0

private def CuspRetraction.Patching.LocalCollapse.identity {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : CuspRetraction.Patching.LocalCollapse f
    where
  homotopy := ⟨Prod.snd, continuous_snd⟩
  map_zero _ := rfl
  fixes_zero _ _ _ := rfl
  nonincreasing _ _ := le_rfl
  collapseSet := ∅
  isOpen_collapseSet := isOpen_empty
  map_one_zero _ h := h.elim

private def
    CuspRetraction.Patching.LocalCollapse.comp {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    (A B : CuspRetraction.Patching.LocalCollapse f) : CuspRetraction.Patching.LocalCollapse f
    where
  homotopy :=
    ⟨fun p => B.homotopy (p.1, A.homotopy p),
      B.homotopy.continuous.comp (continuous_fst.prodMk A.homotopy.continuous)⟩
  map_zero
    x := by
    change B.homotopy (0, A.homotopy (0, x)) = x
    rw [A.map_zero, B.map_zero]
  fixes_zero s x
    hx := by
    change B.homotopy (s, A.homotopy (s, x)) = x
    rw [A.fixes_zero s x hx, B.fixes_zero s x hx]
  nonincreasing s x := (B.nonincreasing s (A.homotopy (s, x))).trans (A.nonincreasing s x)
  collapseSet := A.collapseSet ∪ (fun x => A.homotopy (1, x)) ⁻¹' B.collapseSet
  isOpen_collapseSet :=
    A.isOpen_collapseSet.union
      (B.isOpen_collapseSet.preimage
        (A.homotopy.continuous.comp (continuous_const.prodMk continuous_id)))
  map_one_zero x
    hx := by
    change f (B.homotopy (1, A.homotopy (1, x))) = 0
    rcases hx with hx | hx
    · rw [B.fixes_zero 1 _ (A.map_one_zero x hx)]
      exact A.map_one_zero x hx
    · exact B.map_one_zero (A.homotopy (1, x)) hx

private theorem CuspRetraction.Patching.LocalCollapse.mem_comp_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (A B : CuspRetraction.Patching.LocalCollapse f) {x : X}
    (hx : f x = 0) (h : x ∈ A.collapseSet ∪ B.collapseSet) : x ∈ (A.comp B).collapseSet := by
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    change A.homotopy (1, x) ∈ B.collapseSet
    rwa [A.fixes_zero 1 x hx]

private def
    CuspRetraction.Patching.LocalCollapse.combine {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
    {ι : Type*} (A : ι → CuspRetraction.Patching.LocalCollapse f) :
    List ι → CuspRetraction.Patching.LocalCollapse f
  | [] => identity f
  | i :: l => (A i).comp (combine A l)

private theorem CuspRetraction.Patching.LocalCollapse.mem_combine_collapseSet_of_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*}
    (A : ι → CuspRetraction.Patching.LocalCollapse f) (l : List ι) {x : X} (hx : f x = 0) {i : ι}
    (hi : i ∈ l) (hxi : x ∈ (A i).collapseSet) : x ∈ (combine A l).collapseSet := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inl hxi)
    · exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inr (ih hi))

private theorem CuspRetraction.Patching.exists_localCollapse_covering_zero {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} {ι : Type*} (A : ι → LocalCollapse f)
    (hcompact : IsCompact {x : X | f x = 0})
    (hcover : {x : X | f x = 0} ⊆ ⋃ i, (A i).collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  obtain ⟨s, hs⟩ :=
    hcompact.elim_finite_subcover (fun i => (A i).collapseSet) (fun i => (A i).isOpen_collapseSet)
      hcover
  refine ⟨LocalCollapse.combine A s.toList, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact
    LocalCollapse.mem_combine_collapseSet_of_zero A s.toList hx
      (by simpa only [Finset.mem_toList] using hi) hxi

private theorem CuspRetraction.Patching.exists_localCollapse_covering_zero_of_local {X : Type*}
    [TopologicalSpace X] {f : C(X, ℝ)} (hcompact : IsCompact {x : X | f x = 0})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  choose A hA using fun x : { x : X // f x = 0 } => hlocal x x.2
  apply exists_localCollapse_covering_zero A hcompact
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hA ⟨x, hx⟩⟩

private theorem CuspRetraction.Patching.exists_small_sublevel_localCollapse {X : Type*}
    [TopologicalSpace X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ ∃ A : LocalCollapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  obtain ⟨A, hA⟩ := exists_localCollapse_covering_zero_of_local (zeroSet_isCompact f hr hc) hlocal
  obtain ⟨η, hη, hηr, hηA⟩ :=
    exists_positive_sublevel_subset_open f hf hr hc A.isOpen_collapseSet hA
  exact ⟨η, hη, hηr, A, hηA⟩

private theorem CuspPositiveRetraction.exists_localCollapse_of_orthant_chart {X : Type*}
    [TopologicalSpace X] [T2Space X] (f : C(X, ℝ)) (e : OpenPartialHomeomorph Orthant X)
    {r₀ : Orthant} (hr₀ : r₀ ∈ e.source) (hzero : height r₀ = 0)
    (hheight : ∀ r ∈ e.source, f (e r) = height r) :
    ∃ A : CuspRetraction.Patching.LocalCollapse f, e r₀ ∈ A.collapseSet := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp e.open_source r₀ hr₀
  let U := Metric.ball r₀ R
  let : Nonempty U := ⟨⟨r₀, Metric.mem_ball_self hR⟩⟩
  let ep : U → X := fun r => e r.1
  have hep : Topology.IsOpenEmbedding ep := by
    exact
      e.isOpenEmbedding_restrict.comp
        (Topology.IsOpenEmbedding.inclusion hball
          (Metric.isOpen_ball.preimage continuous_subtype_val))
  let H : C(unitInterval × U, U) :=
    ⟨fun p => ⟨localShrink r₀ R p.1 p.2.1, localShrink_map_ball hzero hR p.1 p.2.2⟩,
      ((localShrink_continuous r₀ R).comp
            (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
        _⟩
  let K : Set U := Subtype.val ⁻¹' Metric.closedBall r₀ (R / 3)
  have hK : IsCompact K := by
    apply
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
        (ProperSpace.isCompact_closedBall r₀ (R / 3))
    intro r hr
    have hrU : r ∈ U := by
      change Dist.dist r r₀ < R
      have hd : Dist.dist r r₀ ≤ R / 3 := hr
      linarith
    exact ⟨⟨r, hrU⟩, rfl⟩
  have hfix : ∀ (s : unitInterval) (r : U), r ∉ K → H (s, r) = r := by
    intro s r hr
    exact Subtype.ext (localShrink_eq_self_of_not_mem_closedBall r₀ hR s hr)
  have hH0 : ∀ r : U, H (0, r) = r := by
    intro r
    exact Subtype.ext (localShrink_zero r₀ R r.1)
  have hHfix : ∀ (s : unitInterval) (r : U), f (ep r) = 0 → H (s, r) = r := by
    intro s r hr
    have hz : height r.1 = 0 := (hheight r.1 (hball r.2)).symm.trans hr
    exact Subtype.ext (localShrink_fixed r₀ R s hz)
  have hHle : ∀ (s : unitInterval) (r : U), f (ep (H (s, r))) ≤ f (ep r) := by
    intro s r
    change f (e (H (s, r)).1) ≤ f (e r.1)
    rw [hheight (H (s, r)).1 (hball (H (s, r)).2), hheight r.1 (hball r.2)]
    exact localShrink_height_le r₀ R s r.1
  let L : Set U := Subtype.val ⁻¹' Metric.ball r₀ (R / 4)
  have hL : IsOpen L := Metric.isOpen_ball.preimage continuous_subtype_val
  let A : CuspRetraction.Patching.LocalCollapse f :=
    { homotopy := Supported.embeddingMap ep hep H K hK hfix
      map_zero := Supported.embeddingExtend_id ep hep H 0 hH0
      fixes_zero := fun s x hx =>
        Supported.embeddingExtend_fixed ep hep H {y | f y = 0} hHfix s x hx
      nonincreasing := Supported.embeddingExtend_height_nonincrease ep hep H f hHle
      collapseSet := ep '' L
      isOpen_collapseSet := hep.isOpenMap L hL
      map_one_zero := by
        rintro x ⟨r, hr, rfl⟩
        change f (Supported.embeddingExtend ep hep H (1, ep r)) = 0
        rw [Supported.embeddingExtend_chart]
        change f (e (H (1, r)).1) = 0
        rw [hheight (H (1, r)).1 (hball (H (1, r)).2)]
        exact localShrink_one_height_of_mem_ball r₀ hR hr }
  refine ⟨A, ⟨⟨r₀, Metric.mem_ball_self hR⟩, ?_, rfl⟩⟩
  exact Metric.mem_ball_self (by linarith)

private theorem CuspPositiveRetraction.exists_small_sublevel_collapse_of_orthant_charts {X : Type*}
    [TopologicalSpace X] [T2Space X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact {x : X | f x ≤ r})
    (hcharts :
      ∀ x : X,
        f x = 0 →
          ∃ (e : OpenPartialHomeomorph Orthant X) (r₀ : Orthant),
            r₀ ∈ e.source ∧ e r₀ = x ∧ ∀ r ∈ e.source, f (e r) = height r) :
    ∃ η : ℝ,
      0 < η ∧
        η ≤ r ∧
          ∃ A : CuspRetraction.Patching.LocalCollapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  apply CuspRetraction.Patching.exists_small_sublevel_localCollapse f hf hr hcompact
  intro x hx
  obtain ⟨e, r₀, hr₀, he, hh⟩ := hcharts x hx
  have hzero : height r₀ = 0 := (hh r₀ hr₀).symm.trans (he ▸ hx)
  obtain ⟨A, hA⟩ := exists_localCollapse_of_orthant_chart f e hr₀ hzero hh
  exact ⟨A, he ▸ hA⟩

private def CuspPositiveRetraction.Covering.pullback {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B)) :
    C(unitInterval × E, B) where
  toFun p := H (p.1, q p.2)
  continuous_toFun :=
    H.continuous.comp
      (continuous_fst.prodMk (hq.isLocalHomeomorph.continuous.comp continuous_snd))

private def
    CuspPositiveRetraction.Covering.lift {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B)) (hzero : ∀ b, H (0, b) = b) :
    C(unitInterval × E, E) :=
  hq.liftHomotopy (pullback hq H) (ContinuousMap.id E) (fun x => hzero (q x))

@[simp]
private theorem CuspPositiveRetraction.Covering.lift_zero {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (x : E) :
    CuspPositiveRetraction.Covering.lift hq H hzero (0, x) = x :=
  hq.liftHomotopy_zero _ _ _ x

private theorem CuspPositiveRetraction.Covering.lift_projection {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (s : unitInterval) (x : E) :
    q (CuspPositiveRetraction.Covering.lift hq H hzero (s, x)) = H (s, q x) :=
  congr_fun (hq.liftHomotopy_lifts (pullback hq H) (ContinuousMap.id E) (fun y => hzero (q y)))
    (s, x)

private theorem CuspPositiveRetraction.Covering.lift_fixed {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (x : E) (hx : ∀ s : unitInterval, H (s, q x) = q x)
    (s : unitInterval) : CuspPositiveRetraction.Covering.lift hq H hzero (s, x) = x := by
  have hc :
    Continuous (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) :=
    (CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h := hq.const_of_comp hc (fun t t' => by simp only [lift_projection hq H hzero, hx]) s 0
  exact h.trans (lift_zero hq H hzero x)

private theorem CuspPositiveRetraction.Covering.lift_equivariant {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    (hdeck : ∀ (g : G) (x : E), q (g • x) = q x) (g : G) (s : unitInterval) (x : E) :
    CuspPositiveRetraction.Covering.lift hq H hzero (s, g • x) =
      g • CuspPositiveRetraction.Covering.lift hq H hzero (s, x) := by
  have hleft :
    Continuous
      (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, g • x)) :=
    (CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hright :
    Continuous
      (fun t : unitInterval => g • CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) :=
    (ContinuousConstSMul.continuous_const_smul g).comp
      ((CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
        (continuous_id.prodMk continuous_const))
  have he :
    q ∘ (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, g • x)) =
      q ∘ (fun t : unitInterval => g • CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) := by
    funext t
    simp only [Function.comp_apply, lift_projection hq H hzero, hdeck]
  exact congr_fun (hq.eq_of_comp_eq hleft hright he 0 (by simp only [lift_zero])) s

private theorem CuspPositiveRetraction.Covering.lift_height_le {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (f : B → ℝ) (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (s : unitInterval) (x : E) :
    f (q (CuspPositiveRetraction.Covering.lift hq H hzero (s, x))) ≤ f (q x) := by
  rw [lift_projection hq H hzero]
  exact hsize s (q x)

private def CuspPositiveRetraction.Covering.liftSublevel {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b) :
    C(unitInterval × { x : E // f (q x) ≤ η }, { x : E // f (q x) ≤ η })
    where
  toFun
    p :=
    ⟨CuspPositiveRetraction.Covering.lift hq H hzero (p.1, p.2.1),
      (lift_height_le hq H hzero f hsize p.1 p.2.1).trans p.2.2⟩
  continuous_toFun :=
    ((CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

private def CuspPositive.positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (_t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => Complex.I * ((C₀ i j).im : ℂ)

private theorem
    CuspPositive.positiveTwist_holomorphic (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ContDiff ℂ ω (fun t => positiveTwist C₀ t i j) :=
  contDiff_const

@[simp]
private theorem CuspPositive.driftMatrix_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ToricSpace.driftMatrix (positiveTwist C₀) t = ToricSpace.driftMatrix (fun _ => C₀) 0 := by
  ext i j
  simp [ToricSpace.driftMatrix, positiveTwist, Complex.mul_im]

private theorem CuspPositive.smallDrift_positiveTwist_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    ToricSpace.SmallDrift (positiveTwist C₀) ε ↔ ToricSpace.SmallDrift (fun _ => C₀) ε := by
  simp only [ToricSpace.SmallDrift, driftMatrix_positiveTwist]
  rfl

private theorem CuspPositive.smallDrift_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hR : ToricSpace.SmallDrift (fun _ => C₀) ε) : ToricSpace.SmallDrift (positiveTwist C₀) ε :=
  (smallDrift_positiveTwist_iff C₀ ε).mpr hR

private theorem
    CuspPositive.exponentialMultiplier_positiveTwist_eq_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ) =
      (‖(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ : ℂ) := by
  simp only [ToricSpace.exponentialMultiplier, Units.val_mk0, Complex.norm_exp,
    Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]

private theorem
    CuspPositive.exponentialMultiplier_positiveTwist_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    ‖(ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ =
      ‖(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ := by
  rw [exponentialMultiplier_positiveTwist_eq_norm]
  simp

private theorem CuspPositive.exponentialMultiplier_positiveTwist_ofReal_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (‖(ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ : ℂ) =
      (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ) := by
  rw [exponentialMultiplier_positiveTwist_norm, exponentialMultiplier_positiveTwist_eq_norm]

private theorem
    CuspPositive.fibreMultiplier_positiveTwist_ofReal_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 3) :
    (‖(ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t) i :
            ℂ)‖ :
        ℂ) =
      (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t) i :
        ℂ) := by
  fin_cases i
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 0
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 1
  · simp [ToricSpace.fibreMultiplier]

@[simp]
private theorem CuspPositive.modulus_translate (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.translate v x) =
      ToricSpace.translate v (ToricSpace.modulus x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  simp only [ToricSpace.translate_inclusion, ToricSpace.modulus_inclusion]

private theorem CuspPositive.coordinateModulus_mul {d : ℕ} (z w : ToricCharts.CoordinateSpace d) :
    ToricCharts.coordinateModulus (z * w) =
      ToricCharts.coordinateModulus z * ToricCharts.coordinateModulus w := by
  funext i
  simp [ToricCharts.coordinateModulus]

private theorem CuspPositive.coordinateModulus_factors_of_nonnegative (s : ToricFan.Triangle)
    (u : ToricSpace.ActingTorus) (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) :
    ToricCharts.coordinateModulus (ToricSpace.factors s u) = ToricSpace.factors s u := by
  change ToricCharts.coordinateModulus (ToricCharts.monomial s.dual (fun i => (u i : ℂ))) = _
  rw [← ToricCharts.monomial_coordinateModulus]
  have he : ToricCharts.coordinateModulus (fun i => (u i : ℂ)) = fun i => (u i : ℂ) := by
    funext i
    exact hu i
  rw [he]
  rfl

private theorem CuspPositive.coordinateModulus_scale_of_nonnegative (s : ToricFan.Triangle)
    (u : ToricSpace.ActingTorus) (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ))
    (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateModulus (ToricSpace.scale s u z) =
      ToricSpace.scale s u (ToricCharts.coordinateModulus z) := by
  rw [ToricSpace.scale, coordinateModulus_mul, coordinateModulus_factors_of_nonnegative s u hu]
  rfl

private theorem CuspPositive.modulus_torusAction_of_nonnegative (u : ToricSpace.ActingTorus)
    (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.torusAction u x) =
      ToricSpace.torusAction u (ToricSpace.modulus x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  simp only [ToricSpace.torusAction_inclusion, ToricSpace.modulus_inclusion,
    coordinateModulus_scale_of_nonnegative s u hu]

private theorem CuspPositive.twistedTranslate_positiveTwist_eq (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (positiveTwist C₀) v x =
      ToricSpace.torusAction
        (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) :=
  rfl

private theorem CuspPositive.modulus_twistedTranslate_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.twistedTranslate (positiveTwist C₀) v x) =
      ToricSpace.twistedTranslate (positiveTwist C₀) v (ToricSpace.modulus x) := by
  rw [twistedTranslate_positiveTwist_eq,
    modulus_torusAction_of_nonnegative _ (fibreMultiplier_positiveTwist_ofReal_norm C₀ v 0),
    modulus_translate, twistedTranslate_positiveTwist_eq]

private theorem CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    Set.MapsTo (ToricSpace.twistedTranslate (positiveTwist C₀) v) ToricSpace.positivePart
      ToricSpace.positivePart := by
  intro x hx
  change ToricSpace.modulus (ToricSpace.twistedTranslate (positiveTwist C₀) v x) = _
  rw [modulus_twistedTranslate_positiveTwist]
  exact congrArg (ToricSpace.twistedTranslate (positiveTwist C₀) v) hx

@[simp]
private theorem CuspPositive.twistedTranslate_positiveTwist_mem_positivePart_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (positiveTwist C₀) v x ∈ ToricSpace.positivePart ↔
      x ∈ ToricSpace.positivePart := by
  constructor
  · intro hx
    have h := twistedTranslate_positiveTwist_preserves_positivePart C₀ (-v) hx
    simpa only [ToricSpace.twistedTranslate_add, neg_add_cancel,
      ToricSpace.twistedTranslate_zero] using h
  · intro hx
    exact twistedTranslate_positiveTwist_preserves_positivePart C₀ v hx

private abbrev CuspPositive.LatticeGroup :=
  CuspQuotient.LatticeGroup

private def CuspPositive.positiveTubeSet (ε : ℝ) : Set (ToricSpace.Tube (CuspQuotient.disc ε)) :=
  Subtype.val ⁻¹' ToricSpace.positivePart

private abbrev CuspPositive.PositiveTube (ε : ℝ) :=
  positiveTubeSet ε

private theorem CuspPositive.positiveTubeSet_isClosed (ε : ℝ) : IsClosed (positiveTubeSet ε) :=
  ToricSpace.positivePart_isClosed.preimage continuous_subtype_val

private instance CuspPositive.positiveTube_locallyCompactSpace (ε : ℝ) :
    LocallyCompactSpace (PositiveTube ε) :=
  (positiveTubeSet_isClosed ε).locallyCompactSpace

private def
    CuspPositive.positiveTubeToPositive (ε : ℝ) (x : PositiveTube ε) : ToricSpace.PositivePart :=
  ⟨(x.1 : ToricSpace.Space), x.2⟩

private theorem CuspPositive.positiveTube_norm_time_lt (ε : ℝ) (x : PositiveTube ε) :
    ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ < ε := by
  have hx : ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε := x.1.2
  simpa only [Metric.mem_ball, dist_zero_right] using hx

private def CuspPositive.positiveTubeHomeomorph (ε : ℝ) :
    PositiveTube ε ≃ₜ
      { x : ToricSpace.PositivePart // ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε }
    where
  toFun x := ⟨positiveTubeToPositive ε x, positiveTube_norm_time_lt ε x⟩
  invFun
    x :=
    ⟨⟨(x.1 : ToricSpace.Space),
        by
        change ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2⟩,
      x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

private def
    CuspPositive.positiveTubeTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (v : Fin 2 → ℤ)
    (x : PositiveTube ε) : PositiveTube ε :=
  ⟨ToricSpace.tubeTranslate (positiveTwist C₀) (CuspQuotient.disc ε) v x.1,
    (twistedTranslate_positiveTwist_mem_positivePart_iff C₀ v (x.1 : ToricSpace.Space)).mpr x.2⟩

@[instance_reducible]
private def CuspPositive.positiveAction (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    MulAction LatticeGroup (PositiveTube ε)
    where
  smul g x := positiveTubeTranslate C₀ ε g.toAdd x
  one_smul
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ToricSpace.twistedTranslate_zero (positiveTwist C₀) (x.1 : ToricSpace.Space)
  mul_smul g h
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (ToricSpace.twistedTranslate_add (positiveTwist C₀) g.toAdd h.toAdd
          (x.1 : ToricSpace.Space)).symm

private theorem CuspPositive.positiveAction_compatible (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
    letI := positiveAction C₀ ε
    ∀ (g : LatticeGroup) (x : PositiveTube ε), (g • x).1 = g • x.1 := by
  intros
  rfl

private theorem CuspPositive.positiveAction_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := positiveAction C₀ ε
    ContinuousConstSMul LatticeGroup (PositiveTube ε) := by
  let := positiveAction C₀ ε
  constructor
  intro g
  exact
    ((ToricSpace.tubeTranslate_holomorphic (positiveTwist C₀) (CuspQuotient.disc ε) g.toAdd
              (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn)).continuous.comp
          continuous_subtype_val).subtype_mk
      _

private theorem
    CuspPositive.positiveAction_free (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsCancelSMul LatticeGroup (PositiveTube ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let :=
    CuspQuotient.free_action (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro g h x he
  exact IsCancelSMul.right_cancel g h x.1 (congrArg Subtype.val he)

private theorem
    CuspPositive.positiveAction_properlyDiscontinuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    ProperlyDiscontinuousSMul LatticeGroup (PositiveTube ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let :=
    CuspQuotient.proper_action (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro K L hK hL
  have hf :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := LatticeGroup)
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)
  apply hf.subset
  rintro g ⟨z, ⟨y, hy, rfl⟩, hz⟩
  refine ⟨(g • y).1, ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
  exact ⟨g • y, hz, rfl⟩

private def
    CuspPositive.relation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : Setoid (PositiveTube ε) :=
  let := positiveAction C₀ ε
  MulAction.orbitRel LatticeGroup (PositiveTube ε)

private abbrev CuspPositive.QuotientSpace (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (relation C₀ ε)

private def CuspPositive.project (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    PositiveTube ε → QuotientSpace C₀ ε :=
  Quotient.mk (relation C₀ ε)

private theorem CuspPositive.project_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Function.Surjective (project C₀ ε) :=
  Quotient.mk_surjective

@[simp]
private theorem
    CuspPositive.project_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (v : Fin 2 → ℤ)
    (x : PositiveTube ε) : project C₀ ε (positiveTubeTranslate C₀ ε v x) = project C₀ ε x := by
  let := positiveAction C₀ ε
  exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := Multiplicative.ofAdd v) (a := x)

private theorem CuspPositive.project_covering (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsQuotientCoveringMap (project C₀ ε) LatticeGroup := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_free C₀ ε hε hε1 hR
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

private theorem CuspPositive.quotient_t2Space (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    T2Space (QuotientSpace C₀ ε) := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (PositiveTube ε)))
  infer_instance

private def CuspPositive.quotientInclusion (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    QuotientSpace C₀ ε → CuspQuotient.QuotientSpace (positiveTwist C₀) ε :=
  Quotient.lift (fun x : PositiveTube ε => CuspQuotient.quotientMap (positiveTwist C₀) ε x.1)
    (by
      let := positiveAction C₀ ε
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact CuspQuotient.quotientMap_translate (positiveTwist C₀) ε g.toAdd y.1)

private theorem CuspPositive.quotientInclusion_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientInclusion C₀ ε) :=
  ((CuspQuotient.quotientMap_continuous (positiveTwist C₀) ε).comp
        continuous_subtype_val).quotient_lift
    _

private def
    CuspPositive.height (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : QuotientSpace C₀ ε) : ℝ :=
  ‖CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x)‖

@[simp]
private theorem
    CuspPositive.height_project (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : PositiveTube ε) :
    height C₀ ε (project C₀ ε x) = ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  rfl

private theorem CuspPositive.height_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (height C₀ ε) :=
  ((CuspQuotient.projection_continuous (positiveTwist C₀) ε).comp
      (quotientInclusion_continuous C₀ ε)).norm

private theorem CuspPositive.height_nonneg (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : QuotientSpace C₀ ε) : 0 ≤ height C₀ ε x :=
  norm_nonneg _

private def CuspPositive.positiveImage (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Set (CuspQuotient.QuotientSpace (positiveTwist C₀) ε) :=
  CuspQuotient.quotientMap (positiveTwist C₀) ε '' positiveTubeSet ε

private theorem
    CuspPositive.positiveImage_isClosed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    IsClosed (positiveImage C₀ ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let := positiveAction C₀ ε
  exact
    InvariantSubsetQuotient.isClosed_image
      (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
        (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
      (positiveAction_compatible C₀ ε) (positiveTubeSet_isClosed ε)

private def CuspPositive.quotientHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    QuotientSpace C₀ ε ≃ₜ positiveImage C₀ ε := by
  letI := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  letI := positiveAction C₀ ε
  exact
    InvariantSubsetQuotient.quotientHomeomorph
      (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
        (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
      (positiveAction_compatible C₀ ε)

private theorem
    CuspPositive.quotientHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (x : QuotientSpace C₀ ε) :
    (quotientHomeomorph C₀ ε hε hε1 hR x : CuspQuotient.QuotientSpace (positiveTwist C₀) ε) =
      quotientInclusion C₀ ε x := by
  obtain ⟨y, rfl⟩ := project_surjective C₀ ε x
  rfl

private theorem
    CuspPositive.quotientInclusion_isClosedEmbedding (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    Topology.IsClosedEmbedding (quotientInclusion C₀ ε) := by
  have h :=
    (positiveImage_isClosed C₀ ε hε hε1 hR).isClosedEmbedding_subtypeVal.comp
      (quotientHomeomorph C₀ ε hε hε1 hR).isClosedEmbedding
  have he : Subtype.val ∘ quotientHomeomorph C₀ ε hε hε1 hR = quotientInclusion C₀ ε :=
    funext (quotientHomeomorph_coe C₀ ε hε hε1 hR)
  rw [he] at h
  exact h

private theorem CuspPositive.height_sublevel_isCompact (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) {η : ℝ}
    (hηε : η < ε) : IsCompact {x : QuotientSpace C₀ ε | height C₀ ε x ≤ η} := by
  obtain ⟨τ, hτ, hτε⟩ := exists_between (max_lt hηε hε)
  have hτ0 : 0 < τ := (le_max_right η 0).trans_lt hτ
  have hcompact :=
    CuspQuotient.closedDisc_preimage_compact (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR hτ0 hτε
  have hpre :=
    (quotientInclusion_isClosedEmbedding C₀ ε hε hε1 hR).isProperMap |>.isCompact_preimage
      hcompact
  apply hpre.of_isClosed_subset (isClosed_le (height_continuous C₀ ε) continuous_const)
  intro x hx
  change
    CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x) ∈
      Metric.closedBall 0 τ
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.trans ((le_max_left η 0).trans hτ.le)

private def CuspPositive.orthantComplexHomeomorph :
    CuspPositiveRetraction.Orthant ≃ₜ
      (ToricCharts.nonnegativeCoordinates : Set (ToricCharts.CoordinateSpace 3))
    where
  toFun r := ⟨fun i => (r.1 i : ℂ), ⟨r.1, r.2, rfl⟩⟩
  invFun
    z :=
    ⟨fun i => (z.1 i).re, by
      obtain ⟨r, hr, hz⟩ := z.2
      intro i
      rw [hz]
      exact hr i⟩
  left_inv
    r := by
    apply Subtype.ext
    rfl
  right_inv
    z := by
    apply Subtype.ext
    obtain ⟨r, hr, hz⟩ := z.2
    simp only [hz, Complex.ofReal_re]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_pi fun i =>
        Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      continuous_pi fun i =>
        Complex.continuous_re.comp ((continuous_apply i).comp continuous_subtype_val)

private theorem CuspPositive.inclusion_preimage_positivePart (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' ToricSpace.positivePart =
      (ToricCharts.nonnegativeCoordinates : Set (ToricCharts.CoordinateSpace 3)) := by
  ext z
  exact ToricSpace.inclusion_mem_positivePart_iff s z

private def
    CuspPositive.positiveInclusion (s : ToricFan.Triangle) (r : CuspPositiveRetraction.Orthant) :
    ToricSpace.PositivePart :=
  ⟨ToricSpace.inclusion s (fun i => (r.1 i : ℂ)),
    (ToricSpace.inclusion_mem_positivePart_iff s _).mpr ⟨r.1, r.2, rfl⟩⟩

private theorem CuspPositive.positiveInclusion_openEmbedding (s : ToricFan.Triangle) :
    Topology.IsOpenEmbedding (positiveInclusion s) := by
  let e :
    CuspPositiveRetraction.Orthant ≃ₜ (ToricSpace.inclusion s ⁻¹' ToricSpace.positivePart) :=
    orthantComplexHomeomorph.trans (Homeomorph.setCongr (inclusion_preimage_positivePart s).symm)
  have h :
    Topology.IsOpenEmbedding
      ((ToricSpace.positivePart.restrictPreimage (ToricSpace.inclusion s)) ∘ e) :=
    ((ToricSpace.inclusion_openEmbedding s).restrictPreimage ToricSpace.positivePart).comp
      e.isOpenEmbedding
  have he :
    ((ToricSpace.positivePart.restrictPreimage (ToricSpace.inclusion s)) ∘ e) =
      positiveInclusion s := by
    funext r
    apply Subtype.ext
    rfl
  rwa [he] at h

private def CuspPositive.positiveParametrization (s : ToricFan.Triangle) :
    OpenPartialHomeomorph CuspPositiveRetraction.Orthant ToricSpace.PositivePart := by
  letI : Nonempty CuspPositiveRetraction.Orthant := ⟨⟨fun _ => 0, fun _ => le_rfl⟩⟩
  exact (positiveInclusion_openEmbedding s).toOpenPartialHomeomorph (positiveInclusion s)

@[simp]
private theorem CuspPositive.positiveParametrization_apply (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) : positiveParametrization s r = positiveInclusion s r :=
  rfl

@[simp]
private theorem CuspPositive.positiveParametrization_target (s : ToricFan.Triangle) :
    (positiveParametrization s).target = Set.range (positiveInclusion s) := by
  simp [positiveParametrization]

private theorem CuspPositive.positiveInclusion_positiveParametrization_symm (s : ToricFan.Triangle)
    {x : ToricSpace.PositivePart} (hx : x ∈ Set.range (positiveInclusion s)) :
    positiveInclusion s ((positiveParametrization s).symm x) = x := by
  have h :=
    (positiveParametrization s).right_inv
      (show x ∈ (positiveParametrization s).target by
        simpa only [positiveParametrization_target] using hx)
  simpa only [positiveParametrization_apply] using h

@[simp]
private theorem CuspPositive.time_positiveInclusion (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) :
    ToricSpace.time (positiveInclusion s r : ToricSpace.Space) =
      (CuspPositiveRetraction.height r : ℂ) := by
  simp [positiveInclusion, ToricFan.Triangle.time, CuspPositiveRetraction.height,
    Fin.prod_univ_succ, mul_assoc]

private theorem CuspPositive.norm_time_positiveInclusion (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) :
    ‖ToricSpace.time (positiveInclusion s r : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height r := by
  rw [time_positiveInclusion]
  exact Complex.norm_of_nonneg (CuspPositiveRetraction.height_nonneg r)

private theorem CuspPositive.positiveInclusion_jointly_surjective (x : ToricSpace.PositivePart) :
    ∃ s r, positiveInclusion s r = x := by
  obtain ⟨s, z, hz⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
  have hp : ToricSpace.inclusion s z ∈ ToricSpace.positivePart := hz.symm ▸ x.property
  obtain ⟨r, hr, he⟩ := (ToricSpace.inclusion_mem_positivePart_iff s z).mp hp
  refine ⟨s, ⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  change ToricSpace.inclusion s (fun i => (r i : ℂ)) = (x : ToricSpace.Space)
  rw [← he]
  exact hz

private def
    CuspPositive.positiveOpenTube (ε : ℝ) : TopologicalSpace.Opens ToricSpace.PositivePart :=
  ⟨{x | ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε},
    isOpen_lt (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).norm
      continuous_const⟩

private def
    CuspPositive.positiveTubeOpenHomeomorph (ε : ℝ) : PositiveTube ε ≃ₜ positiveOpenTube ε :=
  positiveTubeHomeomorph ε

private theorem CuspPositive.positiveOpenTube_nonempty (ε : ℝ) (hε : 0 < ε) :
    Nonempty (positiveOpenTube ε) := by
  refine ⟨⟨positiveInclusion ToricSpace.referenceTriangle ⟨0, fun _ => le_rfl⟩, ?_⟩⟩
  change
    ‖ToricSpace.time
          (positiveInclusion ToricSpace.referenceTriangle ⟨0, fun _ => le_rfl⟩ :
            ToricSpace.Space)‖ <
      ε
  rw [norm_time_positiveInclusion]
  simpa [CuspPositiveRetraction.height] using hε

private def CuspPositive.positiveTubeChart (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (PositiveTube ε) CuspPositiveRetraction.Orthant :=
  (positiveTubeOpenHomeomorph ε).toOpenPartialHomeomorph.trans
    ((positiveParametrization s).symm.subtypeRestr (positiveOpenTube_nonempty ε hε))

@[simp]
private theorem CuspPositive.positiveTubeChart_apply (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    (x : PositiveTube ε) :
    positiveTubeChart ε hε s x = (positiveParametrization s).symm (positiveTubeToPositive ε x) :=
  rfl

private theorem CuspPositive.positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    (positiveTubeChart ε hε s).source =
      {x | positiveTubeToPositive ε x ∈ Set.range (positiveInclusion s)} := by
  unfold positiveTubeChart
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.subtypeRestr_source]
  ext x
  change (x ∈ Set.univ ∧ positiveTubeToPositive ε x ∈ (positiveParametrization s).target) ↔ _
  simp only [Set.mem_univ, true_and, positiveParametrization_target, Set.mem_ofPred_eq]

private theorem
    CuspPositive.exists_positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (x : PositiveTube ε) :
    ∃ s : ToricFan.Triangle, x ∈ (positiveTubeChart ε hε s).source := by
  obtain ⟨s, r, hr⟩ := positiveInclusion_jointly_surjective (positiveTubeToPositive ε x)
  refine ⟨s, ?_⟩
  rw [positiveTubeChart_source]
  exact ⟨r, hr⟩

private theorem
    CuspPositive.positiveTubeChart_symm_positive (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {r : CuspPositiveRetraction.Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    positiveTubeToPositive ε ((positiveTubeChart ε hε s).symm r) = positiveInclusion s r := by
  have hx := (positiveTubeChart ε hε s).map_target hr
  rw [positiveTubeChart_source] at hx
  have he := positiveInclusion_positiveParametrization_symm s hx
  have hinv := (positiveTubeChart ε hε s).right_inv hr
  rw [positiveTubeChart_apply] at hinv
  rw [hinv] at he
  exact he.symm

private theorem
    CuspPositive.positiveTubeChart_height_symm (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {r : CuspPositiveRetraction.Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    ‖ToricSpace.time (((positiveTubeChart ε hε s).symm r).1 : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height r := by
  have h :=
    congrArg (fun x : ToricSpace.PositivePart => ‖ToricSpace.time (x : ToricSpace.Space)‖)
      (positiveTubeChart_symm_positive ε hε s hr)
  exact h.trans (norm_time_positiveInclusion s r)

private theorem CuspPositive.positiveTubeChart_height (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {x : PositiveTube ε} (hx : x ∈ (positiveTubeChart ε hε s).source) :
    ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height (positiveTubeChart ε hε s x) := by
  have h := positiveTubeChart_height_symm ε hε s ((positiveTubeChart ε hε s).map_source hx)
  rwa [(positiveTubeChart ε hε s).left_inv hx] at h

private def
    CuspPositive.quotientChart (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (a : PositiveTube ε)
    (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (QuotientSpace C₀ ε) CuspPositiveRetraction.Orthant :=
  letI := positiveAction C₀ ε
  CoveringOrthant.localChart (project_covering C₀ ε hε hε1 hR) (positiveTubeChart ε hε s) a

private theorem
    CuspPositive.quotientChart_mem_source (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (a : PositiveTube ε)
    (s : ToricFan.Triangle) (ha : a ∈ (positiveTubeChart ε hε s).source) :
    project C₀ ε a ∈ (quotientChart C₀ ε hε hε1 hR a s).source := by
  let := positiveAction C₀ ε
  exact
    CoveringOrthant.self_mem_localChart_source (project_covering C₀ ε hε hε1 hR)
      (positiveTubeChart ε hε s) a ha

private theorem CuspPositive.quotientChart_height_symm (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε)
    (a : PositiveTube ε) (s : ToricFan.Triangle) {r : CuspPositiveRetraction.Orthant}
    (hr : r ∈ (quotientChart C₀ ε hε hε1 hR a s).target) :
    height C₀ ε ((quotientChart C₀ ε hε hε1 hR a s).symm r) = CuspPositiveRetraction.height r := by
  let := positiveAction C₀ ε
  apply
    CoveringOrthant.localChart_coordinate_identity (project_covering C₀ ε hε hε1 hR)
      (positiveTubeChart ε hε s) a (height C₀ ε) CuspPositiveRetraction.height ?_ r hr
  intro x hx
  rw [height_project]
  exact positiveTubeChart_height ε hε s hx

private theorem
    CuspPositive.exists_quotientChart (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (x : QuotientSpace C₀ ε) :
    ∃ e : OpenPartialHomeomorph (QuotientSpace C₀ ε) CuspPositiveRetraction.Orthant,
      x ∈ e.source ∧ ∀ r ∈ e.target, height C₀ ε (e.symm r) = CuspPositiveRetraction.height r := by
  obtain ⟨a, ha⟩ := project_surjective C₀ ε x
  obtain ⟨s, hs⟩ := exists_positiveTubeChart_source ε hε a
  refine ⟨quotientChart C₀ ε hε hε1 hR a s, ?_, ?_⟩
  · rw [← ha]
    exact quotientChart_mem_source C₀ ε hε hε1 hR a s hs
  · intro r hr
    exact quotientChart_height_symm C₀ ε hε hε1 hR a s hr

private def CuspPositive.frozenPhaseCoordinate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) : Circle :=
  ⟨(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
      (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ),
    by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, exponentialMultiplier_positiveTwist_norm]
    exact
      div_self
        (norm_ne_zero_iff.mpr (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i).ne_zero)⟩

@[simp]
private theorem
    CuspPositive.frozenPhaseCoordinate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) :
    (frozenPhaseCoordinate C₀ v i : ℂ) =
      (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
        (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ) :=
  rfl

private theorem
    CuspPositive.frozenPhaseCoordinate_eq_exp (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) :
    frozenPhaseCoordinate C₀ v i =
      Circle.exp (2 * Real.pi * ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re) := by
  apply Circle.ext
  simp only [frozenPhaseCoordinate_coe, Circle.coe_exp, ToricSpace.exponentialMultiplier,
    Units.val_mk0, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]

private def CuspPositive.frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    ToricSpace.CompactTorus :=
  ![frozenPhaseCoordinate C₀ v 0, frozenPhaseCoordinate C₀ v 1, 1]

private theorem CuspPositive.compactTorusUnits_frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    ToricSpace.compactTorusUnits (frozenPhase C₀ v) =
      ToricSpace.fibreMultiplier
        (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 /
          ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0) := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [frozenPhase, ToricSpace.fibreMultiplier]

private theorem CuspPositive.frozenMultiplier_phase_positive (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0) =
      ToricSpace.compactTorusUnits (frozenPhase C₀ v) *
        ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0) := by
  rw [compactTorusUnits_frozenPhase, ← ToricSpace.fibreMultiplier_mul, div_mul_cancel]

private theorem
    CuspPositive.twistedTranslate_constant_eq (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => C₀) v x =
      ToricSpace.torusAction
        (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) :=
  rfl

private def CuspPositive.phaseTransform (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (u : ToricSpace.CompactTorus) : ToricSpace.CompactTorus :=
  frozenPhase C₀ v * ToricSpace.phaseShear (ToricSpace.cuspVector v) u

private theorem CuspPositive.twistedTranslate_constant_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => C₀) v (ToricSpace.compactTorusAction u x) =
      ToricSpace.compactTorusAction (phaseTransform C₀ v u)
        (ToricSpace.twistedTranslate (positiveTwist C₀) v x) := by
  rw [twistedTranslate_constant_eq, ToricSpace.translate_compactTorusAction,
    twistedTranslate_positiveTwist_eq]
  simp only [phaseTransform, ToricSpace.compactTorusAction, map_mul, ToricSpace.torusAction_mul]
  rw [frozenMultiplier_phase_positive]
  congr 1
  ac_rfl

private def
    CuspPositive.closedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (v : Fin 2 → ℤ)
    (q : ToricSpace.ClosedPositiveTube η) : ToricSpace.ClosedPositiveTube η :=
  ⟨⟨ToricSpace.twistedTranslate (positiveTwist C₀) v q.1,
      twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by simpa only [ToricSpace.time_twistedTranslate] using q.2⟩

@[simp]
private theorem CuspPositive.closedPositiveTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    ((closedPositiveTranslate C₀ η v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (positiveTwist C₀) v q.1 :=
  rfl

private def CuspPositiveRetraction.quotientHeight (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    C(CuspPositive.QuotientSpace C₀ ε, ℝ) :=
  ⟨CuspPositive.height C₀ ε, CuspPositive.height_continuous C₀ ε⟩

private theorem
    CuspPositiveRetraction.exists_positiveQuotient_collapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η : ℝ,
      0 < η ∧
        η < ε ∧
          ∃ A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε),
            {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet := by
  let := CuspPositive.quotient_t2Space C₀ ε hε hε1 hR
  have hhalf : 0 < ε / 2 := half_pos hε
  have hhalfε : ε / 2 < ε := half_lt_self hε
  obtain ⟨η, hη, hηhalf, A, hA⟩ :=
    exists_small_sublevel_collapse_of_orthant_charts (quotientHeight C₀ ε)
      (CuspPositive.height_nonneg C₀ ε) hhalf
      (CuspPositive.height_sublevel_isCompact C₀ ε hε hε1 hR hhalfε)
      (by
        intro x _hx
        obtain ⟨e, hx, he⟩ := CuspPositive.exists_quotientChart C₀ ε hε hε1 hR x
        refine ⟨e.symm, e x, e.map_source hx, e.left_inv hx, ?_⟩
        exact he)
  exact ⟨η, hη, hηhalf.trans_lt hhalfε, A, hA⟩

private def CuspPositiveRetraction.closedPositiveSublevelHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) {η : ℝ} (hηε : η < ε) :
    ToricSpace.ClosedPositiveTube η ≃ₜ
      { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } := by
  let F :
    ToricSpace.ClosedPositiveTube η →
      { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } :=
    fun x =>
    by
    have hx : ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε
    exact ⟨⟨⟨(x.1 : ToricSpace.Space), hx⟩, x.1.2⟩, x.2⟩
  let G :
    { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } →
      ToricSpace.ClosedPositiveTube η :=
    fun x => ⟨⟨(x.1.1 : ToricSpace.Space), x.1.2⟩, x.2⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        Continuous.subtype_mk
          (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _) _
      continuous_invFun :=
        (((continuous_subtype_val.comp continuous_subtype_val).comp
                  continuous_subtype_val).subtype_mk
              _).subtype_mk
          _ }

private theorem CuspPositiveRetraction.closedPositiveSublevelHomeomorph_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) {η : ℝ} (hηε : η < ε)
    (x : ToricSpace.ClosedPositiveTube η) :
    (((closedPositiveSublevelHomeomorph C₀ ε hηε x).1).1 : ToricSpace.Space) =
      (x.1 : ToricSpace.Space) :=
  rfl

private theorem CuspPositiveRetraction.closedPositiveSublevelHomeomorph_translate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) {η : ℝ} (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : ToricSpace.ClosedPositiveTube η) :
    (closedPositiveSublevelHomeomorph C₀ ε hηε
          (CuspPositive.closedPositiveTranslate C₀ η v x)).1 =
      CuspPositive.positiveTubeTranslate C₀ ε v (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 :=
  rfl

private theorem CuspPositiveRetraction.positiveCovering (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    IsCoveringMap (CuspPositive.project C₀ ε) := by
  let := CuspPositive.positiveAction C₀ ε
  exact (CuspPositive.project_covering C₀ ε hε hε1 hR).isCoveringMap

private def CuspPositiveRetraction.positiveLift (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) :
    C(unitInterval × CuspPositive.PositiveTube ε, CuspPositive.PositiveTube ε) :=
  Covering.lift (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero

@[simp]
private theorem CuspPositiveRetraction.positiveLift_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε))
    (x : CuspPositive.PositiveTube ε) : positiveLift C₀ ε hε hε1 hR A (0, x) = x :=
  Covering.lift_zero (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x

private theorem
    CuspPositiveRetraction.positiveLift_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) :
    CuspPositive.project C₀ ε (positiveLift C₀ ε hε hε1 hR A (s, x)) =
      A.homotopy (s, CuspPositive.project C₀ ε x) :=
  Covering.lift_projection (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero s x

private theorem
    CuspPositiveRetraction.positiveLift_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (v : Fin 2 → ℤ)
    (s : unitInterval) (x : CuspPositive.PositiveTube ε) :
    positiveLift C₀ ε hε hε1 hR A (s, CuspPositive.positiveTubeTranslate C₀ ε v x) =
      CuspPositive.positiveTubeTranslate C₀ ε v (positiveLift C₀ ε hε hε1 hR A (s, x)) := by
  let := CuspPositive.positiveAction C₀ ε
  let := CuspPositive.positiveAction_continuous C₀ ε
  exact
    Covering.lift_equivariant (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
      (fun g x => CuspPositive.project_translate C₀ ε g.toAdd x) (Multiplicative.ofAdd v) s x

private theorem CuspPositiveRetraction.positiveLift_fixed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) (hx : ToricSpace.time (x.1 : ToricSpace.Space) = 0) :
    positiveLift C₀ ε hε hε1 hR A (s, x) = x := by
  apply Covering.lift_fixed (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x
  intro t
  apply A.fixes_zero
  change ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = 0
  simp only [hx, norm_zero]

private theorem
    CuspPositiveRetraction.positiveLift_nonincreasing (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) :
    ‖ToricSpace.time ((positiveLift C₀ ε hε hε1 hR A (s, x)).1 : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  Covering.lift_height_le (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
    (CuspPositive.height C₀ ε) A.nonincreasing s x

private def CuspPositiveRetraction.positiveDeformation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε) :
    C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η) :=
  let e := closedPositiveSublevelHomeomorph C₀ ε hηε
  let L :=
    Covering.liftSublevel (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
      (CuspPositive.height C₀ ε) η A.nonincreasing
  ⟨fun p => e.symm (L (p.1, e p.2)),
    e.symm.continuous.comp
      (L.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩

private theorem
    CuspPositiveRetraction.positiveDeformation_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η) :
    ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : ToricSpace.Space) =
      ((positiveLift C₀ ε hε hε1 hR A (s, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1)).1 :
        ToricSpace.Space) :=
  rfl

@[simp]
private theorem
    CuspPositiveRetraction.positiveDeformation_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (x : ToricSpace.ClosedPositiveTube η) : positiveDeformation C₀ ε hε hε1 hR A hηε (0, x) = x :=
  by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, positiveLift_zero]
  rfl

private theorem
    CuspPositiveRetraction.positiveDeformation_fixed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η)
    (hx : ToricSpace.time (x.1 : ToricSpace.Space) = 0) :
    positiveDeformation C₀ ε hε hε1 hR A hηε (s, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe]
  have hy := (congrArg ToricSpace.time (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)).trans hx
  have he :=
    positiveLift_fixed C₀ ε hε hε1 hR A s (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 hy
  exact
    (congrArg (fun y : CuspPositive.PositiveTube ε => (y.1 : ToricSpace.Space)) he).trans
      (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)

private theorem
    CuspPositiveRetraction.positiveDeformation_nonincreasing (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η) :
    ‖ToricSpace.time ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  positiveLift_nonincreasing C₀ ε hε hε1 hR A s (closedPositiveSublevelHomeomorph C₀ ε hηε x).1

private theorem
    CuspPositiveRetraction.positiveDeformation_one_central (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (hA : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet)
    (x : ToricSpace.ClosedPositiveTube η) :
    ToricSpace.time ((positiveDeformation C₀ ε hε hε1 hR A hηε (1, x)).1 : ToricSpace.Space) =
      0 := by
  apply norm_eq_zero.mp
  rw [positiveDeformation_coe]
  change
    CuspPositive.height C₀ ε
        (CuspPositive.project C₀ ε
          (positiveLift C₀ ε hε hε1 hR A (1, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1))) =
      0
  rw [positiveLift_projection]
  exact A.map_one_zero _ (hA (closedPositiveSublevelHomeomorph C₀ ε hηε x).2)

private theorem
    CuspPositiveRetraction.positiveDeformation_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ToricSpace.ClosedPositiveTube η) :
    positiveDeformation C₀ ε hε hε1 hR A hηε (s, CuspPositive.closedPositiveTranslate C₀ η v x) =
      CuspPositive.closedPositiveTranslate C₀ η v
        (positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, closedPositiveSublevelHomeomorph_translate,
    positiveLift_equivariant, CuspPositive.closedPositiveTranslate_coe, positiveDeformation_coe]
  rfl

private theorem CuspPositiveRetraction.exists_positive_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ η : ℝ,
            0 < η →
              η ≤ η₀ →
                ∃ P :
                  C(unitInterval × ToricSpace.ClosedPositiveTube η,
                    ToricSpace.ClosedPositiveTube η),
                  (∀ q, P (0, q) = q) ∧
                    (∀ s q,
                      ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) ∧
                      (∀ q, ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) ∧
                        (∀ s v q,
                            P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                              CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
                          (∀ s q,
                            ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
                              ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, A, hA⟩ := exists_positiveQuotient_collapse C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η _hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  have hAη : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet := fun _ hx =>
    hA (hx.trans hηη₀)
  refine
    ⟨positiveDeformation C₀ ε hε hε1 hR A hηε, positiveDeformation_zero C₀ ε hε hε1 hR A hηε,
      positiveDeformation_fixed C₀ ε hε hε1 hR A hηε,
      positiveDeformation_one_central C₀ ε hε hε1 hR A hηε hAη,
      positiveDeformation_equivariant C₀ ε hε hε1 hR A hηε,
      positiveDeformation_nonincreasing C₀ ε hε hε1 hR A hηε⟩

private def
    CuspRetraction.closedCompactAction (η : ℝ) (u : ToricSpace.CompactTorus) (x : ClosedTube η) :
    ClosedTube η :=
  ⟨ToricSpace.compactTorusAction u x,
    by
    rw [ToricSpace.norm_time_compactTorusAction]
    exact x.2⟩

private theorem
    CuspRetraction.closedCompactAction_closedPolarMap (η : ℝ) (u v : ToricSpace.CompactTorus)
    (q : ToricSpace.ClosedPositiveTube η) :
    closedCompactAction η u (ToricSpace.closedPolarMap η (v, q)) =
      ToricSpace.closedPolarMap η (u * v, q) :=
  Subtype.ext (ToricSpace.compactTorusAction_mul u v q.1)

private theorem CuspRetraction.positiveHomotopy_polar_compatible {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u v : ToricSpace.CompactTorus) (q r : ToricSpace.ClosedPositiveTube η)
    (h : ToricSpace.closedPolarMap η (u, q) = ToricSpace.closedPolarMap η (v, r)) :
    ToricSpace.closedPolarMap η (u, P (s, q)) = ToricSpace.closedPolarMap η (v, P (s, r)) := by
  have hqr : q = r := by
    apply Subtype.ext
    apply Subtype.ext
    have hm :
      ToricSpace.modulus (ToricSpace.compactTorusAction u q.1) =
        ToricSpace.modulus (ToricSpace.compactTorusAction v r.1) :=
      congrArg (fun x : ClosedTube η => ToricSpace.modulus (x : ToricSpace.Space)) h
    rwa [ToricSpace.modulus_compactTorusAction, ToricSpace.modulus_compactTorusAction, q.1.2,
      r.1.2] at hm
  subst r
  by_cases hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0
  · rw [hfix s q hq]
    exact h
  · have huv : u = v :=
      ToricSpace.compactTorusAction_injective_of_time_ne_zero hq (congrArg Subtype.val h)
    rw [huv]

private def CuspRetraction.polarRepresentative_mo1973_10806 (η : ℝ) (x : ClosedTube η) :
    ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η :=
  (ToricSpace.closedPolarMap_surjective η x).choose

private theorem CuspRetraction.polarRepresentative_spec_mo1973_10807 (η : ℝ) (x : ClosedTube η) :
    ToricSpace.closedPolarMap η (polarRepresentative_mo1973_10806 η x) = x :=
  (ToricSpace.closedPolarMap_surjective η x).choose_spec

private def CuspRetraction.polarSpread {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (s : unitInterval) (x : ClosedTube η) : ClosedTube η :=
  let p := polarRepresentative_mo1973_10806 η x
  ToricSpace.closedPolarMap η (p.1, P (s, p.2))

private theorem CuspRetraction.polarSpread_closedPolarMap {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (p : ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) :
    polarSpread P s (ToricSpace.closedPolarMap η p) =
      ToricSpace.closedPolarMap η (p.1, P (s, p.2)) := by
  change
    ToricSpace.closedPolarMap η
        ((polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).1,
          P (s, (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).2)) =
      _
  exact
    positiveHomotopy_polar_compatible P hfix s
      (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).1 p.1
      (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).2 p.2
      (polarRepresentative_spec_mo1973_10807 η (ToricSpace.closedPolarMap η p))

private theorem CuspRetraction.polarSpread_continuous {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) :
    Continuous (fun p : unitInterval × ClosedTube η => polarSpread P p.1 p.2) := by
  apply (ToricSpace.closedPolarMap_isQuotientMap η).continuous_lift_prod_right
  have h :
    Continuous
      (fun p : unitInterval × (ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) =>
        ToricSpace.closedPolarMap η (p.2.1, P (p.1, p.2.2))) :=
    (ToricSpace.closedPolarMap_continuous η).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (P.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  simpa only [polarSpread_closedPolarMap P hfix] using h

private theorem CuspRetraction.polarSpread_compactTorus_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u : ToricSpace.CompactTorus) (x : ClosedTube η) :
    polarSpread P s (closedCompactAction η u x) = closedCompactAction η u (polarSpread P s x) := by
  obtain ⟨⟨v, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [closedCompactAction_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, closedCompactAction_closedPolarMap]

private theorem CuspRetraction.polarSpread_zero {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hzero : ∀ q : ToricSpace.ClosedPositiveTube η, P (0, q) = q) (x : ClosedTube η) :
    polarSpread P 0 x = x := by
  obtain ⟨p, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix, hzero]

private theorem CuspRetraction.polarSpread_fixed {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (x : ClosedTube η) (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    polarSpread P s x = x := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  have hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0 := by
    have hn := congrArg Norm.norm hx
    change ‖ToricSpace.time (ToricSpace.compactTorusAction u q.1)‖ = ‖(0 : ℂ)‖ at hn
    rw [ToricSpace.norm_time_compactTorusAction, norm_zero] at hn
    exact norm_eq_zero.mp hn
  rw [polarSpread_closedPolarMap P hfix, hfix s q hq]

private theorem CuspRetraction.polarSpread_one_central {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (x : ClosedTube η) : ToricSpace.time (polarSpread P 1 x : ToricSpace.Space) = 0 := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  change ToricSpace.time (ToricSpace.compactTorusAction u ((P (1, q)).1 : ToricSpace.Space)) = 0
  simp only [ToricSpace.compactTorusAction, ToricSpace.time_torusAction, hone q,
    MulZeroClass.mul_zero]

private abbrev CuspRetraction.CentralFibre :=
  { x : ToricSpace.Space // ToricSpace.time x = 0 }

private def
    CuspRetraction.centralIntoClosedTube (η : ℝ) (hη : 0 ≤ η) : C(CentralFibre, ClosedTube η)
    where
  toFun x := ⟨x, by rw [x.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem CuspPositive.closedTranslate_closedPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (q : ToricSpace.ClosedPositiveTube η) :
    CuspRetraction.closedTranslate (fun _ => C₀) η v (ToricSpace.closedPolarMap η (u, q)) =
      ToricSpace.closedPolarMap η (phaseTransform C₀ v u, closedPositiveTranslate C₀ η v q) :=
  Subtype.ext (twistedTranslate_constant_polar C₀ v u q.1)

private theorem
    CuspRetraction.polarSpread_frozen_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η),
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    polarSpread P s (closedTranslate (fun _ => C₀) η v x) =
      closedTranslate (fun _ => C₀) η v (polarSpread P s x) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [CuspPositive.closedTranslate_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, CuspPositive.closedTranslate_closedPolarMap, hequiv]

private theorem CuspRetraction.polarSpread_norm_time_le {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hmono :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (q.1 : ToricSpace.Space)‖)
    (s : unitInterval) (x : ClosedTube η) :
    ‖ToricSpace.time (polarSpread P s x : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x : ToricSpace.Space)‖ := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  simpa only [ToricSpace.closedPolarMap_coe, ToricSpace.norm_time_compactTorusAction] using
    hmono s q

private def CuspRetraction.compactFibrePhase (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) :
    ToricSpace.CompactTorus :=
  ![⟨(u 0 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 0)⟩,
    ⟨(u 1 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 1)⟩, 1]

@[simp]
private theorem CuspRetraction.compactTorusUnits_compactFibrePhase (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) :
    ToricSpace.compactTorusUnits (compactFibrePhase u hu) = ToricSpace.fibreMultiplier u := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [compactFibrePhase, ToricSpace.fibreMultiplier]

@[simp]
private theorem CuspRetraction.closedCompactAction_compactFibrePhase (η : ℝ) (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedCompactAction η (compactFibrePhase u hu) x = closedFibreAction η u x := by
  apply Subtype.ext
  change
    ToricSpace.torusAction (ToricSpace.compactTorusUnits (compactFibrePhase u hu)) x =
      ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x
  rw [compactTorusUnits_compactFibrePhase]

private theorem CuspRetraction.polarSpread_fibre_torus_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    polarSpread P s (closedFibreAction η u x) = closedFibreAction η u (polarSpread P s x) := by
  simpa only [closedCompactAction_compactFibrePhase] using
    polarSpread_compactTorus_equivariant P hfix s (compactFibrePhase u hu) x

private theorem CuspPositiveRetraction.exists_frozen_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ η : ℝ,
            0 < η →
              η ≤ η₀ →
                ∃ H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                  (∀ x, H (0, x) = x) ∧
                    (∀ s (x : CuspRetraction.ClosedTube η),
                        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                      (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                        (∀ s v x,
                            H (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                              CuspRetraction.closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
                          (∀ s u x,
                              H (s, CuspRetraction.closedCompactAction η u x) =
                                CuspRetraction.closedCompactAction η u (H (s, x))) ∧
                            (∀ s (u : Fin 2 → ℂˣ),
                                (∀ i, ‖(u i : ℂ)‖ = 1) →
                                  ∀ x,
                                    H (s, CuspRetraction.closedFibreAction η u x) =
                                      CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                              (∀ s x,
                                ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                  ‖ToricSpace.time (x : ToricSpace.Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ := exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  let H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η) :=
    ⟨fun p => CuspRetraction.polarSpread P p.1 p.2, CuspRetraction.polarSpread_continuous P hfix⟩
  exact
    ⟨H, CuspRetraction.polarSpread_zero P hfix hzero, CuspRetraction.polarSpread_fixed P hfix,
      CuspRetraction.polarSpread_one_central P hfix hone,
      CuspRetraction.polarSpread_frozen_equivariant C₀ P hfix hequiv,
      CuspRetraction.polarSpread_compactTorus_equivariant P hfix,
      CuspRetraction.polarSpread_fibre_torus_equivariant P hfix,
      CuspRetraction.polarSpread_norm_time_le P hfix hmono⟩

private def
    CuspPositiveRetraction.closedFrozenStraightening (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) : CuspRetraction.ClosedTube η ≃ₜ CuspRetraction.ClosedTube η :=
  CuspRetraction.closedTubeHomeomorph C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε

private theorem
    CuspPositiveRetraction.closedFrozenStraightening_base (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x : ToricSpace.Space) =
      ToricSpace.time (x : ToricSpace.Space) :=
  CuspRetraction.closedTubeHomeomorph_base C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε x

private theorem CuspPositiveRetraction.closedFrozenStraightening_symm_base
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x : ToricSpace.Space) =
      ToricSpace.time (x : ToricSpace.Space) := by
  have h :=
    closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε
      (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x)
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply] at h
  exact h.symm

private theorem
    CuspPositiveRetraction.closedFrozenStraightening_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x = x :=
  CuspRetraction.closedTubeHomeomorph_fixes_central C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε x hx

private theorem CuspPositiveRetraction.closedFrozenStraightening_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) (CuspRetraction.closedTranslate C η v x) =
      CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v
        ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) :=
  CuspRetraction.closedTubeHomeomorph_equivariant C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε v x

private theorem CuspPositiveRetraction.closedFrozenStraightening_symm_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v x) =
      CuspRetraction.closedTranslate C η v
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x) := by
  apply ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).injective
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply,
    closedFrozenStraightening_equivariant,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply]

private theorem CuspPositiveRetraction.closedFrozenStraightening_fibre_torus
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : CuspRetraction.ClosedTube η) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) (CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) :=
  CuspRetraction.closedTubeHomeomorph_fibre_torus C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε u hu x

private theorem CuspPositiveRetraction.closedFrozenStraightening_symm_fibre_torus
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : CuspRetraction.ClosedTube η) :
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x) := by
  apply ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).injective
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply,
    closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply]

private def CuspPositiveRetraction.straightenedHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε)
    (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η)) :
    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η)
    where
  toFun
    p :=
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
      (H (p.1, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) p.2))
  continuous_toFun :=
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm.continuous.comp
      (H.continuous.comp
        (continuous_fst.prodMk
          (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).continuous.comp continuous_snd)))

@[simp]
private theorem CuspPositiveRetraction.straightenedHomotopy_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) =
      ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (H (s, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)) :=
  rfl

private theorem CuspPositiveRetraction.straightenedHomotopy_time (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : ToricSpace.Space) =
      ToricSpace.time
        (H (s, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) : ToricSpace.Space) :=
  closedFrozenStraightening_symm_base C hε hε1 hC hRC hRD hηε _

private theorem CuspPositiveRetraction.straightenedHomotopy_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hzero : ∀ x : CuspRetraction.ClosedTube η, H (0, x) = x) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (0, x) = x := by
  rw [straightenedHomotopy_apply, hzero,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm_apply_apply]

private theorem CuspPositiveRetraction.straightenedHomotopy_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hfixed :
      ∀ (s : unitInterval) (x : CuspRetraction.ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (s : unitInterval) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) = x := by
  have hGx :
    ToricSpace.time ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x : ToricSpace.Space) =
      0 :=
    (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x).trans hx
  rw [straightenedHomotopy_apply,
    hfixed s ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) hGx,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm_apply_apply]

private theorem
    CuspPositiveRetraction.straightenedHomotopy_one_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hone : ∀ x : CuspRetraction.ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x) : ToricSpace.Space) =
      0 := by
  rw [straightenedHomotopy_time]
  exact hone ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)

private theorem CuspPositiveRetraction.straightenedHomotopy_norm_time_le
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hnorm :
      ∀ (s : unitInterval) (x : CuspRetraction.ClosedTube η),
        ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (x : ToricSpace.Space)‖)
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    ‖ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x : ToricSpace.Space)‖ := by
  rw [straightenedHomotopy_time]
  exact
    (hnorm s ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)).trans_eq
      (congrArg Norm.norm (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x))

private theorem
    CuspPositiveRetraction.straightenedHomotopy_equivariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η),
        H (s, CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v x) =
          CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v (H (s, x)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, CuspRetraction.closedTranslate C η v x) =
      CuspRetraction.closedTranslate C η v
        (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply, closedFrozenStraightening_equivariant, hequiv,
    closedFrozenStraightening_symm_equivariant]

private theorem CuspPositiveRetraction.straightenedHomotopy_fibre_torus_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hequiv :
      ∀ (s : unitInterval) (u : Fin 2 → ℂˣ),
        (∀ i, ‖(u i : ℂ)‖ = 1) →
          ∀ x : CuspRetraction.ClosedTube η,
            H (s, CuspRetraction.closedFibreAction η u x) =
              CuspRetraction.closedFibreAction η u (H (s, x)))
    (s : unitInterval) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply,
    closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu, hequiv s u hu,
    closedFrozenStraightening_symm_fibre_torus C hε hε1 hC hRC hRD hηε u hu]

private noncomputable def CuspRetraction.descentRepresentative_mo1973_10849
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) (q : ClosedQuotient C ε η) :
    ClosedTube η :=
  (closedQuotientMap_surjective C hηε q).choose

private theorem CuspRetraction.descentRepresentative_spec_mo1973_10850
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) (q : ClosedQuotient C ε η) :
    closedQuotientMap C hηε (descentRepresentative_mo1973_10849 C hηε q) = q :=
  (closedQuotientMap_surjective C hηε q).choose_spec

private noncomputable def CuspRetraction.closedHomotopyDescent (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η)) (s : unitInterval)
    (q : ClosedQuotient C ε η) : ClosedQuotient C ε η :=
  closedQuotientMap C hηε (H (s, descentRepresentative_mo1973_10849 C hηε q))

private theorem CuspRetraction.closedHomotopyDescent_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (s : unitInterval) (x y : ClosedTube η)
    (hxy : closedQuotientMap C hηε x = closedQuotientMap C hηε y) :
    closedQuotientMap C hηε (H (s, x)) = closedQuotientMap C hηε (H (s, y)) := by
  obtain ⟨v, hv⟩ := (closedQuotientMap_eq_iff C hηε x y).mp hxy
  have hv' : closedTranslate C η v y = x := Subtype.ext hv
  apply (closedQuotientMap_eq_iff C hηε _ _).mpr
  refine ⟨v, ?_⟩
  have he := hH s v y
  rw [hv'] at he
  exact (congrArg Subtype.val he).symm

private theorem
    CuspRetraction.closedHomotopyDescent_closedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (s : unitInterval) (x : ClosedTube η) :
    closedHomotopyDescent C hηε H s (closedQuotientMap C hηε x) =
      closedQuotientMap C hηε (H (s, x)) :=
  closedHomotopyDescent_compatible C hηε H hH s _ _
    (descentRepresentative_spec_mo1973_10850 C hηε (closedQuotientMap C hηε x))

private theorem CuspRetraction.closedHomotopyDescent_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : unitInterval × ClosedQuotient C ε η => closedHomotopyDescent C hηε H p.1 p.2) := by
  have hq := closedQuotientMap_isOpenQuotientMap C hηε hC
  have hprod :
    IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) (closedQuotientMap C hηε)) :=
    IsOpenQuotientMap.id.prodMap hq
  apply hprod.continuous_comp_iff.mp
  change
    Continuous
      (fun p : unitInterval × ClosedTube η =>
        closedHomotopyDescent C hηε H p.1 (closedQuotientMap C hηε p.2))
  simpa only [closedHomotopyDescent_closedQuotientMap C hηε H hH, Prod.mk.eta,
    Function.comp_def] using hq.continuous.comp H.continuous

private theorem
    CuspRetraction.closedHomotopyDescent_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hzero : ∀ x : ClosedTube η, H (0, x) = x) (q : ClosedQuotient C ε η) :
    closedHomotopyDescent C hηε H 0 q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hzero]

private theorem
    CuspRetraction.closedHomotopyDescent_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (s : unitInterval) (q : ClosedQuotient C ε η) (hq : CuspQuotient.projection C ε q = 0) :
    closedHomotopyDescent C hηε H s q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hfix s x hq]

private theorem CuspRetraction.closedHomotopyDescent_one_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (q : ClosedQuotient C ε η) :
    CuspQuotient.projection C ε (closedHomotopyDescent C hηε H 1 q) = 0 := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, closedQuotientMap_projection, hone]

private theorem
    CuspRetraction.closedHomotopyDescent_norm_nonincrease (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hmono :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (x : ToricSpace.Space)‖)
    (s : unitInterval) (q : ClosedQuotient C ε η) :
    ‖CuspQuotient.projection C ε (closedHomotopyDescent C hηε H s q)‖ ≤
      ‖CuspQuotient.projection C ε q‖ := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, closedQuotientMap_projection,
    closedQuotientMap_projection]
  exact hmono s x

private abbrev CuspRetraction.QuotientCentralFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  { q : CuspQuotient.QuotientSpace C ε // CuspQuotient.projection C ε q = 0 }

private def CuspRetraction.quotientCentralIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ)
    (hη : 0 ≤ η) : C(QuotientCentralFibre C ε, ClosedQuotient C ε η)
    where
  toFun q := ⟨q, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private noncomputable def CuspRetraction.closedHomotopyDescentRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) :
    C(ClosedQuotient C ε η, QuotientCentralFibre C ε)
    where
  toFun
    q := ⟨closedHomotopyDescent C hηε H 1 q, closedHomotopyDescent_one_central C hηε H hH hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((closedHomotopyDescent_continuous C hηε H hH hC).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

private theorem CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) (hη : 0 ≤ η) :
    (closedHomotopyDescentRetraction C hηε H hH hC hone).comp
        (quotientCentralIntoClosed C ε η hη) =
      ContinuousMap.id (QuotientCentralFibre C ε) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change
    (closedHomotopyDescent C hηε H 1 (quotientCentralIntoClosed C ε η hη q) :
        CuspQuotient.QuotientSpace C ε) =
      (q : CuspQuotient.QuotientSpace C ε)
  exact
    congrArg Subtype.val
      (closedHomotopyDescent_fixed C hηε H hH hfix 1 (quotientCentralIntoClosed C ε η hη q) q.2)

private noncomputable def CuspRetraction.closedHomotopyDescentHomotopyRel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hzero : ∀ x : ClosedTube η, H (0, x) = x)
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) (hη : 0 ≤ η) :
    (ContinuousMap.id (ClosedQuotient C ε η)).HomotopyRel
      ((quotientCentralIntoClosed C ε η hη).comp
        (closedHomotopyDescentRetraction C hηε H hH hC hone))
      {q : ClosedQuotient C ε η | CuspQuotient.projection C ε q = 0}
    where
  toFun p := closedHomotopyDescent C hηε H p.1 p.2
  continuous_toFun := closedHomotopyDescent_continuous C hηε H hH hC
  map_zero_left := closedHomotopyDescent_zero C hηε H hH hzero
  map_one_left _ := rfl
  prop' s q hq := closedHomotopyDescent_fixed C hηε H hH hfix s q hq

private theorem
    CuspPositiveRetraction.exists_closed_tube_deformation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r : ℝ} (hr : 0 < r) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ η : ℝ,
              0 < η →
                η ≤ η₀ →
                  ∃ H :
                    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                    (∀ x, H (0, x) = x) ∧
                      (∀ s (x : CuspRetraction.ClosedTube η),
                          ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                        (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                          (∀ s v x,
                              H (s, CuspRetraction.closedTranslate C η v x) =
                                CuspRetraction.closedTranslate C η v (H (s, x))) ∧
                            (∀ s (u : Fin 2 → ℂˣ),
                                (∀ i, ‖(u i : ℂ)‖ = 1) →
                                  ∀ x,
                                    H (s, CuspRetraction.closedFibreAction η u x) =
                                      CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                              (∀ s x,
                                ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                  ‖ToricSpace.time (x : ToricSpace.Space)‖) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := CuspRetraction.exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : ToricSpace.SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ := exists_frozen_closed_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono⟩ := hH η hη hηη₀
  refine
    ⟨straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
      straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
      straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
      straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
      straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
      straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε H hfibre,
      straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono⟩

private theorem CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∃ R :
                  C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r),
                  R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                      ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                    ∃ H :
                      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                        ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                        {q : CuspRetraction.ClosedQuotient C r η |
                          CuspQuotient.projection C r q = 0},
                      ∀ s q,
                        ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                          ‖CuspQuotient.projection C r q‖ := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono⟩ := hH η hη hηη₀
  refine
    ⟨CuspRetraction.closedHomotopyDescentRetraction C hηr H hequiv hC hone,
      CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone
        hη.le,
      CuspRetraction.closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le, ?_⟩
  exact CuspRetraction.closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono

private def CuspCentralHomology.centralIntoOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδ : 0 < δ) : C(CuspRetraction.QuotientCentralFibre C r, OpenQuotient C r δ)
    where
  toFun
    q :=
    ⟨q.1, by
      rw [q.2, norm_zero]
      exact hδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private def CuspCentralHomology.openIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδη : δ ≤ η) : C(OpenQuotient C r δ, CuspRetraction.ClosedQuotient C r η)
    where
  toFun q := ⟨q, q.2.le.trans hδη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def
    CuspCentralHomology.restrictClosedRetraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r)) :
    C(OpenQuotient C r δ, CuspRetraction.QuotientCentralFibre C r) :=
  R.comp (openIntoClosed C r δ η hδη)

private theorem CuspCentralHomology.restrictClosedRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ) (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hR :
      R.comp (CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r)) :
    (restrictClosedRetraction C r δ η hδη R).comp (centralIntoOpen C r δ hδ) =
      ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) := by
  apply ContinuousMap.ext
  intro q
  exact ContinuousMap.congr_fun hR q

private def
    CuspCentralHomology.restrictClosedHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
        ((CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
        {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = 0})
    (hmono : ∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤ ‖CuspQuotient.projection C r q‖) :
    (ContinuousMap.id (OpenQuotient C r δ)).HomotopyRel
      ((centralIntoOpen C r δ hδ).comp (restrictClosedRetraction C r δ η hδη R))
      {q : OpenQuotient C r δ | CuspQuotient.projection C r q = 0}
    where
  toFun
    p :=
    ⟨H (p.1, openIntoClosed C r δ η hδη p.2),
      (hmono p.1 (openIntoClosed C r δ η hδη p.2)).trans_lt p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_subtype_val.comp
        (H.continuous.comp
          (continuous_fst.prodMk ((openIntoClosed C r δ η hδη).continuous.comp continuous_snd)))
  map_zero_left
    q := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.map_zero_left (openIntoClosed C r δ η hδη q))
  map_one_left
    q := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.map_one_left (openIntoClosed C r δ η hδη q))
  prop' s q
    hq := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.eq_fst s (show CuspQuotient.projection C r (openIntoClosed C r δ η hδη q) = 0 from hq))

private def
    CuspCentralHomology.openCentralHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hR :
      R.comp (CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
        ((CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
        {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = 0})
    (hmono : ∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤ ‖CuspQuotient.projection C r q‖) :
    CuspRetraction.QuotientCentralFibre C r ≃ₕ OpenQuotient C r δ
    where
  toFun := centralIntoOpen C r δ hδ
  invFun := restrictClosedRetraction C r δ η hδη R
  left_inv := by rw [restrictClosedRetraction_comp_inclusion C r δ η hδ hδη R hR]
  right_inv := ⟨(restrictClosedHomotopy C r δ η hδ hδη R H hmono).toHomotopy.symm⟩

private def
    CuspCentralHomology.centralIntoSmallerQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδ : 0 < δ) (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    C(CuspRetraction.QuotientCentralFibre C r, CuspQuotient.QuotientSpace C δ) :=
  ((openQuotientRadiusHomeomorph C hδr hC).symm :
        C(OpenQuotient C r δ, CuspQuotient.QuotientSpace C δ)).comp
    (centralIntoOpen C r δ hδ)

private theorem
    CuspCentralHomology.exists_centralHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ δ₀ : ℝ,
      0 < δ₀ ∧
        δ₀ < r ∧
          δ₀ < 1 ∧
            ∀ (δ : ℝ) (hδ : 0 < δ),
              δ ≤ δ₀ →
                ∀ hδr : δ ≤ r,
                  ∃ e : CuspRetraction.QuotientCentralFibre C r ≃ₕ CuspQuotient.QuotientSpace C δ,
                    e.toFun = centralIntoSmallerQuotient C r δ hδ hδr hC := by
  obtain ⟨δ₀, hδ₀, hδ₀r, hδ₀1, hex⟩ :=
    CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction C hr hC
  refine ⟨δ₀, hδ₀, hδ₀r, hδ₀1, ?_⟩
  intro δ hδ hδδ₀ hδr
  obtain ⟨R, hR, H, hmono⟩ := hex δ₀ hδ₀ le_rfl
  let e := openCentralHomotopyEquiv C r δ δ₀ hδ hδδ₀ R hR H hmono
  refine ⟨e.trans (openQuotientRadiusHomeomorph C hδr hC).symm.toHomotopyEquiv, rfl⟩

private abbrev CuspPositiveRetraction.PositiveCentralFibre :=
  { q : ToricSpace.PositivePart // ToricSpace.time (q : ToricSpace.Space) = 0 }

private def CuspPositiveRetraction.positiveCentralInclusion (η : ℝ) (hη : 0 ≤ η) :
    C(PositiveCentralFibre, ToricSpace.ClosedPositiveTube η)
    where
  toFun q := ⟨q.1, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem CuspCollapse.exists_compactFibreAction_modulus {x : ToricSpace.Space}
    (hx : ToricSpace.time x = 0) :
    ∃ u : ToricSpace.CompactFibreTorus,
      ToricSpace.compactFibreAction u (ToricSpace.modulus x) = x := by
  obtain ⟨u, hu⟩ := ToricSpace.exists_compactTorusAction_modulus x
  have hzero : ToricSpace.time (ToricSpace.modulus x) = 0 := by
    simp only [ToricSpace.time_modulus, hx, norm_zero, Complex.ofReal_zero]
  obtain ⟨v, hv⟩ := (ToricSpace.branchVertices_nonempty (ToricSpace.modulus x)).mpr hzero
  let w : ToricSpace.CompactTorus := u * ToricSpace.rayCompactPhase v (u 2)⁻¹
  have hw : w 2 = 1 := by
    simp only [w, Pi.mul_apply, ToricSpace.rayCompactPhase_two, mul_inv_cancel]
  let uf : ToricSpace.CompactFibreTorus := ![w 0, w 1]
  have hf : ToricSpace.compactFibrePhase uf = w := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hw.symm
  refine ⟨uf, ?_⟩
  rw [ToricSpace.compactFibreAction_eq_compact, hf]
  change
    ToricSpace.compactTorusAction (u * ToricSpace.rayCompactPhase v (u 2)⁻¹)
        (ToricSpace.modulus x) =
      x
  rw [← ToricSpace.compactTorusAction_mul,
    ToricSpace.rayCompactPhase_fixes_of_mem_rayDivisor v (u 2)⁻¹ hv]
  exact hu

private theorem CuspCollapse.positiveCentral_isClosed :
    IsClosed {q : ToricSpace.PositivePart | ToricSpace.time (q : ToricSpace.Space) = 0} :=
  isClosed_eq (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
    continuous_const

private theorem CuspCollapse.positiveCentralVal_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (fun q : CuspPositiveRetraction.PositiveCentralFibre => (q.1 : ToricSpace.Space)) :=
  ToricSpace.positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    positiveCentral_isClosed.isClosedEmbedding_subtypeVal

private def CuspCollapse.centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space), by
    rw [ToricSpace.time_compactFibreAction, p.2.2]⟩

@[simp]
private theorem CuspCollapse.centralPolarMap_coe
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    (centralPolarMap p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space) :=
  rfl

private theorem CuspCollapse.centralPolarMap_continuous : Continuous centralPolarMap :=
  (ToricSpace.compactFibreAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

private theorem CuspCollapse.modulus_centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    ToricSpace.modulus (centralPolarMap p : ToricSpace.Space) = (p.2.1 : ToricSpace.Space) := by
  rw [centralPolarMap_coe, ToricSpace.modulus_compactFibreAction]
  exact p.2.1.2

private def CuspCollapse.centralModulus (x : CuspRetraction.CentralFibre) :
    CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨ToricSpace.modulusRetraction x, by
    simp only [ToricSpace.modulusRetraction_coe, ToricSpace.time_modulus, x.2, norm_zero,
      Complex.ofReal_zero]⟩

@[simp]
private theorem CuspCollapse.centralModulus_centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    centralModulus (centralPolarMap p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_centralPolarMap p))

private theorem CuspCollapse.centralPolarMap_surjective : Function.Surjective centralPolarMap := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus x.2
  exact ⟨(u, centralModulus x), Subtype.ext hu⟩

private theorem CuspCollapse.centralPolarMap_isProperMap : IsProperMap centralPolarMap := by
  have hinc :
    IsProperMap
      (fun p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre =>
        (p.1, (p.2.1 : ToricSpace.Space))) :=
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).isClosedEmbedding.prodMap
        positiveCentralVal_isClosedEmbedding).isProperMap
  have hcomp :
    IsProperMap
      ((Subtype.val : CuspRetraction.CentralFibre → ToricSpace.Space) ∘ centralPolarMap) :=
    ToricSpace.compactFibreAction_isProperMap.comp hinc
  exact
    isProperMap_of_comp_of_inj centralPolarMap_continuous continuous_subtype_val hcomp
      Subtype.val_injective

private theorem CuspCollapse.centralPolarMap_isClosedMap : IsClosedMap centralPolarMap :=
  centralPolarMap_isProperMap.isClosedMap

private theorem
    CuspCollapse.centralPolarMap_isQuotientMap : Topology.IsQuotientMap centralPolarMap :=
  centralPolarMap_isClosedMap.isQuotientMap centralPolarMap_continuous centralPolarMap_surjective

private theorem CuspCollapse.centralPolarMap_eq_iff
    (p q : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    centralPolarMap p = centralPolarMap q ↔
      p.2 = q.2 ∧
        p.1⁻¹ * q.1 ∈
          MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space) := by
  rcases p with ⟨u, x⟩
  rcases q with ⟨v, y⟩
  constructor
  · intro h
    have hxy : x = y := by
      simpa only [centralModulus_centralPolarMap] using congrArg centralModulus h
    subst y
    refine ⟨rfl, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    have he : u • (x.1 : ToricSpace.Space) = v • (x.1 : ToricSpace.Space) :=
      congrArg Subtype.val h
    rw [SemigroupAction.mul_smul, ← he, inv_smul_smul]
  · rintro ⟨hxy, h⟩
    change x = y at hxy
    subst y
    have hs := congrArg (fun z : ToricSpace.Space => u • z) (MulAction.mem_stabilizer_iff.mp h)
    apply Subtype.ext
    change u • (x.1 : ToricSpace.Space) = v • (x.1 : ToricSpace.Space)
    simpa only [smul_smul, mul_inv_cancel_left] using hs.symm

private def CuspCollapse.deckFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    ToricSpace.CompactFibreTorus := fun i => CuspPositive.frozenPhaseCoordinate C₀ v i

@[simp]
private theorem CuspCollapse.deckFibrePhase_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    deckFibrePhase C₀ 0 = 1 := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe,
    ToricSpace.exponentialMultiplier_zero, Pi.one_apply, Units.val_one, one_div, inv_one,
    Circle.coe_one]

private theorem CuspCollapse.deckFibrePhase_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ) :
    deckFibrePhase C₀ (v + w) = deckFibrePhase C₀ v * deckFibrePhase C₀ w := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe, Pi.mul_apply, Circle.coe_mul]
  rw [ToricSpace.exponentialMultiplier_add, ToricSpace.exponentialMultiplier_add]
  simp only [Pi.mul_apply, Units.val_mul, div_mul_div_comm]

private theorem CuspCollapse.phaseTransform_compactFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactFibreTorus) :
    CuspPositive.phaseTransform C₀ v (ToricSpace.compactFibrePhase u) =
      ToricSpace.compactFibrePhase (deckFibrePhase C₀ v * u) := by
  funext i
  fin_cases i <;>
    simp [CuspPositive.phaseTransform, CuspPositive.frozenPhase, ToricSpace.phaseShear,
      ToricSpace.compactFibrePhase, deckFibrePhase]

private def CuspCollapse.positiveCentralTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space),
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [ToricSpace.time_twistedTranslate, q.2]⟩

@[simp]
private theorem
    CuspCollapse.positiveCentralTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    ((positiveCentralTranslate C₀ v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space) :=
  rfl

@[simp]
private theorem CuspCollapse.positiveCentralTranslate_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) : positiveCentralTranslate C₀ 0 q = q :=
  Subtype.ext (Subtype.ext (ToricSpace.twistedTranslate_zero (CuspPositive.positiveTwist C₀) q.1))

private theorem CuspCollapse.positiveCentralTranslate_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (q : CuspPositiveRetraction.PositiveCentralFibre) :
    positiveCentralTranslate C₀ v (positiveCentralTranslate C₀ w q) =
      positiveCentralTranslate C₀ (v + w) q :=
  Subtype.ext
    (Subtype.ext (ToricSpace.twistedTranslate_add (CuspPositive.positiveTwist C₀) v w q.1))

private theorem CuspCollapse.positiveCentralTranslate_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : Continuous (positiveCentralTranslate C₀ v) :=
  (((ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀) v).continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
        _).subtype_mk
    _

private def CuspCollapse.positiveCentralHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    CuspPositiveRetraction.PositiveCentralFibre ≃ₜ CuspPositiveRetraction.PositiveCentralFibre
    where
  toFun := positiveCentralTranslate C₀ v
  invFun := positiveCentralTranslate C₀ (-v)
  left_inv
    q := by rw [positiveCentralTranslate_add, neg_add_cancel, positiveCentralTranslate_zero]
  right_inv
    q := by rw [positiveCentralTranslate_add, add_neg_cancel, positiveCentralTranslate_zero]
  continuous_toFun := positiveCentralTranslate_continuous C₀ v
  continuous_invFun := positiveCentralTranslate_continuous C₀ (-v)

private def CuspCollapse.phaseDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre :=
  (deckFibrePhase C₀ v * p.1, positiveCentralTranslate C₀ v p.2)

private theorem CuspCollapse.twistedTranslate_central_eq_constant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ToricSpace.twistedTranslate C v x = ToricSpace.twistedTranslate (fun _ => C 0) v x := by
  simp only [ToricSpace.twistedTranslate, ToricSpace.variableMultiplier,
    ToricSpace.time_translate, hx]
  rfl

private theorem CuspCollapse.centralPolarMap_phaseDeckMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ)
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    (centralPolarMap (phaseDeckMap (C 0) v p) : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (centralPolarMap p : ToricSpace.Space) := by
  rw [twistedTranslate_central_eq_constant C v (centralPolarMap p).2]
  change
    ToricSpace.compactFibreAction (deckFibrePhase (C 0) v * p.1)
        ((positiveCentralTranslate (C 0) v p.2).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C 0) v
        (ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space))
  rw [ToricSpace.compactFibreAction_eq_compact, ToricSpace.compactFibreAction_eq_compact,
    CuspPositive.twistedTranslate_constant_polar, phaseTransform_compactFibrePhase]
  rfl

private noncomputable def CuspCollapse.centralClosedZeroHomeomorph :
    CuspRetraction.CentralFibre ≃ₜ CuspRetraction.ClosedTube 0 :=
  Homeomorph.setCongr
    (by
      ext x
      exact norm_le_zero_iff.symm)

private noncomputable def CuspCollapse.quotientCentralClosedZeroHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    CuspRetraction.QuotientCentralFibre C ε ≃ₜ CuspRetraction.ClosedQuotient C ε 0 :=
  Homeomorph.setCongr
    (by
      ext q
      exact norm_le_zero_iff.symm)

private noncomputable def CuspCollapse.centralProject (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (x : CuspRetraction.CentralFibre) : CuspRetraction.QuotientCentralFibre C ε :=
  ⟨CuspQuotient.quotientMap C ε
      ⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        rw [x.2]
        simpa only [Metric.mem_ball, dist_self] using hε⟩,
    x.2⟩

private theorem CuspCollapse.centralProject_eq_comp (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    centralProject C ε hε =
      (quotientCentralClosedZeroHomeomorph C ε).symm ∘
        (CuspRetraction.closedQuotientMap C hε ∘ centralClosedZeroHomeomorph) :=
  rfl

private theorem CuspCollapse.centralProject_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (centralProject C ε hε) := by
  apply Continuous.subtype_mk
  exact (CuspQuotient.quotientMap_continuous C ε).comp (continuous_subtype_val.subtype_mk _)

private theorem CuspCollapse.centralProject_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact
    (quotientCentralClosedZeroHomeomorph C ε).symm.surjective.comp
      ((CuspRetraction.closedQuotientMap_surjective C hε).comp
        centralClosedZeroHomeomorph.surjective)

private theorem
    CuspCollapse.centralProject_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact
    (quotientCentralClosedZeroHomeomorph C ε).symm.isOpenQuotientMap.comp
      ((CuspRetraction.closedQuotientMap_isOpenQuotientMap C hε hC).comp
        centralClosedZeroHomeomorph.isOpenQuotientMap)

private theorem CuspCollapse.centralProject_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (centralProject C ε hε) :=
  (centralProject_isOpenQuotientMap C ε hε hC).isQuotientMap

private theorem
    CuspCollapse.centralProject_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (x y : CuspRetraction.CentralFibre) :
    centralProject C ε hε x = centralProject C ε hε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  rw [← (quotientCentralClosedZeroHomeomorph C ε).injective.eq_iff]
  change
    CuspRetraction.closedQuotientMap C hε (centralClosedZeroHomeomorph x) =
        CuspRetraction.closedQuotientMap C hε (centralClosedZeroHomeomorph y) ↔
      _
  exact CuspRetraction.closedQuotientMap_eq_iff C hε _ _

private abbrev CuspCollapse.PhasePositiveSpace :=
  ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre

private def
    CuspCollapse.centralCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePositiveSpace → CuspRetraction.QuotientCentralFibre C ε :=
  centralProject C ε hε ∘ centralPolarMap

private theorem
    CuspCollapse.centralCollapseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (centralCollapseMap C ε hε) :=
  (centralProject_continuous C ε hε).comp centralPolarMap_continuous

private theorem
    CuspCollapse.centralCollapseMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (centralCollapseMap C ε hε) :=
  (centralProject_surjective C ε hε).comp centralPolarMap_surjective

private theorem
    CuspCollapse.centralCollapseMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (centralCollapseMap C ε hε) :=
  (centralProject_isQuotientMap C ε hε hC).comp centralPolarMap_isQuotientMap

private def CuspCollapse.centralCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : PhasePositiveSpace) : Prop :=
  ∃ v : Fin 2 → ℤ,
    p.2 = positiveCentralTranslate C₀ v q.2 ∧
      p.1⁻¹ * (deckFibrePhase C₀ v * q.1) ∈
        MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space)

private theorem CuspCollapse.centralCollapseMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : PhasePositiveSpace) :
    centralCollapseMap C ε hε p = centralCollapseMap C ε hε q ↔
      centralCollapseRelation (C 0) p q := by
  change centralProject C ε hε (centralPolarMap p) = centralProject C ε hε (centralPolarMap q) ↔ _
  rw [centralProject_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) := by
      apply Subtype.ext
      exact ((centralPolarMap_phaseDeckMap C v q).trans hv).symm
    exact ⟨v, (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mp hpq⟩
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) :=
      (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mpr hv
    refine ⟨v, ?_⟩
    rw [← centralPolarMap_phaseDeckMap C v q]
    exact congrArg Subtype.val hpq.symm

private def
    CuspCollapse.centralCollapseSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Setoid PhasePositiveSpace
    where
  r := centralCollapseRelation C₀
  iseqv := by
    let f := centralCollapseMap (fun _ => C₀) 1 zero_lt_one
    have he (p q : PhasePositiveSpace) : f p = f q ↔ centralCollapseRelation C₀ p q :=
      centralCollapseMap_eq_iff (fun _ => C₀) 1 zero_lt_one p q
    exact
      { refl := fun p => (he p p).mp rfl
        symm := fun {p q} h => (he q p).mp ((he p q).mpr h).symm
        trans := fun {p q r} hpq hqr =>
          (he p r).mp (((he p q).mpr hpq).trans ((he q r).mpr hqr)) }

private abbrev CuspCollapse.CentralCollapseModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (centralCollapseSetoid C₀)

private def
    CuspCollapse.centralCollapseModelMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) → CuspRetraction.QuotientCentralFibre C ε :=
  Quotient.lift (centralCollapseMap C ε hε)
    (fun p q h => (centralCollapseMap_eq_iff C ε hε p q).mpr h)

private theorem
    CuspCollapse.centralCollapseModelMap_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Bijective (centralCollapseModelMap C ε hε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro h
        exact Quotient.sound ((centralCollapseMap_eq_iff C ε hε p q).mp h)
  · intro x
    obtain ⟨p, hp⟩ := centralCollapseMap_surjective C ε hε x
    exact ⟨Quotient.mk (centralCollapseSetoid (C 0)) p, hp⟩

private def
    CuspCollapse.centralCollapseEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) ≃ CuspRetraction.QuotientCentralFibre C ε :=
  Equiv.ofBijective (centralCollapseModelMap C ε hε) (centralCollapseModelMap_bijective C ε hε)

@[simp]
private theorem
    CuspCollapse.centralCollapseEquiv_symm_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : PhasePositiveSpace) :
    (centralCollapseEquiv C ε hε).symm (centralCollapseMap C ε hε p) =
      Quotient.mk (centralCollapseSetoid (C 0)) p := by
  apply (centralCollapseEquiv C ε hε).injective
  rw [Equiv.apply_symm_apply]
  rfl

end Mathoverflow1973

end
