/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRescaling
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientLimit

@[expose] public section

/-! A genuine smooth endpoint under a finite gradient integral. Shorter
Euler solutions are rescaled to a common interval; the already proved
smooth limit supplies the endpoint, and uniqueness identifies it with
every original partial solution. No analytic radius is assumed. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
open scoped Topology

def endpointScale (n : ℕ) : ℝ := 1-1/((n : ℝ)+2)

theorem endpointScale_pos (n : ℕ) : 0 < endpointScale n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : 1/((n : ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  dsimp [endpointScale]
  linarith

theorem endpointScale_lt_one (n : ℕ) : endpointScale n < 1 := by
  have h : 0 < 1/((n : ℝ)+2) := by positivity
  dsimp [endpointScale]
  linarith

theorem endpointScale_tendsto : Tendsto endpointScale atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  change Tendsto (fun n : ℕ => 1-1/((n : ℝ)+2)) atTop (𝓝 1)
  simpa only [one_div,sub_zero] using
    (show Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hi

theorem exists_smooth_endpoint (T : ℝ) (hT : 0 < T) (A : SmoothL2Field Space) (G : ℝ)
    (hpartial : ∀ S (hS : 0 < S), S < T →
      ∃ U : Evolution S hS.le, U.velocity ⟨0,le_rfl,hS.le⟩=A ∧
        ∀ t, U.gradientIntegral t ≤ G) :
    ∃ U : Evolution T hT.le, U.velocity ⟨0,le_rfl,hT.le⟩=A := by
  have hsol (n : ℕ) :
      ∃ U : Evolution (endpointScale n*T) (mul_nonneg (endpointScale_pos n).le hT.le),
        U.velocity ⟨0,le_rfl,mul_nonneg (endpointScale_pos n).le hT.le⟩=A ∧
          ∀ t, U.gradientIntegral t ≤ G := by
    exact hpartial (endpointScale n*T) (mul_pos (endpointScale_pos n) hT)
      (by simpa only [one_mul] using mul_lt_mul_of_pos_right (endpointScale_lt_one n) hT)
  choose U hinit hgrad using hsol
  let V : ℕ → Evolution T hT.le := fun n =>
    (U n).rescale T hT.le (endpointScale n) (endpointScale_pos n) le_rfl
  have hv0 (n : ℕ) : (V n).velocity ⟨0,le_rfl,hT.le⟩=scaleField (endpointScale n) A := by
    exact ((U n).rescale_initial T hT.le (endpointScale n) (endpointScale_pos n) le_rfl).trans
      (congrArg (scaleField (endpointScale n)) (hinit n))
  let M := gradientTensorBound (tensorNorm 3 A) G
  have hb (n : ℕ) (t : Icc (0 : ℝ) T) : tensorNorm 3 ((V n).velocity t) ≤ M := by
    apply (tensorNorm_scaleField_le (endpointScale n) (endpointScale_pos n).le
      (endpointScale_lt_one n).le _ 3).trans
    apply (U n).h3_tensorNorm_gradient_uniform (tensorNorm 3 A) G _ (hgrad n)
    rw [hinit]
  have hb0 : ∀ q, ∃ C : ℝ, ∀ n, tensorNorm q ((V n).velocity ⟨0,le_rfl,hT.le⟩) ≤ C := by
    intro q
    refine ⟨tensorNorm q A,fun n => ?_⟩
    rw [hv0]
    exact tensorNorm_scaleField_le (endpointScale n) (endpointScale_pos n).le
      (endpointScale_lt_one n).le A q
  have hc : Tendsto (fun n => ((V n).velocity ⟨0,le_rfl,hT.le⟩).toLp) atTop (𝓝 A.toLp) := by
    simp_rw [hv0,scaleField_toLp]
    simpa only [one_smul] using endpointScale_tendsto.smul_const A.toLp
  let W := limitEvolutionOfH3 V hT M hb hb0 hc.cauchySeq
  refine ⟨W,smoothField_eq_of_toLp_eq _ A ?_⟩
  exact limitEvolutionOfH3_initial V hT M hb hb0 hc.cauchySeq A.toLp hc

theorem endpoint_matches_partial {T : ℝ} {hT : 0 ≤ T}
    (W : Evolution T hT) (A : SmoothL2Field Space)
    (hW : W.velocity ⟨0,le_rfl,hT⟩=A)
    (S : ℝ) (hS : 0 < S) (hST : S ≤ T) (U : Evolution S hS.le)
    (hU : U.velocity ⟨0,le_rfl,hS.le⟩=A) (t : Icc (0 : ℝ) S) :
    W.velocity ⟨t,t.property.1,t.property.2.trans hST⟩=U.velocity t ∧
      W.pressureForce ⟨t,t.property.1,t.property.2.trans hST⟩=U.pressureForce t := by
  let R := W.restrictTime S hS.le hST
  have hi : (U.velocity ⟨0,le_rfl,hS.le⟩).toLp=(R.velocity ⟨0,le_rfl,hS.le⟩).toLp := by
    rw [hU]
    change A.toLp=(W.velocity ⟨0,le_rfl,hT⟩).toLp
    rw [hW]
  exact ⟨(R.velocity_eq_of_initial U hi t).symm,(R.pressure_eq_of_initial U hS hi t).symm⟩

theorem exists_smooth_endpoint_extension (T : ℝ) (hT : 0 < T)
    (A : SmoothL2Field Space) (G : ℝ)
    (hpartial : ∀ S (hS : 0 < S), S < T →
      ∃ U : Evolution S hS.le, U.velocity ⟨0,le_rfl,hS.le⟩=A ∧
        ∀ t, U.gradientIntegral t ≤ G) :
    ∃ W : Evolution T hT.le, W.velocity ⟨0,le_rfl,hT.le⟩=A ∧
      ∀ S (hS : 0 < S) (hST : S ≤ T) (U : Evolution S hS.le),
        U.velocity ⟨0,le_rfl,hS.le⟩=A → ∀ t : Icc (0 : ℝ) S,
          W.velocity ⟨t,t.property.1,t.property.2.trans hST⟩=U.velocity t ∧
          W.pressureForce ⟨t,t.property.1,t.property.2.trans hST⟩=U.pressureForce t := by
  obtain ⟨W,hW⟩ := exists_smooth_endpoint T hT A G hpartial
  exact ⟨W,hW,fun S hS hST U hU t => endpoint_matches_partial W A hW S hS hST U hU t⟩

end EulerOrdinarySobolev
