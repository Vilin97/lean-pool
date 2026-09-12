/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerGradientControl
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRescaling
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientLimit

/-! The maximal positive horizon of a fixed ordinary Euler datum.
Existence below the supremum and failure above it follow from restriction;
membership of the endpoint is deliberately left to a continuation theorem. -/

section

/-! A genuine smooth endpoint under a finite gradient integral. Shorter
Euler solutions are rescaled to a common interval; the already proved
smooth limit supplies the endpoint, and uniqueness identifies it with
every original partial solution. No analytic radius is assumed. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
open scoped Topology

/-- Endpoint scale, given by `1-1/((n : ℝ)+2)`. -/
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
      ∃ U : Evolution S hS.le, U.velocity ⟨0, le_rfl, hS.le⟩ = A ∧
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
    (hW : W.velocity ⟨0, le_rfl, hT⟩ = A)
    (S : ℝ) (hS : 0 < S) (hST : S ≤ T) (U : Evolution S hS.le)
    (hU : U.velocity ⟨0, le_rfl, hS.le⟩ = A) (t : Icc (0 : ℝ) S) :
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
      ∃ U : Evolution S hS.le, U.velocity ⟨0, le_rfl, hS.le⟩ = A ∧
        ∀ t, U.gradientIntegral t ≤ G) :
    ∃ W : Evolution T hT.le, W.velocity ⟨0,le_rfl,hT.le⟩=A ∧
      ∀ S (hS : 0 < S) (hST : S ≤ T) (U : Evolution S hS.le),
        U.velocity ⟨0,le_rfl,hS.le⟩=A → ∀ t : Icc (0 : ℝ) S,
          W.velocity ⟨t,t.property.1,t.property.2.trans hST⟩=U.velocity t ∧
          W.pressureForce ⟨t,t.property.1,t.property.2.trans hST⟩=U.pressureForce t := by
  obtain ⟨W,hW⟩ := exists_smooth_endpoint T hT A G hpartial
  exact ⟨W,hW,fun S hS hST U hU t => endpoint_matches_partial W A hW S hS hST U hU t⟩

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field

/-- Has euler evolution, given by `∃ hT : 0 < T, ∃ U : Evolution T hT.le, U.velocity
⟨0,le_rfl,hT.le⟩=A`. -/
def HasEulerEvolution (A : SmoothL2Field Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : Evolution T hT.le, U.velocity ⟨0,le_rfl,hT.le⟩=A

theorem HasEulerEvolution.restrict {A : SmoothL2Field Space} {T : ℝ}
    (h : HasEulerEvolution A T) (S : ℝ) (hS : 0 < S) (hST : S ≤ T) :
    HasEulerEvolution A S := by
  obtain ⟨hT,U,hU⟩ := h
  exact ⟨hS,U.restrictTime S hS.le hST,hU⟩

theorem HasEulerEvolution.lt_of_failure {A : SmoothL2Field Space} {T B : ℝ}
    (h : HasEulerEvolution A T) (hB : 0 < B) (hfail : ¬ HasEulerEvolution A B) : T < B := by
  by_contra hn
  exact hfail (h.restrict B hB (le_of_not_gt hn))

/-- A compatible family of smooth solutions on every strictly shorter
positive interval, with no solution on any longer interval. -/
structure FiniteLifespan (A : SmoothL2Field Space) where
  /-- Duration of `FiniteLifespan`, of type `ℝ`. -/
  duration : ℝ
  duration_pos : 0 < duration
  shorter : ∀ S, 0 < S → S < duration → HasEulerEvolution A S
  maximal : ∀ S, duration < S → ¬ HasEulerEvolution A S

theorem exists_finite_lifespan (A : SmoothL2Field Space) (B : ℝ) (hB : 0 < B)
    (hlocal : ∃ T, HasEulerEvolution A T) (hfail : ¬ HasEulerEvolution A B) :
    ∃ L : FiniteLifespan A, L.duration ≤ B := by
  let times : Set ℝ := {T | HasEulerEvolution A T}
  have hne : times.Nonempty := hlocal
  have hbound : ∀ T ∈ times, T ≤ B := fun T hT => (hT.lt_of_failure hB hfail).le
  have hbdd : BddAbove times := ⟨B,hbound⟩
  have hpos : 0 < sSup times := by
    obtain ⟨T,hT⟩ := hlocal
    exact hT.choose.trans_le (le_csSup hbdd hT)
  refine ⟨{
    duration := sSup times
    duration_pos := hpos
    shorter := ?_
    maximal := ?_ },csSup_le hne hbound⟩
  · intro S hS hST
    obtain ⟨T,hT,hST'⟩ := exists_lt_of_lt_csSup hne hST
    exact hT.restrict S hS hST'.le
  · intro S hST hS
    exact (not_le_of_gt hST) (le_csSup hbdd hS)

namespace FiniteLifespan

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Evolution, given by `(L.shorter S hS hST).choose_spec.choose`. -/
def evolution (S : ℝ) (hS : 0 < S) (hST : S < L.duration) : Evolution S hS.le :=
  (L.shorter S hS hST).choose_spec.choose

theorem evolution_initial (S : ℝ) (hS : 0 < S) (hST : S < L.duration) :
    (L.evolution S hS hST).velocity ⟨0,le_rfl,hS.le⟩=A :=
  (L.shorter S hS hST).choose_spec.choose_spec

theorem evolution_agrees (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (hST : S ≤ T)
    (t : Icc (0 : ℝ) S) :
    (L.evolution T hT hTL).velocity ⟨t,t.property.1,t.property.2.trans hST⟩=
        (L.evolution S hS hSL).velocity t ∧
      (L.evolution T hT hTL).pressureForce ⟨t,t.property.1,t.property.2.trans hST⟩=
        (L.evolution S hS hSL).pressureForce t :=
  endpoint_matches_partial (L.evolution T hT hTL) A (L.evolution_initial T hT hTL)
    S hS hST (L.evolution S hS hSL) (L.evolution_initial S hS hSL) t

theorem endpoint_of_bounded_gradient (G : ℝ)
    (hG : ∀ S (hS : 0 < S) (hST : S < L.duration) t,
      (L.evolution S hS hST).gradientIntegral t ≤ G) : HasEulerEvolution A L.duration := by
  refine ⟨L.duration_pos,?_⟩
  apply exists_smooth_endpoint L.duration L.duration_pos A G
  intro S hS hST
  exact ⟨L.evolution S hS hST,L.evolution_initial S hS hST,hG S hS hST⟩

end FiniteLifespan
end EulerOrdinarySobolev
