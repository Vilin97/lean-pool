/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal

@[expose] public section

/-! Actual vorticity supremum norms and their partial integrals on a
half-open maximal Euler interval. All quantities agree exactly with
the genuine smooth solutions on every shorter closed interval. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus EulerMeanCutoffCurl
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff Topology

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

theorem vorticityIntegral_agrees (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (hST : S ≤ T)
    (t : Icc (0 : ℝ) S) :
    (L.evolution S hS hSL).vorticityIntegral t=
      (L.evolution T hT hTL).vorticityIntegral ⟨t,t.property.1,t.property.2.trans hST⟩ := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrs : r ∈ Icc (0 : ℝ) (t : ℝ) := by simpa only [uIcc_of_le t.property.1] using hr
  have hrS : r ∈ Icc (0 : ℝ) S := ⟨hrs.1,hrs.2.trans t.property.2⟩
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hrs.1,hrS.2.trans hST⟩
  change vorticityNorm ((L.evolution S hS hSL).velocity (projIcc 0 S hS.le r))=
    vorticityNorm ((L.evolution T hT hTL).velocity (projIcc 0 T hT.le r))
  rw [projIcc_of_mem hS.le hrS,projIcc_of_mem hT.le hrT,
    L.evolution_agrees_at S T hS hT hSL hTL r hrs.1 hrS.2 hrT.2]

theorem vorticityIntegral_agrees_at (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (t : ℝ)
    (ht0 : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    (L.evolution S hS hSL).vorticityIntegral ⟨t,ht0,htS⟩=
      (L.evolution T hT hTL).vorticityIntegral ⟨t,ht0,htT⟩ := by
  rcases le_total S T with hST | hTS
  · exact L.vorticityIntegral_agrees S T hS hT hSL hTL hST ⟨t,ht0,htS⟩
  · exact (L.vorticityIntegral_agrees T S hT hS hTL hSL hTS ⟨t,ht0,htT⟩).symm

def maximalVorticityNorm (t : L.Time) : ℝ := vorticityNorm (L.maximalField t)

theorem maximalVorticityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVorticityNorm t :=
  vorticityNorm_nonneg _

theorem maximalVorticityNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVorticityNorm t ≤ K ↔ ∀ x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ K :=
  vorticityNorm_le_iff _ K

theorem maximalVorticityNorm_continuous : Continuous L.maximalVorticityNorm :=
  vorticityNorm_continuous L.maximalField L.maximalField_jet_continuous

theorem maximalVorticityNorm_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityNorm (L.shorterTime S hSL t)=(L.evolution S hS hSL).vorticityNormPath t := by
  change vorticityNorm (L.maximalField (L.shorterTime S hSL t))=_
  rw [L.maximalField_eq_evolution S hS hSL t]
  rfl

def maximalVorticityIntegral (t : L.Time) : ℝ :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).vorticityIntegral (L.intermediateTime t)

theorem maximalVorticityIntegral_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityIntegral (L.shorterTime S hSL t)=
      (L.evolution S hS hSL).vorticityIntegral t :=
  L.vorticityIntegral_agrees_at (L.intermediateHorizon (L.shorterTime S hSL t)) S
    (L.intermediateHorizon_pos (L.shorterTime S hSL t)) hS
    (L.intermediateHorizon_lt (L.shorterTime S hSL t)) hSL t t.property.1
    (L.time_lt_intermediateHorizon (L.shorterTime S hSL t)).le t.property.2

theorem maximalVorticityIntegral_nonneg (t : L.Time) : 0 ≤ L.maximalVorticityIntegral t :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).vorticityIntegral_nonneg (L.intermediateTime t)

theorem maximalVorticityIntegral_initial : L.maximalVorticityIntegral L.initialTime=0 :=
  (L.evolution (L.intermediateHorizon L.initialTime) (L.intermediateHorizon_pos L.initialTime)
    (L.intermediateHorizon_lt L.initialTime)).vorticityIntegral_initial

theorem maximalVorticityIntegral_continuous : Continuous L.maximalVorticityIntegral := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  have he : (fun t : Icc (0 : ℝ) S => L.maximalVorticityIntegral (L.shorterTime S hSL t))=
      (L.evolution S hS hSL).vorticityIntegral :=
    funext (L.maximalVorticityIntegral_eq_evolution S hS hSL)
  rw [he]
  exact (L.evolution S hS hSL).vorticityIntegral_continuous

theorem maximalVorticityIntegral_mono : Monotone L.maximalVorticityIntegral := by
  intro s t hst
  let R := L.intermediateHorizon t
  have hR : 0 < R := L.intermediateHorizon_pos t
  have hRL : R < L.duration := L.intermediateHorizon_lt t
  have htR : (t : ℝ) ≤ R := (L.time_lt_intermediateHorizon t).le
  have hsR : (s : ℝ) ≤ R := (show (s : ℝ) ≤ t from hst).trans htR
  have hs := L.maximalVorticityIntegral_eq_evolution R hR hRL ⟨s,s.property.1,hsR⟩
  have ht := L.maximalVorticityIntegral_eq_evolution R hR hRL ⟨t,t.property.1,htR⟩
  change L.maximalVorticityIntegral s=_ at hs
  change L.maximalVorticityIntegral t=_ at ht
  rw [hs,ht]
  exact (L.evolution R hR hRL).vorticityIntegral_mono _ _ hst

theorem vorticityIntegral_eventually_large_of_unbounded
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t)
    (G : ℝ) :
    ∃ (R : ℝ) (_hR : 0 < R) (_hRL : R < L.duration),
      ∀ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration), R ≤ S →
        G < (L.evolution S hS hSL).vorticityIntegral ⟨S,hS.le,le_rfl⟩ := by
  obtain ⟨R,hR,hRL,t,ht⟩ := hunbounded G
  refine ⟨R,hR,hRL,?_⟩
  intro S hS hSL hRS
  rw [L.vorticityIntegral_agrees R S hR hS hRL hSL hRS t] at ht
  exact ht.trans_le ((L.evolution S hS hSL).vorticityIntegral_mono
    ⟨t,t.property.1,t.property.2.trans hRS⟩ ⟨S,hS.le,le_rfl⟩ (t.property.2.trans hRS))

theorem maximalVorticityIntegral_tendsto_atTop
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t) :
    Tendsto L.maximalVorticityIntegral (atTop : Filter L.Time) atTop := by
  apply tendsto_atTop.mpr
  intro G
  obtain ⟨R,hR,hRL,hlarge⟩ := L.vorticityIntegral_eventually_large_of_unbounded hunbounded G
  filter_upwards [eventually_ge_atTop (⟨R,hR.le,hRL⟩ : L.Time)] with t ht
  have htpos : 0 < (t : ℝ) := hR.trans_le ht
  have he := L.maximalVorticityIntegral_eq_evolution t htpos t.property.2 ⟨t,t.property.1,le_rfl⟩
  change L.maximalVorticityIntegral t=_ at he
  rw [he]
  exact (hlarge t htpos t.property.2 ht).le

end EulerOrdinarySobolev.FiniteLifespan
