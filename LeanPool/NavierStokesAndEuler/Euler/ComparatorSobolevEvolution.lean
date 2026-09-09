/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
public import LeanPool.NavierStokesAndEuler.Euler.EulerSingularity

@[expose] public section

/-! Repackaging the reference's ordinary functions as the development's smooth
L² fields. The scalar Euler equations and time-regularity hypotheses coincide. -/

noncomputable section

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open scoped Topology ContDiff

namespace Euler.ComparatorBridge

theorem toL2_field (A : SmoothL2Field Space) : Euler.toL2 A.field = A.toLp := by
  simp only [Euler.toL2, dite_eq_left A.memLp, SmoothL2Field.toLp]

theorem toL2_jet (A : SmoothL2Field Space) (n : ℕ) :
    Euler.toL2 (iteratedFDeriv ℝ n A.field) = A.jetLp n := by
  simp only [Euler.toL2, dite_eq_left (A.integrable n), SmoothL2Field.jetLp]

theorem sobolevSmoothOn_of_path {I : Set ℝ} (A : I → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (v : Space → ℝ → Space) (hv : ∀ t : I, (v · (t : ℝ)) = (A t).field) :
    Euler.SobolevSmoothOn I v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hv ⟨t, ht⟩]
    exact (A ⟨t, ht⟩).smooth
  · intro t ht
    rw [hv ⟨t, ht⟩]
    exact (A ⟨t, ht⟩).memLp
  · intro n t ht
    rw [hv ⟨t, ht⟩]
    exact (A ⟨t, ht⟩).integrable n
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun t : I => Euler.toL2 (v · (t : ℝ))) = fun t => (A t).toLp := by
      funext t
      rw [hv t, toL2_field]
    change Continuous (fun t : I => Euler.toL2 (v · (t : ℝ)))
    rw [he]
    exact continuous_toLp A (hA 0)
  · intro n
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun t : I => Euler.toL2 (iteratedFDeriv ℝ n (v · (t : ℝ)))) =
        fun t => (A t).jetLp n := by
      funext t
      rw [hv t, toL2_jet]
    change Continuous (fun t : I => Euler.toL2 (iteratedFDeriv ℝ n (v · (t : ℝ))))
    rw [he]
    exact hA n

end Euler.ComparatorBridge

namespace Euler.SobolevSmoothOn

variable {I : Set ℝ} {v : Space → ℝ → Space} (h : SobolevSmoothOn I v)

def field (t : I) : SmoothL2Field Space where
  field := (v · (t : ℝ))
  smooth := h.spatial_smooth t t.property
  integrable n := h.jets_integrable n t t.property

theorem field_toLp (t : I) : (h.field t).toLp = Euler.toL2 (v · (t : ℝ)) :=
  (ComparatorBridge.toL2_field (h.field t)).symm

theorem field_jetLp (t : I) (n : ℕ) :
    (h.field t).jetLp n = Euler.toL2 (iteratedFDeriv ℝ n (v · (t : ℝ))) :=
  (ComparatorBridge.toL2_jet (h.field t) n).symm

theorem field_continuous (n : ℕ) : Continuous (fun t => (h.field t).jetLp n) := by
  simp only [h.field_jetLp]
  exact (h.jets_continuous n).domRestrict

end Euler.SobolevSmoothOn

namespace Euler.ComparatorBridge

theorem hasScalarEulerEvolution_of_sobolev
    {A : SmoothL2Field Space} {T : ℝ} (hT : 0 < T)
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field v p) :
    HasScalarEulerEvolution A T := by
  obtain ⟨w, hw, hd, he⟩ := h.euler
  refine ⟨hT, h.velocity_smooth.field, ?_, ?_⟩
  · refine ⟨h.velocity_smooth.field_continuous, hw.field, (fun t x => p x t),
      hw.field_continuous, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [hw.field_toLp]
      apply (hd t (by simpa only [interior_Icc] using ht)).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      rw [projIcc_of_mem hT.le hs, h.velocity_smooth.field_toLp]
    · intro t x
      exact h.div_free x t t.property
    · intro t ht
      exact h.pressure_differentiable t (by simpa only [interior_Icc] using ht)
    · intro t ht x
      exact add_eq_zero_iff_eq_neg.mpr (he x t (by simpa only [interior_Icc] using ht))
  · apply field_ext
    funext x
    exact h.initial_condition x

def evolutionVelocity {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)
    (x : Space) (t : ℝ) : Space := (U.velocity (projIcc 0 T hT t)).field x

def evolutionPressure {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)
    (x : Space) (t : ℝ) : ℝ := U.scalarPressure (projIcc 0 T hT t) x

theorem evolution_sobolevSolution {T : ℝ} {hT : 0 ≤ T}
    (U : Evolution T hT) (A : SmoothL2Field Space)
    (hinit : U.velocity ⟨0, le_rfl, hT⟩ = A) :
    EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field
      (evolutionVelocity U) (evolutionPressure U) := by
  have hv (t : Icc (0 : ℝ) T) :
      (evolutionVelocity U · (t : ℝ)) = (U.velocity t).field := by
    funext x
    simp only [evolutionVelocity, projIcc_of_mem hT t.property]
  let w : Space → ℝ → Space := fun x t => (U.derivative (projIcc 0 T hT t)).field x
  have hw (t : Icc (0 : ℝ) T) : (w · (t : ℝ)) = (U.derivative t).field := by
    funext x
    simp only [w, projIcc_of_mem hT t.property]
  refine ⟨?_, ?_, sobolevSmoothOn_of_path U.velocity U.velocity_continuous _ hv, ?_,
    w, sobolevSmoothOn_of_path U.derivative U.derivative_continuous w hw, ?_, ?_⟩
  · intro x t ht
    rw [hv ⟨t, ht⟩]
    exact EulerMeanClassical.solenoidal_representative_divergence _ (U.solenoidal ⟨t, ht⟩)
      _ (U.velocity ⟨t, ht⟩).smooth (U.velocity ⟨t, ht⟩).toLp_ae x
  · intro x
    change (U.velocity (projIcc 0 T hT 0)).field x = A.field x
    rw [projIcc_of_mem hT ⟨le_rfl, hT⟩, hinit]
  · intro t _
    exact (U.scalarPressure_spec (projIcc 0 T hT t)).1.differentiable (by simp)
  · intro t ht
    have hi : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    have hd := (U.velocityPath_hasDerivWithinAt ⟨t, hi.1.le, hi.2.le⟩).hasDerivAt
      (Icc_mem_nhds hi.1 hi.2)
    rw [U.velocityPath_extend] at hd
    simpa only [evolutionVelocity, w, toL2_field, projIcc_of_mem hT ⟨hi.1.le, hi.2.le⟩]
      using hd
  · intro x t ht
    have hi : t ∈ Icc 0 T := interior_subset ht
    rw [hv ⟨t, hi⟩]
    change (U.derivative (projIcc 0 T hT t)).field x + _ =
      -gradient (U.scalarPressure (projIcc 0 T hT t)) x
    rw [projIcc_of_mem hT hi, (U.scalarPressure_spec ⟨t, hi⟩).2.2 x,
      U.derivative_field]
    dsimp only [evolutionVelocity]
    rw [projIcc_of_mem hT hi]
    abel

theorem exists_sobolevSolution_iff (A : SmoothL2Field Space) (T : ℝ) (hT : 0 < T) :
    (∃ v p, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field v p) ↔
      HasScalarEulerEvolution A T := by
  constructor
  · rintro ⟨v, p, h⟩
    exact hasScalarEulerEvolution_of_sobolev hT h
  · intro h
    obtain ⟨hpos, U, hinit⟩ := (EulerOrdinarySobolev.hasScalarEulerEvolution_iff A T).mp h
    exact ⟨evolutionVelocity U, evolutionPressure U, evolution_sobolevSolution U A hinit⟩

end Euler.ComparatorBridge
