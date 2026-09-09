/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

/-!
# Regularity and locality of the concrete Navier--Stokes residual

All operators below are the ordinary derivatives in `ProblemStatement`.
The main regularity theorem is on an open spacetime domain; it does not
differentiate an unspecified extension through a time boundary.
-/

namespace NavierStokes.ResidualRegularity

noncomputable section

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Parameter-dependent spatial differentiation lowers regularity by one.
The output is the actual Fréchet derivative of each spatial slice. -/
theorem contDiffOn_space_fderiv {s : Set SpaceTime} {g : SpaceTime → V}
    {m n : WithTop ℕ∞} (hs : IsOpen s) (hg : ContDiffOn ℝ n g s)
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (fun z => fderiv ℝ (fun y : Space => g (z.1, y)) z.2) s := by
  intro z hz
  have hpair : ContDiffAt ℝ n
      (Function.uncurry (fun w : SpaceTime => fun y : Space => g (w.1, y)))
      (z, z.2) :=
    (hg.contDiffAt (hs.mem_nhds hz)).comp (z, z.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hpair.fderiv contDiffAt_snd hmn).contDiffWithinAt

/-- Parameter-dependent time differentiation lowers regularity by one. -/
theorem contDiffOn_time_fderiv {s : Set SpaceTime} {g : SpaceTime → V}
    {m n : WithTop ℕ∞} (hs : IsOpen s) (hg : ContDiffOn ℝ n g s)
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (fun z => fderiv ℝ (fun t : ℝ => g (t, z.2)) z.1) s := by
  intro z hz
  have hpair : ContDiffAt ℝ n
      (Function.uncurry (fun w : SpaceTime => fun t : ℝ => g (t, w.2)))
      (z, z.1) :=
    (hg.contDiffAt (hs.mem_nhds hz)).comp (z, z.1)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hpair.fderiv contDiffAt_fst hmn).contDiffWithinAt

theorem contDiffOn_temporalDerivative {s : Set SpaceTime} {u : VelocityField}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (fun z => temporalDerivative u z.1 z.2) s :=
  (contDiffOn_time_fderiv hs hu (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_spatialDerivative {s : Set SpaceTime} {u : VelocityField}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (fun z => spatialDerivative u z.1 z.2) s :=
  contDiffOn_space_fderiv hs hu (by simp)

theorem contDiffOn_advection {s : Set SpaceTime} {u : VelocityField}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (fun z => advection u z.1 z.2) s :=
  (contDiffOn_spatialDerivative hs hu).clm_apply hu

theorem contDiffOn_pressureGradient {s : Set SpaceTime} {p : PressureField}
    (hs : IsOpen s) (hp : ContDiffOn ℝ ∞ p s) :
    ContDiffOn ℝ ∞ (fun z => pressureGradient p z.1 z.2) s := by
  unfold pressureGradient
  apply ContDiffOn.sum
  intro i _
  exact ((contDiffOn_space_fderiv hs hp (by simp)).clm_apply contDiffOn_const).smul
    contDiffOn_const

theorem contDiffOn_spatialLaplacian {s : Set SpaceTime} {u : VelocityField}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (fun z => spatialLaplacian u z.1 z.2) s := by
  unfold spatialLaplacian
  apply ContDiffOn.sum
  intro i _
  have hdir : ContDiffOn ℝ ∞
      (fun z => spatialDerivative u z.1 z.2 (coordinateVector i)) s :=
    (contDiffOn_spatialDerivative hs hu).clm_apply contDiffOn_const
  exact (contDiffOn_space_fderiv hs hdir (by simp)).clm_apply contDiffOn_const

/-- Jointly smooth velocity and pressure have a jointly smooth actual residual. -/
theorem contDiffOn_residual {s : Set SpaceTime} {u : VelocityField} {p : PressureField}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) (hp : ContDiffOn ℝ ∞ p s) :
    ContDiffOn ℝ ∞ (fun z => navierStokesResidual u p z.1 z.2) s :=
  (((contDiffOn_temporalDerivative hs hu).add (contDiffOn_advection hs hu)).sub
    (contDiffOn_spatialLaplacian hs hu)).add (contDiffOn_pressureGradient hs hp)

theorem contDiffOn_residual_product {times : Set ℝ} {u : VelocityField} {p : PressureField}
    (ht : IsOpen times) (hu : ContDiffOn ℝ ∞ u (times ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z => navierStokesResidual u p z.1 z.2)
      (times ×ˢ (univ : Set Space)) :=
  contDiffOn_residual (ht.prod isOpen_univ) hu hp

/-- The candidate's relative smoothness hypotheses suffice at all interior times. -/
theorem contDiffOn_residual_interior {u : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (fun z => navierStokesResidual u p z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  have hsub : Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩
  exact contDiffOn_residual_product isOpen_Ioo (hu.mono hsub) (hp.mono hsub)

/-! ## Exact spatial periods -/

/-- A spatial unit period passes to the actual derivative of the spatial
slice. No differentiability hypothesis is needed for this translation rule. -/
theorem space_fderiv_periods {g : SpaceTime → V} {times : Set ℝ}
    (hg : UnitSpatialPeriodsOn times g) :
    UnitSpatialPeriodsOn times
      (fun z => fderiv ℝ (fun y : Space => g (z.1, y)) z.2) := by
  intro t ht x i
  have heq : (fun y : Space => g (t, y + coordinateVector i)) =
      (fun y : Space => g (t, y)) := by
    funext y
    exact hg t ht y i
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Space => g (t, y))
    (x := x) (coordinateVector i)
  rw [heq] at hd
  exact hd.symm

/-- Time differentiation preserves spatial periods when the period identity
holds on an open neighborhood of the time being differentiated. -/
theorem temporalDerivative_periods {u : VelocityField} {times : Set ℝ}
    (htimes : IsOpen times) (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => temporalDerivative u z.1 z.2) := by
  intro t ht x i
  have heq : (fun r : ℝ => u (r, x + coordinateVector i)) =ᶠ[𝓝 t]
      (fun r : ℝ => u (r, x)) := by
    filter_upwards [htimes.mem_nhds ht] with r hr
    exact hu r hr x i
  exact congrArg (fun L : ℝ →L[ℝ] Space => L 1) heq.fderiv_eq

theorem spatialDerivative_periods {u : VelocityField} {times : Set ℝ}
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => spatialDerivative u z.1 z.2) :=
  space_fderiv_periods hu

theorem advection_periods {u : VelocityField} {times : Set ℝ}
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => advection u z.1 z.2) := by
  intro t ht x i
  exact congrArg₂ (fun (L : Space →L[ℝ] Space) (v : Space) => L v)
    (spatialDerivative_periods hu t ht x i) (hu t ht x i)

theorem pressureGradient_periods {p : PressureField} {times : Set ℝ}
    (hp : UnitSpatialPeriodsOn times p) :
    UnitSpatialPeriodsOn times (fun z => pressureGradient p z.1 z.2) := by
  intro t ht x i
  exact congrArg (fun L : Space →L[ℝ] ℝ =>
    ∑ j : Fin 3, (L (coordinateVector j)) • coordinateVector j)
    (space_fderiv_periods hp t ht x i)

theorem spatialLaplacian_periods {u : VelocityField} {times : Set ℝ}
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => spatialLaplacian u z.1 z.2) := by
  intro t ht x i
  unfold spatialLaplacian
  apply Finset.sum_congr rfl
  intro j _
  have hdir : UnitSpatialPeriodsOn times
      (fun z => spatialDerivative u z.1 z.2 (coordinateVector j)) := by
    intro r hr y k
    exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j))
      (spatialDerivative_periods hu r hr y k)
  exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j))
    (space_fderiv_periods hdir t ht x i)

/-- The concrete residual has the same unit spatial periods as its inputs.
Openness is needed only to pass the period identity through time differentiation. -/
theorem residual_periods {u : VelocityField} {p : PressureField} {times : Set ℝ}
    (htimes : IsOpen times) (hu : UnitSpatialPeriodsOn times u)
    (hp : UnitSpatialPeriodsOn times p) :
    UnitSpatialPeriodsOn times (fun z => navierStokesResidual u p z.1 z.2) := by
  intro t ht x i
  have htime := temporalDerivative_periods htimes hu t ht x i
  have hadv := advection_periods hu t ht x i
  have hlap := spatialLaplacian_periods hu t ht x i
  have hgrad := pressureGradient_periods hp t ht x i
  unfold navierStokesResidual
  dsimp only at htime hadv hlap hgrad ⊢
  rw [htime, hadv, hlap, hgrad]

theorem residual_periods_interior {u : VelocityField} {p : PressureField}
    (hu : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn (Ioo (0 : ℝ) 1)
      (fun z => navierStokesResidual u p z.1 z.2) := by
  apply residual_periods isOpen_Ioo
  · intro t ht x i
    exact hu t ⟨ht.1.le, ht.2⟩ x i
  · intro t ht x i
    exact hp t ⟨ht.1.le, ht.2⟩ x i

/-! ## Locality, without differentiability assumptions -/

theorem space_fderiv_congr {f g : SpaceTime → V} {z : SpaceTime}
    (h : f =ᶠ[𝓝 z] g) :
    fderiv ℝ (fun y : Space => f (z.1, y)) z.2 =
      fderiv ℝ (fun y : Space => g (z.1, y)) z.2 := by
  have hslice : (fun y : Space => f (z.1, y)) =ᶠ[𝓝 z.2]
      (fun y : Space => g (z.1, y)) :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  exact hslice.fderiv_eq

theorem time_fderiv_congr {f g : SpaceTime → V} {z : SpaceTime}
    (h : f =ᶠ[𝓝 z] g) :
    fderiv ℝ (fun t : ℝ => f (t, z.2)) z.1 =
      fderiv ℝ (fun t : ℝ => g (t, z.2)) z.1 := by
  have hslice : (fun t : ℝ => f (t, z.2)) =ᶠ[𝓝 z.1]
      (fun t : ℝ => g (t, z.2)) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  exact hslice.fderiv_eq

theorem temporalDerivative_congr {u v : VelocityField} {z : SpaceTime}
    (h : u =ᶠ[𝓝 z] v) :
    temporalDerivative u z.1 z.2 = temporalDerivative v z.1 z.2 := by
  unfold temporalDerivative
  rw [time_fderiv_congr h]

theorem spatialDerivative_congr {u v : VelocityField} {z : SpaceTime}
    (h : u =ᶠ[𝓝 z] v) :
    spatialDerivative u z.1 z.2 = spatialDerivative v z.1 z.2 :=
  space_fderiv_congr h

theorem advection_congr {u v : VelocityField} {z : SpaceTime}
    (h : u =ᶠ[𝓝 z] v) : advection u z.1 z.2 = advection v z.1 z.2 := by
  unfold advection
  rw [spatialDerivative_congr h]
  exact congrArg (spatialDerivative v z.1 z.2) h.self_of_nhds

theorem pressureGradient_congr {p q : PressureField} {z : SpaceTime}
    (h : p =ᶠ[𝓝 z] q) : pressureGradient p z.1 z.2 = pressureGradient q z.1 z.2 := by
  unfold pressureGradient
  rw [space_fderiv_congr h]

theorem spatialLaplacian_congr {u v : VelocityField} {z : SpaceTime}
    (h : u =ᶠ[𝓝 z] v) : spatialLaplacian u z.1 z.2 = spatialLaplacian v z.1 z.2 := by
  unfold spatialLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hdir : (fun w => spatialDerivative u w.1 w.2 (coordinateVector i)) =ᶠ[𝓝 z]
      (fun w => spatialDerivative v w.1 w.2 (coordinateVector i)) := by
    filter_upwards [h.eventuallyEq_nhds] with w hw
    rw [spatialDerivative_congr hw]
  exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i))
    (space_fderiv_congr hdir)

/-- Local agreement of the two inputs implies agreement of their concrete
residual at the point, including the iterated spatial derivative. -/
theorem residual_congr {u v : VelocityField} {p q : PressureField} {z : SpaceTime}
    (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    navierStokesResidual u p z.1 z.2 = navierStokesResidual v q z.1 z.2 := by
  unfold navierStokesResidual
  rw [temporalDerivative_congr hu, advection_congr hu,
    spatialLaplacian_congr hu, pressureGradient_congr hp]

theorem residual_eventuallyEq {u v : VelocityField} {p q : PressureField} {z : SpaceTime}
    (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    (fun w => navierStokesResidual u p w.1 w.2) =ᶠ[𝓝 z]
      (fun w => navierStokesResidual v q w.1 w.2) := by
  filter_upwards [hu.eventuallyEq_nhds, hp.eventuallyEq_nhds] with w huw hpw
  exact residual_congr huw hpw

theorem residual_eqOn {u v : VelocityField} {p q : PressureField} {s : Set SpaceTime}
    (hs : IsOpen s) (hu : EqOn u v s) (hp : EqOn p q s) :
    EqOn (fun z => navierStokesResidual u p z.1 z.2)
      (fun z => navierStokesResidual v q z.1 z.2) s := by
  intro z hz
  apply residual_congr
  · filter_upwards [hs.mem_nhds hz] with w hw
    exact hu hw
  · filter_upwards [hs.mem_nhds hz] with w hw
    exact hp hw

/-- A local zero extension of velocity and pressure has zero residual. -/
theorem residual_eq_zero_of_eventually_zero {u : VelocityField} {p : PressureField}
    {z : SpaceTime} (hu : u =ᶠ[𝓝 z] (fun _ => 0))
    (hp : p =ᶠ[𝓝 z] (fun _ => 0)) : navierStokesResidual u p z.1 z.2 = 0 := by
  simpa only [zero_residual] using residual_congr hu hp

theorem residual_eventually_zero {u : VelocityField} {p : PressureField}
    {z : SpaceTime} (hu : u =ᶠ[𝓝 z] (fun _ => 0))
    (hp : p =ᶠ[𝓝 z] (fun _ => 0)) :
    (fun w => navierStokesResidual u p w.1 w.2) =ᶠ[𝓝 z] (fun _ => 0) := by
  simpa only [zero_residual] using residual_eventuallyEq hu hp

end

end NavierStokes.ResidualRegularity
