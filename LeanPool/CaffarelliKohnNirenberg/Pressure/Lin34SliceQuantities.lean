/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceForceCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceFubini
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceMeanFree
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SlicePointwise

/-!
# Lin34 Slice Quantities

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-!
# The four time-slice quantities of `prop:lin34`

The integrated estimate `eq:lin35-force` of `paper/ckn.tex` is obtained by
integrating `eq:lin34-pointwise` over `J_ρ = (t₀ - ρ², t₀)`.  This file names
the four functions of time that appear in that integration, proves that they
are integrable on `J_ρ`, and identifies their integrals with the cylinder
quantities `D(z₀, r)` and `D(z₀, ρ)` of `eq:ABCDE`, and `C_hat(z₀, ρ)` of `eq:Chat`.
-/

/-- The spatial `L³` mass of the mean-free velocity on `B_ρ` at time `s`,
the slice integrand of `C_hat(z₀,ρ)` in `eq:Chat`. -/
@[expose] def lin34VelocitySlice (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (ρ s : ℝ) : ℝ :=
  ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (meanFreeVec u z.1 ρ s y) ^ (3 : ℕ)

/-- The spatial `L^{3/2}` mass of the pressure on `B_ρ` at time `s`, the slice
integrand of `D(z₀,ρ)`. -/
@[expose] def lin34PressureSlice (p : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (ρ s : ℝ) : ℝ :=
  ∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ)

/-- The spatial `L^{3/2}` mass of the force group `p₇ + p₈` on `B_r` at time
`s`. -/
@[expose] def lin34ForceSliceIntegral (f : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (ρ r : ℝ) (hρ : 0 < ρ) (s : ℝ) : ℝ :=
  ∫ x in vec3Ball z.1 r, |lin34ForcePart f z.1 ρ hρ s x| ^ (3 / 2 : ℝ)

/-- The left-hand side of `eq:lin34-pointwise`, extended by zero outside
`J_r = (t₀ - r², t₀)`. -/
@[expose] def lin34F (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) : ℝ → ℝ :=
  Set.indicator (Ioc (z.2 - r ^ 2) z.2)
    (fun s => r⁻¹ ^ 2 * lin34PressureSlice p z r s)

/-- The velocity term of `eq:lin34-pointwise`. -/
@[expose] def lin34G (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (ρ : ℝ) : ℝ → ℝ :=
  fun s => ρ⁻¹ ^ 2 * lin34VelocitySlice u z ρ s

/-- The pressure term of `eq:lin34-pointwise`. -/
@[expose] def lin34H (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (ρ : ℝ) : ℝ → ℝ :=
  fun s => ρ⁻¹ ^ 2 * lin34PressureSlice p z ρ s

/-- The force term of `eq:lin34-pointwise`, extended by zero outside `J_r`. -/
@[expose] def lin34J (f : ParabolicPoint → Vec3) (z : ParabolicPoint) (ρ r : ℝ)
    (hρ : 0 < ρ) : ℝ → ℝ :=
  Set.indicator (Ioc (z.2 - r ^ 2) z.2)
    (fun s => r⁻¹ ^ 2 * lin34ForceSliceIntegral f z ρ r hρ s)

/-- `J_r ⊆ J_ρ` at the level of the left endpoints. -/
theorem lin34_time_subset {z : ParabolicPoint} {ρ r : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ) :
    z.2 - ρ ^ 2 ≤ z.2 - r ^ 2 := by
  have hsq : r ^ 2 ≤ ρ ^ 2 := by
    have h0 : (0 : ℝ) ≤ r := hr.le
    nlinarith only [h0, hrρ]
  linarith only [hsq]

/-- Integrating a function extended by zero over the larger time interval is
integrating it over the smaller one. -/
theorem lin34_integral_indicator_subinterval
    {a b c : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    (∫ t in Ioc a c, Set.indicator (Ioc b c) g t) = ∫ t in Ioc b c, g t := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  rw [Set.inter_eq_self_of_subset_left (Set.Ioc_subset_Ioc_left hab)]

private lemma lin34_indicator_integrable
    {a b c : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : Integrable g (volume.restrict (Ioc b c))) :
    Integrable (Set.indicator (Ioc b c) g) (volume.restrict (Ioc a c)) := by
  refine (integrable_indicator_iff measurableSet_Ioc).2 ?_
  change Integrable g ((volume.restrict (Ioc a c)).restrict (Ioc b c))
  rw [Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left (Set.Ioc_subset_Ioc_left hab)]
  exact hg

/-- The velocity slice quantity is integrable in time on `J_ρ`. -/
theorem lin34G_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    Integrable (lin34G u z ρ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hcyl := lin34_integrableOn_meanFree_cube (u := u) (x := z.1)
    (t := z.2) (r := ρ) hρ
    (tsai_integrable_velocity_on_cylinder hsol hρ hsub)
    (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsub)
  have hslice := lin34_slice_integrable_of_cylinder hcyl
  exact hslice.const_mul _

/-- The pressure slice quantity is integrable in time on `J_ρ`. -/
theorem lin34H_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    Integrable (lin34H p z ρ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hcyl := lin34_integrableOn_pressure_pow_cylinder hsol hρ hsub
  have hslice := lin34_slice_integrable_of_cylinder hcyl
  exact hslice.const_mul _

/-- The inner pressure quantity, extended by zero, is integrable on `J_ρ`. -/
theorem lin34F_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (_ : 0 < ρ) (hr : 0 < r)
    (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    Integrable (lin34F p z r) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hsubr : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr.le hrρ).trans hsub
  have hcyl := lin34_integrableOn_pressure_pow_cylinder hsol hr hsubr
  have hslice := lin34_slice_integrable_of_cylinder hcyl
  exact lin34_indicator_integrable (lin34_time_subset hr hrρ)
    (hslice.const_mul _)

/-- The force quantity, extended by zero, is integrable on `J_ρ`. -/
theorem lin34J_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    Integrable (lin34J f z ρ r hρ)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hcyl := lin34_force_integrableOn_cylinder hsol hρ hr hhalf hsub
  have hslice := lin34_slice_integrable_of_cylinder hcyl
  exact lin34_indicator_integrable
    (lin34_time_subset hr (by linarith only [hhalf, hρ]))
    (hslice.const_mul _)

/-- `C_hat(z₀,ρ)` of `eq:Chat` is the time integral of the velocity slice
quantity. -/
theorem lin34_pressureChat_eq_integral
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    pressureChat u z ρ =
      ∫ t, lin34G u z ρ t ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hcyl := lin34_integrableOn_meanFree_cube (u := u) (x := z.1)
    (t := z.2) (r := ρ) hρ
    (tsai_integrable_velocity_on_cylinder hsol hρ hsub)
    (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsub)
  exact pressureChat_eq_time_slice_integral hcyl

/-- `D(z₀,ρ)` is the time integral of the pressure slice quantity. -/
theorem lin34_pressureD_eq_integral
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    pressureD p z ρ =
      ∫ t, lin34H p z ρ t ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) :=
  pressureD_eq_time_slice_integral
    (lin34_integrableOn_pressure_pow_cylinder hsol hρ hsub)

/-- `D(z₀,r)` is the time integral over `J_ρ` of the extended inner pressure
quantity. -/
theorem lin34_pressureD_inner_eq_integral
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (_ : 0 < ρ) (hr : 0 < r)
    (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    pressureD p z r =
      ∫ t, lin34F p z r t ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
  have hsubr : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr.le hrρ).trans hsub
  have hD := pressureD_eq_time_slice_integral
    (lin34_integrableOn_pressure_pow_cylinder hsol hr hsubr)
  rw [hD]
  exact (lin34_integral_indicator_subinterval (lin34_time_subset hr hrρ)
    (fun s => r⁻¹ ^ 2 * lin34PressureSlice p z r s)).symm

end CKN
