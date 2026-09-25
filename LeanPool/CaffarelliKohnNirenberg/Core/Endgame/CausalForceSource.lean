/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ForceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCutoff
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# The causal cutoff force term

Local force measurability on the unit cylinder suffices for the globally
extended source, because the cutoff vanishes outside that cylinder in the
past. Its numerical Morrey bound follows from the original small-data sum.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- A scalar component of the cutoff force, extended by zero to future times. -/
def causalForceComponent (φ : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (i : Fin 3) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => φ z * f z i)

/-- The causal force component vanishes outside the unit cylinder. -/
theorem causalForceComponent_zero_outside_unit
    {φ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0)
    (i : Fin 3) {z : ParabolicPoint} (hz : z ∉ parabolicCylinder (0 : Vec3) 0 1) :
    causalForceComponent φ f i z = 0 := by
  unfold causalForceComponent
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht, hsupp z ht hz, zero_mul]
  · exact indicator_of_notMem ht _

/-- Global measurability of the causal force uses only local measurability
of the original force on the unit cylinder. -/
theorem causalForceComponent_aemeasurable
    {φ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hφ : AEMeasurable φ volume)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0)
    (i : Fin 3)
    (hf : AEMeasurable (fun z => f z i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 1))) :
    AEMeasurable (causalForceComponent φ f i) volume := by
  have hQ : MeasurableSet (parabolicCylinder (0 : Vec3) 0 1) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hPast : MeasurableSet {z : ParabolicPoint | z.2 ≤ 0} :=
    (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  have hlocal : AEMeasurable (causalForceComponent φ f i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 1)) :=
    (hφ.restrict.mul hf).indicator hPast
  have hi := (aemeasurable_indicator_iff hQ).mpr hlocal
  have heq : (parabolicCylinder (0 : Vec3) 0 1).indicator (causalForceComponent φ f i) =
      causalForceComponent φ f i := by
    funext z
    by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 1
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, causalForceComponent_zero_outside_unit hsupp i hz]
  rwa [heq] at hi

/-- A cutoff taking values in `[0,1]` in the past yields pointwise force
domination, including after extension by zero. -/
theorem abs_causalForceComponent_le
    {φ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hφ : ∀ z, z.2 ≤ 0 → 0 ≤ φ z ∧ φ z ≤ 1)
    (i : Fin 3) (z : ParabolicPoint) :
    |causalForceComponent φ f i z| ≤ vec3EuclideanNorm (f z) := by
  have hcomponent : |f z i| ≤ vec3EuclideanNorm (f z) :=
    Real.abs_le_sqrt (Finset.single_le_sum
      (fun j _ => sq_nonneg (f z j)) (Finset.mem_univ i))
  unfold causalForceComponent
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht, abs_mul, abs_of_nonneg (hφ z ht).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hφ z ht).2).trans hcomponent
  · rw [indicator_of_notMem ht, abs_zero]
    exact vec3EuclideanNorm_nonneg _

/-- The concrete causal cutoff force component satisfies the uniform paper
source Morrey bound. -/
theorem causalForceComponent_paper_morrey_le
    (q ε₀ : ℝ) (hq : 5 / 2 < q)
    {φ : ParabolicPoint → ℝ} {u f : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    (hφ : AEMeasurable φ volume)
    (hφrange : ∀ z, z.2 ≤ 0 → 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (i : Fin 3)
    (hf : AEMeasurable (fun z => f z i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 1))) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ)) (causalForceComponent φ f i) ≤
      forceSourceMorreyBound q ε₀ := by
  exact force_source_paper_morrey_le_of_small_data q ε₀ hq
    (causalForceComponent_aemeasurable hφ hsupp i hf) hsmall
    (Filter.Eventually.of_forall (abs_causalForceComponent_le hφrange i))
    (fun _ hz => causalForceComponent_zero_outside_unit hsupp i hz)

/-- Suitable-solution local energy data supply all force measurability needed
for the concrete causal source estimate. -/
theorem causal_force_source_of_suitableWeakSolution
    (q ε₀ : ℝ) (hq : 5 / 2 < q)
    {Ω : Set Vec3} {I : Set ℝ} {φ : ParabolicPoint → ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : AEMeasurable φ volume)
    (hφrange : ∀ z, z.2 ≤ 0 → 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    ∀ i : Fin 3, AEMeasurable (causalForceComponent φ f i) volume ∧
      morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ)) (causalForceComponent φ f i) ≤
        forceSourceMorreyBound q ε₀ := by
  obtain ⟨Ω', J, hbox, _hJ, hunit⟩ := exists_localBox_around_closed_unit hsol.1 hsol.2.1 hdom
  have hfbox := (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.1
  have hfunit : AEStronglyMeasurable f
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 1)) :=
    hfbox.mono_measure (Measure.restrict_mono (subset_closure.trans hunit) le_rfl)
  intro i
  have hfi : AEMeasurable (fun z => f z i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 1)) :=
    ((continuous_apply i).comp_aestronglyMeasurable hfunit).aemeasurable
  exact ⟨causalForceComponent_aemeasurable hφ hsupp i hfi,
    causalForceComponent_paper_morrey_le q ε₀ hq hφ hφrange hsupp hsmall i hfi⟩

end CKN.Core.Endgame
