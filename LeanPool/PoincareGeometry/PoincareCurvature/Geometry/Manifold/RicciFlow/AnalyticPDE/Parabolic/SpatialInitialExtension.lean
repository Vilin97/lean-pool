/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace

/-!
# Time-independent extensions of spatial `C^{2,α}` data

This file packages bounded spatial `C^{2,α}` data by its genuine first and
second Frechet derivatives and a common Hölder modulus.  Regard the data as
constant in time.  The resulting four-jet belongs to the finite-cylinder
parabolic `C^{2+α,1+α/2}` Banach space and its canonical initial trace is the
original spatial function.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Bounded spatial `C^{2,α}` data, including the actual first and second
Frechet derivatives and one uniform Hölder constant for all three fields. -/
structure BoundedSpatialC2AlphaData (X E : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) where
  value : BoundedContinuousFunction X E
  spaceDeriv : BoundedContinuousFunction X (X →L[ℝ] E)
  spaceSecondDeriv : BoundedContinuousFunction X (X →L[ℝ] X →L[ℝ] E)
  holderConstant : ℝ
  holderConstant_nonneg : 0 ≤ holderConstant
  value_holder : ∀ x y,
    ‖value x - value y‖ ≤ holderConstant * dist x y ^ α
  spaceDeriv_holder : ∀ x y,
    ‖spaceDeriv x - spaceDeriv y‖ ≤ holderConstant * dist x y ^ α
  spaceSecondDeriv_holder : ∀ x y,
    ‖spaceSecondDeriv x - spaceSecondDeriv y‖ ≤
      holderConstant * dist x y ^ α
  hasFDerivAt_value : ∀ x,
    HasFDerivAt value (spaceDeriv x) x
  hasFDerivAt_spaceDeriv : ∀ x,
    HasFDerivAt spaceDeriv (spaceSecondDeriv x) x

namespace BoundedSpatialC2AlphaData

variable {α : ℝ}

/-- A bounded spatial Hölder field is parabolically Hölder after making it
constant in time. -/
theorem parabolicC0AlphaOn_snd
    (f : BoundedContinuousFunction X E) (H : ℝ) (hH : 0 ≤ H)
    (hα : 0 ≤ α)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α)
    (s : Set (ℝ × X)) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.2) s := by
  refine ⟨‖f‖, norm_nonneg _, H, hH, ?_⟩
  constructor
  · intro z hz
    exact f.norm_coe_le_norm z.2
  · intro p hp q hq
    calc
      ‖f p.2 - f q.2‖ ≤ H * dist p.2 q.2 ^ α := hholder p.2 q.2
      _ ≤ H * parabolicDistance p q ^ α := by
        apply mul_le_mul_of_nonneg_left _ hH
        exact Real.rpow_le_rpow
          (dist_nonneg : 0 ≤ dist p.2 q.2)
          (parabolicDistance.space_dist_le p q) hα

/-- The genuine time-independent second jet. -/
def timeIndependentSecondJet
    (D : BoundedSpatialC2AlphaData X E α) {t₀ T : ℝ} :
    ParabolicSecondJet (fun z : ℝ × X => D.value z.2)
      (parabolicFiniteCylinder X t₀ T) where
  timeDeriv := fun _ => 0
  spaceDeriv := fun z => D.spaceDeriv z.2
  spaceSecondDeriv := fun z => D.spaceSecondDeriv z.2
  hasTimeDeriv := by
    intro z hz
    simpa using (hasDerivWithinAt_const
      (x := z.1) (s := timeSliceDomain (parabolicFiniteCylinder X t₀ T) z.2)
      (c := D.value z.2))
  hasSpaceDeriv := by
    intro z hz
    exact (D.hasFDerivAt_value z.2).hasFDerivWithinAt
  hasSpaceSecondDeriv := by
    intro z hz
    exact (D.hasFDerivAt_spaceDeriv z.2).hasFDerivWithinAt

/-- A bounded spatial `C^{2,α}` datum, extended constantly in time, as a
finite-cylinder parabolic `C^{2+α,1+α/2}` element. -/
def timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hα : 0 < α) :
    FiniteParabolicC2AlphaBanach X E t₀ T α :=
  FiniteParabolicC2AlphaBanach.ofSecondJet
    (fun z : ℝ × X => D.value z.2)
    (D.timeIndependentSecondJet (t₀ := t₀) (T := T))
    (parabolicC0AlphaOn_snd D.value D.holderConstant
      D.holderConstant_nonneg hα.le D.value_holder _)
    (parabolicC0AlphaOn_snd (E := X →L[ℝ] E)
      D.spaceDeriv D.holderConstant
      D.holderConstant_nonneg hα.le D.spaceDeriv_holder _)
    (by
      simpa [timeIndependentSecondJet] using
        (parabolicC0AlphaOn_snd (E := X →L[ℝ] X →L[ℝ] E)
          D.spaceSecondDeriv D.holderConstant
          D.holderConstant_nonneg hα.le D.spaceSecondDeriv_holder
          (parabolicFiniteCylinder X t₀ T)))
    (by
      simpa [timeIndependentSecondJet] using
        (parabolicC0AlphaOn_snd (E := E)
          (0 : BoundedContinuousFunction X E) 0 le_rfl hα.le
          (by simp) (parabolicFiniteCylinder X t₀ T)))

@[simp]
theorem value_timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hα : 0 < α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    FiniteParabolicC2AlphaBanach.value
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z = D.value z.2 := by
  simpa [timeIndependentExtension, timeIndependentSecondJet] using
    (FiniteParabolicC2AlphaBanach.value_ofSecondJet
      (fun z : ℝ × X => D.value z.2)
      (D.timeIndependentSecondJet (t₀ := t₀) (T := T))
      (parabolicC0AlphaOn_snd D.value D.holderConstant
        D.holderConstant_nonneg hα.le D.value_holder _)
      (parabolicC0AlphaOn_snd (E := X →L[ℝ] E)
        D.spaceDeriv D.holderConstant
        D.holderConstant_nonneg hα.le D.spaceDeriv_holder _)
      (by
        simpa [timeIndependentSecondJet] using
          (parabolicC0AlphaOn_snd (E := X →L[ℝ] X →L[ℝ] E)
            D.spaceSecondDeriv D.holderConstant
            D.holderConstant_nonneg hα.le D.spaceSecondDeriv_holder
            (parabolicFiniteCylinder X t₀ T)))
      (by
        simpa [timeIndependentSecondJet] using
          (parabolicC0AlphaOn_snd (E := E)
            (0 : BoundedContinuousFunction X E) 0 le_rfl hα.le
            (by simp) (parabolicFiniteCylinder X t₀ T))) hz)

@[simp]
theorem spaceDeriv_timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hα : 0 < α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    FiniteParabolicC2AlphaBanach.spaceDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z = D.spaceDeriv z.2 := by
  change FiniteParabolicC2AlphaBanach.spaceDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z =
    (D.timeIndependentSecondJet (t₀ := t₀) (T := T)).spaceDeriv z
  unfold timeIndependentExtension
  apply FiniteParabolicC2AlphaBanach.spaceDeriv_ofSecondJet
  exact hz

@[simp]
theorem spaceSecondDeriv_timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hα : 0 < α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z =
        D.spaceSecondDeriv z.2 := by
  change FiniteParabolicC2AlphaBanach.spaceSecondDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z =
    (D.timeIndependentSecondJet (t₀ := t₀) (T := T)).spaceSecondDeriv z
  unfold timeIndependentExtension
  apply FiniteParabolicC2AlphaBanach.spaceSecondDeriv_ofSecondJet
  exact hz

@[simp]
theorem timeDeriv_timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hα : 0 < α)
    {z : ℝ × X} (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z = 0 := by
  change FiniteParabolicC2AlphaBanach.timeDeriv
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z =
    (D.timeIndependentSecondJet (t₀ := t₀) (T := T)).timeDeriv z
  unfold timeIndependentExtension
  apply FiniteParabolicC2AlphaBanach.timeDeriv_ofSecondJet
  exact hz

/-- The canonical trace of the time-independent extension is precisely the
original bounded spatial datum. -/
@[simp]
theorem initialTraceL_timeIndependentExtension
    (D : BoundedSpatialC2AlphaData X E α)
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) = D.value := by
  change ParabolicC0AlphaBanach.finiteInitialTrace hT hα
    (FiniteParabolicC2AlphaBanach.valueComponentL
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα)) = D.value
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _
    (BoundedContinuousFunction.const (↥(Set.Icc t₀ T)) D.value)
    (BoundedContinuousFunction.const (↥(Set.Icc t₀ T)) D.value).continuous]
  · simp
  · intro t
    ext x
    rw [BoundedContinuousFunction.const_apply']
    let z : ℝ × X := ((t : ℝ), x)
    have hz : z ∈ parabolicFiniteCylinder X t₀ T :=
      ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x
    calc
      D.value x = FiniteParabolicC2AlphaBanach.value
          (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) z := by
        rw [D.value_timeIndependentExtension hα hz]
      _ = ParabolicC0AlphaBanach.evalCLM z hz
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (D.timeIndependentExtension (t₀ := t₀) (T := T) hα)) := by
        rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
      _ = ParabolicC0AlphaBanach.finiteTimeSlice hα
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (D.timeIndependentExtension (t₀ := t₀) (T := T) hα)) t x := rfl

end BoundedSpatialC2AlphaData
end AnalyticPDE
end RicciFlow
