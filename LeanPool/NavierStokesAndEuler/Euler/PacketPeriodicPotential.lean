/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity

@[expose] public section

/-! The literal angular vector potential on the periodic cylinder. -/

noncomputable section

namespace EulerPacketPeriodicPotential

open EulerSmoothLimit EulerPacketPiola EulerPacketAngularPotential EulerPacketCrossProduct
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  Set MeasureTheory
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

theorem liftIco_eq_periodicLift {E : Type*} (f : ℝ → E) (hf : Function.Periodic f P) :
    AddCircle.liftIco P 0 f = hf.lift := by
  funext θ
  change f (AddCircle.equivIco P 0 θ) = hf.lift θ
  exact (hf.lift_coe (AddCircle.equivIco P 0 θ)).symm.trans
    (congrArg hf.lift (AddCircle.coe_equivIco (p := P) (a := 0) (y := θ)))

def field (m : Space → Space) (A : LiftDomain P → Space) (x : LiftDomain P) : Space :=
  AddCircle.liftIco P 0 (potential P (m x.1) (fun θ => A (x.1,(θ : AddCircle P)))) x.2

omit [Fact (0 < P)] in
theorem angle_periodic (A : LiftDomain P → Space) (y : Space) :
    Function.Periodic (fun θ : ℝ => A (y,(θ : AddCircle P))) P := by
  intro θ
  change A (y,((θ+P : ℝ) : AddCircle P)) = A (y,(θ : AddCircle P))
  rw [AddCircle.coe_add_period]

theorem field_cover (m : Space → Space) (A : LiftDomain P → Space)
    (hA : Continuous A)
    (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y,(θ : AddCircle P))) = 0)
    (z : LiftTangent) :
    field P m A (coveringMap P z) =
      coveringPotential P m (localFieldLift P A 0) z := by
  have hAc : Continuous (fun θ : ℝ => A (z.1,(θ : AddCircle P))) :=
    hA.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))
  have hper := potential_periodic P (m z.1) _ hAc (angle_periodic P A z.1) (hmean z.1)
  change AddCircle.liftIco P 0 (potential P (m z.1) (fun θ => A (z.1,(θ : AddCircle P))))
    (z.2 : AddCircle P) = _
  rw [liftIco_eq_periodicLift P _ hper, Function.Periodic.lift_coe]
  simp only [coveringPotential, localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add]

theorem field_smooth (m : Space → Space) (A : LiftDomain P → Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x))
    (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y,(θ : AddCircle P))) = 0)
    (x : LiftDomain P) : ContDiff ℝ ∞ (localFieldLift P (field P m A) x) := by
  have hAc := smoothField_continuous P A hA
  have hQ := coveringPotential_contDiff P (le_of_lt (Fact.out : 0 < P)) m _ hm hnz (hA 0)
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have hx : x = coveringMap P (x.1,θ) := by
    apply Prod.ext
    · rfl
    · exact hθ.symm
  rw [hx, localFieldLift_cover]
  have he : localFieldLift P (field P m A) 0 = coveringPotential P m (localFieldLift P A 0) := by
    funext z
    simpa only [localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add, coveringMap] using
      field_cover P m A hAc hmean z
  rw [he]
  exact hQ.comp (contDiff_const.add contDiff_id)

theorem field_continuous (m : Space → Space) (A : LiftDomain P → Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x))
    (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y,(θ : AddCircle P))) = 0) :
    Continuous (field P m A) :=
  smoothField_continuous P _ (field_smooth P m A hm hnz hA hmean)

theorem field_vanishes (m : Space → Space) (A : LiftDomain P → Space)
    (y : Space) (hy : ∀ θ : AddCircle P, A (y,θ)=0) (θ : AddCircle P) :
    field P m A (y,θ)=0 := by
  unfold field
  have hzero : (fun s : ℝ => A (y,(s : AddCircle P))) = fun _ => 0 := funext fun s => hy s
  rw [hzero, potential_zero]
  rfl

/-- Angular integration preserves the compact spatial support of the input. -/
theorem field_compact (m : Space → Space) (A : LiftDomain P → Space)
    (hA : HasCompactSupport A) : HasCompactSupport (field P m A) := by
  let K : Set Space := Prod.fst '' tsupport A
  have hK : IsCompact K := hA.image continuous_fst
  apply HasCompactSupport.intro (hK.prod (isCompact_univ : IsCompact (univ : Set (AddCircle P))))
  intro x hx
  have hy : x.1 ∉ K := fun h => hx ⟨h,mem_univ _⟩
  apply field_vanishes P m A x.1 _ x.2
  intro θ
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  exact hy ⟨(x.1,θ),hs,rfl⟩

/-- The actual angular derivative of the genuine periodic potential. -/
theorem field_angle_derivative (m : Space → Space) (A : LiftDomain P → Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x))
    (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y,(θ : AddCircle P))) = 0)
    (x : LiftDomain P) :
    fieldDerivative P (0,1) (field P m A) x = potentialMultiplier (m x.1) (A x) := by
  have hAc := smoothField_continuous P A hA
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have hx : x = coveringMap P (x.1,θ) := by
    apply Prod.ext
    · rfl
    · exact hθ.symm
  rw [hx]
  unfold fieldDerivative
  rw [fderiv_localFieldLift_cover]
  have he : localFieldLift P (field P m A) 0 = coveringPotential P m (localFieldLift P A 0) := by
    funext z
    simpa only [localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add, coveringMap] using
      field_cover P m A hAc hmean z
  rw [he]
  simpa only [localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add, coveringMap] using
    coveringPotential_angle_derivative P m _ (x.1,θ)
    ((hA 0).continuous.comp (continuous_const.prodMk continuous_id))
    ((coveringPotential_contDiff P (le_of_lt (Fact.out : 0 < P)) m _ hm hnz (hA 0)).differentiable
      (by simp) _)

end EulerPacketPeriodicPotential
