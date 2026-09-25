/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.PartitionAverageConstants
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable

/-! # Partition Averages Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open scoped BigOperators
open MeasureTheory

/-!
# Restriction-Carrier Partition-Average Fluctuation Definitions

Definitions and equality lemmas for the restriction-carrier engineering
partition-average fluctuation endpoints. Source-manuscript counterparts live
in the source-specific API.
-/

noncomputable section

/-- The origin observable centered by its expectation. -/
noncomputable def restrictionCenteredOriginObservable {d : ℕ} (P : RestrictionCoeffLaw d)
    (n : ℤ) (X : Set (Vec d) → RegCoeffField d → ℝ) : RegCoeffField d → ℝ :=
  fun a => X (cubeSet (originCube d n)) a -
    ∫ b, X (cubeSet (originCube d n)) b ∂P

/-- The uncentered descendant partition average over the scale-`n` descendants
of the origin cube at scale `m`. -/
noncomputable def restrictionDescendantAverage {d : ℕ}
    (n m : ℤ) (X : Set (Vec d) → RegCoeffField d → ℝ) : RegCoeffField d → ℝ :=
  fun a =>
    ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale (originCube d m) n, X (cubeSet R) a

/-- The centered descendant partition average over the scale-`n` descendants of
the origin cube at scale `m`. -/
noncomputable def restrictionCenteredDescendantAverage {d : ℕ} (P : RestrictionCoeffLaw d)
    (n m : ℤ) (X : Set (Vec d) → RegCoeffField d → ℝ) : RegCoeffField d → ℝ :=
  fun a =>
    ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale (originCube d m) n,
        (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d n)) b ∂P)

/-- The uncentered descendant partition average over the scale-`n` descendants
of an arbitrary parent cube. -/
noncomputable def restrictionDescendantAverageOnCube {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (X : Set (Vec d) → RegCoeffField d → ℝ) :
    RegCoeffField d → ℝ :=
  fun a =>
    ((descendantsAtScale Q n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale Q n, X (cubeSet R) a

/-- The centered descendant partition average over the scale-`n` descendants
of an arbitrary parent cube, centered by the origin scale-`n` expectation. -/
noncomputable def restrictionCenteredDescendantAverageOnCube {d : ℕ} (P : RestrictionCoeffLaw d)
    (Q : TriadicCube d) (n : ℤ) (X : Set (Vec d) → RegCoeffField d → ℝ) :
    RegCoeffField d → ℝ :=
  fun a =>
    ((descendantsAtScale Q n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale Q n,
        (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d n)) b ∂P)

/-- A.e.-equal observables have the same centered origin observable. -/
theorem restrictionCenteredOriginObservable_ae_eq_of_ae_eq {d : ℕ} {P : RestrictionCoeffLaw d}
    {n : ℤ} {X Y : Set (Vec d) → RegCoeffField d → ℝ}
    (hXY :
      X (cubeSet (originCube d n)) =ᵐ[P] Y (cubeSet (originCube d n))) :
    restrictionCenteredOriginObservable P n X =ᵐ[P] restrictionCenteredOriginObservable P n Y := by
  have hμ :
      ∫ b, X (cubeSet (originCube d n)) b ∂P =
        ∫ b, Y (cubeSet (originCube d n)) b ∂P :=
    integral_congr_ae hXY
  filter_upwards [hXY] with a ha
  simp [restrictionCenteredOriginObservable, ha, hμ]

/-- A.e.-equal descendant observables have the same uncentered descendant
average on a fixed parent cube. -/
theorem restrictionDescendantAverageOnCube_ae_eq_of_ae_eq {d : ℕ} {P : RestrictionCoeffLaw d}
    {Q : TriadicCube d} {n : ℤ} {X Y : Set (Vec d) → RegCoeffField d → ℝ}
    (hXY :
      ∀ R, R ∈ descendantsAtScale Q n →
        X (cubeSet R) =ᵐ[P] Y (cubeSet R)) :
    restrictionDescendantAverageOnCube Q n X =ᵐ[P] restrictionDescendantAverageOnCube Q n Y := by
  have hAll :
      ∀ᵐ a ∂P, ∀ R, R ∈ descendantsAtScale Q n →
        X (cubeSet R) a = Y (cubeSet R) a :=
    ae_forall_mem_finset (P := P) (descendantsAtScale Q n) hXY
  filter_upwards [hAll] with a ha
  unfold restrictionDescendantAverageOnCube
  congr 1
  exact Finset.sum_congr rfl fun R hR => by
    simp [ha R hR]

/-- A.e.-equal descendant observables, with a.e.-equal origin representatives
for the centering constant, have the same centered descendant average on a
fixed parent cube. -/
theorem restrictionCenteredDescendantAverageOnCube_ae_eq_of_ae_eq {d : ℕ} {P : RestrictionCoeffLaw d}
    {Q : TriadicCube d} {n : ℤ} {X Y : Set (Vec d) → RegCoeffField d → ℝ}
    (hOrigin :
      X (cubeSet (originCube d n)) =ᵐ[P] Y (cubeSet (originCube d n)))
    (hDesc :
      ∀ R, R ∈ descendantsAtScale Q n →
        X (cubeSet R) =ᵐ[P] Y (cubeSet R)) :
    restrictionCenteredDescendantAverageOnCube P Q n X =ᵐ[P]
      restrictionCenteredDescendantAverageOnCube P Q n Y := by
  have hμ :
      ∫ b, X (cubeSet (originCube d n)) b ∂P =
        ∫ b, Y (cubeSet (originCube d n)) b ∂P :=
    integral_congr_ae hOrigin
  have hAll :
      ∀ᵐ a ∂P, ∀ R, R ∈ descendantsAtScale Q n →
        X (cubeSet R) a = Y (cubeSet R) a :=
    ae_forall_mem_finset (P := P) (descendantsAtScale Q n) hDesc
  filter_upwards [hAll] with a ha
  unfold restrictionCenteredDescendantAverageOnCube
  rw [hμ]
  congr 1
  exact Finset.sum_congr rfl fun R hR => by
    simp [ha R hR]

/-- The centered descendant average on an arbitrary parent cube is the
uncentered descendant average minus the origin-cube centering constant. -/
theorem restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {n : ℤ}
    (hnQ : n ≤ Q.scale) (X : Set (Vec d) → RegCoeffField d → ℝ) :
    restrictionCenteredDescendantAverageOnCube P Q n X =
      fun a =>
        restrictionDescendantAverageOnCube Q n X a -
          ∫ b, X (cubeSet (originCube d n)) b ∂P := by
  let s := descendantsAtScale Q n
  let μ0 : ℝ := ∫ b, X (cubeSet (originCube d n)) b ∂P
  have hs_nonempty : s.Nonempty := by
    simpa [s] using descendantsAtScale_nonempty Q hnQ
  have hs_card_ne_zero : ((s.card : ℝ)) ≠ 0 := by
    exact_mod_cast hs_nonempty.card_ne_zero
  funext a
  rw [restrictionCenteredDescendantAverageOnCube, restrictionDescendantAverageOnCube]
  change
    ((s.card : ℝ)⁻¹ * ∑ R ∈ s, (X (cubeSet R) a - μ0)) =
      ((s.card : ℝ)⁻¹ * ∑ R ∈ s, X (cubeSet R) a) - μ0
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp [nsmul_eq_mul, μ0]
  field_simp [hs_card_ne_zero]

/-- The response observable `U ↦ J(U,p,q;·)` used in the special partition
average corollary. -/
noncomputable abbrev restrictionResponseJCubeObservable {d : ℕ} (p q : Vec d) :
    Set (Vec d) → RegCoeffField d → ℝ :=
  fun U a => ResponseJ U p q a.toFun

/-- The response observable on the origin cube, centered by its expectation. -/
noncomputable abbrev restrictionCenteredResponseJOriginObservable {d : ℕ} (P : RestrictionCoeffLaw d)
    (n : ℤ) (p q : Vec d) : RegCoeffField d → ℝ :=
  restrictionCenteredOriginObservable P n (restrictionResponseJCubeObservable p q)

/-- The uncentered partition average of the response functional over scale-`n`
descendants of the origin cube at scale `m`. -/
noncomputable abbrev restrictionResponseJDescendantAverage {d : ℕ}
    (n m : ℤ) (p q : Vec d) : RegCoeffField d → ℝ :=
  restrictionDescendantAverage n m (restrictionResponseJCubeObservable p q)

/-- The centered partition average of the response functional over scale-`n`
descendants of the origin cube at scale `m`. -/
noncomputable abbrev restrictionCenteredResponseJDescendantAverage {d : ℕ} (P : RestrictionCoeffLaw d)
    (n m : ℤ) (p q : Vec d) : RegCoeffField d → ℝ :=
  restrictionCenteredDescendantAverage P n m (restrictionResponseJCubeObservable p q)

/-- Exact Chapter 4 color-count constant multiplying the genuinely `L^p`
Rosenthal term in the partition-average fluctuation bound. -/
noncomputable def rosenthalDescendantsAtScaleLpConst
    (d : ℕ) (k : ℤ) (p : ℕ) : ℝ :=
  2 * (p : ℝ) * ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) ^ (1 - 1 / (p : ℝ))

/-- Exact Chapter 4 color-count constant multiplying the square-function
Rosenthal term in the partition-average fluctuation bound. -/
noncomputable def rosenthalDescendantsAtScaleSqrtConst
    (d : ℕ) (k : ℤ) (p : ℕ) : ℝ :=
  4 * rosenthalBennettIntegralConst *
    (Real.sqrt p * Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)))

end

end Ch04
end Book
end Homogenization
