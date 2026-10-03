/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus

/-!
# Supports of space-time test functions

The integrability clauses of `def:sws` are stated on `tsupport φ` viewed as a
subset of the parabolic space-time, while the test-function class
`CKN.spaceTimeTestFunction` states its own support condition on the ordinary product
`Vec3 × ℝ`.  The two closed supports are the same set, but they are produced by
two different topology instances, so a proof has to move between them
explicitly; `CKN.tsupport_parabolic_eq` is the bridge, and this file packages
the consequences that every clause lemma needs:

* the closed support is compact and lies inside the space-time carrier;
* Lebesgue measure restricted to a compact set is finite, which is what turns
  every exponent-lowering step into an application of Hölder's inequality;
* the first and second spatial derivatives and the time derivative of a test
  function again have compact support inside that of the test function, are
  smooth, and are therefore bounded.

Boundedness is the form in which the test function enters: an integrand of
`def:sws` is an integrable field times a bounded factor coming from the test
function.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! ### Moving compactness between the parabolic and the product topology -/

/-- A parabolically compact set is compact for the product topology of the
space and time factors: the identity is a homeomorphism between the two. -/
theorem isCompact_prod_of_isCompact_parabolic {K : Set ParabolicPoint}
    (hK : IsCompact K) :
    IsCompact (show Set (Vec3 × ℝ) from K) := by
  rw [← parabolicHomeomorph.isCompact_preimage (s := (show Set (Vec3 × ℝ) from K))]
  rwa [parabolicHomeomorph_preimage]

/-- The closed support of a compactly supported function on space-time is
compact also when read in the parabolic topology, which is the form the
integrability clauses of `def:sws` use. -/
theorem isCompact_tsupport_parabolic {V : Type} [Zero V]
    {ψ : Vec3 × ℝ → V} (hψc : HasCompactSupport ψ) :
    IsCompact (tsupport (show ParabolicPoint → V from ψ)) := by
  have h : IsCompact (parabolicHomeomorph ⁻¹' (tsupport ψ)) :=
    parabolicHomeomorph.isCompact_preimage.2 hψc.isCompact
  rw [parabolicHomeomorph_preimage] at h
  rwa [tsupport_parabolic_eq]

/-- The parabolic closed support of a space-time test function lies inside the
space-time carrier. -/
theorem tsupport_parabolic_subset_spaceTimeSet {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → V}
    (hψ : ψ ∈ spaceTimeTestFunction (V := V) Ω I) :
    tsupport (show ParabolicPoint → V from ψ) ⊆ spaceTimeSet Ω I := by
  rw [tsupport_parabolic_eq]
  exact hψ.2.2

/-- Lebesgue measure restricted to a compact space-time set is a finite
measure.  Every use of Hölder's inequality below rests on this. -/
theorem isFiniteMeasure_restrict_of_isCompact {K : Set ParabolicPoint}
    (hK : IsCompact K) :
    IsFiniteMeasure (volume.restrict K) := by
  refine isFiniteMeasure_restrict.mpr ?_
  have h : (volume : Measure (Vec3 × ℝ)) (show Set (Vec3 × ℝ) from K) < ⊤ :=
    (isCompact_prod_of_isCompact_parabolic hK).measure_lt_top
  exact h.ne

/-! ### Supports of the derivatives of a test function -/

/-- The closed support of a time derivative lies in that of the function. -/
theorem tsupport_timePartial_subset (ψ : Vec3 × ℝ → ℝ) :
    tsupport (fun z : Vec3 × ℝ => timePartial ψ z) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hcon
  exact hz (timePartial_eq_zero_off_tsupport hcon)

/-- A second spatial derivative vanishes off the closed support. -/
theorem spatialSecondPartial_eq_zero_off_tsupport {ψ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i j : Fin 3) :
    spatialSecondPartial ψ i j z = 0 := by
  have hout : z ∉ tsupport (fun w : Vec3 × ℝ => spatialPartial ψ i w) := fun hmem =>
    hz (tsupport_spatialPartial_subset i hmem)
  exact spatialPartial_eq_zero_off_tsupport hout j

/-- The closed support of a second spatial derivative lies in that of the
function. -/
theorem tsupport_spatialSecondPartial_subset (ψ : Vec3 × ℝ → ℝ) (i j : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialSecondPartial ψ i j z) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hcon
  exact hz (spatialSecondPartial_eq_zero_off_tsupport hcon i j)

section CompactSupport

variable {ψ : Vec3 × ℝ → ℝ}

/-- A spatial derivative of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_spatialPartial (hψc : HasCompactSupport ψ) (i : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) :=
  hψc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_spatialPartial_subset i)

/-- The time derivative of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_timePartial (hψc : HasCompactSupport ψ) :
    HasCompactSupport (fun z : Vec3 × ℝ => timePartial ψ z) :=
  hψc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_timePartial_subset ψ)

/-- A second spatial derivative of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_spatialSecondPartial (hψc : HasCompactSupport ψ)
    (i j : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ => spatialSecondPartial ψ i j z) :=
  hψc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_spatialSecondPartial_subset ψ i j)

end CompactSupport

/-! ### Smoothness of the time derivative -/

/-- The time derivative of a smooth function on space-time is smooth.  This is
the time analogue of `CKN.spatialPartial_contDiff`. -/
theorem contDiff_timePartial {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial (show ParabolicPoint → ℝ from ψ) z) := by
  let F : (Vec3 × ℝ) → ℝ → ℝ := fun z s => ψ (z.1, s)
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun w : (Vec3 × ℝ) × ℝ => (w.1.1, w.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    convert hψ.comp hmap using 1
    funext w
    rfl
  have hderiv := hF.fderiv_apply
    (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := (1 : ℝ)))
    (by simp)
  simpa only [F, timePartial, Function.uncurry] using hderiv

/-! ### Bounds on a test function and its derivatives -/

section Bounds

variable {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ}

/-- A space-time test function is bounded. -/
theorem exists_bound_of_mem_spaceTimeTestFunction
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    ∃ C : ℝ, ∀ z : Vec3 × ℝ, ‖ψ z‖ ≤ C :=
  hψ.2.1.exists_bound_of_continuous hψ.1.continuous

/-- Each spatial derivative of a space-time test function is bounded. -/
theorem exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i : Fin 3) :
    ∃ C : ℝ, ∀ z : Vec3 × ℝ, ‖spatialPartial ψ i z‖ ≤ C :=
  (hasCompactSupport_spatialPartial hψ.2.1 i).exists_bound_of_continuous
    (spatialPartial_contDiff hψ.1 i).continuous

/-- The time derivative of a space-time test function is bounded. -/
theorem exists_bound_timePartial_of_mem_spaceTimeTestFunction
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    ∃ C : ℝ, ∀ z : Vec3 × ℝ, ‖timePartial ψ z‖ ≤ C :=
  (hasCompactSupport_timePartial hψ.2.1).exists_bound_of_continuous
    (contDiff_timePartial hψ.1).continuous

/-- Each second spatial derivative of a space-time test function is bounded. -/
theorem exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i j : Fin 3) :
    ∃ C : ℝ, ∀ z : Vec3 × ℝ, ‖spatialSecondPartial ψ i j z‖ ≤ C :=
  (hasCompactSupport_spatialSecondPartial hψ.2.1 i j).exists_bound_of_continuous
    (spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i) j).continuous

end Bounds

end CKN
