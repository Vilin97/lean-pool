/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.MeasurableObservable
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich

/-!
# The globally bounded clamped observable

`efronStein_transfer_ae_restriction` requires the product observable to be **globally**
bounded (`∀ y, |G y| ≤ M`), not merely a.e. bounded.  The raw product observable
`rawPhaseObservable` is only bounded on the a.e. event where the recombined field
is elliptic, so we clamp it to `[0, C]` with `C := 2(Θ‖p‖² + ‖q‖²)` — the exact
`C1′` sandwich bound for the coarse quadratic of a `(1,Θ)`-elliptic field.

The clamp is the identity exactly where it matters: for any measurable, a.e.-
`(1,Θ)`-elliptic field `b` the truncated glued field `glueField ℓ σ Θ b` is
genuinely `(1,Θ)`-elliptic on the cube, so `phaseObservable ℓ σ m P b ∈ [0, C]`
(`phaseObservable_mem_Icc`), and hence `clampedPhaseObservable (R b) = phaseObservable b`.
-/

@[expose] public section

open Homogenization
open scoped MeasureTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## Per-field ellipticity and boundedness of the fixed-phase observable -/

/-- The truncated glued field of a measurable field is genuinely `(1,Θ)`-elliptic
on the cube. -/
theorem isEllipticFieldOn_glueField_of_field {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (hΘ : 1 ≤ Θ) {b : CoeffField d}
    (hbmeas : ∀ i j : Fin d, Measurable fun x : Vec d => b x i j) :
    IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (glueField ℓ σ Θ b) := by
  classical
  have hcorrM : MeasurableSet (corridorSet ℓ σ) := measurableSet_corridorSet ℓ σ
  have hUmeas : MeasurableSet (cubeSet (originCube d m)) :=
    measurableSet_cubeSet (originCube d m)
  have hmeasField :
      Measurable (fun x : Vec d => fun i j =>
        if x ∈ cubeSet (originCube d m) then (corridorField ℓ σ b) x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have hrw :
        (fun x : Vec d =>
          if x ∈ cubeSet (originCube d m) then (corridorField ℓ σ b) x i j else 0)
          = fun x : Vec d =>
            if x ∈ cubeSet (originCube d m) then
              (if x ∈ corridorSet ℓ σ then (1 : Mat d) i j else b x i j) else 0 := by
      funext x
      by_cases hxU : x ∈ cubeSet (originCube d m)
      · simp only [hxU, if_true]
        by_cases hxc : x ∈ corridorSet ℓ σ
        · rw [corridorField_apply_of_mem hxc]; simp [hxc]
        · rw [corridorField_apply_of_not_mem hxc]; simp [hxc]
      · simp [hxU]
    rw [hrw]
    exact Measurable.ite hUmeas
      (Measurable.ite hcorrM measurable_const (hbmeas i j)) measurable_const
  exact isEllipticFieldOn_ellipticTruncate hUmeas hΘ hmeasField

/-- The truncated glued field agrees a.e. on the cube with the corridor field. -/
theorem glueField_ae_eq_corridorField {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (hΘ : 1 ≤ Θ) {b : CoeffField d}
    (hbell : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      IsEllipticMatrix 1 Θ (b x)) :
    glueField ℓ σ Θ b
      =ᵐ[MeasureTheory.volume.restrict (cubeSet (originCube d m))]
    corridorField ℓ σ b := by
  refine ellipticTruncate_ae_eq ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hbell] with x hx
  by_cases hxc : x ∈ corridorSet ℓ σ
  · rw [corridorField_apply_of_mem hxc]; exact isEllipticMatrix_one hΘ
  · rw [corridorField_apply_of_not_mem hxc]; exact hx

/-- The fixed-phase observable equals the coarse quadratic of the truncated glued
field (they agree a.e., so the coarse matrices coincide). -/
theorem phaseObservable_eq_blockVecDot_glueField {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (hΘ : 1 ≤ Θ) (P : BlockVec d) {b : CoeffField d}
    (hbell : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      IsEllipticMatrix 1 Θ (b x)) :
    phaseObservable ℓ σ m P b
      = blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (glueField ℓ σ Θ b)) P) := by
  unfold phaseObservable
  rw [coarseBlockMatrix_congr_of_ae_eq (glueField_ae_eq_corridorField hΘ hbell).symm]

/-- **C1′ bounds for the fixed-phase observable.**  For any measurable, a.e.
`(1,Θ)`-elliptic field, the observable lands in `[0, 2(Θ‖p‖² + ‖q‖²)]`. -/
theorem phaseObservable_mem_Icc [NeZero d] {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (hΘ : 1 ≤ Θ) (P : BlockVec d) {b : CoeffField d}
    (hbmeas : ∀ i j : Fin d, Measurable fun x : Vec d => b x i j)
    (hbell : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      IsEllipticMatrix 1 Θ (b x)) :
    0 ≤ phaseObservable ℓ σ m P b
      ∧ phaseObservable ℓ σ m P b ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  rw [phaseObservable_eq_blockVecDot_glueField hΘ P hbell]
  refine ⟨zero_le_blockVecDot_coarseBlockMatrix_cube
      (isEllipticFieldOn_glueField_of_field hΘ hbmeas) P,
    blockVecDot_coarseBlockMatrix_cube_le
      (isEllipticFieldOn_glueField_of_field hΘ hbmeas) P⟩

/-! ## The clamped observable -/

/-- The bound constant `C = 2(Θ‖p‖² + ‖q‖²)` for the coarse quadratic. -/
noncomputable def phaseBound (Θ : ℝ) (P : BlockVec d) : ℝ :=
  2 * (Θ * vecNormSq P.1 + vecNormSq P.2)

theorem phaseBound_nonneg {Θ : ℝ} (hΘ : 1 ≤ Θ) (P : BlockVec d) :
    0 ≤ phaseBound Θ P := by
  have h1 : (0 : ℝ) ≤ Θ * vecNormSq P.1 :=
    mul_nonneg (by linarith) (vecNormSq_nonneg _)
  have h2 : (0 : ℝ) ≤ vecNormSq P.2 := vecNormSq_nonneg _
  unfold phaseBound; linarith

/-- The globally bounded product observable: `rawPhaseObservable` clamped to
`[0, phaseBound Θ P]`. -/
noncomputable def clampedPhaseObservable (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → CoeffField d) : ℝ :=
  max 0 (min (phaseBound Θ P) (rawPhaseObservable ℓ σ Θ m P K y))

theorem measurable_clampedPhaseObservable {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (P : BlockVec d) (K : Finset (Fin d → ℤ)) :
    Measurable
      (fun y : {k // k ∈ K} → CoeffField d => clampedPhaseObservable ℓ σ Θ m P K y) := by
  unfold clampedPhaseObservable
  exact measurable_const.max (measurable_const.min (measurable_rawPhaseObservable P K))

/-- The clamped observable is globally bounded by `phaseBound Θ P`. -/
theorem abs_clampedPhaseObservable_le {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hΘ : 1 ≤ Θ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ)) (y : {k // k ∈ K} → CoeffField d) :
    |clampedPhaseObservable ℓ σ Θ m P K y| ≤ phaseBound Θ P := by
  unfold clampedPhaseObservable
  rw [abs_le]
  refine ⟨le_trans (by linarith [phaseBound_nonneg hΘ P]) (le_max_left _ _),
    max_le (phaseBound_nonneg hΘ P) (min_le_left _ _)⟩

/-- **Clamp is the identity on the diagonal.**  For any measurable, a.e.
`(1,Θ)`-elliptic field `b`, the clamped observable on the restriction tuple `R b`
equals the fixed-phase observable of `b`. -/
theorem clampedPhaseObservable_restrict_eq_of_field [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (b : CoeffField d)
    (hbmeas : ∀ i j : Fin d, Measurable fun x : Vec d => b x i j)
    (hbell : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      IsEllipticMatrix 1 Θ (b x)) :
    clampedPhaseObservable ℓ σ Θ m P K
        (fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) b)
      = phaseObservable ℓ σ m P b := by
  unfold clampedPhaseObservable
  rw [rawPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK b hbmeas hbell]
  obtain ⟨hlo, hhi⟩ := phaseObservable_mem_Icc hΘ P hbmeas hbell
  rw [min_eq_right (by simpa [phaseBound] using hhi), max_eq_right hlo]

end Homogenization
