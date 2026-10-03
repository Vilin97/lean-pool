/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteBasis

/-! # Localized Finite Basis -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open Section54.VarianceBoundGoodScale

/-!
# Localized finite-basis reduction

This file upgrades the one-cube finite-basis reduction to the finite maximum
over the scale-`n` descendants of the scale-`m` origin cube.
-/

noncomputable section

/-- The finite maximum, over descendants, of the coordinate/pair probe sum
controlling the limiting-normalized quadratic form. -/
noncomputable def localizedLimitNormalizedJProbeSumMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (m n : ℕ) : RegCoeffField d → ℝ :=
  fun a =>
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    if hD : D.Nonempty then
      D.sup' hD (fun R => limitNormalizedJProbeSum hP hStruct R a)
    else
      0

/-- The localized maximum of the normalized coordinate/pair probe sum. -/
noncomputable def localizedLimitNormalizedJNormalizedProbeSumMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (m n : ℕ) : RegCoeffField d → ℝ :=
  fun a =>
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    if hD : D.Nonempty then
      D.sup' hD (fun R => limitNormalizedJNormalizedProbeSum hP hStruct R a)
    else
      0

theorem limitNormalizedJProbeSum_le_localizedLimitNormalizedJProbeSumMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ))
    (a : RegCoeffField d) :
    limitNormalizedJProbeSum hP hStruct R a ≤
      localizedLimitNormalizedJProbeSumMax hP hStruct m n a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty := ⟨R, by simpa [D] using hR⟩
  dsimp [localizedLimitNormalizedJProbeSumMax]
  simp only [D, hD, dite_true]
  exact Finset.le_sup' (s := D)
    (f := fun S => limitNormalizedJProbeSum hP hStruct S a)
    (b := R) (by simpa [D] using hR)

/-- The localized maximum over any fixed unit vector is a.s. controlled by the
localized finite-probe maximum.  This is the Lean form of the finite-basis
reduction used in Theorem `t.homogenization.quenched`. -/
theorem localizedLimitNormalizedJMax_le_probeSumMax_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m)
    (e : FullBlockVec d) (he : dotProduct e e ≤ 1) :
    (localizedLimitNormalizedJMax hP hStruct m n e) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        (Fintype.card (BlockCoord d) : ℝ) *
          localizedLimitNormalizedJProbeSumMax hP hStruct m n a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  have hAll :
      ∀ᵐ a ∂P, ∀ R ∈ D,
        limitNormalizedBlockJObservable hP hStruct R e a ≤
          (Fintype.card (BlockCoord d) : ℝ) *
            limitNormalizedJProbeSum hP hStruct R a := by
    rw [Filter.eventually_all_finset]
    intro R _hR
    simpa using!
      limitNormalizedBlockJObservable_le_probeSum_ae hP hStruct hΓ R e he
  filter_upwards [hAll] with a hAll_a
  have hloc_eq :
      localizedLimitNormalizedJMax hP hStruct m n e a =
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R e a) := by
    dsimp [localizedLimitNormalizedJMax]
    simp [D, hD]
  have hprobe_eq :
      localizedLimitNormalizedJProbeSumMax hP hStruct m n a =
        D.sup' hD (fun R => limitNormalizedJProbeSum hP hStruct R a) := by
    dsimp [localizedLimitNormalizedJProbeSumMax]
    simp [D, hD]
  rw [hloc_eq, hprobe_eq]
  refine Finset.sup'_le hD _ ?_
  intro R hR
  calc
    limitNormalizedBlockJObservable hP hStruct R e a
        ≤ (Fintype.card (BlockCoord d) : ℝ) *
            limitNormalizedJProbeSum hP hStruct R a := hAll_a R hR
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          D.sup' hD (fun S => limitNormalizedJProbeSum hP hStruct S a) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (s := D)
            (f := fun S => limitNormalizedJProbeSum hP hStruct S a) hR)
          (by positivity)

theorem localizedLimitNormalizedJMax_le_normalizedProbeSumMax_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m)
    (e : FullBlockVec d) (he : dotProduct e e ≤ 1) :
    (localizedLimitNormalizedJMax hP hStruct m n e) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  have hAll :
      ∀ᵐ a ∂P, ∀ R ∈ D,
        limitNormalizedBlockJObservable hP hStruct R e a ≤
          (4 * (Fintype.card (BlockCoord d) : ℝ)) *
            limitNormalizedJNormalizedProbeSum hP hStruct R a := by
    rw [Filter.eventually_all_finset]
    intro R _hR
    simpa using!
      limitNormalizedBlockJObservable_le_normalizedProbeSum_ae
        hP hStruct hΓ R e he
  filter_upwards [hAll] with a hAll_a
  have hloc_eq :
      localizedLimitNormalizedJMax hP hStruct m n e a =
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R e a) := by
    dsimp [localizedLimitNormalizedJMax]
    simp [D, hD]
  have hprobe_eq :
      localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a =
        D.sup' hD (fun R => limitNormalizedJNormalizedProbeSum hP hStruct R a) := by
    dsimp [localizedLimitNormalizedJNormalizedProbeSumMax]
    simp [D, hD]
  rw [hloc_eq, hprobe_eq]
  refine Finset.sup'_le hD _ ?_
  intro R hR
  calc
    limitNormalizedBlockJObservable hP hStruct R e a
        ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
            limitNormalizedJNormalizedProbeSum hP hStruct R a := hAll_a R hR
    _ ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          D.sup' hD
            (fun S => limitNormalizedJNormalizedProbeSum hP hStruct S a) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (s := D)
            (f := fun S => limitNormalizedJNormalizedProbeSum hP hStruct S a) hR)
          (by positivity)

theorem localizedLimitNormalizedJMax_smul_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m)
    (c : ℝ) (hc : c ≠ 0) (e : FullBlockVec d) :
    localizedLimitNormalizedJMax hP hStruct m n (c • e) =ᵐ[P]
      fun a : RegCoeffField d =>
        c ^ (2 : ℕ) * localizedLimitNormalizedJMax hP hStruct m n e a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  have hAll :
      ∀ᵐ a ∂P, ∀ R ∈ D,
        limitNormalizedBlockJObservable hP hStruct R (c • e) a =
          c ^ (2 : ℕ) *
            limitNormalizedBlockJObservable hP hStruct R e a := by
    rw [Filter.eventually_all_finset]
    intro R _hR
    simpa using!
      limitNormalizedBlockJObservable_smul_ae hP hStruct hΓ R c e
  filter_upwards [hAll] with a hAll_a
  have hloc_ce :
      localizedLimitNormalizedJMax hP hStruct m n (c • e) a =
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R (c • e) a) := by
    dsimp [localizedLimitNormalizedJMax]
    simp [D, hD]
  have hloc_e :
      localizedLimitNormalizedJMax hP hStruct m n e a =
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R e a) := by
    dsimp [localizedLimitNormalizedJMax]
    simp [D, hD]
  rw [hloc_ce, hloc_e]
  have hcongr :
      D.sup' hD
          (fun R => limitNormalizedBlockJObservable hP hStruct R (c • e) a) =
        D.sup' hD
          (fun R =>
            c ^ (2 : ℕ) *
              limitNormalizedBlockJObservable hP hStruct R e a) :=
    Finset.sup'_congr (s := D) (H := hD) (t := D) rfl
      (fun R hR => hAll_a R hR)
  rw [hcongr]
  exact
    (Finset.mul₀_sup'
      (a := c ^ (2 : ℕ))
      (f := fun R => limitNormalizedBlockJObservable hP hStruct R e a)
      (s := D) (hs := hD) (sq_pos_of_ne_zero hc).le).symm

end

end Section57
end Ch05
end Book
end Homogenization
