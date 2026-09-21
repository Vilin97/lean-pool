/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.OnCube

/-! # Integrability -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-carrier partition-average moment estimates: integrability
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Integrability of the centered descendant average follows from the
corresponding centered origin-cube moment by stationarity and translation
covariance. -/
theorem integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary_of_isTranslationCovariant
    {d : ℕ} {n m : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : RestrictionStationaryLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (X (cubeSet R)) P)
    (hp : 1 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    Integrable (fun a => |restrictionCenteredDescendantAverage P n m X a| ^ p) P := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (Z R) P := by
    intro R hR
    simpa [Z] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
  have hZ_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    have hscaleR : R.scale = n := by
      calc
        R.scale = (originCube d m).scale - Int.toNat ((originCube d m).scale - n) := by
          exact scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d m) hnm hR
        _ = m - Int.toNat (m - n) := by
              rfl
        _ = n := by
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm)]
              ring
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (scaleTranslationShift n R))
            (cubeSet (originCube d n)) := by
      have hscale_nonneg : 0 ≤ R.scale := by
        simpa [hscaleR] using hn
      calc
        cubeSet R =
            translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
        _ =
            translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n)) := by
              simp [hscaleR]
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap :
        Measure.map (Y (cubeSet R)) P =
          Measure.map (Y (cubeSet (originCube d n))) P := by
      calc
        Measure.map (Y (cubeSet R)) P =
            Measure.map
              (Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n)))) P := by
              rw [hshift]
        _ = Measure.map (Y (cubeSet (originCube d n))) P := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
                (scaleTranslationShift n R)
    have hYR_int :
        Integrable (fun a => |Y (cubeSet R) a| ^ p) P := by
      exact integrable_abs_pow_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap hY0Lp_int
    simpa [Z, Y] using hYR_int
  let S : RegCoeffField d → ℝ :=
    fun a => ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a
  have hS_memLp : MemLp S (p : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro R hR
    refine (integrable_norm_rpow_iff
      (hZ_aemeas R hR).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hZ_int R hR
  let Aavg : RegCoeffField d → ℝ :=
    ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ • S
  have hAavg_eq : Aavg = restrictionCenteredDescendantAverage P n m X := by
    funext a
    simp [Aavg, S, Z, restrictionCenteredDescendantAverage, μ0]
  have hAavg_memLp : MemLp Aavg (p : ENNReal) P := hS_memLp.const_smul _
  simpa [Aavg, hAavg_eq, Real.norm_eq_abs] using
    hAavg_memLp.integrable_norm_pow hp_nat_ne_zero

/-- Integrability of the centered descendant average follows from the
corresponding centered origin-cube moment by stationarity. -/
theorem integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary
    {d : ℕ} {n m : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : RestrictionStationaryLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (X (cubeSet R)) P)
    (hp : 1 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    Integrable (fun a => |restrictionCenteredDescendantAverage P n m X a| ^ p) P :=
  integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary_of_isTranslationCovariant
    (d := d) (n := n) (m := m) (P := P) (p := p)
    hn hnm hPstat X hX_cov hX0_aemeas hX_desc_aemeas hp hX0Lp_int

/-- Integrability of the centered descendant average over an arbitrary parent
cube follows from the corresponding centered origin-cube moment by
stationarity and translation covariance. -/
theorem integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary_of_isTranslationCovariant
    {d : ℕ} {Q : TriadicCube d} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hp : 1 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    Integrable (fun a => |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p) P := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (Z R) P := by
    intro R hR
    simpa [Z] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
  have hZ_int :
      ∀ R ∈ descendantsAtScale Q n,
        Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    have hscaleR : R.scale = n := by
      calc
        R.scale = Q.scale - Int.toNat (Q.scale - n) := by
          exact scale_eq_sub_of_mem_descendantsAtScale (Q := Q) hnQ hR
        _ = n := by
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnQ)]
              ring
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (scaleTranslationShift n R))
            (cubeSet (originCube d n)) := by
      have hscale_nonneg : 0 ≤ R.scale := by
        simpa [hscaleR] using hn
      calc
        cubeSet R =
            translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
        _ =
            translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n)) := by
              simp [hscaleR]
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap :
        Measure.map (Y (cubeSet R)) P =
          Measure.map (Y (cubeSet (originCube d n))) P := by
      calc
        Measure.map (Y (cubeSet R)) P =
            Measure.map
              (Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n)))) P := by
              rw [hshift]
        _ = Measure.map (Y (cubeSet (originCube d n))) P := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
                (scaleTranslationShift n R)
    have hYR_int :
        Integrable (fun a => |Y (cubeSet R) a| ^ p) P := by
      exact integrable_abs_pow_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap hY0Lp_int
    simpa [Z, Y] using hYR_int
  let S : RegCoeffField d → ℝ :=
    fun a => ∑ R ∈ descendantsAtScale Q n, Z R a
  have hS_memLp : MemLp S (p : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro R hR
    refine (integrable_norm_rpow_iff
      (hZ_aemeas R hR).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hZ_int R hR
  let Aavg : RegCoeffField d → ℝ :=
    ((descendantsAtScale Q n).card : ℝ)⁻¹ • S
  have hAavg_eq : Aavg = restrictionCenteredDescendantAverageOnCube P Q n X := by
    funext a
    simp [Aavg, S, Z, restrictionCenteredDescendantAverageOnCube, μ0]
  have hAavg_memLp : MemLp Aavg (p : ENNReal) P := hS_memLp.const_smul _
  simpa [Aavg, hAavg_eq, Real.norm_eq_abs] using
    hAavg_memLp.integrable_norm_pow hp_nat_ne_zero

/-- Integrability of the centered descendant average over an arbitrary parent
cube follows from the corresponding centered origin-cube moment by
stationarity. -/
theorem integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary
    {d : ℕ} {Q : TriadicCube d} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hp : 1 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    Integrable (fun a => |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p) P :=
  integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary_of_isTranslationCovariant
    (d := d) (Q := Q) (n := n) (P := P) (p := p)
    hn hnQ hPstat X hX_cov hX0_aemeas hX_desc_aemeas hp hX0Lp_int

/-- Integrability of the finite parent maximum of centered descendant averages.

This is the integrability half of the public finite-parent moment estimate; it
is useful when a downstream theorem first compares another observable to this
finite maximum and then applies the Ch4 moment bound. -/
theorem integrable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_of_stationary
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {p : ℕ}
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hp : 1 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P) :
    Integrable
      (fun a : RegCoeffField d =>
        (parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) ^ p) P := by
  have hsum_int :
      Integrable
        (fun a : RegCoeffField d =>
          ∑ Q ∈ parents, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p) P :=
    MeasureTheory.integrable_finsetSum parents fun Q hQ =>
      integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary
        (d := d) (Q := Q) (n := n) (P := P) (p := p)
        hn (hparent_scale Q hQ) hPstat X hX_cov hX0_aemeas
        (hX_desc_aemeas Q hQ) hp hX0Lp_int
  have hsup_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          parents.sup' hparents
            (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) P := by
    have h :
        AEMeasurable
          (parents.sup' hparents
            (fun Q (a : RegCoeffField d) =>
              |restrictionCenteredDescendantAverageOnCube P Q n X a|)) P := by
      refine Finset.sup'_induction (s := parents) (H := hparents)
        (f := fun Q a => |restrictionCenteredDescendantAverageOnCube P Q n X a|)
        (p := fun f => AEMeasurable f P) ?_ ?_
      · intro _f hf _g hg
        exact hf.sup hg
      · intro Q hQ
        have havg :
            AEMeasurable (fun a => restrictionCenteredDescendantAverageOnCube P Q n X a) P := by
          unfold restrictionCenteredDescendantAverageOnCube
          have hsum :
              AEMeasurable
                (fun a =>
                  ∑ R ∈ descendantsAtScale Q n,
                    (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d n)) b ∂P)) P := by
            have hsum' : AEMeasurable
                (∑ R ∈ descendantsAtScale Q n,
                  fun a => X (cubeSet R) a -
                    ∫ b, X (cubeSet (originCube d n)) b ∂P) P :=
              Finset.aemeasurable_sum _ fun R hR =>
                (hX_desc_aemeas Q hQ R hR).sub aemeasurable_const
            convert hsum' using 1
            ext a
            simp
          exact aemeasurable_const.mul
            hsum
        simpa [Real.norm_eq_abs] using havg.norm
    convert h using 1
    ext a
    exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hparents
      (fun Q (a : RegCoeffField d) =>
        |restrictionCenteredDescendantAverageOnCube P Q n X a|) a).symm
  refine Integrable.mono' hsum_int (hsup_aemeas.pow_const p).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro a
  have hparents_nonempty : parents.Nonempty := hparents
  obtain ⟨Q0, hQ0⟩ := hparents_nonempty
  have hsup_nonneg :
      0 ≤ parents.sup' hparents
        (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) :=
    (abs_nonneg (restrictionCenteredDescendantAverageOnCube P Q0 n X a)).trans
      (Finset.le_sup'
        (f := fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) hQ0)
  have hsup_le_sum :
      (parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) ^ p ≤
        ∑ Q ∈ parents, |restrictionCenteredDescendantAverageOnCube P Q n X a| ^ p := by
    obtain ⟨Q, hQ, hsup_le⟩ :
        ∃ Q ∈ parents,
          parents.sup' hparents
              (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) ≤
            |restrictionCenteredDescendantAverageOnCube P Q n X a| := by
      simpa only [Finset.le_sup'_iff] using
        (show parents.sup' hparents
            (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) ≤
          parents.sup' hparents
            (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) from le_rfl)
    have hQ_le_sup :
        |restrictionCenteredDescendantAverageOnCube P Q n X a| ≤
          parents.sup' hparents
            (fun R => |restrictionCenteredDescendantAverageOnCube P R n X a|) :=
      Finset.le_sup'
        (f := fun R => |restrictionCenteredDescendantAverageOnCube P R n X a|) hQ
    have hsup_eq :
        parents.sup' hparents
            (fun R => |restrictionCenteredDescendantAverageOnCube P R n X a|) =
          |restrictionCenteredDescendantAverageOnCube P Q n X a| :=
      le_antisymm hsup_le hQ_le_sup
    rw [hsup_eq]
    exact Finset.single_le_sum
      (f := fun R => |restrictionCenteredDescendantAverageOnCube P R n X a| ^ p)
      (fun R _ => by positivity) hQ
  have hleft_nonneg :
      0 ≤
        (parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) ^ p :=
    pow_nonneg hsup_nonneg p
  have habs_eq :
      |parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)| =
        parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) :=
    abs_of_nonneg hsup_nonneg
  simpa [Real.norm_eq_abs, habs_eq, abs_of_nonneg hleft_nonneg] using hsup_le_sum

end

end Ch04
end Book
end Homogenization
