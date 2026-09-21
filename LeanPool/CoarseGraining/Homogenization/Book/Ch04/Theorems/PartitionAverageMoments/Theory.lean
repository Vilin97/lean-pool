/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Integrability

/-! # Theory -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-carrier partition-average moment estimates

This file exposes the finite-moment partition-average estimate against the
clean Chapter 4 observable surface.  The hypotheses are direct: locality on the
descendant cubes, translation covariance, measurability, and the origin-cube
moment input.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- A finite supremum costs only `card ^ (1 / p)` in an `L^p` root when each
observable has `L^p` root bounded by the same constant. -/
theorem integral_finsetSup_abs_pow_rpow_inv_le_card_rpow_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Finset ι} (hs : s.Nonempty) {p : ℕ} {K : ℝ}
    (hp : 1 ≤ p) (hK_nonneg : 0 ≤ K)
    (X : ι → Ω → ℝ)
    (hX_aemeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hX_root :
      ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      (s.card : ℝ) ^ (1 / (p : ℝ)) * K := by
  have hp_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  have hsum_int :
      Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ :=
    MeasureTheory.integrable_finsetSum s hX_int
  have hsup_aemeas :
      AEMeasurable (fun ω => s.sup' hs (fun i => |X i ω|)) μ := by
    have h :
        AEMeasurable (s.sup' hs (fun i (ω : Ω) => |X i ω|)) μ := by
      refine Finset.sup'_induction (s := s) (H := hs)
        (f := fun i ω => |X i ω|)
        (p := fun f => AEMeasurable f μ) ?_ ?_
      · intro _f hf _g hg
        exact hf.sup hg
      · intro i hi
        simpa [Real.norm_eq_abs] using (hX_aemeas i hi).norm
    convert h using 1
    ext ω
    exact (Finset.sup'_apply (C := fun _ : Ω => ℝ) hs
      (fun i (ω : Ω) => |X i ω|) ω).symm
  have hsup_pow_int :
      Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ := by
    refine Integrable.mono' hsum_int (hsup_aemeas.pow_const p).aestronglyMeasurable ?_
    filter_upwards with ω
    have hs_nonempty : s.Nonempty := hs
    obtain ⟨i0, hi0⟩ := hs_nonempty
    have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) :=
      (abs_nonneg (X i0 ω)).trans (Finset.le_sup' (f := fun i => |X i ω|) hi0)
    have hsup_le_sum :
        s.sup' hs (fun i => |X i ω|) ^ p ≤ ∑ i ∈ s, |X i ω| ^ p := by
      obtain ⟨i, hi, hsup_le⟩ :
          ∃ i ∈ s, s.sup' hs (fun i => |X i ω|) ≤ |X i ω| := by
        simpa only [Finset.le_sup'_iff] using
          (show s.sup' hs (fun i => |X i ω|) ≤
              s.sup' hs (fun i => |X i ω|) from le_rfl)
      have hi_le_sup : |X i ω| ≤ s.sup' hs (fun i => |X i ω|) :=
        Finset.le_sup' (f := fun j => |X j ω|) hi
      have hsup_eq : s.sup' hs (fun i => |X i ω|) = |X i ω| :=
        le_antisymm hsup_le hi_le_sup
      rw [hsup_eq]
      exact Finset.single_le_sum
        (f := fun j => |X j ω| ^ p) (fun j _ => by positivity) hi
    have hleft_nonneg : 0 ≤ (s.sup' hs (fun i => |X i ω|)) ^ p :=
      pow_nonneg hsup_nonneg p
    have habs_eq : |s.sup' hs (fun i => |X i ω|)| = s.sup' hs (fun i => |X i ω|) :=
      abs_of_nonneg hsup_nonneg
    simpa [Real.norm_eq_abs, habs_eq, abs_of_nonneg hleft_nonneg] using hsup_le_sum
  have hsup_integral_le :
      ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ ≤
        ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
    calc
      ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ
          ≤ ∫ ω, ∑ i ∈ s, |X i ω| ^ p ∂μ := by
            refine integral_mono hsup_pow_int hsum_int ?_
            intro ω
            have hs_nonempty : s.Nonempty := hs
            obtain ⟨i0, hi0⟩ := hs_nonempty
            have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) :=
              (abs_nonneg (X i0 ω)).trans
                (Finset.le_sup' (f := fun i => |X i ω|) hi0)
            obtain ⟨i, hi, hsup_le⟩ :
                ∃ i ∈ s, s.sup' hs (fun i => |X i ω|) ≤ |X i ω| := by
              simpa only [Finset.le_sup'_iff] using
                (show s.sup' hs (fun i => |X i ω|) ≤
                    s.sup' hs (fun i => |X i ω|) from le_rfl)
            have hi_le_sup : |X i ω| ≤ s.sup' hs (fun i => |X i ω|) :=
              Finset.le_sup' (f := fun j => |X j ω|) hi
            have hsup_eq : s.sup' hs (fun i => |X i ω|) = |X i ω| :=
              le_antisymm hsup_le hi_le_sup
            change (s.sup' hs (fun i => |X i ω|)) ^ p ≤
              ∑ i ∈ s, |X i ω| ^ p
            rw [hsup_eq]
            exact Finset.single_le_sum
              (f := fun j => |X j ω| ^ p) (fun j _ => by positivity) hi
      _ = ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
        simpa using integral_finsetSum (μ := μ) s hX_int
  have hsum_le :
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ ≤ (s.card : ℝ) * K ^ p := by
    calc
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ
          ≤ ∑ i ∈ s, K ^ p := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hroot := hX_root i hi
            have hroot_nonneg :
                0 ≤ (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
              positivity
            have hpow :
                ((∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ))) ^ p ≤ K ^ p :=
              pow_le_pow_left₀ hroot_nonneg hroot p
            have hint_nonneg : 0 ≤ ∫ ω, |X i ω| ^ p ∂μ := by
              positivity
            have hint_eq :
                ((∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ))) ^ p =
                  ∫ ω, |X i ω| ^ p ∂μ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hint_nonneg, one_div,
                inv_mul_cancel₀ (show (p : ℝ) ≠ 0 by exact_mod_cast hp_ne_zero),
                Real.rpow_one]
            exact hint_eq ▸ hpow
      _ = (s.card : ℝ) * K ^ p := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsup_integral_nonneg :
      0 ≤ ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
    refine integral_nonneg ?_
    intro ω
    have hs_nonempty : s.Nonempty := hs
    obtain ⟨i0, hi0⟩ := hs_nonempty
    exact pow_nonneg
      ((abs_nonneg (X i0 ω)).trans (Finset.le_sup' (f := fun i => |X i ω|) hi0))
      p
  have hroot :
      (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        ((s.card : ℝ) * K ^ p) ^ (1 / (p : ℝ)) := by
    exact Real.rpow_le_rpow hsup_integral_nonneg
      (hsup_integral_le.trans hsum_le) (by positivity)
  have htarget :
      ((s.card : ℝ) * K ^ p) ^ (1 / (p : ℝ)) =
        (s.card : ℝ) ^ (1 / (p : ℝ)) * K := by
    rw [one_div, Real.mul_rpow (by positivity) (pow_nonneg hK_nonneg p),
      Real.pow_rpow_inv_natCast hK_nonneg hp_ne_zero]
  exact hroot.trans_eq htarget

/-- Finite-parent maximum of restriction-centered descendant averages, using
the restriction-unit-range partition-average moment theorem on each parent cube.

This is the Ch4 probabilistic block behind the one-scale fluctuation estimate
in the Section 5.2 multiscale ellipticity moment lemma: the finite maximum over
parents costs only `parents.card ^ (1 / p)` after the per-parent Rosenthal
bound has been proved. -/
theorem integral_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {p : ℕ} {K B : ℝ}
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_local :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X (cubeSet R)))
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n,
        AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K) (hB_nonneg : 0 ≤ B)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K)
    (hB :
      ∀ Q ∈ parents,
        ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p *
              ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p *
              Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) ≤ B) :
    (∫ a,
        (parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      (parents.card : ℝ) ^ (1 / (p : ℝ)) * B := by
  have hp_one : 1 ≤ p := by omega
  refine
    integral_finsetSup_abs_pow_rpow_inv_le_card_rpow_mul
      (μ := P) (s := parents) hparents (p := p) (K := B)
      hp_one hB_nonneg
      (fun Q a => restrictionCenteredDescendantAverageOnCube P Q n X a) ?_ ?_ ?_
  · intro Q hQ
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
  · intro Q hQ
    exact
      integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary
        (d := d) (Q := Q) (n := n) (P := P) (p := p)
        hn (hparent_scale Q hQ) hPstat X hX_cov hX0_aemeas
        (hX_desc_aemeas Q hQ) hp_one hX0Lp_int
  · intro Q hQ
    exact
      (integral_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw
        (d := d) (Q := Q) (n := n) (P := P) (p := p) (K := K)
        hn (hparent_scale Q hQ) hPstat hPdep X
        (hX_local Q hQ) hX_cov hX0_aemeas (hX_desc_aemeas Q hQ)
        hp hK_nonneg hX0Lp_int hX0Lp).trans (hB Q hQ)

/-- Completed-local finite-parent version of
`integral_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw`.

The caller supplies raw translation-covariant observables and Ch4 supplies
local representatives on each descendant cube.  This is the form used by
law-facing coarse-block fluctuation estimates, where the raw totalized
observable is a.e.-equal to a local-test representative but is not itself
definitionally local. -/
theorem integral_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {p : ℕ} {K B : ℝ}
    (hP : RestrictionLawCarrier P)
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_localRep :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n,
        ∃ Y : RegCoeffField d → ℝ,
          IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet R) =ᵐ[P] Y)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n,
        AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K) (hB_nonneg : 0 ≤ B)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K)
    (hB :
      ∀ Q ∈ parents,
        ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p *
              ((descendantsAtScale Q n).card : ℝ) ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p *
              Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) ≤ B) :
    (∫ a,
        (parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      (parents.card : ℝ) ^ (1 / (p : ℝ)) * B := by
  have hp_one : 1 ≤ p := by omega
  refine
    integral_finsetSup_abs_pow_rpow_inv_le_card_rpow_mul
      (μ := P) (s := parents) hparents (p := p) (K := B)
      hp_one hB_nonneg
      (fun Q a => restrictionCenteredDescendantAverageOnCube P Q n X a) ?_ ?_ ?_
  · intro Q hQ
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
    exact aemeasurable_const.mul hsum
  · intro Q hQ
    exact
      integrable_abs_pow_restrictionCenteredDescendantAverageOnCube_of_stationary
        (d := d) (Q := Q) (n := n) (P := P) (p := p)
        hn (hparent_scale Q hQ) hPstat X hX_cov hX0_aemeas
        (hX_desc_aemeas Q hQ) hp_one hX0Lp_int
  · intro Q hQ
    exact
      (integral_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
        (d := d) (Q := Q) (n := n) (P := P) (p := p) (K := K)
        hP hn (hparent_scale Q hQ) hPstat hPdep X
        (hX_localRep Q hQ) hX_cov hX0_aemeas (hX_desc_aemeas Q hQ)
        hp hK_nonneg hX0Lp_int hX0Lp).trans (hB Q hQ)

/-- Low-moment finite partition-average fluctuation estimate with explicit
Rosenthal constants. -/
theorem integral_abs_restrictionCenteredDescendantAverage_le_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X (cubeSet R)))
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (X (cubeSet R)) P)
    (hξ : 2 ≤ ξ) (hK_nonneg : 0 ≤ K)
    (hX0ξ_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ ξ) P)
    (hX0ξ :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ ξ ∂P) ^
          (1 / (ξ : ℝ)) ≤ K) :
    ∫ a, |restrictionCenteredDescendantAverage P n m X a| ∂P ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleLpConst d n 2 *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K +
          rosenthalDescendantsAtScaleSqrtConst d n 2 *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
  let X0 : RegCoeffField d → ℝ := restrictionCenteredOriginObservable P n X
  have hX0c_aemeas : AEMeasurable X0 P := by
    simpa [X0, restrictionCenteredOriginObservable] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hX0_two_int :
      Integrable (fun a => |X0 a| ^ (2 : ℕ)) P := by
    have hξ_ne_zero : ξ ≠ 0 := by omega
    have h_memLp_ξ : MemLp X0 (ξ : ENNReal) P := by
      rw [← integrable_norm_rpow_iff
        hX0c_aemeas.aestronglyMeasurable (by exact_mod_cast hξ_ne_zero) (by simp)]
      simpa [X0, Real.norm_eq_abs] using hX0ξ_int
    have h_memLp_two : MemLp X0 (2 : ENNReal) P := by
      exact h_memLp_ξ.mono_exponent (by exact_mod_cast hξ)
    simpa [X0, Real.norm_eq_abs] using h_memLp_two.integrable_norm_pow (by norm_num)
  have hX0_two :
      (∫ a, |X0 a| ^ (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤ K := by
    exact
      (integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv_aemeasurable
        (μ := P) (f := X0) hξ hX0c_aemeas (by simpa [X0] using hX0ξ_int)).trans
        (by simpa [X0] using hX0ξ)
  have havg_two :=
    integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw
      (d := d) (n := n) (m := m) (P := P) (p := 2) (K := K)
      hn hnm hPstat hPdep X hX_local hX_cov hX0_aemeas hX_desc_aemeas
      (by norm_num) hK_nonneg (by simpa [X0] using hX0_two_int)
      (by simpa [X0] using hX0_two)
  have hAavg_aemeas : AEMeasurable (restrictionCenteredDescendantAverage P n m X) P := by
    unfold restrictionCenteredDescendantAverage
    have hsum :
        AEMeasurable
          (fun a =>
            ∑ R ∈ descendantsAtScale (originCube d m) n,
              (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d n)) b ∂P)) P := by
      have hsum' : AEMeasurable
          (∑ R ∈ descendantsAtScale (originCube d m) n,
            fun a => X (cubeSet R) a -
              ∫ b, X (cubeSet (originCube d n)) b ∂P) P :=
        Finset.aemeasurable_sum _ (fun R hR =>
          (hX_desc_aemeas R hR).sub aemeasurable_const)
      convert hsum' using 1
      ext a
      simp
    exact aemeasurable_const.mul
      hsum
  have hAavg_two_int :
      Integrable (fun a => |restrictionCenteredDescendantAverage P n m X a| ^ (2 : ℕ)) P := by
    exact
      integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary
        (d := d) (n := n) (m := m) (P := P) (p := 2)
        hn hnm hPstat X hX_cov hX0_aemeas hX_desc_aemeas
        (by norm_num) (by simpa [X0] using hX0_two_int)
  have hsqrt_card :
      Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) =
        ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (1 / (2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
  calc
    ∫ a, |restrictionCenteredDescendantAverage P n m X a| ∂P
      ≤
        (∫ a, |restrictionCenteredDescendantAverage P n m X a| ^ (2 : ℕ) ∂P) ^
          (1 / (2 : ℝ)) := by
            exact integral_abs_le_integral_abs_sq_rpow_half_aemeasurable
              hAavg_aemeas hAavg_two_int
    _ ≤
        ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n 2 *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K +
            rosenthalDescendantsAtScaleSqrtConst d n 2 *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
              simpa [hsqrt_card, Real.rpow_natCast, one_div] using havg_two

end

end Ch04
end Book
end Homogenization
