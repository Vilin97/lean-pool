/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.Scaling

@[expose] public section

/-!
# Homogeneity of the actual similarity coordinates

The coordinate `q` is the positive branch constructed in
`SimilarityCoordinates`. Its scaling law follows from uniqueness of that
branch. The band coordinates below are `(R,(Z,T))`, with `T = τ / Q`.
Consequently the profile coordinate is `X = R² / (2 q(T,Z))`, not a fixed
function of `R` alone. Profile weights are transported exactly by a change
of band scale.
-/

noncomputable section

namespace NavierStokes.SimilarityHomogeneity

open SimilarityCoordinates
open scoped ContDiff

abbrev D := CoordinateAlgebra.D

/-- The scalar defining equation has the required anisotropic homogeneity. -/
theorem forwardScalar_scale {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q) (a z : ℝ) :
    forwardScalar a (Q ^ ((1 - a) / 2) * z) (Q * q) =
      Q * forwardScalar a z q := by
  have hp : (Q ^ ((1 - a) / 2)) ^ 2 * Q ^ a = Q := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ]
    rw [show (1 - a) / 2 * (2 : ℕ) + a = (1 : ℝ) by ring, Real.rpow_one]
  unfold forwardScalar
  rw [Real.mul_rpow hQ.le hq.le, mul_pow]
  calc
    Q * q - (Q ^ ((1 - a) / 2)) ^ 2 * z ^ 2 * (Q ^ a * q ^ a) =
        Q * q - ((Q ^ ((1 - a) / 2)) ^ 2 * Q ^ a) * (z ^ 2 * q ^ a) := by ring
    _ = Q * (q - z ^ 2 * q ^ a) := by rw [hp]; ring

/-- Exact scaling of the defined coordinate, obtained by positive-branch
uniqueness rather than by postulating homogeneity. -/
theorem coordinateQ_scale {a Q τ z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateQ a (Q * τ, Q ^ ((1 - a) / 2) * z) =
      Q * coordinateQ a (τ, z) := by
  have hs := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  apply (eq_coordinateQ ha ha1 (mul_pos hQ hτ) (mul_pos hQ hs.1) ?_).symm
  rw [forwardScalar_scale hQ hs.1, hs.2]

/-- The defined axial similarity parameter is invariant under scaling. -/
theorem coordinateEta_scale {a Q τ z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateEta a (Q * τ, Q ^ ((1 - a) / 2) * z) =
      coordinateEta a (τ, z) := by
  have hq := (coordinateQ_spec ha ha1 (p := (τ, z)) hτ).1
  unfold coordinateEta
  rw [coordinateQ_scale ha ha1 hQ hτ, Real.mul_rpow hQ.le hq.le]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hQ _).ne'

/-- Scaling `s` and `τ` by the same factor preserves the defined `X`. -/
theorem coordinateX_scale {a Q τ z s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateX a (Q * s) (Q * τ, Q ^ ((1 - a) / 2) * z) =
      coordinateX a s (τ, z) := by
  unfold coordinateX
  rw [coordinateQ_scale ha ha1 hQ hτ]
  exact mul_div_mul_left _ _ hQ.ne'

/-- The manuscript's exact `h,D` convention. -/
theorem coordinateQ_scale_h {h Q τ z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateQ (2 * h) (Q * τ, Q ^ D h * z) =
      Q * coordinateQ (2 * h) (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateQ_scale (a := 2 * h) (by linarith) (by linarith) hQ hτ

theorem coordinateEta_scale_h {h Q τ z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateEta (2 * h) (Q * τ, Q ^ D h * z) =
      coordinateEta (2 * h) (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateEta_scale (a := 2 * h) (by linarith) (by linarith) hQ hτ

theorem coordinateX_scale_h {h Q τ z s : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateX (2 * h) (Q * s) (Q * τ, Q ^ D h * z) =
      coordinateX (2 * h) s (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateX_scale (a := 2 * h) (s := s) (by linarith) (by linarith) hQ hτ

/-- Physical time is `t=1-τ`; physical points have layout `(t,(s,z))`. -/
noncomputable def physicalScale (h Q : ℝ) (p : SimilarityProfile.PhysicalPoint) :
    SimilarityProfile.PhysicalPoint :=
  (1 - Q * (1 - p.1), (Q * p.2.1, Q ^ D h * p.2.2))

theorem physicalScale_smooth (h Q : ℝ) : ContDiff ℝ ∞ (physicalScale h Q) :=
  (contDiff_const.sub (contDiff_const.mul (contDiff_const.sub contDiff_fst))).prodMk
    ((contDiff_const.mul contDiff_snd.fst).prodMk
      (contDiff_const.mul contDiff_snd.snd))

theorem physicalScale_time_lt_one {h Q : ℝ} (hQ : 0 < Q)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    (physicalScale h Q p).1 < 1 := by
  change 1 - Q * (1 - p.1) < 1
  linarith [mul_pos hQ (sub_pos.mpr hp)]

theorem q_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.q h (physicalScale h Q p) = Q * SimilarityProfile.q h p := by
  change coordinateQ (2 * h) (1 - (1 - Q * (1 - p.1)), Q ^ D h * p.2.2) = _
  rw [show 1 - (1 - Q * (1 - p.1)) = Q * (1 - p.1) by ring]
  exact coordinateQ_scale_h hh hh1 hQ (sub_pos.mpr hp)

theorem eta_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.eta h (physicalScale h Q p) = SimilarityProfile.eta h p := by
  change coordinateEta (2 * h) (1 - (1 - Q * (1 - p.1)), Q ^ D h * p.2.2) = _
  rw [show 1 - (1 - Q * (1 - p.1)) = Q * (1 - p.1) by ring]
  exact coordinateEta_scale_h hh hh1 hQ (sub_pos.mpr hp)

theorem X_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.X h (physicalScale h Q p) = SimilarityProfile.X h p := by
  unfold SimilarityProfile.X
  rw [q_physicalScale hh hh1 hQ hp]
  change (Q * p.2.1) / (Q * SimilarityProfile.q h p) = _
  exact mul_div_mul_left _ _ hQ.ne'

theorem inner_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.inner h (physicalScale h Q p) = SimilarityProfile.inner h p :=
  Prod.ext (X_physicalScale hh hh1 hQ hp) (eta_physicalScale hh hh1 hQ hp)

/-- Homogeneity holds for every profile, without assuming its smoothness. -/
theorem pullback_physicalScale {h Q b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1)
    (f : SimilarityProfile.InnerProfile) :
    SimilarityProfile.pullback h b f (physicalScale h Q p) =
      Q ^ b * SimilarityProfile.pullback h b f p := by
  unfold SimilarityProfile.pullback
  rw [q_physicalScale hh hh1 hQ hp, inner_physicalScale hh hh1 hQ hp,
    Real.mul_rpow hQ.le (SimilarityProfile.q_pos hh hh1 hp).le]
  ring

abbrev ChartPoint := ℝ × (ℝ × ℝ)

/-- A band chart is ordered `(R,(Z,T))`. -/
noncomputable def chartQ (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateQ (2 * h) (p.2.2, p.2.1)

noncomputable def chartEta (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateEta (2 * h) (p.2.2, p.2.1)

noncomputable def chartX (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateX (2 * h) (p.1 ^ 2 / 2) (p.2.2, p.2.1)

noncomputable def chartInner (h : ℝ) (p : ChartPoint) : ℝ × ℝ :=
  (chartX h p, chartEta h p)

/-- Transition from the band of scale `Q` to the band of scale `Q'`. -/
noncomputable def chartTransition (h Q Q' : ℝ) (p : ChartPoint) : ChartPoint :=
  ((Q / Q') ^ (1 / 2 : ℝ) * p.1,
    ((Q / Q') ^ D h * p.2.1, (Q / Q') * p.2.2))

theorem chartTransition_smooth (h Q Q' : ℝ) :
    ContDiff ℝ ∞ (chartTransition h Q Q') :=
  (contDiff_const.mul contDiff_fst).prodMk
    ((contDiff_const.mul contDiff_snd.fst).prodMk
      (contDiff_const.mul contDiff_snd.snd))

theorem chartTransition_time_pos {h Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    {p : ChartPoint} (hp : 0 < p.2.2) : 0 < (chartTransition h Q Q' p).2.2 :=
  mul_pos (div_pos hQ hQ') hp

theorem chartQ_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartQ h (chartTransition h Q Q' p) = (Q / Q') * chartQ h p :=
  coordinateQ_scale_h hh hh1 (div_pos hQ hQ') hp

theorem chartEta_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartEta h (chartTransition h Q Q' p) = chartEta h p :=
  coordinateEta_scale_h hh hh1 (div_pos hQ hQ') hp

theorem chartX_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartX h (chartTransition h Q Q' p) = chartX h p := by
  have hr : 0 < Q / Q' := div_pos hQ hQ'
  have hs : ((Q / Q') ^ (1 / 2 : ℝ) * p.1) ^ 2 / 2 =
      (Q / Q') * (p.1 ^ 2 / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hr.le]
    norm_num
    ring
  change coordinateX (2 * h) (((Q / Q') ^ (1 / 2 : ℝ) * p.1) ^ 2 / 2)
    ((Q / Q') * p.2.2, (Q / Q') ^ D h * p.2.1) = _
  rw [hs]
  exact coordinateX_scale_h hh hh1 hr hp

theorem chartInner_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartInner h (chartTransition h Q Q' p) = chartInner h p :=
  Prod.ext (chartX_transition hh hh1 hQ hQ' hp) (chartEta_transition hh hh1 hQ hQ' hp)

/-- The genuine chart-to-physical map, with radial variable `s=r²/2`. -/
noncomputable def chartToPhysical (h Q : ℝ) (p : ChartPoint) :
    SimilarityProfile.PhysicalPoint :=
  (1 - Q * p.2.2, (Q * (p.1 ^ 2 / 2), Q ^ D h * p.2.1))

theorem chartToPhysical_smooth (h Q : ℝ) : ContDiff ℝ ∞ (chartToPhysical h Q) :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd.snd)).prodMk
    ((contDiff_const.mul ((contDiff_fst.pow 2).div_const 2)).prodMk
      (contDiff_const.mul contDiff_snd.fst))

theorem chartToPhysical_time_lt_one {h Q : ℝ} (hQ : 0 < Q)
    {p : ChartPoint} (hp : 0 < p.2.2) : (chartToPhysical h Q p).1 < 1 := by
  change 1 - Q * p.2.2 < 1
  linarith [mul_pos hQ hp]

/-- The radial component really is obtained from `r = sqrt(Q) R`. -/
theorem chartToPhysical_radial {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (p : ChartPoint) :
    (chartToPhysical h Q p).2.1 = (Scaling.radialLength Q * p.1) ^ 2 / 2 := by
  unfold chartToPhysical Scaling.radialLength
  dsimp only
  rw [mul_pow, ← Real.rpow_mul_natCast hQ.le]
  norm_num
  ring

theorem q_chartToPhysical {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : ChartPoint} (hp : 0 < p.2.2) :
    SimilarityProfile.q h (chartToPhysical h Q p) = Q * chartQ h p := by
  change coordinateQ (2 * h) (1 - (1 - Q * p.2.2), Q ^ D h * p.2.1) = _
  rw [show 1 - (1 - Q * p.2.2) = Q * p.2.2 by ring]
  exact coordinateQ_scale_h hh hh1 hQ hp

theorem eta_chartToPhysical {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : ChartPoint} (hp : 0 < p.2.2) :
    SimilarityProfile.eta h (chartToPhysical h Q p) = chartEta h p := by
  change coordinateEta (2 * h) (1 - (1 - Q * p.2.2), Q ^ D h * p.2.1) = _
  rw [show 1 - (1 - Q * p.2.2) = Q * p.2.2 by ring]
  exact coordinateEta_scale_h hh hh1 hQ hp

theorem X_chartToPhysical {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : ChartPoint} (hp : 0 < p.2.2) :
    SimilarityProfile.X h (chartToPhysical h Q p) = chartX h p := by
  unfold SimilarityProfile.X
  rw [q_chartToPhysical hh hh1 hQ hp]
  change (Q * (p.1 ^ 2 / 2)) / (Q * chartQ h p) = (p.1 ^ 2 / 2) / chartQ h p
  exact mul_div_mul_left _ _ hQ.ne'

theorem inner_chartToPhysical {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : ChartPoint} (hp : 0 < p.2.2) :
    SimilarityProfile.inner h (chartToPhysical h Q p) = chartInner h p :=
  Prod.ext (X_chartToPhysical hh hh1 hQ hp) (eta_chartToPhysical hh hh1 hQ hp)

/-- Two band descriptions of the same physical point agree exactly. -/
theorem chartToPhysical_transition {h Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (p : ChartPoint) :
    chartToPhysical h Q' (chartTransition h Q Q' p) = chartToPhysical h Q p := by
  have hr : 0 < Q / Q' := div_pos hQ hQ'
  have hs : ((Q / Q') ^ (1 / 2 : ℝ)) ^ 2 = Q / Q' := by
    rw [← Real.rpow_mul_natCast hr.le]
    norm_num
  have hz : Q' ^ D h * (Q / Q') ^ D h = Q ^ D h := by
    rw [← Real.mul_rpow hQ'.le hr.le]
    congr 1
    field_simp
  apply Prod.ext
  · dsimp [chartToPhysical, chartTransition]
    field_simp
  · apply Prod.ext
    · dsimp [chartToPhysical, chartTransition]
      rw [mul_pow, hs]
      field_simp
    · dsimp [chartToPhysical, chartTransition]
      rw [← mul_assoc, hz]

theorem chartTransition_refl {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (p : ChartPoint) :
    chartTransition h Q Q p = p := by
  simp [chartTransition, hQ.ne']

theorem chartTransition_comp {h Q Q' Q'' : ℝ}
    (hQ : 0 < Q) (hQ' : 0 < Q') (hQ'' : 0 < Q'') (p : ChartPoint) :
    chartTransition h Q' Q'' (chartTransition h Q Q' p) =
      chartTransition h Q Q'' p := by
  have hr : Q' / Q'' * (Q / Q') = Q / Q'' := by field_simp
  have hpow (a : ℝ) : (Q' / Q'') ^ a * (Q / Q') ^ a = (Q / Q'') ^ a := by
    rw [← Real.mul_rpow (div_pos hQ' hQ'').le (div_pos hQ hQ').le, hr]
  apply Prod.ext
  · dsimp [chartTransition]
    rw [← mul_assoc, hpow]
  · apply Prod.ext
    · dsimp [chartTransition]
      rw [← mul_assoc, hpow]
    · dsimp [chartTransition]
      rw [← mul_assoc, hr]

theorem chartTransition_inverse {h Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (p : ChartPoint) :
    chartTransition h Q' Q (chartTransition h Q Q' p) = p := by
  rw [chartTransition_comp hQ hQ' hQ, chartTransition_refl hQ]

/-- The usual open annular-chart domain; profile annulus restrictions can
be added using `chartX_mem_transition`. -/
noncomputable def chartDomain : Set ChartPoint := {p | 0 < p.1 ∧ 0 < p.2.2}

theorem isOpen_chartDomain : IsOpen chartDomain :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd.snd)

theorem chartTransition_mem_iff {h Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (p : ChartPoint) : chartTransition h Q Q' p ∈ chartDomain ↔ p ∈ chartDomain := by
  change (0 < (Q / Q') ^ (1 / 2 : ℝ) * p.1 ∧ 0 < (Q / Q') * p.2.2) ↔ _
  rw [mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos (div_pos hQ hQ') _),
    mul_pos_iff_of_pos_left (div_pos hQ hQ')]
  rfl

theorem chartInner_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ChartPoint} (hp : 0 < p.2.2) : ContDiffAt ℝ ∞ (chartInner h) p := by
  have hm : ContDiffAt ℝ ∞ (fun x : ChartPoint => (x.2.2, x.2.1)) p :=
    contDiffAt_snd.snd.prodMk contDiffAt_snd.fst
  have hq : ContDiffAt ℝ ∞ (chartQ h) p :=
    (coordinateQ_smooth (by linarith) (by linarith) (p := (p.2.2, p.2.1)) hp).comp p hm
  have he : ContDiffAt ℝ ∞ (chartEta h) p :=
    (coordinateEta_smooth (by linarith) (by linarith) (p := (p.2.2, p.2.1)) hp).comp p hm
  have hqp : 0 < chartQ h p :=
    (coordinateQ_spec (by linarith) (by linarith) (p := (p.2.2, p.2.1)) hp).1
  exact (((contDiffAt_fst.pow 2).div_const 2).div hq hqp.ne').prodMk he

theorem chartX_mem_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) (I : Set ℝ) :
    chartX h (chartTransition h Q Q' p) ∈ I ↔ chartX h p ∈ I := by
  rw [chartX_transition hh hh1 hQ hQ' hp]

/-- Every profile depending on both actual inner coordinates is unchanged. -/
theorem chartProfile_transition {E : Type*} {h Q Q' : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQ' : 0 < Q')
    {p : ChartPoint} (hp : 0 < p.2.2) (F : (ℝ × ℝ) → E) :
    F (chartInner h (chartTransition h Q Q' p)) = F (chartInner h p) := by
  rw [chartInner_transition hh hh1 hQ hQ' hp]

noncomputable def chartWeight {E : Type*} (h : ℝ) (ζ : ℝ → E) (p : ChartPoint) : E :=
  ζ (chartX h p)

/-- In particular an arbitrarily flat weight is transported with factor one. -/
theorem chartWeight_transition {E : Type*} {h Q Q' : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQ' : 0 < Q')
    {p : ChartPoint} (hp : 0 < p.2.2) (ζ : ℝ → E) :
    chartWeight h ζ (chartTransition h Q Q' p) = chartWeight h ζ p :=
  congrArg ζ (chartX_transition hh hh1 hQ hQ' hp)

/-- The lesser of one and the two logarithmic distances to fixed profile
edges. Positivity is asserted only inside a positive profile interval. -/
noncomputable def profileLogDistance (left right X : ℝ) : ℝ :=
  min 1 (min (Real.log X - Real.log left) (Real.log right - Real.log X))

theorem profileLogDistance_pos {left right X : ℝ} (hl : 0 < left)
    (hLX : left < X) (hXR : X < right) : 0 < profileLogDistance left right X := by
  exact lt_min zero_lt_one (lt_min (sub_pos.mpr (Real.log_lt_log hl hLX))
    (sub_pos.mpr (Real.log_lt_log (hl.trans hLX) hXR)))

noncomputable def chartLogDistance (h left right : ℝ) (p : ChartPoint) : ℝ :=
  profileLogDistance left right (chartX h p)

theorem chartLogDistance_transition {h Q Q' : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQ' : 0 < Q')
    {p : ChartPoint} (hp : 0 < p.2.2) (left right : ℝ) :
    chartLogDistance h left right (chartTransition h Q Q' p) =
      chartLogDistance h left right p :=
  congrArg (profileLogDistance left right) (chartX_transition hh hh1 hQ hQ' hp)

/-- Exact transport includes square-root flat weights and every real edge
power, including the negative powers used for derivative losses. -/
theorem chartWeightedFactor_transition {h Q Q' : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQ' : 0 < Q')
    {p : ChartPoint} (hp : 0 < p.2.2) (ζ : ℝ → ℝ) (left right exponent : ℝ) :
    Real.sqrt (chartWeight h ζ (chartTransition h Q Q' p)) *
        chartLogDistance h left right (chartTransition h Q Q' p) ^ exponent =
      Real.sqrt (chartWeight h ζ p) * chartLogDistance h left right p ^ exponent := by
  rw [chartWeight_transition hh hh1 hQ hQ' hp,
    chartLogDistance_transition hh hh1 hQ hQ' hp]

end NavierStokes.SimilarityHomogeneity
