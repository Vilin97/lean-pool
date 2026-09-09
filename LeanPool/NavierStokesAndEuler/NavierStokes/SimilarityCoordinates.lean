/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Analytic existence of the similarity coordinates

Here `a = 2h`. We construct the unique positive solution of
`τ = q - z² q^a` for `0 < a < 1` and `τ > 0`.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.SimilarityCoordinates

/-- Forward scalar, given by `q - z ^ 2 * q ^ a`. -/
def forwardScalar (a z q : ℝ) : ℝ := q - z ^ 2 * q ^ a

theorem forwardScalar_factor {q : ℝ} (hq : 0 < q) (a z : ℝ) :
    forwardScalar a z q = q ^ a * (q ^ (1 - a) - z ^ 2) := by
  have hpow : q ^ a * q ^ (1 - a) = q := by
    rw [← Real.rpow_add hq]
    have he : a + (1 - a) = 1 := by ring
    rw [he, Real.rpow_one]
  unfold forwardScalar
  rw [mul_sub, hpow]
  ring

/-- A positive solution exists. The proof uses the intermediate value
theorem after the change of variable `w = q^(1-a)`. -/
theorem exists_positive_solution {a τ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hτ : 0 < τ) (z : ℝ) : ∃ q : ℝ, 0 < q ∧ forwardScalar a z q = τ := by
  let p : ℝ := a / (1 - a)
  have hd : 0 < 1 - a := sub_pos.mpr ha1
  have hp : 0 < p := div_pos ha hd
  let w₁ : ℝ := z ^ 2 + τ + 1
  let g : ℝ → ℝ := fun w => w ^ p * (w - z ^ 2)
  have hw₁ : 1 ≤ w₁ := by dsimp [w₁]; nlinarith [sq_nonneg z]
  have hg : Continuous g :=
    (Real.continuous_rpow_const hp.le).mul (continuous_id.sub continuous_const)
  have hg₀ : g (z ^ 2) = 0 := by simp [g]
  have hg₁ : τ ≤ g w₁ := by
    have hw : 1 ≤ w₁ ^ p := by
      simpa only [Real.one_rpow] using
        (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hw₁ hp.le)
    dsimp [g, w₁] at *
    nlinarith
  have hab : z ^ 2 ≤ w₁ := by dsimp [w₁]; linarith
  obtain ⟨w, hw, hgw⟩ := intermediate_value_Icc hab hg.continuousOn
    (show τ ∈ Icc (g (z ^ 2)) (g w₁) by rw [hg₀]; exact ⟨hτ.le, hg₁⟩)
  have hw₀ : 0 ≤ w := (sq_nonneg z).trans hw.1
  have hwpos : 0 < w := by
    by_contra! hn
    have hwzero : w = 0 := le_antisymm hn hw₀
    have : g w = 0 := by simp [g, hwzero, Real.zero_rpow hp.ne']
    linarith
  let q : ℝ := w ^ (1 - a)⁻¹
  have hq : 0 < q := Real.rpow_pos_of_pos hwpos _
  have hqa : q ^ a = w ^ p := by
    dsimp [q, p]
    rw [← Real.rpow_mul hw₀]
    congr 1
    ring
  have hqe : q = w ^ p * w := by
    dsimp [q]
    have he : (1 - a)⁻¹ = p + 1 := by
      dsimp [p]
      field_simp; ring
    rw [he, Real.rpow_add hwpos, Real.rpow_one]
  refine ⟨q, hq, ?_⟩
  unfold forwardScalar
  rw [hqa, hqe]
  calc
    w ^ p * w - z ^ 2 * w ^ p = g w := by dsimp [g]; ring
    _ = τ := hgw

/-- On the region where the scalar map is positive, it is strictly
increasing. No global monotonicity below the positive branch is asserted. -/
theorem forwardScalar_lt {a z q₁ q₂ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hq₁ : 0 < q₁) (hqq : q₁ < q₂) (hf₁ : 0 < forwardScalar a z q₁) :
    forwardScalar a z q₁ < forwardScalar a z q₂ := by
  have hq₂ : 0 < q₂ := hq₁.trans hqq
  have hp₁ : 0 < q₁ ^ a := Real.rpow_pos_of_pos hq₁ _
  have hp : q₁ ^ a ≤ q₂ ^ a := Real.rpow_le_rpow hq₁.le hqq.le ha.le
  have hd : q₁ ^ (1 - a) - z ^ 2 < q₂ ^ (1 - a) - z ^ 2 :=
    sub_lt_sub_right (Real.rpow_lt_rpow hq₁.le hqq (sub_pos.mpr ha1)) _
  rw [forwardScalar_factor hq₁] at hf₁ ⊢
  rw [forwardScalar_factor hq₂]
  have hd₁ : 0 < q₁ ^ (1 - a) - z ^ 2 := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hp₁.le hn)) hf₁
  calc
    q₁ ^ a * (q₁ ^ (1 - a) - z ^ 2) <
        q₁ ^ a * (q₂ ^ (1 - a) - z ^ 2) := mul_lt_mul_of_pos_left hd hp₁
    _ ≤ q₂ ^ a * (q₂ ^ (1 - a) - z ^ 2) :=
      mul_le_mul_of_nonneg_right hp (hd₁.le.trans hd.le)

theorem positive_solution_unique {a τ z q₁ q₂ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (he₁ : forwardScalar a z q₁ = τ) (he₂ : forwardScalar a z q₂ = τ) : q₁ = q₂ := by
  rcases lt_trichotomy q₁ q₂ with hlt | heq | hgt
  · have := forwardScalar_lt ha ha1 hq₁ hlt (by rwa [he₁])
    rw [he₁, he₂] at this
    exact (lt_irrefl τ this).elim
  · exact heq
  · have := forwardScalar_lt ha ha1 hq₂ hgt (by rwa [he₂])
    rw [he₁, he₂] at this
    exact (lt_irrefl τ this).elim

theorem existsUnique_positive_solution {a τ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hτ : 0 < τ) (z : ℝ) : ∃! q : ℝ, 0 < q ∧ forwardScalar a z q = τ := by
  obtain ⟨q, hq, he⟩ := exists_positive_solution ha ha1 hτ z
  exact ⟨q, ⟨hq, he⟩, fun q' hq' =>
    positive_solution_unique ha ha1 hτ hq'.1 hq hq'.2 he⟩

/-- The unique positive coordinate, with value `1` outside the intended
parameter domain. Only its restriction to that open domain is used. -/
def coordinateQ (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  if hp : 0 < a ∧ a < 1 ∧ 0 < p.1 then
    Classical.choose (exists_positive_solution hp.1 hp.2.1 hp.2.2 p.2)
  else 1

theorem coordinateQ_spec {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    0 < coordinateQ a p ∧ forwardScalar a p.2 (coordinateQ a p) = p.1 := by
  simp only [coordinateQ, dite_eq_left (show 0 < a ∧ a < 1 ∧ 0 < p.1 from ⟨ha, ha1, hp⟩)]
  exact Classical.choose_spec (exists_positive_solution ha ha1 hp p.2)

theorem eq_coordinateQ {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) {q : ℝ} (hq : 0 < q)
    (he : forwardScalar a p.2 q = p.1) : q = coordinateQ a p := by
  have hs := coordinateQ_spec ha ha1 hp
  exact positive_solution_unique ha ha1 hp hq hs.1 he hs.2

/-- Scalar slope, given by `1 - z ^ 2 * a * q ^ (a - 1)`. -/
def scalarSlope (a z q : ℝ) : ℝ := 1 - z ^ 2 * a * q ^ (a - 1)

theorem scalarSlope_pos {a z q : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hq : 0 < q) (hf : 0 < forwardScalar a z q) : 0 < scalarSlope a z q := by
  have hsmall : z ^ 2 * q ^ a / q < 1 := by
    apply (div_lt_one hq).mpr
    dsimp [forwardScalar] at hf
    linarith
  have hprod := mul_nonneg ha.le (sub_nonneg.mpr hsmall.le)
  have hpos : 0 < 1 - a * (z ^ 2 * q ^ a / q) := by nlinarith
  unfold scalarSlope
  rw [Real.rpow_sub_one hq.ne']
  convert! hpos using 1
  ring

/-- The forward map whose inverse supplies smooth dependence on `(τ,z)`. -/
def forwardMap (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (forwardScalar a p.2 p.1, p.2)

/-- Explicit invertible triangular linear map used by the inverse theorem. -/
def triangularEquiv (m b : ℝ) (hm : m ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun v := (m * v.1 + b * v.2, v.2)
  invFun w := ((w.1 - b * w.2) / m, w.2)
  left_inv := by
    intro v
    apply Prod.ext
    · dsimp
      field_simp; ring
    · rfl
  right_inv := by
    intro v
    apply Prod.ext
    · dsimp
      field_simp; ring
    · rfl
  map_add' := by
    intro v w
    apply Prod.ext
    · dsimp
      ring
    · rfl
  map_smul' := by
    intro c v
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
      ring
    · rfl
  continuous_toFun :=
    ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)).prodMk continuous_snd
  continuous_invFun :=
    ((continuous_fst.sub (continuous_const.mul continuous_snd)).div_const m).prodMk
      continuous_snd

theorem forwardMap_smooth {a : ℝ} {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (forwardMap a) p := by
  exact (contDiffAt_fst.sub
    ((contDiffAt_snd.pow 2).mul (contDiffAt_fst.rpow_const_of_ne hp))).prodMk
      contDiffAt_snd

theorem forwardMap_hasFDerivAt {a : ℝ} {p : ℝ × ℝ} (hp : p.1 ≠ 0)
    (hm : scalarSlope a p.2 p.1 ≠ 0) :
    HasFDerivAt (forwardMap a)
      (triangularEquiv (scalarSlope a p.2 p.1) (-2 * p.2 * p.1 ^ a) hm :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  have hf : HasFDerivAt (fun v : ℝ × ℝ => v.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hz : HasFDerivAt (fun v : ℝ × ℝ => v.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hder := (hf.sub ((hz.mul hz).mul (hf.rpow_const (p := a) (Or.inl hp)))).prodMk hz
  have hlin :
      (triangularEquiv (scalarSlope a p.2 p.1) (-2 * p.2 * p.1 ^ a) hm :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
      ((ContinuousLinearMap.fst ℝ ℝ ℝ -
          ((p.2 * p.2) • ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
            p.1 ^ a • (p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ +
              p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ))).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · change (1 - p.2 ^ 2 * a * p.1 ^ (a - 1)) * v.1 +
          (-2 * p.2 * p.1 ^ a) * v.2 =
        v.1 - ((p.2 * p.2) * ((a * p.1 ^ (a - 1)) * v.1) +
          p.1 ^ a * (p.2 * v.2 + p.2 * v.2))
      ring
    · rfl
  rw [hlin]
  change HasFDerivAt (fun v : ℝ × ℝ => (v.1 - v.2 ^ 2 * v.1 ^ a, v.2)) _ p
  simpa only [Pi.mul_apply, Pi.sub_apply, pow_two] using hder

/-- Inverse map, given by `(coordinateQ a p, p.2)`. -/
def inverseMap (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (coordinateQ a p, p.2)

theorem inverseMap_forwardMap {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hq : 0 < p.1) (hF : 0 < forwardScalar a p.2 p.1) :
    inverseMap a (forwardMap a p) = p := by
  apply Prod.ext
  · exact (eq_coordinateQ ha ha1 hF hq rfl).symm
  · rfl

theorem eventually_inverseMap_forwardMap {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hq : 0 < p.1) (hF : 0 < forwardScalar a p.2 p.1) :
    ∀ᶠ x in 𝓝 p, inverseMap a (forwardMap a x) = x := by
  have hqev : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1 :=
    continuousAt_fst.eventually (Ioi_mem_nhds hq)
  have hFev : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < forwardScalar a x.2 x.1 :=
    (forwardMap_smooth hq.ne').continuousAt.fst.eventually (Ioi_mem_nhds hF)
  filter_upwards [hqev, hFev] with x hqx hFx
  exact inverseMap_forwardMap ha ha1 hqx hFx

/-- The canonical inverse is smooth at every image point on the positive
branch, by the actual inverse function theorem. -/
theorem inverseMap_smooth_at_image {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hq : 0 < p.1) (hF : 0 < forwardScalar a p.2 p.1) :
    ContDiffAt ℝ ∞ (inverseMap a) (forwardMap a p) := by
  have hm := (scalarSlope_pos ha ha1 hq hF).ne'
  have hsm := forwardMap_smooth (a := a) hq.ne'
  have hder := forwardMap_hasFDerivAt (a := a) hq.ne' hm
  have horder : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hsm.hasStrictFDerivAt' hder horder
  have heq := hs.localInverse_unique (eventually_inverseMap_forwardMap ha ha1 hq hF)
  exact (hsm.to_localInverse hder horder).congr_of_eventuallyEq heq

theorem inverseMap_hasFDerivAt_image {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hq : 0 < p.1) (hF : 0 < forwardScalar a p.2 p.1) :
    HasFDerivAt (inverseMap a)
      ((triangularEquiv (scalarSlope a p.2 p.1) (-2 * p.2 * p.1 ^ a)
        (scalarSlope_pos ha ha1 hq hF).ne').symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      (forwardMap a p) := by
  have hsm := forwardMap_smooth (a := a) hq.ne'
  have hder := forwardMap_hasFDerivAt (a := a) hq.ne'
    (scalarSlope_pos ha ha1 hq hF).ne'
  have hs := hsm.hasStrictFDerivAt' hder (by simp)
  exact (hs.to_local_left_inverse
    (eventually_inverseMap_forwardMap ha ha1 hq hF)).hasFDerivAt

/-- Smooth dependence on both physical parameters `(τ,z)` for `τ>0`. -/
theorem coordinateQ_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : ContDiffAt ℝ ∞ (coordinateQ a) p := by
  have hspec := coordinateQ_spec ha ha1 hp
  have hF : 0 < forwardScalar a p.2 (coordinateQ a p) := by rwa [hspec.2]
  have hsm := inverseMap_smooth_at_image ha ha1 (p := (coordinateQ a p, p.2)) hspec.1 hF
  have himage : forwardMap a (coordinateQ a p, p.2) = p := by
    exact Prod.ext hspec.2 rfl
  rw [himage] at hsm
  exact hsm.fst

theorem coordinateQ_smoothOn {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ContDiffOn ℝ ∞ (coordinateQ a) {p : ℝ × ℝ | 0 < p.1} := by
  intro p hp
  exact (coordinateQ_smooth ha ha1 hp).contDiffWithinAt

/-- Full Fréchet derivative of the actual implicitly defined coordinate. -/
theorem coordinateQ_fderiv_apply {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) (v : ℝ × ℝ) :
    fderiv ℝ (coordinateQ a) p v =
      (v.1 + 2 * p.2 * coordinateQ a p ^ a * v.2) /
        scalarSlope a p.2 (coordinateQ a p) := by
  have hspec := coordinateQ_spec ha ha1 hp
  have hF : 0 < forwardScalar a p.2 (coordinateQ a p) := by rwa [hspec.2]
  have hd := inverseMap_hasFDerivAt_image ha ha1
    (p := (coordinateQ a p, p.2)) hspec.1 hF
  have himage : forwardMap a (coordinateQ a p, p.2) = p := Prod.ext hspec.2 rfl
  rw [himage] at hd
  change fderiv ℝ (fun x => (inverseMap a x).1) p v = _
  rw [hd.fst.fderiv]
  change (v.1 - (-2 * p.2 * coordinateQ a p ^ a) * v.2) /
    scalarSlope a p.2 (coordinateQ a p) = _
  ring

theorem coordinateQ_hasDerivAt_tau {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun t => coordinateQ a (t, z))
      (1 / scalarSlope a z (coordinateQ a (τ, z))) τ := by
  have hd := ((coordinateQ_smooth ha ha1 (p := (τ, z)) hτ).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ z))
  rw [coordinateQ_fderiv_apply ha ha1 hτ] at hc
  simpa only [Function.comp_def, id_eq, Prod.fst, Prod.snd, mul_zero, add_zero] using hc

theorem coordinateQ_hasDerivAt_z {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun x => coordinateQ a (τ, x))
      (2 * z * coordinateQ a (τ, z) ^ a /
        scalarSlope a z (coordinateQ a (τ, z))) z := by
  have hd := ((coordinateQ_smooth ha ha1 (p := (τ, z)) hτ).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt z ((hasDerivAt_const z τ).prodMk (hasDerivAt_id z))
  rw [coordinateQ_fderiv_apply ha ha1 hτ] at hc
  simpa only [Function.comp_def, id_eq, Prod.fst, Prod.snd, mul_one, zero_add] using hc

/-- The physical time is `t=1-τ`, giving the required negative sign. -/
theorem coordinateQ_hasDerivAt_time {a t z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t < 1) :
    HasDerivAt (fun s => coordinateQ a (1 - s, z))
      (-1 / scalarSlope a z (coordinateQ a (1 - t, z))) t := by
  have hc := (coordinateQ_hasDerivAt_tau (z := z) ha ha1 (sub_pos.mpr ht)).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! hc using 1
  ring

/-- Coordinate eta, given by `p.2 / coordinateQ a p ^ ((1 - a) / 2)`. -/
def coordinateEta (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 / coordinateQ a p ^ ((1 - a) / 2)

theorem coordinateEta_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : ContDiffAt ℝ ∞ (coordinateEta a) p := by
  have hq := (coordinateQ_spec ha ha1 hp).1
  exact contDiffAt_snd.div ((coordinateQ_smooth ha ha1 hp).rpow_const_of_ne hq.ne')
    (Real.rpow_pos_of_pos hq _).ne'

theorem coordinateEta_sq {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    coordinateEta a p ^ 2 = p.2 ^ 2 * coordinateQ a p ^ a / coordinateQ a p := by
  have hq := (coordinateQ_spec ha ha1 hp).1
  have hpow := (Real.rpow_pos_of_pos hq a).ne'
  unfold coordinateEta
  rw [div_pow, ← Real.rpow_mul_natCast hq.le]
  have he : ((1 - a) / 2) * (2 : ℕ) = 1 - a := by ring
  rw [he, Real.rpow_sub hq, Real.rpow_one]
  field_simp

theorem coordinateEta_sq_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : coordinateEta a p ^ 2 < 1 := by
  have hq := coordinateQ_spec ha ha1 hp
  rw [coordinateEta_sq ha ha1 hp]
  apply (div_lt_one hq.1).mpr
  dsimp [forwardScalar] at hq
  linarith [hq.2]

theorem coordinateEta_abs_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : |coordinateEta a p| < 1 := by
  have hs := coordinateEta_sq_lt_one ha ha1 hp
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- The branch lies strictly beyond the manuscript's threshold
`|z|^(1/D)`, where `D=(1-a)/2`. -/
theorem coordinateQ_above_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    |p.2| ^ (((1 - a) / 2)⁻¹) < coordinateQ a p := by
  have hq := (coordinateQ_spec ha ha1 hp).1
  have hd : 0 < (1 - a) / 2 := by linarith
  have hpow : 0 < coordinateQ a p ^ ((1 - a) / 2) := Real.rpow_pos_of_pos hq _
  have hη := coordinateEta_abs_lt_one ha ha1 hp
  unfold coordinateEta at hη
  rw [abs_div, abs_of_pos hpow] at hη
  exact (Real.rpow_inv_lt_iff_of_pos (abs_nonneg p.2) hq.le hd).mpr
    ((div_lt_one hpow).mp hη)

/-- Both implicit descriptions in equation (3) agree for the constructed
coordinates: `τ=q(1-η²)`. -/
theorem tau_coordinate_identity {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 = coordinateQ a p * (1 - coordinateEta a p ^ 2) := by
  have hq := coordinateQ_spec ha ha1 hp
  calc
    p.1 = coordinateQ a p - p.2 ^ 2 * coordinateQ a p ^ a := hq.2.symm
    _ = _ := by
      rw [coordinateEta_sq ha ha1 hp]
      field_simp [hq.1.ne']

/-- The actual Jacobian denominator equals the manuscript's `L`. -/
theorem scalarSlope_eq_L {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    scalarSlope a p.2 (coordinateQ a p) = 1 - a * coordinateEta a p ^ 2 := by
  have hq := (coordinateQ_spec ha ha1 hp).1
  unfold scalarSlope
  rw [Real.rpow_sub_one hq.ne', coordinateEta_sq ha ha1 hp]
  ring

theorem coordinateQ_hasDerivAt_tau_L {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun t => coordinateQ a (t, z))
      (1 / (1 - a * coordinateEta a (τ, z) ^ 2)) τ := by
  have hc := coordinateQ_hasDerivAt_tau (z := z) ha ha1 hτ
  rwa [scalarSlope_eq_L ha ha1 (p := (τ, z)) hτ] at hc

theorem coordinateQ_hasDerivAt_time_L {a t z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t < 1) :
    HasDerivAt (fun s => coordinateQ a (1 - s, z))
      (-1 / (1 - a * coordinateEta a (1 - t, z) ^ 2)) t := by
  have hc := coordinateQ_hasDerivAt_time (z := z) ha ha1 ht
  rwa [scalarSlope_eq_L ha ha1 (p := (1 - t, z)) (sub_pos.mpr ht)] at hc

theorem coordinateEta_hasDerivAt_tau {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun t => coordinateEta a (t, z))
      (-((1 - a) / 2) * coordinateEta a (τ, z) /
        (coordinateQ a (τ, z) * scalarSlope a z (coordinateQ a (τ, z)))) τ := by
  have hq := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  have hm := (scalarSlope_pos ha ha1 hq.1 (by rwa [hq.2])).ne'
  have hpow := (Real.rpow_pos_of_pos hq.1 ((1 - a) / 2)).ne'
  have hc := (hasDerivAt_const τ z).div
    ((coordinateQ_hasDerivAt_tau ha ha1 hτ).rpow_const
      (p := (1 - a) / 2) (Or.inl hq.1.ne')) hpow
  change HasDerivAt (fun t => z / coordinateQ a (t, z) ^ ((1 - a) / 2)) _ τ
  convert! hc using 1
  unfold coordinateEta
  rw [Real.rpow_sub_one hq.1.ne']
  field_simp [hq.1.ne', hpow, hm]; ring

theorem coordinateEta_hasDerivAt_z {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun x => coordinateEta a (τ, x))
      ((1 - coordinateEta a (τ, z) ^ 2) /
        (coordinateQ a (τ, z) ^ ((1 - a) / 2) *
          scalarSlope a z (coordinateQ a (τ, z)))) z := by
  have hq := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  have hm := (scalarSlope_pos ha ha1 hq.1 (by rwa [hq.2])).ne'
  have hpow := (Real.rpow_pos_of_pos hq.1 ((1 - a) / 2)).ne'
  have hc := (hasDerivAt_id z).div
    ((coordinateQ_hasDerivAt_z ha ha1 hτ).rpow_const
      (p := (1 - a) / 2) (Or.inl hq.1.ne')) hpow
  change HasDerivAt (fun x => x / coordinateQ a (τ, x) ^ ((1 - a) / 2)) _ z
  convert! hc using 1
  simp only [id_eq]
  rw [coordinateEta_sq ha ha1 hτ, Real.rpow_sub_one hq.1.ne']
  field_simp [hq.1.ne', hpow, hm]
  unfold scalarSlope
  rw [Real.rpow_sub_one hq.1.ne']
  field_simp [hq.1.ne']; ring

theorem coordinateEta_hasDerivAt_time {a t z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t < 1) :
    HasDerivAt (fun s => coordinateEta a (1 - s, z))
      (((1 - a) / 2) * coordinateEta a (1 - t, z) /
        (coordinateQ a (1 - t, z) *
          (1 - a * coordinateEta a (1 - t, z) ^ 2))) t := by
  have hc := (coordinateEta_hasDerivAt_tau (z := z) ha ha1 (sub_pos.mpr ht)).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  rw [scalarSlope_eq_L ha ha1 (p := (1 - t, z)) (sub_pos.mpr ht)] at hc
  convert! hc using 1
  ring

theorem coordinateEta_hasDerivAt_z_L {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun x => coordinateEta a (τ, x))
      ((1 - coordinateEta a (τ, z) ^ 2) /
        (coordinateQ a (τ, z) ^ ((1 - a) / 2) *
          (1 - a * coordinateEta a (τ, z) ^ 2))) z := by
  have hc := coordinateEta_hasDerivAt_z (z := z) ha ha1 hτ
  rwa [scalarSlope_eq_L ha ha1 (p := (τ, z)) hτ] at hc

theorem coordinateQ_hasDerivAt_z_L {a τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun x => coordinateQ a (τ, x))
      (2 * coordinateEta a (τ, z) * coordinateQ a (τ, z) ^ (1 - (1 - a) / 2) /
        (1 - a * coordinateEta a (τ, z) ^ 2)) z := by
  have hq := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  have hpow := (Real.rpow_pos_of_pos hq.1 ((1 - a) / 2)).ne'
  have hc := coordinateQ_hasDerivAt_z (z := z) ha ha1 hτ
  rw [scalarSlope_eq_L ha ha1 (p := (τ, z)) hτ] at hc
  have hnum : 2 * coordinateEta a (τ, z) * coordinateQ a (τ, z) ^ (1 - (1 - a) / 2) =
      2 * z * coordinateQ a (τ, z) ^ a := by
    have he : 1 - (1 - a) / 2 = a + (1 - a) / 2 := by ring
    rw [he, Real.rpow_add hq.1]
    unfold coordinateEta
    field_simp [hpow]
  rw [hnum]
  exact hc

/-- Coordinate X, given by `s / coordinateQ a p`. -/
def coordinateX (a s : ℝ) (p : ℝ × ℝ) : ℝ := s / coordinateQ a p

theorem coordinateX_smooth {a s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : ContDiffAt ℝ ∞ (coordinateX a s) p := by
  exact contDiffAt_const.div (coordinateQ_smooth ha ha1 hp)
    (coordinateQ_spec ha ha1 hp).1.ne'

theorem coordinateX_hasDerivAt_time {a s t z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ht : t < 1) :
    HasDerivAt (fun u => coordinateX a s (1 - u, z))
      (coordinateX a s (1 - t, z) /
        (coordinateQ a (1 - t, z) * (1 - a * coordinateEta a (1 - t, z) ^ 2))) t := by
  have hτ : 0 < 1 - t := sub_pos.mpr ht
  have hq := coordinateQ_spec ha ha1 (p := (1 - t, z)) hτ
  have hm : 1 - a * coordinateEta a (1 - t, z) ^ 2 ≠ 0 := by
    rw [← scalarSlope_eq_L ha ha1 (sub_pos.mpr ht)]
    exact (scalarSlope_pos ha ha1 hq.1 (by rwa [hq.2])).ne'
  have hc := (hasDerivAt_const t s).div (coordinateQ_hasDerivAt_time_L ha ha1 ht) hq.1.ne'
  change HasDerivAt (fun u => s / coordinateQ a (1 - u, z)) _ t
  convert! hc using 1
  unfold coordinateX
  field_simp [hq.1.ne', hm]
  ring_nf

theorem coordinateX_hasDerivAt_z {a s τ z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hτ : 0 < τ) :
    HasDerivAt (fun x => coordinateX a s (τ, x))
      (-2 * coordinateEta a (τ, z) * coordinateX a s (τ, z) /
        (coordinateQ a (τ, z) ^ ((1 - a) / 2) *
          (1 - a * coordinateEta a (τ, z) ^ 2))) z := by
  have hq := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  have hpow := (Real.rpow_pos_of_pos hq.1 ((1 - a) / 2)).ne'
  have hm : 1 - a * coordinateEta a (τ, z) ^ 2 ≠ 0 := by
    rw [← scalarSlope_eq_L ha ha1 hτ]
    exact (scalarSlope_pos ha ha1 hq.1 (by rwa [hq.2])).ne'
  have hc := (hasDerivAt_const z s).div (coordinateQ_hasDerivAt_z_L ha ha1 hτ) hq.1.ne'
  change HasDerivAt (fun x => s / coordinateQ a (τ, x)) _ z
  convert! hc using 1
  rw [Real.rpow_sub hq.1, Real.rpow_one]
  unfold coordinateX
  field_simp [hq.1.ne', hpow, hm]; ring

/-- Joint physical `(t,z)` smoothness of the actual coordinate functions. -/
theorem physical_coordinates_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : p.1 < 1) :
    ContDiffAt ℝ ∞
      (fun x : ℝ × ℝ =>
        (coordinateQ a (1 - x.1, x.2), coordinateEta a (1 - x.1, x.2))) p := by
  have hm : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => (1 - x.1, x.2)) p :=
    (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
  exact ((coordinateQ_smooth ha ha1 (p := (1 - p.1, p.2)) (sub_pos.mpr hp)).prodMk
    (coordinateEta_smooth ha ha1 (p := (1 - p.1, p.2)) (sub_pos.mpr hp))).comp p hm

/-- Equation (3), with exactly the manuscript's exponent `2h`. -/
theorem manuscript_coordinate_existsUnique {h τ : ℝ} (hh : 0 < h)
    (hh1 : h < 1 / 2) (hτ : 0 < τ) (z : ℝ) :
    ∃! q : ℝ, 0 < q ∧ q - z ^ 2 * q ^ (2 * h) = τ := by
  exact existsUnique_positive_solution (by linarith) (by linarith) hτ z

end NavierStokes.SimilarityCoordinates
