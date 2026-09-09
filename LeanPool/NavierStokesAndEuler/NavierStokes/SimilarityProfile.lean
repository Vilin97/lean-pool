/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.CoordinateAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Actual derivatives of reconstructed similarity profiles

The physical variables are `(t,s,z)`, with `s = r²/2`. Inner profiles use
`(X,η)`. All partial derivatives below are genuine Fréchet derivatives.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SimilarityProfile

open Set Filter
open scoped Topology ContDiff

/-- Physical point: an abbreviation for `ℝ × (ℝ × ℝ)`. -/
abbrev PhysicalPoint := ℝ × (ℝ × ℝ)
/-- Inner point: an abbreviation for `ℝ × ℝ`. -/
abbrev InnerPoint := ℝ × ℝ
/-- Inner profile: an abbreviation for `InnerPoint → ℝ`. -/
abbrev InnerProfile := InnerPoint → ℝ
/-- Physical profile: an abbreviation for `PhysicalPoint → ℝ`. -/
abbrev PhysicalProfile := PhysicalPoint → ℝ

/-- D: an abbreviation for `CoordinateAlgebra.D`. -/
abbrev D := CoordinateAlgebra.D
/-- D: an abbreviation for `CoordinateAlgebra.d`. -/
abbrev d := CoordinateAlgebra.d
/-- L: an abbreviation for `CoordinateAlgebra.L`. -/
abbrev L := CoordinateAlgebra.L

/-- Q, given by `SimilarityCoordinates.coordinateQ (2 * h) (1 - p.1, p.2.2)`. -/
def q (h : ℝ) (p : PhysicalPoint) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) (1 - p.1, p.2.2)

/-- Eta, given by `SimilarityCoordinates.coordinateEta (2 * h) (1 - p.1, p.2.2)`. -/
def eta (h : ℝ) (p : PhysicalPoint) : ℝ :=
  SimilarityCoordinates.coordinateEta (2 * h) (1 - p.1, p.2.2)

/-- X, given by `p.2.1 / q h p`. -/
def X (h : ℝ) (p : PhysicalPoint) : ℝ := p.2.1 / q h p
/-- Inner, given by `(X h p, eta h p)`. -/
def inner (h : ℝ) (p : PhysicalPoint) : InnerPoint := (X h p, eta h p)

/-- Partial X, given by `fderiv ℝ f w (1, 0)`. -/
def partialX (f : InnerProfile) (w : InnerPoint) : ℝ := fderiv ℝ f w (1, 0)
/-- Partial eta, given by `fderiv ℝ f w (0, 1)`. -/
def partialEta (f : InnerProfile) (w : InnerPoint) : ℝ := fderiv ℝ f w (0, 1)

/-- T, given by `CoordinateAlgebra.timeCoeff b h w.2 w.1 (f w) (partialX f w) (partialEta f w)`. -/
def T (h b : ℝ) (f : InnerProfile) (w : InnerPoint) : ℝ :=
  CoordinateAlgebra.timeCoeff b h w.2 w.1 (f w) (partialX f w) (partialEta f w)

/-- Z, given by `CoordinateAlgebra.axialCoeff b h w.2 w.1 (f w) (partialX f w) (partialEta f
w)`. -/
def Z (h b : ℝ) (f : InnerProfile) (w : InnerPoint) : ℝ :=
  CoordinateAlgebra.axialCoeff b h w.2 w.1 (f w) (partialX f w) (partialEta f w)

/-- Pullback, given by `q h p ^ b * f (inner h p)`. -/
def pullback (h b : ℝ) (f : InnerProfile) (p : PhysicalPoint) : ℝ :=
  q h p ^ b * f (inner h p)

/-- Partial T, given by `fderiv ℝ F p (1, (0, 0))`. -/
def partialT (F : PhysicalProfile) (p : PhysicalPoint) : ℝ := fderiv ℝ F p (1, (0, 0))
/-- Partial S, given by `fderiv ℝ F p (0, (1, 0))`. -/
def partialS (F : PhysicalProfile) (p : PhysicalPoint) : ℝ := fderiv ℝ F p (0, (1, 0))
/-- Partial Z, given by `fderiv ℝ F p (0, (0, 1))`. -/
def partialZ (F : PhysicalProfile) (p : PhysicalPoint) : ℝ := fderiv ℝ F p (0, (0, 1))

theorem D_eq (h : ℝ) : (1 - 2 * h) / 2 = D h := by unfold D CoordinateAlgebra.D; ring

theorem q_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : 0 < q h p :=
  (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)).1

theorem eta_sq_lt_one {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : eta h p ^ 2 < 1 :=
  SimilarityCoordinates.coordinateEta_sq_lt_one (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)

theorem L_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : 0 < L h (eta h p) :=
  CoordinateAlgebra.L_pos hh.le hh1 (eta_sq_lt_one hh hh1 hp).le

theorem q_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (q h) p := by
  exact (SimilarityCoordinates.coordinateQ_smooth (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)).comp p
      ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd.snd)

theorem eta_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (eta h) p := by
  exact (SimilarityCoordinates.coordinateEta_smooth (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)).comp p
      ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd.snd)

theorem inner_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (inner h) p := by
  exact (contDiffAt_snd.fst.div (q_smoothAt hh hh1 hp) (q_pos hh hh1 hp).ne').prodMk
    (eta_smoothAt hh hh1 hp)

theorem pullback_smoothAt {h b : ℝ} {f : InnerProfile} {n : ℕ∞}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : ContDiffAt ℝ n f (inner h p)) : ContDiffAt ℝ n (pullback h b f) p := by
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : n ≤ (⊤ : ℕ∞))
  exact (((q_smoothAt hh hh1 hp).of_le hn).rpow_const_of_ne (q_pos hh hh1 hp).ne').mul
    (hf.comp p ((inner_smoothAt hh hh1 hp).of_le hn))

theorem pullback_differentiableAt {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) : DifferentiableAt ℝ (pullback h b f) p := by
  exact (((q_smoothAt hh hh1 hp).differentiableAt (by simp)).rpow_const
    (Or.inl (q_pos hh hh1 hp).ne')).mul
      (hf.comp p ((inner_smoothAt hh hh1 hp).differentiableAt (by simp)))

theorem q_hasDerivAt_time {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun t => q h (t, p.2)) (CoordinateAlgebra.qTime h (eta h p)) p.1 := by
  simpa only [q, eta, CoordinateAlgebra.qTime, CoordinateAlgebra.L] using
    SimilarityCoordinates.coordinateQ_hasDerivAt_time_L (a := 2 * h)
      (z := p.2.2) (by linarith) (by linarith) hp

theorem eta_hasDerivAt_time {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun t => eta h (t, p.2))
      (CoordinateAlgebra.etaTime (q h p) h (eta h p)) p.1 := by
  simpa only [q, eta, CoordinateAlgebra.etaTime, CoordinateAlgebra.L, D_eq] using
    SimilarityCoordinates.coordinateEta_hasDerivAt_time (a := 2 * h)
      (z := p.2.2) (by linarith) (by linarith) hp

theorem X_hasDerivAt_time {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun t => X h (t, p.2))
      (CoordinateAlgebra.xTime (q h p) h (eta h p) (X h p)) p.1 := by
  simpa only [q, eta, X, CoordinateAlgebra.xTime, CoordinateAlgebra.L,
    SimilarityCoordinates.coordinateX] using
    SimilarityCoordinates.coordinateX_hasDerivAt_time (a := 2 * h)
      (s := p.2.1) (z := p.2.2) (by linarith) (by linarith) hp

theorem q_hasDerivAt_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun z => q h (p.1, (p.2.1, z)))
      (CoordinateAlgebra.qAxial (q h p) h (eta h p)) p.2.2 := by
  rw [CoordinateAlgebra.qAxial_rpow (q_pos hh hh1 hp)]
  simpa only [q, eta, CoordinateAlgebra.L, D_eq] using
    SimilarityCoordinates.coordinateQ_hasDerivAt_z_L (a := 2 * h)
      (τ := 1 - p.1) (z := p.2.2) (by linarith) (by linarith) (sub_pos.mpr hp)

theorem eta_hasDerivAt_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun z => eta h (p.1, (p.2.1, z)))
      (CoordinateAlgebra.etaAxial (q h p) h (eta h p)) p.2.2 := by
  simpa only [q, eta, CoordinateAlgebra.etaAxial, CoordinateAlgebra.L,
    CoordinateAlgebra.d, D_eq] using
    SimilarityCoordinates.coordinateEta_hasDerivAt_z_L (a := 2 * h)
      (τ := 1 - p.1) (z := p.2.2) (by linarith) (by linarith) (sub_pos.mpr hp)

theorem X_hasDerivAt_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    HasDerivAt (fun z => X h (p.1, (p.2.1, z)))
      (CoordinateAlgebra.xAxial (q h p) h (eta h p) (X h p)) p.2.2 := by
  simpa only [q, eta, X, CoordinateAlgebra.xAxial, CoordinateAlgebra.L,
    SimilarityCoordinates.coordinateX, D_eq] using
    SimilarityCoordinates.coordinateX_hasDerivAt_z (a := 2 * h)
      (s := p.2.1) (τ := 1 - p.1) (z := p.2.2)
      (by linarith) (by linarith) (sub_pos.mpr hp)

theorem fderiv_inner_apply (f : InnerProfile) (w v : InnerPoint) :
    fderiv ℝ f w v = partialX f w * v.1 + partialEta f w * v.2 := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul, partialX, partialEta]
  ring

/-- The physical time derivative, obtained by product and chain rules. -/
theorem hasDerivAt_pullback_time {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    HasDerivAt (fun t => pullback h b f (t, p.2))
      (pullback h (b - 1) (T h b f) p) p.1 := by
  have hc := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((X_hasDerivAt_time hh hh1 hp).prodMk (eta_hasDerivAt_time hh hh1 hp))
  have hm := ((q_hasDerivAt_time hh hh1 hp).rpow_const
    (p := b) (Or.inl (q_pos hh hh1 hp).ne')).mul hc
  rw [fderiv_inner_apply] at hm
  have he := CoordinateAlgebra.time_chain_coefficient (q_pos hh hh1 hp)
    b h (eta h p) (X h p) (f (inner h p)) (partialX f (inner h p)) (partialEta f (inner h p))
  have hr : CoordinateAlgebra.qTime h (eta h p) * b * q h p ^ (b - 1) * f (inner h p) +
      q h p ^ b * (partialX f (inner h p) * CoordinateAlgebra.xTime (q h p) h (eta h p) (X h p) +
        partialEta f (inner h p) * CoordinateAlgebra.etaTime (q h p) h (eta h p)) =
      pullback h (b - 1) (T h b f) p := by
    simpa only [pullback, T, inner, mul_comm, mul_left_comm, mul_assoc] using he
  exact hm.congr_deriv hr

/-- The physical axial derivative, including the change of both inner coordinates. -/
theorem hasDerivAt_pullback_z {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    HasDerivAt (fun z => pullback h b f (p.1, (p.2.1, z)))
      (pullback h (b - D h) (Z h b f) p) p.2.2 := by
  have hc := hf.hasFDerivAt.comp_hasDerivAt p.2.2
    ((X_hasDerivAt_z hh hh1 hp).prodMk (eta_hasDerivAt_z hh hh1 hp))
  have hm := ((q_hasDerivAt_z hh hh1 hp).rpow_const
    (p := b) (Or.inl (q_pos hh hh1 hp).ne')).mul hc
  rw [fderiv_inner_apply] at hm
  have he := CoordinateAlgebra.axial_chain_coefficient (q_pos hh hh1 hp)
    b h (eta h p) (X h p) (f (inner h p)) (partialX f (inner h p)) (partialEta f (inner h p))
  have hr : CoordinateAlgebra.qAxial (q h p) h (eta h p) * b * q h p ^ (b - 1) * f (inner h p) +
      q h p ^ b * (partialX f (inner h p) * CoordinateAlgebra.xAxial (q h p) h (eta h p) (X h p) +
        partialEta f (inner h p) * CoordinateAlgebra.etaAxial (q h p) h (eta h p)) =
      pullback h (b - D h) (Z h b f) p := by
    simpa only [pullback, Z, inner, mul_comm, mul_left_comm, mul_assoc] using he
  exact hm.congr_deriv hr

theorem hasDerivAt_pullback_s {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    HasDerivAt (fun s => pullback h b f (p.1, (s, p.2.2)))
      (pullback h (b - 1) (partialX f) p) p.2.1 := by
  have hx : HasDerivAt (fun s => s / q h p) (1 / q h p) p.2.1 :=
    (hasDerivAt_id p.2.1).div_const _
  have hc := hf.hasFDerivAt.comp_hasDerivAt p.2.1 (hx.prodMk (hasDerivAt_const p.2.1 (eta h p)))
  have hm := hc.const_mul (q h p ^ b)
  rw [fderiv_inner_apply] at hm
  have he : q h p ^ b * (partialX f (inner h p) * (1 / q h p) + partialEta f (inner h p) * 0) =
      pullback h (b - 1) (partialX f) p := by
    rw [pullback, Real.rpow_sub_one (q_pos hh hh1 hp).ne']
    ring
  exact hm.congr_deriv he

/-- Joint-coordinate time partial, in the same convention as AxisymmetricResidual. -/
theorem partialT_pullback {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    partialT (pullback h b f) p = pullback h (b - 1) (T h b f) p := by
  have hc := (pullback_differentiableAt (b := b) hh hh1 hp hf).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hc.unique (hasDerivAt_pullback_time hh hh1 hp hf)

theorem partialS_pullback {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    partialS (pullback h b f) p = pullback h (b - 1) (partialX f) p := by
  have hc := (pullback_differentiableAt (b := b) hh hh1 hp hf).hasFDerivAt.comp_hasDerivAt p.2.1
    ((hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))
  exact hc.unique (hasDerivAt_pullback_s hh hh1 hp hf)

theorem partialZ_pullback {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : DifferentiableAt ℝ f (inner h p)) :
    partialZ (pullback h b f) p = pullback h (b - D h) (Z h b f) p := by
  have hc := (pullback_differentiableAt (b := b) hh hh1 hp hf).hasFDerivAt.comp_hasDerivAt p.2.2
    ((hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2)))
  exact hc.unique (hasDerivAt_pullback_z hh hh1 hp hf)

theorem partialX_smoothAt {f : InnerProfile} {w : InnerPoint} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f w) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (partialX f) w :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

theorem partialEta_smoothAt {f : InnerProfile} {w : InnerPoint} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f w) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (partialEta f) w :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

/-- A local `C²` profile gives the local `C¹` axial coefficient required
for the second physical derivative. The denominator condition is explicit. -/
theorem Z_smoothAt {h b : ℝ} {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ 1 (Z h b f) w := by
  have hf₁ : ContDiffAt ℝ 1 f w := hf.of_le (by norm_num)
  have hx : ContDiffAt ℝ 1 (partialX f) w := partialX_smoothAt hf (by norm_num)
  have hη : ContDiffAt ℝ 1 (partialEta f) w := partialEta_smoothAt hf (by norm_num)
  exact ((((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul hf₁).add
    ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul hη) |>.sub
    (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_fst).mul hx)).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem T_smoothAt {h b : ℝ} {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ 1 (T h b f) w := by
  have hf₁ : ContDiffAt ℝ 1 f w := hf.of_le (by norm_num)
  have hx : ContDiffAt ℝ 1 (partialX f) w := partialX_smoothAt hf (by norm_num)
  have hη : ContDiffAt ℝ 1 (partialEta f) w := partialEta_smoothAt hf (by norm_num)
  exact (((contDiffAt_const.mul hf₁).add ((contDiffAt_const.mul contDiffAt_snd).mul hη)).add
    (contDiffAt_fst.mul hx)).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem eventually_C2_inner {h : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : ContDiffAt ℝ 2 f (inner h p)) :
    ∀ᶠ p' in 𝓝 p, ContDiffAt ℝ 2 f (inner h p') :=
  (inner_smoothAt hh hh1 hp).continuousAt.eventually (hf.eventually (by norm_num))

theorem partialS_partialS_pullback {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : ContDiffAt ℝ 2 f (inner h p)) :
    partialS (partialS (pullback h b f)) p =
      pullback h (b - 2) (partialX (partialX f)) p := by
  have heq : partialS (pullback h b f) =ᶠ[𝓝 p] pullback h (b - 1) (partialX f) := by
    filter_upwards [eventually_C2_inner hh hh1 hp hf,
      continuousAt_fst.eventually (Iio_mem_nhds hp)] with y hfy hyt
    exact partialS_pullback hh hh1 hyt (hfy.differentiableAt (by norm_num))
  change (fderiv ℝ (partialS (pullback h b f)) p) (0, (1, 0)) = _
  rw [heq.fderiv_eq]
  change partialS (pullback h (b - 1) (partialX f)) p = _
  rw [partialS_pullback hh hh1 hp
    ((partialX_smoothAt hf (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rw [show b - 1 - 1 = b - 2 by ring]

/-- The complete iterated axial chain rule for the actual reconstructed profile. -/
theorem partialZ_partialZ_pullback {h b : ℝ} {f : InnerProfile}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : ContDiffAt ℝ 2 f (inner h p)) :
    partialZ (partialZ (pullback h b f)) p =
      pullback h (b - 2 * D h) (Z h (b - D h) (Z h b f)) p := by
  have heq : partialZ (pullback h b f) =ᶠ[𝓝 p] pullback h (b - D h) (Z h b f) := by
    filter_upwards [eventually_C2_inner hh hh1 hp hf,
      continuousAt_fst.eventually (Iio_mem_nhds hp)] with y hfy hyt
    exact partialZ_pullback hh hh1 hyt (hfy.differentiableAt (by norm_num))
  change (fderiv ℝ (partialZ (pullback h b f)) p) (0, (0, 1)) = _
  rw [heq.fderiv_eq]
  change partialZ (pullback h (b - D h) (Z h b f)) p = _
  rw [partialZ_pullback hh hh1 hp
    ((Z_smoothAt hf (L_pos hh hh1 hp).ne').differentiableAt (by norm_num))]
  rw [show b - D h - D h = b - 2 * D h by ring]

/-- The natural open physical domain associated to an open inner-profile domain. -/
def physicalDomain (h : ℝ) (U : Set InnerPoint) : Set PhysicalPoint :=
  {p | p.1 < 1 ∧ inner h p ∈ U}

theorem isOpen_physicalDomain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U : Set InnerPoint} (hU : IsOpen U) : IsOpen (physicalDomain h U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hi : ∀ᶠ y in 𝓝 p, inner h y ∈ U :=
    (inner_smoothAt hh hh1 hp.1).continuousAt.eventually (hU.mem_nhds hp.2)
  filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hp.1), hi] with y hy hyU
  exact ⟨hy, hyU⟩

/-- Joint smoothness in `(t,s,z)` on the open coordinate domain; no global
smooth extension through the singular time or the edge of the profile is assumed. -/
theorem pullback_smoothOn {h b : ℝ} {f : InnerProfile} {n : ℕ∞}
    (hh : 0 < h) (hh1 : h < 1 / 2) {U : Set InnerPoint} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) : ContDiffOn ℝ n (pullback h b f) (physicalDomain h U) := by
  intro p hp
  exact (pullback_smoothAt hh hh1 hp.1 (hf.contDiffAt (hU.mem_nhds hp.2))).contDiffWithinAt

end NavierStokes.SimilarityProfile
