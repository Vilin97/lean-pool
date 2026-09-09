/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevEmbedding
public import LeanPool.NavierStokesAndEuler.Euler.SobolevTranslationDifferentiation

@[expose] public section

/-! Actual pointwise multiplication as a bounded bilinear map Hq × L² → L². -/

noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace
open scoped Topology ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual scalar-vector product belongs to L² by the proved Sobolev embedding. -/
theorem scalarProduct_memLp {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v : LiftL2 period) :
    MemLp (fun x => L (value period u x) • v x) 2 (liftMeasure period) := by
  apply (Lp.memLp v).of_le_mul (c := ‖L‖ * sobolevEmbeddingConstant period q * ‖u‖)
  · exact (L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (value period u))).smul
      (Lp.aestronglyMeasurable v)
  · filter_upwards [value_ae_bound period hq u] with x hx
    rw [norm_smul]
    have hL := (L.le_opNorm (value period u x)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg L))
    exact (mul_le_mul_of_nonneg_right hL (norm_nonneg (v x))).trans_eq (by ring)

/-- The actual almost-everywhere scalar-vector product represented in cylinder L². -/
def scalarProduct {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v : LiftL2 period) : LiftL2 period :=
  (scalarProduct_memLp period hq L u v).toLp (fun x => L (value period u x) • v x)

theorem scalarProduct_ae {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v : LiftL2 period) :
    (scalarProduct period hq L u v : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      (fun x => L (value period u x) • v x) := (scalarProduct_memLp period hq L u v).coeFn_toLp

/-- The actual L² product has the quantitative bilinear bound. -/
theorem scalarProduct_norm {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v : LiftL2 period) :
    ‖scalarProduct period hq L u v‖ ≤ (‖L‖ * sobolevEmbeddingConstant period q) * ‖u‖ * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarProduct_ae period hq L u v, value_ae_bound period hq u] with x hp hu
  rw [hp, norm_smul]
  exact (mul_le_mul_of_nonneg_right
    ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg L))) (norm_nonneg
      _)).trans_eq (by ring)

theorem scalarProduct_add_right {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v w : LiftL2 period) :
    scalarProduct period hq L u (v+w) = scalarProduct period hq L u v + scalarProduct period hq L u
      w := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hq L u (v+w), scalarProduct_ae period hq L u v,
    scalarProduct_ae period hq L u w, Lp.coeFn_add v w,
    Lp.coeFn_add (scalarProduct period hq L u v) (scalarProduct period hq L u w)] with x h1 h2 h3
      h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1, h5, h2, h3, h4, smul_add]

theorem scalarProduct_smul_right {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (r : ℝ) (v : LiftL2 period) :
    scalarProduct period hq L u (r • v) = r • scalarProduct period hq L u v := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hq L u (r • v), scalarProduct_ae period hq L u v,
    Lp.coeFn_smul r v, Lp.coeFn_smul r (scalarProduct period hq L u v)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4
  rw [h1, h4, h2, h3, smul_comm]

theorem scalarProduct_add_left {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u w : SobolevSpace period q) (v : LiftL2 period) :
    scalarProduct period hq L (u+w) v = scalarProduct period hq L u v + scalarProduct period hq L w
      v := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hq L (u+w) v, scalarProduct_ae period hq L u v,
    scalarProduct_ae period hq L w v, Lp.coeFn_add (value period u) (value period w),
    Lp.coeFn_add (scalarProduct period hq L u v) (scalarProduct period hq L w v)] with x h1 h2 h3
      h4 h5
  simp only [Pi.add_apply] at h4 h5
  change (value period (u+w)) x = value period u x + value period w x at h4
  rw [h1, h5, h2, h3, h4, map_add, add_smul]

theorem scalarProduct_smul_left {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (r : ℝ) (u : SobolevSpace period q) (v : LiftL2 period) :
    scalarProduct period hq L (r • u) v = r • scalarProduct period hq L u v := by
  apply Lp.ext
  filter_upwards [scalarProduct_ae period hq L (r • u) v, scalarProduct_ae period hq L u v,
    Lp.coeFn_smul r (value period u), Lp.coeFn_smul r (scalarProduct period hq L u v)] with x h1 h2
      h3 h4
  simp only [Pi.smul_apply] at h3 h4
  change value period (r • u) x = r • value period u x at h3
  rw [h1, h4, h2, h3, map_smul, smul_assoc]

/-- Pointwise multiplication by an Hq scalar component is a bounded linear L² operator. -/
def scalarProductRight {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := scalarProduct period hq L u
      map_add' := scalarProduct_add_right period hq L u
      map_smul' := scalarProduct_smul_right period hq L u }
    ((‖L‖ * sobolevEmbeddingConstant period q) * ‖u‖)
    (scalarProduct_norm period hq L u)

theorem scalarProductRight_norm {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) :
    ‖scalarProductRight period hq L u‖ ≤ (‖L‖ * sobolevEmbeddingConstant period q) * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (norm_nonneg _) (sobolevEmbeddingConstant_nonneg period q))
      (norm_nonneg _))
    (scalarProduct_norm period hq L u)

/-- Actual scalar-vector multiplication, as a continuous bilinear map on the complete spaces. -/
def scalarProductBilinear {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ) :
    SobolevSpace period q →L[ℝ] LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := scalarProductRight period hq L
      map_add' := by
        intro u w
        apply ContinuousLinearMap.ext
        intro v
        exact scalarProduct_add_left period hq L u w v
      map_smul' := by
        intro r u
        apply ContinuousLinearMap.ext
        intro v
        exact scalarProduct_smul_left period hq L r u v }
    (‖L‖ * sobolevEmbeddingConstant period q) (scalarProductRight_norm period hq L)

@[simp] theorem scalarProductBilinear_apply {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u : SobolevSpace period q) (v : LiftL2 period) :
    scalarProductBilinear period hq L u v = scalarProduct period hq L u v := rfl

/-- The actual product is equivariant under simultaneous cylinder translation. -/
theorem scalarProduct_translation {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (a : LiftDomain period) (u : SobolevSpace period q) (v : LiftL2 period) :
    scalarProduct period hq L (sobolevTranslation period q a u) (translation period a v) =
      translation period a (scalarProduct period hq L u v) := by
  apply Lp.ext
  have hp := (measurePreserving_translation period a).quasiMeasurePreserving.ae (scalarProduct_ae
    period hq L u v)
  filter_upwards [scalarProduct_ae period hq L (sobolevTranslation period q a u) (translation
    period a v),
    translation_ae period a (value period u), translation_ae period a v,
    translation_ae period a (scalarProduct period hq L u v), hp] with x h1 h2 h3 h4 h5
  change value period (sobolevTranslation period q a u) x = value period u (x+a) at h2
  rw [h1, h2, h3, h4, h5]

end EulerSobolevL2Product
