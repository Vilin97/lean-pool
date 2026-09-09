/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCylinderSolenoidal
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTerminalAmplitude
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds

@[expose] public section

/-! A genuine smooth spatial L² field, embedded as a time-independent,
angle-independent cylinder field. Tensor bounds give a fixed mixed Sobolev
word bound, and classical divergence zero gives the actual lifted constraint. -/

noncomputable section

namespace EulerStaticCylinder

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpTranslation EulerLpCylinderTranslation EulerCylinderSpatialEmbedding
  EulerCylinderSpatialMean EulerMeanCylinderSolenoidal EulerCylinderClassicalSolenoidal
  EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerGevrey EulerVolterraConvolution EulerCylinderSobolev
open scoped ContDiff

variable (P T : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space)

def spatialOrbit (a : LiftTangent) : Lp Space 2 (volume : Measure Space) :=
  EulerLpTranslation.translation a.1 u.toLp

theorem spatialOrbit_smooth : ContDiff ℝ ∞ (spatialOrbit u) :=
  u.translation_contDiff.comp contDiff_fst

theorem embeddedOrbit_smooth : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (embedding P
  u.toLp)) := by
  have he : (fun a : LiftTangent => translate P a (embedding P u.toLp)) =
      (embedding P) ∘ spatialOrbit u := by
    funext a
    exact embedding_translate P a u.toLp
  rw [he]
  exact (embedding P).contDiff.comp (spatialOrbit_smooth u)

def field : Field P T (fun z => u.field z.2.1) :=
  Field.ofLifted (ContinuousMap.const (Icc (0 : ℝ) T) (embedding P u.toLp))
    (constantPath_orbit_contDiff P _ (embeddedOrbit_smooth P u))
    (fun _ z => u.field z.1)
    (fun _ => u.smooth.continuous.comp continuous_fst)
    (fun _ => embedding_representative P u.toLp u.field u.toLp_ae)
    (fun _ _ _ => rfl)

@[simp] theorem field_path :
    (field P T u).path=ContinuousMap.const (Icc (0 : ℝ) T) (embedding P u.toLp) := rfl

theorem field_time (hT : 0 ≤ T) : TimeDerivative hT (field P T u) (Field.zero P T) := by
  intro t
  change HasDerivWithinAt (fun _ : ℝ => embedding P u.toLp) 0 (Icc (0 : ℝ) T) t
  exact hasDerivWithinAt_const _ _ _

theorem field_divergence (κ : ℝ) (m : Space)
    (hu : ∀ x, EulerSmoothLimit.divergence u.field x=0) (t : Icc (0 : ℝ) T) :
    (field P T u).path t ∈ divergenceFreeSpace P κ m := by
  apply mem_of_classical P κ m (embedding P u.toLp) (fun z => u.field z.1)
    (embedding_representative P u.toLp u.field u.toLp_ae)
  · intro z
    exact u.smooth.comp (contDiff_const.add contDiff_fst)
  · exact lift_classical_divergence P κ m u.field u.smooth hu

theorem spatialOrbit_derivative_norm (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (spatialOrbit u) a‖ ≤ ‖u.jetLp n‖ := by
  let L := ContinuousLinearMap.fst ℝ Space ℝ
  have he : spatialOrbit u=(fun b : Space => EulerLpTranslation.translation b u.toLp) ∘ L := rfl
  rw [he,L.iteratedFDeriv_comp_right u.translation_contDiff a (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b u.toLp) a.1‖*
        ∏ _i : Fin n, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg L)
        (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
    _ = ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b u.toLp) a.1‖ := by
      simp only [Finset.prod_const_one,mul_one]
    _ ≤ ‖u.jetLp n‖ := u.norm_iteratedFDeriv_translation_le n a.1

theorem field_wordBound (q : ℕ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hb : u.HasJetBound C R) :
    (field P T u).WordBound q (sobolevCoefficientRadius (Fin 4) R)
      (Real.sqrt P*sobolevCoefficientAmplitude (Fin 4) q R C) 0 := by
  have hF := spatialOrbit_smooth u
  have hFb (n : ℕ) (a : LiftTangent) :
      ‖iteratedFDeriv ℝ n (spatialOrbit u) a‖ ≤ C*majorant R 0 n :=
    (spatialOrbit_derivative_norm u n a).trans (by simpa only [majorant,Nat.add_zero,mul_assoc]
      using hb n)
  have hB (n : ℕ) : block standardDirection q (spatialOrbit u) n 0 ≤
      sobolevCoefficientAmplitude (Fin 4) q R C*majorant (sobolevCoefficientRadius (Fin 4) R) 0 n
        := by
    have hh := coefficientBlock_of_tensor_bound standardDirection
      (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) q (spatialOrbit u)
      hF R C hR hC hFb n 0
    have hp : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
    exact ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hp
      (block_nonneg standardDirection q (spatialOrbit u) n 0))).trans hh
  intro n
  have hc := constantPath_block_le (K := Icc (0 : ℝ) T) P standardDirection q
    (embedding P u.toLp) (embeddedOrbit_smooth P u) n 0
  have he : (fun a : LiftTangent => translate P a (embedding P u.toLp)) =
      (embedding P) ∘ spatialOrbit u := by
    funext a
    exact embedding_translate P a u.toLp
  rw [he] at hc
  have hm := block_comp_clm_le standardDirection q (embedding (V := Space) P) (spatialOrbit u) hF n
    0
  apply hc.trans (hm.trans _)
  exact (mul_le_mul (embedding_norm P) (hB n)
    (block_nonneg standardDirection q (spatialOrbit u) n 0) (Real.sqrt_nonneg P)).trans_eq (by ring)

end EulerStaticCylinder
