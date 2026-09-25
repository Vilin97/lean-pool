/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationL2

/-! # Restricted raw-function bounds for the L² operator

The completed-space estimates transfer to raw representatives on the L²
carrier. Additivity and sublinearity are asserted only almost everywhere;
no algebraic property of the definition outside L² is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The raw representative satisfies the strong `(2,2)` power-integral
estimate on its actual L² carrier. -/
theorem raw_rieszSecond_strong_two {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    (∫⁻ x, absE (rieszSecondL2RawOperator hL2 f) x ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((1 : ℝ) ^ 2) * ∫⁻ x, absE f x ^ (2 : ℕ) := by
  have hout := rieszSecondL2RawOperator_ae_eq hL2 hf
  have hin := hf.coeFn_toLp
  have houtI := lintegral_congr_ae (hout.fun_comp (fun v : ℝ => ENNReal.ofReal |v| ^ (2 : ℕ)))
  have hinI := lintegral_congr_ae (hin.fun_comp (fun v : ℝ => ENNReal.ofReal |v| ^ (2 : ℕ)))
  simp only [Function.comp_apply] at houtI hinI
  change (∫⁻ x, ENNReal.ofReal |rieszSecondL2RawOperator hL2 f x| ^ (2 : ℕ)) ≤ _
  rw [houtI]
  have h := rieszSecondL2MeasurableOperator_l2_bound hL2 (hf.toLp f)
  change (∫⁻ x, ENNReal.ofReal |rieszSecondL2MeasurableOperator hL2 (hf.toLp f) x| ^
      (2 : ℕ)) ≤ (∫⁻ x, ENNReal.ofReal |(hf.toLp f : Vec3 → ℝ) x| ^ (2 : ℕ)) at h
  rw [hinI] at h
  simpa only [one_pow, ENNReal.ofReal_one, one_mul, absE] using h

/-- The raw operator is additive a.e. for pairs of L² inputs. -/
theorem raw_rieszSecond_add_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) (hg : MemLp g (2 : ℝ≥0∞) volume) :
    rieszSecondL2RawOperator hL2 (f + g) =ᵐ[volume]
      rieszSecondL2RawOperator hL2 f + rieszSecondL2RawOperator hL2 g := by
  have hadd := rieszSecondL2MeasurableOperator_add_ae hL2 (hf.toLp f) (hg.toLp g)
  rw [← MemLp.toLp_add hf hg] at hadd
  exact (rieszSecondL2RawOperator_ae_eq hL2 (hf.add hg)).trans
    (hadd.trans ((rieszSecondL2RawOperator_ae_eq hL2 hf).symm.add
      (rieszSecondL2RawOperator_ae_eq hL2 hg).symm))

/-- Almost-everywhere equal L² inputs have almost-everywhere equal raw outputs. -/
theorem raw_rieszSecond_congr_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) (hg : MemLp g (2 : ℝ≥0∞) volume)
    (hfg : f =ᵐ[volume] g) :
    rieszSecondL2RawOperator hL2 f =ᵐ[volume] rieszSecondL2RawOperator hL2 g := by
  have hclass : hf.toLp f = hg.toLp g := MemLp.toLp_congr hf hg hfg
  calc
    _ =ᵐ[volume] rieszSecondL2MeasurableOperator hL2 (hf.toLp f) :=
      rieszSecondL2RawOperator_ae_eq hL2 hf
    _ =ᵐ[volume] rieszSecondL2MeasurableOperator hL2 (hg.toLp g) := by rw [hclass]
    _ =ᵐ[volume] _ := (rieszSecondL2RawOperator_ae_eq hL2 hg).symm

/-- Scalar multiplication commutes a.e. with the raw operator on L² inputs. -/
theorem raw_rieszSecond_smul_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (c : ℝ) {f : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    rieszSecondL2RawOperator hL2 (c • f) =ᵐ[volume]
      c • rieszSecondL2RawOperator hL2 f := by
  have hsmul := rieszSecondL2MeasurableOperator_smul_ae hL2 c (hf.toLp f)
  rw [← MemLp.toLp_const_smul c hf] at hsmul
  exact (rieszSecondL2RawOperator_ae_eq hL2 (hf.const_smul c)).trans
    (hsmul.trans ((rieszSecondL2RawOperator_ae_eq hL2 hf).symm.const_smul c))

/-- Restricted a.e. sublinearity follows from the actual L² additivity. -/
theorem raw_rieszSecond_sublinear_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) (hg : MemLp g (2 : ℝ≥0∞) volume) :
    ∀ᵐ x ∂volume, |rieszSecondL2RawOperator hL2 (f + g) x| ≤
      |rieszSecondL2RawOperator hL2 f x| + |rieszSecondL2RawOperator hL2 g x| := by
  filter_upwards [raw_rieszSecond_add_ae hL2 hf hg] with x hx
  rw [hx]
  exact abs_add_le _ _

/-- The raw L² representative satisfies the concrete distributional
pairing against every smooth compactly supported test function. -/
theorem raw_rieszSecond_distributional_identity {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f ψ : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, rieszSecondL2RawOperator hL2 f x * CKN.spatialLaplacian ψ x) =
      ∫ x, f x * CKN.mixedSecond ψ i j x := by
  calc
    _ = ∫ x, rieszSecondL2MeasurableOperator hL2 (hf.toLp f) x *
        CKN.spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [rieszSecondL2RawOperator_ae_eq hL2 hf] with x hx
      rw [hx]
    _ = ∫ x, (hf.toLp f : Vec3 → ℝ) x * CKN.mixedSecond ψ i j x :=
      rieszSecondL2_distributional_identity hL2 hψ hψc (hf.toLp f)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

end CKN.Core.Endgame
