/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.ImportedAnalyticInputs
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # OrthogonalReduction -/


noncomputable section

open scoped BigOperators ENNReal
open Complex MeasureTheory Real

namespace OrthogonalReduction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)
variable [MeasureTheory.SigmaFinite μ]

private def localDefect (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ) (f0 : H) (h : H) : ℝ :=
  MeasureTheory.lpNorm
    (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖)
    2 μ

omit [CompleteSpace H] [SigmaFinite μ] in
private lemma localDefect_nonneg (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ) (f0 : H) :
    ∀ h : H, 0 ≤ localDefect μ ι f0 h := by
  intro h
  simp [localDefect]

omit [SigmaFinite μ] in
private lemma lpNorm_mono_real_ae {f : Ω → ℝ} {g : Ω → ℝ}
    (hg : MeasureTheory.MemLp g 2 μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    MeasureTheory.lpNorm f 2 μ ≤ MeasureTheory.lpNorm g 2 μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← MeasureTheory.toReal_eLpNorm hf,
      ← MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono hg.eLpNorm_ne_top
      (MeasureTheory.eLpNorm_mono_ae_real hfg)
  · simp only [lpNorm, hf, ↓reduceIte]
    exact MeasureTheory.lpNorm_nonneg

omit [SigmaFinite μ] in
private lemma lpNorm_coe_l2 {E : Type*} [NormedAddCommGroup E]
    (F : MeasureTheory.Lp E 2 μ) :
    MeasureTheory.lpNorm (fun x : Ω => F x) 2 μ = ‖F‖ := by
  have hmeas : AEStronglyMeasurable (fun x : Ω => F x) μ := by
    fun_prop
  rw [MeasureTheory.Lp.norm_def]
  exact (MeasureTheory.toReal_eLpNorm hmeas).symm

omit [SigmaFinite μ] in
private lemma lpNorm_norm_l2 (F : MeasureTheory.Lp ℂ 2 μ) :
    MeasureTheory.lpNorm (fun x : Ω => ‖(F : Ω → ℂ) x‖) 2 μ = ‖F‖ := by
  have hmeas : AEStronglyMeasurable (fun x : Ω => (F : Ω → ℂ) x) μ := by
    fun_prop
  rw [MeasureTheory.lpNorm_norm hmeas 2]
  exact lpNorm_coe_l2 μ F

private lemma abs_norm_sq_sub_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖x - y‖ * ‖x + y‖ := by
  have hident : ‖x‖ ^ 2 - ‖y‖ ^ 2 = inner ℝ (x - y) (x + y) := by
    simp [inner_sub_left, inner_add_right, real_inner_comm]
  rw [hident]
  simpa using norm_inner_le_norm (𝕜 := ℝ) (x - y) (x + y)

omit [CompleteSpace H] [SigmaFinite μ] in
private lemma compare_pointwise_ae
    (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (f0 h : H) (a : ℝ) :
    ∀ᵐ x ∂μ,
      |‖(ι (h - (a : ℂ) • f0 + f0) : Ω → ℂ) x‖ -
          ‖(ι (h + f0) : Ω → ℂ) x‖| ≤
        |a| * ‖(ι f0 : Ω → ℂ) x‖ := by
  let F : MeasureTheory.Lp ℂ 2 μ := ι f0
  let Hh : MeasureTheory.Lp ℂ 2 μ := ι h
  have hA :
      (ι (h - (a : ℂ) • f0 + f0) : MeasureTheory.Lp ℂ 2 μ) =
        Hh - (a : ℂ) • F + F := by
    calc
      (ι (h - (a : ℂ) • f0 + f0) : MeasureTheory.Lp ℂ 2 μ)
          = ι h - (a : ℂ) • ι f0 + ι f0 := by
              rw [map_add, map_sub, ι.map_smul]
      _ = Hh - (a : ℂ) • F + F := by
              rfl
  have hB :
      (ι (h + f0) : MeasureTheory.Lp ℂ 2 μ) = Hh + F := by
    calc
      (ι (h + f0) : MeasureTheory.Lp ℂ 2 μ) = ι h + ι f0 := by
        rw [map_add]
      _ = Hh + F := by
        rfl
  have hAae :
      ((ι (h - (a : ℂ) • f0 + f0) : MeasureTheory.Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] fun x => Hh x - (a : ℂ) * F x + F x := by
    rw [hA]
    filter_upwards [MeasureTheory.Lp.coeFn_add (Hh - (a : ℂ) • F) F,
      MeasureTheory.Lp.coeFn_sub Hh ((a : ℂ) • F),
      MeasureTheory.Lp.coeFn_smul (a : ℂ) F] with x h_add h_sub h_smul
    rw [h_add]
    simp only [Pi.add_apply]
    rw [h_sub]
    simp only [Pi.sub_apply]
    rw [h_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hBae :
      ((ι (h + f0) : MeasureTheory.Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] fun x => Hh x + F x := by
    rw [hB]
    exact MeasureTheory.Lp.coeFn_add Hh F
  filter_upwards [hAae, hBae] with x hxA hxB
  rw [hxA, hxB]
  have h0 := abs_norm_sub_norm_le (Hh x - (a : ℂ) * F x + F x) (Hh x + F x)
  have hdiff :
      ‖(Hh x - (a : ℂ) * F x + F x) - (Hh x + F x)‖ = |a| * ‖F x‖ := by
    have hdiff' :
        (Hh x - (a : ℂ) * F x + F x) - (Hh x + F x) =
          -((a : ℂ) * F x) := by
      ring
    rw [hdiff', norm_neg, norm_mul]
    simp [Complex.norm_real, Real.norm_eq_abs]
  simpa [hdiff, F] using h0

/-
Scaffolding theorem: local stability in `L²(μ)`.

This is the abstract orthogonal-reduction step from `HermiteSPR.tex`,
Theorem 2.4. The defect is the `L²` norm of the pointwise modulus difference,
encoded in mathlib via `eLpNorm` of a real-valued function.
-/
omit [CompleteSpace H] [SigmaFinite μ] in
theorem local_stability
    (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (f0 : H) (hf0 : ‖ι f0‖ = 1)
    (M : ℝ)
    (hMpos : 0 < M)
    (hM : ∀ g : H,
      inner ℂ g f0 = 0 →
      ‖g‖ ≤ M *
        MeasureTheory.lpNorm
            (fun x : Ω => ‖(ι (g + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖)
            2 μ) :
    ∃ δ > 0, ∃ M' > 0, ∀ h : H,
      ‖h‖ ≤ δ →
      Complex.im (inner ℂ h f0) = 0 →
      ‖h‖ ≤ M' *
        MeasureTheory.lpNorm (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖) 2 μ := by
  let defect : H → ℝ := localDefect μ ι f0
  have hdefect_nonneg : ∀ h : H, 0 ≤ defect h := by
    intro h
    dsimp [defect, localDefect]
    exact MeasureTheory.lpNorm_nonneg
  have horth :
      ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ M * defect g := by
    intro g hg
    simpa [defect, localDefect] using hM g hg
  have hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h := by
    intro h a
    let db : Ω → ℝ := fun x =>
      ‖(ι (h - (a : ℂ) • f0 + f0) : Ω → ℂ) x‖ -
        ‖(ι (h + f0) : Ω → ℂ) x‖
    let dh : Ω → ℝ := fun x =>
      ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖
    let vf : Ω → ℝ := fun x => |a| * ‖(ι f0 : Ω → ℂ) x‖
    have hdb_mem : MeasureTheory.MemLp db 2 μ := by
      have hA :
          MeasureTheory.MemLp
            (fun x : Ω => ‖(ι (h - (a : ℂ) • f0 + f0) : Ω → ℂ) x‖) 2 μ := by
        simpa using
          (MeasureTheory.Lp.memLp
            (ι (h - (a : ℂ) • f0 + f0) : MeasureTheory.Lp ℂ 2 μ)).norm
      have hB :
          MeasureTheory.MemLp
            (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖) 2 μ := by
        simpa using
          (MeasureTheory.Lp.memLp (ι (h + f0) : MeasureTheory.Lp ℂ 2 μ)).norm
      refine MeasureTheory.MemLp.ae_eq ?_ (hA.sub hB)
      filter_upwards with x
      rfl
    have hvf_mem : MeasureTheory.MemLp vf 2 μ := by
      have hF : MeasureTheory.MemLp (fun x : Ω => ‖(ι f0 : Ω → ℂ) x‖) 2 μ := by
        simpa using (MeasureTheory.Lp.memLp (ι f0 : MeasureTheory.Lp ℂ 2 μ)).norm
      refine MeasureTheory.MemLp.ae_eq ?_ (hF.const_smul |a|)
      filter_upwards with x
      rfl
    have hdb_le : MeasureTheory.lpNorm db 2 μ ≤ |a| := by
      have hae : ∀ᵐ x ∂μ, ‖db x‖ ≤ vf x := by
        filter_upwards [compare_pointwise_ae μ ι f0 h a] with x hx
        simpa [db, vf, Real.norm_eq_abs] using hx
      have hle := lpNorm_mono_real_ae μ hvf_mem hae
      have hvf_norm : MeasureTheory.lpNorm vf 2 μ = |a| := by
        have htmp :
            MeasureTheory.lpNorm vf 2 μ =
              |a| * MeasureTheory.lpNorm (fun x : Ω => ‖(ι f0 : Ω → ℂ) x‖) 2 μ := by
          have h := MeasureTheory.lpNorm_const_smul (c := |a|)
            (f := fun x : Ω => ‖(ι f0 : Ω → ℂ) x‖)
            (p := (2 : ℝ≥0∞)) (μ := μ)
          simp only [coe_nnnorm, Real.norm_eq_abs, abs_abs] at h
          exact h
        have hnorm :
            MeasureTheory.lpNorm (fun x : Ω => ‖(ι f0 : Ω → ℂ) x‖) 2 μ = ‖ι f0‖ := by
          exact lpNorm_norm_l2 μ (ι f0)
        rw [htmp, hnorm, hf0, mul_one]
      simpa [hvf_norm] using hle
    have hdh_mem : MeasureTheory.MemLp dh 2 μ := by
      have hB :
          MeasureTheory.MemLp
            (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖) 2 μ := by
        simpa using
          (MeasureTheory.Lp.memLp (ι (h + f0) : MeasureTheory.Lp ℂ 2 μ)).norm
      have hF : MeasureTheory.MemLp (fun x : Ω => ‖(ι f0 : Ω → ℂ) x‖) 2 μ := by
        simpa using (MeasureTheory.Lp.memLp (ι f0 : MeasureTheory.Lp ℂ 2 μ)).norm
      refine MeasureTheory.MemLp.ae_eq ?_ (hB.sub hF)
      filter_upwards with x
      rfl
    calc
      defect (h - (a : ℂ) • f0)
          = MeasureTheory.lpNorm (db + dh) 2 μ := by
              simp only [coe_smul, localDefect, map_add, map_sub, AddSubgroup.coe_add,
                AddSubgroupClass.coe_sub, defect, db, dh]
              congr 1
              funext x
              simp only [Pi.add_apply]
              ring
      _ ≤ MeasureTheory.lpNorm db 2 μ + MeasureTheory.lpNorm dh 2 μ := by
              simpa using
                (MeasureTheory.lpNorm_add_le hdb_mem (g := dh)
                  (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num))
      _ ≤ |a| + MeasureTheory.lpNorm dh 2 μ := by
              exact add_le_add hdb_le le_rfl
      _ = |a| + defect h := by
              simp [defect, localDefect, dh]
  have hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖) := by
    intro h _him
    let A : MeasureTheory.Lp ℂ 2 μ := ι (h + f0)
    let F : MeasureTheory.Lp ℂ 2 μ := ι f0
    let Xfun : Ω → ℝ := fun x => ‖(A : Ω → ℂ) x‖
    let Yfun : Ω → ℝ := fun x => ‖(F : Ω → ℂ) x‖
    have hX_mem : MeasureTheory.MemLp Xfun 2 μ := by
      simpa [Xfun, A] using
        (MeasureTheory.Lp.memLp (ι (h + f0) : MeasureTheory.Lp ℂ 2 μ)).norm
    have hY_mem : MeasureTheory.MemLp Yfun 2 μ := by
      simpa [Yfun, F] using
        (MeasureTheory.Lp.memLp (ι f0 : MeasureTheory.Lp ℂ 2 μ)).norm
    let X : MeasureTheory.Lp ℝ 2 μ := hX_mem.toLp Xfun
    let Y : MeasureTheory.Lp ℝ 2 μ := hY_mem.toLp Yfun
    have hA_norm : ‖A‖ = ‖h + f0‖ := by
      dsimp [A]
      exact ι.norm_map (h + f0)
    have hF_norm : ‖F‖ = ‖f0‖ := by
      dsimp [F]
      exact ι.norm_map f0
    have hXnorm : ‖X‖ = ‖A‖ := by
      dsimp [X]
      rw [MeasureTheory.Lp.norm_toLp]
      rw [MeasureTheory.toReal_eLpNorm hX_mem.1]
      simpa [Xfun] using lpNorm_norm_l2 μ A
    have hYnorm : ‖Y‖ = ‖F‖ := by
      dsimp [Y]
      rw [MeasureTheory.Lp.norm_toLp]
      rw [MeasureTheory.toReal_eLpNorm hY_mem.1]
      simpa [Yfun] using lpNorm_norm_l2 μ F
    have hsubnorm : ‖X - Y‖ = defect h := by
      have hsub : X - Y = (hX_mem.sub hY_mem).toLp (Xfun - Yfun) := by
        dsimp [X, Y]
        exact (MeasureTheory.MemLp.toLp_sub hX_mem hY_mem).symm
      rw [hsub, MeasureTheory.Lp.norm_toLp]
      rw [MeasureTheory.toReal_eLpNorm (hX_mem.sub hY_mem).1]
      rfl
    have hsum_bound : ‖X + Y‖ ≤ 2 + ‖h‖ := by
      calc
        ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le X Y
        _ = ‖A‖ + ‖F‖ := by
            rw [hXnorm, hYnorm]
        _ = ‖h + f0‖ + ‖f0‖ := by
            rw [hA_norm, hF_norm]
        _ ≤ (‖h‖ + ‖f0‖) + ‖f0‖ := by
            gcongr
            exact norm_add_le h f0
        _ = 2 + ‖h‖ := by
            have hf0' : ‖f0‖ = 1 := by
              simpa [hF_norm] using hf0
            rw [hf0']
            ring
    have hleft_eq :
        (2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2 = ‖X‖ ^ 2 - ‖Y‖ ^ 2 := by
      have hf0' : ‖f0‖ = 1 := by
        simpa [hF_norm] using hf0
      rw [hXnorm, hYnorm, hA_norm, hF_norm]
      have hadd := norm_add_sq (𝕜 := ℂ) h f0
      rw [hadd, hf0']
      change (2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2 =
        ‖h‖ ^ 2 + 2 * (inner ℂ h f0).re + 1 ^ 2 - 1 ^ 2
      ring
    calc
      |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2|
          = |‖X‖ ^ 2 - ‖Y‖ ^ 2| := by
              rw [hleft_eq]
      _ ≤ ‖X - Y‖ * ‖X + Y‖ := abs_norm_sq_sub_norm_sq_le X Y
      _ ≤ defect h * (2 + ‖h‖) := by
              rw [hsubnorm]
              exact mul_le_mul_of_nonneg_left hsum_bound (hdefect_nonneg h)
  have hf0' : ‖f0‖ = 1 := by
    simpa using hf0
  simpa [defect, localDefect] using
    (HermiteLEAN.phase_normalized_orthogonal_reduction
      (defect := defect)
      (hdefect_nonneg := hdefect_nonneg)
      f0 hf0' M hMpos
      horth
      hscalar
      hcompare)

end OrthogonalReduction
