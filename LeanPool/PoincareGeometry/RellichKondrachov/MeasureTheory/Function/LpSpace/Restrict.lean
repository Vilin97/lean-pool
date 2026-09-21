/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Restrict -/

@[expose] public section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`L^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

noncomputable def vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
lemma vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      simpa using! (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using! hadd.symm
      calc
        vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    ·
      have hadd' :
          vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using! hadd.symm
      calc
        vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      simpa using! (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using! hsmul.symm
      calc
        vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    ·
      have hsmul' :
          c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using! hsmul.symm
      calc
        vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using! hf
            have hcx :
                (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using! hsmul
                _ = 0 := by simp [hf0]
            simpa using! hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using! (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using!
    (vendorMeasureTheoryFunctionLpSpaceRestrict_extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

lemma extendByZeroₗᵢ_congr (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by
  -- `extendByZeroₗᵢ` is characterized by its pointwise representative.
  refine LinearIsometry.toLinearMap_injective ?_
  refine LinearMap.ext ?_
  intro f
  refine MeasureTheory.Lp.ext (E := E) (p := p) (μ := μ) ?_
  have h₁ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₁) f
  have h₂ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₂) f
  exact h₁.trans h₂.symm

end

end Lp

end MeasureTheory
