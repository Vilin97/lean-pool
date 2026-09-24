/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondStrong
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationRestricted
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtension
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RestrictedInterpolationAE
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RawCZBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.PressureDecay
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Identification

/-!
# Consumer-facing Calderón--Zygmund bounds

The endpoint assembly is conditional only on the two endpoint estimates.  The
declarations here put its `3 / 2` and `6 / 5` specializations into the norm
conventions used by the pressure consumers.  The pressure identification is
kept as an explicit a.e. input until the distributional identification and
the endpoint estimates are available together.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Parabolic

/-- The real-valued operator constant at exponent `3 / 2`. -/
def czP1Constant (A₁ A₂ : ℝ) : ℝ :=
  (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ ((3 : ℝ) / 2))) ^
      (2 / 3 : ℝ) |>.toReal

/-- The real-valued component constant at exponent `6 / 5`. -/
def czGradientComponentConstant (A₁ A₂ : ℝ) : ℝ :=
  (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ ((6 : ℝ) / 5))) ^
      (5 / 6 : ℝ) |>.toReal

theorem lpNorm_bound_of_eLpNorm
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {p : ℝ} {K : ℝ≥0∞}
    (hK : K ≠ ∞) {g : Vec3 → ℝ}
    (hgmem : MemLp g (ENNReal.ofReal p) volume)
    (hbound : eLpNorm (T g) (ENNReal.ofReal p) volume ≤
      K * eLpNorm g (ENNReal.ofReal p) volume) :
    lpNorm (T g) (ENNReal.ofReal p) volume ≤
      K.toReal * lpNorm g (ENNReal.ofReal p) volume := by
  have hfiniteT : eLpNorm (T g) (ENNReal.ofReal p) volume < ∞ := by
    exact hbound.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hgmem)
  have hfiniteG : eLpNorm g (ENNReal.ofReal p) volume ≠ ∞ := hgmem.ne
  rw [lpNorm, lpNorm]
  rw [← ENNReal.toReal_mul]
  exact (ENNReal.toReal_le_toReal hfiniteT.ne (ENNReal.mul_ne_top hK hfiniteG)).2 hbound

theorem eLpNorm_bound_of_l2_interpolation
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g, Measurable f → Integrable f volume → MemLp f 2 volume →
      Measurable g → MemLp g 2 volume → ∀ᵐ x ∂volume, |T (f + g) x| ≤
        |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → MemLp f 2 volume → Measurable (T f))
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |T f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f → MemLp f 2 volume →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {g : Vec3 → ℝ} (hg : Measurable g)
    (hgp : MemLp g (ENNReal.ofReal p) volume) (hg₂ : MemLp g 2 volume) :
    eLpNorm (T g) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^
          (1 / p : ℝ) *
        eLpNorm g (ENNReal.ofReal p) volume := by
  have hpow := CKN.Core.Endgame.interpolation_weak11_strong22_of_l2_classes_ae
    (T := T) hTsub hTmeas hweak hstrong hA₁ hp1 hp2 hg hgp hg₂
  have hTg : Measurable (T g) := hTmeas g hg hg₂
  have hTga : AEStronglyMeasurable (T g) volume := hTg.aestronglyMeasurable
  have hga : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  rw [eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hTga,
    eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hga]
  have hpow' : eLpNorm' (T g) p volume ^ p ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p) *
        eLpNorm' g p volume ^ p := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0]
    simpa only [absE, Real.enorm_eq_ofReal_abs, rieszSecondInterpolationConstant] using hpow
  have hres : eLpNorm' (T g) p volume ≤
      (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^ (1 / p) *
        eLpNorm' g p volume := by
    calc
      eLpNorm' (T g) p volume =
          (eLpNorm' (T g) p volume ^ p) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul]
        field_simp
        simp
      _ ≤ (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p) *
          eLpNorm' g p volume ^ p) ^ (1 / p) := by
        exact ENNReal.rpow_le_rpow hpow' (by positivity)
      _ = (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^ (1 / p) *
          eLpNorm' g p volume := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        field_simp
        simp
  simpa only [ENNReal.toReal_ofReal hp0.le] using hres

/-- Build extension data from subadditivity, weak-(1,1), measurability and an L² bound. -/
def l2ExtensionInput
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g, Measurable f → Integrable f volume → MemLp f 2 volume →
      Measurable g → MemLp g 2 volume → ∀ᵐ x ∂volume, |T (f + g) x| ≤
        |T f x| + |T g x|)
    (hTmeas : ∀ f, MemLp f 2 volume → Measurable (T f))
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |T f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f → MemLp f 2 volume →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    (hcongr : ∀ {f g}, MemLp f 2 volume → MemLp g 2 volume →
      f =ᵐ[volume] g → T f =ᵐ[volume] T g)
    (hadd : ∀ {f g}, MemLp f 2 volume → MemLp g 2 volume →
      T (f + g) =ᵐ[volume] T f + T g)
    (hsmul : ∀ (c : ℝ) {f : Vec3 → ℝ}, MemLp f 2 volume →
      T (c • f) =ᵐ[volume] c • T f)
    (hK : (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^
      (1 / p : ℝ) ≠ ∞) :
    LpExtensionInput (ENNReal.ofReal p)
      ((ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^
        (1 / p : ℝ)).toReal := by
  let K : ℝ≥0∞ :=
    (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ p)) ^ (1 / p : ℝ)
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have houtput : ∀ {f : Vec3 → ℝ}, MemLp f (ENNReal.ofReal p) volume →
      MemLp f 2 volume → MemLp (T f) (ENNReal.ofReal p) volume := by
    intro f hf hf₂
    let hfae : AEMeasurable f volume := hf.aestronglyMeasurable.aemeasurable
    let f' : Vec3 → ℝ := hfae.mk f
    have hff' : f =ᵐ[volume] f' := hfae.ae_eq_mk
    have hf' : MemLp f' (ENNReal.ofReal p) volume :=
      memLp_congr_ae hff' |>.1 hf
    have hf₂' : MemLp f' 2 volume :=
      memLp_congr_ae hff' |>.1 hf₂
    have hbound := eLpNorm_bound_of_l2_interpolation
      hTsub (fun f _hf h₂ => hTmeas f h₂) hweak hstrong hA₁ hp1 hp2
        hfae.measurable_mk hf' hf₂'
    have hT' : MemLp (T f') (ENNReal.ofReal p) volume := by
      rw [memLp_iff]
      exact hbound.trans_lt
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hf'.eLpNorm_lt_top)
    exact memLp_congr_ae (hcongr hf₂ hf₂' hff') |>.2 hT'
  refine
    { T := T
      measurable := fun hf₂ => hTmeas _ hf₂
      output_mem := houtput
      congr_ae := fun hf hg hfg => hcongr hf hg hfg
      add_ae := fun hf hg => hadd hf hg
      smul_ae := fun c {f} hf => hsmul c hf
      bound := ?_ }
  intro f hf hf₂
  let hfae : AEMeasurable f volume := hf.aestronglyMeasurable.aemeasurable
  let f' : Vec3 → ℝ := hfae.mk f
  have hff' : f =ᵐ[volume] f' := hfae.ae_eq_mk
  have hf' : MemLp f' (ENNReal.ofReal p) volume :=
    memLp_congr_ae hff' |>.1 hf
  have hf₂' : MemLp f' 2 volume :=
    memLp_congr_ae hff' |>.1 hf₂
  have hbound' := eLpNorm_bound_of_l2_interpolation
    hTsub (fun f _hf h₂ => hTmeas f h₂) hweak hstrong hA₁ hp1 hp2
      hfae.measurable_mk hf' hf₂'
  have hbound : eLpNorm (T f) (ENNReal.ofReal p) volume ≤
      K * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      eLpNorm (T f) (ENNReal.ofReal p) volume =
          eLpNorm (T f') (ENNReal.ofReal p) volume :=
        eLpNorm_congr_ae (hcongr hf₂ hf₂' hff')
      _ ≤ K * eLpNorm f' (ENNReal.ofReal p) volume := by
        simpa only [K] using hbound'
      _ = K * eLpNorm f (ENNReal.ofReal p) volume := by
        rw [eLpNorm_congr_ae hff']
  have hlp := lpNorm_bound_of_eLpNorm hK hf hbound
  rw [Lp.norm_toLp, Lp.norm_toLp]
  simpa only [eLpNorm_congr_ae
    (houtput hf hf₂).coeFn_toLp,
    eLpNorm_congr_ae hf.coeFn_toLp, K, lpNorm] using hlp

/-- Extension data for a second Riesz transform obtained by interpolation below exponent two. -/
def rieszSecondExtensionInput
    {i j : Fin 3} {p A₁ : ℝ}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    (hK : (ENNReal.ofReal
      (rieszSecondInterpolationConstant A₁ 1 p)) ^ (1 / p : ℝ) ≠ ∞) :
    LpExtensionInput (ENNReal.ofReal p)
      ((ENNReal.ofReal (rieszSecondInterpolationConstant A₁ 1 p)) ^
        (1 / p : ℝ)).toReal :=
  l2ExtensionInput
    (hTsub := fun f g _hf hfi hf₂ _hg hg₂ =>
      CKN.Core.Endgame.raw_rieszSecond_sublinear_ae hL2 hf₂ hg₂)
    (hTmeas := fun f hf₂ =>
      rieszSecondL2RawOperator_measurable hL2 hf₂)
    (hweak := hWeak11)
    (hstrong := fun f _hf hf₂ => by
      simpa only [one_pow, ENNReal.ofReal_one, one_mul] using
        CKN.Core.Endgame.raw_rieszSecond_strong_two hL2 hf₂)
    (hA₁ := hA₁) (hp1 := hp1) (hp2 := hp2)
    (hcongr := fun hf hg hfg =>
      CKN.Core.Endgame.raw_rieszSecond_congr_ae hL2 hf hg hfg)
    (hadd := fun hf hg =>
      CKN.Core.Endgame.raw_rieszSecond_add_ae hL2 hf hg)
    (hsmul := fun (c : ℝ) {f : Vec3 → ℝ} hf =>
      CKN.Core.Endgame.raw_rieszSecond_smul_ae hL2 c hf)
    hK

/-- The extension input for the scalar pressure operator at exponent 3 / 2. -/
def rieszSecondP1ExtensionInput {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l) :
    LpExtensionInput (ENNReal.ofReal ((3 : ℝ) / 2))
      (czP1Constant rieszSecondWeakTypeConstant 1) := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  have hK : (ENNReal.ofReal
      (rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1
        ((3 : ℝ) / 2))) ^ (1 / ((3 : ℝ) / 2) : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  simpa only [czP1Constant, show (1 / ((3 : ℝ) / 2) : ℝ) = 2 / 3 by norm_num] using
    (rieszSecondExtensionInput hL2 hWeak11 (by
      unfold rieszSecondWeakTypeConstant
      have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
      positivity) (by norm_num) (by norm_num) hK)

/-- The extension input for one scalar gradient component at exponent 6 / 5. -/
def rieszSecondGradientExtensionInput {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l) :
    LpExtensionInput (ENNReal.ofReal ((6 : ℝ) / 5))
      (czGradientComponentConstant rieszSecondWeakTypeConstant 1) := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  have hK : (ENNReal.ofReal
      (rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1
        ((6 : ℝ) / 5))) ^ (1 / ((6 : ℝ) / 5) : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  simpa only [czGradientComponentConstant,
    show (1 / ((6 : ℝ) / 5) : ℝ) = 5 / 6 by norm_num] using
    (rieszSecondExtensionInput hL2 hWeak11 (by
      unfold rieszSecondWeakTypeConstant
      have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
      positivity) (by norm_num) (by norm_num) hK)

/-- The scalar pressure operator after completion from the L2 carrier. -/
def rieszSecondP1ExtensionOperator {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (f : Vec3 → ℝ) : Vec3 → ℝ := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative (by norm_num)
    (rieszSecondP1ExtensionInput hL2 hWeak11) f

/-- One completed scalar pressure output is in L^(3/2). -/
theorem rieszSecondP1Extension_memLp {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (_ : HasCompactSupport f) :
    MemLp (rieszSecondP1ExtensionOperator hL2 hWeak11 f)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_memLp (by norm_num)
    (rieszSecondP1ExtensionInput hL2 hWeak11) hf

/-- The real norm bound for the completed scalar pressure operator. -/
theorem rieszSecondP1Extension_toLp_bound {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hfc : HasCompactSupport f) :
    ‖(rieszSecondP1Extension_memLp hL2 hWeak11 hf hfc).toLp
        (rieszSecondP1ExtensionOperator hL2 hWeak11 f)‖ ≤
      czP1Constant rieszSecondWeakTypeConstant 1 * ‖hf.toLp f‖ := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_norm_le (by norm_num)
    (rieszSecondP1ExtensionInput hL2 hWeak11) hf

/-- The indexed completed operator at exponent 6 / 5. -/
def rieszSecondGradientExtensionOperator {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (f : Vec3 → ℝ) : Vec3 → ℝ := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative (by norm_num)
    (rieszSecondGradientExtensionInput hL2 hWeak11) f

/-- One completed indexed output is in L^(6/5). -/
theorem rieszSecondGradientExtension_memLp {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (_ : HasCompactSupport f) :
    MemLp (rieszSecondGradientExtensionOperator hL2 hWeak11 f)
      (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_memLp (by norm_num)
    (rieszSecondGradientExtensionInput hL2 hWeak11) hf

/-- The real norm bound for one completed indexed output. -/
theorem rieszSecondGradientExtension_toLp_bound {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hfc : HasCompactSupport f) :
    ‖(rieszSecondGradientExtension_memLp hL2 hWeak11 hf hfc).toLp
        (rieszSecondGradientExtensionOperator hL2 hWeak11 f)‖ ≤
      czGradientComponentConstant rieszSecondWeakTypeConstant 1 * ‖hf.toLp f‖ := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_norm_le (by norm_num)
    (rieszSecondGradientExtensionInput hL2 hWeak11) hf

/- The vector-valued estimate below uses the product norm on `Vec3`; the
   elementary coordinate aggregation is kept local to this file. -/
private lemma pi_norm_le_sum_abs (v : Vec3) :
    ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  rw [Pi.norm_def]
  have hs : Finset.univ.sup (fun i : Fin 3 => ‖v i‖₊) ≤
      ∑ i : Fin 3, ‖v i‖₊ := by
    apply Finset.sup_le
    intro i hi
    have hnonneg : ∀ j : Fin 3, j ∈ (Finset.univ : Finset (Fin 3)) →
        0 ≤ ‖v j‖₊ := fun j _hj => (‖v j‖₊).2
    exact Finset.single_le_sum hnonneg (Finset.mem_univ i)
  exact_mod_cast hs

private theorem eLpNorm_vec3_le_sum_abs
    {f : Vec3 → Vec3} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f p volume ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) p volume := by
  calc
    eLpNorm f p volume ≤ eLpNorm (fun x => ∑ i : Fin 3, |f x i|) p volume := by
      apply eLpNorm_mono_ae_real hf
      filter_upwards [] with x
      exact pi_norm_le_sum_abs (f x)
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |f x i|) p volume := by
      change eLpNorm (∑ i : Fin 3, (fun x => |f x i|)) p volume ≤ _
      exact eLpNorm_sum_le (p := p) (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => (fun x => |f x i|)) hp
    _ = ∑ i : Fin 3, eLpNorm (fun x => f x i) p volume := by
      apply Finset.sum_congr rfl
      intro i hi
      have hfi : AEStronglyMeasurable (fun x => f x i) volume := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      simpa only [Real.norm_eq_abs] using (eLpNorm_norm (fun x => f x i) hfi)

/- The strong theorem is used here in its component form.  Once the endpoint
   theorem for the concrete convolution is established, each scalar component is
   supplied by `rieszSecond_eLpNorm_bound_of_inputs`. -/
/-- The canonical `L^(3/2)` Calderón--Zygmund bound for one scalar component. -/
theorem cz_p1_bound
    {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hWeak11 : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hL2 : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) {g : Vec3 → ℝ} (hg : Measurable g)
    (hgmem : MemLp g (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (_ : HasCompactSupport g) :
    lpNorm (T g) (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      czP1Constant A₁ A₂ *
        lpNorm g (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  have hbound := rieszSecond_eLpNorm_bound_of_inputs hTsub hTmeas hWeak11 hL2
    hA₁ (by norm_num : (1 : ℝ) < (3 : ℝ) / 2) (by norm_num : (3 : ℝ) / 2 < 2) hg
  have hK : (ENNReal.ofReal (rieszSecondInterpolationConstant A₁ A₂ ((3 : ℝ) / 2))) ^
      (1 / ((3 : ℝ) / 2) : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hlp := lpNorm_bound_of_eLpNorm hK hgmem hbound
  simpa only [czP1Constant, show (1 / ((3 : ℝ) / 2) : ℝ) = 2 / 3 by norm_num]
    using hlp

/-- The global `hCZ_p1` consumer shape after the a.e. identification of `p₁`.
The three consumer files use this bound as their common source estimate. -/
theorem hCZ_p1_of_cz_p1_bound
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {p₁ g : Vec3 → ℝ} {C_CZ C₁₁ E : ℝ}
    (hT : ∀ f, MemLp f (ENNReal.ofReal ((3 : ℝ) / 2)) volume →
      HasCompactSupport f →
      lpNorm (T f) (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
        C_CZ * lpNorm f (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hg : MemLp g (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hgc : HasCompactSupport g) (hident : p₁ =ᵐ[volume] T g)
    (hsource : lpNorm g (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤ E ^ (2 / 3 : ℝ))
    (hC_CZ : 0 ≤ C_CZ) (hconst : C_CZ ≤ C₁₁) (hE : 0 ≤ E) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  exact CKN.hCZ_p1_of_operator_bound hT hg hgc hident hsource hC_CZ hconst hE

/- The local pressure-decay consumer uses the same identification after a
   time-space slice estimate has been formed from the global operator bound. -/
/-- Transport a slice estimate for `T` to the exact pressure-decay `hCZ_p1`. -/
theorem hCZ_p1_of_slice_operator_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {G : ParabolicPoint → Vec3 → ℝ}
    {z : ParabolicPoint} {r ρ C₁₂ : ℝ}
    (hident :
      (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1) =ᵐ[
        volume.restrict (parabolicCylinder z.1 z.2 r)]
        (fun w => T (G w) w.1))
    (hsource :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => T (G w) w.1)
            (3 / 2 : ℝ) (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
          (3 / 2 : ℝ) (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) := by
  calc
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
            (3 / 2 : ℝ) (volume.restrict (parabolicCylinder z.1 z.2 r)) =
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => T (G w) w.1)
            (3 / 2 : ℝ) (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
      rw [eLpNorm'_congr_ae hident]
    _ ≤ _ := hsource

/-! The old literal representative is not used for the global
gradient bound.  The selected weak field is the signed indexed extension;
its distributional characterization is supplied by the weak-gradient
consumer and by the pairing-transfer theorem for the extension. -/

/-- The norm-only gradient-bound predicate for a selected indexed operator. -/
def HasCZGradientOperatorBound
    (T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ) (C_CZ : ℝ) : Prop :=
  ∀ (i : Fin 3) (G : Vec3 → ℝ),
    MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume → HasCompactSupport G →
      eLpNorm (fun x j => T i j G x)
          (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
        ENNReal.ofReal C_CZ *
          eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume

/-- The signed weak-gradient operator selected from the pressure extension. -/
def rieszSecondWeakGradientExtensionOperator
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (i : Fin 3) (G : Vec3 → ℝ) : Vec3 → Vec3 :=
  fun x j => -(rieszSecondGradientExtensionOperator (hL2 i j)
    (hWeak11 i j) G x)

/-- The selected weak-gradient field has the indexed L^(6/5) membership. -/
theorem rieszSecondWeakGradientExtensionOperator_memLp
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {i : Fin 3} {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hGc : HasCompactSupport G) :
    MemLp (rieszSecondWeakGradientExtensionOperator hL2 hWeak11 i G)
      (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
  apply (memLp_pi_iff).2
  intro j
  change MemLp (fun x =>
    -(rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x))
      (ENNReal.ofReal ((6 : ℝ) / 5)) volume
  exact (rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG
    hGc).neg

/-- The selected weak-gradient field has the component-summed L^(6/5) bound. -/
theorem rieszSecondWeakGradientExtensionOperator_eLpNorm_le
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {i : Fin 3} {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hGc : HasCompactSupport G) :
    eLpNorm (rieszSecondWeakGradientExtensionOperator hL2 hWeak11 i G)
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
      ENNReal.ofReal (3 * czGradientComponentConstant
        rieszSecondWeakTypeConstant 1) *
        eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
  have hcomponent : ∀ j : Fin 3,
      eLpNorm (fun x =>
        -(rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x))
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
      ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
        eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
    intro j
    change eLpNorm (-rieszSecondGradientExtensionOperator
      (hL2 i j) (hWeak11 i j) G)
      (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤ _
    rw [eLpNorm_neg]
    exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le hG
      (rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG
        hGc)
      (by unfold czGradientComponentConstant; positivity)
      (rieszSecondGradientExtension_toLp_bound (hL2 i j) (hWeak11 i j) hG
        hGc)
  have hcomponent_top : ∀ j : Fin 3,
      eLpNorm (fun x =>
        -(rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x))
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume < ∞ := by
    intro j
    exact (hcomponent j).trans_lt (by finiteness)
  have hmeas : AEStronglyMeasurable
      (rieszSecondWeakGradientExtensionOperator hL2 hWeak11 i G) volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.of_eval
    intro j
    exact aestronglyMeasurable_of_eLpNorm_ne_top (hcomponent_top j).ne |>.aemeasurable
  have hsum := eLpNorm_vec3_le_sum_abs
    (p := ENNReal.ofReal ((6 : ℝ) / 5)) (by norm_num) hmeas
  calc
    eLpNorm (rieszSecondWeakGradientExtensionOperator hL2 hWeak11 i G)
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
        ∑ j : Fin 3, eLpNorm (fun x =>
          -(rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x))
            (ENNReal.ofReal ((6 : ℝ) / 5)) volume := hsum
    _ ≤ ∑ _j : Fin 3,
        ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
          eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
      exact Finset.sum_le_sum (fun j _hj => hcomponent j)
    _ = ENNReal.ofReal (3 * czGradientComponentConstant
        rieszSecondWeakTypeConstant 1) *
        eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      change (3 : ℝ≥0∞) *
          (ENNReal.ofReal (czGradientComponentConstant
            rieszSecondWeakTypeConstant 1) *
            eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume) = _
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
      calc
        ENNReal.ofReal (3 : ℝ) *
              (ENNReal.ofReal (czGradientComponentConstant
                rieszSecondWeakTypeConstant 1) *
                eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume) =
            (ENNReal.ofReal (3 : ℝ) *
              ENNReal.ofReal (czGradientComponentConstant
                rieszSecondWeakTypeConstant 1)) *
              eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by ring
        _ = ENNReal.ofReal (3 * czGradientComponentConstant
              rieszSecondWeakTypeConstant 1) *
              eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- Aggregate indexed component bounds into the selected vector-valued predicate. -/
theorem hCZ_grad_of_component_bounds
    {T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ}
    {Ccomp C_CZ : ℝ} (_ : 0 ≤ Ccomp)
    (hconst : 3 * Ccomp ≤ C_CZ)
    (hcomponent : ∀ (i j : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume → HasCompactSupport G →
        eLpNorm (T i j G) (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
          ENNReal.ofReal Ccomp *
            eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume) :
    HasCZGradientOperatorBound T C_CZ := by
  intro i G hG hGc
  have hcomponent_top : ∀ j : Fin 3,
      eLpNorm (T i j G) (ENNReal.ofReal ((6 : ℝ) / 5)) volume < ∞ := by
    intro j
    exact (hcomponent i j G hG hGc).trans_lt (by finiteness)
  have hmeas : AEStronglyMeasurable (fun x j => T i j G x) volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.of_eval
    intro j
    exact aestronglyMeasurable_of_eLpNorm_ne_top (hcomponent_top j).ne |>.aemeasurable
  have hsum := eLpNorm_vec3_le_sum_abs
    (p := ENNReal.ofReal ((6 : ℝ) / 5)) (by norm_num) hmeas
  calc
    eLpNorm (fun x j => T i j G x)
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
        ∑ j : Fin 3, eLpNorm (T i j G)
          (ENNReal.ofReal ((6 : ℝ) / 5)) volume := hsum
    _ ≤ ∑ _j : Fin 3,
        ENNReal.ofReal Ccomp * eLpNorm G
          (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
      exact Finset.sum_le_sum (fun j _hj => hcomponent i j G hG hGc)
    _ = ENNReal.ofReal (3 * Ccomp) *
        eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      change (3 : ℝ≥0∞) *
          (ENNReal.ofReal Ccomp * eLpNorm G
            (ENNReal.ofReal ((6 : ℝ) / 5)) volume) = _
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
      calc
        ENNReal.ofReal (3 : ℝ) *
              (ENNReal.ofReal Ccomp * eLpNorm G
                (ENNReal.ofReal ((6 : ℝ) / 5)) volume) =
            (ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal Ccomp) *
              eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by ring
        _ = ENNReal.ofReal (3 * Ccomp) *
              eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ ENNReal.ofReal C_CZ *
        eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst)
        (by positivity)

/-- Assemble the selected gradient bound without a classical representative premise. -/
theorem hCZ_grad_of_rieszSecond_inputs
    {T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ}
    {Ccomp C_CZ : ℝ} (hCcomp : 0 ≤ Ccomp)
    (hconst : 3 * Ccomp ≤ C_CZ)
    (hcomponent : ∀ (i j : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume → HasCompactSupport G →
        eLpNorm (T i j G) (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤
          ENNReal.ofReal Ccomp *
            eLpNorm G (ENNReal.ofReal ((6 : ℝ) / 5)) volume) :
    HasCZGradientOperatorBound T C_CZ :=
  hCZ_grad_of_component_bounds hCcomp hconst hcomponent

end Euclidean
end Foundation
end CKN
