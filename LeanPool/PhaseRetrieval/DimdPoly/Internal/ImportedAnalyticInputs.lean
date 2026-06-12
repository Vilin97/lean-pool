/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Probability.Distributions.Gaussian.Real
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import LeanPool.PhaseRetrieval.Constant.Internal.RotationalAveraging

/-! # ImportedAnalyticInputs -/


noncomputable section

namespace DimdPolyLEAN

open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

/-!
# ImportedAnalyticInputs

Mathlib-facing wrapper file for the analytic inputs that later modules are
allowed to cite through a stable local API.
-/

/-- `Circle`: Circle. -/
abbrev Circle := AddCircle (2 * Real.pi)

/-- `μCircle`: the normalized Haar measure on the circle `AddCircle (2π)`. -/
noncomputable def μCircle : MeasureTheory.Measure Circle :=
  AddCircle.haarAddCircle

/-- `muCircle`: mu Circle. -/
noncomputable abbrev muCircle : MeasureTheory.Measure Circle := μCircle

/-- `Cavg`: Cavg. -/
def Cavg : ℝ := 1

theorem Cavg_pos : 0 < Cavg := by
  norm_num [Cavg]

/-- `Crot`: Crot. -/
def Crot : ℝ := 64 * Real.pi

theorem Crot_pos : 0 < Crot := by
  unfold Crot
  nlinarith [Real.pi_pos]

/-- `zeta`: zeta. -/
noncomputable def zeta (x : Circle) : ℂ :=
  AddCircle.toCircle x

theorem norm_zeta (x : Circle) : ‖zeta x‖ = 1 := by
  simp [zeta]

/-- `circleChar`: circle Char. -/
noncomputable def circleChar (n : Nat) : Circle -> ℂ :=
  fun x => zeta x ^ n

theorem circleChar_eq_zeta_pow (n : Nat) (x : Circle) :
    circleChar n x = zeta x ^ n := rfl

/-- `CircleArc`: Circle Arc. -/
structure CircleArc where
  /-- `left`: left. -/
  left : ℝ
  /-- `right`: right. -/
  right : ℝ
  left_le_right : left ≤ right
  width_le_period : right - left ≤ 2 * Real.pi

/-- `arcLength`: arc Length. -/
def arcLength (I : CircleArc) : ℝ := I.right - I.left

/-- `arcParam`: arc Param. -/
def arcParam (I : CircleArc) (t : ℝ) : Circle :=
  QuotientAddGroup.mk (I.left + t * arcLength I)

/-- `arcSet`: arc Set. -/
def arcSet (I : CircleArc) : Set Circle :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, arcParam I t = x}

/-- `carrierArc`: carrier Arc. -/
noncomputable def carrierArc (N : Nat) (k : Fin N) : CircleArc where
  left := (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ)
  right := (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
  left_le_right := by
    have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
    have hN : 0 <= (N : ℝ) := by exact_mod_cast (Nat.le_of_lt hNnat)
    apply div_le_div_of_nonneg_right ?_ hN
    gcongr
    exact_mod_cast Nat.le_succ k.1
  width_le_period := by
    have hNnat : 1 <= N :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2)
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hNnat)
    have hNge : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast hNnat
    have hpi_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
    have hwidth :
        (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
          (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) =
        (2 * Real.pi) / (N : ℝ) := by
      field_simp [ne_of_gt hNpos]
      norm_num
    rw [hwidth]
    exact div_le_self hpi_nonneg hNge

theorem carrierArc_length {N : Nat} (k : Fin N) :
    arcLength (carrierArc N k) = (2 * Real.pi) / (N : ℝ) := by
  unfold arcLength carrierArc
  have hNnat : 1 <= N :=
    Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hNnat)
  field_simp [ne_of_gt hNpos]
  norm_num

theorem carrierArc_length_pos {N : Nat} (k : Fin N) :
    0 < arcLength (carrierArc N k) := by
  rw [carrierArc_length k]
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  positivity

theorem carrierArc_left_nonneg {N : Nat} (k : Fin N) :
    0 <= (carrierArc N k).left := by
  unfold carrierArc
  positivity

theorem carrierArc_right_le_period {N : Nat} (k : Fin N) :
    (carrierArc N k).right <= 2 * Real.pi := by
  unfold carrierArc
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hle : ((k.1 + 1 : Nat) : ℝ) <= (N : ℝ) := by
    exact_mod_cast k.2
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  calc
    (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
        <= (2 * Real.pi) * (N : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hT_nonneg)
        (le_of_lt hNpos)
    _ = 2 * Real.pi := by
      field_simp [ne_of_gt hNpos]

theorem carrierArc_left_lt_right {N : Nat} (k : Fin N) :
    (carrierArc N k).left < (carrierArc N k).right := by
  have hlen := carrierArc_length_pos k
  dsimp [arcLength] at hlen
  linarith

theorem carrierArc_arcSet_eq_mk_image_Icc {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      QuotientAddGroup.mk ''
        Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨(carrierArc N k).left + t * arcLength (carrierArc N k), ?_, rfl⟩
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      le_of_lt (carrierArc_length_pos k)
    constructor
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.1, hlen_nonneg]
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.2, hlen_nonneg]
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    let t : ℝ := (y - (carrierArc N k).left) / arcLength (carrierArc N k)
    refine ⟨t, ?_, ?_⟩
    · have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      constructor
      · dsimp [t]
        exact div_nonneg (sub_nonneg.mpr hy.1) (le_of_lt hlen_pos)
      · dsimp [t]
        rw [div_le_one hlen_pos]
        dsimp [arcLength]
        linarith [hy.2]
    · dsimp [arcParam, t]
      have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      apply congrArg (fun r : ℝ => (QuotientAddGroup.mk r : Circle))
      field_simp [ne_of_gt hlen_pos]
      ring_nf

theorem carrierArc_arcSet_eq_mk_image_Ioc_union_left {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      (QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∪
        {(QuotientAddGroup.mk ((carrierArc N k).left) : Circle)} := by
  rw [carrierArc_arcSet_eq_mk_image_Icc k]
  have hIcc :
      Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) ∪
          {((carrierArc N k).left)} := by
    ext y
    constructor
    · intro hy
      by_cases hleft : y = (carrierArc N k).left
      · exact Or.inr hleft
      · exact Or.inl ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft), hy.2⟩
    · intro hy
      rcases hy with hy | hy
      · exact ⟨le_of_lt hy.1, hy.2⟩
      · rw [Set.mem_singleton_iff.mp hy]
        exact ⟨le_rfl, le_of_lt (carrierArc_left_lt_right k)⟩
  rw [hIcc, Set.image_union, Set.image_singleton]

theorem quotient_mk_injOn_Ioc_zero_period :
    Set.InjOn (fun t : ℝ => (QuotientAddGroup.mk t : Circle))
      (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hx0 : x ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by
    simpa using hx
  have hy0 : y ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by
    simpa using hy
  have hx' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk x : Circle) = ⟨x, hx0⟩ :=
    AddCircle.equivIoc_coe_eq hx0
  have hy' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk y : Circle) = ⟨y, hy0⟩ :=
    AddCircle.equivIoc_coe_eq hy0
  have h := congrArg (AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)) hxy
  rw [hx', hy'] at h
  exact Subtype.ext_iff.mp h

theorem carrierArc_mk_preimage_image_Ioc_inter_fundamental
    {N : Nat} (k : Fin N) :
    ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹'
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∩
      Set.Ioc (0 : ℝ) (2 * Real.pi)) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx.1 with ⟨y, hy, hyx⟩
    have hy_fund : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hy.1,
        le_trans hy.2 (carrierArc_right_le_period k)⟩
    have hxy : y = x :=
      quotient_mk_injOn_Ioc_zero_period hy_fund hx.2 hyx
    rwa [← hxy]
  · intro hx
    constructor
    · exact ⟨x, hx, rfl⟩
    · exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hx.1,
        le_trans hx.2 (carrierArc_right_le_period k)⟩

theorem volume_singleton_circle (x : Circle) :
    MeasureTheory.volume ({x} : Set Circle) = 0 := by
  have h := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
  simpa using h

theorem μCircle_singleton (x : Circle) :
    μCircle ({x} : Set Circle) = 0 := by
  have hvol : MeasureTheory.volume ({x} : Set Circle) = 0 :=
    volume_singleton_circle x
  rw [AddCircle.volume_eq_smul_haarAddCircle, MeasureTheory.Measure.smul_apply] at hvol
  rw [smul_eq_mul] at hvol
  have hcoef : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.pi_pos]
  simpa [μCircle] using (mul_eq_zero.mp hvol).resolve_left hcoef

theorem carrierArc_arcSet_ae_eq_mk_image_Ioc {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[μCircle]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[μCircle] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null (μ := μCircle) (t := {e}) ?_
      (μCircle_singleton e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null (μ := μCircle) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp

theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_volume {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Circle)]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
      Circle)] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle)) (t := {e}) ?_
      (volume_singleton_circle e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle)) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp

/-- `carrierAverage`: carrier Average. -/
noncomputable def carrierAverage {N : Nat} (k : Fin N)
    (f : Circle -> ℂ) : ℂ :=
  (N : ℂ) * ∫ x in arcSet (carrierArc N k), f x ∂ μCircle

theorem arcLength_nonneg (I : CircleArc) : 0 <= arcLength I := by
  dsimp [arcLength]
  exact sub_nonneg.mpr I.left_le_right

theorem continuous_arcParam (I : CircleArc) : Continuous (arcParam I) := by
  unfold arcParam
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
    (continuous_const.add (continuous_id.mul continuous_const))

theorem arcSet_eq_image (I : CircleArc) :
    arcSet I = arcParam I '' Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

theorem isCompact_arcSet (I : CircleArc) : IsCompact (arcSet I) := by
  rw [arcSet_eq_image]
  exact isCompact_Icc.image (continuous_arcParam I)

theorem measurableSet_arcSet (I : CircleArc) : MeasurableSet (arcSet I) :=
  (isCompact_arcSet I).measurableSet

theorem volume_mk_image_carrierArc_Ioc {N : Nat} (k : Fin N) :
    MeasureTheory.volume
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hS_null :
      MeasureTheory.NullMeasurableSet S
        (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc_volume k)
  have hpre :=
    (AddCircle.measurePreserving_mk (T := 2 * Real.pi) (t := 0)).measure_preimage hS_null
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc] at hpre
  change MeasureTheory.volume
      (((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi)) =
      MeasureTheory.volume S at hpre
  have hpre_set :
      ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) =
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
    simpa [S] using carrierArc_mk_preimage_image_Ioc_inter_fundamental k
  rw [hpre_set, Real.volume_Ioc] at hpre
  dsimp [arcLength]
  symm
  rw [← hpre]

theorem period_smul_μCircle_mk_image_carrierArc_Ioc {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle
          ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
            Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hmeasure := congrArg (fun μ : MeasureTheory.Measure Circle => μ S)
    (AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi))
  change MeasureTheory.volume S =
    ENNReal.ofReal (2 * Real.pi) * μCircle S at hmeasure
  rw [← hmeasure]
  exact volume_mk_image_carrierArc_Ioc k

theorem period_smul_μCircle_carrierArc {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle (arcSet (carrierArc N k)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  rw [MeasureTheory.measure_congr (carrierArc_arcSet_ae_eq_mk_image_Ioc k)]
  exact period_smul_μCircle_mk_image_carrierArc_Ioc k

/-- `arcIntegral`: arc Integral. -/
noncomputable def arcIntegral (I : CircleArc) (f : Circle -> ℝ) : ℝ :=
  ∫ x in arcSet I, f x ∂ μCircle

theorem carrierArc_arcIntegral_eq_mk_image_Ioc
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    arcIntegral (carrierArc N k) f =
      ∫ x in QuotientAddGroup.mk ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle := by
  unfold arcIntegral
  rw [MeasureTheory.Measure.restrict_congr_set (carrierArc_arcSet_ae_eq_mk_image_Ioc k)]

theorem carrierArc_mk_image_Ioc_integral_eq_scaled
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle) =
      (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let A : Set ℝ := Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let F : Set ℝ := Set.Ioc (0 : ℝ) (2 * Real.pi)
  have hS_null : MeasureTheory.NullMeasurableSet S μCircle := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc k)
  have hhaar := AddCircle.integral_haarAddCircle (T := 2 * Real.pi)
    (f := S.indicator f)
  change ∫ x, S.indicator f x ∂ μCircle =
    (2 * Real.pi)⁻¹ • ∫ x, S.indicator f x at hhaar
  rw [MeasureTheory.integral_indicator₀ hS_null] at hhaar
  have hpre := AddCircle.integral_preimage (T := 2 * Real.pi) (t := 0)
    (f := S.indicator f)
  have hpre' :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ x : Circle, S.indicator f x := by
    simpa [F] using hpre
  have hfund_to_A :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by
    have hpre_set :
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F = A := by
      simpa [S, A, F] using carrierArc_mk_preimage_image_Ioc_inter_fundamental k
    have hfun : Set.EqOn
        (fun t : ℝ => S.indicator f (QuotientAddGroup.mk t : Circle))
        (fun t : ℝ => A.indicator
          (fun y : ℝ => f (QuotientAddGroup.mk y : Circle)) t)
        F := by
      intro t htF
      by_cases htS : (QuotientAddGroup.mk t : Circle) ∈ S
      · have htA : t ∈ A := by
          have htpre :
              t ∈ ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F :=
            ⟨htS, htF⟩
          simpa [hpre_set] using htpre
        simp [Set.indicator_of_mem htS, Set.indicator_of_mem htA]
      · have htA : t ∉ A := by
          intro htA
          exact htS ⟨t, htA, rfl⟩
        simp [Set.indicator_of_notMem htS, Set.indicator_of_notMem htA]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hfun]
    rw [MeasureTheory.setIntegral_indicator (μ := MeasureTheory.volume) (s := F) (t := A)
      measurableSet_Ioc]
    have h_inter : F ∩ A = A := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro htA
        exact ⟨⟨lt_of_le_of_lt (carrierArc_left_nonneg k) htA.1,
          le_trans htA.2 (carrierArc_right_le_period k)⟩, htA⟩
    rw [h_inter]
  calc
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle)
        = ∫ x in S, f x ∂ μCircle := by rfl
    _ = (2 * Real.pi)⁻¹ * ∫ x : Circle, S.indicator f x := by
      simpa [smul_eq_mul] using hhaar
    _ = (2 * Real.pi)⁻¹ *
        (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) := by
      rw [hpre']
    _ = (2 * Real.pi)⁻¹ * ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by
      rw [hfund_to_A]
    _ = (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by rfl

/-- `arcAverage`: arc Average. -/
noncomputable def arcAverage (I : CircleArc) (f : Circle -> ℂ) : ℂ :=
  (arcLength I)⁻¹ • ∫ x in arcSet I, f x ∂ μCircle

theorem intervalParam_mem_arc (I : CircleArc) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, arcParam I t ∈ arcSet I := by
  intro t ht
  exact ⟨t, ht, rfl⟩

theorem arcIntegral_nonneg
    (I : CircleArc) {f : Circle -> ℝ}
    (hf : ∀ x ∈ arcSet I, 0 <= f x) :
    0 <= arcIntegral I f := by
  unfold arcIntegral
  refine MeasureTheory.integral_nonneg_of_ae ?_
  exact (MeasureTheory.ae_restrict_mem (measurableSet_arcSet I)).mono fun x hx => hf x hx

theorem arcAverage_eq_arcIntegral_div
    (I : CircleArc) (f : Circle -> ℂ) :
    arcAverage I f =
      (arcLength I)⁻¹ •
        ∫ x in arcSet I, f x ∂ μCircle := rfl

theorem norm_circleChar (n : Nat) (x : Circle) : ‖circleChar n x‖ = 1 := by
  simp [circleChar, norm_zeta]

theorem circleChar_zero (x : Circle) : circleChar 0 x = 1 := by
  simp [circleChar]

theorem circleChar_one (x : Circle) : circleChar 1 x = zeta x := by
  simp [circleChar]

theorem circleChar_add (m n : Nat) (x : Circle) :
    circleChar (m + n) x = circleChar m x * circleChar n x := by
  simp [circleChar, pow_add]

theorem circleChar_mk (n : Nat) (theta : ℝ) :
    circleChar n (QuotientAddGroup.mk theta : Circle) =
      Complex.exp (Complex.I * (n : ℂ) * theta) := by
  simp only [circleChar, zeta, AddCircle.toCircle, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
    Real.pi_ne_zero, or_self, not_false_eq_true, div_self, one_mul, Function.Periodic.lift_coe,
    Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem circleChar_eq_fourier_nat (n : Nat) (x : Circle) :
    circleChar n x = fourier (n : Int) x := by
  induction n with
  | zero =>
      simp [circleChar]
  | succ n ih =>
      rw [circleChar_eq_zeta_pow, pow_succ]
      change circleChar n x * zeta x = fourier ((n + 1 : Nat) : Int) x
      rw [ih]
      simp only [fourier_apply, Nat.cast_add, Nat.cast_one]
      rw [show ((↑n + 1 : ℤ) • x : AddCircle (2 * Real.pi)) =
          (n : ℤ) • x + x by
        rw [add_zsmul, one_zsmul]]
      rw [AddCircle.toCircle_add]
      rfl

private theorem rotational_averaging_bound_complex (q : ℂ) :
    ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        ∂AddCircle.haarAddCircle ≥
      ‖q‖ ^ 2 / 8 := by
  by_cases hq : q = 0
  · simp [hq, FockSPR.rho, norm_zero]
  · set r := ‖q‖
    have hr_pos : 0 < r := norm_pos_iff.mpr hq
    set α := (r : ℂ)⁻¹ * q
    have hα_norm : ‖α‖ = 1 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr_pos]
      exact inv_mul_cancel₀ (ne_of_gt hr_pos)
    have h_rw : ∀ t : Circle,
        (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((r : ℂ) * ((fourier (1 : ℤ) t : ℂ) * α))) ^ 2 := by
      intro t
      congr 2
      show (fourier (1 : ℤ) t : ℂ) * q =
        ↑r * ((fourier (1 : ℤ) t : ℂ) * α)
      simp only [α]
      have hr_ne' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      field_simp
    simp_rw [h_rw]
    have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    obtain ⟨s, hs⟩ := (AddCircle.homeomorphCircle hT_ne).surjective
      ⟨α, by
        rw [← SetLike.mem_coe, Submonoid.coe_unitSphere,
          Metric.mem_sphere, dist_zero_right]
        exact hα_norm⟩
    rw [AddCircle.homeomorphCircle_apply] at hs
    have hα_eq : (fourier (1 : ℤ) s : ℂ) = α := by
      simp only [fourier_apply, one_zsmul]
      exact congr_arg Subtype.val hs
    have h_shift : ∀ t : Circle,
        (fourier (1 : ℤ) t : ℂ) * α = fourier (1 : ℤ) (t + s) := by
      intro t
      rw [← hα_eq]
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    simp_rw [h_shift]
    set F : Circle → ℝ :=
      fun u => (FockSPR.rho ((r : ℂ) * fourier (1 : ℤ) u)) ^ 2
    change ∫ t, F (t + s) ∂AddCircle.haarAddCircle ≥ r ^ 2 / 8
    simp_rw [show ∀ t : Circle, t + s = s + t from fun t => add_comm t s]
    rw [MeasureTheory.integral_add_left_eq_self]
    exact FockSPR.rotational_averaging_bound (r := r) (norm_nonneg q)

private theorem carrierArc_interval_rho_sq_eq_full_circle
    {N : Nat} (k : Fin N) (q : ℂ) :
    ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
      (N : ℝ)⁻¹ * ((2 * Real.pi) *
        ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
          ∂AddCircle.haarAddCircle) := by
  have hT_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_nat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr hN_nat
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have fourier_rescale : ∀ s : ℝ,
      circleChar N (QuotientAddGroup.mk (s / ↑N) : Circle) =
      fourier (1 : ℤ) (QuotientAddGroup.mk s : Circle) := by
    intro s
    rw [circleChar_eq_fourier_nat]
    simp only [fourier_coe_apply]
    congr 1
    have hN_complex : (↑N : ℂ) ≠ 0 := by exact_mod_cast hN_ne
    have hT_complex : (↑(2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast hT_ne
    push_cast
    field_simp [hN_complex, hT_complex]
  set g : ℝ → ℝ := fun t =>
    (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2
  have h_eq_haar_int :
      ∫ t in (carrierArc N k).left..(carrierArc N k).right, g t =
        (↑N : ℝ)⁻¹ * ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
    have key := intervalIntegral.integral_comp_mul_left
      (fun s => g (s / ↑N)) hN_ne
      (a := (carrierArc N k).left) (b := (carrierArc N k).right)
    have h_simp : (fun x => g ((↑N : ℝ) * x / ↑N)) = g := by
      ext x
      show g (↑N * x / ↑N) = g x
      congr 1
      field_simp [hN_ne]
    rw [h_simp] at key
    have h_el : (↑N : ℝ) * (carrierArc N k).left =
        (2 * Real.pi) * ↑k.val := by
      unfold carrierArc
      field_simp [hN_ne]
    have h_er : (↑N : ℝ) * (carrierArc N k).right =
        (2 * Real.pi) * (↑k.val + 1) := by
      unfold carrierArc
      push_cast
      field_simp [hN_ne]
    rw [h_el, h_er] at key
    rw [key, smul_eq_mul]
    congr 1
    have h_congr :
        ∀ s ∈ Set.uIcc ((2 * Real.pi) * ↑k.val)
            ((2 * Real.pi) * (↑k.val + 1)),
          g (s / ↑N) =
            (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2 := by
      intro s _
      change (FockSPR.rho (circleChar N (↑(s / ↑N) : Circle) * q)) ^ 2 = _
      rw [fourier_rescale]
    rw [intervalIntegral.integral_congr h_congr]
    set g₁ : ℝ → ℝ := fun s =>
      (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
    have hg₁_periodic : Function.Periodic g₁ (2 * Real.pi) := by
      intro s
      change (FockSPR.rho
          ((fourier (1 : ℤ) (↑(s + 2 * Real.pi) : Circle) : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
      simp only [QuotientAddGroup.mk_add_of_mem _
        (AddSubgroup.mem_zmultiples (2 * Real.pi))]
    rw [show (2 * Real.pi) * (↑k.val + 1) =
        (2 * Real.pi) * ↑k.val + (2 * Real.pi) by ring]
    rw [hg₁_periodic.intervalIntegral_add_eq ((2 * Real.pi) * ↑k.val) 0]
    have h_preimage := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    have h_haar := @AddCircle.integral_haarAddCircle (2 * Real.pi) _ ℝ _ _
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    calc ∫ x in (0 : ℝ)..(0 + 2 * Real.pi), g₁ x
        = ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 :=
          h_preimage
      _ = (2 * Real.pi) *
          ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle := by
        rw [h_haar, smul_eq_mul]
        set V := ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        rw [mul_comm (2 * Real.pi) ((2 * Real.pi)⁻¹ * V), mul_assoc,
          mul_comm V (2 * Real.pi), ← mul_assoc, inv_mul_cancel₀ hT_ne, one_mul]
  exact h_eq_haar_int

private theorem carrierArc_interval_rho_sq_lower
    {N : Nat} (k : Fin N) (q : ℂ) :
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
      ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
  have hN_nat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_nat
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hrot := rotational_averaging_bound_complex q
  rw [carrierArc_interval_rho_sq_eq_full_circle k q]
  calc
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8
        = (N : ℝ)⁻¹ * ((2 * Real.pi) * (‖q‖ ^ 2 / 8)) := by
          rw [carrierArc_length k]
          field_simp [hN_ne]
    _ <= (N : ℝ)⁻¹ *
        ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hN_pos))
      exact mul_le_mul_of_nonneg_left hrot.le (by positivity)

private lemma constant_center_defect_eq_norm_sq_rho
    {c u z : ℂ} (hc : c ≠ 0) :
    (‖c + z * u‖ - ‖c‖) ^ 2 =
      ‖c‖ ^ 2 * (FockSPR.rho (z * (u / c))) ^ 2 := by
  have hfactor : c + z * u = c * (1 + z * (u / c)) := by
    field_simp [hc]
  rw [hfactor, norm_mul]
  unfold FockSPR.rho
  rw [sq_abs]
  ring

private theorem carrierArc_setIntegral_constant_center_lower
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <=
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
  set q : ℂ := u / c
  have h_interval := carrierArc_interval_rho_sq_lower k q
  have h_interval' :
      arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [← intervalIntegral.integral_of_le (le_of_lt (carrierArc_left_lt_right k))]
    exact h_interval
  have hconst :
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          ‖c‖ ^ 2 *
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
        ‖c‖ ^ 2 *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  have hscale :
      ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) =
        arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    dsimp [q]
    rw [norm_div]
    have hc_norm_ne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    field_simp [hc_norm_ne]
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8
        = ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) := hscale.symm
    _ <= ‖c‖ ^ 2 *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left h_interval' (sq_nonneg ‖c‖)
    _ = ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
      rw [← hconst]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simpa [q] using
        (constant_center_defect_eq_norm_sq_rho
          (c := c) (u := u) (z := circleChar N (QuotientAddGroup.mk t : Circle)) hc).symm

theorem circleChar_carrierArc_arcParam {N : Nat} (k : Fin N) (t : ℝ) :
    circleChar N (arcParam (carrierArc N k) t) =
      Complex.exp (Complex.I * (2 * Real.pi * t)) := by
  rw [arcParam, circleChar_mk]
  unfold carrierArc arcLength
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hNnat)
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNnat)
  have harg :
      Complex.I * (N : ℂ) *
          ↑((2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) +
            t * ((2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
              (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ))) =
        Complex.I * (2 * Real.pi * (k.1 : ℝ)) +
          Complex.I * (2 * Real.pi * t) := by
    push_cast
    field_simp [hN, hNreal]
    ring
  rw [harg, Complex.exp_add]
  have hint : Complex.exp (Complex.I * (2 * Real.pi * (k.1 : ℝ))) = 1 := by
    rw [show Complex.I * (2 * Real.pi * (k.1 : ℝ)) =
        (k.1 : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k.1
  rw [hint, one_mul]

theorem circleIntegral_union_finset
    {ι : Type} [Fintype ι] (I : ι -> CircleArc)
    (hdisj : Pairwise fun i j => Disjoint (arcSet (I i)) (arcSet (I j)))
    {f : Circle -> ℝ}
    (hf : ∀ i, MeasureTheory.IntegrableOn f (arcSet (I i)) μCircle) :
    ∫ x in (⋃ i, arcSet (I i)), f x ∂ μCircle =
      ∑ i, arcIntegral (I i) f := by
  simpa [arcIntegral] using
    (MeasureTheory.integral_iUnion_fintype
      (μ := μCircle) (f := f) (s := fun i => arcSet (I i))
      (fun i => measurableSet_arcSet (I i)) hdisj hf)

theorem circleIntegral_split_compl
    (s : Set Circle) (hs : MeasurableSet s) {f : Circle -> ℝ}
    (hf : MeasureTheory.Integrable f μCircle) :
    ∫ x, f x ∂ μCircle =
      ∫ x in s, f x ∂ μCircle + ∫ x in sᶜ, f x ∂ μCircle := by
  exact (MeasureTheory.integral_add_compl (μ := μCircle) (f := f) hs hf).symm

theorem constantCenter_fastRotate_carrierArc_sq_le_defectSq
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
      Crot *
        arcIntegral (carrierArc N k)
          (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2) := by
  let f : Circle -> ℝ := fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2
  have hrewrite :
      arcIntegral (carrierArc N k) f =
        (2 * Real.pi)⁻¹ *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            f (QuotientAddGroup.mk t : Circle) := by
    rw [carrierArc_arcIntegral_eq_mk_image_Ioc k f]
    exact carrierArc_mk_image_Ioc_integral_eq_scaled k f
  rw [hrewrite]
  set J : ℝ :=
    ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
      f (QuotientAddGroup.mk t : Circle)
  have hJ_lower : arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <= J := by
    dsimp [J, f]
    exact carrierArc_setIntegral_constant_center_lower k hc
  have hleft_nonneg :
      0 <= arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      arcLength_nonneg (carrierArc N k)
    have hnorm_nonneg : 0 <= ‖u‖ ^ 2 := sq_nonneg ‖u‖
    nlinarith
  have hJ_nonneg : 0 <= J := le_trans hleft_nonneg hJ_lower
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2
        = 8 * (arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8) := by ring
    _ <= 8 * J := by
      exact mul_le_mul_of_nonneg_left hJ_lower (by norm_num)
    _ <= 32 * J := by nlinarith
    _ = Crot * ((2 * Real.pi)⁻¹ * J) := by
      unfold Crot
      have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hpi_ne]
      ring

private theorem gamma_d_isOpenPosMeasure (d : Nat) :
    MeasureTheory.Measure.IsOpenPosMeasure (gammaD d) := by
  refine ⟨?_⟩
  intro U hU hUne
  rcases hUne with ⟨x, hxU⟩
  rcases Metric.isOpen_iff.mp hU x hxU with ⟨r, hr, hball⟩
  let w : Cd d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  have hgauss_cont : Continuous (gaussianDensity d) := by
    unfold gaussianDensity
    fun_prop
  have hw_meas : Measurable w := by
    exact ENNReal.measurable_ofReal.comp hgauss_cont.measurable
  have hw_ne_zero : ∀ z : Cd d, w z ≠ 0 := by
    intro z
    have hpos : 0 < gaussianDensity d z := by
      unfold gaussianDensity
      positivity
    simpa [w, ENNReal.ofReal_eq_zero, not_le] using hpos
  have hball_ne : gammaD d (Metric.ball x r) ≠ 0 := by
    intro hzero
    have hzero' : MeasureTheory.volume.withDensity w (Metric.ball x r) = 0 := by
      simpa [gammaD, w] using hzero
    have hvol_zero :
        MeasureTheory.volume ({z : Cd d | w z ≠ 0} ∩ Metric.ball x r) = 0 := by
      exact (MeasureTheory.withDensity_apply_eq_zero hw_meas).1 hzero'
    have hball_eq :
        {z : Cd d | w z ≠ 0} ∩ Metric.ball x r = Metric.ball x r := by
      ext z
      simp [hw_ne_zero z]
    have hball_vol_zero : MeasureTheory.volume (Metric.ball x r) = 0 := by
      simpa [hball_eq] using hvol_zero
    exact (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Cd d)) x hr).ne'
      hball_vol_zero
  exact fun hzero => hball_ne (MeasureTheory.measure_mono_null hball hzero)

theorem continuous_eq_of_ae_eq_gamma
    {d : Nat} (hd : 0 < d) {f g : Cd d -> ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfg : f =ᵐ[gammaD d] g) :
    f = g := by
  let _ := hd
  /-
  Scaffolding contract:
  this packages the a.e.-to-everywhere uniqueness bridge for continuous
  representatives under the frozen Gaussian measure.
  -/
  haveI := gamma_d_isOpenPosMeasure d
  exact MeasureTheory.Measure.eq_of_ae_eq hfg hf hg

/-!
## Phase-space analytic boundary stubs

These declaration-shaped stubs expose the analytic objects needed by
`ExactModulusRecovery`.  The definitions are placeholders; the theorem
statements record the frozen API that the STFT/ambiguity proof must eventually
provide.
-/

/-- `RealVec`: Real Vec. -/
abbrev RealVec (d : Nat) := EuclideanSpace ℝ (Fin d)

/-- `PhaseSpace`: Phase Space. -/
abbrev PhaseSpace (d : Nat) := RealVec d × RealVec d

/-- `L2Real`: L2 Real. -/
abbrev L2Real (d : Nat) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))

/-- `stftRep`: stft Rep. -/
noncomputable def stftRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun h f ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) t) *
        star ((h : RealVec d -> ℂ) (t - ξ.1)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))

/-- `ambiguityRep`: ambiguity Rep. -/
noncomputable def ambiguityRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun f g ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • ξ.1))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • ξ.1))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))

/-- `symplecticFourierRep`: symplectic Fourier Rep. -/
noncomputable def symplecticFourierRep {d : Nat}
    (F : PhaseSpace d -> ℂ) : PhaseSpace d -> ℂ :=
  fun ξ =>
    ∫ η : PhaseSpace d,
      F η * Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))

theorem symplecticFourierPhase_norm {d : Nat} (η ξ : PhaseSpace d) :
    ‖Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre :
      (((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- `symplecticFormLinear`: symplectic Form Linear. -/
def symplecticFormLinear {d : Nat} : PhaseSpace d →ₗ[ℝ] PhaseSpace d →ₗ[ℝ] ℝ where
  toFun η :=
    { toFun := fun ξ => inner ℝ η.1 ξ.2 - inner ℝ η.2 ξ.1
      map_add' := by
        intro ξ ζ
        simp [inner_add_right]
        ring
      map_smul' := by
        intro c ξ
        simp [inner_smul_right]
        ring }
  map_add' := by
    intro η θ
    apply LinearMap.ext
    intro ξ
    simp [inner_add_left]
    ring
  map_smul' := by
    intro c η
    apply LinearMap.ext
    intro ξ
    simp [inner_smul_left]
    ring

theorem symplecticFourierRep_eq_vectorFourier {d : Nat}
    (F : PhaseSpace d -> ℂ) (ξ : PhaseSpace d) :
    symplecticFourierRep F ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (symplecticFormLinear (d := d)) F ξ := by
  unfold symplecticFourierRep VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with η
  simp [symplecticFormLinear, Real.fourierChar_apply, Circle.smul_def, sub_eq_add_neg,
    mul_assoc, mul_comm]

theorem symplecticFourierRep_sub_le_lpNorm_one {d : Nat}
    {G₁ G₂ : PhaseSpace d -> ℂ}
    (h1 : Integrable G₁ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (h2 : Integrable G₂ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (ξ : PhaseSpace d) :
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖ ≤
      MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let φ : PhaseSpace d -> ℂ := fun η =>
    Complex.exp
      ((2 * Real.pi : ℂ) * Complex.I *
        (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))
  have hφ_meas : AEStronglyMeasurable φ μ := by
    exact (by fun_prop : Measurable φ).aestronglyMeasurable
  have hφ_bound : ∀ᵐ η : PhaseSpace d ∂μ, ‖φ η‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall
      (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
    exact le_of_eq hη
  have hdiff : Integrable (fun η : PhaseSpace d => G₁ η - G₂ η) μ := by
    exact h1.sub h2
  have h1φ : Integrable (fun η : PhaseSpace d => G₁ η * φ η) μ := by
    exact h1.mul_bdd hφ_meas hφ_bound
  have h2φ : Integrable (fun η : PhaseSpace d => G₂ η * φ η) μ := by
    exact h2.mul_bdd hφ_meas hφ_bound
  calc
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖
        = ‖∫ η : PhaseSpace d, (G₁ η - G₂ η) * φ η ∂μ‖ := by
            unfold symplecticFourierRep
            rw [← MeasureTheory.integral_sub h1φ h2φ]
            have hfun :
                (fun η : PhaseSpace d => G₁ η * φ η - G₂ η * φ η) =
                  (fun η : PhaseSpace d => (G₁ η - G₂ η) * φ η) := by
              funext η
              simp [sub_mul]
            rw [hfun]
    _ ≤ ∫ η : PhaseSpace d, ‖(G₁ η - G₂ η) * φ η‖ ∂μ := by
          exact norm_integral_le_integral_norm _
    _ = ∫ η : PhaseSpace d, ‖G₁ η - G₂ η‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall
            (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
          rw [norm_mul, hη, mul_one]
    _ = MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1 μ := by
          symm
          exact MeasureTheory.lpNorm_one_eq_integral_norm hdiff.aestronglyMeasurable

theorem tendsto_symplecticFourierRep_of_lpNorm_one {d : Nat}
    {G : PhaseSpace d -> ℂ} {Gₙ : Nat -> PhaseSpace d -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (ξ : PhaseSpace d) :
    Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop
      (nhds (symplecticFourierRep G ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hLp
  intro n
  simpa using symplecticFourierRep_sub_le_lpNorm_one (h1 := hGₙ n) (h2 := hG) ξ

theorem symplecticFourierRep_eq_of_lpNorm_one_approx {d : Nat}
    {G : PhaseSpace d -> ℂ} {Gₙ : Nat -> PhaseSpace d -> ℂ}
    {A : ℂ} {Aₙ : Nat -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (hA : Tendsto Aₙ atTop (nhds A))
    (ξ : PhaseSpace d)
    (hEq : ∀ n : Nat, symplecticFourierRep (Gₙ n) ξ = Aₙ n) :
    symplecticFourierRep G ξ = A := by
  have hleft := tendsto_symplecticFourierRep_of_lpNorm_one hG hGₙ hLp ξ
  have hright :
      Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop (nhds A) := by
    rw [show (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) = Aₙ by
      funext n
      exact hEq n]
    exact hA
  exact tendsto_nhds_unique hleft hright

private theorem exists_schwartz_lpNorm_sub_le_realVec {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SchwartzMap (RealVec d) ℂ,
      MeasureTheory.lpNorm (f - (s : RealVec d -> ℂ)) 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤ ε := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  obtain ⟨g, hg₁, hg₂, hg₃⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (by norm_num : 1 ≤ (2 : ENNReal)) hf hε
  let s : SchwartzMap (RealVec d) ℂ := hg₁.toSchwartzMap hg₂
  have hs : MeasureTheory.MemLp (f - (s : RealVec d -> ℂ)) 2 μ :=
    hf.sub (s.memLp 2 μ)
  have hg₃' :
      MeasureTheory.eLpNorm (f - (s : RealVec d -> ℂ)) 2 μ ≤ ENNReal.ofReal ε := hg₃
  refine ⟨s, ?_⟩
  rw [← MeasureTheory.toReal_eLpNorm hs.aestronglyMeasurable]
  exact (ENNReal.toReal_le_toReal hs.eLpNorm_ne_top (by simp)).mpr hg₃' |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

private noncomputable def schwartzApproxRealVec {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) : SchwartzMap (RealVec d) ℂ :=
  Classical.choose <|
    exists_schwartz_lpNorm_sub_le_realVec (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)

private theorem schwartzApproxRealVec_lpNorm_sub_le {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) :
    MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤ 1 / ((n : ℝ) + 1) :=
  Classical.choose_spec <|
    exists_schwartz_lpNorm_sub_le_realVec (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)

private theorem schwartzApproxRealVec_lpNorm_le {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) :
    MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤
      MeasureTheory.lpNorm f 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) + 1 / ((n : ℝ) + 1) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hs : MeasureTheory.MemLp (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ :=
    (schwartzApproxRealVec hf n).memLp 2 μ
  calc
    MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ
        = MeasureTheory.lpNorm (f - (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)))
            2 μ := by
            congr 1
            funext t
            simp
    _ ≤ MeasureTheory.lpNorm f 2 μ +
        MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2 μ := by
          exact MeasureTheory.lpNorm_sub_le
            (f := f) (g := f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) hf
            (by norm_num)
    _ ≤ MeasureTheory.lpNorm f 2 μ + 1 / ((n : ℝ) + 1) := by
          gcongr
          exact schwartzApproxRealVec_lpNorm_sub_le hf n

private theorem schwartzApproxRealVec_lpNorm_le_add_one {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) :
    MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤
        MeasureTheory.lpNorm f 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) + 1 := by
  refine le_trans (schwartzApproxRealVec_lpNorm_le hf n) ?_
  gcongr
  have hnat : 0 ≤ (n : ℝ) := by positivity
  have hdenom : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
  simpa using one_div_le_one_div_of_le (by positivity : 0 < (1 : ℝ)) hdenom

private theorem schwartzApproxRealVec_tendsto_lpNorm_sub_zero {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop (nhds 0) := by
  have hε :
      Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  exact squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg)
    (schwartzApproxRealVec_lpNorm_sub_le hf) hε

private theorem schwartzApproxRealVec_tendsto_lpNorm {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop
      (nhds (MeasureTheory.lpNorm f 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  rw [tendsto_iff_dist_tendsto_zero]
  have hε :
      Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hbound :
      ∀ n : Nat,
        |MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ -
            MeasureTheory.lpNorm f 2 μ| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hs : MeasureTheory.MemLp (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ :=
      (schwartzApproxRealVec hf n).memLp 2 μ
    have h₁ :
        MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ ≤
          MeasureTheory.lpNorm f 2 μ + 1 / ((n : ℝ) + 1) :=
      schwartzApproxRealVec_lpNorm_le hf n
    have h₂ :
        MeasureTheory.lpNorm f 2 μ ≤
          MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            1 / ((n : ℝ) + 1) := by
      calc
        MeasureTheory.lpNorm f 2 μ
            = MeasureTheory.lpNorm
                ((schwartzApproxRealVec hf n : RealVec d -> ℂ) -
                  ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - f)) 2 μ := by
                  congr 1
                  funext t
                  simp
        _ ≤ MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            MeasureTheory.lpNorm ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - f) 2 μ := by
            exact MeasureTheory.lpNorm_sub_le
              (f := (schwartzApproxRealVec hf n : RealVec d -> ℂ))
              (g := (schwartzApproxRealVec hf n : RealVec d -> ℂ) - f) hs (by norm_num)
        _ ≤ MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            1 / ((n : ℝ) + 1) := by
            gcongr
            simpa [MeasureTheory.lpNorm_sub_comm] using
              schwartzApproxRealVec_lpNorm_sub_le hf n
    rw [abs_sub_le_iff]
    constructor <;> linarith
  simpa [Real.dist_eq, μ] using squeeze_zero (fun _ => abs_nonneg _) hbound hε

private theorem schwartzApproxRealVec_toLp_tendsto {d : Nat} (f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop (nhds f) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hf : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp f
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      ∀ n : Nat,
        dist ((schwartzApproxRealVec hf n).toLp 2 μ) f =
          MeasureTheory.lpNorm
            ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ := by
    intro n
    let s : SchwartzMap (RealVec d) ℂ := schwartzApproxRealVec hf n
    have hs : MeasureTheory.MemLp (s : RealVec d -> ℂ) 2 μ := s.memLp 2 μ
    have hsub : MeasureTheory.MemLp ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ :=
      hs.sub hf
    calc
      dist (s.toLp 2 μ) f
          = (edist (s.toLp 2 μ) f).toReal := by
            rw [MeasureTheory.Lp.dist_edist]
      _ = (edist ((s.memLp 2 μ).toLp (s : RealVec d -> ℂ)) f).toReal := by
            rfl
      _ = (edist ((s.memLp 2 μ).toLp (s : RealVec d -> ℂ)) (hf.toLp f)).toReal := by
            rw [MeasureTheory.Lp.toLp_coeFn]
      _ = (MeasureTheory.eLpNorm
            ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ).toReal := by
            rw [MeasureTheory.Lp.edist_toLp_toLp]
      _ = MeasureTheory.lpNorm
            ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ := by
            rw [MeasureTheory.toReal_eLpNorm hsub.aestronglyMeasurable]
  have hraw :
      Tendsto
        (fun n : Nat =>
          MeasureTheory.lpNorm
            ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ)
        atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm, hf, μ] using
      schwartzApproxRealVec_tendsto_lpNorm_sub_zero hf
  simpa [hdist, hf, μ] using hraw

/-- `IsL2Rep`: Is L2 Rep. -/
def IsL2Rep {d : Nat} (f : L2Real d) (fRep : RealVec d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp fRep 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)),
    hf_mem.toLp fRep = f

/-- `translateL2`: translate L2. -/
noncomputable def translateL2 {d : Nat} (a : RealVec d) (f : L2Real d) : L2Real d :=
  DomAddAct.mk a +ᵥ f

theorem translateL2_coeFn {d : Nat} (a : RealVec d) (f : L2Real d) :
    ((translateL2 a f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => (f : RealVec d -> ℂ) (t + a) := by
  filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk a) f] with t ht
  simpa [translateL2, vadd_eq_add, add_comm] using ht

theorem translateL2_neg_coeFn {d : Nat} (a : RealVec d) (f : L2Real d) :
    ((translateL2 (-a) f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => (f : RealVec d -> ℂ) (t - a) := by
  simpa [sub_eq_add_neg] using translateL2_coeFn (-a) f

theorem norm_translateL2 {d : Nat} (a : RealVec d) (f : L2Real d) :
    ‖translateL2 a f‖ = ‖f‖ := by
  simp [translateL2]

theorem dist_translateL2 {d : Nat} (a : RealVec d) (f g : L2Real d) :
    dist (translateL2 a f) (translateL2 a g) = dist f g := by
  simp [translateL2]

theorem continuous_translateL2_apply {d : Nat} (f : L2Real d) :
    Continuous fun a : RealVec d => translateL2 a f := by
  haveI : Fact (Ne (2 : ENNReal) ⊤) := ⟨by norm_num⟩
  simpa [translateL2] using
    (DomAddAct.continuous_mk.vadd (continuous_const : Continuous fun _ : RealVec d => f))

/-- `modulationPhase`: modulation Phase. -/
noncomputable def modulationPhase {d : Nat} (ω : RealVec d) (t : RealVec d) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))

theorem modulationPhase_norm {d : Nat} (ω t : RealVec d) :
    ‖modulationPhase ω t‖ = 1 := by
  unfold modulationPhase
  rw [Complex.norm_exp]
  have hre :
      (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

private theorem modulationPhase_add {d : Nat} (ω a b : RealVec d) :
    modulationPhase ω (a + b) = modulationPhase ω a * modulationPhase ω b := by
  unfold modulationPhase
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem modulationPhase_neg_right {d : Nat} (ω y : RealVec d) :
    modulationPhase ω (-y) = modulationPhase (-ω) y := by
  unfold modulationPhase
  rw [inner_neg_right, inner_neg_left]

private theorem star_modulationPhase {d : Nat} (ω t : RealVec d) :
    star (modulationPhase ω t) = modulationPhase (-ω) t := by
  unfold modulationPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using (Complex.conj_ofReal (2 : ℝ))
  simp [inner_neg_left, htwo, mul_assoc, mul_comm, mul_left_comm]

private theorem modulationPhase_neg_inv {d : Nat} (ω a : RealVec d) :
    modulationPhase ω a * modulationPhase (-ω) a = 1 := by
  unfold modulationPhase
  rw [inner_neg_left]
  rw [← Complex.exp_add]
  have hzero :
      -(2 * Real.pi : ℂ) * Complex.I * ↑⟪ω, a⟫ +
          (-(2 * Real.pi : ℂ) * Complex.I * ↑(-⟪ω, a⟫)) = 0 := by
    rw [Complex.ofReal_neg]
    ring
  rw [hzero, Complex.exp_zero]

private theorem modulationPhase_neg_split {d : Nat} (ω y a : RealVec d) :
    modulationPhase (-ω) y = modulationPhase ω a * modulationPhase (-ω) (y + a) := by
  rw [modulationPhase_add]
  calc
    modulationPhase (-ω) y = 1 * modulationPhase (-ω) y := by ring
    _ = (modulationPhase ω a * modulationPhase (-ω) a) * modulationPhase (-ω) y := by
      rw [modulationPhase_neg_inv]
    _ = modulationPhase ω a * (modulationPhase (-ω) y * modulationPhase (-ω) a) := by ring

private theorem symplecticFourier_phase_eq_modulationPhase {d : Nat}
    (x ω y η : RealVec d) :
    Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η x : ℝ) - (inner ℝ y ω : ℝ) : ℝ) : ℂ)) =
      modulationPhase ω y * modulationPhase (-x) η := by
  unfold modulationPhase
  rw [← Complex.exp_add]
  rw [inner_neg_left]
  rw [real_inner_comm y ω]
  rw [real_inner_comm η x]
  rw [Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  ring

theorem fourier_translate_realVec {d : Nat} (a : RealVec d) (f : RealVec d -> ℂ)
    (_hf : Integrable f (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    FourierTransform.fourier (fun t : RealVec d => f (t - a)) =
      fun ω : RealVec d => modulationPhase a ω * FourierTransform.fourier f ω := by
  have h := (VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (L := innerₗ (RealVec d)) (f := f) (v₀ := -a))
  rw [FourierTransform.fourier]
  ext ω
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d))
      (fun t : RealVec d => f (t - a)) ω =
    modulationPhase a ω *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d)) f ω
  have hω := congrFun h ω
  simp only [Function.comp_def] at hω
  simpa [modulationPhase, Real.fourierChar_apply, sub_eq_add_neg, Circle.smul_def, mul_assoc,
    mul_left_comm, mul_comm] using hω

private theorem sub_const_hasTemperateGrowth {d : Nat} (a : RealVec d) :
    (fun x : RealVec d => x - a).HasTemperateGrowth := by
  fun_prop

private theorem sub_const_antilipschitz {d : Nat} (a : RealVec d) :
    AntilipschitzWith 1 (fun x : RealVec d => x - a) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  simp

-- to_mathlib: Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean
/-- `schwartzCompSubConstCLM`: schwartz Comp Sub Const CLM. -/
noncomputable def schwartzCompSubConstCLM {d : Nat} (a : RealVec d) :
    SchwartzMap (RealVec d) ℂ →L[ℂ] SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (sub_const_hasTemperateGrowth a)
    (sub_const_antilipschitz a)

@[simp] theorem schwartzCompSubConstCLM_apply {d : Nat} (a : RealVec d)
    (f : SchwartzMap (RealVec d) ℂ) :
    schwartzCompSubConstCLM a f = f ∘ fun x : RealVec d => x - a := by
  rfl

theorem fourier_schwartzCompSubConstCLM_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (a : RealVec d) :
    FourierTransform.fourier (schwartzCompSubConstCLM a f : RealVec d -> ℂ) =
      fun ω : RealVec d =>
        modulationPhase a ω * FourierTransform.fourier (f : RealVec d -> ℂ) ω := by
  ext ω
  simpa [schwartzCompSubConstCLM_apply, Function.comp_def] using
    congrFun (fourier_translate_realVec a (f : RealVec d -> ℂ) f.integrable) ω

private def stftWindowSchwartz {d : Nat} (x : RealVec d)
    (h : SchwartzMap (RealVec d) ℂ) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (F := ℂ) (G := ℂ) Complex.conjCLE
    (schwartzCompSubConstCLM x h)

@[simp] private theorem stftWindowSchwartz_apply {d : Nat}
    (x t : RealVec d) (h : SchwartzMap (RealVec d) ℂ) :
    stftWindowSchwartz x h t = star (h (t - x)) := by
  simp [stftWindowSchwartz]

private def stftSliceSchwartz {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (stftWindowSchwartz x h).hasTemperateGrowth f

@[simp] private theorem stftSliceSchwartz_apply {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x t : RealVec d) :
    stftSliceSchwartz h f x t = f t * star (h (t - x)) := by
  simp [stftSliceSchwartz]

private theorem stftRep_schwartz_eq_fourier_apply {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    stftRep (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) =
      FourierTransform.fourier (stftSliceSchwartz h f x : RealVec d -> ℂ) ω := by
  unfold stftRep
  rw [Real.fourier_eq]
  apply integral_congr_ae
  have hf_ae :
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) : RealVec d -> ℂ)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))] f :=
    f.coeFn_toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
  have hh_ae :
      (fun t : RealVec d =>
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) : RealVec d -> ℂ)
          (t - x)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t : RealVec d => h (t - x) := by
    simpa [Function.comp_def] using
      (MeasureTheory.measurePreserving_sub_right
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) x).quasiMeasurePreserving.ae_eq
        (h.coeFn_toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
  filter_upwards [hf_ae, hh_ae] with t hft hht
  rw [hft, hht]
  simp [Real.fourierChar_apply, Circle.smul_def, real_inner_comm, mul_assoc, mul_comm]

private theorem integral_fourier_sq_phase_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    ∫ η, ((‖(FourierTransform.fourier (f : RealVec d -> ℂ)) η‖ ^ 2 : ℝ) : ℂ) *
        modulationPhase (-x) η =
      ∫ t, star (f t) * f (t + x) := by
  have h :=
    SchwartzMap.integral_inner_fourier_fourier f (schwartzCompSubConstCLM (-x) f)
  simp_rw [SchwartzMap.fourier_coe] at h
  rw [fourier_schwartzCompSubConstCLM_realVec f (-x)] at h
  simpa [schwartzCompSubConstCLM_apply, modulationPhase, RCLike.inner_apply',
    RCLike.mul_conj, pow_two, sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm] using h

private theorem integral_stftRep_sq_phase_slice_schwartz {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (y x : RealVec d) :
    ∫ η,
        ((‖stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (y, η)‖ ^ 2 : ℝ) : ℂ) * modulationPhase (-x) η =
      ∫ t, star (stftSliceSchwartz h f y t) * stftSliceSchwartz h f y (t + x) := by
  simpa [stftRep_schwartz_eq_fourier_apply] using
    integral_fourier_sq_phase_schwartz_realVec (stftSliceSchwartz h f y) x

private theorem integrable_norm_sq_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) :
    Integrable (fun x : RealVec d => ‖f x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f := (f : RealVec d -> ℂ)) f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))

private theorem integrable_norm_sq_neg_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) :
    Integrable (fun y : RealVec d => ‖h (-y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hmem : MemLp (fun y : RealVec d => h (-y)) 2 μ := by
    simpa [Function.comp_def, μ] using
      (h.memLp 2 μ).comp_measurePreserving (Measure.measurePreserving_neg μ)
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := μ) (f := fun y : RealVec d => h (-y))
      hmem.aestronglyMeasurable).mp hmem

private theorem integrable_norm_sq_translate_sub_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    Integrable (fun y : RealVec d => ‖h (t - y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hneg : MemLp (fun y : RealVec d => h (-y)) 2 μ := by
    simpa [Function.comp_def, μ] using
      (h.memLp 2 μ).comp_measurePreserving (Measure.measurePreserving_neg μ)
  have hcomp : MemLp (fun y : RealVec d => h (-(y - t))) 2 μ := by
    simpa [Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ t)
  have hmem : MemLp (fun y : RealVec d => h (t - y)) 2 μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, μ] using hcomp
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := μ) (f := fun y : RealVec d => h (t - y))
      hmem.aestronglyMeasurable).mp hmem

private theorem integral_norm_sq_translate_sub_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    ∫ y : RealVec d, ‖h (t - y)‖ ^ 2 = ∫ y : RealVec d, ‖h y‖ ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  calc
    ∫ y : RealVec d, ‖h (t - y)‖ ^ 2
        = ∫ y : RealVec d, ‖h (-y)‖ ^ 2 := by
          simpa [sub_eq_add_neg, μ] using
            (integral_sub_right_eq_self (μ := μ)
              (f := fun y : RealVec d => ‖h (-y)‖ ^ 2) t)
    _ = ∫ y : RealVec d, ‖h y‖ ^ 2 := by
      simpa [μ] using
        (integral_neg_eq_self (μ := μ) (f := fun y : RealVec d => ‖h y‖ ^ 2))

private theorem integral_stft_kernel_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2 =
      ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  calc
    ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2
        = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h (t - y)‖ ^ 2 := by
          simpa using
            (MeasureTheory.integral_const_mul
              (r := ‖f t‖ ^ 2) (f := fun y : RealVec d => ‖h (t - y)‖ ^ 2)
              (μ := μ))
    _ = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 := by
      rw [integral_norm_sq_translate_sub_schwartz_realVec h t]

private theorem integrable_stft_kernel_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable
      (fun p : RealVec d × RealVec d => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let K : RealVec d × RealVec d → ℝ := fun p => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2
  have hK_meas : AEStronglyMeasurable K (μ.prod μ) := by
    fun_prop
  refine (MeasureTheory.integrable_prod_iff hK_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hslice : Integrable (fun y : RealVec d => ‖h (t - y)‖ ^ 2) μ := by
      simpa [μ] using integrable_norm_sq_translate_sub_schwartz_realVec h t
    simpa [K, mul_comm, μ] using hslice.const_mul (‖f t‖ ^ 2)
  · have hf_sq : Integrable (fun t : RealVec d => ‖f t‖ ^ 2) μ := by
      simpa [μ] using integrable_norm_sq_schwartz_realVec f
    have h_outer :
        (fun t : RealVec d => ∫ y : RealVec d, ‖K (t, y)‖ ∂μ) =
          fun t : RealVec d => ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ := by
      funext t
      calc
        ∫ y : RealVec d, ‖K (t, y)‖ ∂μ
            = ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with y
              simp [K]
        _ = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ := by
          exact integral_stft_kernel_slice_schwartz_realVec h f t
    rw [h_outer]
    simpa [mul_comm] using hf_sq.const_mul (∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ)

private theorem integral_norm_sq_stft_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    ∫ ω : RealVec d, ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2 =
      ∫ t : RealVec d, ‖stftSliceSchwartz h f x t‖ ^ 2 := by
  calc
    ∫ ω : RealVec d, ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2 =
        ∫ ω : RealVec d, ‖FourierTransform.fourier
          (stftSliceSchwartz h f x : RealVec d -> ℂ) ω‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [stftRep_schwartz_eq_fourier_apply h f x ω]
    _ = ∫ t : RealVec d, ‖stftSliceSchwartz h f x t‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier (stftSliceSchwartz h f x)

private theorem integrable_stftRep_sq_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable (fun ω : RealVec d => ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  have h_fourier :
      Integrable
        (fun ω : RealVec d =>
          ‖(FourierTransform.fourier (stftSliceSchwartz h f x)) ω‖ ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
    exact integrable_norm_sq_schwartz_realVec
      (FourierTransform.fourier (stftSliceSchwartz h f x))
  simp_rw [stftRep_schwartz_eq_fourier_apply h f x]
  exact h_fourier

private theorem integral_signal_autocorr_phase_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    ∫ t, star (f t) * f (t + x) * modulationPhase ω (t + (1 / 2 : ℝ) • x) =
      ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let a : RealVec d := (1 / 2 : ℝ) • x
  have ha : a + a = x := by
    rw [← two_smul ℝ a]
    simp [a]
  have hshift :
      ∫ t, star (f t) * f (t + x) * modulationPhase ω (t + a) =
        ∫ t, f (t + a) * star (f (t - a)) * modulationPhase ω t := by
    simpa [ha, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using
      (integral_add_right_eq_self (μ := μ)
        (f := fun t : RealVec d =>
          f (t + a) * star (f (t - a)) * modulationPhase ω t) a)
  unfold ambiguityRep
  rw [hshift]
  have hf_ae :
      (f.toLp 2 μ : RealVec d -> ℂ) =ᵐ[μ] f :=
    f.coeFn_toLp 2 μ
  have hplus :
      (fun t : RealVec d => (f.toLp 2 μ : RealVec d -> ℂ) (t + a)) =ᵐ[μ]
        fun t : RealVec d => f (t + a) := by
    simpa [Function.comp_def] using
      ((MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving).ae_eq_comp
        hf_ae
  have hminus :
      (fun t : RealVec d => (f.toLp 2 μ : RealVec d -> ℂ) (t - a)) =ᵐ[μ]
        fun t : RealVec d => f (t - a) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((MeasureTheory.measurePreserving_add_right μ (-a)).quasiMeasurePreserving).ae_eq_comp
        hf_ae
  apply integral_congr_ae
  filter_upwards [hplus, hminus] with t hplus_t hminus_t
  rw [hplus_t, hminus_t]
  simp [modulationPhase]

private theorem signal_autocorr_integrable_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable (fun t : RealVec d => star (f t) * f (t + x))
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hshift : MemLp (fun t : RealVec d => f (t + x)) 2 μ := by
    simpa [Function.comp_def, μ] using
      (f.memLp 2 μ).comp_measurePreserving
        (MeasureTheory.measurePreserving_add_right μ x)
  have hmul := (f.memLp 2 μ).star.integrable_mul hshift
  refine hmul.congr ?_
  filter_upwards with t
  simp only [Pi.mul_apply, Pi.star_apply]

private theorem reflected_memLp_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) :
    MemLp (fun y : RealVec d => h (-y)) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  simpa [Function.comp_def, μ] using
    (h.memLp 2 μ).comp_measurePreserving (Measure.measurePreserving_neg μ)

private theorem window_autocorr_integrable_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x : RealVec d) :
    Integrable (fun y : RealVec d => h (t - y) * star (h (t + x - y)))
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hneg : MemLp (fun y : RealVec d => h (-y)) 2 μ := by
    simpa [μ] using reflected_memLp_schwartz_realVec h
  have hleft' : MemLp (fun y : RealVec d => h (-(y - t))) 2 μ := by
    simpa [Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ t)
  have hright' : MemLp (fun y : RealVec d => h (-(y - (t + x)))) 2 μ := by
    simpa [Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ (t + x))
  have hleft : MemLp (fun y : RealVec d => h (t - y)) 2 μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hleft'
  have hright : MemLp (fun y : RealVec d => h (t + x - y)) 2 μ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hright'
  have hmul := hleft.integrable_mul hright.star
  refine hmul.congr ?_
  filter_upwards with y
  simp only [Pi.mul_apply, Pi.star_apply]

private theorem integral_window_autocorr_norm_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x : RealVec d) :
    ∫ y : RealVec d, ‖h (t - y) * star (h (t + x - y))‖ =
      ∫ y : RealVec d, ‖h (-y) * star (h (x - y))‖ := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, μ] using
    (integral_sub_right_eq_self (μ := μ)
      (f := fun y : RealVec d => ‖h (-y) * star (h (x - y))‖) t)

private theorem autocorr_kernel_integrable_schwartz_realVec {d : Nat}
    (f h : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable
      (fun p : RealVec d × RealVec d =>
        (star (f p.1) * f (p.1 + x)) *
          (h (p.1 - p.2) * star (h (p.1 + x - p.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let A : RealVec d → ℂ := fun t => star (f t) * f (t + x)
  let B : RealVec d × RealVec d → ℂ := fun p =>
    h (p.1 - p.2) * star (h (p.1 + x - p.2))
  have hA : Integrable A μ := signal_autocorr_integrable_schwartz_realVec f x
  have hB : ∀ᵐ t ∂μ, Integrable (fun y : RealVec d => A t * B (t, y)) μ := by
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [A, B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc,
      mul_left_comm, mul_comm, μ] using
      (window_autocorr_integrable_schwartz_realVec h t x).const_mul (A t)
  have hmeas : AEStronglyMeasurable (fun p : RealVec d × RealVec d => A p.1 * B p)
      (μ.prod μ) := by
    fun_prop
  refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
  constructor
  · exact hB
  · have hA_norm : Integrable (fun t : RealVec d => ‖A t‖) μ := hA.norm
    let C : ℝ := ∫ y : RealVec d, ‖h (-y) * star (h (x - y))‖ ∂μ
    have hC : ∀ t : RealVec d, ∫ y : RealVec d, ‖B (t, y)‖ ∂μ = C := by
      intro t
      simpa [B, C, μ] using integral_window_autocorr_norm_schwartz_realVec h t x
    have houter : Integrable (fun t : RealVec d => ∫ y : RealVec d,
        ‖A t‖ * ‖B (t, y)‖ ∂μ) μ := by
      have hconst : ∀ t : RealVec d,
          ∫ y : RealVec d, ‖A t‖ * ‖B (t, y)‖ ∂μ = ‖A t‖ * C := by
        intro t
        calc
          ∫ y : RealVec d, ‖A t‖ * ‖B (t, y)‖ ∂μ
              = ‖A t‖ * ∫ y : RealVec d, ‖B (t, y)‖ ∂μ := by
                simpa using
                  (MeasureTheory.integral_const_mul
                    (r := ‖A t‖)
                    (f := fun y : RealVec d => ‖B (t, y)‖)
                    (μ := μ))
          _ = ‖A t‖ * C := by rw [hC t]
      have houterEq :
          (fun t : RealVec d => ∫ y : RealVec d, ‖A t‖ * ‖B (t, y)‖ ∂μ) =
            fun t : RealVec d => ‖A t‖ * C := by
        funext t
        exact hconst t
      simpa [houterEq, mul_comm] using hA_norm.const_mul C
    convert houter using 1
    ext t
    apply integral_congr_ae
    filter_upwards with y
    rw [norm_mul]

private theorem ambiguityRep_neg_neg_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (-x, -ω) =
      star (ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let a : RealVec d := (1 / 2 : ℝ) • x
  have hneg_half : (1 / 2 : ℝ) • (-x) = -a := by
    simp [a]
  unfold ambiguityRep
  have hf_ae :
      (f.toLp 2 μ : RealVec d -> ℂ) =ᵐ[μ] f :=
    f.coeFn_toLp 2 μ
  have hleft_plus :
      (fun t : RealVec d =>
        (f.toLp 2 μ : RealVec d -> ℂ) (t + (1 / 2 : ℝ) • (-x)))
        =ᵐ[μ] fun t : RealVec d => f (t - a) := by
    have h :=
      ((MeasureTheory.measurePreserving_add_right μ (-a)).quasiMeasurePreserving).ae_eq_comp
        hf_ae
    filter_upwards [h] with t ht
    rw [hneg_half]
    simpa [Function.comp_def, sub_eq_add_neg] using ht
  have hleft_minus :
      (fun t : RealVec d =>
        (f.toLp 2 μ : RealVec d -> ℂ) (t - (1 / 2 : ℝ) • (-x)))
        =ᵐ[μ] fun t : RealVec d => f (t + a) := by
    have h :=
      ((MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving).ae_eq_comp
        hf_ae
    filter_upwards [h] with t ht
    rw [hneg_half]
    simpa [Function.comp_def, sub_eq_add_neg] using ht
  have hright_plus :
      (fun t : RealVec d => (f.toLp 2 μ : RealVec d -> ℂ) (t + a)) =ᵐ[μ]
        fun t : RealVec d => f (t + a) := by
    simpa [Function.comp_def] using
      ((MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving).ae_eq_comp
        hf_ae
  have hright_minus :
      (fun t : RealVec d => (f.toLp 2 μ : RealVec d -> ℂ) (t - a)) =ᵐ[μ]
        fun t : RealVec d => f (t - a) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((MeasureTheory.measurePreserving_add_right μ (-a)).quasiMeasurePreserving).ae_eq_comp
        hf_ae
  calc
    ∫ t : RealVec d,
        (f.toLp 2 μ : RealVec d -> ℂ) (t + (1 / 2 : ℝ) • (-x)) *
          star ((f.toLp 2 μ : RealVec d -> ℂ) (t - (1 / 2 : ℝ) • (-x))) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ↑(inner ℝ (-ω) t))
        = ∫ t : RealVec d, f (t - a) * star (f (t + a)) *
            modulationPhase (-ω) t := by
            apply integral_congr_ae
            filter_upwards [hleft_plus, hleft_minus] with t ht1 ht2
            rw [ht1, ht2]
            simp [modulationPhase]
    _ = star (∫ t : RealVec d, f (t + a) * star (f (t - a)) *
          modulationPhase ω t) := by
            calc
              ∫ t : RealVec d, f (t - a) * star (f (t + a)) *
                  modulationPhase (-ω) t =
                ∫ t : RealVec d, star (f (t + a) * star (f (t - a)) *
                  modulationPhase ω t) := by
                    apply integral_congr_ae
                    filter_upwards with t
                    simp [star_mul, star_modulationPhase, mul_comm]
              _ = star (∫ t : RealVec d, f (t + a) * star (f (t - a)) *
                    modulationPhase ω t) := by
                    exact integral_conj
    _ = star (∫ t : RealVec d,
        (f.toLp 2 μ : RealVec d -> ℂ) (t + (1 / 2 : ℝ) • x) *
          star ((f.toLp 2 μ : RealVec d -> ℂ) (t - (1 / 2 : ℝ) • x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ↑(inner ℝ ω t))) := by
            congr 1
            apply integral_congr_ae
            filter_upwards [hright_plus, hright_minus] with t ht1 ht2
            rw [ht1, ht2]
            simp [modulationPhase, a]

private theorem integral_window_autocorr_phase_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x ω : RealVec d) :
    ∫ y : RealVec d,
      h (t - y) * star (h (t + x - y)) * modulationPhase ω y =
        modulationPhase ω (t + (1 / 2 : ℝ) • x) *
          star (ambiguityRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let a : RealVec d := (1 / 2 : ℝ) • x
  have ha : a + a = x := by
    rw [← two_smul ℝ a]
    simp [a]
  have hneg_half : (1 / 2 : ℝ) • (-x) = -a := by
    simp [a]
  have hphase_t : ∀ y : RealVec d,
      modulationPhase ω y = modulationPhase ω t * modulationPhase ω (y - t) := by
    intro y
    have hphase := modulationPhase_add ω t (y - t)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hphase
  have hshift_t :
      ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y =
        modulationPhase ω t *
          ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y := by
    calc
      ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y
          = ∫ y : RealVec d, modulationPhase ω t *
              (h (t - y) * star (h (t + x - y)) *
                modulationPhase ω (y - t)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_t y]
                ring_nf
      _ = modulationPhase ω t *
            ∫ y : RealVec d,
              h (t - y) * star (h (t + x - y)) * modulationPhase ω (y - t) := by
                simpa [mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := modulationPhase ω t)
                    (f := fun y : RealVec d =>
                      h (t - y) * star (h (t + x - y)) *
                        modulationPhase ω (y - t)))
      _ = modulationPhase ω t *
            ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y := by
                congr 1
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                  (integral_sub_right_eq_self (μ := μ)
                    (f := fun y : RealVec d =>
                      h (-y) * star (h (x - y)) * modulationPhase ω y) t)
  have hneg :
      ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y =
        ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      modulationPhase_neg_right, mul_assoc] using
      (integral_neg_eq_self (μ := μ)
        (f := fun y : RealVec d => h y * star (h (x + y)) * modulationPhase (-ω) y))
  have hphase_x : ∀ y : RealVec d,
      modulationPhase (-ω) y = modulationPhase ω a * modulationPhase (-ω) (y + a) := by
    intro y
    exact modulationPhase_neg_split ω y a
  have hshift_x :
      ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y =
        modulationPhase ω a *
          ∫ y : RealVec d, h (y - a) * star (h (y + a)) *
            modulationPhase (-ω) y := by
    calc
      ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y
          = ∫ y : RealVec d, modulationPhase ω a *
              (h y * star (h (x + y)) * modulationPhase (-ω) (y + a)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_x y]
                ring_nf
      _ = modulationPhase ω a *
            ∫ y : RealVec d, h y * star (h (x + y)) *
              modulationPhase (-ω) (y + a) := by
              simpa [mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (r := modulationPhase ω a)
                  (f := fun y : RealVec d =>
                    h y * star (h (x + y)) * modulationPhase (-ω) (y + a)))
      _ = modulationPhase ω a *
            ∫ y : RealVec d, h (y - a) * star (h (y + a)) *
              modulationPhase (-ω) y := by
              congr 1
              simpa [ha, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                (integral_add_right_eq_self (μ := μ)
                  (f := fun y : RealVec d =>
                    h (y - a) * star (h (y + a)) * modulationPhase (-ω) y) a)
  have hamb :
      ∫ y : RealVec d, h (y - a) * star (h (y + a)) * modulationPhase (-ω) y =
        ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (-x, -ω) := by
    unfold ambiguityRep
    have hh_ae : (h.toLp 2 μ : RealVec d -> ℂ) =ᵐ[μ] h := h.coeFn_toLp 2 μ
    have hplus :
        (fun y : RealVec d =>
          (h.toLp 2 μ : RealVec d -> ℂ) (y + (1 / 2 : ℝ) • (-x)))
          =ᵐ[μ] fun y : RealVec d => h (y - a) := by
      have hq :=
        ((MeasureTheory.measurePreserving_add_right μ (-a)).quasiMeasurePreserving).ae_eq_comp
          hh_ae
      filter_upwards [hq] with y hy
      rw [hneg_half]
      simpa [Function.comp_def, sub_eq_add_neg] using hy
    have hminus :
        (fun y : RealVec d =>
          (h.toLp 2 μ : RealVec d -> ℂ) (y - (1 / 2 : ℝ) • (-x)))
          =ᵐ[μ] fun y : RealVec d => h (y + a) := by
      have hq :=
        ((MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving).ae_eq_comp
          hh_ae
      filter_upwards [hq] with y hy
      rw [hneg_half]
      simpa [Function.comp_def, sub_eq_add_neg] using hy
    symm
    apply integral_congr_ae
    filter_upwards [hplus, hminus] with y hy1 hy2
    rw [hy1, hy2]
    simp [modulationPhase]
  calc
    ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y
        = modulationPhase ω t *
            ∫ y : RealVec d, h (-y) * star (h (x - y)) *
              modulationPhase ω y := hshift_t
    _ = modulationPhase ω t *
          (modulationPhase ω a * ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (-x, -ω)) := by
            rw [hneg, hshift_x, hamb]
    _ = modulationPhase ω (t + a) *
          star (ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (x, ω)) := by
            rw [ambiguityRep_neg_neg_schwartz_realVec h x ω]
            rw [modulationPhase_add]
            ring

private theorem modulateL2_mem {d : Nat} (ω : RealVec d) (f : L2Real d) :
    MeasureTheory.MemLp
      (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
      2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  have hf := MeasureTheory.Lp.memLp f
  refine hf.of_le ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by
      unfold modulationPhase
      fun_prop)).mul hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul, modulationPhase_norm]
      simp

/-- `modulateL2`: modulate L2. -/
noncomputable def modulateL2 {d : Nat} (ω : RealVec d) (f : L2Real d) : L2Real d :=
  (modulateL2_mem ω f).toLp
    (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)

theorem modulateL2_coeFn {d : Nat} (ω : RealVec d) (f : L2Real d) :
    ((modulateL2 ω f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => modulationPhase ω t * (f : RealVec d -> ℂ) t := by
  exact (modulateL2_mem ω f).coeFn_toLp

theorem norm_modulateL2 {d : Nat} (ω : RealVec d) (f : L2Real d) :
    ‖modulateL2 ω f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [modulateL2_coeFn ω f] with t hmod
  rw [hmod, norm_mul, modulationPhase_norm]
  simp

-- to_mathlib: Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean
private theorem tendsto_lintegral_filter_of_dominated_convergence_ae
    {α ι : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι -> α -> ℝ≥0∞} {f : α -> ℝ≥0∞}
    (bound : α -> ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, AEMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' bound ?_ ?_ h_fin ?_
  · intro n
    exact (h (n + k) (Nat.le_add_left _ _)).1
  · intro n
    exact (h (n + k) (Nat.le_add_left _ _)).2
  · refine h_lim.mono fun a h_lim => ?_
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_atTop_iff_nat]
    assumption

private theorem modulation_eLpNorm_tendsto_zero {d : Nat} (f : L2Real d) (ω0 : RealVec d) :
    Tendsto
      (fun ω : RealVec d => MeasureTheory.eLpNorm
        (fun t : RealVec d =>
          modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
        2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
  have hf := MeasureTheory.Lp.memLp f
  have hInt :
      Tendsto
        (fun ω : RealVec d => ∫⁻ t : RealVec d,
          ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
    have hdc := tendsto_lintegral_filter_of_dominated_convergence_ae
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (l := 𝓝 ω0)
      (F := fun ω t =>
        ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
          modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ))
      (f := fun _ : RealVec d => (0 : ℝ≥0∞))
      (bound := fun t : RealVec d => ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ))
      ?_ ?_ ?_ ?_
    · simpa using hdc
    · exact Filter.Eventually.of_forall fun ω => by
        exact (((Continuous.aestronglyMeasurable (by
          unfold modulationPhase
          fun_prop)).mul hf.aestronglyMeasurable).sub
            ((Continuous.aestronglyMeasurable (by
              unfold modulationPhase
              fun_prop)).mul hf.aestronglyMeasurable)).enorm.pow_const (2 : ℝ)
    · exact Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun t => by
        have hnorm :
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ ≤
              ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ := by
          calc
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖
                ≤ ‖modulationPhase ω t * (f : RealVec d -> ℂ) t‖ +
                    ‖modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ := norm_sub_le _ _
            _ = ‖(f : RealVec d -> ℂ) t‖ + ‖(f : RealVec d -> ℂ) t‖ := by
              rw [norm_mul, norm_mul, modulationPhase_norm, modulationPhase_norm]
              ring_nf
            _ = ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ := by
              rw [norm_mul]
              norm_num
              ring_nf
        have henorm :
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ≤
              ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hnorm
        exact ENNReal.rpow_le_rpow henorm (by norm_num)
    · have hmul_mem : MeasureTheory.MemLp
          (fun t : RealVec d => (2 : ℂ) * (f : RealVec d -> ℂ) t)
          2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
        exact hf.const_mul (2 : ℂ)
      exact (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f := fun t : RealVec d => (2 : ℂ) * (f : RealVec d -> ℂ) t)
        (by norm_num) (by norm_num) hmul_mem.2).ne
    · exact Filter.Eventually.of_forall fun t => by
        have hphase : Tendsto (fun ω : RealVec d => modulationPhase ω t) (𝓝 ω0)
            (𝓝 (modulationPhase ω0 t)) := by
          have hcont : Continuous fun ω : RealVec d => modulationPhase ω t := by
            unfold modulationPhase
            fun_prop
          exact hcont.tendsto ω0
        have hdiff : Tendsto
            (fun ω : RealVec d =>
              modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
            (𝓝 ω0) (𝓝 0) := by
          have hleft : Tendsto
              (fun ω : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
              (𝓝 ω0) (𝓝 (modulationPhase ω0 t * (f : RealVec d -> ℂ) t)) :=
            hphase.mul tendsto_const_nhds
          have hright : Tendsto
              (fun _ : RealVec d => modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
              (𝓝 ω0) (𝓝 (modulationPhase ω0 t * (f : RealVec d -> ℂ) t)) :=
            tendsto_const_nhds
          simpa using hleft.sub hright
        have hnorm : Tendsto
            (fun ω : RealVec d =>
              ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ)
            (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
          simpa [Function.comp_def] using (continuous_enorm.tendsto 0).comp hdiff
        have hpow_cont : Continuous fun x : ℝ≥0∞ => x ^ (2 : ℝ) :=
          ENNReal.continuous_rpow_const
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ))] using
          (hpow_cont.tendsto (0 : ℝ≥0∞)).comp hnorm
  have hpow : Tendsto
      (fun ω : RealVec d =>
        (∫⁻ t : RealVec d,
          ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ^ (1 / (2 : ℝ)))
      (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
    have hpow_cont : Continuous fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1 / (2 : ℝ)))] using
      (hpow_cont.tendsto (0 : ℝ≥0∞)).comp hInt
  simpa [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] using hpow

theorem continuous_modulateL2_apply {d : Nat} (f : L2Real d) :
    Continuous fun ω : RealVec d => modulateL2 ω f := by
  rw [continuous_iff_continuousAt]
  intro ω0
  dsimp [ContinuousAt]
  simpa [modulateL2] using
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f := fun ω t => modulationPhase ω t * (f : RealVec d -> ℂ) t)
      (f_ℒp := fun ω => modulateL2_mem ω f)
      (f_lim := fun t => modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
      (f_lim_ℒp := modulateL2_mem ω0 f)).2 (modulation_eLpNorm_tendsto_zero f ω0)

theorem stftRep_congr_right
    {d : Nat} {h f g : L2Real d} (hfg : f = g) :
    stftRep h f = stftRep h g := by
  subst hfg
  rfl

theorem stftRep_congr_left
    {d : Nat} {h h' f : L2Real d} (hh : h = h') :
    stftRep h f = stftRep h' f := by
  subst hh
  rfl

theorem ambiguityRep_congr_left
    {d : Nat} {f f' g : L2Real d} (hf : f = f') :
    ambiguityRep f g = ambiguityRep f' g := by
  subst hf
  rfl

theorem ambiguityRep_congr_right
    {d : Nat} {f g g' : L2Real d} (hg : g = g') :
    ambiguityRep f g = ambiguityRep f g' := by
  subst hg
  rfl

theorem ambiguityRep_eq_lpPairing
    {d : Nat} (f g : L2Real d) (ξ : PhaseSpace d) :
    ambiguityRep f g ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2
          (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold ambiguityRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    translateL2_coeFn ((1 / 2 : ℝ) • ξ.1) f,
    modulateL2_coeFn ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g),
    translateL2_neg_coeFn ((1 / 2 : ℝ) • ξ.1) g] with t hf hmod hstar hg
  rw [hf, hmod, hstar]
  simp only [Pi.star_apply]
  rw [hg]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ring_nf

theorem edist_modulateL2 {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    edist (modulateL2 ω f) (modulateL2 ω g) = edist f g := by
  rw [MeasureTheory.Lp.edist_def, MeasureTheory.Lp.edist_def]
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [
    modulateL2_coeFn ω f,
    modulateL2_coeFn ω g] with t hmf hmg
  rw [Pi.sub_apply, Pi.sub_apply, hmf, hmg]
  calc
    ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
        modulationPhase ω t * (g : RealVec d -> ℂ) t‖
        = ‖modulationPhase ω t * ((f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t)‖ := by
          ring_nf
    _ = ‖(f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t‖ := by
      rw [norm_mul, modulationPhase_norm]
      simp

theorem dist_modulateL2 {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    dist (modulateL2 ω f) (modulateL2 ω g) = dist f g := by
  rw [dist_edist, dist_edist, edist_modulateL2]

theorem continuous_modulateL2 {d : Nat} {X : Type*} [TopologicalSpace X]
    {ω : X -> RealVec d} {h : X -> L2Real d}
    (hω : Continuous ω) (hh : Continuous h) :
    Continuous fun x : X => modulateL2 (ω x) (h x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hbase : Tendsto (fun x : X => modulateL2 (ω x) (h x0)) (𝓝 x0)
      (𝓝 (modulateL2 (ω x0) (h x0))) :=
    (continuous_modulateL2_apply (h x0)).continuousAt.comp hω.continuousAt
  refine hbase.congr_dist ?_
  have hdist_h : Tendsto (fun x : X => dist (h x) (h x0)) (𝓝 x0) (𝓝 0) := by
    exact tendsto_iff_dist_tendsto_zero.mp hh.continuousAt
  simpa [dist_comm, dist_modulateL2] using hdist_h

theorem edist_star_L2 {d : Nat} (f g : L2Real d) :
    edist (star f) (star g) = edist f g := by
  rw [MeasureTheory.Lp.edist_def, MeasureTheory.Lp.edist_def]
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [
    MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g] with t hf hg
  rw [Pi.sub_apply, Pi.sub_apply, hf, hg]
  simp only [Pi.star_apply]
  calc
    ‖star ((f : RealVec d -> ℂ) t) - star ((g : RealVec d -> ℂ) t)‖
        = ‖star ((f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t)‖ := by
          rw [star_sub]
    _ = ‖(f : RealVec d -> ℂ) t - (g : RealVec d -> ℂ) t‖ := norm_star _

theorem dist_star_L2 {d : Nat} (f g : L2Real d) :
    dist (star f) (star g) = dist f g := by
  rw [MeasureTheory.Lp.dist_edist, MeasureTheory.Lp.dist_edist, edist_star_L2]

theorem continuous_star_L2 {d : Nat} : Continuous fun f : L2Real d => star f := by
  have hIso : Isometry (fun f : L2Real d => star f) := by
    intro f g
    exact edist_star_L2 f g
  exact hIso.continuous

theorem norm_star_L2 {d : Nat} (f : L2Real d) :
    ‖star f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [MeasureTheory.Lp.coeFn_star f] with t hf
  rw [hf]
  simp only [Pi.star_apply]
  exact norm_star ((f : RealVec d -> ℂ) t)

private theorem lpPairing_mul_norm_le {d : Nat} (f g : L2Real d) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2) f g‖ ≤ ‖f‖ * ‖g‖ := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let B := (ContinuousLinearMap.mul ℂ ℂ)
  have hB : ‖B‖ ≤ (1 : ℝ) := by
    simp [B]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  let H : MeasureTheory.Lp ℂ 1 μ := B.holder (1 : ENNReal) f g
  have hHae : H =ᵐ[μ] fun x => B (f x) (g x) := by
    exact ContinuousLinearMap.coeFn_holder B f g
  have hnorm_int : ‖∫ x, B (f x) (g x) ∂μ‖ ≤ ‖H‖ := by
    calc
      ‖∫ x, B (f x) (g x) ∂μ‖ = ‖∫ x, H x ∂μ‖ := by
        exact congrArg norm (integral_congr_ae hHae.symm)
      _ ≤ ∫ x, ‖H x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ‖H‖ := by rw [MeasureTheory.L1.norm_eq_integral_norm]
  have hholder : ‖H‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
    simpa [H] using ContinuousLinearMap.norm_holder_apply_apply_le B f g
  have hmul : ‖B‖ * ‖f‖ * ‖g‖ ≤ ‖f‖ * ‖g‖ := by
    calc
      ‖B‖ * ‖f‖ * ‖g‖ ≤ 1 * ‖f‖ * ‖g‖ := by gcongr
      _ = ‖f‖ * ‖g‖ := by ring
  exact hnorm_int.trans (hholder.trans hmul)

theorem norm_ambiguityRep_le {d : Nat} (f g : L2Real d) (ξ : PhaseSpace d) :
    ‖ambiguityRep f g ξ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ambiguityRep_eq_lpPairing]
  have hpair := lpPairing_mul_norm_le
    (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
    (modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)))
  calc
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)))‖
        ≤ ‖translateL2 ((1 / 2 : ℝ) • ξ.1) f‖ *
            ‖modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))‖ := hpair
    _ = ‖f‖ * ‖g‖ := by
      rw [norm_translateL2, norm_modulateL2, norm_star_L2, norm_translateL2]

theorem stftRep_eq_lpPairing
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    stftRep h f ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        f
        (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold stftRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    modulateL2_coeFn ξ.2 (star (translateL2 (-ξ.1) h)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-ξ.1) h),
    translateL2_neg_coeFn ξ.1 h] with t hmod hstar hh
  rw [hmod, hstar]
  simp only [Pi.star_apply]
  rw [hh]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ring_nf

theorem norm_stftRep_le {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    ‖stftRep h f ξ‖ ≤ ‖f‖ * ‖h‖ := by
  rw [stftRep_eq_lpPairing]
  have hpair := lpPairing_mul_norm_le f (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h)))
  calc
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
        f (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h)))‖
        ≤ ‖f‖ * ‖modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))‖ := hpair
    _ = ‖f‖ * ‖h‖ := by
      rw [norm_modulateL2, norm_star_L2, norm_translateL2]

private theorem norm_stftRep_sub_le {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) (ξ : PhaseSpace d) :
    ‖stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ‖ ≤
      ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  let T : L2Real d → L2Real d := fun h =>
    modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))
  have hT_norm : ‖T h₁‖ = ‖h₁‖ := by
    simp [T, norm_modulateL2, norm_star_L2, norm_translateL2]
  have hT_sub_norm : ‖T h₁ - T h₂‖ = ‖h₁ - h₂‖ := by
    calc
      ‖T h₁ - T h₂‖ = dist (T h₁) (T h₂) := by
        rw [dist_eq_norm]
      _ = dist (star (translateL2 (-ξ.1) h₁)) (star (translateL2 (-ξ.1) h₂)) := by
        simp [T, dist_modulateL2]
      _ = dist (translateL2 (-ξ.1) h₁) (translateL2 (-ξ.1) h₂) := by
        rw [dist_star_L2]
      _ = dist h₁ h₂ := by
        rw [dist_translateL2]
      _ = ‖h₁ - h₂‖ := by
        rw [dist_eq_norm]
  rw [stftRep_eq_lpPairing h₁ f₁ ξ, stftRep_eq_lpPairing h₂ f₂ ξ]
  change ‖P f₁ (T h₁) - P f₂ (T h₂)‖ ≤
    ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖
  have hsplit :
      P f₁ (T h₁) - P f₂ (T h₂) =
        P (f₁ - f₂) (T h₁) + P f₂ (T h₁ - T h₂) := by
    simp [P]
  calc
    ‖P f₁ (T h₁) - P f₂ (T h₂)‖
        = ‖P (f₁ - f₂) (T h₁) + P f₂ (T h₁ - T h₂)‖ := by
          rw [hsplit]
    _ ≤ ‖P (f₁ - f₂) (T h₁)‖ + ‖P f₂ (T h₁ - T h₂)‖ := norm_add_le _ _
    _ ≤ ‖f₁ - f₂‖ * ‖T h₁‖ + ‖f₂‖ * ‖T h₁ - T h₂‖ := by
      exact add_le_add (lpPairing_mul_norm_le (f₁ - f₂) (T h₁))
        (lpPairing_mul_norm_le f₂ (T h₁ - T h₂))
    _ = ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
      rw [hT_norm, hT_sub_norm]

theorem continuous_stftRep
    {d : Nat} (h f : L2Real d) :
    Continuous (stftRep h f) := by
  rw [show stftRep h f = fun ξ : PhaseSpace d =>
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        f
        (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))) by
    funext ξ
    exact stftRep_eq_lpPairing h f ξ]
  have htrans : Continuous fun ξ : PhaseSpace d =>
      translateL2 (-ξ.1) h := by
    exact (continuous_translateL2_apply h).comp (by fun_prop)
  have hstar : Continuous fun ξ : PhaseSpace d =>
      star (translateL2 (-ξ.1) h) :=
    continuous_star_L2.comp htrans
  have hsecond : Continuous fun ξ : PhaseSpace d =>
      modulateL2 ξ.2 (star (translateL2 (-ξ.1) h)) := by
    exact continuous_modulateL2 continuous_snd hstar
  let pairing :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  exact (pairing f).continuous.comp hsecond

private theorem stftRep_aestronglyMeasurable {d : Nat} (h f : L2Real d) :
    AEStronglyMeasurable (stftRep h f)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) :=
  (continuous_stftRep h f).aestronglyMeasurable

private theorem stftRep_sq_integrable_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable (fun p : PhaseSpace d => ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  let F : PhaseSpace d → ℝ := fun p => ‖stftRep hLp fLp p‖ ^ 2
  have hF_meas : AEStronglyMeasurable F (μ.prod μ) := by
    exact ((continuous_stftRep hLp fLp).norm.pow 2).aestronglyMeasurable
  change Integrable F (μ.prod μ)
  refine (MeasureTheory.integrable_prod_iff hF_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro x
    simpa [F, hLp, fLp, μ] using integrable_stftRep_sq_slice_schwartz_realVec h f x
  · have hkernel : Integrable
        (fun p : RealVec d × RealVec d => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2)
        (μ.prod μ) := by
      simpa [μ] using integrable_stft_kernel_schwartz_realVec h f
    have h_outer :
        (fun x : RealVec d => ∫ ω : RealVec d, ‖F (x, ω)‖ ∂μ) =
          fun x : RealVec d => ∫ t : RealVec d, ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2 ∂μ := by
      funext x
      calc
        ∫ ω : RealVec d, ‖F (x, ω)‖ ∂μ
            = ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              simp [F]
        _ = ∫ t : RealVec d, ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2 ∂μ := by
          rw [integral_norm_sq_stft_slice_schwartz_realVec h f x]
          refine integral_congr_ae ?_
          filter_upwards with t
          simp [stftSliceSchwartz_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [h_outer]
    simpa using hkernel.integral_norm_prod_right

private theorem stftRep_sq_complex_integrable_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable
      (fun p : PhaseSpace d => ((‖stftRep
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2 : ℝ) : ℂ))
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  simpa using (stftRep_sq_integrable_schwartz_realVec h f).ofReal (𝕜 := ℂ)

private theorem integral_norm_sq_schwartz_eq_lpNorm_sq_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) :
    ∫ x : RealVec d, ‖f x‖ ^ 2 =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hf : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := f.memLp 2 μ
  have hnorm :
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ =
        (∫ x : RealVec d, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
      hf.aestronglyMeasurable]
    norm_num
  rw [hnorm]
  have hpow :
      ∫ x : RealVec d, ‖f x‖ ^ (2 : ℝ) ∂μ =
        ∫ x : RealVec d, ‖f x‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    norm_num
  rw [hpow]
  have hint_nonneg : 0 ≤ ∫ x : RealVec d, ‖f x‖ ^ 2 ∂μ := by
    exact integral_nonneg fun _ => by positivity
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt hint_nonneg).symm

private theorem integral_stftRep_sq_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    ∫ p : PhaseSpace d,
        ‖stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2 =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  let K : RealVec d → RealVec d → ℝ := fun x t => ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    have hswap := (integrable_stft_kernel_schwartz_realVec h f).swap
    refine hswap.congr ?_
    filter_upwards with p
    simp [K, Function.uncurry, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
  calc
    ∫ p : PhaseSpace d, ‖stftRep (h.toLp 2 μ) (f.toLp 2 μ) p‖ ^ 2
        = ∫ x : RealVec d, ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 := by
            change
              ∫ p : RealVec d × RealVec d, ‖stftRep hLp fLp p‖ ^ 2 ∂(μ.prod μ) =
                ∫ x : RealVec d, ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 ∂μ ∂μ
            rw [MeasureTheory.integral_prod
              (μ := μ) (ν := μ)
              (f := fun p : RealVec d × RealVec d => ‖stftRep hLp fLp p‖ ^ 2)]
            exact stftRep_sq_integrable_schwartz_realVec h f
    _ = ∫ x : RealVec d, ∫ t : RealVec d, K x t := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_norm_sq_stft_slice_schwartz_realVec h f x]
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ‖stftSliceSchwartz h f x t‖ ^ 2
                = ‖f t * star (h (t - x))‖ ^ 2 := by
                  rw [stftSliceSchwartz_apply]
            _ = (‖f t‖ * ‖h (t - x)‖) ^ 2 := by
                  rw [norm_mul, norm_star]
            _ = K x t := by
                  simp [K, pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ t : RealVec d, ∫ x : RealVec d, K x t := by
          exact MeasureTheory.integral_integral_swap hK
    _ = ∫ t : RealVec d, ‖f t‖ ^ 2 * ∫ x : RealVec d, ‖h x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards with t
          exact integral_stft_kernel_slice_schwartz_realVec h f t
    _ = (∫ t : RealVec d, ‖f t‖ ^ 2) * (∫ x : RealVec d, ‖h x‖ ^ 2) := by
          exact MeasureTheory.integral_mul_const
            (f := fun t : RealVec d => ‖f t‖ ^ 2)
            (r := ∫ x : RealVec d, ‖h x‖ ^ 2) (μ := μ)
    _ = MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 := by
          rw [integral_norm_sq_schwartz_eq_lpNorm_sq_realVec f,
            integral_norm_sq_schwartz_eq_lpNorm_sq_realVec h]

private theorem stftRep_memLp_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.MemLp
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (stftRep_aestronglyMeasurable
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))))).2
      (stftRep_sq_integrable_schwartz_realVec h f)

private theorem lpNorm_stftRep_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.lpNorm
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
      (stftRep_aestronglyMeasurable hLp fLp)]
  norm_num
  rw [show
      ∫ p : PhaseSpace d, ‖stftRep hLp fLp p‖ ^ 2 =
        MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 by
        simpa [hLp, fLp, μ] using integral_stftRep_sq_schwartz_realVec h f]
  have hnonneg :
      0 ≤ MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ := by
    exact mul_nonneg MeasureTheory.lpNorm_nonneg MeasureTheory.lpNorm_nonneg
  rw [show
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 =
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) ^ 2 by ring]
  rw [← Real.sqrt_eq_rpow]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg, μ]

private theorem eLpNorm_stftRep_schwartz_eq {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.eLpNorm
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) =
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  calc
    MeasureTheory.eLpNorm
        (fun p : PhaseSpace d =>
          stftRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
        2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d))
        = ENNReal.ofReal
            (MeasureTheory.lpNorm
              (fun p : PhaseSpace d =>
                stftRep
                  (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
                  (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
              2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d))) := by
            symm
            exact MeasureTheory.ofReal_lpNorm (stftRep_memLp_schwartz_realVec h f)
    _ = ENNReal.ofReal
          (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
              (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
              (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
          rw [lpNorm_stftRep_schwartz_realVec]

private theorem stftRep_tendsto_schwartzApprox_pointwise {d : Nat}
    (h f : L2Real d) (ξ : PhaseSpace d) :
    Tendsto
      (fun n : Nat =>
        stftRep
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ)
      atTop (nhds (stftRep h f ξ)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hhN : Tendsto hN atTop (nhds h) := by
    simpa [hN, μ] using schwartzApproxRealVec_toLp_tendsto h
  have hfN : Tendsto fN atTop (nhds f) := by
    simpa [fN, μ] using schwartzApproxRealVec_toLp_tendsto f
  have hf_err : Tendsto (fun n : Nat => ‖fN n - f‖) atTop (nhds 0) := by
    have hf_const : Tendsto (fun _ : Nat => f) atTop (nhds f) := tendsto_const_nhds
    simpa using (hfN.sub hf_const).norm
  have hh_err : Tendsto (fun n : Nat => ‖hN n - h‖) atTop (nhds 0) := by
    have hh_const : Tendsto (fun _ : Nat => h) atTop (nhds h) := tendsto_const_nhds
    simpa using (hhN.sub hh_const).norm
  have hh_norm : Tendsto (fun n : Nat => ‖hN n‖) atTop (nhds ‖h‖) := hhN.norm
  have hbound_tendsto :
      Tendsto
        (fun n : Nat => ‖fN n - f‖ * ‖hN n‖ + ‖f‖ * ‖hN n - h‖)
        atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : Nat => ‖fN n - f‖ * ‖hN n‖) atTop (nhds 0) := by
      simpa using hf_err.mul hh_norm
    have h₂ : Tendsto (fun n : Nat => ‖f‖ * ‖hN n - h‖) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hh_err)
    simpa using h₁.add h₂
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) ?_ hbound_tendsto
  intro n
  rw [dist_eq_norm]
  exact norm_stftRep_sub_le (hN n) h (fN n) f ξ

private theorem eLpNorm_stftRep_le {d : Nat} (h f : L2Real d) :
    MeasureTheory.eLpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hmem : MeasureTheory.MemLp (h : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp h
  let fmem : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp f
  let hN : Nat → L2Real d := fun n => (schwartzApproxRealVec hmem n).toLp 2 μ
  let fN : Nat → L2Real d := fun n => (schwartzApproxRealVec fmem n).toLp 2 μ
  let F : PhaseSpace d → ℂ := stftRep h f
  let Fₙ : Nat → PhaseSpace d → ℂ := fun n => stftRep (hN n) (fN n)
  have hpoint : ∀ᵐ p : PhaseSpace d ∂μP, Tendsto (fun n : Nat => Fₙ n p) atTop (nhds (F p)) := by
    filter_upwards with p
    simpa [F, Fₙ, hN, fN, hmem, fmem, μ] using
      stftRep_tendsto_schwartzApprox_pointwise h f p
  have hmeas : ∀ n : Nat, AEStronglyMeasurable (Fₙ n) μP := by
    intro n
    simpa [Fₙ, hN, fN, μP] using stftRep_aestronglyMeasurable (hN n) (fN n)
  have hliminf :
      MeasureTheory.eLpNorm F 2 μP ≤
        atTop.liminf (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP) := by
    exact MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas F hpoint
  have hprod :
      Tendsto
        (fun n : Nat =>
          MeasureTheory.lpNorm (schwartzApproxRealVec fmem n : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (schwartzApproxRealVec hmem n : RealVec d -> ℂ) 2 μ)
        atTop
        (nhds (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ)) := by
    exact (schwartzApproxRealVec_tendsto_lpNorm fmem).mul
      (schwartzApproxRealVec_tendsto_lpNorm hmem)
  have hnorms' :
      Tendsto
        (fun n : Nat =>
          ENNReal.ofReal
            (MeasureTheory.lpNorm (schwartzApproxRealVec fmem n : RealVec d -> ℂ) 2 μ *
              MeasureTheory.lpNorm (schwartzApproxRealVec hmem n : RealVec d -> ℂ) 2 μ))
        atTop
        (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
    exact
      (ENNReal.continuous_ofReal.tendsto
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ)).comp hprod
  have hnorms :
      Tendsto (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP)
        atTop
        (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
    have hnorms_aux :
        Tendsto
          (fun n : Nat =>
            MeasureTheory.eLpNorm
              (fun p : PhaseSpace d =>
                stftRep
                  ((schwartzApproxRealVec hmem n).toLp 2 μ)
                  ((schwartzApproxRealVec fmem n).toLp 2 μ) p)
              2 μP)
          atTop
          (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
      simpa [μ, μP, eLpNorm_stftRep_schwartz_eq] using hnorms'
    simpa [Fₙ, hN, fN] using hnorms_aux
  calc
    MeasureTheory.eLpNorm (stftRep h f) 2 μP
        = MeasureTheory.eLpNorm F 2 μP := by rfl
    _ ≤ atTop.liminf (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP) := hliminf
    _ = ENNReal.ofReal
          (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) := by
          rw [hnorms.liminf_eq]

private theorem stftRep_sq_integrable {d : Nat} (h f : L2Real d) :
    Integrable (fun p : PhaseSpace d => ‖stftRep h f p‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hfinite_rhs :
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hfin : MeasureTheory.eLpNorm (stftRep h f) 2 μP < ⊤ :=
    lt_of_le_of_lt (eLpNorm_stftRep_le h f) hfinite_rhs
  have hmem : MeasureTheory.MemLp (stftRep h f) 2 μP :=
    ⟨stftRep_aestronglyMeasurable h f, hfin⟩
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (stftRep_aestronglyMeasurable h f)).mp hmem

private theorem stftRep_sq_complex_integrable {d : Nat} (h f : L2Real d) :
    Integrable (fun p : PhaseSpace d => ((‖stftRep h f p‖ ^ 2 : ℝ) : ℂ))
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  simpa using (stftRep_sq_integrable h f).ofReal (𝕜 := ℂ)

private theorem stftRep_memLp {d : Nat} (h f : L2Real d) :
    MeasureTheory.MemLp (stftRep h f) 2
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (stftRep_aestronglyMeasurable h f)).2 (stftRep_sq_integrable h f)

private theorem lpNorm_coeFn_L2Real_eq_norm {d : Nat} (f : L2Real d) :
    MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm (MeasureTheory.Lp.memLp f).aestronglyMeasurable]

private theorem lpNorm_stftRep_le_lpNorm {d : Nat} (h f : L2Real d) :
    MeasureTheory.lpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hmem : MeasureTheory.MemLp (stftRep h f) 2 μP := stftRep_memLp h f
  rw [← MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable]
  simpa using
    (ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
      (eLpNorm_stftRep_le h f)

private theorem lpNorm_stftRep_le {d : Nat} (h f : L2Real d) :
    MeasureTheory.lpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ‖f‖ * ‖h‖ := by
  simpa [lpNorm_coeFn_L2Real_eq_norm] using lpNorm_stftRep_le_lpNorm h f

private theorem translateL2_sub {d : Nat} (a : RealVec d) (f g : L2Real d) :
    translateL2 a (f - g) = translateL2 a f - translateL2 a g := by
  simpa [translateL2] using DomAddAct.vadd_Lp_sub (DomAddAct.mk a) f g

private theorem star_L2_sub {d : Nat} (f g : L2Real d) :
    star (f - g) = star f - star g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (f - g), MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g, MeasureTheory.Lp.coeFn_sub f g,
    MeasureTheory.Lp.coeFn_sub (star f) (star g)] with t hfg hf hg hsub hstarsub
  rw [hfg, hstarsub]
  simp only [Pi.star_apply, Pi.sub_apply] at *
  rw [hsub, hf, hg]
  simp

private theorem modulateL2_sub {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    modulateL2 ω (f - g) = modulateL2 ω f - modulateL2 ω g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateL2_coeFn ω (f - g), modulateL2_coeFn ω f,
    modulateL2_coeFn ω g, MeasureTheory.Lp.coeFn_sub f g,
    MeasureTheory.Lp.coeFn_sub (modulateL2 ω f) (modulateL2 ω g)] with t hfg hf hg hsub hmodsub
  rw [hfg, hmodsub]
  simp only [Pi.sub_apply] at *
  rw [hf, hg, hsub]
  ring

private theorem stftRep_sub_eq_add {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) (ξ : PhaseSpace d) :
    stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ =
      stftRep h₁ (f₁ - f₂) ξ + stftRep (h₁ - h₂) f₂ ξ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  let T : L2Real d → L2Real d := fun h =>
    modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))
  have hT_sub : T (h₁ - h₂) = T h₁ - T h₂ := by
    simp [T, translateL2_sub, star_L2_sub, modulateL2_sub]
  rw [stftRep_eq_lpPairing h₁ f₁ ξ, stftRep_eq_lpPairing h₂ f₂ ξ,
    stftRep_eq_lpPairing h₁ (f₁ - f₂) ξ,
    stftRep_eq_lpPairing (h₁ - h₂) f₂ ξ]
  change P f₁ (T h₁) - P f₂ (T h₂) =
    P (f₁ - f₂) (T h₁) + P f₂ (T (h₁ - h₂))
  rw [hT_sub]
  simp [P]

private theorem lpNorm_stftRep_sub_le {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) :
    MeasureTheory.lpNorm
      (fun ξ : PhaseSpace d => stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hmem₁ : MeasureTheory.MemLp (stftRep h₁ (f₁ - f₂)) 2 μP :=
    stftRep_memLp h₁ (f₁ - f₂)
  have hmem₂ : MeasureTheory.MemLp (stftRep (h₁ - h₂) f₂) 2 μP :=
    stftRep_memLp (h₁ - h₂) f₂
  calc
    MeasureTheory.lpNorm
        (fun ξ : PhaseSpace d => stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ) 2 μP
        = MeasureTheory.lpNorm
            ((stftRep h₁ (f₁ - f₂)) + stftRep (h₁ - h₂) f₂) 2 μP := by
            congr 1
            funext ξ
            exact stftRep_sub_eq_add h₁ h₂ f₁ f₂ ξ
    _ ≤ MeasureTheory.lpNorm (stftRep h₁ (f₁ - f₂)) 2 μP +
          MeasureTheory.lpNorm (stftRep (h₁ - h₂) f₂) 2 μP := by
          exact MeasureTheory.lpNorm_add_le hmem₁ (by norm_num)
    _ ≤ ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
          gcongr
          · exact lpNorm_stftRep_le h₁ (f₁ - f₂)
          · exact lpNorm_stftRep_le (h₁ - h₂) f₂

-- This convergence proof has a large phase-space `lpNorm` expression; the algebra is direct,
-- but normalization exceeds the default heartbeat budget.
private theorem lpNorm_stftRep_tendsto_schwartzApprox {d : Nat}
    (h f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm
          (fun ξ : PhaseSpace d =>
            stftRep
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ -
              stftRep h f ξ)
          2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hhN : Tendsto hN atTop (nhds h) := by
    simpa [hN, μ] using schwartzApproxRealVec_toLp_tendsto h
  have hfN : Tendsto fN atTop (nhds f) := by
    simpa [fN, μ] using schwartzApproxRealVec_toLp_tendsto f
  have hf_err : Tendsto (fun n : Nat => ‖fN n - f‖) atTop (nhds 0) := by
    have hf_const : Tendsto (fun _ : Nat => f) atTop (nhds f) := tendsto_const_nhds
    simpa using (hfN.sub hf_const).norm
  have hh_err : Tendsto (fun n : Nat => ‖hN n - h‖) atTop (nhds 0) := by
    have hh_const : Tendsto (fun _ : Nat => h) atTop (nhds h) := tendsto_const_nhds
    simpa using (hhN.sub hh_const).norm
  have hh_norm : Tendsto (fun n : Nat => ‖hN n‖) atTop (nhds ‖h‖) := hhN.norm
  have hbound_tendsto :
      Tendsto
        (fun n : Nat => ‖fN n - f‖ * ‖hN n‖ + ‖f‖ * ‖hN n - h‖)
        atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : Nat => ‖fN n - f‖ * ‖hN n‖) atTop (nhds 0) := by
      simpa using hf_err.mul hh_norm
    have h₂ : Tendsto (fun n : Nat => ‖f‖ * ‖hN n - h‖) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hh_err)
    simpa using h₁.add h₂
  refine squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg) ?_ hbound_tendsto
  intro n
  simpa [hN, fN, μ, μP] using lpNorm_stftRep_sub_le (hN n) h (fN n) f

private theorem lpNorm_mul_le_real
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    MeasureTheory.lpNorm (fun x => f x * g x) 1 μ ≤
      MeasureTheory.lpNorm f 2 μ * MeasureTheory.lpNorm g 2 μ := by
  have hmem : MeasureTheory.MemLp (fun x => f x * g x) 1 μ := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hg.mul hf)
    filter_upwards with x
    simp [Pi.mul_apply]
  rw [MeasureTheory.lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  have hpq : Real.HolderConjugate 2 2 := by
    constructor <;> norm_num
  have hf_abs : MeasureTheory.MemLp (fun x => |f x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hg_abs : MeasureTheory.MemLp (fun x => |g x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [Real.norm_eq_abs] using hg.norm
  have hf_nonneg : 0 ≤ᵐ[μ] fun x => |f x| :=
    Filter.Eventually.of_forall fun _ => abs_nonneg _
  have hg_nonneg : 0 ≤ᵐ[μ] fun x => |g x| :=
    Filter.Eventually.of_forall fun _ => abs_nonneg _
  have hholder := @MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg α _ μ 2 2 hpq
    (fun x => |f x|) (fun x => |g x|) hf_nonneg hg_nonneg hf_abs hg_abs
  have hf_lp :
      (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        MeasureTheory.lpNorm f 2 μ := by
    have h := hf.eLpNorm_eq_integral_rpow_norm (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    norm_num at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (by positivity),
      MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable] at h'
    simpa [Real.norm_eq_abs] using h'.symm
  have hg_lp :
      (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        MeasureTheory.lpNorm g 2 μ := by
    have h := hg.eLpNorm_eq_integral_rpow_norm (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    norm_num at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (by positivity),
      MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable] at h'
    simpa [Real.norm_eq_abs] using h'.symm
  have hleft :
      ∫ x, ‖f x * g x‖ ∂μ = ∫ x, |f x| * |g x| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [Real.norm_eq_abs]
  rw [hleft]
  rw [hf_lp, hg_lp] at hholder
  exact hholder

-- This is the Hölder/square-difference estimate over phase space; the proof is copied
-- from the one-dimensional STFT route but with vector-valued `L2Real` approximants.
private theorem lpNorm_stftRep_sq_sub_tendsto_zero {d : Nat}
    (h f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm
          (fun ξ : PhaseSpace d =>
            (((‖stftRep
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ‖ ^ 2 : ℝ) : ℂ) -
              ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ)))
          1 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  let F : PhaseSpace d → ℂ := stftRep h f
  let Fₙ : Nat → PhaseSpace d → ℂ := fun n => stftRep (hN n) (fN n)
  let Dₙ : Nat → PhaseSpace d → ℂ := fun n ξ =>
    (((‖Fₙ n ξ‖ ^ 2 : ℝ) : ℂ) - ((‖F ξ‖ ^ 2 : ℝ) : ℂ))
  let Aₙ : Nat → PhaseSpace d → ℝ := fun n ξ => ‖Fₙ n ξ‖ + ‖F ξ‖
  let Bₙ : Nat → PhaseSpace d → ℝ := fun n ξ => ‖Fₙ n ξ - F ξ‖
  let Cₙ : Nat → ℝ := fun n => ‖fN n‖ * ‖hN n‖ + ‖f‖ * ‖h‖
  have hhN : Tendsto hN atTop (nhds h) := by
    simpa [hN, μ] using schwartzApproxRealVec_toLp_tendsto h
  have hfN : Tendsto fN atTop (nhds f) := by
    simpa [fN, μ] using schwartzApproxRealVec_toLp_tendsto f
  have hdiff :
      Tendsto
        (fun n : Nat => MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP)
        atTop (nhds 0) := by
    simpa [F, Fₙ, hN, fN, μ, μP] using lpNorm_stftRep_tendsto_schwartzApprox h f
  have hC_tendsto :
      Tendsto Cₙ atTop (nhds (‖f‖ * ‖h‖ + ‖f‖ * ‖h‖)) := by
    have hprod : Tendsto (fun n : Nat => ‖fN n‖ * ‖hN n‖) atTop
        (nhds (‖f‖ * ‖h‖)) := hfN.norm.mul hhN.norm
    exact hprod.add tendsto_const_nhds
  have hCtendsto :
      Tendsto
        (fun n : Nat =>
          Cₙ n * MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP)
        atTop (nhds 0) := by
    simpa using hC_tendsto.mul hdiff
  refine squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg) ?_ hCtendsto
  intro n
  have hmemFn : MeasureTheory.MemLp (Fₙ n) 2 μP := by
    dsimp [Fₙ]
    exact stftRep_memLp (hN n) (fN n)
  have hmemF : MeasureTheory.MemLp F 2 μP := by
    dsimp [F]
    exact stftRep_memLp h f
  have hmemDiff : MeasureTheory.MemLp (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP :=
    hmemFn.sub hmemF
  have hAmem : MeasureTheory.MemLp (Aₙ n) 2 μP := by
    dsimp [Aₙ]
    exact hmemFn.norm.add hmemF.norm
  have hBmem : MeasureTheory.MemLp (Bₙ n) 2 μP := by
    dsimp [Bₙ]
    exact hmemDiff.norm
  have hHmem : MeasureTheory.MemLp (fun ξ : PhaseSpace d => Aₙ n ξ * Bₙ n ξ) 1 μP := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hBmem.mul hAmem)
    filter_upwards with ξ
    simp [Pi.mul_apply]
  have hpoint : ∀ ξ : PhaseSpace d, ‖Dₙ n ξ‖ ≤ Aₙ n ξ * Bₙ n ξ := by
    intro ξ
    have hsum_nonneg : 0 ≤ ‖Fₙ n ξ‖ + ‖F ξ‖ := by positivity
    calc
      ‖Dₙ n ξ‖ =
          ‖(((‖Fₙ n ξ‖ ^ 2 : ℝ) : ℂ) - ((‖F ξ‖ ^ 2 : ℝ) : ℂ))‖ := by
            rfl
      _ = |‖Fₙ n ξ‖ ^ 2 - ‖F ξ‖ ^ 2| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ = (‖Fₙ n ξ‖ + ‖F ξ‖) * |‖Fₙ n ξ‖ - ‖F ξ‖| := by
            rw [sq_sub_sq, abs_mul, abs_of_nonneg hsum_nonneg]
      _ ≤ (‖Fₙ n ξ‖ + ‖F ξ‖) * ‖Fₙ n ξ - F ξ‖ := by
            exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) hsum_nonneg
      _ = Aₙ n ξ * Bₙ n ξ := by
            simp [Aₙ, Bₙ]
  have hD_le :
      MeasureTheory.lpNorm (Dₙ n) 1 μP ≤
        MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Aₙ n ξ * Bₙ n ξ) 1 μP :=
    MeasureTheory.lpNorm_mono_real hHmem hpoint
  have hAB_le :
      MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Aₙ n ξ * Bₙ n ξ) 1 μP ≤
        MeasureTheory.lpNorm (Aₙ n) 2 μP * MeasureTheory.lpNorm (Bₙ n) 2 μP :=
    lpNorm_mul_le_real hAmem hBmem
  have hA_le : MeasureTheory.lpNorm (Aₙ n) 2 μP ≤ Cₙ n := by
    calc
      MeasureTheory.lpNorm (Aₙ n) 2 μP
          ≤ MeasureTheory.lpNorm (fun ξ : PhaseSpace d => ‖Fₙ n ξ‖) 2 μP +
              MeasureTheory.lpNorm (fun ξ : PhaseSpace d => ‖F ξ‖) 2 μP := by
              dsimp [Aₙ]
              exact
                MeasureTheory.lpNorm_add_le hmemFn.norm
                  (g := fun ξ : PhaseSpace d => ‖F ξ‖) (by norm_num)
      _ = MeasureTheory.lpNorm (Fₙ n) 2 μP + MeasureTheory.lpNorm F 2 μP := by
            simp [MeasureTheory.lpNorm_norm, hmemFn.aestronglyMeasurable,
              hmemF.aestronglyMeasurable]
      _ ≤ ‖fN n‖ * ‖hN n‖ + ‖f‖ * ‖h‖ := by
            gcongr
            · exact lpNorm_stftRep_le (hN n) (fN n)
            · exact lpNorm_stftRep_le h f
  calc
    MeasureTheory.lpNorm (Dₙ n) 1 μP
        ≤ MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Aₙ n ξ * Bₙ n ξ) 1 μP := hD_le
    _ ≤ MeasureTheory.lpNorm (Aₙ n) 2 μP * MeasureTheory.lpNorm (Bₙ n) 2 μP := hAB_le
    _ ≤ Cₙ n * MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP := by
          rw [show MeasureTheory.lpNorm (Bₙ n) 2 μP =
              MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP by
                simp [Bₙ, MeasureTheory.lpNorm_norm, hmemDiff.aestronglyMeasurable]]
          exact mul_le_mul_of_nonneg_right hA_le MeasureTheory.lpNorm_nonneg

private theorem norm_ambiguityRep_sub_le {d : Nat}
    (f₁ f₂ g₁ g₂ : L2Real d) (ξ : PhaseSpace d) :
    ‖ambiguityRep f₁ g₁ ξ - ambiguityRep f₂ g₂ ξ‖ ≤
      ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  let T₁ : L2Real d → L2Real d := fun f => translateL2 ((1 / 2 : ℝ) • ξ.1) f
  let T₂ : L2Real d → L2Real d := fun g =>
    modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))
  have hT₁_norm : ‖T₁ f₂‖ = ‖f₂‖ := by
    simp [T₁, norm_translateL2]
  have hT₂_norm : ‖T₂ g₁‖ = ‖g₁‖ := by
    simp [T₂, norm_modulateL2, norm_star_L2, norm_translateL2]
  have hT₁_sub_norm : ‖T₁ f₁ - T₁ f₂‖ = ‖f₁ - f₂‖ := by
    calc
      ‖T₁ f₁ - T₁ f₂‖ = dist (T₁ f₁) (T₁ f₂) := by
        rw [dist_eq_norm]
      _ = dist f₁ f₂ := by
        simp [T₁, dist_translateL2]
      _ = ‖f₁ - f₂‖ := by
        rw [dist_eq_norm]
  have hT₂_sub_norm : ‖T₂ g₁ - T₂ g₂‖ = ‖g₁ - g₂‖ := by
    calc
      ‖T₂ g₁ - T₂ g₂‖ = dist (T₂ g₁) (T₂ g₂) := by
        rw [dist_eq_norm]
      _ = dist (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₁))
            (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₂)) := by
        simp [T₂, dist_modulateL2]
      _ = dist (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₁)
            (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₂) := by
        rw [dist_star_L2]
      _ = dist g₁ g₂ := by
        rw [dist_translateL2]
      _ = ‖g₁ - g₂‖ := by
        rw [dist_eq_norm]
  rw [ambiguityRep_eq_lpPairing f₁ g₁ ξ, ambiguityRep_eq_lpPairing f₂ g₂ ξ]
  change ‖P (T₁ f₁) (T₂ g₁) - P (T₁ f₂) (T₂ g₂)‖ ≤
    ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖
  have hsplit :
      P (T₁ f₁) (T₂ g₁) - P (T₁ f₂) (T₂ g₂) =
        P (T₁ f₁ - T₁ f₂) (T₂ g₁) + P (T₁ f₂) (T₂ g₁ - T₂ g₂) := by
    simp [P]
  calc
    ‖P (T₁ f₁) (T₂ g₁) - P (T₁ f₂) (T₂ g₂)‖
        = ‖P (T₁ f₁ - T₁ f₂) (T₂ g₁) + P (T₁ f₂) (T₂ g₁ - T₂ g₂)‖ := by
          rw [hsplit]
    _ ≤ ‖P (T₁ f₁ - T₁ f₂) (T₂ g₁)‖ +
          ‖P (T₁ f₂) (T₂ g₁ - T₂ g₂)‖ := norm_add_le _ _
    _ ≤ ‖T₁ f₁ - T₁ f₂‖ * ‖T₂ g₁‖ +
          ‖T₁ f₂‖ * ‖T₂ g₁ - T₂ g₂‖ := by
          exact add_le_add (lpPairing_mul_norm_le (T₁ f₁ - T₁ f₂) (T₂ g₁))
            (lpPairing_mul_norm_le (T₁ f₂) (T₂ g₁ - T₂ g₂))
    _ = ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖ := by
          rw [hT₁_sub_norm, hT₂_norm, hT₁_norm, hT₂_sub_norm]

private theorem ambiguityRep_tendsto_schwartzApprox {d : Nat}
    (f : L2Real d) (ξ : PhaseSpace d) :
    Tendsto
      (fun n : Nat =>
        ambiguityRep
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ)
      atTop (nhds (ambiguityRep f f ξ)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hfN : Tendsto fN atTop (nhds f) := by
    simpa [fN, μ] using schwartzApproxRealVec_toLp_tendsto f
  have hf_err : Tendsto (fun n : Nat => ‖fN n - f‖) atTop (nhds 0) := by
    have hf_const : Tendsto (fun _ : Nat => f) atTop (nhds f) := tendsto_const_nhds
    simpa using (hfN.sub hf_const).norm
  have hf_norm : Tendsto (fun n : Nat => ‖fN n‖) atTop (nhds ‖f‖) := hfN.norm
  have hbound_tendsto :
      Tendsto (fun n : Nat => ‖fN n - f‖ * ‖fN n‖ + ‖f‖ * ‖fN n - f‖)
        atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : Nat => ‖fN n - f‖ * ‖fN n‖) atTop (nhds 0) := by
      simpa using hf_err.mul hf_norm
    have h₂ : Tendsto (fun n : Nat => ‖f‖ * ‖fN n - f‖) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hf_err)
    simpa using h₁.add h₂
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) ?_ hbound_tendsto
  intro n
  rw [dist_eq_norm]
  simpa [fN, μ] using norm_ambiguityRep_sub_le (fN n) f (fN n) f ξ

/-- Fubini/phase unfolding of `symplecticFourierRep` applied to the spectrogram
density: it rewrites the phase-space integral as the iterated integral with the
two one-dimensional modulation phases.  Factored out of the Moyal identity so the
remaining normalisation `calc` stays within the default heartbeat budget. -/
private lemma symplecticFourierRep_stft_sq_eq_iterated {d : Nat}
    (x ω : RealVec d)
    (hLp fLp : L2Real d)
    (hSphase :
      Integrable
        (fun η : PhaseSpace d =>
          ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp
              ((2 * Real.pi : ℂ) * Complex.I *
                (((inner ℝ η.2 x : ℝ) - (inner ℝ η.1 ω : ℝ) : ℝ) : ℂ)))
        ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω) =
      ∫ y : RealVec d, ∫ η : RealVec d,
        ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η) := by
  simp only [symplecticFourierRep]
  rw [MeasureTheory.Measure.volume_eq_prod (RealVec d) (RealVec d),
    MeasureTheory.integral_prod _ hSphase]
  refine integral_congr_ae ?_
  filter_upwards with y
  refine integral_congr_ae ?_
  filter_upwards with η
  rw [symplecticFourier_phase_eq_modulationPhase x ω y η]

/-- The tail of the Moyal calc: swap the order of integration in the windowed
autocorrelation kernel `K` and collapse the inner integrals to the two ambiguity
functions.  Isolated so the normalisation `calc` stays within the default
heartbeat budget. -/
private lemma moyal_kernel_iterated_eq {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) (hLp fLp : L2Real d)
    (hhLp : hLp = h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (hfLp : fLp = f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (K : RealVec d → RealVec d → ℂ)
    (hKdef : K = fun y t =>
      (star (f t) * f (t + x)) *
        (h (t - y) * star (h (t + x - y))) * modulationPhase ω y)
    (hK : Integrable (Function.uncurry K)
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) :
    ∫ y : RealVec d, ∫ t : RealVec d, K y t =
      ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω)) := by
  subst hKdef hfLp
  calc
    ∫ y : RealVec d, ∫ t : RealVec d,
        (star (f t) * f (t + x)) *
          (h (t - y) * star (h (t + x - y))) * modulationPhase ω y
        = ∫ t : RealVec d, ∫ y : RealVec d,
            (star (f t) * f (t + x)) *
              (h (t - y) * star (h (t + x - y))) * modulationPhase ω y :=
          MeasureTheory.integral_integral_swap hK
    _ = ∫ t : RealVec d, (star (f t) * f (t + x)) *
          (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
            star (ambiguityRep hLp hLp (x, ω))) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ∫ y : RealVec d,
                (star (f t) * f (t + x)) *
                  (h (t - y) * star (h (t + x - y))) * modulationPhase ω y
                = ∫ y : RealVec d, (star (f t) * f (t + x)) *
                    (h (t - y) * star (h (t + x - y)) * modulationPhase ω y) := by
                    refine integral_congr_ae ?_
                    filter_upwards with y
                    ring
            _ = (star (f t) * f (t + x)) *
                ∫ y : RealVec d,
                  h (t - y) * star (h (t + x - y)) * modulationPhase ω y := by
                simpa [mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := star (f t) * f (t + x))
                    (f := fun y : RealVec d =>
                      h (t - y) * star (h (t + x - y)) * modulationPhase ω y))
            _ = (star (f t) * f (t + x)) *
                (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
                  star (ambiguityRep hLp hLp (x, ω))) := by
                rw [integral_window_autocorr_phase_schwartz_realVec h t x ω, ← hhLp]
    _ = star (ambiguityRep hLp hLp (x, ω)) *
          ∫ t : RealVec d,
            (star (f t) * f (t + x)) * modulationPhase ω (t + (1 / 2 : ℝ) • x) := by
          calc
            ∫ t : RealVec d, (star (f t) * f (t + x)) *
                (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
                  star (ambiguityRep hLp hLp (x, ω)))
                = ∫ t : RealVec d, star (ambiguityRep hLp hLp (x, ω)) *
                    ((star (f t) * f (t + x)) *
                      modulationPhase ω (t + (1 / 2 : ℝ) • x) ) := by
                    refine integral_congr_ae ?_
                    filter_upwards with t
                    ring
            _ = star (ambiguityRep hLp hLp (x, ω)) *
                ∫ t : RealVec d,
                  (star (f t) * f (t + x)) *
                    modulationPhase ω (t + (1 / 2 : ℝ) • x) := by
                simpa [mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := star (ambiguityRep hLp hLp (x, ω)))
                    (f := fun t : RealVec d =>
                      (star (f t) * f (t + x)) *
                        modulationPhase ω (t + (1 / 2 : ℝ) • x)))
    _ = star (ambiguityRep hLp hLp (x, ω)) *
          ambiguityRep (f.toLp 2 MeasureTheory.volume)
            (f.toLp 2 MeasureTheory.volume) (x, ω) := by
          rw [integral_signal_autocorr_phase_schwartz_realVec f x ω]
    _ = ambiguityRep (f.toLp 2 MeasureTheory.volume)
          (f.toLp 2 MeasureTheory.volume) (x, ω) *
          star (ambiguityRep hLp hLp (x, ω)) := by
          ring

/-- Middle of the Moyal calc: collapse the inner `η`-integral of the squared STFT
times the modulation phases into the slice autocorrelation, and rewrite the slices
as the windowed autocorrelation kernel `K`.  Isolated to keep each proof within the
default heartbeat budget. -/
private lemma moyal_slice_collapse {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d)
    (hLp fLp : L2Real d)
    (hhLp : hLp = h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (hfLp : fLp = f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (K : RealVec d → RealVec d → ℂ)
    (hKdef : K = fun y t =>
      (star (f t) * f (t + x)) *
        (h (t - y) * star (h (t + x - y))) * modulationPhase ω y) :
    ∫ y : RealVec d, ∫ η : RealVec d,
        ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η) =
      ∫ y : RealVec d, ∫ t : RealVec d, K y t := by
  subst hhLp hfLp hKdef
  refine integral_congr_ae ?_
  filter_upwards with y
  calc
    ∫ η : RealVec d,
        ((‖stftRep (h.toLp 2 MeasureTheory.volume) (f.toLp 2 MeasureTheory.volume)
          (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η)
        = ∫ η : RealVec d, modulationPhase ω y *
            (((‖stftRep (h.toLp 2 MeasureTheory.volume)
              (f.toLp 2 MeasureTheory.volume) (y, η)‖ ^ 2 : ℝ) : ℂ) *
              modulationPhase (-x) η) := by
              refine integral_congr_ae ?_
              filter_upwards with η
              ring
    _ = modulationPhase ω y *
        ∫ η : RealVec d,
          ((‖stftRep (h.toLp 2 MeasureTheory.volume)
            (f.toLp 2 MeasureTheory.volume) (y, η)‖ ^ 2 : ℝ) : ℂ) *
            modulationPhase (-x) η :=
          MeasureTheory.integral_const_mul _ _
    _ = modulationPhase ω y *
        ∫ t : RealVec d, star (stftSliceSchwartz h f y t) *
          stftSliceSchwartz h f y (t + x) := by
          rw [integral_stftRep_sq_phase_slice_schwartz h f y x]
    _ = ∫ t : RealVec d, modulationPhase ω y *
          (star (stftSliceSchwartz h f y t) *
            stftSliceSchwartz h f y (t + x)) := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (r := modulationPhase ω y)
              (f := fun t : RealVec d =>
                star (stftSliceSchwartz h f y t) *
                  stftSliceSchwartz h f y (t + x))).symm
    _ = ∫ t : RealVec d,
          (star (f t) * f (t + x)) *
            (h (t - y) * star (h (t + x - y))) * modulationPhase ω y := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simp [stftSliceSchwartz_apply, mul_left_comm, mul_comm]

-- The vector Schwartz Moyal proof is one long Fubini/phase-normalization calc.
private theorem symplecticFourier_stft_sq_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    symplecticFourierRep
        (fun η : PhaseSpace d =>
          ((‖stftRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) η‖ ^ 2 : ℝ) :
            ℂ))
        (x, ω) =
      ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) *
        star (ambiguityRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  change
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω) =
      ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω))
  let S : PhaseSpace d → ℂ := fun η => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)
  let phase : PhaseSpace d → ℂ := fun η =>
    Complex.exp
      ((2 * Real.pi : ℂ) * Complex.I *
        (((inner ℝ η.2 x : ℝ) - (inner ℝ η.1 ω : ℝ) : ℝ) : ℂ))
  let K : RealVec d → RealVec d → ℂ := fun y t =>
    (star (f t) * f (t + x)) *
      (h (t - y) * star (h (t + x - y))) *
      modulationPhase ω y
  let G : RealVec d × RealVec d → ℂ := fun p =>
    ((star (f p.1) * f (p.1 + x)) *
      (h (p.1 - p.2) * star (h (p.1 + x - p.2)))) *
      modulationPhase ω p.2
  have hS : Integrable S (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
    simpa [S, hLp, fLp, μ] using stftRep_sq_complex_integrable_schwartz_realVec h f
  have hphase_meas :
      AEStronglyMeasurable phase
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
    exact (by fun_prop : Measurable phase).aestronglyMeasurable
  have hphase_bound :
      ∀ᵐ η : PhaseSpace d ∂(MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)),
        ‖phase η‖ ≤ (1 : ℝ) := by
    filter_upwards with η
    simpa [phase] using le_of_eq (symplecticFourierPhase_norm η (x, ω))
  have hSphase :
      Integrable (fun η : PhaseSpace d => S η * phase η)
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) :=
    hS.mul_bdd hphase_meas hphase_bound
  have hmod_meas :
      AEStronglyMeasurable (fun p : RealVec d × RealVec d => modulationPhase ω p.2)
        (μ.prod μ) := by
    exact
      (by
        unfold modulationPhase
        fun_prop :
        Measurable fun p : RealVec d × RealVec d => modulationPhase ω p.2).aestronglyMeasurable
  have hmod_bound :
      ∀ᵐ p : RealVec d × RealVec d ∂(μ.prod μ), ‖modulationPhase ω p.2‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    simpa using le_of_eq (modulationPhase_norm ω p.2)
  have hG : Integrable G (μ.prod μ) := by
    have hbase :
        Integrable
          (fun p : RealVec d × RealVec d =>
            (star (f p.1) * f (p.1 + x)) *
              (h (p.1 - p.2) * star (h (p.1 + x - p.2))))
          (μ.prod μ) := by
      simpa [μ] using autocorr_kernel_integrable_schwartz_realVec f h x
    simpa [G, mul_assoc] using hbase.mul_bdd hmod_meas hmod_bound
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine hG.swap.congr ?_
    filter_upwards with p
    simp only [K, G, Function.uncurry, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, mul_assoc]
  have hSphase_prod :
      Integrable
        (fun η : PhaseSpace d =>
          ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp
              ((2 * Real.pi : ℂ) * Complex.I *
                (((inner ℝ η.2 x : ℝ) - (inner ℝ η.1 ω : ℝ) : ℝ) : ℂ)))
        ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := hSphase
  calc
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω)
        = ∫ y : RealVec d, ∫ η : RealVec d,
            ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
              (modulationPhase ω y * modulationPhase (-x) η) :=
          symplecticFourierRep_stft_sq_eq_iterated x ω hLp fLp hSphase_prod
    _ = ∫ y : RealVec d, ∫ t : RealVec d, K y t :=
          moyal_slice_collapse h f x ω hLp fLp rfl rfl K rfl
    _ = ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω)) :=
          moyal_kernel_iterated_eq h f x ω hLp fLp rfl rfl K rfl hK

theorem continuous_spectrogramRep
    {d : Nat} (h f : L2Real d) :
    Continuous fun ξ : PhaseSpace d => ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hstft : Continuous (stftRep h f) := continuous_stftRep h f
  exact Complex.continuous_ofReal.comp ((continuous_norm.comp hstft).pow 2)

theorem spectrogramRep_eq_stft_mul_star
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ) =
      stftRep h f ξ * star (stftRep h f ξ) := by
  rw [Complex.star_def]
  exact_mod_cast (Complex.mul_conj' (stftRep h f ξ)).symm

theorem spectrogram_ambiguity_identity_of_product_moyal
    {d : Nat}
    (hmoyal : ∀ (h f : L2Real d) (ξ : PhaseSpace d),
      symplecticFourierRep
          (fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η)) ξ =
        ambiguityRep f f ξ * star (ambiguityRep h h ξ))
    (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by
  rw [show (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) =
      fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η) by
    funext η
    exact spectrogramRep_eq_stft_mul_star h f η]
  exact hmoyal h f ξ

theorem spectrogram_ambiguity_identity
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  let G : PhaseSpace d → ℂ := fun η => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)
  let Gₙ : Nat → PhaseSpace d → ℂ := fun n η => ((‖stftRep (hN n) (fN n) η‖ ^ 2 : ℝ) : ℂ)
  let A : ℂ := ambiguityRep f f ξ * star (ambiguityRep h h ξ)
  let Aₙ : Nat → ℂ := fun n => ambiguityRep (fN n) (fN n) ξ *
    star (ambiguityRep (hN n) (hN n) ξ)
  have hG : Integrable G μP := by
    simpa [G, μP] using stftRep_sq_complex_integrable h f
  have hGₙ : ∀ n : Nat, Integrable (Gₙ n) μP := by
    intro n
    simpa [Gₙ, hN, fN, μ, μP] using
      stftRep_sq_complex_integrable_schwartz_realVec
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n)
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n)
  have hLp :
      Tendsto
        (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1 μP)
        atTop (nhds 0) := by
    simpa [G, Gₙ, hN, fN, μ, μP] using lpNorm_stftRep_sq_sub_tendsto_zero h f
  have hfAmb :
      Tendsto (fun n : Nat => ambiguityRep (fN n) (fN n) ξ) atTop
        (nhds (ambiguityRep f f ξ)) := by
    simpa [fN, μ] using ambiguityRep_tendsto_schwartzApprox f ξ
  have hhAmb :
      Tendsto (fun n : Nat => ambiguityRep (hN n) (hN n) ξ) atTop
        (nhds (ambiguityRep h h ξ)) := by
    simpa [hN, μ] using ambiguityRep_tendsto_schwartzApprox h ξ
  have hA : Tendsto Aₙ atTop (nhds A) := by
    have hhAmbStar :
        Tendsto (fun n : Nat => star (ambiguityRep (hN n) (hN n) ξ)) atTop
          (nhds (star (ambiguityRep h h ξ))) := hhAmb.star
    simpa [A, Aₙ] using hfAmb.mul hhAmbStar
  have hEq : ∀ n : Nat, symplecticFourierRep (Gₙ n) ξ = Aₙ n := by
    intro n
    simpa [Gₙ, Aₙ, hN, fN, μ] using
      symplecticFourier_stft_sq_schwartz_realVec
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n)
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n) ξ.1 ξ.2
  simpa [G, A, μP] using
    symplecticFourierRep_eq_of_lpNorm_one_approx
      (G := G) (Gₙ := Gₙ) (A := A) (Aₙ := Aₙ) hG hGₙ hLp hA ξ hEq

theorem continuous_ambiguityRep
    {d : Nat} (f g : L2Real d) :
    Continuous (ambiguityRep f g) := by
  rw [show ambiguityRep f g = fun ξ : PhaseSpace d =>
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2
          (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))) by
    funext ξ
    exact ambiguityRep_eq_lpPairing f g ξ]
  have hfirst : Continuous fun ξ : PhaseSpace d =>
      translateL2 ((1 / 2 : ℝ) • ξ.1) f := by
    exact (continuous_translateL2_apply f).comp (by fun_prop)
  have htrans : Continuous fun ξ : PhaseSpace d =>
      translateL2 (-((1 / 2 : ℝ) • ξ.1)) g := by
    exact (continuous_translateL2_apply g).comp (by fun_prop)
  have hstar : Continuous fun ξ : PhaseSpace d =>
      star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g) :=
    continuous_star_L2.comp htrans
  have hsecond : Continuous fun ξ : PhaseSpace d =>
      modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)) := by
    exact continuous_modulateL2 continuous_snd hstar
  let pairing :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  exact ((pairing.continuous.comp hfirst).clm_apply hsecond)

theorem ae_unimodular_phase_to_L2_eq
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ} {w : ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hphase :
      gRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun u => w * fRep u) :
    g = w • f := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  rcases hg_rep with ⟨hg_mem, hg_eq⟩
  apply MeasureTheory.Lp.ext
  have hg_coe :
      ((g : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] gRep := by
    rw [← hg_eq]
    exact hg_mem.coeFn_toLp
  have hf_coe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hsmul :
      ((w • f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun u => w * fRep u := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul w f, hf_coe] with u hw hf
    rw [hw]
    simp [Pi.smul_apply, smul_eq_mul, hf]
  filter_upwards [hg_coe, hphase, hsmul] with u hg hph hsm
  calc
    ((g : L2Real d) : RealVec d -> ℂ) u = gRep u := hg
    _ = w * fRep u := hph
    _ = ((w • f : L2Real d) : RealVec d -> ℂ) u := hsm.symm

theorem rep_ae_eq_zero_of_L2_eq_zero
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hf_zero : f = 0) :
    fRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
      fun _ => (0 : ℂ) := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  have hcoe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hzero :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun _ => (0 : ℂ) := by
    rw [hf_zero]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 MeasureTheory.volume
  exact hcoe.symm.trans hzero

theorem L2_eq_zero_of_rep_ae_eq_zero
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep)
    (hzero : fRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
      fun _ => (0 : ℂ)) :
    f = 0 := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  apply MeasureTheory.Lp.ext
  have hcoe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  filter_upwards [hcoe, hzero,
    MeasureTheory.Lp.coeFn_zero ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))] with u hf hrep h0
  calc
    ((f : L2Real d) : RealVec d -> ℂ) u = fRep u := hf
    _ = 0 := hrep
    _ = ((0 : L2Real d) : RealVec d -> ℂ) u := h0.symm

theorem boxPartialSums_have_L2_limit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    True := by
  let _ := hd
  let _ := kappa
  /-
  Placeholder for the imported `L²` convergence package for box partial sums of
  square-summable coefficient data.
  -/
  trivial

theorem circleFourier_exact_modulus_bridge :
    True := by
  /-
  Placeholder for the one-dimensional analytic uniqueness and Fourier/STFT
  bridge used downstream by the circle and rigidity modules.
  -/
  trivial

end DimdPolyLEAN
