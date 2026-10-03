/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Dyadic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The consumer-facing Calderón--Zygmund decomposition certificate

The certificate records the maximal dyadic cubes and all estimates needed by
the good/bad part argument.  Its geometry is native to `Vec3`; no alternate
Euclidean carrier is introduced.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Euclidean

instance dyadicIndexCountable : Countable DyadicIndex := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (ℤ × DyadicCorner)
  apply Countable.mk
  refine ⟨fun Q : DyadicIndex => f (Q.scale, Q.corner), ?_⟩
  intro Q R h
  cases Q
  cases R
  have hc := Prod.mk.inj (hf h)
  cases hc.1
  cases hc.2
  rfl

/-- Iterated dyadic parent, with the original cube at generation zero. -/
def dyadicAncestor (Q : DyadicIndex) : ℕ → DyadicIndex
  | 0 => Q
  | n + 1 => dyadicParent (dyadicAncestor Q n)

private theorem dyadicAncestor_zero (Q : DyadicIndex) :
    dyadicAncestor Q 0 = Q := by
  rfl

private theorem dyadicAncestor_succ (Q : DyadicIndex) (n : ℕ) :
    dyadicAncestor Q (n + 1) = dyadicParent (dyadicAncestor Q n) := by
  rfl

private theorem dyadicAncestor_add (Q : DyadicIndex) (m n : ℕ) :
    dyadicAncestor (dyadicAncestor Q m) n = dyadicAncestor Q (m + n) := by
  induction n with
  | zero => simp [dyadicAncestor]
  | succ n ih =>
      rw [dyadicAncestor_succ, ih,
        show m + (n + 1) = (m + n) + 1 by omega,
        dyadicAncestor_succ]

private theorem dyadicAncestor_scale (Q : DyadicIndex) (n : ℕ) :
    (dyadicAncestor Q n).scale = Q.scale - (n : ℤ) := by
  induction n with
  | zero => simp [dyadicAncestor]
  | succ n ih =>
      rw [dyadicAncestor_succ, show n + 1 = Nat.succ n by rfl]
      change (dyadicAncestor Q n).scale - 1 = _
      rw [ih]
      push_cast
      ring

private theorem dyadicCube_subset_ancestor (Q : DyadicIndex) (n : ℕ) :
    dyadicCube Q.scale Q.corner ⊆
      dyadicCube (dyadicAncestor Q n).scale (dyadicAncestor Q n).corner := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
      rw [dyadicAncestor_succ]
      exact ih.trans (dyadicCube_subset_parent (dyadicAncestor Q n))

private theorem volume_dyadicAncestor (Q : DyadicIndex) (n : ℕ) :
    volume (dyadicCube (dyadicAncestor Q n).scale (dyadicAncestor Q n).corner) =
      (8 : ℝ≥0∞) ^ n * volume (dyadicCube Q.scale Q.corner) := by
  induction n with
  | zero => simp [dyadicAncestor]
  | succ n ih =>
      rw [dyadicAncestor_succ, dyadicParent_volume_ratio, ih, pow_succ]
      ac_rfl

private theorem dyadicIndex_eq_of_same_scale_intersect
    {Q R : DyadicIndex} (hscale : Q.scale = R.scale)
    (hint : (dyadicCube Q.scale Q.corner ∩
      dyadicCube R.scale R.corner).Nonempty) : Q = R := by
  obtain ⟨x, hxQ, hxR⟩ := hint
  cases Q with
  | mk qk qa =>
    cases R with
    | mk rk ra =>
      simp only at hscale ⊢
      subst rk
      congr
      exact dyadicCorner_unique hxQ hxR

private theorem dyadicAncestor_eq_of_intersect_of_scale_le
    {Q R : DyadicIndex} (hscale : Q.scale ≤ R.scale)
    (hint : (dyadicCube Q.scale Q.corner ∩
      dyadicCube R.scale R.corner).Nonempty) :
    dyadicAncestor R (Int.toNat (R.scale - Q.scale)) = Q := by
  let n : ℕ := Int.toNat (R.scale - Q.scale)
  have hnonneg : 0 ≤ R.scale - Q.scale := sub_nonneg.mpr hscale
  have hn : (n : ℤ) = R.scale - Q.scale := by
    dsimp [n]
    exact Int.toNat_of_nonneg hnonneg
  have hancscale : (dyadicAncestor R n).scale = Q.scale := by
    rw [dyadicAncestor_scale, hn]
    ring
  have hsubset := dyadicCube_subset_ancestor R n
  obtain ⟨x, hxQ, hxR⟩ := hint
  apply dyadicIndex_eq_of_same_scale_intersect hancscale
  exact ⟨x, hsubset hxR, hxQ⟩

/-- Half-open geometric cube represented by a dyadic index. -/
@[expose]
def dyadicCubeSet (Q : DyadicIndex) : Set Vec3 :=
  dyadicCube Q.scale Q.corner

/-- Geometric cube corresponding to the immediate dyadic parent. -/
def dyadicParentSet (Q : DyadicIndex) : Set Vec3 :=
  dyadicCubeSet (dyadicParent Q)

/-- Signed average of a scalar function on a dyadic cube. -/
@[expose]
def dyadicAverage (F : Vec3 → ℝ) (Q : DyadicIndex) : ℝ :=
  ⨍ x in dyadicCubeSet Q, F x

/-- Average absolute value on a dyadic cube, used in the stopping criterion. -/
@[expose]
def dyadicAbsAverage (F : Vec3 → ℝ) (Q : DyadicIndex) : ℝ :=
  ⨍ x in dyadicCubeSet Q, |F x|

/-- Extended nonnegative integral of the absolute value for the dyadic decomposition. -/
@[expose]
def dyadicL1Norm (F : Vec3 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal |F x|

/-- Membership in the union of a chosen family of dyadic cubes. -/
@[expose]
def dyadicCubeMember (D : Set DyadicIndex) (x : Vec3) : Prop :=
  ∃ Q, Q ∈ D ∧ x ∈ dyadicCubeSet Q

/-- Good part obtained by replacing the function by its average on each selected cube. -/
@[expose] noncomputable def dyadicGoodPart (F : Vec3 → ℝ) (D : Set DyadicIndex) : Vec3 → ℝ := by
  classical
  exact fun x => if hx : dyadicCubeMember D x then
    dyadicAverage F (Classical.choose hx)
  else F x

/-- Mean-zero bad part supported on one selected dyadic cube. -/
@[expose]
def dyadicBadPart (F : Vec3 → ℝ) (Q : DyadicIndex) : Vec3 → ℝ :=
  (dyadicCubeSet Q).indicator (fun x => F x - dyadicAverage F Q)

/-- Stopping condition that the dyadic absolute average exceeds the chosen height. -/
def dyadicHigh (F : Vec3 → ℝ) (height : ℝ) (Q : DyadicIndex) : Prop :=
  height < dyadicAbsAverage F Q

/-- High-average cubes whose strict ancestors all fail the stopping condition. -/
def dyadicMaximalCubes (F : Vec3 → ℝ) (height : ℝ) : Set DyadicIndex :=
  {Q | dyadicHigh F height Q ∧
    ∀ n : ℕ, 0 < n → ¬dyadicHigh F height (dyadicAncestor Q n)}

private theorem dyadicAbsAverage_lt_of_l1
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height)
    {Q : DyadicIndex}
    (hvol : dyadicL1Norm F < ENNReal.ofReal height *
      volume (dyadicCube Q.scale Q.corner)) :
    dyadicAbsAverage F Q < height := by
  have hI : IntegrableOn (fun x => |F x|)
      (dyadicCube Q.scale Q.corner) volume := hF.norm.integrableOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (dyadicCube Q.scale Q.corner)]
      (fun x => |F x|) := ae_of_all _ (fun x => abs_nonneg _)
  have havg := ofReal_setAverage hI hnonneg
  have hmono :
      (∫⁻ x in dyadicCube Q.scale Q.corner, ENNReal.ofReal |F x|) ≤
        dyadicL1Norm F := by
    exact setLIntegral_le_lintegral _ _
  have hvol0 : volume (dyadicCube Q.scale Q.corner) ≠ 0 := by
    rw [volume_dyadicCube_eq_pow]
    positivity
  have hvoltop : volume (dyadicCube Q.scale Q.corner) ≠ ∞ := by
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  have hdiv :
      (∫⁻ x in dyadicCube Q.scale Q.corner, ENNReal.ofReal |F x|) /
          volume (dyadicCube Q.scale Q.corner) < ENNReal.ofReal height := by
    apply (ENNReal.div_lt_iff (Or.inl hvol0) (Or.inl hvoltop)).2
    exact hmono.trans_lt hvol
  have hreal : ENNReal.ofReal (dyadicAbsAverage F Q) < ENNReal.ofReal height := by
    change ENNReal.ofReal (⨍ x in dyadicCube Q.scale Q.corner, |F x|) <
      ENNReal.ofReal height
    rw [havg]
    exact hdiv
  exact (ENNReal.ofReal_lt_ofReal_iff hheight).mp hreal

private theorem dyadicL1Norm_ne_top {F : Vec3 → ℝ} (hF : Integrable F) :
    dyadicL1Norm F ≠ ∞ := by
  rw [dyadicL1Norm]
  have h := ofReal_integral_norm_eq_lintegral_enorm hF
  have h' : (∫⁻ x, ENNReal.ofReal |F x|) =
      ENNReal.ofReal (∫ x, ‖F x‖) := by
    calc
      (∫⁻ x, ENNReal.ofReal |F x|) = ∫⁻ x, ‖F x‖ₑ := by
        apply lintegral_congr
        intro x
        rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
        simp [Real.norm_eq_abs]
      _ = ENNReal.ofReal (∫ x, ‖F x‖) := h.symm
  rw [h']
  exact ENNReal.ofReal_ne_top

private theorem eventually_ancestor_average_lt
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height)
    (Q : DyadicIndex) :
    ∀ᶠ n : ℕ in atTop,
      dyadicAbsAverage F (dyadicAncestor Q n) < height := by
  have hLtop : dyadicL1Norm F ≠ ∞ := dyadicL1Norm_ne_top hF
  have hpowR : Tendsto (fun n : ℕ => (8 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (8 : ℝ)) (by norm_num)
  have hpowE : Tendsto (fun n : ℕ => ENNReal.ofReal ((8 : ℝ) ^ n)) atTop
      (𝓝 ∞) := ENNReal.tendsto_ofReal_nhds_top.mpr hpowR
  have hpowE' : Tendsto (fun n : ℕ => (8 : ℝ≥0∞) ^ n) atTop (𝓝 ∞) := by
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_ofNat] using hpowE
  have hV0 : volume (dyadicCube Q.scale Q.corner) ≠ 0 := by
    rw [volume_dyadicCube_eq_pow]
    positivity
  have hvol : Tendsto
      (fun n : ℕ => volume (dyadicCube (dyadicAncestor Q n).scale
        (dyadicAncestor Q n).corner)) atTop (𝓝 ∞) := by
    have htemp := ENNReal.Tendsto.mul_const hpowE'
      (b := volume (dyadicCube Q.scale Q.corner)) (Or.inl ENNReal.top_ne_zero)
    simpa only [volume_dyadicAncestor, ENNReal.top_mul hV0] using htemp
  have hmul : Tendsto
      (fun n : ℕ => ENNReal.ofReal height *
        volume (dyadicCube (dyadicAncestor Q n).scale
          (dyadicAncestor Q n).corner)) atTop (𝓝 ∞) := by
    have htemp := ENNReal.Tendsto.const_mul hvol (a := ENNReal.ofReal height)
      (Or.inl ENNReal.top_ne_zero)
    have hpos : ENNReal.ofReal height ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hheight).ne'
    simpa only [ENNReal.mul_top hpos] using htemp
  have hev : ∀ᶠ n : ℕ in atTop,
      dyadicL1Norm F < ENNReal.ofReal height *
        volume (dyadicCube (dyadicAncestor Q n).scale
          (dyadicAncestor Q n).corner) := by
    exact (ENNReal.nhds_top_basis.tendsto_right_iff.mp hmul)
      (dyadicL1Norm F) (lt_top_iff_ne_top.mpr hLtop)
  filter_upwards [hev] with n hn
  exact dyadicAbsAverage_lt_of_l1 hF hheight hn

private theorem exists_ancestor_average_le
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height)
    (Q : DyadicIndex) :
    ∃ n : ℕ, dyadicAbsAverage F (dyadicAncestor Q n) ≤ height := by
  obtain ⟨n, hn⟩ := (eventually_ancestor_average_lt hF hheight Q).exists
  exact ⟨n, hn.le⟩

private theorem exists_maximal_cube_super
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height)
    {Q : DyadicIndex} (hQ : dyadicHigh F height Q) :
    ∃ R, R ∈ dyadicMaximalCubes F height ∧
      dyadicCubeSet Q ⊆ dyadicCubeSet R := by
  classical
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (eventually_ancestor_average_lt hF hheight Q)
  let P : ℕ → Prop := fun n ↦
    dyadicHigh F height (dyadicAncestor Q n)
  have hP0 : P 0 := by
    simpa [P, dyadicAncestor] using hQ
  let m : ℕ := Nat.findGreatest P N
  have hmP : P m := by
    dsimp [m]
    exact Nat.findGreatest_spec (P := P) (by omega) hP0
  have hm_max : ∀ n : ℕ, m < n → ¬P n := by
    intro n hmn
    by_cases hnN : n ≤ N
    · exact Nat.findGreatest_is_greatest hmn hnN
    · have hNn : N ≤ n := le_of_not_ge hnN
      have hlow := hN n hNn
      exact fun hhigh => (not_lt_of_ge hlow.le) hhigh
  refine ⟨dyadicAncestor Q m, ?_, dyadicCube_subset_ancestor Q m⟩
  refine ⟨?_, ?_⟩
  · exact hmP
  · intro n hn hhigh
    have hhigh' : P (m + n) := by
      change dyadicHigh F height (dyadicAncestor Q (m + n))
      rw [← dyadicAncestor_add]
      exact hhigh
    exact hm_max (m + n) (by omega) hhigh'

private theorem dyadicAbsAverage_le_eight_parent
    {F : Vec3 → ℝ} (hF : Integrable F) (Q : DyadicIndex) :
    dyadicAbsAverage F Q ≤ 8 * dyadicAbsAverage F (dyadicParent Q) := by
  have hQint : IntegrableOn (fun x => |F x|) (dyadicCubeSet Q) volume :=
    hF.norm.integrableOn
  have hPint : IntegrableOn (fun x => |F x|)
      (dyadicCubeSet (dyadicParent Q)) volume := hF.norm.integrableOn
  have hmono :
      (∫ x in dyadicCubeSet Q, |F x|) ≤
        ∫ x in dyadicCubeSet (dyadicParent Q), |F x| := by
    apply setIntegral_mono_set hPint
      (ae_of_all _ (fun x => abs_nonneg (F x)))
    exact ae_of_all _ (fun x hx => dyadicCube_subset_parent Q hx)
  have hvol0 : volume (dyadicCubeSet Q) ≠ 0 := by
    change volume (dyadicCube Q.scale Q.corner) ≠ 0
    rw [volume_dyadicCube_eq_pow]
    positivity
  have hvoltop : volume (dyadicCubeSet Q) ≠ ∞ := by
    change volume (dyadicCube Q.scale Q.corner) ≠ ∞
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  have hvpos : 0 < (volume (dyadicCubeSet Q)).toReal :=
    ENNReal.toReal_pos hvol0 hvoltop
  have hvolreal :
      (volume (dyadicCubeSet (dyadicParent Q))).toReal =
        8 * (volume (dyadicCubeSet Q)).toReal := by
    change (volume (dyadicCube (dyadicParent Q).scale
      (dyadicParent Q).corner)).toReal =
        8 * (volume (dyadicCube Q.scale Q.corner)).toReal
    rw [dyadicParent_volume_ratio, ENNReal.toReal_mul]
    norm_num
  have havgQ : dyadicAbsAverage F Q =
      (volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet Q, |F x|) := by
    rw [dyadicAbsAverage, setAverage_eq]
    rfl
  have havgP : dyadicAbsAverage F (dyadicParent Q) =
      (volume (dyadicCubeSet (dyadicParent Q))).toReal⁻¹ *
        (∫ x in dyadicCubeSet (dyadicParent Q), |F x|) := by
    rw [dyadicAbsAverage, setAverage_eq]
    rfl
  rw [havgQ, havgP, hvolreal]
  calc
    (volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet Q, |F x|) ≤
      (volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet (dyadicParent Q), |F x|) := by
          gcongr
    _ = 8 * ((8 * (volume (dyadicCubeSet Q)).toReal)⁻¹ *
        (∫ x in dyadicCubeSet (dyadicParent Q), |F x|)) := by
          field_simp

private theorem dyadicMaximal_volume_sum_le
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height)
    (D : Set DyadicIndex)
    (hDdisjoint : D.Pairwise (Function.onFun Disjoint dyadicCubeSet))
    (hDhigh : ∀ Q ∈ D, dyadicHigh F height Q) :
    (∑' Q : {Q // Q ∈ D}, volume (dyadicCubeSet Q.1)) ≤
      dyadicL1Norm F / ENNReal.ofReal height := by
  have hheight0 : ENNReal.ofReal height ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hheight).ne'
  have hheighttop : ENNReal.ofReal height ≠ ∞ := ENNReal.ofReal_ne_top
  have hcondition (Q : {Q // Q ∈ D}) :
      ENNReal.ofReal height * volume (dyadicCubeSet Q.1) ≤
        ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x| := by
    have hI : IntegrableOn (fun x => |F x|) (dyadicCubeSet Q.1) volume :=
      hF.norm.integrableOn
    have hnonneg : 0 ≤ᵐ[volume.restrict (dyadicCubeSet Q.1)]
        (fun x => |F x|) := ae_of_all _ (fun x => abs_nonneg _)
    have hnonnegavg : 0 ≤ dyadicAbsAverage F Q.1 := by
      exact average_nonneg_of_ae hnonneg
    have havg := ofReal_setAverage hI hnonneg
    have hlt : ENNReal.ofReal height ≤
        ENNReal.ofReal (dyadicAbsAverage F Q.1) := by
      exact (ENNReal.ofReal_le_ofReal_iff hnonnegavg).2 (hDhigh Q.1 Q.2).le
    change ENNReal.ofReal height ≤
      ENNReal.ofReal (⨍ x in dyadicCubeSet Q.1, |F x|) at hlt
    rw [havg] at hlt
    have hvol0 : volume (dyadicCubeSet Q.1) ≠ 0 := by
      change volume (dyadicCube Q.1.scale Q.1.corner) ≠ 0
      rw [volume_dyadicCube_eq_pow]
      positivity
    have hvoltop : volume (dyadicCubeSet Q.1) ≠ ∞ := by
      change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
      rw [volume_dyadicCube_eq_pow]
      exact ENNReal.ofReal_ne_top
    exact (ENNReal.le_div_iff_mul_le (Or.inl hvol0) (Or.inl hvoltop)).mp hlt
  have hsum_integral :
      (∑' Q : {Q // Q ∈ D},
        ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) ≤
        dyadicL1Norm F := by
    calc
      (∑' Q : {Q // Q ∈ D},
          ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) =
          ∫⁻ x in ⋃ Q : {Q // Q ∈ D}, dyadicCubeSet Q.1,
            ENNReal.ofReal |F x| := by
        symm
        apply lintegral_iUnion
        · intro Q
          exact dyadicCube_measurable Q.1.scale Q.1.corner
        · intro Q R hQR
          exact hDdisjoint Q.2 R.2 (Subtype.coe_ne_coe.mpr hQR)
      _ ≤ dyadicL1Norm F := by
        dsimp [dyadicL1Norm]
        gcongr
        exact MeasureTheory.Measure.restrict_le_self
  apply (ENNReal.le_div_iff_mul_le (Or.inl hheight0) (Or.inl hheighttop)).2
  calc
    (∑' Q : {Q // Q ∈ D}, volume (dyadicCubeSet Q.1)) *
        ENNReal.ofReal height =
      ∑' Q : {Q // Q ∈ D},
        ENNReal.ofReal height * volume (dyadicCubeSet Q.1) := by
          calc
            (∑' Q : {Q // Q ∈ D}, volume (dyadicCubeSet Q.1)) *
                ENNReal.ofReal height =
              ENNReal.ofReal height *
                (∑' Q : {Q // Q ∈ D}, volume (dyadicCubeSet Q.1)) := by
                  ac_rfl
            _ = ∑' Q : {Q // Q ∈ D},
                ENNReal.ofReal height * volume (dyadicCubeSet Q.1) := by
                  rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' Q : {Q // Q ∈ D},
        ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x| :=
      ENNReal.tsum_le_tsum (fun Q => hcondition Q)
    _ ≤ dyadicL1Norm F := hsum_integral

private theorem dyadicCube_subset_closedBall_center (k : ℤ) (a : DyadicCorner) :
    dyadicCube k a ⊆
      Metric.closedBall (dyadicCubeCenter k a) (dyadicScale k / 2) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have hx' := (mem_dyadicCube.mp hx) i
  change |x i - dyadicCubeCenter k a i| ≤ dyadicScale k / 2
  dsimp [dyadicCubeCenter]
  rw [abs_le]
  constructor <;> nlinarith only [hx'.1, hx'.2, hs]

private theorem dyadicCube_ae_eq_closedBall_center (k : ℤ) (a : DyadicCorner) :
    dyadicCube k a =ᵐ[volume]
      Metric.closedBall (dyadicCubeCenter k a) (dyadicScale k / 2) := by
  apply ae_eq_of_subset_of_measure_ge (dyadicCube_subset_closedBall_center k a)
  · rw [Real.volume_pi_closedBall _
      (by exact div_nonneg (dyadicScale_pos k).le (by norm_num)),
      volume_dyadicCube]
    rw [← ENNReal.ofReal_pow (dyadicScale_pos k).le 3]
    apply ENNReal.ofReal_le_ofReal
    norm_num [Fintype.card_fin]
    calc
      (2 * (dyadicScale k / 2)) ^ 3 = dyadicScale k ^ 3 := by ring
      _ ≤ dyadicScale k ^ 3 := le_rfl
  · exact (dyadicCube_measurable k a).nullMeasurableSet
  · rw [Real.volume_pi_closedBall _
      (by exact div_nonneg (dyadicScale_pos k).le (by norm_num))]
    exact ENNReal.ofReal_ne_top

private theorem dyadic_maximal_off_cubes_le_ae
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height) :
    ∀ᵐ x ∂volume,
      x ∉ ⋃ Q ∈ dyadicMaximalCubes F height, dyadicCubeSet Q →
        |F x| ≤ height := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average volume
    (hF.norm.locallyIntegrable) 1
  filter_upwards [hdiff] with x hx
  intro hxoff
  have hcube_le (n : ℕ) :
      dyadicAbsAverage F
          ⟨(n : ℤ), dyadicCorner (n : ℤ) x⟩ ≤ height := by
    apply le_of_not_gt
    intro hgt
    obtain ⟨R, hR, hsub⟩ := exists_maximal_cube_super hF hheight hgt
    apply hxoff
    refine mem_iUnion.2 ⟨R, mem_iUnion.2 ⟨hR, ?_⟩⟩
    exact hsub (mem_dyadicCube_of_corner (n : ℤ) x)
  have hscale_nat (n : ℕ) :
      dyadicScale (n : ℤ) = (1 / 2 : ℝ) ^ n := by
    dsimp [dyadicScale]
    rw [zpow_neg, zpow_natCast, one_div]
    exact (inv_pow 2 n).symm
  have hdelta : Tendsto
      (fun n : ℕ => dyadicScale (n : ℤ) / 2) atTop (𝓝[>] 0) := by
    have hmain : Tendsto
        (fun n : ℕ => ((1 / 2 : ℝ) ^ n) / 2) atTop (𝓝 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
          (by norm_num) (by norm_num)).div_const 2
    have hmain' : Tendsto
        (fun n : ℕ => dyadicScale (n : ℤ) / 2) atTop (𝓝 0) := by
      simpa only [hscale_nat] using hmain
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmain', Filter.Eventually.of_forall ?_⟩
    intro n
    exact div_pos (dyadicScale_pos (n : ℤ)) (by norm_num)
  have hmem : ∀ᶠ n : ℕ in atTop,
      x ∈ Metric.closedBall
        (dyadicCubeCenter (n : ℤ) (dyadicCorner (n : ℤ) x))
        (1 * (dyadicScale (n : ℤ) / 2)) := by
    exact Filter.Eventually.of_forall (fun n => by
      rw [one_mul]
      exact dyadicCube_subset_closedBall_center (n : ℤ) (dyadicCorner (n : ℤ) x)
        (mem_dyadicCube_of_corner (n : ℤ) x))
  have hlim := hx
      (fun n : ℕ => dyadicCubeCenter (n : ℤ) (dyadicCorner (n : ℤ) x))
      (fun n : ℕ => dyadicScale (n : ℤ) / 2) hdelta hmem
  have havg_le : ∀ᶠ n : ℕ in atTop,
      (⨍ y in Metric.closedBall
        (dyadicCubeCenter (n : ℤ) (dyadicCorner (n : ℤ) x))
        (dyadicScale (n : ℤ) / 2), |F y|) ≤ height := by
    exact Filter.Eventually.of_forall (fun n => by
      have heq := dyadicCube_ae_eq_closedBall_center
        (n : ℤ) (dyadicCorner (n : ℤ) x)
      have heq' :
          (⨍ y in dyadicCube (n : ℤ) (dyadicCorner (n : ℤ) x), |F y|) =
            (⨍ y in Metric.closedBall
              (dyadicCubeCenter (n : ℤ) (dyadicCorner (n : ℤ) x))
              (dyadicScale (n : ℤ) / 2), |F y|) :=
        setAverage_congr (μ := volume) (f := fun y => |F y|) heq
      rw [← heq']
      exact hcube_le n)
  simpa [Real.norm_eq_abs] using le_of_tendsto hlim havg_le

private theorem dyadicMaximal_pairwise
    {F : Vec3 → ℝ} {height : ℝ} :
    (dyadicMaximalCubes F height).Pairwise
      (Function.onFun Disjoint dyadicCubeSet) := by
  intro Q hQ R hR hQR
  rcases hQ with ⟨hQhigh, hQmax⟩
  rcases hR with ⟨hRhigh, hRmax⟩
  apply Set.disjoint_left.2
  intro x hxQ hxR
  have hint :
      (dyadicCube Q.scale Q.corner ∩
        dyadicCube R.scale R.corner).Nonempty := ⟨x, hxQ, hxR⟩
  rcases le_total Q.scale R.scale with hscale | hscale
  · let n : ℕ := Int.toNat (R.scale - Q.scale)
    have heq : dyadicAncestor R n = Q := by
      dsimp [n]
      exact dyadicAncestor_eq_of_intersect_of_scale_le hscale hint
    by_cases hn : n = 0
    · have hQR' : Q = R := by
        have hRQ : R = Q := by
          rw [hn, dyadicAncestor] at heq
          exact heq
        exact hRQ.symm
      exact hQR hQR'
    · have hhigh : dyadicHigh F height (dyadicAncestor R n) := by
        rw [heq]
        exact hQhigh
      exact hRmax n (Nat.pos_of_ne_zero hn) hhigh
  · let n : ℕ := Int.toNat (Q.scale - R.scale)
    have heq : dyadicAncestor Q n = R := by
      dsimp [n]
      have hint' :
          (dyadicCube R.scale R.corner ∩
            dyadicCube Q.scale Q.corner).Nonempty := by
        exact ⟨x, hxR, hxQ⟩
      exact dyadicAncestor_eq_of_intersect_of_scale_le hscale hint'
    by_cases hn : n = 0
    · have hQR' : Q = R := by
        rw [hn, dyadicAncestor] at heq
        exact heq
      exact hQR hQR'
    · have hhigh : dyadicHigh F height (dyadicAncestor Q n) := by
        rw [heq]
        exact hRhigh
      exact hQmax n (Nat.pos_of_ne_zero hn) hhigh

theorem abs_dyadicAverage_le_dyadicAbsAverage
    {F : Vec3 → ℝ} (Q : DyadicIndex) :
    |dyadicAverage F Q| ≤ dyadicAbsAverage F Q := by
  have hvnonneg : 0 ≤ (volume (dyadicCubeSet Q)).toReal⁻¹ := by
    positivity
  have havgF : dyadicAverage F Q =
      (volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet Q, F x) := by
    rw [dyadicAverage, setAverage_eq]
    rfl
  have havgN : dyadicAbsAverage F Q =
      (volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet Q, |F x|) := by
    rw [dyadicAbsAverage, setAverage_eq]
    rfl
  rw [havgF, havgN]
  calc
    |(volume (dyadicCubeSet Q)).toReal⁻¹ *
        (∫ x in dyadicCubeSet Q, F x)| =
      (volume (dyadicCubeSet Q)).toReal⁻¹ *
        |∫ x in dyadicCubeSet Q, F x| := by
          rw [abs_mul, abs_of_nonneg hvnonneg]
    _ ≤ (volume (dyadicCubeSet Q)).toReal⁻¹ *
      (∫ x in dyadicCubeSet Q, |F x|) := by
      gcongr
      exact MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (dyadicCubeSet Q)) (fun x : Vec3 => F x)

private theorem dyadic_maximal_good_part_bound_ae
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height) :
    ∀ᵐ x ∂volume,
      |dyadicGoodPart F (dyadicMaximalCubes F height) x| ≤ 8 * height := by
  have hoff := dyadic_maximal_off_cubes_le_ae hF hheight
  filter_upwards [hoff] with x hxoff
  by_cases hxmem : dyadicCubeMember (dyadicMaximalCubes F height) x
  · have hchoose := Classical.choose_spec hxmem
    have hparent :
        dyadicAbsAverage F (dyadicParent (Classical.choose hxmem)) ≤ height := by
      apply le_of_not_gt
      intro hgt
      exact hchoose.1.2 1 Nat.zero_lt_one hgt
    have hbound :
        |dyadicAverage F (Classical.choose hxmem)| ≤ 8 * height := by
      calc
        |dyadicAverage F (Classical.choose hxmem)| ≤
            dyadicAbsAverage F (Classical.choose hxmem) :=
          abs_dyadicAverage_le_dyadicAbsAverage _
        _ ≤ 8 * dyadicAbsAverage F
            (dyadicParent (Classical.choose hxmem)) :=
          dyadicAbsAverage_le_eight_parent hF _
        _ ≤ 8 * height := by
          gcongr
    simpa [dyadicGoodPart, hxmem] using hbound
  · have hxoff' :
        x ∉ ⋃ Q ∈ dyadicMaximalCubes F height, dyadicCubeSet Q := by
      intro hxU
      rcases mem_iUnion.mp hxU with ⟨Q, hxU⟩
      rcases mem_iUnion.mp hxU with ⟨hQ, hxQ⟩
      exact hxmem ⟨Q, hQ, hxQ⟩
    have hbound : |F x| ≤ 8 * height := by
      calc
        |F x| ≤ height := hxoff hxoff'
        _ ≤ 8 * height := by nlinarith only [hheight]
    simpa [dyadicGoodPart, hxmem] using hbound

theorem dyadicMaximalCubes_spec
    {F : Vec3 → ℝ} (hF : Integrable F) {height : ℝ} (hheight : 0 < height) :
    let D := dyadicMaximalCubes F height
    D.Countable ∧
      D.Pairwise (Function.onFun Disjoint dyadicCubeSet) ∧
      (∀ Q ∈ D, height < dyadicAbsAverage F Q) ∧
      (∀ Q ∈ D, dyadicAbsAverage F Q ≤ 8 * height) ∧
      (∀ Q ∈ D, dyadicAbsAverage F (dyadicParent Q) ≤ height) ∧
      ((∑' Q : {Q // Q ∈ D}, volume (dyadicCubeSet Q.1)) ≤
        dyadicL1Norm F / ENNReal.ofReal height) ∧
      (∀ᵐ x ∂volume,
        x ∉ ⋃ Q ∈ D, dyadicCubeSet Q → |F x| ≤ height) ∧
      (∀ᵐ x ∂volume,
        |dyadicGoodPart F D x| ≤ 8 * height) := by
  dsimp
  let D := dyadicMaximalCubes F height
  have hDcount : D.Countable :=
    Set.Countable.mono (fun _ _ => Set.mem_univ _) Set.countable_univ
  have hDpair : D.Pairwise (Function.onFun Disjoint dyadicCubeSet) := by
    exact dyadicMaximal_pairwise
  have hDgt : ∀ Q ∈ D, height < dyadicAbsAverage F Q := by
    intro Q hQ
    exact hQ.1
  have hDparent : ∀ Q ∈ D,
      dyadicAbsAverage F (dyadicParent Q) ≤ height := by
    intro Q hQ
    apply le_of_not_gt
    intro hgt
    exact hQ.2 1 Nat.zero_lt_one hgt
  have hDle : ∀ Q ∈ D, dyadicAbsAverage F Q ≤ 8 * height := by
    intro Q hQ
    have hparent := hDparent Q hQ
    calc
      dyadicAbsAverage F Q ≤
          8 * dyadicAbsAverage F (dyadicParent Q) :=
        dyadicAbsAverage_le_eight_parent hF Q
      _ ≤ 8 * height := by gcongr
  refine ⟨hDcount, hDpair, hDgt, hDle, hDparent, ?_, ?_, ?_⟩
  · exact dyadicMaximal_volume_sum_le hF hheight D hDpair hDgt
  · exact dyadic_maximal_off_cubes_le_ae hF hheight
  · exact dyadic_maximal_good_part_bound_ae hF hheight

/-- Dyadic Calderón–Zygmund decomposition with quantitative good and bad part estimates. -/
structure CZDecomposition (F : Vec3 → ℝ) (height : ℝ) where
  height_pos : 0 < height
  integrable : Integrable F
  /-- Selected dyadic cubes supporting the bad pieces of the decomposition. -/
  cubes : Set DyadicIndex
  cubes_countable : cubes.Countable
  cubes_pairwise_disjoint : cubes.Pairwise (Function.onFun Disjoint dyadicCubeSet)
  cube_average_gt : ∀ Q ∈ cubes, height < dyadicAbsAverage F Q
  cube_average_le : ∀ Q ∈ cubes, dyadicAbsAverage F Q ≤ 8 * height
  parent_average_le : ∀ Q ∈ cubes, dyadicAbsAverage F (dyadicParent Q) ≤ height
  cube_volume_sum_le :
    (∑' Q : {Q // Q ∈ cubes}, volume (dyadicCubeSet Q.1)) ≤
      dyadicL1Norm F / ENNReal.ofReal height
  off_cubes_le_ae : ∀ᵐ x ∂volume,
    x ∉ ⋃ Q ∈ cubes, dyadicCubeSet Q → |F x| ≤ height
  good_part_bound_ae : ∀ᵐ x ∂volume,
    |dyadicGoodPart F cubes x| ≤ 8 * height
  good_part_l1_le :
    (∫⁻ x, ENNReal.ofReal |dyadicGoodPart F cubes x|) ≤ dyadicL1Norm F
  bad_part_mean_zero : ∀ Q ∈ cubes,
    ∫ x in dyadicCubeSet Q, dyadicBadPart F Q x = 0
  bad_part_l1_sum_le :
    (∑' Q : {Q // Q ∈ cubes},
      ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |dyadicBadPart F Q.1 x|) ≤
        2 * dyadicL1Norm F

theorem dyadicGoodPart_eq_of_not_mem {F : Vec3 → ℝ} {D : Set DyadicIndex}
    {x : Vec3} (hx : ¬dyadicCubeMember D x) :
    dyadicGoodPart F D x = F x := by
  simp [dyadicGoodPart, hx]

theorem dyadicBadPart_support_subset {F : Vec3 → ℝ} (Q : DyadicIndex) :
    Function.support (dyadicBadPart F Q) ⊆ dyadicCubeSet Q := by
  intro x hx
  by_contra hxc
  simp [dyadicBadPart, hxc] at hx

theorem CZDecomposition.off_cubes_bound {F : Vec3 → ℝ} {height : ℝ}
    (D : CZDecomposition F height) :
    ∀ᵐ x ∂volume,
      x ∉ ⋃ Q ∈ D.cubes, dyadicCubeSet Q → |F x| ≤ height :=
  D.off_cubes_le_ae

theorem CZDecomposition.good_part_bound {F : Vec3 → ℝ} {height : ℝ}
    (D : CZDecomposition F height) :
    ∀ᵐ x ∂volume, |dyadicGoodPart F D.cubes x| ≤ 8 * height :=
  D.good_part_bound_ae

theorem CZDecomposition.bad_part_mean {F : Vec3 → ℝ} {height : ℝ}
    (D : CZDecomposition F height) {Q : DyadicIndex} (hQ : Q ∈ D.cubes) :
    ∫ x in dyadicCubeSet Q, dyadicBadPart F Q x = 0 :=
  D.bad_part_mean_zero Q hQ

end CKN.Foundation.Euclidean
