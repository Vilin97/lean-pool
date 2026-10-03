/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.RecursionIncrement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.FlowTransport

/-! The analytic induction behind the first stream-regularity increment estimate. -/

@[expose] public section

open MeasureTheory Homogenization Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

/-- Rational weight used in the joint derivative induction. -/
def Section2JointInduction.section2Weight (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3

theorem Section2JointInduction.nat_add_three_le_three_mul_two_pow (k : ℕ) :
    k + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k + 1 + 3 ≤ 2 * (k + 3) := by omega
        _ ≤ 2 * (3 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 3 * 2 ^ (k + 1) := by rw [pow_succ]; omega

theorem Section2JointInduction.section2_weight_half_power (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ^ (n - 2) ≤ 3 * Section2JointInduction.section2Weight n := by
  let k := n - 2
  have hidx : k + 2 = n := by dsimp [k]; omega
  have hnat := Section2JointInduction.nat_add_three_le_three_mul_two_pow k
  have hnatR : (n : ℝ) + 1 ≤ 3 * (2 : ℝ) ^ k := by
    calc
      (n : ℝ) + 1 = ((k + 2 : ℕ) : ℝ) + 1 := by rw [← hidx]
      _ = (k : ℝ) + 3 := by push_cast; ring
      _ ≤ 3 * (2 : ℝ) ^ k := by exact_mod_cast hnat
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hleft : (1 : ℝ) / (2 : ℝ) ^ k ≤ 3 / ((n : ℝ) + 1) := by
    apply (div_le_iff₀ hp).2
    field_simp [ne_of_gt hn1]
    nlinarith [hnatR]
  have hweight : 3 / ((n : ℝ) + 1) ≤ 3 * Section2JointInduction.section2Weight n := by
    apply (div_le_iff₀ hn1).2
    dsimp [Section2JointInduction.section2Weight]
    have hnreal : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
    field_simp
    nlinarith [hsq]
  have hpow : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by
    rw [one_div_pow]
  simpa [k, hpow] using hleft.trans hweight

theorem Section2JointInduction.section2_stream_slice_smooth {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hΦ := (streamSeq_isAdmissible hseq m).1
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (Φ m) (t, x))
  exact hΦ.comp hmap

theorem Section2JointInduction.section2_amplitude_increment_budget {β : ℝ} {I : Ingredients β}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M) (m : ℕ) (hm : 1 ≤ m) :
    30 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
        ((9 / 8) * R (m - 1) + 20 * Real.pi / epsilon β I.Λ m) ^ 2 ≤
      M m - M (m - 1) := by
  let E := epsilon β I.Λ m
  let Rp := R (m - 1)
  let Rc := (9 / 8) * Rp + 20 * Real.pi / E
  have hE : 0 < E := by
    dsimp [E]
    exact Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hRp : 0 ≤ Rp := section2_radius_nonneg hscales (m - 1)
  have ha : 0 ≤ a β I.Λ m := Real.rpow_nonneg (le_of_lt hE) _
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hgeom : 30 * E ^ 2 * Rc ^ 2 ≤ 128 * E ^ 2 * Rp ^ 2 + 2 ^ 18 := by
    have hsum : E * Rc = (9 / 8 : ℝ) * (E * Rp) + 20 * Real.pi := by
      dsimp [Rc]
      field_simp [ne_of_gt hE]
    have hsq : (E * Rc) ^ 2 ≤
        2 * ((9 / 8 : ℝ) * (E * Rp)) ^ 2 + 2 * (20 * Real.pi) ^ 2 := by
      rw [hsum]
      nlinarith [sq_nonneg ((9 / 8 : ℝ) * (E * Rp) - 20 * Real.pi)]
    calc
      30 * E ^ 2 * Rc ^ 2 = 30 * (E * Rc) ^ 2 := by ring
      _ ≤
          60 * ((9 / 8 : ℝ) * (E * Rp)) ^ 2 + 60 * (20 * Real.pi) ^ 2 := by
        nlinarith [hsq]
      _ ≤ 128 * E ^ 2 * Rp ^ 2 + 2 ^ 18 := by
        nlinarith [sq_nonneg (E * Rp), hpi]
  have hMdiff : M m - M (m - 1) =
      2 ^ 7 * a β I.Λ m * E ^ 2 * Rp ^ 2 + 2 ^ 18 * a β I.Λ m := by
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hstep := hscales.amplitude_step (m - 1)
    rw [hmidx] at hstep
    rw [hstep]
    dsimp [E, Rp]
    ring
  rw [hMdiff]
  have hmul := mul_le_mul_of_nonneg_left hgeom ha
  calc
    30 * a β I.Λ m * E ^ 2 * Rc ^ 2 = a β I.Λ m *
        (30 * E ^ 2 * Rc ^ 2) := by ring
    _ ≤ a β I.Λ m * (128 * E ^ 2 * Rp ^ 2 + 2 ^ 18) := hmul
    _ = 2 ^ 7 * a β I.Λ m * E ^ 2 * Rp ^ 2 + 2 ^ 18 * a β I.Λ m := by ring

/-- One induction step for `e.indyhyp`. The App. B.2 inverse estimate is
applied only after the previous-scale hypothesis has been established. -/
theorem section2_stream_induction_step {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1)) :
    Section2StreamInductionHypothesis (Φ := Φ) R M m := by
  intro t n hn
  let Rp := R (m - 1)
  let Rm := R m
  let Rc := (9 / 8) * Rp + 20 * Real.pi / epsilon β I.Λ m
  let E := epsilon β I.Λ m
  let P := Section2JointInduction.section2Weight n
  have hRp : 0 < Rp := section2_radius_pos hscales (m - 1)
  have hRm : 0 < Rm := section2_radius_pos hscales m
  have hE : 0 < E := by
    dsimp [E]
    exact Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hRc : 0 < Rc := by
    dsimp [Rc]
    positivity
  have hMprev : 0 < M (m - 1) := section2_amplitude_pos hscales (m - 1)
  have hM : 0 < M m := section2_amplitude_pos hscales m
  have hMmono : M (m - 1) ≤ M m := by
    have hstep := hscales.amplitude_step (m - 1)
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hmidx] at hstep
    rw [hstep]
    have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m)
    have ha : 0 ≤ a β I.Λ m := Real.rpow_nonneg he.le _
    have hRnonneg := section2_radius_nonneg hscales (m - 1)
    have hinc : 0 ≤ 2 ^ 7 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
        R (m - 1) ^ 2 + 2 ^ 18 * a β I.Λ m := by positivity
    linarith
  have hP : 0 < P := by
    dsimp [P, Section2JointInduction.section2Weight]
    positivity
  have hRrecM : Rm = (9 / 4) * Rp + 2 ^ 7 * E⁻¹ := by
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    simpa [Rm, Rp, E, hmidx] using hscales.radius_step (m - 1)
  have hRtwice : 2 * Rc ≤ Rm := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hraw : 40 * Real.pi ≤ (128 : ℝ) := by norm_num at hpi ⊢; linarith
    rw [hRrecM]
    have hdiv : 40 * Real.pi / E ≤ 128 * E⁻¹ := by
      have hdiv' := div_le_div_of_nonneg_right hraw hE.le
      simpa [div_eq_mul_inv] using hdiv'
    dsimp [Rc]
    rw [show 2 * ((9 / 8 : ℝ) * Rp + 20 * Real.pi / E) =
      (9 / 4) * Rp + 40 * Real.pi / E by ring]
    nlinarith [hdiv]
  have hRple : Rp ≤ Rm := by
    have hRcompLower : (9 / 8 : ℝ) * Rp ≤ Rc := by
      dsimp [Rc]
      have hpos : 0 < 20 * Real.pi / E := by positivity
      linarith
    nlinarith
  have hRprevRatio : 0 ≤ Rp / Rm ∧ Rp / Rm ≤ 1 := by
    constructor
    · exact (div_pos hRp hRm).le
    · exact (div_le_one hRm).2 hRple
  have hRcompRatio : 0 ≤ Rc / Rm ∧ Rc / Rm ≤ 1 / 2 := by
    constructor
    · exact (div_pos hRc hRm).le
    · exact (div_le_iff₀ hRm).2 (by nlinarith [hRtwice])
  have hΦprev : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) t) :=
    Section2JointInduction.section2_stream_slice_smooth hseq (m - 1) t
  have hΦm : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    Section2JointInduction.section2_stream_slice_smooth hseq m t
  let Δ : Vec 2 → ℝ := fun x => Φ m t x - Φ (m - 1) t x
  have hΔ : ContDiff ℝ (⊤ : ℕ∞) Δ := by
    dsimp [Δ]
    exact hΦm.sub hΦprev
  have hprevBar : barNorm n Rp (Φ (m - 1) t) ≤
      ENNReal.ofReal (M (m - 1) * Rp⁻¹ ^ 2 * P) := by
    rw [barNorm_eq_snorm (Φ (m - 1) t) n Rp (hΦprev.of_le (by simp))]
    exact hprev t n hn
  have hincComp :=
    (stream_increment_bounds_at_scale hscales happB2 m hm hprev t n).1
  have hincBar : barNorm n Rc Δ ≤ ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
    change barNorm n Rc (Φ m t - Φ (m - 1) t) ≤ _
    simpa [Rc, E, Rp] using hincComp
  have hqprev_pow : (Rp / Rm) ^ (n - 2) ≤ 1 := by
    have hq := hRprevRatio
    exact pow_le_one₀ hq.1 hq.2
  have hqprev_id : Rp⁻¹ ^ 2 * (Rp / Rm) ^ n =
      Rm⁻¹ ^ 2 * (Rp / Rm) ^ (n - 2) := by
    have hnidx : n - 2 + 2 = n := by omega
    have hqpow : (Rp / Rm) ^ n =
        (Rp / Rm) ^ (n - 2) * (Rp / Rm) ^ 2 := by
      calc
        (Rp / Rm) ^ n = (Rp / Rm) ^ (n - 2 + 2) := by rw [hnidx]
        _ = (Rp / Rm) ^ (n - 2) * (Rp / Rm) ^ 2 := by rw [pow_add]
    rw [hqpow]
    have hqsq : (Rp / Rm) ^ 2 = Rp ^ 2 * Rm⁻¹ ^ 2 := by
      field_simp [hRm.ne']
    rw [hqsq]
    field_simp [hRp.ne', hRm.ne']
  have hprevReal : M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n ≤
      M (m - 1) * Rm⁻¹ ^ 2 * P := by
    have hcoef : 0 ≤ M (m - 1) * P * Rm⁻¹ ^ 2 := by positivity
    calc
      M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n =
          M (m - 1) * P * (Rp⁻¹ ^ 2 * (Rp / Rm) ^ n) := by ring
      _ = M (m - 1) * P * (Rm⁻¹ ^ 2 * (Rp / Rm) ^ (n - 2)) := by
        rw [hqprev_id]
      _ = (M (m - 1) * P * Rm⁻¹ ^ 2) * (Rp / Rm) ^ (n - 2) := by ring
      _ ≤
          M (m - 1) * P * Rm⁻¹ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hqprev_pow hcoef
      _ = M (m - 1) * Rm⁻¹ ^ 2 * P := by ring
  have hprevScaled : barNorm n Rm (Φ (m - 1) t) ≤
      ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) := by
    rw [barNorm_radius_change (hΦprev.of_le (by simp)) hRp hRm]
    have hqnonneg : 0 ≤ Rp / Rm := hRprevRatio.1
    have hKnonneg : 0 ≤ M (m - 1) * Rp⁻¹ ^ 2 * P := by positivity
    calc
      barNorm n Rp (Φ (m - 1) t) * ENNReal.ofReal (Rp / Rm) ^ n ≤
          ENNReal.ofReal (M (m - 1) * Rp⁻¹ ^ 2 * P) *
            ENNReal.ofReal (Rp / Rm) ^ n :=
        mul_le_mul_of_nonneg_right hprevBar (by positivity)
      _ = ENNReal.ofReal
          (M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n) := by
        rw [← ENNReal.ofReal_pow hqnonneg, ← ENNReal.ofReal_mul hKnonneg]
      _ ≤ ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) :=
        ENNReal.ofReal_le_ofReal hprevReal
  have hqcomp_pow : (Rc / Rm) ^ (n - 2) ≤ 3 * P := by
    have hsmall := Section2JointInduction.section2_weight_half_power n hn
    have hpow := pow_le_pow_left₀ hRcompRatio.1 hRcompRatio.2 (n - 2)
    exact hpow.trans hsmall
  have hqcomp_id : (Rc / Rm) ^ 2 = Rc ^ 2 * Rm⁻¹ ^ 2 := by
    field_simp [hRm.ne']
  have hbudget := Section2JointInduction.section2_amplitude_increment_budget hscales m hm
  have hincReal : 10 * a β I.Λ m * E ^ 2 * (Rc / Rm) ^ n ≤
      (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P := by
    have hnidx : n = (n - 2) + 2 := by omega
    rw [hnidx, pow_add, mul_comm ((Rc / Rm) ^ (n - 2)) ((Rc / Rm) ^ 2), hqcomp_id]
    have hfactor : 0 ≤ 10 * a β I.Λ m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2) := by
      have ha : 0 ≤ a β I.Λ m := Real.rpow_nonneg hE.le _
      positivity
    calc
      10 * a β I.Λ m * E ^ 2 *
          ((Rc ^ 2 * Rm⁻¹ ^ 2) * (Rc / Rm) ^ (n - 2)) =
        (10 * a β I.Λ m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2)) *
          (Rc / Rm) ^ (n - 2) := by ring
      _ ≤ (10 * a β I.Λ m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2)) * (3 * P) :=
        mul_le_mul_of_nonneg_left hqcomp_pow hfactor
      _ = (30 * a β I.Λ m * E ^ 2 * Rc ^ 2) * Rm⁻¹ ^ 2 * P := by ring
      _ ≤ (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hbudget' : 30 * a β I.Λ m * E ^ 2 * Rc ^ 2 ≤ M m - M (m - 1) := by
          simpa [E, Rc, Rp] using hbudget
        exact hbudget'
  have hincScaled : barNorm n Rm Δ ≤
      ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) := by
    rw [barNorm_radius_change (hΔ.of_le (by simp)) hRc hRm]
    have hqnonneg : 0 ≤ Rc / Rm := hRcompRatio.1
    have ha : 0 ≤ a β I.Λ m := Real.rpow_nonneg hE.le _
    have hKnonneg : 0 ≤ 10 * a β I.Λ m * E ^ 2 := by positivity
    calc
      barNorm n Rc Δ * ENNReal.ofReal (Rc / Rm) ^ n ≤
          ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) *
            ENNReal.ofReal (Rc / Rm) ^ n :=
        mul_le_mul_of_nonneg_right hincBar (by positivity)
      _ = ENNReal.ofReal
          (10 * a β I.Λ m * E ^ 2 * (Rc / Rm) ^ n) := by
        rw [← ENNReal.ofReal_pow hqnonneg, ← ENNReal.ofReal_mul hKnonneg]
      _ ≤ ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
        ENNReal.ofReal_le_ofReal hincReal
  have hdecomp : Φ m t = Φ (m - 1) t + Δ := by
    funext x
    simp [Δ]
  have hbarFinal : barNorm n Rm (Φ m t) ≤ ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by
    rw [hdecomp]
    calc
      barNorm n Rm (Φ (m - 1) t + Δ) ≤
        barNorm n Rm (Φ (m - 1) t) + barNorm n Rm Δ :=
        barNorm_add_le _ _ n Rm (hΦprev.of_le (by simp)) (hΔ.of_le (by simp))
      _ ≤ ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) +
        ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
        add_le_add hprevScaled hincScaled
      _ = ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by
        calc
          _ = ENNReal.ofReal
              (M (m - 1) * Rm⁻¹ ^ 2 * P +
                (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
            (ENNReal.ofReal_add
              (p := M (m - 1) * Rm⁻¹ ^ 2 * P)
              (q := (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P)
              (by positivity)
              (mul_nonneg
                (mul_nonneg (sub_nonneg.mpr hMmono) (by positivity))
                (by positivity))).symm
          _ = ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by congr 1; ring
  rw [← barNorm_eq_snorm (Φ m t) n Rm (hΦm.of_le (by simp))]
  simpa [Rm, P, Section2JointInduction.section2Weight] using hbarFinal

/-- The joint `e.indyhyp` induction over every Section 2 scale. -/
theorem section2_stream_induction {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M) :
    ∀ m : ℕ, Section2StreamInductionHypothesis (Φ := Φ) R M m := by
  intro m
  induction m with
  | zero =>
      intro t n hn
      rw [hseq.1]
      rw [hscales.amplitude_zero, hscales.radius_zero]
      have hn0 : n ≠ 0 := by omega
      have hLift : FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ)) =
          fun _ => (0 : ℝ) := by
        funext x
        simp [FaaDiBruno.liftVecOne]
      have hIter : iteratedFDeriv ℝ n
          (FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ))) = 0 := by
        rw [hLift]
        exact iteratedFDeriv_const_of_ne hn0 (0 : ℝ)
      have hpartial (J : Fin n → Fin 2) (x : Vec 2) :
          FaaDiBruno.orderedPartial n (fun _ : Vec 2 => (0 : ℝ)) x J = 0 := by
        change iteratedFDeriv ℝ n
          (FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ)))
          (WithLp.toLp 1 x) (fun j => FaaDiBruno.coordinateVectorOne 2 (J j)) = 0
        rw [hIter]
        simp
      have hderiv : FaaDiBruno.derivativeSup n (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
        unfold FaaDiBruno.derivativeSup
        apply le_antisymm
        · apply iSup_le
          intro J
          unfold FaaDiBruno.partialSup
          have hfun : (fun x : Vec 2 =>
              FaaDiBruno.orderedPartial n (fun _ : Vec 2 => (0 : ℝ)) x J) = 0 := by
            funext x
            exact hpartial J x
          rw [hfun]
          change eLpNormEssSup (0 : Vec 2 → ℝ) (FaaDiBruno.vecVolume 2) ≤ 0
          exact le_of_eq eLpNormEssSup_zero
        · exact bot_le
      simp only [FaaDiBruno.snorm, hderiv, mul_zero]
      exact bot_le
  | succ m ih =>
      exact section2_stream_induction_step hscales happB2 (m + 1) (by omega)
        (by simpa using ih)

/-- One scale of the source-form flow data used by §2 and Appendix B. The
fields retain the displayed bounds; only the scale index is fixed. -/
structure Section2FlowBoundsAtScale {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ) (Cmat : ℝ)
    (m : ℕ) : Prop where
  inverse_regbounds : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
    flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionFlowInvJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤
      ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m)
  flow_close : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ x : Vec 2,
      ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4
  flow_jacobian_composed : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
    flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
    ContDiff ℝ (⊤ : ℕ∞) (fun x => constructionComposedFlowJacobian hseq m s t x)
  flow_jacobian : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
      (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12
  flow_higher_derivative : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)
  material_jacobian : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
    n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
      ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => constructionComposedFlowJacobian hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * (epsilon β I.Λ m)⁻¹ ^ n *
              (epsilon β I.Λ m ^ (β - 2)) ^ ell
  material_jacobian_time_diff : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionComposedFlowJacobian hseq m s r x (basisVec j) i) t
  inverse_jacobian_time_diff : ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionFlowInvJacobian hseq m r s x) t

/-- The §2 induction proves every `e.indyhyp` and the first stream-regularity increment
display. Flow estimates are assembled separately from the preceding-scale
induction hypothesis in `Section2FlowBridge`. -/
theorem section2_joint_induction {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M) :
    (∀ m : ℕ, Section2StreamInductionHypothesis (Φ := Φ) R M m) ∧
      StreamIncrementBounds I Φ := by
  have hind := section2_stream_induction hscales happB2
  have hinc : StreamIncrementBounds I Φ := by
    intro m hm t n
    exact stream_increment_bound_at_scale hscales happB2 m hm
      (hind (m - 1)) t n
  exact ⟨hind, hinc⟩

end AVenhance.Infra.Construction
