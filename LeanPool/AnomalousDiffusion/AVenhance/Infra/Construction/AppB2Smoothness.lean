/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2FieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart

/-! Repackage all finite joint flow orders into the spatial smoothness witness
required by the consumed App. B.2 inverse-flow data. -/

@[expose] public section

open MeasureTheory Homogenization

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

theorem constructionFlowInv_spatial_smooth_of_joint_orders
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (s u : ℝ) :
    ContDiff ℝ ∞ (fun x : Vec 2 =>
      constructionFlowInv hseq m (s + u) x s) := by
  have hforward : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) := by
    rw [contDiff_infty]
    intro n
    exact hjoint m n
  let spaceTimeMap : Vec 2 → ℝ × Vec 2 × ℝ := fun x => (s, x, s + u)
  have hmapSmooth : ContDiff ℝ ∞ spaceTimeMap := by
    fun_prop
  have hinv :
      (fun x : Vec 2 => constructionFlowInv hseq m (s + u) x s) =
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2) ∘ spaceTimeMap := by
    funext x
    simp [spaceTimeMap, constructionFlowInv, constructionFlow, AVenhance.flowInv]
  rw [hinv]
  exact hforward.comp hmapSmooth

theorem AppB2Smoothness.identity_orderedPartial_one (x : Vec 2) (I : Fin 1 → Fin 2) :
    AVenhance.FaaDiBruno.orderedPartial 1 (fun y : Vec 2 => y) x I =
      AVenhance.FaaDiBruno.coordinateVector 2 (I 0) := by
  open AVenhance.FaaDiBruno in
  have hderiv : fderiv ℝ
      (fun z : AVenhance.FaaDiBruno.VecOne 2 =>
        AVenhance.FaaDiBruno.vecOneEquiv 2 z)
      (WithLp.toLp 1 x) =
        (AVenhance.FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap := by
    exact (AVenhance.FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.fderiv
  rw [AVenhance.FaaDiBruno.orderedPartial,
    show AVenhance.FaaDiBruno.liftVecOne (fun y : Vec 2 => y) =
      fun z => AVenhance.FaaDiBruno.vecOneEquiv 2 z by rfl,
    iteratedFDeriv_one_apply, hderiv]
  ext j
  by_cases hji : j = I 0 <;>
    simp [AVenhance.FaaDiBruno.vecOneEquiv,
      AVenhance.FaaDiBruno.coordinateVectorOne,
      AVenhance.FaaDiBruno.coordinateVector, hji]

theorem AppB2Smoothness.identity_orderedPartial_ge_two (x : Vec 2) {n : ℕ}
    (hn : 2 ≤ n) (I : Fin n → Fin 2) :
    AVenhance.FaaDiBruno.orderedPartial n (fun y : Vec 2 => y) x I = 0 := by
  open AVenhance.FaaDiBruno in
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      have hconst :
          (fun y : VecOne 2 => fderiv ℝ (fun z : VecOne 2 => vecOneEquiv 2 z) y) =
            fun _ => (vecOneEquiv 2).toContinuousLinearMap := by
        funext y
        exact (vecOneEquiv 2).toContinuousLinearMap.fderiv
      rw [orderedPartial,
        show liftVecOne (fun y : Vec 2 => y) = fun z => vecOneEquiv 2 z by rfl,
        iteratedFDeriv_succ_apply_right, hconst]
      have hz := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := VecOne 2)
        (F := VecOne 2 →L[ℝ] Vec 2) (n := k + 1) (by omega)
        ((vecOneEquiv 2).toContinuousLinearMap)
      rw [hz]
      simp

theorem AppB2Smoothness.identity_derivativeSup_le_one {n : ℕ} (hn : 1 ≤ n) :
    AVenhance.FaaDiBruno.derivativeSup n (fun x : Vec 2 => x) ≤ ENNReal.ofReal 1 := by
  open AVenhance.FaaDiBruno in
  by_cases hOne : n = 1
  · subst n
    unfold derivativeSup
    apply iSup_le
    intro I
    unfold partialSup
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    rw [AppB2Smoothness.identity_orderedPartial_one x I]
    have hnorm : ‖AVenhance.FaaDiBruno.coordinateVector 2 (I 0)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonempty]
      intro j
      by_cases hj : j = I 0 <;>
        simp [AVenhance.FaaDiBruno.coordinateVector, hj]
    exact hnorm
  · have hnTwo : 2 ≤ n := by omega
    have hpartialZero (I : Fin n → Fin 2) :
        partialSup n (fun x : Vec 2 => x) I = 0 := by
      unfold partialSup
      rw [eLpNormEssSup_eq_zero_iff]
      filter_upwards with x
      exact AppB2Smoothness.identity_orderedPartial_ge_two x hnTwo I
    have hzero : derivativeSup n (fun x : Vec 2 => x) = 0 := by
      unfold derivativeSup
      apply le_antisymm
      · exact iSup_le fun I => (hpartialZero I).le
      · exact bot_le
    rw [hzero]
    simp

theorem AppB2Smoothness.identity_snorm_le_four_div {n : ℕ} (hn : 1 ≤ n) {S : ℝ}
    (hS : 0 < S) :
    AVenhance.FaaDiBruno.snorm (fun x : Vec 2 => x) n S ≤
      ENNReal.ofReal (4 / S) := by
  open AVenhance.FaaDiBruno in
  by_cases hOne : n = 1
  · subst n
    have hD := AppB2Smoothness.identity_derivativeSup_le_one (n := 1) (by norm_num)
    have hfactor :
        ((4 / S) * S ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
          ((↑(1 : ℕ) + 1 : ℝ) ^ 2)) = 1 := by
      norm_num [Nat.factorial]
      field_simp [ne_of_gt hS]
    have htarget : ENNReal.ofReal 1 ≤ ENNReal.ofReal
        ((4 / S) * S ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
          ((↑(1 : ℕ) + 1 : ℝ) ^ 2)) := by
      rw [hfactor]
    apply snorm_le_of_derivativeSup_le (fun x : Vec 2 => x) hS
    exact hD.trans htarget
  · have hnTwo : 2 ≤ n := by omega
    have hpartialZero (I : Fin n → Fin 2) :
        partialSup n (fun x : Vec 2 => x) I = 0 := by
      unfold partialSup
      rw [eLpNormEssSup_eq_zero_iff]
      filter_upwards with x
      exact AppB2Smoothness.identity_orderedPartial_ge_two x hnTwo I
    have hzero : derivativeSup n (fun x : Vec 2 => x) = 0 := by
      unfold derivativeSup
      apply le_antisymm
      · exact iSup_le fun I => (hpartialZero I).le
      · exact bot_le
    unfold snorm
    rw [hzero]
    simp

theorem AppB2Smoothness.derivativeSup_add_le_vec {n : ℕ} (f g : Vec 2 → Vec 2)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.FaaDiBruno.derivativeSup n (fun x => f x + g x) ≤
      AVenhance.FaaDiBruno.derivativeSup n f +
        AVenhance.FaaDiBruno.derivativeSup n g := by
  classical
  open AVenhance.FaaDiBruno in
  unfold derivativeSup
  refine iSup_le fun I => ?_
  calc
    partialSup n (fun x => f x + g x) I ≤ partialSup n f I + partialSup n g I := by
      unfold partialSup
      have hadd : liftVecOne (fun x => f x + g x) = liftVecOne f + liftVecOne g := by
        funext z
        rfl
      have hpart (x : Vec 2) :
          orderedPartial n (fun x => f x + g x) x I =
            orderedPartial n f x I + orderedPartial n g x I := by
        simp only [orderedPartial, hadd]
        rw [iteratedFDeriv_add_apply
          (contDiff_liftVecOne hf).contDiffAt
          (contDiff_liftVecOne hg).contDiffAt]
        rfl
      have hfun :
          (fun x => orderedPartial n (fun x => f x + g x) x I) =
            (fun x => orderedPartial n f x I) +
              (fun x => orderedPartial n g x I) := by
        funext x
        exact hpart x
      rw [hfun]
      exact eLpNormEssSup_add_le
    _ ≤ derivativeSup n f + derivativeSup n g :=
      add_le_add (le_iSup_of_le I le_rfl) (le_iSup_of_le I le_rfl)

theorem AppB2Smoothness.snorm_add_le_vec {n : ℕ} {S : ℝ} (f g : Vec 2 → Vec 2)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.FaaDiBruno.snorm (fun x => f x + g x) n S ≤
      AVenhance.FaaDiBruno.snorm f n S + AVenhance.FaaDiBruno.snorm g n S := by
  open AVenhance.FaaDiBruno in
  unfold snorm
  have hD := AppB2Smoothness.derivativeSup_add_le_vec f g hf hg
  let c := ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal S)⁻¹ ^ n
  calc
    _ ≤ c * (derivativeSup n f + derivativeSup n g) := by
      dsimp [c]
      gcongr
    _ = _ := by
      dsimp [c]
      rw [mul_add]

theorem AppB2Smoothness.snorm_neg_eq_vec {n : ℕ} {S : ℝ} (f : Vec 2 → Vec 2) :
    AVenhance.FaaDiBruno.snorm (fun x => -f x) n S =
      AVenhance.FaaDiBruno.snorm f n S := by
  open AVenhance.FaaDiBruno in
  have hpartial (I : Fin n → Fin 2) :
      partialSup n (fun x => -f x) I = partialSup n f I := by
    unfold partialSup
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    apply essSup_congr_ae
    filter_upwards with x
    have h : orderedPartial n (fun x => -f x) x I = -orderedPartial n f x I := by
      change iteratedFDeriv ℝ n
        (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
          (fun j => coordinateVectorOne 2 (I j)) =
        -iteratedFDeriv ℝ n
          (fun z : VecOne 2 => f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
            (fun j => coordinateVectorOne 2 (I j))
      rw [show (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) =
        -(fun z : VecOne 2 => f ((vecOneEquiv 2) z)) by rfl, iteratedFDeriv_neg]
      rfl
    rw [h]
    simp
  have hderiv :
      derivativeSup n (fun x => -f x) = derivativeSup n f := by
    unfold derivativeSup
    apply le_antisymm
    · apply iSup_le
      intro I
      rw [hpartial I]
      exact le_iSup_of_le I le_rfl
    · apply iSup_le
      intro I
      rw [← hpartial I]
      exact le_iSup_of_le I le_rfl
  unfold snorm
  rw [hderiv]

theorem AppB2Smoothness.constructionFlow_jointSmooth_of_joint_orders
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ =>
        constructionFlow hseq m p.1.1 p.1.2 p.2) := by
  have hjointAll : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) := by
    rw [contDiff_infty]
    intro n
    exact hjoint m n
  have hperm : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => (p.1.1, p.1.2, p.2)) := by
    fun_prop
  change ContDiff ℝ ∞
    ((fun p : ℝ × Vec 2 × ℝ =>
      constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
      fun p : (ℝ × Vec 2) × ℝ => (p.1.1, p.1.2, p.2))
  exact hjointAll.comp hperm

theorem AppB2Smoothness.constructionFlow_shift_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) (s : ℝ) :
    IsFlow (fun t x => b (s + t) x)
      (fun t x r => X (s + t) x (s + r)) := by
  refine ⟨?_, ?_⟩
  · intro x r
    exact hX.1 x (s + r)
  · intro x r t
    have hbase : HasDerivAt (fun z => X z x (s + r))
        (b (t + s) (X (t + s) x (s + r))) (t + s) := by
      simpa [add_comm] using hX.2 x (s + r) (s + t)
    have hshifted := hbase.comp_add_const t s
    convert hshifted using 1 <;> simp [add_comm]

theorem AppB2Smoothness.constructionFlowInv_displacement_data_of_joint_orders
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹)
    (n : ℕ) (hn : 1 ≤ n) :
    ContDiff ℝ n
      (fun x : Vec 2 => constructionFlow hseq (m - 1) s x (s + u) - x) ∧
    AVenhance.FaaDiBruno.snorm
      (fun x : Vec 2 => constructionFlow hseq (m - 1) s x (s + u) - x)
      n ((9 / 8) * R (m - 1)) ≤
      ENNReal.ofReal (1 / (4 * R (m - 1))) := by
  let q : ℕ := m - 1
  let Rq : ℝ := R q
  let Mq : ℝ := M q
  let Cf : ℝ := Mq / Rq
  let Cg : ℝ := Mq / Rq
  have hRq : 0 < Rq := by dsimp [Rq, q]; exact section2_radius_pos hscales (m - 1)
  have hMq : 0 < Mq := by dsimp [Mq, q]; exact section2_amplitude_pos hscales (m - 1)
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCfR : Cf * Rq = Mq := by
    dsimp [Cf]
    field_simp [ne_of_gt hRq]
  have hu' : |u| ≤ (1 / 64 : ℝ) * Mq⁻¹ := by
    have hz : (2 : ℝ) ^ (-6 : ℤ) = (1 / 64 : ℝ) := by norm_num
    simpa [hz, Mq, q, mul_comm] using hu
  have htime : |u| ≤ 1 / (8 * Cf * Rq) := by
    calc
      |u| ≤ (1 / 64 : ℝ) * Mq⁻¹ := hu'
      _ ≤ (1 / 8 : ℝ) * Mq⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hMq.le)
      _ = 1 / (8 * Cf * Rq) := by
        have hmul : 8 * Cf * Rq = 8 * Mq := by
          calc
            8 * Cf * Rq = 8 * (Cf * Rq) := by ring
            _ = 8 * Mq := by rw [hCfR]
        rw [hmul]
        field_simp [ne_of_gt hMq]
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ q)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq q
  have hφ := streamSeq_isAdmissible hseq q
  have hb : AVenhance.Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b]
    dsimp [constructionFlow]
    exact flow_isFlow (streamVel (Φ q)) hφ.vel_continuous hφ.vel_lipschitz
  have hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2) := by
    simpa [X] using AppB2Smoothness.constructionFlow_jointSmooth_of_joint_orders hseq q hjoint
  let bShift : ℝ → Vec 2 → Vec 2 := fun t x => b (s + t) x
  let gShift : ℝ → Vec 2 → Vec 2 := fun t x => -bShift t x
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun t x r => X (s + t) x (s + r)
  have hbShift : ContDiff ℝ ∞ (Function.uncurry bShift) := by
    have hmap : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ ∞ (Function.uncurry b ∘
      fun p : ℝ × Vec 2 => (s + p.1, p.2))
    exact hb.smooth.comp hmap
  have hgShift : ContDiff ℝ ∞ (Function.uncurry gShift) := by
    change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      -(Function.uncurry bShift p))
    exact contDiff_neg.comp hbShift
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using AppB2Smoothness.constructionFlow_shift_isFlow hX s
  let Y : ℝ → Vec 2 → Vec 2 := fun t x => X s x (s + t) - x
  have hYjoint : ContDiff ℝ ∞ (Function.uncurry Y) := by
    let map : ℝ × Vec 2 → (ℝ × Vec 2) × ℝ :=
      fun p => ((s, p.2), s + p.1)
    have hmap : ContDiff ℝ ∞ map := by fun_prop
    have hF : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => X s p.2 (s + p.1)) := by
      change ContDiff ℝ ∞
        ((fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2) ∘ map)
      exact hXsmooth.comp hmap
    have hId : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => p.2) := by fun_prop
    change ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => X s p.2 (s + p.1) - p.2)
    exact hF.sub hId
  have hYslice : ContDiff ℝ n (Y u) := by
    have hmap : ContDiff ℝ n (fun x : Vec 2 => (u, x)) := by fun_prop
    exact (hYjoint.of_le (by simp)).comp hmap
  have htransport :
      AVenhance.FaaDiBruno.IsClassicalTransportSolution bShift gShift Y := by
    simpa [bShift, gShift, Y, b, X] using
      AVenhance.FaaDiBruno.flow_inverse_displacement_at_start_isTransportSolution_of_jointSmooth
        hb hX hXsmooth s
  have hB : ∀ t k, 1 ≤ k → k ≤ n →
      AVenhance.FaaDiBruno.snorm (bShift t) k Rq ≤ ENNReal.ofReal Cf := by
    intro t k hk hkn
    have hfield := section2_streamVel_snorm_bound hseq hprev hk hRq hMq (s + t)
    simpa [bShift, b, Cf, Cg, Rq, Mq, q] using hfield
  have hG : ∀ t k, 1 ≤ k → k ≤ n →
      AVenhance.FaaDiBruno.snorm (gShift t) k Rq ≤ ENNReal.ofReal Cg := by
    intro t k hk hkn
    rw [AppB2Smoothness.snorm_neg_eq_vec]
    have hfield := section2_streamVel_snorm_bound hseq hprev hk hRq hMq (s + t)
    simpa [bShift, b, Cf, Cg, Rq, Mq, q] using hfield
  have hYest : ∀ k, 1 ≤ k → k ≤ n → ∀ t,
      |t| ≤ 1 / (8 * Cf * Rq) →
      AVenhance.FaaDiBruno.snorm (Y t) k
        (AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |t|) ≤
        ENNReal.ofReal (16 * Cg * |t|) := by
    exact AVenhance.FaaDiBruno.transportSolution_snorm_equalRadius_all
      htransport hbShift hgShift hXShift hCf hCg hRq hB hG
  have hYat := hYest n hn (by omega) u htime
  let Sout : ℝ := (9 / 8) * Rq
  have hSout : 0 < Sout := by dsimp [Sout]; positivity
  have hshift :
      AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |u| ≤ Sout := by
    have huM : 8 * Mq * |u| ≤ 1 / 8 := by
      calc
        8 * Mq * |u| ≤ 8 * Mq * ((1 / 64 : ℝ) * Mq⁻¹) := by gcongr
        _ = 1 / 8 := by field_simp [ne_of_gt hMq]; ring
    change AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |u| ≤ (9 / 8) * Rq
    rw [AVenhance.FaaDiBruno.transportShiftRadius]
    have hterm : 8 * |u| * Cf * Rq ^ 2 = (8 * Mq * |u|) * Rq := by
      rw [← hCfR]
      ring
    rw [hterm]
    nlinarith [hRq, huM]
  have hYout : AVenhance.FaaDiBruno.snorm (Y u) n Sout ≤
      ENNReal.ofReal (16 * Cg * |u|) := by
    apply AVenhance.FaaDiBruno.snorm_le_of_radius_le (Y u)
      (by
        rw [AVenhance.FaaDiBruno.transportShiftRadius]
        positivity)
      hSout hshift (by positivity) hYat
  have hdispReal : 16 * Cg * |u| ≤ 1 / (4 * Rq) := by
    rw [show 1 / (4 * Rq) = (1 / 4 : ℝ) / Rq by ring]
    apply (le_div_iff₀ hRq).2
    have hleft : (16 * Cg * |u|) * Rq = 16 * Mq * |u| := by
      dsimp [Cg]
      field_simp [ne_of_gt hRq]
    rw [hleft]
    calc
      16 * Mq * |u| ≤ 16 * Mq * ((1 / 64 : ℝ) * Mq⁻¹) := by gcongr
      _ = 1 / 4 := by field_simp [ne_of_gt hMq]; ring
  have hYout' : AVenhance.FaaDiBruno.snorm (Y u) n Sout ≤
      ENNReal.ofReal (1 / (4 * Rq)) :=
    hYout.trans (ENNReal.ofReal_le_ofReal hdispReal)
  exact ⟨hYslice, by simpa [Y, Sout, q] using hYout'⟩

theorem AppB2Smoothness.constructionFlowInv_snorm_bound_of_joint_orders
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹)
    (n : ℕ) (hn : 1 ≤ n) :
    AVenhance.FaaDiBruno.snorm
      (fun x : Vec 2 => constructionFlowInv hseq (m - 1) (s + u) x s)
      n ((9 / 8) * R (m - 1)) ≤
      ENNReal.ofReal (5 * (8 / 9 : ℝ) * (R (m - 1))⁻¹) := by
  let q : ℕ := m - 1
  let Rq : ℝ := R q
  let Sout : ℝ := (9 / 8) * Rq
  have hRq : 0 < Rq := by dsimp [Rq, q]; exact section2_radius_pos hscales (m - 1)
  have hSout : 0 < Sout := by dsimp [Sout]; positivity
  obtain ⟨hYslice, hYbound⟩ :=
    AppB2Smoothness.constructionFlowInv_displacement_data_of_joint_orders
      hseq hscales hjoint m hprev s u hu n hn
  let Y : Vec 2 → Vec 2 := fun x => constructionFlow hseq q s x (s + u) - x
  have htargetfun :
      (fun x : Vec 2 => constructionFlowInv hseq q (s + u) x s) =
        (fun x => x + Y x) := by
    funext x
    simp [Y, q, constructionFlowInv, constructionFlow, AVenhance.flowInv]
  have hid := AppB2Smoothness.identity_snorm_le_four_div hn hSout
  have hadd := AppB2Smoothness.snorm_add_le_vec (n := n) (S := Sout)
    (fun x : Vec 2 => x) Y contDiff_id hYslice
  rw [htargetfun]
  have hsum := hadd.trans (add_le_add hid hYbound)
  have hcoef : 4 / Sout + 1 / (4 * Rq) ≤ 40 / 9 * Rq⁻¹ := by
    dsimp [Sout]
    field_simp [ne_of_gt hRq]
    nlinarith
  calc
    AVenhance.FaaDiBruno.snorm (fun x : Vec 2 => x + Y x) n Sout ≤
        ENNReal.ofReal (4 / Sout) + ENNReal.ofReal (1 / (4 * Rq)) := hsum
    _ = ENNReal.ofReal (4 / Sout + 1 / (4 * Rq)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (40 / 9 * Rq⁻¹) := ENNReal.ofReal_le_ofReal hcoef
    _ = ENNReal.ofReal (5 * (8 / 9 : ℝ) * (R (m - 1))⁻¹) := by
      congr 1
      change 40 / 9 * (R (m - 1))⁻¹ = 5 * (8 / 9 : ℝ) * (R (m - 1))⁻¹
      ring

/-- Construct the consumed App. B.2 package from the previous-scale induction
bound, provided every finite joint order of the construction flow is available.
The finite-order premise assembles the smooth inverse witness; the quantitative
field input is exactly `e.indyhyp` at scale `m - 1`. -/
theorem appB2InverseFlowData_of_joint_orders
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m p.1 p.2.1 p.2.2)) :
    AppB2InverseFlowData I Φ hseq R M := by
  refine ⟨?_, ?_⟩
  · intro m hm s u
    exact constructionFlowInv_spatial_smooth_of_joint_orders hseq hjoint (m - 1) s u
  · intro m hm hprev s u hu n hn
    exact AppB2Smoothness.constructionFlowInv_snorm_bound_of_joint_orders
      hseq hscales hjoint m hprev s u hu n hn

/-- Construct all finite joint orders of the construction flow from the
merged all-orders ODE theorem. Each scale's stream velocity is a smooth
periodic field, and its characterized construction flow is therefore jointly
C∞ in target time, initial point, and start time. -/
theorem appB2InverseFlowData_of_smoothPeriodicFlow
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M) :
    AppB2InverseFlowData I Φ hseq R M := by
  apply appB2InverseFlowData_of_joint_orders hseq hscales
  intro m n
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  have hφ := streamSeq_isAdmissible hseq m
  have hb : AVenhance.Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b]
    dsimp [constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hJointSmooth : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) :=
    AVenhance.Infra.Flow.flow_joint_contDiff_infty hb hX
  simpa [X] using hJointSmooth.of_le (by simp : (n : ℕ∞ω) ≤ ∞)

end AVenhance.Infra.Construction

end
