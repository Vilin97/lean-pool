/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseContextAssembly

@[expose] public section

/-!
# Weighted classes of the actual base stress

The flat weight is transported exactly by the physical chart.  Only powers
of the reciprocal edge distance are enlarged.  All derivatives are actual
Fréchet derivatives, and every estimate is uniform over the dyadic bands.
-/

noncomputable section

namespace NavierStokes.BaseStressClasses

open Set Filter Function WeightedClasses
open scoped ContDiff Topology BigOperators

abbrev Point := BaseContextAssembly.Point
abbrev Chart := SlowBorelBase.Chart
abbrev Inner := SlowBorelBase.Inner

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section Composition

variable {D E V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Independent estimates for each derivative order give a single estimate
for every fixed finite prefix.  The polynomial degree may depend on the
prefix, but never on the band or evaluation point. -/
theorem majorant_prefix (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) (a : ℕ → ℕ → D → ℝ)
    (ha : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ n x, x ∈ s.domain → a j n x ≤ majorant s w α C p n x)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
      ∀ j ≤ m, a j n x ≤ majorant s w α C p n x := by
  induction m with
  | zero =>
      obtain ⟨C, hC, p, hp⟩ := ha 0
      exact ⟨C, hC, p, fun n x hx j hj => by simpa only [Nat.eq_zero_of_le_zero hj] using hp n x hx⟩
  | succ m ih =>
      obtain ⟨C, hC, p, hp⟩ := ih
      obtain ⟨B, hB, q, hq⟩ := ha (m+1)
      refine ⟨C+B, add_nonneg hC hB, p+q, fun n x hx j hj => ?_⟩
      have hCp : majorant s w α C p n x ≤ majorant s w α C (p+q) n x :=
        majorant_mono_degree s w α hC (Nat.le_add_right p q) n x (hw n x hx)
      have hBq : majorant s w α B q n x ≤ majorant s w α B (p+q) n x :=
        majorant_mono_degree s w α hB (Nat.le_add_left q p) n x (hw n x hx)
      have hsum : majorant s w α C (p+q) n x + majorant s w α B (p+q) n x =
          majorant s w α (C+B) (p+q) n x := by unfold majorant; ring
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exact (hp n x hx j (Nat.le_of_lt_succ hlt)).trans (hCp.trans
          ((le_add_of_nonneg_right (majorant_nonneg s w α hB _ _ _ (hw n x hx))).trans_eq hsum))
      · exact (hq n x hx).trans (hBq.trans
          ((le_add_of_nonneg_left (majorant_nonneg s w α hC _ _ _ (hw n x hx))).trans_eq hsum))

/-- Weighted outer jets and a genuinely controlled inner map imply the
class of the composite.  In particular, no derivative estimate for the
composite itself is assumed. -/
theorem class_comp_of_outer_jets {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → E → V} {g : ℕ → D → E} {U : Set E}
    (hU : IsOpen U) (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hg : UnweightedClass s 0 g) (hmap : ∀ n, MapsTo (g n) s.domain U)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hb : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
      ‖iteratedFDeriv ℝ j (f n) (g n x)‖ ≤ majorant s w α C p n x) :
    MemClass s w α (fun n x => f n (g n x)) := by
  refine ⟨hw, fun n => (hf n).comp (hg.smooth n) (hmap n), fun m => ?_⟩
  obtain ⟨C, hC, p, hp⟩ := majorant_prefix s w α hw
    (fun j n x => ‖iteratedFDeriv ℝ j (f n) (g n x)‖) hb m
  obtain ⟨B, hB, q, hq⟩ := hg.bounds m
  refine ⟨(m.factorial : ℝ) * C * (B+1)^m, by positivity, p+q*m, ?_⟩
  intro n x hx j hj
  have hG : 1 ≤ s.growth n x := s.one_le_growth n x
  have hD : 1 ≤ (B+1) * s.growth n x ^ q :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hG)
  have hA : 0 ≤ majorant s w α C p n x := majorant_nonneg s w α hC _ _ _ (hw n x hx)
  have hcomp := norm_iteratedFDerivWithin_comp_le (hf n) (hg.smooth n) (nat_le_infty j)
    hU.uniqueDiffOn s.isOpen_domain.uniqueDiffOn (hmap n) hx
    (C := majorant s w α C p n x) (D := (B+1) * s.growth n x ^ q)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU (hmap n hx)]
      exact hp n x hx i (hi.trans hj))
    (fun i hi hij => by
      rw [iteratedFDerivWithin_of_isOpen i s.isOpen_domain hx]
      have hi0 := hq n x hx i (hij.trans hj)
      simp only [majorant, Real.rpow_zero, mul_one] at hi0
      exact hi0.trans ((mul_le_mul_of_nonneg_right (by linarith : B ≤ B+1)
        (pow_nonneg (s.growth_nonneg n x) q)).trans (by simpa using pow_le_pow_right₀ hD hi)))
  rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at hcomp
  calc
    _ ≤ (j.factorial : ℝ) * majorant s w α C p n x * ((B+1)*s.growth n x^q)^j := hcomp
    _ ≤ (m.factorial : ℝ) * majorant s w α C p n x * ((B+1)*s.growth n x^q)^m := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA
      · exact pow_le_pow_right₀ hD hj
      · positivity
      · positivity
    _ = _ := by simp only [majorant, mul_pow, ← pow_mul, pow_add]; ring

end Composition

section Rescaling

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Banach-valued recentering of actual blown jets.  The loss involves the
bounded normalized scale `rho`, never the inverse dyadic scale. -/
theorem scaled_jet_from_blown {f : Chart → V}
    (hf : ContDiffOn ℝ ∞ f BaseChartJets.sumRegion) {Q rho M : ℝ} {w : Inner}
    (hQ : 0 < Q) (hrho : 0 < rho) (hw : 0 < w.1)
    (hM : 1 ≤ M) (hi : 1/rho ≤ M) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ SlowBorelBase.scaleMap Q) (rho,w)‖ ≤
      ‖SlowBorelBase.blownJet j f (Q*rho,w)‖ * M^j := by
  have hs : ContDiffOn ℝ ∞ (f ∘ SlowBorelBase.scaleMap (Q*rho)) BaseChartJets.sumRegion :=
    hf.comp (SlowBorelBase.scaleMap (Q*rho)).contDiff.contDiffOn
      (fun y hy => ⟨mul_pos (mul_pos hQ hrho) hy.1, hy.2⟩)
  have heq : f ∘ SlowBorelBase.scaleMap Q =
      (f ∘ SlowBorelBase.scaleMap (Q*rho)) ∘ SlowBorelBase.scaleMap rho⁻¹ := by
    funext y
    change f (Q*y.1,y.2) = f (Q*rho*(rho⁻¹*y.1),y.2)
    congr 1
    apply Prod.ext
    · change Q*y.1 = Q*rho*(rho⁻¹*y.1)
      field_simp
    · rfl
  have hx : SlowBorelBase.scaleMap rho⁻¹ (rho,w) ∈ BaseChartJets.sumRegion := by
    simpa only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne'] using
      (show ((1:ℝ),w) ∈ BaseChartJets.sumRegion from ⟨by norm_num, hw, mem_univ _⟩)
  have hb := PhaseJetBounds.norm_jet_comp_linear BaseChartJets.sumRegion_open hs
    (SlowBorelBase.scaleMap rho⁻¹) hx j
  have hn : ‖SlowBorelBase.scaleMap rho⁻¹‖ ≤ M := BaseChartJets.scaleMap_norm_le hM
    (by simpa only [abs_of_pos (inv_pos.mpr hrho), one_div] using hi)
  rw [← heq] at hb
  apply hb.trans
  have he : SlowBorelBase.scaleMap rho⁻¹ (rho,w) = (1,w) := by
    simp only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne']
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn j) (norm_nonneg _)

end Rescaling

section NativeGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- The exact normalized coordinates in the mean-variable order. -/
noncomputable def coordinates (x : Point) : Chart :=
  BaseChartJets.normalizedCoordinates F.data.h (BaseContextAssembly.slowCoordinates x)

theorem coordinates_unweighted (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    UnweightedClass (BaseContextAssembly.nativeStrip W U) 0 (fun _ => coordinates (F := F)) := by
  apply BaseContextAssembly.unweighted_polynomial_pullback
    (BaseContextAssembly.nativeStrip W U)
    (BaseChartJets.normalizedCoordinates_polynomial F.data.h_pos F.data.h_lt_half
      (div_pos U.qlo_pos (by norm_num)) (BaseContextAssembly.native_geometry W U ℕ))
  exact fun _ => BaseContextAssembly.slowCoordinates_maps W U

/-- The source edge distance is the capped minimum of twice the two radial
log distances.  Thus it is at least the native strip distance. -/
theorem native_edgeDistance_le (U : LocalSignedRequest.SlowRegion (2*F.data.h))
    {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip W U).domain) :
    (BaseContextAssembly.nativeStrip W U).delta x ≤
      FinalSlowBase.edgeDistance W (coordinates (F := F) x).2 := by
  let r := PrimaryTargetBounds.profileRadius F.data.h (BaseContextAssembly.slowCoordinates x)
  let a := PrimaryTargetBounds.leftRadius W
  let b := PrimaryTargetBounds.rightRadius W
  have ha : 0 < a := PrimaryTargetBounds.leftRadius_pos W
  have hb : 0 < b := PrimaryTargetBounds.rightRadius_pos W
  have hr : r ∈ Ioo a b := (BaseContextAssembly.nativeStrip_mem W U x).mp hx |>.2
  have hrp : 0 < r := ha.trans hr.1
  have hasq : a^2/2 = NominalConeAssembly.activeLeft W := by
    dsimp [a, PrimaryTargetBounds.leftRadius]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)]
    ring
  have hbsq : b^2/2 = NominalConeAssembly.activeRight W := by
    dsimp [b, PrimaryTargetBounds.rightRadius]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)]
    ring
  have hX : r^2/2 = (coordinates (F := F) x).2.1 :=
    PrimaryTargetBounds.profileRadius_sq (F := F) (BaseContextAssembly.nativeStrip_time W U hx)
  have halog := PrimaryTargetBounds.log_square_half ha
  have hblog := PrimaryTargetBounds.log_square_half hb
  rw [hasq] at halog
  rw [hbsq] at hblog
  have hl : Real.log (coordinates (F := F) x).2.1 - FinalSlowBase.logLeft W =
      2 * WeightedRadialPrimitive.logPosition a r := by
    rw [← hX, FinalSlowBase.logLeft, WeightedRadialPrimitive.logPosition,
      Real.log_div hrp.ne' ha.ne', PrimaryTargetBounds.log_square_half hrp, halog]
    ring
  have hh : FinalSlowBase.logRight W - Real.log (coordinates (F := F) x).2.1 =
      2 * (WeightedRadialPrimitive.logLength a b - WeightedRadialPrimitive.logPosition a r) := by
    rw [← hX, FinalSlowBase.logRight, WeightedRadialPrimitive.logLength,
      WeightedRadialPrimitive.logPosition, Real.log_div hb.ne' ha.ne',
      Real.log_div hrp.ne' ha.ne', PrimaryTargetBounds.log_square_half hrp, hblog]
    ring
  have hlog := WeightedRadialPrimitive.logPosition_mem ha hr
  have hd : (BaseContextAssembly.nativeStrip W U).delta x =
      WeightedRadialPrimitive.delta (WeightedRadialPrimitive.logLength a b)
        (WeightedRadialPrimitive.logPosition a r) := by
    change WeightedRadialPrimitive.delta _ (WeightedRadialPrimitive.logPosition _
      (x.1 / Real.sqrt (MeanRankUpdate.chartQ (2*F.data.h) x))) = _
    rw [← PrimaryTargetBounds.meanPoint_scalar (F := F) x]
    rfl
  rw [hd]
  unfold FinalSlowBase.edgeDistance BaseResidual.activeDelta ActiveAnnulusWeight.edgeDistance
  rw [hl, hh]
  exact min_le_min le_rfl (min_le_min (by linarith [hlog.1]) (by linarith [hlog.2]))

theorem inverse_edgeDistance_le_growth (U : LocalSignedRequest.SlowRegion (2*F.data.h))
    (n : ℕ) {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip W U).domain) :
    (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹ ≤
      (BaseContextAssembly.nativeStrip W U).growth n x := by
  let s := BaseContextAssembly.nativeStrip W U
  have hi : (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹ ≤ (s.delta x)⁻¹ :=
    inv_anti₀ (s.delta_pos x hx) (native_edgeDistance_le W U hx)
  apply hi.trans
  apply (le_max_right (1:ℝ) ((s.delta x)⁻¹)).trans
  exact le_mul_of_one_le_left (zero_le_one.trans (le_max_left _ _)) (s.one_le_slow n)

theorem coordinates_range (U : LocalSignedRequest.SlowRegion (2*F.data.h))
    {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip W U).domain) :
    (coordinates (F := F) x).1 ∈ Ioo (U.qlo/2) (BaseContextAssembly.geometryUpper U) :=
  (BaseContextAssembly.native_geometry W U ℕ).q_range 0 _
    (BaseContextAssembly.slowCoordinates_maps W U hx)

/-- Every fixed real power of the normalized positive scale has genuine
uniform jets on the moving strip, including as physical time tends to zero. -/
theorem coordinate_power_unweighted (U : LocalSignedRequest.SlowRegion (2*F.data.h)) (a : ℝ) :
    UnweightedClass (BaseContextAssembly.nativeStrip W U) 0
      (fun _ x => (coordinates (F := F) x).1 ^ a) := by
  have hqlo : 0 < U.qlo/2 := div_pos U.qlo_pos (by norm_num)
  have hc := BaseChartJets.normalizedCoordinates_polynomial F.data.h_pos F.data.h_lt_half
    hqlo (BaseContextAssembly.native_geometry W U ℕ)
  have hq := hc.clm (ContinuousLinearMap.fst ℝ ℝ Inner)
  have hp := hq.compact_comp isOpen_Ioi
    (show ContDiffOn ℝ ∞ (fun r : ℝ => r^a) (Ioi 0) from
      fun r hr => (contDiffAt_id.rpow_const_of_ne hr.ne').contDiffWithinAt)
    (K := Icc (U.qlo/2) (BaseContextAssembly.geometryUpper U)) isCompact_Icc
    (fun r hr => hqlo.trans_le hr.1)
    (fun n p hp => ⟨((BaseContextAssembly.native_geometry W U ℕ).q_range n p hp).1.le,
      ((BaseContextAssembly.native_geometry W U ℕ).q_range n p hp).2.le⟩)
  exact BaseContextAssembly.unweighted_polynomial_pullback
    (BaseContextAssembly.nativeStrip W U) hp (fun _ => BaseContextAssembly.slowCoordinates_maps W U)

end NativeGeometry

section ActualStress

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The literal positive-order part of the normalized tensor. -/
noncomputable def correction (upper : ℝ) (B : ℕ) (y : Chart) : Inner :=
  FinalSlowBase.normalizedStress H v upper B y -
    BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0 y.2

theorem correction_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (correction H v upper B) BaseChartJets.sumRegion := by
  intro y hy
  exact ((FinalSlowBase.normalizedStress_smoothAt H v upper B hy.1).sub
    ((BaseResidual.stressPair_smooth (FinalSlowBase.coefficients_smooth H v) 0).contDiffAt.comp
      y contDiffAt_snd)).contDiffWithinAt

/-- The weighted normalized remainder estimate holds at every positive
physical scale.  Above one its actual blown jets vanish by the cutoff germ. -/
theorem correction_weighted_jets (upper : ℝ) (B m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → ∀ w ∈ FinalSlowBase.annulus W,
      ‖SlowBorelBase.blownJet m (correction H v upper B) (q,w)‖ ≤
        D * q ^ F.data.h * FinalSlowBase.weight W w * (FinalSlowBase.edgeDistance W w)⁻¹ ^ N := by
  obtain ⟨D, hD, N, hb⟩ := FinalSlowBase.weighted_jets H v upper B m
  refine ⟨D, hD, N, fun q hq w hw => ?_⟩
  by_cases hq1 : q ≤ 1
  · exact hb q hq hq1 w hw
  · have hz := AllBandBaseJets.correction_blownJet_eq_zero
      (FinalSlowBase.scales_admissible H v upper B).positive F.data.h
      (BaseResidual.stressPair (FinalSlowBase.coefficients H v)) (lt_of_not_ge hq1) w m
    change SlowBorelBase.blownJet m (correction H v upper B) (q,w) = 0 at hz
    rw [hz, norm_zero]
    have hw' : w ∈ BaseResidual.activeWindow (FinalSlowBase.logLeft W) (FinalSlowBase.logRight W)
      := by
      rwa [← FinalSlowBase.annulus_eq W]
    have hzeta : 0 ≤ FinalSlowBase.weight W w :=
      (ActiveAnnulusWeight.radialWeight_pos hw'.1).le
    have hd : 0 ≤ (FinalSlowBase.edgeDistance W w)⁻¹ :=
      inv_nonneg.mpr (BaseResidual.activeDelta_bounds hw').1.le
    exact mul_nonneg (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg hq.le _)) hzeta)
      (pow_nonneg hd N)

/-- The order-zero tensor, composed with the actual moving chart, keeps
the exact edge weight.  Its proof uses the checked profile-jet estimates. -/
theorem leading_composed_meanClass (hcone : LeadingStressWeights.FullTrueCone v)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 0
      (fun _ x => BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0
        (coordinates (F := F) x).2) := by
  let s := BaseContextAssembly.nativeStrip W U
  apply class_comp_of_outer_jets (s := s) (U := univ) isOpen_univ
    (fun _ => (BaseResidual.stressPair_smooth (FinalSlowBase.coefficients_smooth H v) 0).contDiffOn)
    ((coordinates_unweighted W U).map (ContinuousLinearMap.snd ℝ ℝ Inner))
    (fun _ _ _ => mem_univ _) (fun _ x hx => s.zeta_nonneg x hx)
  intro j
  obtain ⟨D, hD, N, hb⟩ := FinalSlowBase.leading_coefficient_jets H v hcone j
  refine ⟨D, hD.le, N, fun n x hx => ?_⟩
  have hpos : 0 < FinalSlowBase.edgeDistance W (coordinates (F := F) x).2 :=
    (s.delta_pos x hx).trans_le (native_edgeDistance_le W U hx)
  have hi := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le)
    (inverse_edgeDistance_le_growth W U n hx) N
  have hw : FinalSlowBase.weight W (coordinates (F := F) x).2 = s.zeta x :=
    (BaseContextAssembly.nativeStrip_weight W U hx).symm
  calc
    _ ≤ D * FinalSlowBase.weight W (coordinates (F := F) x).2 *
        (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹ ^ N :=
      hb _ (BaseContextAssembly.nativeStrip_active W U hx)
    _ = D * s.zeta x * (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹ ^ N := by rw [hw]
    _ ≤ D * s.zeta x * s.growth n x ^ N :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg hD.le (s.zeta_nonneg x hx))
    _ = _ := by simp only [majorant, Real.rpow_zero, mul_one]; ring

/-- The actual positive-order normalized tensor is one mean order smaller
after the band rescaling, uniformly over all bands. -/
theorem correction_composed_meanClass (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => correction H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n) (coordinates (F := F) x))) := by
  let s := BaseContextAssembly.nativeStrip W U
  have hs n : ContDiffOn ℝ ∞
      (correction H v upper B ∘ SlowBorelBase.scaleMap (ChartScales.Q n)) BaseChartJets.sumRegion :=
    (correction_smooth H v upper B).comp (SlowBorelBase.scaleMap (ChartScales.Q
      n)).contDiff.contDiffOn
      (fun y hy => ⟨mul_pos (ChartScales.Q_pos n) hy.1, hy.2⟩)
  have hmap (n : ℕ) : MapsTo (fun x => coordinates (F := F) x) s.domain BaseChartJets.sumRegion :=
    by
    intro x hx
    have hq := coordinates_range W U hx
    have hw := BaseContextAssembly.nativeStrip_active W U hx
    exact ⟨(div_pos U.qlo_pos (by norm_num)).trans hq.1,
      (NominalConeAssembly.activeLeft_pos W).trans hw.1.1, mem_univ _⟩
  apply class_comp_of_outer_jets (s := s) BaseChartJets.sumRegion_open hs
    (coordinates_unweighted W U) hmap (fun _ x hx => s.zeta_nonneg x hx)
  intro j
  obtain ⟨D, hD, N, hb⟩ := correction_weighted_jets H v upper B j
  let K : ℝ := max 1 (1/(U.qlo/2))
  let R : ℝ := BaseContextAssembly.geometryUpper U
  have hR : 0 < R := BaseContextAssembly.geometryUpper_pos U
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨D * R^F.data.h * K^j, by positivity, N, fun n x hx => ?_⟩
  have hqp : 0 < (coordinates (F := F) x).1 := (hmap n hx).1
  have hxpos : 0 < (coordinates (F := F) x).2.1 := (hmap n hx).2.1
  have hqr := coordinates_range W U hx
  have hinv : 1 / (coordinates (F := F) x).1 ≤ K :=
    (one_div_le_one_div_of_le (div_pos U.qlo_pos (by norm_num)) hqr.1.le).trans (le_max_right _ _)
  have hscaled := scaled_jet_from_blown (correction_smooth H v upper B)
    (ChartScales.Q_pos n) hqp hxpos hK hinv j
  have hbound := hb (ChartScales.Q n * (coordinates (F := F) x).1)
    (mul_pos (ChartScales.Q_pos n) hqp) _ (BaseContextAssembly.nativeStrip_active W U hx)
  have hzeta : FinalSlowBase.weight W (coordinates (F := F) x).2 = s.zeta x :=
    (BaseContextAssembly.nativeStrip_weight W U hx).symm
  have hpos : 0 < FinalSlowBase.edgeDistance W (coordinates (F := F) x).2 :=
    (s.delta_pos x hx).trans_le (native_edgeDistance_le W U hx)
  have hd := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le)
    (inverse_edgeDistance_le_growth W U n hx) N
  have hrpow : (ChartScales.Q n * (coordinates (F := F) x).1)^F.data.h ≤
      s.epsilon n * R^F.data.h := by
    rw [Real.mul_rpow (ChartScales.Q_pos n).le hqp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqp.le hqr.2.le F.data.h_pos.le)
      (Real.rpow_nonneg (ChartScales.Q_pos n).le _)
  calc
    _ ≤ ‖SlowBorelBase.blownJet j (correction H v upper B)
        (ChartScales.Q n * (coordinates (F := F) x).1, (coordinates (F := F) x).2)‖ * K^j := hscaled
    _ ≤ (D * (ChartScales.Q n * (coordinates (F := F) x).1)^F.data.h *
        FinalSlowBase.weight W (coordinates (F := F) x).2 *
        (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹^N) * K^j :=
      mul_le_mul_of_nonneg_right hbound (pow_nonneg (zero_le_one.trans hK) j)
    _ = (D * (ChartScales.Q n * (coordinates (F := F) x).1)^F.data.h * s.zeta x *
        (FinalSlowBase.edgeDistance W (coordinates (F := F) x).2)⁻¹^N) * K^j := by rw [hzeta]
    _ ≤ (D * (s.epsilon n * R^F.data.h) * s.zeta x * s.growth n x^N) * K^j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hK) j)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hD.le) (s.zeta_nonneg x hx))
        hd (pow_nonneg (inv_nonneg.mpr hpos.le) N)
        (mul_nonneg (mul_nonneg hD.le (mul_nonneg (s.epsilon_pos n).le
          (Real.rpow_nonneg hR.le _))) (s.zeta_nonneg x hx))
    _ = _ := by simp only [majorant, Real.rpow_one]; ring

/-- The band scalar is exactly the first power of the class parameter. -/
theorem epsilon_bandBound (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    BandBound (BaseContextAssembly.nativeStrip W U) 1 (ChartScales.epsilon F.data.h) := by
  refine ⟨1, zero_le_one, 0, fun n => ?_⟩
  change ‖ChartScales.epsilon F.data.h n‖ ≤
    1 * (ChartScales.epsilon F.data.h n)^(1:ℝ) * BaseContextAssembly.slowScale n^0
  simp only [Real.norm_of_nonneg (ChartScales.epsilon_pos F.data.h n).le,
    Real.rpow_one, one_mul, pow_zero, mul_one, le_refl]

include H in
/-- Raw positive-radius formula for the literal leading stress, including
the exact physical power of the normalized similarity scale. -/
theorem raw_leading_meanClass (hcone : LeadingStressWeights.FullTrueCone v)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (ChartScales.epsilon F.data.h n *
        (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2)) •
          FinalSlowBase.leadingStress v (coordinates (F := F) x).2) := by
  have h0 : MeanClass (BaseContextAssembly.nativeStrip W U) 0
      (fun _ x => (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2) •
        BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0 (coordinates (F := F) x).2) := by
    simpa only [MeanClass, UnweightedClass, one_mul, zero_add] using
      (coordinate_power_unweighted W U (-CoordinateAlgebra.A F.data.h-1/2)).smul
        (leading_composed_meanClass H v hcone U)
  have h1 : MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (ChartScales.epsilon F.data.h n *
        (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2)) •
        BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0 (coordinates (F := F) x).2) := by
    simpa only [zero_add, smul_smul] using h0.band_smul (epsilon_bandBound (W := W) U)
  apply CurlClassBounds.class_congr h1
  intro n x hx
  dsimp only
  have hw := BaseContextAssembly.nativeStrip_active W U hx
  rw [FinalSlowBase.leading_stress_eq H v (p := (coordinates (F := F) x).2)
    ((NominalConeAssembly.activeLeft_pos W).trans hw.1.1).le (abs_le.mpr hw.2)]

/-- Raw positive-radius formula for the higher stress remainder.  The
extra mean order follows from the actual weighted Borel estimate and the
physical band factor, without a lower bound on the flat weight. -/
theorem raw_higher_meanClass (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (ChartScales.epsilon F.data.h n *
        (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2)) •
          (FinalSlowBase.normalizedStress H v upper B
              (SlowBorelBase.scaleMap (ChartScales.Q n) (coordinates (F := F) x)) -
            FinalSlowBase.leadingStress v (coordinates (F := F) x).2)) := by
  have h0 : MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2) •
        correction H v upper B (SlowBorelBase.scaleMap (ChartScales.Q n) (coordinates (F := F) x)))
          := by
    simpa only [MeanClass, UnweightedClass, one_mul, zero_add] using
      (coordinate_power_unweighted W U (-CoordinateAlgebra.A F.data.h-1/2)).smul
        (correction_composed_meanClass H v upper B U)
  have h1 : MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (ChartScales.epsilon F.data.h n *
        (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2)) •
        correction H v upper B (SlowBorelBase.scaleMap (ChartScales.Q n) (coordinates (F := F) x)))
          := by
    simpa only [show (1:ℝ)+1=2 by norm_num, smul_smul] using
      h0.band_smul (epsilon_bandBound (W := W) U)
  apply CurlClassBounds.class_congr h1
  intro n x hx
  have hw := BaseContextAssembly.nativeStrip_active W U hx
  simp only [correction, SlowBorelBase.scaleMap_apply]
  rw [FinalSlowBase.leading_stress_eq H v (p := (coordinates (F := F) x).2)
    ((NominalConeAssembly.activeLeft_pos W).trans hw.1.1).le (abs_le.mpr hw.2)]

/-- The full raw stress has mean order one. -/
theorem raw_stress_meanClass (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (ChartScales.epsilon F.data.h n *
        (coordinates (F := F) x).1 ^ (-CoordinateAlgebra.A F.data.h-1/2)) •
          FinalSlowBase.normalizedStress H v upper B
            (SlowBorelBase.scaleMap (ChartScales.Q n) (coordinates (F := F) x))) := by
  have hh := (raw_higher_meanClass H v upper B U).mono_exponent (by norm_num : (1:ℝ) ≤ 2)
  apply CurlClassBounds.class_congr (hh.add (raw_leading_meanClass H v hcone U))
  intro n x hx
  simp only [smul_sub, sub_add_cancel]

/-- The leading term of the same actual base context belongs to `M₁`. -/
theorem leadingVirtualStress_meanClass (hcone : LeadingStressWeights.FullTrueCone v)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (BaseContextAssembly.leadingVirtualStress H v) := by
  apply CurlClassBounds.class_congr (raw_leading_meanClass H v hcone U)
  intro n x hx
  exact (BaseContextAssembly.leadingVirtualStress_eq H v n
    (BaseContextAssembly.nativeStrip_time W U hx) (BaseContextAssembly.nativeStrip_radius W U
      hx)).symm

/-- Actual virtual stress, with the signed-radius extension fixed by the
base context.  On this native strip the radius is strictly positive. -/
theorem virtualStress_meanClass (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (BaseContextAssembly.virtualStress H v upper B) := by
  apply CurlClassBounds.class_congr (raw_stress_meanClass H v hcone upper B U)
  intro n x hx
  exact (BaseContextAssembly.virtualStress_normalized H v upper B n
    (BaseContextAssembly.nativeStrip_time W U hx) (BaseContextAssembly.nativeStrip_radius W U
      hx)).symm

/-- The difference between the actual virtual tensor and its actual
leading term belongs to `M₂`, with constants uniform over every band. -/
theorem higherStress_meanClass (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => BaseContextAssembly.virtualStress H v upper B n x -
        BaseContextAssembly.leadingVirtualStress H v n x) := by
  apply CurlClassBounds.class_congr (raw_higher_meanClass H v upper B U)
  intro n x hx
  dsimp only
  rw [BaseContextAssembly.virtualStress_normalized H v upper B n
      (BaseContextAssembly.nativeStrip_time W U hx) (BaseContextAssembly.nativeStrip_radius W U hx),
    BaseContextAssembly.leadingVirtualStress_eq H v n
      (BaseContextAssembly.nativeStrip_time W U hx) (BaseContextAssembly.nativeStrip_radius W U hx)]
  exact smul_sub _ _ _

/-- The two physical tensor entries can be consumed separately by the
correction step, retaining the same strip and class exponent. -/
theorem virtualStress_components (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (BaseContextAssembly.virtualStress H v upper B n x).1) ∧
    MeanClass (BaseContextAssembly.nativeStrip W U) 1
      (fun n x => (BaseContextAssembly.virtualStress H v upper B n x).2) := by
  have hs := virtualStress_meanClass H v hcone upper B U
  exact ⟨hs.map (ContinuousLinearMap.fst ℝ ℝ ℝ), hs.map (ContinuousLinearMap.snd ℝ ℝ ℝ)⟩

theorem higherStress_components (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*F.data.h)) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (BaseContextAssembly.virtualStress H v upper B n x).1 -
        (BaseContextAssembly.leadingVirtualStress H v n x).1) ∧
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (BaseContextAssembly.virtualStress H v upper B n x).2 -
        (BaseContextAssembly.leadingVirtualStress H v n x).2) := by
  have hs := higherStress_meanClass H v upper B U
  exact ⟨hs.map (ContinuousLinearMap.fst ℝ ℝ ℝ), hs.map (ContinuousLinearMap.snd ℝ ℝ ℝ)⟩

end ActualStress

end NavierStokes.BaseStressClasses
