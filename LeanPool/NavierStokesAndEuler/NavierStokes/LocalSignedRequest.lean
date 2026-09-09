/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanDomain
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedWaveUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanChartCompatibility
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction

@[expose] public section

/-!
# A physical signed request on its moving radial shell

The profile coordinate is `R / sqrt(q)`.  Its pullback retains the same flat
edge weight as the primary field.  All slow hypotheses are local; in
particular no positive or bounded extension of `q` to the entire plane is
assumed.
-/

noncomputable section

namespace NavierStokes.LocalSignedRequest

open Set Function Filter MeasureTheory
open WeightedClasses WeightedRadialPrimitive
open scoped ContDiff Topology Interval BigOperators

abbrev Plane := PressureStream.Plane
abbrev Point := PressureStream.Lift Plane

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

section Composition

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact pullback of the weights, with a local domain for the map. -/
noncomputable def localPullbackStrip (s : StripData D) (Φ : E → D)
    (U : Set E) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) : StripData E where
  domain := U ∩ Φ ⁻¹' s.domain
  isOpen_domain := hΦ.continuousOn.isOpen_inter_preimage hU s.isOpen_domain
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (Φ x)
  delta_pos := fun x hx => s.delta_pos (Φ x) hx.2
  zeta := fun x => s.zeta (Φ x)
  zeta_smooth := s.zeta_smooth.comp (hΦ.mono inter_subset_left) (fun _ hx => hx.2)
  zeta_nonneg := fun x hx => s.zeta_nonneg (Φ x) hx.2

/-- Positive jets, rather than the value of an unbounded auxiliary coordinate,
are what the composition estimate uses. -/
noncomputable def BoundedPositiveJets (Φ : E → D) (U : Set E) : Prop :=
  ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ B

theorem class_comp {s : StripData D} {t : StripData E} {w : ℕ → D → ℝ}
    {α : ℝ} {f : ℕ → D → F} (hf : MemClass s w α f)
    (Φ : E → D) (hΦ : ContDiffOn ℝ ∞ Φ t.domain)
    (hmap : MapsTo Φ t.domain s.domain)
    (hε : ∀ n, t.epsilon n = s.epsilon n) (hL : ∀ n, t.slow n = s.slow n)
    (hδ : ∀ x ∈ t.domain, t.delta x = s.delta (Φ x))
    (hjets : BoundedPositiveJets Φ t.domain) :
    MemClass t (fun n x => w n (Φ x)) α (fun n x => f n (Φ x)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n (Φ x) (hmap hx),
    fun n => (hf.smooth n).comp hΦ hmap, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hBj⟩ := hjets m
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, p, ?_⟩
  intro n x hx j hj
  have hA : 0 ≤ majorant s w α C p n (Φ x) :=
    majorant_nonneg s w α hC p n (Φ x) (hf.weight_nonneg n (Φ x) (hmap hx))
  have hbound := norm_iteratedFDerivWithin_comp_le (hf.smooth n) hΦ (nat_le_infty j)
    s.isOpen_domain.uniqueDiffOn t.isOpen_domain.uniqueDiffOn hmap hx
    (C := majorant s w α C p n (Φ x)) (D := B)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i s.isOpen_domain (hmap hx)]
      exact hb n (Φ x) (hmap hx) i (hi.trans hj))
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i t.isOpen_domain hx]
      exact (hBj i hi (him.trans hj) x hx).trans
        (by simpa using pow_le_pow_right₀ hB hi))
  rw [iteratedFDerivWithin_of_isOpen j t.isOpen_domain hx] at hbound
  calc
    ‖iteratedFDeriv ℝ j (fun x => f n (Φ x)) x‖ ≤
        (j.factorial : ℝ) * majorant s w α C p n (Φ x) * B ^ j := hbound
    _ ≤ (m.factorial : ℝ) * majorant s w α C p n (Φ x) * B ^ m := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA
      · exact pow_le_pow_right₀ hB hj
      · positivity
      · positivity
    _ = majorant t (fun n x => w n (Φ x)) α ((m.factorial : ℝ) * C * B ^ m) p n x := by
      simp only [majorant, StripData.growth, hε, hL, hδ x hx]
      ring

theorem class_localPullback {s : StripData D} {w : ℕ → D → ℝ}
    {α : ℝ} {f : ℕ → D → F} (hf : MemClass s w α f)
    (Φ : E → D) (U : Set E) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hjets : BoundedPositiveJets Φ (U ∩ Φ ⁻¹' s.domain)) :
    MemClass (localPullbackStrip s Φ U hU hΦ) (fun n x => w n (Φ x)) α
      (fun n x => f n (Φ x)) :=
  class_comp hf Φ (hΦ.mono inter_subset_left) (fun _ hx => hx.2)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) hjets

end Composition

/-- A genuine open positive-time region with bounds on the actual normalized
similarity coordinate.  Its endpoints and constants are independent of bands. -/
structure SlowRegion (coord : ℝ) where
  carrier : Set Plane
  isOpen : IsOpen carrier
  coord_pos : 0 < coord
  coord_lt_one : coord < 1
  qlo : ℝ
  qhi : ℝ
  qlo_pos : 0 < qlo
  time_pos : ∀ s ∈ carrier, 0 < s.1
  q_mem : ∀ s ∈ carrier, SimilarityCoordinates.coordinateQ coord s ∈ Icc qlo qhi

noncomputable def profileMap (coord : ℝ) (x : Point) : Point :=
  (x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x), x.2)

noncomputable def inverseProfileMap (coord : ℝ) (x : Point) : Point :=
  (Real.sqrt (MeanRankUpdate.chartQ coord x) * x.1, x.2)

@[simp] theorem chartQ_profileMap (coord : ℝ) (x : Point) :
    MeanRankUpdate.chartQ coord (profileMap coord x) = MeanRankUpdate.chartQ coord x := rfl

@[simp] theorem chartQ_inverseProfileMap (coord : ℝ) (x : Point) :
    MeanRankUpdate.chartQ coord (inverseProfileMap coord x) = MeanRankUpdate.chartQ coord x := rfl

theorem profileMap_inverse (coord : ℝ) (x : Point) (hq : 0 < MeanRankUpdate.chartQ coord x) :
    profileMap coord (inverseProfileMap coord x) = x := by
  apply Prod.ext
  · change Real.sqrt (MeanRankUpdate.chartQ coord x) * x.1 /
      Real.sqrt (MeanRankUpdate.chartQ coord x) = x.1
    field_simp
  · rfl

theorem inverseProfileMap_profile (coord : ℝ) (x : Point) (hq : 0 < MeanRankUpdate.chartQ coord x) :
    inverseProfileMap coord (profileMap coord x) = x := by
  apply Prod.ext
  · change Real.sqrt (MeanRankUpdate.chartQ coord x) *
      (x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x)) = x.1
    have hn := (Real.sqrt_pos.mpr hq).ne'
    field_simp
  · rfl

private noncomputable def profileModel (x : PhysicalCoordinateBounds.Point) : ℝ :=
  x.2.1 / Real.sqrt x.1

private noncomputable def inverseProfileModel (x : PhysicalCoordinateBounds.Point) : ℝ :=
  Real.sqrt x.1 * x.2.1

private theorem profileModel_smooth :
    ContDiffOn ℝ ∞ profileModel PhysicalCoordinateBounds.positiveTime := by
  intro x hx
  exact (contDiffAt_snd.fst.div (contDiffAt_fst.sqrt (ne_of_gt hx))
    (Real.sqrt_pos.mpr hx).ne').contDiffWithinAt

private theorem inverseProfileModel_smooth :
    ContDiffOn ℝ ∞ inverseProfileModel PhysicalCoordinateBounds.positiveTime := by
  intro x hx
  exact ((contDiffAt_fst.sqrt (ne_of_gt hx)).mul contDiffAt_snd.fst).contDiffWithinAt

theorem profileMap_smooth {coord : ℝ} (U : SlowRegion coord) :
    ContDiffOn ℝ ∞ (profileMap coord) (PhysicalMeanDomain.slowDomain U.carrier) :=
  (MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
    (fun x hx => U.time_pos x.2.1 hx) profileModel_smooth).prodMk contDiff_snd.contDiffOn

theorem inverseProfileMap_smooth {coord : ℝ} (U : SlowRegion coord) :
    ContDiffOn ℝ ∞ (inverseProfileMap coord) (PhysicalMeanDomain.slowDomain U.carrier) :=
  (MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
    (fun x hx => U.time_pos x.2.1 hx) inverseProfileModel_smooth).prodMk contDiff_snd.contDiffOn

theorem SlowRegion.chartQ_pos {coord : ℝ} (U : SlowRegion coord) {x : Point}
    (hx : x.2.1 ∈ U.carrier) : 0 < MeanRankUpdate.chartQ coord x :=
  U.qlo_pos.trans_le (U.q_mem x.2.1 hx).1

noncomputable def movingStripData {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    StripData Point :=
  localPullbackStrip
    (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U.carrier U.isOpen)
    (profileMap coord) (PhysicalMeanDomain.slowDomain U.carrier)
    (PhysicalMeanDomain.slowDomain_open U.isOpen) (profileMap_smooth U)

theorem movingStrip_domain {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (x : Point) :
    x ∈ (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain ↔
      x.2.1 ∈ U.carrier ∧ (profileMap coord x).1 ∈ Ioo a b := by
  change (x.2.1 ∈ U.carrier ∧ ((profileMap coord x).1 ∈ Ioo a b ∧ x.2.1 ∈ U.carrier)) ↔ _
  tauto

theorem movingStrip_majorant_eq {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (α C : ℝ) (k n : ℕ) (x : Point)
    (hx : (profileMap coord x).1 ∈ Ioo a b) :
    let s := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
    majorant s (fun _ x => s.zeta x) α C k n x =
      (C * ε n ^ α * L n ^ k) * logWeight cL cR a b k
        (x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x)) :=
  PhysicalMeanDomain.localStrip_majorant_eq ha hcL hcR ε L hε hεone hL U.carrier U.isOpen
    α C k n (profileMap coord x) hx

private theorem radialMap_positiveJets {U : Set Plane} (hU : IsOpen U)
    {φ : Point → ℝ} (hφ : ContDiffOn ℝ ∞ φ (PhysicalMeanDomain.slowDomain U))
    {S : Set Point} (hS : S ⊆ PhysicalMeanDomain.slowDomain U)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m φ S C) :
    BoundedPositiveJets (fun x : Point => (φ x, x.2)) S := by
  intro m
  obtain ⟨C, hC, hbound⟩ := hb m
  refine ⟨C + 1, by linarith, ?_⟩
  intro j hj hjm x hx
  have hφx := (hφ.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds (hS hx))).of_le
    (nat_le_infty j)
  rw [PhysicalGraphBounds.iteratedFDeriv_pair hφx contDiffAt_snd,
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact (hbound j hjm x hx).trans (by linarith)
  · have h := ParametricKernelBounds.norm_iteratedFDeriv_linear_le
      (ContinuousLinearMap.snd ℝ ℝ (Plane × Plane)) j hj x
    have hn : ‖ContinuousLinearMap.snd ℝ ℝ (Plane × Plane)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro p
      change ‖p.2‖ ≤ 1 * ‖p‖
      simpa only [one_mul] using norm_snd_le p
    exact h.trans (hn.trans (by linarith))

theorem profileMap_positiveJets {coord rlo rhi : ℝ} (U : SlowRegion coord)
    {S : Set Point} (hS : S ⊆ PhysicalMeanDomain.slowDomain U.carrier)
    (hR : ∀ x ∈ S, x.1 ∈ Icc rlo rhi) : BoundedPositiveJets (profileMap coord) S := by
  have hφ := MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
    (fun x (hx : x ∈ PhysicalMeanDomain.slowDomain U.carrier) => U.time_pos x.2.1 hx)
      profileModel_smooth
  exact radialMap_positiveJets U.isOpen (φ := MeanRankUpdate.chartKernel coord profileModel) hφ hS
    (MeanRankUpdate.chartKernel_finiteJetBounds U.coord_pos U.coord_lt_one U.qlo_pos
      (fun x hx => U.time_pos x.2.1 (hS hx))
      (fun x hx => U.q_mem x.2.1 (hS hx)) hR profileModel_smooth)

theorem inverseProfileMap_positiveJets {coord rlo rhi : ℝ} (U : SlowRegion coord)
    {S : Set Point} (hS : S ⊆ PhysicalMeanDomain.slowDomain U.carrier)
    (hR : ∀ x ∈ S, x.1 ∈ Icc rlo rhi) : BoundedPositiveJets (inverseProfileMap coord) S := by
  have hφ := MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
    (fun x (hx : x ∈ PhysicalMeanDomain.slowDomain U.carrier) => U.time_pos x.2.1 hx)
      inverseProfileModel_smooth
  exact radialMap_positiveJets U.isOpen (φ := MeanRankUpdate.chartKernel coord inverseProfileModel)
    hφ hS
    (MeanRankUpdate.chartKernel_finiteJetBounds U.coord_pos U.coord_lt_one U.qlo_pos
      (fun x hx => U.time_pos x.2.1 (hS hx))
      (fun x hx => U.q_mem x.2.1 (hS hx)) hR inverseProfileModel_smooth)

theorem moving_radial_bounds {coord a b : ℝ} (U : SlowRegion coord) (ha : 0 < a)
    {x : Point} (hx : x.2.1 ∈ U.carrier) (hr : (profileMap coord x).1 ∈ Ioo a b) :
    x.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) := by
  have hq := U.q_mem x.2.1 hx
  have hs := Real.sqrt_pos.mpr (U.chartQ_pos hx)
  change a < x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x) ∧
    x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x) < b at hr
  have hab : a < b := hr.1.trans hr.2
  have hL := Real.sqrt_le_sqrt hq.1
  have hR := Real.sqrt_le_sqrt hq.2
  constructor
  · calc
      Real.sqrt U.qlo * a ≤ Real.sqrt (MeanRankUpdate.chartQ coord x) * a :=
        mul_le_mul_of_nonneg_right hL ha.le
      _ ≤ x.1 := by nlinarith [(lt_div_iff₀ hs).mp hr.1]
  · calc
      x.1 ≤ Real.sqrt (MeanRankUpdate.chartQ coord x) * b :=
        by nlinarith [(div_lt_iff₀ hs).mp hr.2]
      _ ≤ Real.sqrt U.qhi * b := mul_le_mul_of_nonneg_right hR (ha.trans hab).le

section ClassMaps

variable {coord : ℝ} (U : SlowRegion coord)
  (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
  (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

theorem meanClass_profileMap {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α : ℝ} {f : ℕ → Point → V}
    (hf : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
      ε L hε hεone hL U.carrier U.isOpen) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n x => f n (profileMap coord x)) := by
  apply class_localPullback hf (profileMap coord) (PhysicalMeanDomain.slowDomain U.carrier)
    (PhysicalMeanDomain.slowDomain_open U.isOpen) (profileMap_smooth U)
  exact profileMap_positiveJets U (fun _ hx => hx.1)
    (fun _ hx => moving_radial_bounds U ha hx.1 hx.2.1)

theorem meanClass_inverseProfileMap {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α : ℝ} {f : ℕ → Point → V}
    (hf : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
      ε L hε hεone hL U.carrier U.isOpen) α
      (fun n x => f n (inverseProfileMap coord x)) := by
  have hm : MapsTo (inverseProfileMap coord)
      (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U.carrier
        U.isOpen).domain
      (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    change profileMap coord (inverseProfileMap coord x) ∈
      (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U.carrier
        U.isOpen).domain
    rw [profileMap_inverse coord x (U.chartQ_pos hx.2)]
    exact hx
  have h := class_comp
    (t := PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U.carrier U.isOpen)
    hf (inverseProfileMap coord)
    ((inverseProfileMap_smooth U).mono (fun _ hx => hx.2)) hm
    (fun _ => rfl) (fun _ => rfl)
    (fun x hx => by
      change (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
        ε L hε hεone hL U.carrier U.isOpen).delta x =
        (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
          ε L hε hεone hL U.carrier U.isOpen).delta (profileMap coord (inverseProfileMap coord x))
      rw [profileMap_inverse coord x (U.chartQ_pos hx.2)])
    (inverseProfileMap_positiveJets U (fun _ hx => hx.2) (fun _ hx => ⟨hx.1.1.le, hx.1.2.le⟩))
  refine ⟨fun _ x hx => (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
    ε L hε hεone hL U.carrier U.isOpen).zeta_nonneg x hx, h.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := h.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).zeta
      (inverseProfileMap coord x) =
      (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
        ε L hε hεone hL U.carrier U.isOpen).zeta x := by
    change (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
      ε L hε hεone hL U.carrier U.isOpen).zeta (profileMap coord (inverseProfileMap coord x)) = _
    rw [profileMap_inverse coord x (U.chartQ_pos hx.2)]
  simpa only [majorant, he] using hb n x hx j hj

end ClassMaps

section LocalPrimitive

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
theorem compact_fiberLocal (χ : ℝ → ℝ) (M : ℝ) (v : Plane) :
    PhysicalMeanDomain.FiberLocal
      (TransportPrimitive.compactIntegral χ M ((0 : S), v) :
        (PressureStream.Lift S → ℝ) → PressureStream.Lift S → ℝ) := by
  intro f g s he r Y
  simp [TransportPrimitive.compactIntegral, TransportPrimitive.pastIntegral,
    TransportPrimitive.totalIntegral, TransportPrimitive.shift, he]

theorem compact_contDiffOn {a b M : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (v : Plane) {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (TransportPrimitive.compactIntegral χ M ((0 : S), v) f)
      (PhysicalMeanDomain.slowDomain U) :=
  (compact_fiberLocal χ M v).contDiffOn_of_supported
    (fun _ hf hs => TransportPrimitive.compactIntegral_contDiff hχ hf hs) hU hf hs

/-- The actual compact transport primitive preserves the radial flat weight
on an arbitrary open slow domain.  The cutoff is the supplied fixed cutoff. -/
theorem meanClass_compact {a b c d cL cR : ℝ}
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) (α : ℝ) (M : ℕ → ℝ) (v : ℕ → Plane)
    (f : ℕ → PressureStream.Lift S → ℝ)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U))
    (hs : ∀ n, PhysicalMeanDomain.SupportedOn a b U (f n))
    (hclass : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
      ε L hε hεone hL U hU) α f) :
    MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR
      ε L hε hεone hL U hU) α
      (fun n => TransportPrimitive.compactIntegral χ (M n) ((0 : S), v n) (f n)) := by
  refine ⟨hclass.weight_nonneg,
    fun n => (compact_contDiffOn hχ (v n) hU (hf n) (hs n)).mono (fun _ hp => hp.2), ?_⟩
  intro m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds m
  obtain ⟨K, hK, hbound⟩ := PhysicalMeanDomain.transport_compact_finiteJets_fiber
    (S := S) (V := ℝ) ha hac hcd hdb hcL hcR k m χ hχ hleft hright
  refine ⟨K * C, mul_nonneg hK hC, k, ?_⟩
  intro n p hp j hj
  obtain ⟨c₀, _, hcs, hcf, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hp.2 (hf n)
  have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) _)
  have hin : ∀ i ≤ m, ∀ R ∈ Ioo a b, ∀ Y : Plane,
      ‖iteratedFDeriv ℝ i (PhysicalMeanDomain.localize c₀ (f n)) (R, (p.2.1, Y))‖ ≤
        (C * ε n ^ α * L n ^ k) * logWeight cL cR a b k R := by
    intro i hi R hR Y
    rw [he.jet_eq i R Y]
    have h := hb n (R, (p.2.1, Y)) ⟨hR, hp.2⟩ i hi
    rwa [PhysicalMeanDomain.localStrip_majorant_eq ha hcL hcR
      ε L hε hεone hL U hU α C k n _ hR] at h
  have hout := hbound (M n) (v n) _ hcf (PhysicalMeanDomain.localize_supported hcs (hs n))
    (C * ε n ^ α * L n ^ k) hA p.2.1 hin p hp.1 rfl j hj
  rw [((compact_fiberLocal χ (M n) (v n)).germ he).jet_eq j p.1 p.2.2] at hout
  rw [PhysicalMeanDomain.localStrip_majorant_eq ha hcL hcR
    ε L hε hεone hL U hU α (K * C) k n p hp.1]
  exact hout.trans_eq (by ring)

omit [FiniteDimensional ℝ S] in
theorem sigma_fiberLocal (P : SignedStressPrimitive.Patch) (e : ℕ) :
    PhysicalMeanDomain.FiberLocal
      (SignedStressPrimitive.sigma P e :
        (PressureStream.Lift S → ℝ) → PressureStream.Lift S → ℝ) := by
  intro f g s he r Y
  simp [SignedStressPrimitive.sigma, SignedStressPrimitive.primitive,
    SignedStressPrimitive.weightedSource, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral, TransportPrimitive.totalIntegral,
    TransportPrimitive.shift, he]

theorem sigma_contDiffOn (P : SignedStressPrimitive.Patch) (e : ℕ)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn P.a P.b U f) :
    ContDiffOn ℝ ∞ (SignedStressPrimitive.sigma P e f) (PhysicalMeanDomain.slowDomain U) :=
  (sigma_fiberLocal P e).contDiffOn_of_supported
    (fun _ hf hs => SignedStressPrimitive.sigma_contDiff P e hf hs) hU hf hs

theorem meanClass_sigma (P : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U))
    (hs : ∀ n, PhysicalMeanDomain.SupportedOn P.a P.b U (f n))
    (hclass : MeanClass (PhysicalMeanDomain.localStripData P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL U hU) α f) :
    MeanClass (PhysicalMeanDomain.localStripData P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL U hU) α (fun n => SignedStressPrimitive.sigma P e (f n)) := by
  have hw := PhysicalMeanDomain.meanClass_radialMultiply P.a_pos hcL hcR
    ε L hε hεone hL U hU hclass (contDiff_id.pow e)
  have hi := meanClass_compact P.a_pos P.a_lt_left P.left_lt_right P.right_lt_b hcL hcR
    (SignedStressPrimitive.cutoff P) (SignedStressPrimitive.cutoff_contDiff P)
    (fun _ h => SignedStressPrimitive.cutoff_zero P h)
    (fun _ h => SignedStressPrimitive.cutoff_one P h)
    ε L hε hεone hL U hU α (fun _ => 0) (fun _ => 0)
    (fun n => SignedStressPrimitive.weightedSource e (f n))
    (fun n => (contDiff_fst.pow e).contDiffOn.mul (hf n))
    (fun n p hp hz => hs n p hp (right_ne_zero_of_mul hz)) hw
  exact PhysicalMeanDomain.meanClass_radialMultiply P.a_pos hcL hcR
    ε L hε hεone hL U hU hi (SignedStressPrimitive.inversePower_contDiff P e).neg

theorem meanClass_barSigma (P : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U))
    (hs : ∀ n, PhysicalMeanDomain.SupportedOn P.a P.b U (f n))
    (hclass : MeanClass (PhysicalMeanDomain.localStripData P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL U hU) α f) :
    MeanClass (PhysicalMeanDomain.localStripData P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL U hU) α
      (fun n x => SignedStressPrimitive.barSigma P e (f n) (x.1, x.2.1)) := by
  have hm := PhysicalMeanDomain.meanClass_liftedTorusAverage P.a_pos hcL hcR
    ε L hε hεone hL U hU hf hclass
  have h := meanClass_sigma P e hcL hcR ε L hε hεone hL U hU
    (fun n => PhysicalMeanDomain.liftedTorusAverage_contDiffOn hU (hf n))
    (fun n => PhysicalMeanDomain.liftedTorusAverage_supportedOn hU (hf n) (hs n)) hm
  exact MeanRankUpdate.meanClass_congr_on h
    (fun n x _ => (SignedWaveUpdate.sigma_liftedTorusAverage P e (f n) x).symm)

end LocalPrimitive

section PhysicalRequest

/-- Support on the same moving shell used in the weight. -/
noncomputable def MovingSupport (a b coord : ℝ) (U : Set Plane) (f : Point → ℝ) : Prop :=
  ∀ x, x.2.1 ∈ U → f x ≠ 0 → (profileMap coord x).1 ∈ Icc a b

theorem inverseProfile_source_smooth {coord : ℝ} (U : SlowRegion coord) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier)) :
    ContDiffOn ℝ ∞ (fun x => f (inverseProfileMap coord x))
      (PhysicalMeanDomain.slowDomain U.carrier) :=
  hf.comp (inverseProfileMap_smooth U) (fun _ hx => hx)

theorem inverseProfile_source_supported {coord a b : ℝ} (U : SlowRegion coord)
    {f : Point → ℝ} (hs : MovingSupport a b coord U.carrier f) :
    PhysicalMeanDomain.SupportedOn a b U.carrier (fun x => f (inverseProfileMap coord x)) := by
  intro x hx hn
  have h := hs (inverseProfileMap coord x) hx hn
  rwa [profileMap_inverse coord x (U.chartQ_pos hx)] at h

theorem chartKernel_unweighted {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {g : PhysicalCoordinateBounds.Point → ℝ}
    (hg : ContDiffOn ℝ ∞ g PhysicalCoordinateBounds.positiveTime) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ => MeanRankUpdate.chartKernel coord g) := by
  apply unweighted_of_finiteJetBounds
  · exact MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
      (fun x hx => U.time_pos x.2.1 hx.1) hg
  · intro m
    obtain ⟨C, _, hC⟩ := MeanRankUpdate.chartKernel_finiteJetBounds U.coord_pos U.coord_lt_one
      U.qlo_pos (fun x (hx : x ∈ (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain) =>
        U.time_pos x.2.1 hx.1)
      (fun x hx => U.q_mem x.2.1 hx.1)
      (fun x hx => moving_radial_bounds U ha hx.1 hx.2.1) hg m
    exact ⟨C, hC⟩

theorem length_unweighted {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ x => Real.sqrt (MeanRankUpdate.chartQ coord x)) := by
  apply chartKernel_unweighted U a b cL cR ha hcL hcR ε L hε hεone hL
    (g := fun p => Real.sqrt p.1)
  intro x hx
  exact (contDiffAt_fst.sqrt (ne_of_gt hx)).contDiffWithinAt

theorem qPower_unweighted {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (p : ℝ) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ x => MeanRankUpdate.chartQ coord x ^ p) := by
  apply chartKernel_unweighted U a b cL cR ha hcL hcR ε L hε hεone hL
    (g := fun x => x.1 ^ p)
  intro x hx
  exact (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt

theorem physicalBarSigma_profile (P : SignedStressPrimitive.Patch) (e : ℕ)
    (coord : ℝ) (f : Point → ℝ) (x : Point) :
    SignedStressPrimitive.physicalBarSigma P e (SimilarityCoordinates.coordinateQ coord) f
        (x.1, x.2.1) =
      Real.sqrt (MeanRankUpdate.chartQ coord x) *
        SignedStressPrimitive.barSigma P e (fun y => f (inverseProfileMap coord y))
          ((profileMap coord x).1, x.2.1) := rfl

theorem torusAverage_inverseProfileMap (coord : ℝ) (f : Point → ℝ) (x : Point) :
    MeanMomentBounds.liftedTorusAverage (fun y => f (inverseProfileMap coord y)) x =
      MeanMomentBounds.liftedTorusAverage f (inverseProfileMap coord x) := rfl

theorem meanClass_liftedTorusAverage {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => MeanMomentBounds.liftedTorusAverage (f n)) := by
  have hi := meanClass_inverseProfileMap U a b cL cR ha hcL hcR ε L hε hεone hL hclass
  have hb := PhysicalMeanDomain.meanClass_liftedTorusAverage ha hcL hcR ε L hε hεone hL
    U.carrier U.isOpen (fun n => inverseProfile_source_smooth U (hf n)) hi
  have hp := meanClass_profileMap U a b cL cR ha hcL hcR ε L hε hεone hL hb
  apply MeanRankUpdate.meanClass_congr_on hp
  intro n x hx
  rw [torusAverage_inverseProfileMap, inverseProfileMap_profile coord x (U.chartQ_pos hx.1)]

theorem meanClass_centered {coord : ℝ} (U : SlowRegion coord)
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n => TemporalMeanUpdate.centered (f n)) :=
  MeanIncrementBounds.Class.sub hclass
    (meanClass_liftedTorusAverage U a b cL cR ha hcL hcR ε L hε hεone hL hf hclass)

/-- The physical signed primitive, in the actual moving weight, costs no
power of epsilon.  The only constants come from the fixed profile and the
bounded normalized slow region. -/
theorem meanClass_physicalBarSigma {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, MovingSupport P.a P.b coord U.carrier (f n))
    (hclass : MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α f) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α
      (fun n x => SignedStressPrimitive.physicalBarSigma P e
        (SimilarityCoordinates.coordinateQ coord) (f n) (x.1, x.2.1)) := by
  have hi := meanClass_inverseProfileMap U P.a P.b cL cR P.a_pos hcL hcR
    ε L hε hεone hL hclass
  have hb := meanClass_barSigma P e hcL hcR ε L hε hεone hL U.carrier U.isOpen
    (fun n => inverseProfile_source_smooth U (hf n))
    (fun n => inverseProfile_source_supported U (hs n)) hi
  have hp := meanClass_profileMap U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL hb
  have hmul := MeanIncrementBounds.Class.coefficient_mul
    (length_unweighted U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) hp
  simp only [zero_add] at hmul
  simp only [physicalBarSigma_profile]
  exact hmul

/-- Both components are computed from the same actual state. -/
noncomputable def requestedStress (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ℕ → Point → SignedWaveUpdate.Vec2 :=
  fun n x => ![SignedStressPrimitive.physicalBarSigma P 2 (SimilarityCoordinates.coordinateQ coord)
      (u.thetaResidual c n) (x.1, x.2.1),
    SignedStressPrimitive.physicalBarSigma P 1 (SimilarityCoordinates.coordinateQ coord)
      (u.axialResidual c n) (x.1, x.2.1)]

noncomputable def normalizedRequest (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ℕ → Point → SignedWaveUpdate.Vec2 :=
  fun n x => (s.epsilon n)⁻¹ • requestedStress P coord c u n x

theorem normalizedRequest_class {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsθ : ∀ n, MovingSupport P.a P.b coord U.carrier (u.thetaResidual c n))
    (hsz : ∀ n, MovingSupport P.a P.b coord U.carrier (u.axialResidual c n))
    (hcθ : MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (u.thetaResidual c))
    (hcz : MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (u.axialResidual c)) :
    ∀ i, MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α - 1)
      (fun n x => normalizedRequest
        (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) P coord c u n x i) := by
  have h1 := meanClass_physicalBarSigma U P 2 hcL hcR ε L hε hεone hL hθ hsθ hcθ
  have h2 := meanClass_physicalBarSigma U P 1 hcL hcR ε L hε hεone hL hz hsz hcz
  have hscale := bandBound_rpow
    (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (-1)
  intro i
  fin_cases i
  · simpa [normalizedRequest, requestedStress, Real.rpow_neg_one, sub_eq_add_neg] using
    h1.band_smul hscale
  · simpa [normalizedRequest, requestedStress, Real.rpow_neg_one, sub_eq_add_neg] using
    h2.band_smul hscale

end PhysicalRequest

section AngularLift

theorem normalizedRequest_frozen (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (v : Plane) :
    SignedWaveUpdate.FrozenAlong (0, (0, v)) (normalizedRequest s P coord c u) := by
  rintro n ⟨r,z,Y⟩ t
  simp only [normalizedRequest, requestedStress, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

/-- Genuine pullback to the full coefficient domain, including the angle. -/
noncomputable def fullRequest (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ℕ → Point × ℝ → SignedWaveUpdate.Vec2 :=
  fun n x => normalizedRequest s P coord c u n x.1

theorem fullRequest_class (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) {α : ℝ}
    (h : ∀ i, MeanClass s α (fun n x => normalizedRequest s P coord c u n x i)) :
    ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) α
      (fun n x => fullRequest s P coord c u n x i) :=
  fun i => HarmonicWaveInteraction.class_lift (h i)

theorem fullRequest_angle_frozen (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    SignedWaveUpdate.FrozenAlong (0, 1) (fullRequest s P coord c u) := by
  rintro n ⟨x,θ⟩ t
  simp only [fullRequest, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

theorem fullRequest_torus_frozen (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (v : Plane) :
    SignedWaveUpdate.FrozenAlong ((0, (0, v)), 0) (fullRequest s P coord c u) := by
  rintro n ⟨x,θ⟩ t
  exact normalizedRequest_frozen s P coord c u v n x t

end AngularLift

section ChartCoherence

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem sigma_fiber_congr (P : SignedStressPrimitive.Patch) (e : ℕ)
    {f : ℝ × S → ℝ} {g : ℝ × T → ℝ} {s : S} {t : T}
    (he : ∀ r, f (r, s) = g (r, t)) (r : ℝ) :
    SignedStressPrimitive.sigma P e f (r, s) = SignedStressPrimitive.sigma P e g (r, t) := by
  simp [SignedStressPrimitive.sigma, SignedStressPrimitive.primitive,
    SignedStressPrimitive.weightedSource, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral, TransportPrimitive.totalIntegral, TransportPrimitive.shift, he]

theorem sigma_fiber_mul (P : SignedStressPrimitive.Patch) (e : ℕ) (u : ℝ)
    {f : ℝ × S → ℝ} {g : ℝ × T → ℝ} {s : S} {t : T}
    (he : ∀ r, f (r, s) = u * g (r, t)) (r : ℝ) :
    SignedStressPrimitive.sigma P e f (r, s) = u * SignedStressPrimitive.sigma P e g (r, t) := by
  rw [← SignedStressPrimitive.sigma_slow_mul P e (fun _ : T => u) g (r, t)]
  exact sigma_fiber_congr P e he r

/-- Physical radial scaling changes a primitive by exactly one length factor. -/
theorem physicalSigma_scaled_fiber (P : SignedStressPrimitive.Patch) (e : ℕ)
    {q : S → ℝ} {q' : T → ℝ} {f : ℝ × S → ℝ} {g : ℝ × T → ℝ}
    {s : S} {t : T} {l : ℝ} (hl : 0 < l) (hq : 0 < q s) (u : ℝ)
    (hlength : Real.sqrt (q' t) = l * Real.sqrt (q s))
    (he : ∀ r, f (r, s) = u * g (l * r, t)) (r : ℝ) :
    SignedStressPrimitive.physicalSigma P e q f (r, s) =
      (u / l) * SignedStressPrimitive.physicalSigma P e q' g (l * r, t) := by
  have hn := (Real.sqrt_pos.mpr hq).ne'
  have hnative : ∀ v, SignedStressPrimitive.nativeSource q f (v, s) =
      u * SignedStressPrimitive.nativeSource q' g (v, t) := by
    intro v
    simp only [SignedStressPrimitive.nativeSource, SignedStressPrimitive.lengthScale, he, hlength]
    congr 2
    ring_nf
  have hr : (l * r) / Real.sqrt (q' t) = r / Real.sqrt (q s) := by
    rw [hlength]
    field_simp
  unfold SignedStressPrimitive.physicalSigma SignedStressPrimitive.lengthScale
  rw [sigma_fiber_mul P e u hnative, hr, hlength]
  field_simp

theorem torusAverage_coverPull_local (l : ℝ) (C : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {U : Set T} (hU : IsOpen U) {f : PressureStream.Lift T → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) (r : ℝ) {s : S} (hs : C s ∈ U) :
    PressureStream.torusAverage (MeanChartCompatibility.coverPull l C k u f) (r, s) =
      u * PressureStream.torusAverage f (l * r, C s) := by
  have hg : ContDiff ℝ ∞ (fun Y : Plane => f (l * r, (C s, Y))) := by
    rw [contDiff_iff_contDiffAt]
    intro Y
    exact (hf.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hs)).comp Y
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    u * f (l * r, (C s, TemporalMeanUpdate.coverMap k (x, y)))) =
      u * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (l * r, (C s, (x, y))))
  simp only [intervalIntegral.integral_const_mul]
  congr 1
  change TorusAverages.squareAverage (fun Y => f (l * r, (C s, TemporalMeanUpdate.coverMap k Y))) =
    _
  simp_rw [TemporalMeanUpdate.coverMap_eq_iterate]
  exact TorusAverages.squareAverage_covering_iterate_real hg.continuous (hp (l * r) (C s) hs) k

/-- One physical request has all chart views.  Only the target slow fiber
needs regularity and periodicity. -/
theorem physicalBarSigma_chart (P : SignedStressPrimitive.Patch) (e : ℕ)
    {q : S → ℝ} {q' : T → ℝ} {f : PressureStream.Lift S → ℝ}
    {g : PressureStream.Lift T → ℝ} {s : S} {l : ℝ} (hl : 0 < l) (hq : 0 < q s)
    (C : S →L[ℝ] T) (k : ℕ) (u : ℝ) {U : Set T} (hU : IsOpen U) (hs : C s ∈ U)
    (hg : ContDiffOn ℝ ∞ g (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U g)
    (hlength : Real.sqrt (q' (C s)) = l * Real.sqrt (q s))
    (he : ∀ r Y, f (r, (s, Y)) = u * g (l * r, (C s, TemporalMeanUpdate.coverMap k Y)))
    (r : ℝ) :
    SignedStressPrimitive.physicalBarSigma P e q f (r, s) =
      (u / l) * SignedStressPrimitive.physicalBarSigma P e q' g (l * r, C s) := by
  apply physicalSigma_scaled_fiber P e hl hq u hlength
  intro v
  have hslice : PressureStream.torusAverage f (v, s) =
      PressureStream.torusAverage (MeanChartCompatibility.coverPull l C k u g) (v, s) :=
    PressureStream.torusAverage_congr_slice (v, s) (he v)
  rw [hslice]
  exact torusAverage_coverPull_local l C k u hU hg hp v hs

/-- This field has no band index: every normalized request below represents
this same physical signed stress. -/
noncomputable def physicalRequestedStress (P : SignedStressPrimitive.Patch) (q : S → ℝ)
    (Fθ Fz : PressureStream.Lift S → ℝ) (x : ℝ × S) : SignedWaveUpdate.Vec2 :=
  ![SignedStressPrimitive.physicalBarSigma P 2 q Fθ x,
    SignedStressPrimitive.physicalBarSigma P 1 q Fz x]

theorem stress_unit_factor {Q : ℝ} (hQ : 0 < Q) (A : ℝ) :
    Q ^ (2 * A) * (Q ^ (-(2 * A + 1 / 2)) / Q ^ (-(1 / 2 : ℝ))) = 1 := by
  rw [← Real.rpow_sub hQ, ← Real.rpow_add hQ]
  convert! Real.rpow_zero Q using 1 ; ring_nf

/-- Exact Q-normalization of one physical primitive.  The hypotheses refer
to the actual represented source, not to the desired stress or its bounds. -/
theorem normalizedRequest_represents {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (s : StripData Point)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) {Q : ℝ} (hQ : 0 < Q) (A : ℝ)
    (q : S → ℝ) (Fθ Fz : PressureStream.Lift S → ℝ)
    (C : S →L[ℝ] Plane) (k : ℕ) (t : S) (ht : C t ∈ U.carrier) (hqt : 0 < q t)
    (hθ : ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hlength : Real.sqrt (SimilarityCoordinates.coordinateQ coord (C t)) =
      Q ^ (-(1 / 2 : ℝ)) * Real.sqrt (q t))
    (heθ : ∀ r Y, Fθ (r, (t, Y)) = Q ^ (-(2 * A + 1 / 2)) *
      u.thetaResidual c n (Q ^ (-(1 / 2 : ℝ)) * r, (C t, TemporalMeanUpdate.coverMap k Y)))
    (hez : ∀ r Y, Fz (r, (t, Y)) = Q ^ (-(2 * A + 1 / 2)) *
      u.axialResidual c n (Q ^ (-(1 / 2 : ℝ)) * r, (C t, TemporalMeanUpdate.coverMap k Y)))
    (r : ℝ) (Y : Plane) :
    normalizedRequest s P coord c u n (Q ^ (-(1 / 2 : ℝ)) * r, (C t, Y)) =
      (s.epsilon n)⁻¹ • (Q ^ (2 * A) • physicalRequestedStress P q Fθ Fz (r, t)) := by
  have h1 := physicalBarSigma_chart P 2 (Real.rpow_pos_of_pos hQ _) hqt C k
    (Q ^ (-(2 * A + 1 / 2))) U.isOpen ht hθ hpθ hlength heθ r
  have h2 := physicalBarSigma_chart P 1 (Real.rpow_pos_of_pos hQ _) hqt C k
    (Q ^ (-(2 * A + 1 / 2))) U.isOpen ht hz hpz hlength hez r
  have hfct := stress_unit_factor hQ A
  apply congrArg (fun v : SignedWaveUpdate.Vec2 => (s.epsilon n)⁻¹ • v)
  funext i
  fin_cases i
  · change _ = Q ^ (2 * A) * SignedStressPrimitive.physicalBarSigma P 2 q Fθ (r, t)
    rw [h1, ← mul_assoc, hfct, one_mul]
    rfl
  · change _ = Q ^ (2 * A) * SignedStressPrimitive.physicalBarSigma P 1 q Fz (r, t)
    rw [h2, ← mul_assoc, hfct, one_mul]
    rfl

theorem physicalSigma_fiber_congr (P : SignedStressPrimitive.Patch) (e : ℕ)
    {q : S → ℝ} {q' : T → ℝ} {f : ℝ × S → ℝ} {g : ℝ × T → ℝ}
    {s : S} {t : T} (hq : q s = q' t) (he : ∀ r, f (r, s) = g (r, t)) (r : ℝ) :
    SignedStressPrimitive.physicalSigma P e q f (r, s) =
      SignedStressPrimitive.physicalSigma P e q' g (r, t) := by
  unfold SignedStressPrimitive.physicalSigma SignedStressPrimitive.lengthScale
  rw [hq]
  congr 1
  apply sigma_fiber_congr P e
  intro v
  simpa only [SignedStressPrimitive.nativeSource, SignedStressPrimitive.lengthScale, hq] using
    he (Real.sqrt (q' t) * v)

end ChartCoherence

section LocalIdentities

private noncomputable def frozenBar (f : Point → ℝ) (s : Plane) (x : ℝ × ℝ) : ℝ :=
  PressureStream.torusAverage f (x.1, s)

private theorem frozenBar_smooth {U : Set Plane} (hU : IsOpen U) {s : Plane} (hs : s ∈ U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) :
    ContDiff ℝ ∞ (frozenBar f s) := by
  have hb := PhysicalMeanDomain.liftedTorusAverage_contDiffOn hU hf
  rw [contDiff_iff_contDiffAt]
  intro x
  change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
    MeanMomentBounds.liftedTorusAverage f (z.1, (s, (0 : Plane)))) x
  have hh := hb.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds
    (show (x.1, (s, (0 : Plane))) ∈ PhysicalMeanDomain.slowDomain U from hs))
  have hmap : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.1, (s, (0 : Plane)))) x :=
    contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_const)
  have hc := hh.comp x hmap
  exact hc

private theorem frozenBar_supported {coord : ℝ} (P : SignedStressPrimitive.Patch)
    {U : Set Plane} {s : Plane} (hs : s ∈ U) {f : Point → ℝ}
    (hsupp : MovingSupport P.a P.b coord U f) :
    SignedStressPrimitive.PhysicalSupport P (fun _ : ℝ => SimilarityCoordinates.coordinateQ coord s)
      (frozenBar f s) := by
  intro x hx
  by_contra hn
  apply hx
  apply PressureStream.torusAverage_zero_of_forall
  intro Y
  by_contra hY
  exact hn (hsupp (x.1, (s, Y)) hs hY)

private theorem frozenBar_sigma (P : SignedStressPrimitive.Patch) (e : ℕ)
    (coord : ℝ) (f : Point → ℝ) (s : Plane) (r : ℝ) :
    SignedStressPrimitive.physicalBarSigma P e (SimilarityCoordinates.coordinateQ coord) f (r, s) =
      SignedStressPrimitive.physicalSigma P e
        (fun _ : ℝ => SimilarityCoordinates.coordinateQ coord s) (frozenBar f s) (r, 0) :=
  physicalSigma_fiber_congr (S := Plane) (T := ℝ) P e
    (q := SimilarityCoordinates.coordinateQ coord)
    (q' := fun _ : ℝ => SimilarityCoordinates.coordinateQ coord s)
    (f := PressureStream.torusAverage f) (g := frozenBar f s) (s := s) (t := 0)
    rfl (fun _ => rfl) r

theorem physicalBarSigma_eq_negative_primitive {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) {s : Plane} (hsp : s ∈ U.carrier) (r : ℝ) :
    SignedStressPrimitive.physicalBarSigma P e (SimilarityCoordinates.coordinateQ coord) f (r, s) =
      -(∫ t in (0 : ℝ)..r, t ^ e * SignedStressPrimitive.physicalAdjusted P e
        (SimilarityCoordinates.coordinateQ coord) (PressureStream.torusAverage f) (t, s)) / r ^ e
          := by
  rw [frozenBar_sigma]
  exact SignedStressPrimitive.physicalSigma_eq_negative_primitive P e contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem s hsp).1)
    (frozenBar_smooth U.isOpen hsp hf) (frozenBar_supported P hsp hs) (r, 0)

theorem physicalBarSigma_angular_divergence {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) {s : Plane} (hsp : s ∈ U.carrier)
    {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 2
      (fun t => SignedStressPrimitive.physicalBarSigma P 2 (SimilarityCoordinates.coordinateQ
        coord) f (t, s)) r =
      -SignedStressPrimitive.physicalAdjusted P 2 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage f) (r, s) := by
  simp_rw [frozenBar_sigma]
  exact SignedStressPrimitive.physical_angular_divergence P contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem s hsp).1)
    (frozenBar_smooth U.isOpen hsp hf) (frozenBar_supported P hsp hs) 0 hr

theorem physicalBarSigma_axial_divergence {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) {s : Plane} (hsp : s ∈ U.carrier)
    {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 1
      (fun t => SignedStressPrimitive.physicalBarSigma P 1 (SimilarityCoordinates.coordinateQ
        coord) f (t, s)) r =
      -SignedStressPrimitive.physicalAdjusted P 1 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage f) (r, s) := by
  simp_rw [frozenBar_sigma]
  exact SignedStressPrimitive.physical_axial_divergence P contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem s hsp).1)
    (frozenBar_smooth U.isOpen hsp hf) (frozenBar_supported P hsp hs) 0 hr

theorem physicalAdjusted_moment_zero {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) {s : Plane} (hsp : s ∈ U.carrier) :
    SignedStressPrimitive.mass e (SignedStressPrimitive.physicalAdjusted P e
      (SimilarityCoordinates.coordinateQ coord) (PressureStream.torusAverage f)) s = 0 :=
  SignedStressPrimitive.physicalAdjusted_moment_zero P e contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem s hsp).1)
    (frozenBar_smooth U.isOpen hsp hf) (frozenBar_supported P hsp hs) 0

theorem physicalBarSigma_supported {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) :
    MovingSupport P.a P.b coord U.carrier
      (fun x => SignedStressPrimitive.physicalBarSigma P e
        (SimilarityCoordinates.coordinateQ coord) f (x.1, x.2.1)) := by
  intro x hx hn
  change SignedStressPrimitive.physicalBarSigma P e
    (SimilarityCoordinates.coordinateQ coord) f (x.1, x.2.1) ≠ 0 at hn
  rw [frozenBar_sigma] at hn
  exact SignedStressPrimitive.physicalSigma_supported P e contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem x.2.1 hx).1)
    (frozenBar_smooth U.isOpen hx hf) (frozenBar_supported P hx hs) (x.1, 0) hn

theorem physicalBarSigma_slice_compact {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) {s : Plane} (hsp : s ∈ U.carrier) :
    HasCompactSupport (fun r => SignedStressPrimitive.physicalBarSigma P e
      (SimilarityCoordinates.coordinateQ coord) f (r, s)) := by
  simp_rw [frozenBar_sigma]
  exact SignedStressPrimitive.physicalSigma_slice_compact P e contDiff_const
    (fun _ => U.qlo_pos.trans_le (U.q_mem s hsp).1)
    (frozenBar_smooth U.isOpen hsp hf) (frozenBar_supported P hsp hs) 0

theorem physicalBarSigma_contDiffOn {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {f : Point → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : MovingSupport P.a P.b coord U.carrier f) :
    ContDiffOn ℝ ∞ (fun x : Point => SignedStressPrimitive.physicalBarSigma P e
      (SimilarityCoordinates.coordinateQ coord) f (x.1, x.2.1))
      (PhysicalMeanDomain.slowDomain U.carrier) := by
  have hg := inverseProfile_source_smooth U hf
  have hgs := inverseProfile_source_supported U hs
  have hb := sigma_contDiffOn P e U.isOpen
    (PhysicalMeanDomain.liftedTorusAverage_contDiffOn U.isOpen hg)
    (PhysicalMeanDomain.liftedTorusAverage_supportedOn U.isOpen hg hgs)
  have hr : ContDiffOn ℝ ∞ (fun x : Point => Real.sqrt (MeanRankUpdate.chartQ coord x))
      (PhysicalMeanDomain.slowDomain U.carrier) := by
    apply MeanRankUpdate.chartKernel_contDiffOn U.coord_pos U.coord_lt_one
      (g := fun p => Real.sqrt p.1) (fun x hx => U.time_pos x.2.1 hx)
    intro x hx
    exact (contDiffAt_fst.sqrt (ne_of_gt hx)).contDiffWithinAt
  have h := hr.mul (hb.comp (profileMap_smooth U) (fun _ hx => hx))
  simp only [physicalBarSigma_profile]
  change ContDiffOn ℝ ∞ (fun x => Real.sqrt (MeanRankUpdate.chartQ coord x) *
    SignedStressPrimitive.sigma P e (MeanMomentBounds.liftedTorusAverage
      (fun x => f (inverseProfileMap coord x))) (profileMap coord x)) _ at h
  simp only [SignedWaveUpdate.sigma_liftedTorusAverage] at h
  exact h

end LocalIdentities

section RemovedBump

theorem physicalDensity_meanClass {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) 0
      (fun _ x => SignedStressPrimitive.physicalDensity P e
        (SimilarityCoordinates.coordinateQ coord) (x.1, x.2.1)) := by
  have hd := PhysicalMeanDomain.memClass_restrict P.a_pos hcL hcR ε L hε hεone hL U.carrier U.isOpen
    (SignedStressPrimitive.momentDensity_meanClass (E := Plane × Plane) P e hcL hcR ε L hε hεone hL)
  have hp := meanClass_profileMap U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL hd
  have hm : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) 0
      (fun _ x => (Real.sqrt (MeanRankUpdate.chartQ coord x) ^ (e + 1))⁻¹) := by
    apply chartKernel_unweighted U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL
      (g := fun p => (Real.sqrt p.1 ^ (e + 1))⁻¹)
    intro x hx
    exact (((contDiffAt_fst.sqrt (ne_of_gt hx)).pow (e + 1)).inv
      (pow_ne_zero _ (Real.sqrt_pos.mpr hx).ne')).contDiffWithinAt
  have h := MeanIncrementBounds.Class.coefficient_mul hm hp
  simp only [zero_add, SignedStressPrimitive.physicalDensity, SignedStressPrimitive.lengthScale,
    profileMap, MeanRankUpdate.chartQ, MeanRankUpdate.chartInput_apply,
      PhysicalCoordinateBounds.qCoord,
    div_eq_mul_inv, mul_comm] at h ⊢
  exact h

theorem fderiv_slowLift (D : Plane → ℝ) (x : Point) (v : Plane)
    (hD : DifferentiableAt ℝ D x.2.1) :
    fderiv ℝ (fun p : Point => D p.2.1) x (0, (v, 0)) = fderiv ℝ D x.2.1 v := by
  let L : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane Plane).comp
    (ContinuousLinearMap.snd ℝ ℝ (Plane × Plane))
  have h := hD.hasFDerivAt.comp x L.hasFDerivAt
  change HasFDerivAt (fun p : Point => D p.2.1) ((fderiv ℝ D x.2.1).comp L) x at h
  rw [h.fderiv]
  rfl

/-- A measured moment equal to epsilon times a slow derivative yields the
extra epsilon in the actual removed physical bump, in the same moving weight. -/
theorem physicalBump_improvedClass_of_moment {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (F : ℕ → Point → ℝ) (D : ℕ → Plane → ℝ) (v : Plane) (α : ℝ)
    (hD : ∀ n, ContDiffOn ℝ ∞ (D n) U.carrier)
    (hclass : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => D n x.2.1))
    (hmoment : ∀ n s, s ∈ U.carrier →
      SignedStressPrimitive.mass e (PressureStream.torusAverage (F n)) s =
        ε n * fderiv ℝ (D n) s v) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P e (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage (F n)) (x.1, x.2.1)) := by
  have hd := hclass.directional ((0 : ℝ), (v, (0 : Plane)))
  have hm := MeanIncrementBounds.Class.mul_coefficient
    (physicalDensity_meanClass U P e hcL hcR ε L hε hεone hL) hd
  have hb := hm.band_smul (bandBound_rpow
    (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) 1)
  simp only [zero_add] at hb
  apply MeanRankUpdate.meanClass_congr_on hb
  intro n x hx
  simp only [SignedStressPrimitive.physicalBump, hmoment n x.2.1 hx.1,
    Real.rpow_one, smul_eq_mul, Pi.mul_apply]
  rw [fderiv_slowLift (D n) x v
    (((hD n).contDiffAt (U.isOpen.mem_nhds hx.1)).differentiableAt (by simp))]
  change _ = ε n * _
  ring

end RemovedBump

end NavierStokes.LocalSignedRequest
