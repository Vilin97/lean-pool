/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseChartJets

@[expose] public section

/-!
# Primary phase geometry for the constructed slow base

The representatives are chosen in the actual positive-time mask support.
The phase carrier is an open two-mesh cell; the larger three-mesh cell is
used for the local base estimates.  Compact constants use the genuine
stable inverse branch, including its regular zero-time boundary.
-/

noncomputable section

namespace NavierStokes.PrimaryGeometryAssembly

open Set Filter Function
open scoped Topology ContDiff InnerProductSpace EuclideanSpace

abbrev Slow := PhaseCalculus.Slow
abbrev Plane := MovingFrameODE.Plane


/-! ## The actual positive support cells -/

/-- Two meshes leave an open neighborhood of the closed one-mesh mask
support.  They also give the precise `3/S³` representative distance used
by the phase comparison theorem. -/
noncomputable def openCell (n : ℕ) (k : SlotColoring.Grid) : Set Slow :=
  let s := SquaredPartition.nativeSpacing n
  (Ioo (s * (k 0 : ℝ) - 2 * s) (s * (k 0 : ℝ) + 2 * s) ×ˢ
    (Ioo (s * (k 1 : ℝ) - 2 * s) (s * (k 1 : ℝ) + 2 * s) ×ˢ
      Ioo (s * (k 2 : ℝ) - 2 * s) (s * (k 2 : ℝ) + 2 * s))) ∩
    PositiveRepresentatives.positiveTime

theorem openCell_open (n : ℕ) (k : SlotColoring.Grid) : IsOpen (openCell n k) :=
  (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)).inter PositiveRepresentatives.positiveTime_open

theorem openCell_convex (n : ℕ) (k : SlotColoring.Grid) : Convex ℝ (openCell n k) :=
  ((convex_Ioo _ _).prod ((convex_Ioo _ _).prod (convex_Ioo _ _))).inter
    PositiveRepresentatives.positiveTime_convex

theorem openCell_subset_box (n : ℕ) (k : SlotColoring.Grid) :
    openCell n k ⊆ PrimaryRepresentatives.gridBox n k 2 := by
  intro p hp j
  have hj : SquaredPartition.nativeSpacing n * (k j : ℝ) -
        2 * SquaredPartition.nativeSpacing n < PrimaryRepresentatives.position p j ∧
      PrimaryRepresentatives.position p j < SquaredPartition.nativeSpacing n * (k j : ℝ) +
        2 * SquaredPartition.nativeSpacing n := by
    fin_cases j
    · exact hp.1.1
    · exact hp.1.2.1
    · exact hp.1.2.2
  exact abs_le.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩

theorem openCell_subset_larger {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    openCell n k ⊆ PositiveRepresentatives.positiveCell n k :=
  fun _ hp => PositiveRepresentatives.enlarged_positive_subset_cell hn k
    ⟨openCell_subset_box n k hp, hp.2⟩

theorem support_subset_openCell {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    tsupport (PrimaryRepresentatives.nativeMask n k) ∩ PositiveRepresentatives.positiveTime ⊆
      openCell n k := by
  intro p hp
  have hs := SquaredPartition.nativeSpacing_pos hn
  have hb := PrimaryRepresentatives.nativeMask_tsupport_subset hn k hp.1
  have hc (j : Fin 3) : SquaredPartition.nativeSpacing n * (k j : ℝ) -
        2 * SquaredPartition.nativeSpacing n < PrimaryRepresentatives.position p j ∧
      PrimaryRepresentatives.position p j < SquaredPartition.nativeSpacing n * (k j : ℝ) +
        2 * SquaredPartition.nativeSpacing n := by
    have hj := abs_le.mp (hb j)
    constructor <;> linarith [hj.1, hj.2]
  exact ⟨⟨hc 0, hc 1, hc 2⟩, hp.2⟩

theorem representative_mem_openCell (K : Set Slow) (L : PositiveRepresentatives.ActiveLabel K) :
    PositiveRepresentatives.representative K L ∈ openCell L.val.1 L.val.2 :=
  support_subset_openCell L.property.1 L.val.2
    ⟨PositiveRepresentatives.representative_mem_tsupport K L,
      PositiveRepresentatives.representative_time_pos K L⟩

theorem openCell_representative_distance (K : Set Slow) (L : PositiveRepresentatives.ActiveLabel K)
    {p : Slow} (hp : p ∈ openCell L.val.1 L.val.2) :
    ‖p - PositiveRepresentatives.representative K L‖ ≤ 3 / ChartScales.S L.val.1 ^ 3 :=
  PositiveRepresentatives.representative_enlarged_distance K L (openCell_subset_box _ _ hp)

noncomputable def cellDomain (h lo hi : ℝ) (N : ℕ) :
    PhaseJetBounds.Domain (BaseChartJets.CellIndex h lo hi N) Slow where
  scale L := ChartScales.S (BaseChartJets.cellBand L)
  carrier L := openCell L.val.val.1 L.val.val.2
  isOpen _ := openCell_open _ _
  one_le_scale L := (BaseChartJets.positiveCellDomain h lo hi N).one_le_scale L

theorem cellDomain_subset_larger {h lo hi : ℝ} {N : ℕ} (L : BaseChartJets.CellIndex h lo hi N) :
    (cellDomain h lo hi N).carrier L ⊆ (BaseChartJets.positiveCellDomain h lo hi N).carrier L :=
  openCell_subset_larger L.val.property.1 L.val.val.2

theorem cellDomain_support {h lo hi : ℝ} {N : ℕ} (L : BaseChartJets.CellIndex h lo hi N) :
    tsupport (PrimaryRepresentatives.nativeMask L.val.val.1 L.val.val.2) ∩
      PositiveRepresentatives.positiveTime ⊆
      (cellDomain h lo hi N).carrier L :=
  support_subset_openCell L.val.property.1 L.val.val.2

theorem cellDomain_representative {h lo hi : ℝ} {N : ℕ} (L : BaseChartJets.CellIndex h lo hi N) :
    PositiveRepresentatives.representative (PrimaryRepresentatives.referenceCompact h lo hi) L.val ∈
      (cellDomain h lo hi N).carrier L :=
  representative_mem_openCell _ L.val

/-- Restrict labels after the constants have been chosen.  The actual
label and its chosen positive representative are unchanged. -/
noncomputable def earlierIndex {h lo hi : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (L : BaseChartJets.CellIndex h lo hi M) : BaseChartJets.CellIndex h lo hi N :=
  ⟨L.val, hNM.trans L.property⟩

@[simp] theorem earlierIndex_band {h lo hi : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (L : BaseChartJets.CellIndex h lo hi M) : BaseChartJets.cellBand (earlierIndex hNM L) =
      BaseChartJets.cellBand L := rfl

theorem polynomial_restrict_reindex {ι κ E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : PhaseJetBounds.Domain ι E} {D' : PhaseJetBounds.Domain κ E} {f : ι → E → V}
    (hf : PhaseJetBounds.PolynomialJets D f) (e : κ → ι)
    (hscale : ∀ i, D'.scale i = D.scale (e i))
    (hinside : ∀ i, D'.carrier i ⊆ D.carrier (e i)) :
    PhaseJetBounds.PolynomialJets D' (fun i => f (e i)) := by
  refine ⟨fun i => (hf.smooth (e i)).mono (hinside i), fun N => ?_⟩
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, fun i j hj p hp => ?_⟩
  rw [hscale]
  exact hm (e i) j hj p (hinside i hp)

/-! ## The fixed profile, schedule, and joint label family -/

section ActualFields

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def referenceSet : Set Slow :=
  PrimaryRepresentatives.referenceCompact F.data.h (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W)

abbrev Index (N : ℕ) :=
  BaseChartJets.CellIndex F.data.h (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W) N

instance indexCountable (N : ℕ) : Countable (Index W N) := by
  dsimp only [Index, BaseChartJets.CellIndex, PositiveRepresentatives.ActiveLabel,
    PrimaryRepresentatives.ActiveLabel]
  infer_instance

noncomputable def label {N : ℕ} (L : Index W N) : PartitionedCovariance.UnsignedLabel := L.val.val

theorem label_injective {N : ℕ} : Injective (label W (N := N)) :=
  fun _ _ he => Subtype.ext (Subtype.ext he)

noncomputable def domain (N : ℕ) : PhaseJetBounds.Domain (Index W N) Slow :=
  cellDomain F.data.h (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) N

noncomputable def representative {N : ℕ} (L : Index W N) : Slow :=
  PositiveRepresentatives.representative (referenceSet W) L.val

noncomputable def baseDomain {N : ℕ} (L : Index W N) : Set Slow :=
  PositiveRepresentatives.positiveCell L.val.val.1 L.val.val.2

theorem representative_positive {N : ℕ} (L : Index W N) :
    0 < (representative W L).2.2 :=
  PositiveRepresentatives.representative_time_pos _ L.val

theorem representative_in_reference {N : ℕ} (L : Index W N) :
    representative W L ∈ referenceSet W :=
  PositiveRepresentatives.representative_mem _ L.val

theorem representative_in_carrier {N : ℕ} (L : Index W N) :
    representative W L ∈ (domain W N).carrier L :=
  cellDomain_representative L

theorem representative_in_baseDomain {N : ℕ} (L : Index W N) :
    representative W L ∈ baseDomain W L :=
  PositiveRepresentatives.representative_mem_cell _ L.val

theorem carrier_in_baseDomain {N : ℕ} (L : Index W N) :
    (domain W N).carrier L ⊆ baseDomain W L := cellDomain_subset_larger L

theorem representative_distance {N : ℕ} (L : Index W N) {p : Slow}
    (hp : p ∈ (domain W N).carrier L) :
    ‖p - representative W L‖ ≤ 3 / (domain W N).scale L ^ 3 :=
  openCell_representative_distance _ L.val hp

theorem native_support_in_carrier {N : ℕ} (L : Index W N) :
    tsupport (PrimaryRepresentatives.nativeMask L.val.val.1 L.val.val.2) ∩
      PositiveRepresentatives.positiveTime ⊆ (domain W N).carrier L :=
  cellDomain_support L

theorem native_jet_support_in_carrier {N : ℕ} (L : Index W N) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (PrimaryRepresentatives.nativeMask L.val.val.1 L.val.val.2)) ∩
      PositiveRepresentatives.positiveTime ⊆ (domain W N).carrier L := by
  intro p hp
  exact native_support_in_carrier W L
    ⟨tsupport_iteratedFDeriv_subset (𝕜 := ℝ) m hp.1, hp.2⟩

/-- Every genuinely nonzero physical mask has one of the joint positive
labels used here. The implicit inverse is never evaluated at zero time. -/
theorem physicalMask_has_index {N : ℕ} (L : PartitionedCovariance.UnsignedLabel)
    (hL : 1 ≤ L.1) (hN : N ≤ L.1) {q : ℝ} {x : SlotColoring.Position}
    (hq : 0 < q) (hR : 0 ≤ x 0) (hT : 0 < x 2)
    (he : SimilarityCoordinates.forwardScalar (2 * F.data.h) (x 1) q = x 2)
    (hX : x 0 ^ 2 / (2 * q) ∈ Icc (NominalConeAssembly.activeLeft W)
      (NominalConeAssembly.activeRight W))
    (hm : PartitionedCovariance.mask (CoordinateAlgebra.D F.data.h) L q x ≠ 0) :
    ∃ i : Index W N, label W i = L := by
  obtain ⟨A, hA⟩ := PositiveRepresentatives.physicalMask_has_positive_representative
    L hL hq hR hT he hX hm
  refine ⟨⟨A, ?_⟩, hA⟩
  simpa only [hA] using hN

/-- Mean-flow charts use `(T,Z)`, while the phase chart uses `(R,(Z,T))`.
This explicit map prevents their equal product types hiding a swap. -/
noncomputable def fromTimeAxial (R : ℝ) (tz : ℝ × ℝ) : Slow := (R, (tz.2, tz.1))

@[simp] theorem fromTimeAxial_time (R : ℝ) (tz : ℝ × ℝ) :
    (fromTimeAxial R tz).2.2 = tz.1 := rfl

@[simp] theorem fromTimeAxial_axial (R : ℝ) (tz : ℝ × ℝ) :
    (fromTimeAxial R tz).2.1 = tz.2 := rfl

variable {W} (H : NominalConeAssembly.Certificate W)
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The chart field of the very same `FinalSlowBase` schedule. -/
noncomputable def frequency (upper : ℝ) (B n : ℕ) : Slow → ℝ :=
  BaseChartJets.frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

noncomputable def axial (upper : ℝ) (B n : ℕ) : Slow → ℝ :=
  BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

noncomputable def leadingFrequency : Slow → ℝ :=
  BaseChartJets.leadingFrequency F.data.h W.axis.normalization (FinalSlowBase.coefficients H v)

noncomputable def leadingAxial : Slow → ℝ :=
  BaseChartJets.leadingAxial F.data.h (FinalSlowBase.coefficients H v)

noncomputable def shear : Slow → Plane :=
  PhaseEstimates.shearVector (leadingFrequency H v) (leadingAxial H v)

/-- This record is an output of the concrete construction below.  None of
its analytic bounds are assumptions of the exported constructor. -/
structure Prepared (upper : ℝ) (B : ℕ) (r0 : ℝ) (N0 : ℕ) where
  N : ℕ
  threshold : N0 ≤ N
  M : ℝ
  u : ℝ
  eta : ℝ
  target : Slow → Plane
  one_le_M : 1 ≤ M
  u_pos : 0 < u
  eta_pos : 0 < eta
  u_le : u ≤ M
  length_bound : 1 / (2 * r0) ≤ M
  slot_bound : 4 * r0 * ChartScales.Tg ≤ M
  base : ∀ L : Index W N,
    PhaseEstimates.LocalBaseBounds
      (frequency H v upper B (BaseChartJets.cellBand L))
      (axial H v upper B (BaseChartJets.cellBand L))
      (leadingFrequency H v) (leadingAxial H v) (baseDomain W L) M
      (ChartScales.epsilon F.data.h (BaseChartJets.cellBand L))
  frequency_jets : PhaseJetBounds.PolynomialJets (domain W N)
    (fun L => frequency H v upper B (BaseChartJets.cellBand L))
  axial_jets : PhaseJetBounds.PolynomialJets (domain W N)
    (fun L => axial H v upper B (BaseChartJets.cellBand L))
  radius_pos : ∀ (L : Index W N) (p : Slow), p ∈ (domain W N).carrier L → 0 < p.1
  radius : ∀ (L : Index W N) (p : Slow), p ∈ (domain W N).carrier L →
    1 / M ≤ |p.1| ∧ |p.1| ≤ M
  parameters : ∀ L : Index W N,
    PrimaryRepresentatives.ParameterBounds M (representative W L).1
      (leadingFrequency H v (representative W L)) (shear H v (representative W L))
  cone : ∀ L : Index W N,
    PrimaryRepresentatives.ReferenceCone (leadingFrequency H v (representative W L))
      (shear H v (representative W L))
  target_continuous : ContinuousOn target (referenceSet W)
  target_unit : ∀ p ∈ referenceSet W, ‖target p‖ = 1
  target_actual : ∀ p ∈ referenceSet W,
    (PositiveRepresentatives.stableInner F.data.h p).1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
    target p = PrimaryRepresentatives.normalDirection
      (ProfileSpectralCone.stressVector v.profiles F.data.h
        (PositiveRepresentatives.stableInner F.data.h p))
  target_margin : ∀ (L : Index W N) (p : Slow),
    p ∈ PositiveRepresentatives.positivePart (referenceSet W) →
    p ∈ (domain W N).carrier L →
      ⟪target p, PrimaryRepresentatives.normalDirection (shear H v (representative W L))⟫_ℝ ≤ -eta ∧
      |PrimaryRepresentatives.c0 (leadingFrequency H v (representative W L))
          (shear H v (representative W L)) *
        ⟪target p, PrimaryRepresentatives.transverseDirection (shear H v (representative W L))⟫_ℝ /
        ⟪target p, PrimaryRepresentatives.normalDirection (shear H v (representative W L))⟫_ℝ| +
          eta ≤
        PrimaryRepresentatives.slopeRatio u
  large : ∀ n, N ≤ n → BasePhaseGeometry.LargeBand F.data.h M u n

noncomputable def phaseSign (c : Fin 2) : ℝ := if c = 0 then 1 else -1

theorem phaseSign_abs (c : Fin 2) : |phaseSign c| = 1 := by
  fin_cases c <;> norm_num [phaseSign]

/-- The actual positive representatives instantiate every entry of the
phase data, including the unstable eigenpair and the nonzero rounding. -/
noncomputable def family {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (c : Fin 2) :
    BasePhaseGeometry.FamilyData (domain W a.N) F.data.h r0 a.u a.M := by
  have hlow (L : Index W a.N) := (a.parameters L).positive_lower a.one_le_M
    (a.radius_pos L _ (representative_in_carrier W L)) (a.cone L)
  refine {
    band := BaseChartJets.cellBand
    scale_eq := fun _ => rfl
    F := fun L => frequency H v upper B (BaseChartJets.cellBand L)
    G := fun L => axial H v upper B (BaseChartJets.cellBand L)
    F0 := fun _ => leadingFrequency H v
    G0 := fun _ => leadingAxial H v
    U := baseDomain W
    q0 := representative W
    K := fun L => PrimaryRepresentatives.transverseDirection (shear H v (representative W L))
    lam := fun L => PrimaryRepresentatives.lambda0 (leadingFrequency H v (representative W L))
      (shear H v (representative W L))
    c0 := fun L => PrimaryRepresentatives.c0 (leadingFrequency H v (representative W L))
      (shear H v (representative W L))
    sigma := fun _ => phaseSign c
    theta := fun _ => 0
    base := a.base
    baseF := a.frequency_jets
    baseG := a.axial_jets
    inside := carrier_in_baseDomain W
    representative_inside := representative_in_baseDomain W
    distance := fun L _ hp => representative_distance W L hp
    radius := a.radius
    representative_radius := fun L => a.radius L _ (representative_in_carrier W L)
    unit := fun L => PrimaryRepresentatives.transverseDirection_unit (a.cone L).shear_ne_zero
    orthogonal := fun L => PrimaryRepresentatives.transverseDirection_inner_shear _
    frequency_bound := fun L => (a.parameters L).frequency
    shear_bound := fun L => (a.parameters L).shear
    shear_inv := fun L => by
      simp only [one_div]
      exact (hlow L).2.1
    lambda_bound := fun L => ⟨by simpa only [one_div] using (hlow L).2.2.1,
      (a.parameters L).lambda⟩
    ratio_bound := fun L => ⟨by simpa only [one_div] using (hlow L).2.2.2,
      (a.parameters L).ratio⟩
    eigen12 := ?_
    eigen21 := ?_
    sign := fun _ => phaseSign_abs c }
  · intro L
    simpa only [PrimaryRepresentatives.quarterTurn_transverseDirection] using (a.cone
      L).lambda0_div_c0
  · intro L
    have he := (a.cone L).lambda0_mul_c0
    rw [← BasePhaseGeometry.Representatives.normal_inner_shear (a.cone L).shear_ne_zero] at he
    simp only [PrimaryRepresentatives.quarterTurn_transverseDirection] at he ⊢
    exact he

/-- Both signs have one joint domain and the same constants, which were
fixed before its band threshold. All phase comparison outputs are proved
by `FamilyData.construction`. -/
noncomputable def construction {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (hr0 : 0 < r0) (c : Fin 2) :
    PrimaryPulseBounds.PhaseConstruction (domain W a.N) :=
  (family H v a c).construction F.data.h_pos.le hr0 a.one_le_M a.u_pos a.u_le
    a.length_bound a.slot_bound (fun L => a.large _ L.property)

/-- Every fixed chart, radial, and slot constant is enlarged before any
phase band is selected. -/
theorem exists_majorant (M0 b u r0 lo hi : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ M0 ≤ M ∧ b ≤ M ∧ u ≤ M ∧ 1 / (2 * r0) ≤ M ∧
      4 * r0 * ChartScales.Tg ≤ M ∧ PositiveRepresentatives.cellBound hi ≤ M ∧
      2 / Real.sqrt lo ≤ M := by
  refine ⟨max 1 (max M0 (max b (max u (max (1 / (2 * r0))
    (max (4 * r0 * ChartScales.Tg) (max (PositiveRepresentatives.cellBound hi)
      (2 / Real.sqrt lo))))))), ?_⟩
  simp only [le_max_iff, le_refl, true_or, or_true, and_self]

theorem active_order : NominalConeAssembly.activeLeft W < NominalConeAssembly.activeRight W := by
  have he := Real.exp_lt_exp.mpr (LeadingStressWeights.edges_ordered W)
  simpa only [LeadingStressWeights.leftEdge, LeadingStressWeights.rightEdge,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W),
    Real.exp_log (LeadingStressWeights.activeRight_pos W)] using he

theorem radius_lower_of_majorant {lo M : ℝ} (hlo : 0 < lo) (hM : 1 ≤ M)
    (hbound : 2 / Real.sqrt lo ≤ M) : 1 / M ≤ Real.sqrt lo / 2 := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hs : 0 < Real.sqrt lo := Real.sqrt_pos.mpr hlo
  have hb := (div_le_iff₀ hs).mp hbound
  apply (div_le_iff₀ hM0).mpr
  nlinarith

/-- The smooth summed base, its positive mask representatives, and the
actual strict cone supply every datum used by the phase theorem.  The
last threshold is chosen only after `u`, the target margin, and `M`.
The same threshold applies to every active label and to both signs. -/
theorem exists_prepared (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (r0 : ℝ)
    (hbox : 2 * NominalConeAssembly.activeRight W ≤ FinalSlowBase.boxRadius W upper)
    (N0 : ℕ) : Nonempty (Prepared H v upper B r0 N0) := by
  obtain ⟨T, M0, u, eta, hM0, hu, heta, hTc, hTn, hTa, hparam, Nt, hNt⟩ :=
    AlignedProfileSpectralCone.modulated_representative_bounds v H hcone
  have hlo := NominalConeAssembly.activeLeft_pos W
  have hhi := (active_order (W := W)).le
  obtain ⟨Nr, hNr⟩ := PositiveRepresentatives.exists_positive_reference_charts
    F.data.h_pos F.data.h_lt_half hlo hhi
  have ha := FinalSlowBase.scales_admissible_on H v upper B (half_pos hlo).le hbox
  obtain ⟨Nb, hNb, hest, C, hC, hbase⟩ := BaseChartJets.exists_actual_positive_charts
    F.data.h_pos F.data.h_lt_half hlo hhi (FinalSlowBase.coefficients_smooth H v) ha (max N0 Nr)
  obtain ⟨M, hM, hM0M, hCM, huM, hLM, hslotM, hcellM, hradM⟩ :=
    exists_majorant M0 C u r0 (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
  obtain ⟨N, hN, hlarge⟩ := BasePhaseGeometry.exists_large_band F.data.h M u 0
    F.data.h_pos hM (max Nb Nt)
  have hNbN : Nb ≤ N := (le_max_left _ _).trans hN
  have hNtN : Nt ≤ N := (le_max_right _ _).trans hN
  have hNrN : Nr ≤ N := (le_max_right _ _).trans (hNb.trans hNbN)
  have hN0N : N0 ≤ N := (le_max_left _ _).trans (hNb.trans hNbN)
  have hc (L : Index W N) (p : Slow) (hp : p ∈ (domain W N).carrier L) :=
    (hNr L.val (hNrN.trans L.property)).2.2.2.2 p (carrier_in_baseDomain W L hp)
  refine ⟨{
    N := N
    threshold := hN0N
    M := M
    u := u
    eta := eta
    target := T
    one_le_M := hM
    u_pos := hu
    eta_pos := heta
    u_le := huM
    length_bound := hLM
    slot_bound := hslotM
    base := ?_
    frequency_jets := ?_
    axial_jets := ?_
    radius_pos := fun L p hp => (hc L p hp).1
    radius := ?_
    parameters := fun L => (hparam L.val).mono hM0M
    cone := ?_
    target_continuous := hTc
    target_unit := hTn
    target_actual := hTa
    target_margin := ?_
    large := fun n hn => (hlarge n hn).1 }⟩
  · intro L
    exact BasePhaseGeometry.localBase_mono (hbase (earlierIndex hNbN L)) hCM
  · exact polynomial_restrict_reindex hest.polynomial_fields.1 (earlierIndex hNbN)
      (fun _ => rfl) (fun L => cellDomain_subset_larger L)
  · exact polynomial_restrict_reindex hest.polynomial_fields.2 (earlierIndex hNbN)
      (fun _ => rfl) (fun L => cellDomain_subset_larger L)
  · intro L p hp
    refine ⟨?_, ?_⟩
    · rw [abs_of_pos (hc L p hp).1]
      exact (radius_lower_of_majorant hlo hM hradM).trans (hc L p hp).2.1
    · simpa only [Real.norm_eq_abs] using
        (norm_fst_le p).trans ((hc L p hp).2.2.1.trans hcellM)
  · intro L
    exact AlignedProfileSpectralCone.modulated_positive_reference_cone v H hcone
      ⟨representative_in_reference W L, representative_positive W L⟩
  · intro L p hp hcell
    exact hNt L.val (hNtN.trans L.property) p hp (openCell_subset_box _ _ hcell)

/-- A selected, fully constructed datum.  The caller supplies no local
base bound, eigenpair estimate, or phase comparison. -/
noncomputable def prepared (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (r0 : ℝ)
    (hbox : 2 * NominalConeAssembly.activeRight W ≤ FinalSlowBase.boxRadius W upper)
    (N0 : ℕ) : Prepared H v upper B r0 N0 :=
  Classical.choice (exists_prepared H v hcone upper B r0 hbox N0)

noncomputable def phases (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (hbox : 2 * NominalConeAssembly.activeRight W ≤ FinalSlowBase.boxRadius W upper)
    (N0 : ℕ) : Fin 2 → PrimaryPulseBounds.PhaseConstruction
      (domain W (prepared H v hcone upper B r0 hbox N0).N) :=
  construction H v (prepared H v hcone upper B r0 hbox N0) hr0

/-- A canonical box large enough for every enlarged chart of the active
annulus. This uses exactly `FinalSlowBase.scales H v (2*activeRight) B`. -/
noncomputable def canonicalPrepared (hcone : LeadingStressWeights.FullTrueCone v)
    (B : ℕ) (r0 : ℝ) (N0 : ℕ) :
    Prepared H v (2 * NominalConeAssembly.activeRight W) B r0 N0 :=
  prepared H v hcone (2 * NominalConeAssembly.activeRight W) B r0 (le_max_left _ _) N0

noncomputable def canonicalPhases (hcone : LeadingStressWeights.FullTrueCone v)
    (B : ℕ) (r0 : ℝ) (hr0 : 0 < r0) (N0 : ℕ) :
    Fin 2 → PrimaryPulseBounds.PhaseConstruction
      (domain W (canonicalPrepared H v hcone B r0 N0).N) :=
  construction H v (canonicalPrepared H v hcone B r0 N0) hr0

theorem prepared_threshold (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (r0 : ℝ)
    (hbox : 2 * NominalConeAssembly.activeRight W ≤ FinalSlowBase.boxRadius W upper)
    (N0 : ℕ) : N0 ≤ (prepared H v hcone upper B r0 hbox N0).N :=
  (prepared H v hcone upper B r0 hbox N0).threshold

section Bindings

variable {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : Prepared H v upper B r0 N0) (hr0 : 0 < r0)

theorem four_le_threshold : 4 ≤ a.N := (a.large a.N le_rfl).four_le

theorem construction_frequency (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).phase.F L = frequency H v upper B (BaseChartJets.cellBand L) := rfl

theorem construction_axial (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).phase.G L = axial H v upper B (BaseChartJets.cellBand L) := rfl

theorem construction_epsilon (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).phase.epsilon L =
      ChartScales.epsilon F.data.h (BaseChartJets.cellBand L) := rfl

theorem construction_viscosity (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).viscosity L =
      ChartScales.epsilon F.data.h (BaseChartJets.cellBand L) *
        (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ) ^ 2 := rfl

theorem construction_length (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).L L =
      ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) := rfl

theorem construction_slot (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).V L =
      Ioo (-ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L))
        (2 * ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L)) := rfl

theorem construction_lambda (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).lam L =
      PrimaryRepresentatives.lambda0 (leadingFrequency H v (representative W L))
        (shear H v (representative W L)) := rfl

theorem construction_ratio (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).c0 L =
      PrimaryRepresentatives.c0 (leadingFrequency H v (representative W L))
        (shear H v (representative W L)) := rfl

theorem construction_transverse (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).K L =
      PrimaryRepresentatives.transverseDirection (shear H v (representative W L)) := rfl

theorem construction_u (c : Fin 2) (L : Index W a.N) :
    (construction H v a hr0 c).u L = a.u := rfl

/-- The actual integer angular mode is retained; zero-floor rounding is
not replaced by an unproved assertion that a real frequency is integral. -/
noncomputable def angularMode (c : Fin 2) (L : Index W a.N) : ℤ :=
  (family H v a c).angularMode L

theorem angularMode_ne_zero (c : Fin 2) (L : Index W a.N) :
    angularMode H v a c L ≠ 0 := (family H v a c).angularMode_ne_zero L

theorem carrier_mul_phase_p (c : Fin 2) (L : Index W a.N) :
    (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ) *
        (construction H v a hr0 c).phase.p L = (angularMode H v a c L : ℝ) :=
  (family H v a c).carrier_mul_angular_frequency L

theorem angular_rounding_error (c : Fin 2) (L : Index W a.N) :
    |(construction H v a hr0 c).phase.p L - (family H v a c).target L| ≤
      1 / (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ) :=
  (family H v a c).angular_rounding_error L

theorem phase_signs (L : Index W a.N) :
    (family H v a 0).sigma L = 1 ∧ (family H v a 1).sigma L = -1 := by
  norm_num [family, phaseSign]

theorem common_bounds (c d : Fin 2) :
    (construction H v a hr0 c).r = (construction H v a hr0 d).r ∧
    (construction H v a hr0 c).b = (construction H v a hr0 d).b ∧
    (construction H v a hr0 c).M = (construction H v a hr0 d).M ∧
    (construction H v a hr0 c).C = (construction H v a hr0 d).C ∧
    (construction H v a hr0 c).E = (construction H v a hr0 d).E :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem carrier_time_positive {L : Index W a.N} {p : Slow}
    (hp : p ∈ (domain W a.N).carrier L) : 0 < p.2.2 := hp.2

theorem target_eq_normalized_stress {p : Slow} (hp : p ∈ referenceSet W)
    (hT : 0 < p.2.2)
    (hX : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    a.target p = PrimaryRepresentatives.normalDirection
      (ProfileSpectralCone.stressVector v.profiles F.data.h
        (BaseChartJets.normalizedCoordinates F.data.h p).2) := by
  have he := AlignedProfileSpectralCone.stableInner_eq_normalized W hT
  have hs := a.target_actual p hp (by simpa only [he] using hX)
  simpa only [he] using hs

theorem frequency_eq_physical {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) (n : ℕ) :
    frequency H v upper B n p = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p) 1 /
        p.1 := by
  exact BaseChartJets.frequency_eq_normalized_velocity
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT hR

theorem axial_eq_physical {p : Slow} (hT : 0 < p.2.2) (n : ℕ) :
    axial H v upper B n p = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p) 2
        := by
  exact BaseChartJets.axial_eq_normalized_velocity
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT

end Bindings

/-! ## A later common cutoff preserves the already selected geometry -/

namespace Prepared

variable {H v}

/-- Restriction changes only the set of admissible labels.  It does not
reselect a target direction, parameter constant, representative, or
Fourier mode.  A final consumer can therefore take the maximum of its
covariance cutoff and this geometry cutoff. -/
noncomputable def restrict {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (N : ℕ) (hN : a.N ≤ N) :
    Prepared H v upper B r0 N0 where
  N := N
  threshold := a.threshold.trans hN
  M := a.M
  u := a.u
  eta := a.eta
  target := a.target
  one_le_M := a.one_le_M
  u_pos := a.u_pos
  eta_pos := a.eta_pos
  u_le := a.u_le
  length_bound := a.length_bound
  slot_bound := a.slot_bound
  base L := a.base (earlierIndex hN L)
  frequency_jets := polynomial_restrict_reindex a.frequency_jets (earlierIndex hN)
    (fun _ => rfl) (fun _ => Subset.rfl)
  axial_jets := polynomial_restrict_reindex a.axial_jets (earlierIndex hN)
    (fun _ => rfl) (fun _ => Subset.rfl)
  radius_pos L := a.radius_pos (earlierIndex hN L)
  radius L := a.radius (earlierIndex hN L)
  parameters L := a.parameters (earlierIndex hN L)
  cone L := a.cone (earlierIndex hN L)
  target_continuous := a.target_continuous
  target_unit := a.target_unit
  target_actual := a.target_actual
  target_margin L := a.target_margin (earlierIndex hN L)
  large n hn := a.large n (hN.trans hn)

@[simp] theorem restrict_N {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (N : ℕ) (hN : a.N ≤ N) :
    (a.restrict N hN).N = N := rfl

@[simp] theorem restrict_parameters {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (N : ℕ) (hN : a.N ≤ N) :
    (a.restrict N hN).M = a.M ∧ (a.restrict N hN).u = a.u ∧
      (a.restrict N hN).eta = a.eta ∧ (a.restrict N hN).target = a.target :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem restrict_frame {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (hr0 : 0 < r0) (N : ℕ) (hN : a.N ≤ N)
    (c : Fin 2) (L : Index W N) :
    (construction H v (a.restrict N hN) hr0 c).frame L =
      (construction H v a hr0 c).frame (earlierIndex hN L) := rfl

theorem restrict_angularMode {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (N : ℕ) (hN : a.N ≤ N)
    (c : Fin 2) (L : Index W N) :
    angularMode H v (a.restrict N hN) c L = angularMode H v a c (earlierIndex hN L) := rfl

theorem restrict_phase_p {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0) (hr0 : 0 < r0) (N : ℕ) (hN : a.N ≤ N)
    (c : Fin 2) (L : Index W N) :
    (construction H v (a.restrict N hN) hr0 c).phase.p L =
      (construction H v a hr0 c).phase.p (earlierIndex hN L) := rfl

end Prepared

end ActualFields

end NavierStokes.PrimaryGeometryAssembly
