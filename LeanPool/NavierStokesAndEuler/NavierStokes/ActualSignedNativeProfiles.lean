/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior

/-!
# The actual signed carrier profiles on their Prepared regions

The family keeps each label's genuine Prepared phase domain.  The closed
one-mesh mask support lies strictly inside the open two-mesh domain at
positive time.  This proves the physical closure-coverage condition without
extending the profile functions across a native domain boundary.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedNativeProfiles

open Set Function Filter WeightedClasses PhaseJetBounds
open CorrectionInitialization PhysicalWaveSum
open scoped ContDiff Topology


/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label
/-- Native label: an abbreviation for `ActualSignedPhysicalData.NativeLabel
(ActualSignedExterior.labels B N0)`. -/
abbrev NativeLabel (B N0 : ℕ) :=
  ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.labels B N0)
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency
/-- Lift point: an abbreviation for `PhysicalGraphBounds.LiftPoint`. -/
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint

variable {B N0 : ℕ}

/-- No Prepared data is chosen for omitted physical labels. -/
noncomputable def region (B N0 : ℕ) (L : BandLabel) : Set Slow := by
  classical
  exact if hL : L ∈ ActualSignedExterior.labels B N0 then
    (ActualSignedPhysicalBinding.domain
      (ActualSignedExterior.actualLabel ⟨L.val,L.property,hL⟩)).carrier 0
  else ∅

theorem region_open (B N0 : ℕ) (L : BandLabel) : IsOpen (region B N0 L) := by
  classical
  unfold region
  split_ifs
  · exact (ActualSignedPhysicalBinding.domain _).isOpen _
  · exact isOpen_empty

theorem region_active (L : NativeLabel B N0) :
    region B N0 L = (ActualSignedPhysicalBinding.domain
      (ActualSignedExterior.actualLabel L)).carrier 0 := by
  classical
  simp only [region, dite_eq_left L.mem]

/-- Profile pair as an element of `ℝ × ℝ`. -/
noncomputable def profilePair (B : ℕ) (n : ℕ) (p : Slow) : ℝ × ℝ :=
  (PrimaryGeometryAssembly.frequency ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n p,
    PrimaryGeometryAssembly.axial ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B n p)

/-- Profile domain, given by `PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => region
B N0 L) (fun _ L => region_open B N0 L)`. -/
noncomputable def profileDomain (B N0 : ℕ) : Domain (Frequency × BandLabel) Slow :=
  PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => region B N0 L)
    (fun _ L => region_open B N0 L)

/-- The constants come from the original joint Prepared family before
selecting a physical label or a lattice copy. -/
theorem profile_jets : PolynomialJets (profileDomain B N0)
    (fun I p => profilePair B I.2.val.1 p) := by
  classical
  have hfg := (ActualPrimary.choice B N0).prepared.frequency_jets.pair
    (ActualPrimary.choice B N0).prepared.axial_jets
  constructor
  · intro I
    by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
    · let L : NativeLabel B N0 := ⟨I.2.val,I.2.property,hI⟩
      have hb := ActualSignedExterior.actualLabel_reference L
      change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = I.2.val.1 at hb
      have hs := hfg.smooth (ActualSignedExterior.actualLabel L).1
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_left hI,
        ActualSignedPhysicalBinding.domain, ActualParticularStageControls.reindexDomain,
        profilePair, hb, L] using hs
    · intro p hp
      have hempty : p ∈ (∅ : Set Slow) := by
        simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI]
            using hp
      exact hempty.elim
  · intro N
    obtain ⟨C,hC,m,hm⟩ := hfg.bound N
    refine ⟨C,hC,m,?_⟩
    intro I j hj p hp
    by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
    · let L : NativeLabel B N0 := ⟨I.2.val,I.2.property,hI⟩
      have hb := ActualSignedExterior.actualLabel_reference L
      change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = I.2.val.1 at hb
      have hp' : p ∈ (PrimaryGeometryAssembly.domain ActualPrimary.nominal
          (ActualPrimary.choice B N0).prepared.N).carrier (ActualSignedExterior.actualLabel L).1 :=
              by
        simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_left hI,
          ActualSignedPhysicalBinding.domain, ActualParticularStageControls.reindexDomain, L] using
              hp
      have hbound := hm (ActualSignedExterior.actualLabel L).1 j hj p hp'
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, profilePair,
        PrimaryGeometryAssembly.domain, PrimaryGeometryAssembly.cellDomain, hb] using hbound
    · simp only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] at hp
      exact hp.elim

/-- Lifted slow, given by `(PolarCharts.radius (PhysicalGraphBounds.liftXY x),
PhysicalGraphBounds.liftZT x)`. -/
noncomputable def liftedSlow (x : LiftPoint) : Slow :=
  (PolarCharts.radius (PhysicalGraphBounds.liftXY x), PhysicalGraphBounds.liftZT x)

theorem liftedSlow_continuous : Continuous liftedSlow :=
  (PolarCharts.radius_continuous.comp PhysicalGraphBounds.liftXY.continuous).prodMk
    PhysicalGraphBounds.liftZT.continuous

theorem liftedSlow_physical (n : ℕ) (w : ProblemStatement.SpaceTime) :
    liftedSlow (PhysicalGraphBounds.physicalLift ActualPrimary.h n w) =
      ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w) :=
  ActualSignedExterior.physicalLift_slow n w

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

theorem singleton_profiles (L : NativeLabel B N0) (K : BandLabel) (k : Frequency) (p : Slow) :
    ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
        ((ActualSignedExterior.family s).singleton L) K k).F p,
      (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
        ((ActualSignedExterior.family s).singleton L) K k).G p) =
      if K = (L : BandLabel) then profilePair B K.val.1 p else 0 := by
  classical
  by_cases he : K = (L : BandLabel)
  · subst K
    have hm : (L : BandLabel) ∈ ((ActualSignedExterior.family s).singleton L).active :=
        Set.mem_singleton _
    simp only [ite_true, ActualSignedPhysicalData.extendedCarrier, dite_eq_left hm]
    have hb := ActualSignedExterior.actualLabel_reference L
    change BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1 = L.val.1 at hb
    change profilePair B (BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1) p =
      profilePair B L.val.1 p
    rw [hb]
  · have hm : K ∉ ((ActualSignedExterior.family s).singleton L).active := by
      change K ∉ {(L : BandLabel)}
      simpa only [Set.mem_singleton_iff] using he
    simp only [ite_eq_right he, ActualSignedPhysicalData.extendedCarrier, dite_eq_right hm,
      ActualSignedPhysicalData.carrier, Prod.zero_eq_mk]

/-- A single active branch uses the common joint constants; omitted
branches have identically zero carrier profiles. -/
theorem singleton_jets (L : NativeLabel B N0) :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).F p,
        (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).G p)) := by
  classical
  have he : (fun I p =>
      ((ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).F p,
        (ActualSignedPhysicalData.extendedCarrier (h := ActualPrimary.h)
          ((ActualSignedExterior.family s).singleton L) I.2 I.1).G p)) =
      (fun (I : Frequency × BandLabel) p => if I.2 = (L : BandLabel) then profilePair B I.2.val.1 p
          else 0) := by
    funext I p
    exact singleton_profiles s L I.2 I.1 p
  rw [he]
  constructor
  · intro I
    by_cases hI : I.2 = (L : BandLabel)
    · simpa only [hI, ite_true] using (profile_jets (B := B) (N0 := N0)).smooth I
    · simpa only [ite_eq_right hI] using (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : Slow => (0 : ℝ × ℝ)) ((profileDomain B N0).carrier I))
  · intro N
    obtain ⟨C,hC,m,hm⟩ := (profile_jets (B := B) (N0 := N0)).bound N
    refine ⟨C,hC,m,?_⟩
    intro I j hj p hp
    by_cases hI : I.2 = (L : BandLabel)
    · simpa only [ite_eq_left hI] using hm I j hj p hp
    · simp only [ite_eq_right hI, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans ((profileDomain B N0).one_le_scale I)) m)

theorem core_empty (L : NativeLabel B N0) {K : BandLabel} (hne : K ≠ (L : BandLabel)) :
    ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L) K = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hK,_,_⟩
  exact hne (Set.mem_singleton_iff.mp hK)

theorem core_in_mask_support (L : NativeLabel B N0) :
    ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L) L ⊆
      liftedSlow ⁻¹' tsupport (PrimaryRepresentatives.nativeMask
        (BaseChartJets.cellBand (ActualSignedExterior.actualLabel L).1)
        (PrimaryGeometryAssembly.label ActualPrimary.nominal (ActualSignedExterior.actualLabel
            L).1).2) := by
  rintro x ⟨hL,hm,_⟩
  exact ActualPrimary.spatialMask_native_support (ActualSignedExterior.actualLabel L).1 (liftedSlow
      x) hm

theorem closure_covers (L : NativeLabel B N0) (K : BandLabel) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ preterminal)
    (hc : PhysicalGraphBounds.physicalLift ActualPrimary.h K.val.1 w ∈
      closure (ActualSignedPhysicalData.primitiveCore ((ActualSignedExterior.family s).singleton L)
          K)) :
    ActualSignedPhysicalData.nativeSlow (PhysicalMeanJetBounds.graph ActualPrimary.h K.val.1 0 w) ∈
      region B N0 K := by
  classical
  by_cases he : K = (L : BandLabel)
  · subst K
    rw [region_active L]
    have hclosure := closure_minimal (core_in_mask_support s L)
      ((isClosed_tsupport _).preimage liftedSlow_continuous)
    have hmask := hclosure hc
    rw [mem_preimage, liftedSlow_physical] at hmask
    exact PrimaryGeometryAssembly.native_support_in_carrier ActualPrimary.nominal
      (ActualSignedExterior.actualLabel L).1
      ⟨hmask, PhysicalMeanJetBounds.graph_time_pos ActualPrimary.h L.val.1 0 hw⟩
  · rw [core_empty s L he, closure_empty] at hc
    exact hc.elim

/-- The actual homogeneous singleton interface needed by the physical
factory, with no extension or output-bound assumptions. -/
noncomputable def nativeProfiles (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeProfiles (h := ActualPrimary.h)
      ((ActualSignedExterior.family s).singleton L) where
  region := region B N0
  region_open := region_open B N0
  jets := singleton_jets s L
  covers K w hw _ hc := closure_covers s L K w hw hc

/-- The actual assembled potential carrier retains the joint Prepared
bound, including the copy index and every physical label. -/
theorem potential_profiles_jets (i : Fin 3) :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((((ActualSignedExterior.family s).potentialCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le i).carrier I.1 I.2).F p,
        (((ActualSignedExterior.family s).potentialCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le i).carrier I.1 I.2).G p)) := by
  classical
  apply (profile_jets (B := B) (N0 := N0)).congr
  intro I p hp
  by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
  · have hactive : I.2 ∈ (ActualSignedExterior.family s).active := hI
    have he := singleton_profiles s ⟨I.2.val,I.2.property,hI⟩ I.2 I.1 p
    simp only [ite_true] at he
    simp only [DependentSignedPhysicalFamily.Family.potentialCopies,
      DependentSignedPhysicalFamily.Family.assembled, DependentSignedPhysicalFamily.diagonal,
      DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hactive,
      ActualSignedPhysicalData.potentialFamily]
    exact he.symm
  · have hempty : p ∈ (∅ : Set Slow) := by
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] using
          hp
    exact hempty.elim

theorem pressure_profiles_jets :
    PolynomialJets (profileDomain B N0) (fun I p =>
      ((((ActualSignedExterior.family s).pressureCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le).carrier I.1 I.2).F p,
        (((ActualSignedExterior.family s).pressureCopies ActualPrimary.slots
          ActualPrimary.outgoing.data.h_pos.le).carrier I.1 I.2).G p)) := by
  classical
  apply (profile_jets (B := B) (N0 := N0)).congr
  intro I p hp
  by_cases hI : I.2 ∈ ActualSignedExterior.labels B N0
  · have hactive : I.2 ∈ (ActualSignedExterior.family s).active := hI
    have he := singleton_profiles s ⟨I.2.val,I.2.property,hI⟩ I.2 I.1 p
    simp only [ite_true] at he
    simp only [DependentSignedPhysicalFamily.Family.pressureCopies,
      DependentSignedPhysicalFamily.Family.assembled, DependentSignedPhysicalFamily.diagonal,
      DependentSignedPhysicalFamily.Family.copyAt, dite_eq_left hactive,
      ActualSignedPhysicalData.pressureFamily]
    exact he.symm
  · have hempty : p ∈ (∅ : Set Slow) := by
      simpa only [profileDomain, PhysicalCopyBounds.copyBandDomain, region, dite_eq_right hI] using
          hp
    exact hempty.elim

end NavierStokes.ActualSignedNativeProfiles
