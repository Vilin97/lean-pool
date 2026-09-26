/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMinimizerFamily
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Definitions
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SmoothSliceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.RegIntegralAdapter

/-!
# Exact-source locality of canonical doubled-`Mu` solutions

The coarse source has deterministic AEE-slice coverage on every triadic cube.
The least-slice partition therefore assembles the canonical totalized
minimizer and its fixed-test energy pairing pointwise from source-local slice
pieces.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

noncomputable section

private theorem measurableSet_sourceLocal_aeeSlice {d : ℕ} (Q : TriadicCube d)
    (k : ℕ) :
    @MeasurableSet (Source.Coarse.Carrier d)
      (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q))
      {a : Source.Coarse.Carrier d |
        AEEQuantitativeEllipticSlice (cubeSet Q) k a.1} :=
  (measurableSet_smoothLocalSigmaR_aeeSlice Q k).preimage
    (Source.Coarse.measurable_coarseToRegular_smoothLocal
      (cubeSet Q) (measurableSet_cubeSet Q))

private theorem measurable_source_coarse_entryTest {d : ℕ} (Q : TriadicCube d)
    (i j : Fin d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ cubeSet Q) :
    @Measurable (Source.Coarse.Carrier d) ℝ
      (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _
      (fun a => entryTestR i j φ (Source.Coarse.coarseToRegular a)) := by
  have hentry_smooth :
      @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR (cubeSet Q)) _
        (entryTestR i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, φ, hφ_cont, hφ_compact, hφ_support, t, ht, rfl⟩
  exact hentry_smooth.comp
    (Source.Coarse.measurable_coarseToRegular_smoothLocal
      (cubeSet Q) (measurableSet_cubeSet Q))

/-- The selected canonical doubled-`Mu` Hilbert minimizer is measurable for the
exact coarse-source local sigma algebra.  The target carries the explicitly
specified Borel measurable space. -/
theorem measurable_sourceLocal_canonicalMuHilbertMinimizerCubeSet {d : ℕ}
    (Q : TriadicCube d) (P0 : BlockVec d) :
    @Measurable (Source.Coarse.Carrier d) (HilbertBlockL2 (cubeSet Q))
      (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q))
      (borel (HilbertBlockL2 (cubeSet Q)))
      (fun a : Source.Coarse.Carrier d =>
        canonicalMuHilbertMinimizerCubeSet Q P0 a.1) := by
  classical
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  let : MeasurableSpace (HilbertBlockL2 (cubeSet Q)) := borel _
  have : BorelSpace (HilbertBlockL2 (cubeSet Q)) := ⟨rfl⟩
  let slice : ℕ → Set (Source.Coarse.Carrier d) :=
    fun k => {a | AEEQuantitativeEllipticSlice (cubeSet Q) k a.1}
  let firstSlice : ℕ → Set (Source.Coarse.Carrier d) :=
    fun k => slice k ∩ ⋂ j ∈ Finset.range k, (slice j)ᶜ
  have hslice_meas : ∀ k : ℕ,
      @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) (slice k) := by
    intro k
    exact measurableSet_sourceLocal_aeeSlice Q k
  have hfirst_meas : ∀ k : ℕ,
      @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) (firstSlice k) := by
    intro k
    have hprev : @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q))
        (⋂ j ∈ Finset.range k, (slice j)ᶜ) :=
      (Finset.range k).measurableSet_biInter fun j _hj => (hslice_meas j).compl
    exact (hslice_meas k).inter hprev
  have hfirst_unique :
      ∀ {i j : ℕ} {a : Source.Coarse.Carrier d},
        a ∈ firstSlice i → a ∈ firstSlice j → i = j := by
    intro i j a hi hj
    by_cases hij : i = j
    · exact hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hnot : a ∉ slice i := by
        have hcompl : a ∈ (slice i)ᶜ := by
          simpa using
            (Set.mem_iInter.mp (Set.mem_iInter.mp hj.2 i) (by simpa using hlt))
        simpa using hcompl
      exact False.elim (hnot hi.1)
    · have hnot : a ∉ slice j := by
        have hcompl : a ∈ (slice j)ᶜ := by
          simpa using
            (Set.mem_iInter.mp (Set.mem_iInter.mp hi.2 j) (by simpa using hgt))
        simpa using hcompl
      exact False.elim (hnot hj.1)
  have hcover : ⋃ k : ℕ, firstSlice k = Set.univ := by
    ext a
    constructor
    · intro _ha
      exact Set.mem_univ a
    · intro _ha
      obtain ⟨k, hak⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
      have hcover_a : ∃ n : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) n a.1 := ⟨k, hak⟩
      let k0 : ℕ := Nat.find hcover_a
      have hak0 : a ∈ firstSlice k0 := by
        refine ⟨?_, ?_⟩
        · simpa [slice, k0] using Nat.find_spec hcover_a
        · refine Set.mem_iInter.mpr ?_
          intro j
          refine Set.mem_iInter.mpr ?_
          intro hj
          have hjlt : j < k0 := by simpa [k0] using hj
          have hnot : ¬ AEEQuantitativeEllipticSlice (cubeSet Q) j a.1 := by
            intro hja
            exact (not_lt_of_ge (Nat.find_min' hcover_a hja)) (by simpa [k0] using hjlt)
          simpa [slice] using hnot
      exact Set.mem_iUnion.mpr ⟨k0, hak0⟩
  let piece : (k : ℕ) → firstSlice k → HilbertBlockL2 (cubeSet Q) :=
    fun k a =>
      ((canonicalAEEMuOperatorSystemData Q k
        ⟨a.1.1, a.2.1⟩).toMuHilbertRealization).minimizerMap P0
  have hpiece_meas : ∀ k : ℕ, Measurable (piece k) := by
    intro k
    have hEntry :
        ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
          @Measurable (firstSlice k) ℝ _ _
            (fun x => entryTestR i j φ
              (Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))) := by
      intro i j φ hφ_cont hφ_compact hφ_support
      exact (measurable_source_coarse_entryTest Q i j hφ_cont hφ_compact hφ_support).comp
        measurable_subtype_coe
    have hsm :=
      stronglyMeasurable_canonicalMinimizer_carrier
        (mΩ := (inferInstance : MeasurableSpace (firstSlice k))) Q
        (A := fun x : firstSlice k =>
          Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))
        (fun x => x.2.1) hEntry P0
    exact hsm.measurable
  have hLift :
      @Measurable (Source.Coarse.Carrier d) (HilbertBlockL2 (cubeSet Q))
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _
        (Set.liftCover firstSlice piece (by
          intro i j a hai haj
          have hij := hfirst_unique hai haj
          subst j
          rfl) hcover) :=
    measurable_liftCover firstSlice hfirst_meas piece hpiece_meas (by
      intro i j a hai haj
      have hij := hfirst_unique hai haj
      subst j
      rfl) hcover
  have hEq :
      Set.liftCover firstSlice piece (by
        intro i j a hai haj
        have hij := hfirst_unique hai haj
        subst j
        rfl) hcover =
        fun a : Source.Coarse.Carrier d => canonicalMuHilbertMinimizerCubeSet Q P0 a.1 := by
    funext a
    obtain ⟨k, hak⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
    have hcover_a : ∃ n : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) n a.1 := ⟨k, hak⟩
    let k0 : ℕ := Nat.find hcover_a
    have hak0 : a ∈ firstSlice k0 := by
      refine ⟨?_, ?_⟩
      · simpa [slice, k0] using Nat.find_spec hcover_a
      · refine Set.mem_iInter.mpr ?_
        intro j
        refine Set.mem_iInter.mpr ?_
        intro hj
        have hjlt : j < k0 := by simpa [k0] using hj
        have hnot : ¬ AEEQuantitativeEllipticSlice (cubeSet Q) j a.1 := by
          intro hja
          exact (not_lt_of_ge (Nat.find_min' hcover_a hja)) (by simpa [k0] using hjlt)
        simpa [slice] using hnot
    rw [Set.liftCover_of_mem
      (S := firstSlice) (f := piece) (i := k0) hak0]
    simp only [piece, canonicalMuHilbertMinimizerCubeSet, hcover_a, k0]
    rfl
  rw [← hEq]
  exact hLift

/-- The canonical doubled-`Mu` Hilbert minimizer is a.e. strongly measurable
under every source law. -/
theorem aestronglyMeasurable_sourceLocal_canonicalMuHilbertMinimizerCubeSet
    {d : ℕ} {P : SourceCoeffLaw d} (Q : TriadicCube d) (P0 : BlockVec d) :
    AEStronglyMeasurable
      (fun a : Source.Coarse.Carrier d => canonicalMuHilbertMinimizerCubeSet Q P0 a.1) P := by
  classical
  let U : Set (Vec d) := cubeSet Q
  let : MeasurableSpace (HilbertBlockL2 U) := borel _
  have : BorelSpace (HilbertBlockL2 U) := ⟨rfl⟩
  let f : Source.Coarse.Carrier d → HilbertBlockL2 U :=
    fun a => canonicalMuHilbertMinimizerCubeSet Q P0 a.1
  have hLocalMeas :
      @Measurable (Source.Coarse.Carrier d) (HilbertBlockL2 U)
        (Source.Coarse.localSigma U (by simpa [U] using measurableSet_cubeSet Q))
        (borel (HilbertBlockL2 U)) f := by
    simpa [U, f] using measurable_sourceLocal_canonicalMuHilbertMinimizerCubeSet Q P0
  have hMeas :
      @Measurable (Source.Coarse.Carrier d) (HilbertBlockL2 U)
        (Source.Coarse.globalSigma d) (borel (HilbertBlockL2 U)) f := by
    apply Measurable.mono hLocalMeas
    · exact Source.Coarse.localSigma_mono
        (by simpa [U] using measurableSet_cubeSet Q) MeasurableSet.univ (Set.subset_univ U)
    · exact le_rfl
  have hNull : NullMeasurable f P := by
    intro s hs
    exact (hMeas hs).nullMeasurableSet
  let sliceRange : ℕ → Set (HilbertBlockL2 U) := fun k =>
    Set.range fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
      ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0
  let sepSet : Set (HilbertBlockL2 U) :=
    ({0} : Set (HilbertBlockL2 U)) ∪ ⋃ k : ℕ, sliceRange k
  have hSep : TopologicalSpace.IsSeparable sepSet := by
    have hSlices : TopologicalSpace.IsSeparable (⋃ k : ℕ, sliceRange k) := by
      refine .iUnion ?_
      intro k
      let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
        AEEQuantitativeEllipticSlice.localMeasurableSpace U k
      have hslice : StronglyMeasurable
          (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
            ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0) := by
        simpa [U] using
          Homogenization.stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
            (Q := Q) (k := k) P0
      simpa [sliceRange] using hslice.isSeparable_range
    exact (Set.finite_singleton (0 : HilbertBlockL2 U)).isSeparable.union hSlices
  have hMemSep : ∀ᵐ a ∂P, f a ∈ sepSet := by
    filter_upwards with a
    obtain ⟨k, hslice⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
    have ha : ∃ n : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) n a.1 := ⟨k, hslice⟩
    let k0 : ℕ := Nat.find ha
    have hslice0 : AEEQuantitativeEllipticSlice (cubeSet Q) k0 a.1 := Nat.find_spec ha
    right
    refine Set.mem_iUnion.mpr ⟨k0, ⟨⟨a.1, by simpa [U] using hslice0⟩, ?_⟩⟩
    simp only [f, canonicalMuHilbertMinimizerCubeSet, U, ha, k0]
    rfl
  exact (aestronglyMeasurable_iff_nullMeasurable_separable).2
    ⟨hNull, ⟨sepSet, hSep, hMemSep⟩⟩

/-- The fixed-test canonical energy pairing is local for the exact
coarse-source sigma algebra. -/
theorem isSourceLocalRandomVariable_canonicalMuHilbertEnergyBilinFixedCubeSet
    {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY a.1) := by
  classical
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  let slice : ℕ → Set (Source.Coarse.Carrier d) :=
    fun k => {a | AEEQuantitativeEllipticSlice (cubeSet Q) k a.1}
  let firstSlice : ℕ → Set (Source.Coarse.Carrier d) :=
    fun k => slice k ∩ ⋂ j ∈ Finset.range k, (slice j)ᶜ
  have hslice_meas : ∀ k : ℕ,
      @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) (slice k) := by
    intro k
    exact measurableSet_sourceLocal_aeeSlice Q k
  have hfirst_meas : ∀ k : ℕ,
      @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) (firstSlice k) := by
    intro k
    have hprev : @MeasurableSet (Source.Coarse.Carrier d)
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q))
        (⋂ j ∈ Finset.range k, (slice j)ᶜ) :=
      (Finset.range k).measurableSet_biInter fun j _hj => (hslice_meas j).compl
    exact (hslice_meas k).inter hprev
  have hfirst_unique :
      ∀ {i j : ℕ} {a : Source.Coarse.Carrier d},
        a ∈ firstSlice i → a ∈ firstSlice j → i = j := by
    intro i j a hi hj
    by_cases hij : i = j
    · exact hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hnot : a ∉ slice i := by
        have hcompl : a ∈ (slice i)ᶜ := by
          simpa using
            (Set.mem_iInter.mp (Set.mem_iInter.mp hj.2 i) (by simpa using hlt))
        simpa using hcompl
      exact False.elim (hnot hi.1)
    · have hnot : a ∉ slice j := by
        have hcompl : a ∈ (slice j)ᶜ := by
          simpa using
            (Set.mem_iInter.mp (Set.mem_iInter.mp hi.2 j) (by simpa using hgt))
        simpa using hcompl
      exact False.elim (hnot hj.1)
  have hcover : ⋃ k : ℕ, firstSlice k = Set.univ := by
    ext a
    constructor
    · intro _ha
      exact Set.mem_univ a
    · intro _ha
      obtain ⟨k, hak⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
      have hcover_a : ∃ n : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) n a.1 := ⟨k, hak⟩
      let k0 : ℕ := Nat.find hcover_a
      have hak0 : a ∈ firstSlice k0 := by
        refine ⟨?_, ?_⟩
        · simpa [slice, k0] using Nat.find_spec hcover_a
        · refine Set.mem_iInter.mpr ?_
          intro j
          refine Set.mem_iInter.mpr ?_
          intro hj
          have hjlt : j < k0 := by simpa [k0] using hj
          have hnot : ¬ AEEQuantitativeEllipticSlice (cubeSet Q) j a.1 := by
            intro hja
            exact (not_lt_of_ge (Nat.find_min' hcover_a hja)) (by simpa [k0] using hjlt)
          simpa [slice] using hnot
      exact Set.mem_iUnion.mpr ⟨k0, hak0⟩
  let piece : (k : ℕ) → firstSlice k → ℝ :=
    fun k a =>
      ((canonicalAEEMuOperatorSystemData Q k
        ⟨a.1.1, a.2.1⟩).toMuHilbertRealization).energyBilin
        (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
        (((canonicalAEEMuOperatorSystemData Q k
          ⟨a.1.1, a.2.1⟩).toMuHilbertRealization).minimizerMap P0)
  have hpiece_meas : ∀ k : ℕ, Measurable (piece k) := by
    intro k
    have hEntry :
        ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
          @Measurable (firstSlice k) ℝ _ _
            (fun x => entryTestR i j φ
              (Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))) := by
      intro i j φ hφ_cont hφ_compact hφ_support
      exact (measurable_source_coarse_entryTest Q i j hφ_cont hφ_compact hφ_support).comp
        measurable_subtype_coe
    exact
      measurable_energyBilin_fixed_canonicalMinimizer_carrier
        (mΩ := (inferInstance : MeasurableSpace (firstSlice k))) Q
        (A := fun x : firstSlice k =>
          Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))
        (fun x => x.2.1) hEntry P0 Y hY
  have hLift :
      @Measurable (Source.Coarse.Carrier d) ℝ
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _
        (Set.liftCover firstSlice piece (by
          intro i j a hai haj
          have hij := hfirst_unique hai haj
          subst j
          rfl) hcover) :=
    measurable_liftCover firstSlice hfirst_meas piece hpiece_meas (by
      intro i j a hai haj
      have hij := hfirst_unique hai haj
      subst j
      rfl) hcover
  have hEq :
      Set.liftCover firstSlice piece (by
        intro i j a hai haj
        have hij := hfirst_unique hai haj
        subst j
        rfl) hcover =
        fun a : Source.Coarse.Carrier d =>
          canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY a.1 := by
    funext a
    obtain ⟨k, hak⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
    have hcover_a : ∃ n : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) n a.1 := ⟨k, hak⟩
    let k0 : ℕ := Nat.find hcover_a
    have hak0 : a ∈ firstSlice k0 := by
      refine ⟨?_, ?_⟩
      · simpa [slice, k0] using Nat.find_spec hcover_a
      · refine Set.mem_iInter.mpr ?_
        intro j
        refine Set.mem_iInter.mpr ?_
        intro hj
        have hjlt : j < k0 := by simpa [k0] using hj
        have hnot : ¬ AEEQuantitativeEllipticSlice (cubeSet Q) j a.1 := by
          intro hja
          exact (not_lt_of_ge (Nat.find_min' hcover_a hja)) (by simpa [k0] using hjlt)
        simpa [slice] using hnot
    rw [Set.liftCover_of_mem
      (S := firstSlice) (f := piece) (i := k0) hak0]
    simp [canonicalMuHilbertEnergyBilinFixedCubeSet, hcover_a, k0, piece]
  rw [← hEq]
  exact hLift

namespace SourceObservable
/-- The fixed-test canonical doubled-`Mu` energy pairing as an exact
source-local observable. -/
noncomputable def canonicalMuHilbertEnergyBilinFixed {d : ℕ}
    (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    SourceObservable d (cubeSet Q) ℝ where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY a.1
  isLocal :=
    isSourceLocalRandomVariable_canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY

@[simp]
theorem canonicalMuHilbertEnergyBilinFixed_apply {d : ℕ}
    (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval)
    (a : Source.Coarse.Carrier d) :
    canonicalMuHilbertEnergyBilinFixed Q P0 Y hY a =
      canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY a.1 :=
  rfl

end SourceObservable

end

end Homogenization.Book.Ch04
