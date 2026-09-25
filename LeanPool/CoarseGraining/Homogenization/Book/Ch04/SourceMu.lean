/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SmoothSliceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.RegIntegralAdapter

/-!
# Source-local coarse-grained energy

The exact coarse-source carrier has deterministic AEE-slice coverage on each
triadic cube.  On every slice, the coarse-to-regular integral realization lets
the carrier `Mu` engine consume the source's smooth integral observables.  A
countable `liftCover` then gives an exactly source-local, pointwise equal
version of `Mu`.
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

/-- The exact coarse-source energy on a triadic cube is source-local.  Its
proof uses only deterministic source-carrier slice coverage. -/
theorem isSourceLocalRandomVariable_Mu_cubeSet {d : ℕ}
    (Q : TriadicCube d) (P0 : BlockVec d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => Mu (cubeSet Q) P0 a.1) := by
  classical
  let slice : ℕ → Set (Source.Coarse.Carrier d) :=
    fun k => {a | AEEQuantitativeEllipticSlice (cubeSet Q) k a.1}
  let covered : Set (Source.Coarse.Carrier d) := ⋃ k : ℕ, slice k
  let cover : Option ℕ → Set (Source.Coarse.Carrier d)
    | none => coveredᶜ
    | some k => slice k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some _k, a => Mu (cubeSet Q) P0 (Source.Coarse.coarseToRegular a.1).toFun
  have hagree :
      ∀ (i j : Option ℕ) (a : Source.Coarse.Carrier d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
          f i ⟨a, hai⟩ = f j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k => exact absurd (Set.mem_iUnion.mpr ⟨k, haj⟩) hai
    | some k =>
        cases j with
        | none => exact absurd (Set.mem_iUnion.mpr ⟨k, hai⟩) haj
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    refine ⟨fun _ => Set.mem_univ a, fun _ => ?_⟩
    by_cases ha : a ∈ covered
    · rcases Set.mem_iUnion.mp ha with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hk⟩
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using ha⟩
  let Y : Source.Coarse.Carrier d → ℝ := Set.liftCover cover f hagree hcover
  have hY_local :
      @Measurable (Source.Coarse.Carrier d) ℝ
        (Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)) _ Y := by
    let : MeasurableSpace (Source.Coarse.Carrier d) :=
      Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
    have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
      intro i
      cases i with
      | none =>
          exact (MeasurableSet.iUnion fun k =>
            measurableSet_sourceLocal_aeeSlice Q k).compl
      | some k => exact measurableSet_sourceLocal_aeeSlice Q k
    have hfm : ∀ i : Option ℕ, Measurable (f i) := by
      intro i
      cases i with
      | none => exact measurable_const
      | some k =>
          have hEntry :
              ∀ (i' j' : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
                HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
                @Measurable (cover (some k)) ℝ _ _
                  (fun x => entryTestR i' j' φ
                    (Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))) := by
            intro i' j' φ hφ_cont hφ_compact hφ_support
            have hentry_smooth :
                @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR (cubeSet Q)) _
                  (entryTestR i' j' φ) := by
              intro t ht
              exact MeasurableSpace.measurableSet_generateFrom
                ⟨i', j', φ, hφ_cont, hφ_compact, hφ_support, t, ht, rfl⟩
            exact hentry_smooth.comp
              ((Source.Coarse.measurable_coarseToRegular_smoothLocal
                (cubeSet Q) (measurableSet_cubeSet Q)).comp measurable_subtype_coe)
          simpa [f] using
            measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q
              (A := fun x : cover (some k) =>
                Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))
              (fun x => x.2) hEntry P0
    exact measurable_liftCover cover hcover_meas f hfm hagree hcover
  have hY_eq : (fun a : Source.Coarse.Carrier d => Mu (cubeSet Q) P0 a.1) = Y := by
    funext a
    obtain ⟨k, hak⟩ := exists_source_aeeQuantitativeEllipticSlice_cubeSet a Q
    have ha_cover : a ∈ cover (some k) := hak
    change Mu (cubeSet Q) P0 a.1 = Set.liftCover cover f hagree hcover a
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k) ha_cover]
    rfl
  rw [hY_eq]
  exact hY_local

namespace SourceObservable

/-- The coarse-grained energy on a triadic cube, bundled as an exact
source-local observable. -/
noncomputable def mu {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d) :
    SourceObservable d (cubeSet Q) ℝ where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => Mu (cubeSet Q) P0 a.1
  isLocal := isSourceLocalRandomVariable_Mu_cubeSet Q P0

@[simp]
theorem mu_apply {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d)
    (a : Source.Coarse.Carrier d) :
    mu Q P0 a = Mu (cubeSet Q) P0 a.1 :=
  rfl

end SourceObservable

end

end Homogenization.Book.Ch04
