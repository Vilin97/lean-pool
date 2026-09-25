/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.MuLocalityGate
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily

/-! # Mu -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# `Mu` measurability (carrier re-aim, Packet P5 centrepiece)

This file is the public Ch4 handoff for the coarse-grained energy `Mu` on the
honest carrier.  Following the carrier redesign, a law `P : RestrictionCoeffLaw d` is a
measure on `RegCoeffField d`, and the observable is `a ↦ Mu (cubeSet Q) P0 a.toFun`.

The measurability is genuinely established, not merely null-covered.  The
carrier `Mu`-slice engine `measurable_Mu_comp_aeeSlice_of_measurable_entryTest`
(`Internal/AEESliceAssembly/CarrierMuFamily.lean`) makes `Mu ∘ toFun`
**genuinely `LocalSigmaR (cubeSet Q)`-measurable on each AEE quantitative slice**,
using only the honest entry-test generators of the carrier (no fine pointwise
data).  The AEE slice events are genuinely `LocalSigmaR`-measurable (P4b), so the
countable slice cover assembles by a **genuine `liftCover`** — no null
bookkeeping — into a `LocalSigmaR`-measurable representative `Y`, which the gate
`IsRestrictionLocalRandomVariable.of_measurable_localSigmaR` promotes to a genuine
restriction-local random variable.

Note (statement check, Packet P5): `Mu ∘ toFun` is **not** `LocalSigmaR`-measurable
on all of the carrier — off the a.e.-elliptic locus the carrier admits fields on
which `Mu` is uninformative — so `exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet`
is *not* trivialised: the a.e.-representative `Y` (equal to `Mu ∘ toFun` on the
a.s.-full elliptic locus) is genuinely needed.  The honest endpoint therefore
remains law-relative `AEMeasurable`, with the genuine local representative `Y`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace RestrictionLawCarrier

/-- **Law-relative local representative of `Mu` on a fixed triadic cube.**  The
carrier `Mu`-slice engine makes `Mu ∘ toFun` genuinely `LocalSigmaR (cubeSet Q)`-
measurable on each AEE quantitative slice; the slices are genuinely
`LocalSigmaR`-measurable and cover the law a.s., so a genuine `liftCover` produces
a `LocalSigmaR`-measurable `Y` agreeing with `Mu ∘ toFun` almost surely, promoted
to a restriction-local random variable by the gate. -/
theorem exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    ∃ Y : RegCoeffField d → ℝ,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => Mu (cubeSet Q) P0 a.toFun) =ᵐ[P] Y := by
  classical
  let slice : ℕ → Set (RegCoeffField d) :=
    fun k => {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
  let covered : Set (RegCoeffField d) := ⋃ k : ℕ, slice k
  let cover : Option ℕ → Set (RegCoeffField d)
    | none => coveredᶜ
    | some k => slice k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some _k, a => Mu (cubeSet Q) P0 a.1.toFun
  have hagree :
      ∀ (i j : Option ℕ) (a : RegCoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
          f i ⟨a, hai⟩ = f j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exact absurd (Set.mem_iUnion.mpr ⟨k, haj⟩) hai
    | some k =>
        cases j with
        | none =>
            exact absurd (Set.mem_iUnion.mpr ⟨k, hai⟩) haj
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    refine ⟨fun _ => Set.mem_univ a, fun _ => ?_⟩
    by_cases ha : a ∈ covered
    · rcases Set.mem_iUnion.mp ha with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hk⟩
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using ha⟩
  let Y : RegCoeffField d → ℝ := Set.liftCover cover f hagree hcover
  refine ⟨Y, ?_, ?_⟩
  · -- `Y` is `LocalSigmaR (cubeSet Q)`-measurable, hence restriction-local.
    have hY_localSigma :
        @Measurable (RegCoeffField d) ℝ (LocalSigmaR (cubeSet Q)) _ Y := by
      let : MeasurableSpace (RegCoeffField d) := LocalSigmaR (cubeSet Q)
      have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
        intro i
        cases i with
        | none =>
            exact (MeasurableSet.iUnion fun k =>
              measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k).compl
        | some k => exact measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k
      have hfm : ∀ i : Option ℕ, Measurable (f i) := by
        intro i
        cases i with
        | none => exact measurable_const
        | some k =>
            have hEntry :
                ∀ (i' j' : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
                  HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
                  @Measurable (cover (some k)) ℝ _ _
                    (fun x => entryTestR i' j' φ (x : RegCoeffField d)) := by
              intro i' j' φ hφ_cont hφ_compact hφ_support
              have hφ_probe : IsProbeR φ := IsProbeR.of_smooth hφ_cont hφ_compact
              have hφ_support' : Function.support φ ⊆ cubeSet Q :=
                (Function.support_subset_iff.2 fun x hx => subset_tsupport φ hx).trans hφ_support
              exact (measurable_entryTestR_localSigmaR i' j' hφ_probe hφ_support').comp
                measurable_subtype_coe
            simpa [f] using
              measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q
                (A := fun x : cover (some k) => (x : RegCoeffField d))
                (fun x => x.2) hEntry P0
      exact measurable_liftCover cover hcover_meas f hfm hagree hcover
    exact IsRestrictionLocalRandomVariable.of_measurable_localSigmaR (measurableSet_cubeSet Q) hY_localSigma
  · -- `Y` agrees with `Mu ∘ toFun` on the a.s.-full elliptic locus.
    have hcovered_ae : ∀ᵐ a ∂P, a ∈ covered := by
      filter_upwards
          [hP.ae_locally_uniformly_elliptic.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q]
        with a ha
      exact Set.mem_iUnion.mpr ha
    filter_upwards [hcovered_ae] with a ha
    rcases Set.mem_iUnion.mp ha with ⟨k, hak⟩
    have ha_cover : a ∈ cover (some k) := hak
    change Mu (cubeSet Q) P0 a.toFun = Set.liftCover cover f hagree hcover a
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k) ha_cover]

/-- The canonical Chapter 4 law-facing measurability theorem for `Mu` on a
deterministic triadic cube.  Downstream chapters should use this theorem
directly; `coarseBlockMatrix`, `ResponseJ`, and `BlockJ` measurability should
be derived from this finite-polarization root. -/
theorem aemeasurable_Mu_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEMeasurable (fun a : RegCoeffField d => Mu (cubeSet Q) P0 a.toFun) P := by
  obtain ⟨Y, hY_local, hY_eq⟩ := hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet Q P0
  have hY_restr :
      @Measurable (RegCoeffField d) ℝ
        (RestrictionSigmaR (cubeSet Q) (measurableSet_cubeSet Q)) _ Y := hY_local
  have hY_meas : Measurable Y :=
    hY_restr.mono (restrictionSigmaR_le (cubeSet Q) (measurableSet_cubeSet Q)) le_rfl
  exact hY_meas.aemeasurable.congr hY_eq.symm

end RestrictionLawCarrier

end Ch04
end Book
end Homogenization
