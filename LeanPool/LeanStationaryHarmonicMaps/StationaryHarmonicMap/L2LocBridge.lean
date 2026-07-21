/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.WeakStationarity

/-!
# Local `L²` bridge

This module isolates the measure-theoretic `L²_loc` input used by the Sobolev
bridge.  The map and gradient components are phrased using mathlib's `MemLp` on
compact restrictions.  For the gradient we also keep the global a.e.
measurability field explicitly: local compact `MemLp` data is enough for the
energy integrability part, while global a.e. measurability on an arbitrary
domain is a separate measurable-cover problem.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Local `L²` membership via mathlib's `MemLp`, tested on every compact subset
of the domain. -/
def LocallyMemLpTwoIn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Domain n → E) (Ω : Set (Domain n)) : Prop :=
  ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)

/-- Local `MemLp 2` implies local integrability of the squared norm. -/
theorem locallyMemLpTwoIn_to_locallyIntegrable_norm_sq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} {Ω : Set (Domain n)}
    (hf : LocallyMemLpTwoIn f Ω) :
    LocallyIntegrableScalarIn (fun x : Domain n => ‖f x‖ ^ 2) Ω := by
  intro K hK hKΩ
  have hmem : MemLp f 2 (volume.restrict K) := hf K hK hKΩ
  simpa [IntegrableOn] using hmem.integrable_norm_pow (p := 2) (by norm_num)

/-- Local `MemLp 2` for the map gives the custom map `L²_loc` field. -/
theorem mapLocallyL2In_of_locallyMemLpTwoIn
    {n m : ℕ} {u : Domain n → Target m} {Ω : Set (Domain n)}
    (hu : LocallyMemLpTwoIn u Ω) :
    MapLocallyL2In u Ω := by
  simpa [MapLocallyL2In] using
    locallyMemLpTwoIn_to_locallyIntegrable_norm_sq
      (n := n) (E := Target m) (f := u) (Ω := Ω) hu

/-- Local gradient `L²` membership via mathlib's `MemLp`, together with global
a.e. strong measurability on the domain. -/
structure GradientLocallyMemLpTwoIn {n m : ℕ}
    (Du : Domain n → Gradient n m) (Ω : Set (Domain n)) : Prop where
  aestronglyMeasurable : GradientAEStronglyMeasurableIn Du Ω
  memLpTwo_loc : LocallyMemLpTwoIn Du Ω

/-- Local `MemLp 2` for the gradient field gives integrability of the
Hilbert-Schmidt energy density on compact subsets. -/
theorem gradientLocallyL2In_of_gradientLocallyMemLpTwoIn
    {n m : ℕ} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (hDu : GradientLocallyMemLpTwoIn Du Ω) :
    GradientLocallyL2In Du Ω := by
  intro K hK hKΩ
  have hmem : MemLp Du 2 (volume.restrict K) := hDu.memLpTwo_loc K hK hKΩ
  unfold weakEnergyDensity gradientEnergy
  have hbase :
      ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) →
        Integrable (fun x : Domain n => ‖Du x i‖ ^ 2) (volume.restrict K) := by
    intro i hi
    have hiMem : MemLp (fun x : Domain n => Du x i) 2 (volume.restrict K) := by
      simpa [Function.comp_def] using
        (hmem.continuousLinearMap_comp
          (ContinuousLinearMap.proj (R := ℝ) i : Gradient n m →L[ℝ] Target m))
    simpa using hiMem.integrable_norm_pow (p := 2) (by norm_num)
  have hsum :
      Integrable
        (Finset.sum (Finset.univ : Finset (Fin n))
          (fun i : Fin n => fun x : Domain n => ‖Du x i‖ ^ 2))
        (volume.restrict K) :=
    Finset.sum_induction
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => fun x : Domain n => ‖Du x i‖ ^ 2)
      (p := fun g : Domain n → ℝ => Integrable g (volume.restrict K))
      (fun a b ha hb => ha.add hb)
      (integrable_zero (α := Domain n) (ε' := ℝ) (μ := volume.restrict K))
      hbase
  rw [IntegrableOn]
  convert hsum using 1
  ext x
  simp

/-- The a.e. measurability component of the gradient local `MemLp 2` package. -/
theorem GradientLocallyMemLpTwoIn.toGradientAEStronglyMeasurableIn
    {n m : ℕ} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (hDu : GradientLocallyMemLpTwoIn Du Ω) :
    GradientAEStronglyMeasurableIn Du Ω :=
  hDu.aestronglyMeasurable

/-- The local `L²` data needed before adding the weak-gradient relation. -/
structure LocalL2DataIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  map_memLpTwo_loc : LocallyMemLpTwoIn u Ω
  gradient_memLpTwo_loc : GradientLocallyMemLpTwoIn Du Ω

/-- Extract the custom map `L²_loc` field from local `MemLp 2` data. -/
theorem LocalL2DataIn.toMapLocallyL2In {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : LocalL2DataIn u Du Ω) :
    MapLocallyL2In u Ω :=
  mapLocallyL2In_of_locallyMemLpTwoIn h.map_memLpTwo_loc

/-- Extract the custom gradient a.e. measurability field from local gradient
`MemLp 2` data. -/
theorem LocalL2DataIn.toGradientAEStronglyMeasurableIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : LocalL2DataIn u Du Ω) :
    GradientAEStronglyMeasurableIn Du Ω :=
  h.gradient_memLpTwo_loc.toGradientAEStronglyMeasurableIn

/-- Extract the custom gradient `L²_loc` field from local gradient `MemLp 2`
data. -/
theorem LocalL2DataIn.toGradientLocallyL2In {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : LocalL2DataIn u Du Ω) :
    GradientLocallyL2In Du Ω :=
  gradientLocallyL2In_of_gradientLocallyMemLpTwoIn h.gradient_memLpTwo_loc

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
