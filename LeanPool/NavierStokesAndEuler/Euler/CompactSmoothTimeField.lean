/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.CompactSupportBoundedPath
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-! Jointly smooth spatially compact families define smooth time fields.
The compact support is common to the time slices, so compact joint continuity
upgrades to continuity in the uniform spatial norm at every derivative order. -/

@[expose] public section


noncomputable section

open Set Filter
open scoped ContDiff BoundedContinuousFunction Topology


namespace EulerCompactSmoothTimeField

variable {P E V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Taking a spatial derivative preserves joint smoothness on an arbitrary
parameter set. Only the spatial domain needs unique derivatives. -/
theorem contDiffOn_spatial_fderiv {s : Set P} {u : P × E → V}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × E => fderiv ℝ (fun x => u (z.1, x)) z.2)
      (s ×ˢ univ) := by
  intro z hz
  have ha : ContDiffOn ℝ ∞
      (fun w : (P × E) × E => u (w.1.1, w.2))
      ((s ×ˢ univ) ×ˢ univ) :=
    hu.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun w hw => ⟨hw.1.1, mem_univ _⟩)
  have hb := (ha (z, z.2) ⟨hz, mem_univ _⟩).fderivWithin
    (f := fun (w : P × E) (x : E) => u (w.1, x))
    contDiffWithinAt_snd uniqueDiffOn_univ (m := ∞) (by simp) hz
    (fun _ _ => mem_univ _)
  simpa only [fderivWithin_univ] using hb

/-- Every actual spatial jet is jointly smooth, including at the boundary of
the parameter set. -/
theorem contDiffOn_spatial_jet {s : Set P} {u : P × E → V}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞
      (fun z : P × E => iteratedFDeriv ℝ n (fun x => u (z.1, x)) z.2)
      (s ×ˢ univ) := by
  induction n with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.contDiff.contDiffOn.comp
        hu (mapsTo_univ _ _)
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E)
        V).symm.toContinuousLinearEquiv.contDiff.contDiffOn.comp
      (contDiffOn_spatial_fderiv ih) (mapsTo_univ _ _)

end EulerCompactSmoothTimeField

namespace SmoothTimeField

variable {K L E V : Type} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pulling back time by a continuous map preserves all uniform spatial jets. -/
def reparametrize (A : SmoothTimeField K E V) (r : C(L, K)) : SmoothTimeField L E V where
  field := A.field.comp r
  smooth t := A.smooth (r t)
  jet n := (A.jet n).comp r
  jet_eq n t x := A.jet_eq n (r t) x

@[simp] theorem reparametrize_apply (A : SmoothTimeField K E V) (r : C(L, K))
    (t : L) (x : E) : (A.reparametrize r).field t x = A.field (r t) x := rfl

@[simp] theorem reparametrize_jet_apply (A : SmoothTimeField K E V) (r : C(L, K))
    (n : ℕ) (t : L) (x : E) : (A.reparametrize r).jet n t x = A.jet n (r t) x := rfl

end SmoothTimeField

namespace SmoothTimeField

variable {A E V : Type} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instCompactSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instCompactSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instCompactSmoothTimeField3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instCompactSmoothTimeField4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

/-- Continuous spatial jets with one common compact support yield a bounded
smooth coefficient path. The support condition on derivatives is derived. -/
def ofCompactSupportJets (u : A × E → V) (hu : Continuous u)
    (hsmooth : ∀ t, ContDiff ℝ ∞ (fun x => u (t, x)))
    (hjet : ∀ n : ℕ, Continuous
      (fun z : A × E => iteratedFDeriv ℝ n (fun x => u (z.1, x)) z.2))
    (K : Set E) (hK : IsCompact K)
    (hsupp : ∀ t, tsupport (fun x => u (t, x)) ⊆ K) : SmoothTimeField A E V where
  field := EulerComparator.compactSupportBoundedPath u hu K hK hsupp
  smooth := hsmooth
  jet n := EulerComparator.compactSupportBoundedPath _ (hjet n) K hK
    (fun t => (tsupport_iteratedFDeriv_subset n).trans (hsupp t))
  jet_eq _ _ _ := rfl

@[simp] theorem ofCompactSupportJets_apply (u : A × E → V) (hu : Continuous u)
    (hsmooth : ∀ t, ContDiff ℝ ∞ (fun x => u (t, x)))
    (hjet : ∀ n : ℕ, Continuous
      (fun z : A × E => iteratedFDeriv ℝ n (fun x => u (z.1, x)) z.2))
    (K : Set E) (hK : IsCompact K)
    (hsupp : ∀ t, tsupport (fun x => u (t, x)) ⊆ K) (t : A) (x : E) :
    (ofCompactSupportJets u hu hsmooth hjet K hK hsupp).field t x = u (t, x) := rfl

end SmoothTimeField

namespace SmoothTimeField

variable {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A jointly smooth family on a compact parameter set with common compact
spatial support has all spatial jets continuous in the uniform norm. -/
def ofContDiffOnCompactSupport (s : Set P) [CompactSpace s]
    (u : P × E → V) (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ))
    (K : Set E) (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, tsupport (fun x => u (t, x)) ⊆ K) :
    SmoothTimeField s E V :=
  ofCompactSupportJets (fun z : s × E => u (z.1, z.2))
    (hu.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, mem_univ _⟩))
    (fun t => by
      change ContDiff ℝ ∞ (fun x : E => u ((t : P), x))
      apply contDiffOn_univ.mp
      exact hu.comp ((contDiffOn_const (c := (t : P))).prodMk contDiffOn_id)
        (fun _ _ => ⟨t.property, mem_univ _⟩))
    (fun n => (EulerCompactSmoothTimeField.contDiffOn_spatial_jet hu n).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, mem_univ _⟩))
    K hK (fun t => hsupp t t.property)

@[simp] theorem ofContDiffOnCompactSupport_apply (s : Set P) [CompactSpace s]
    (u : P × E → V) (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ))
    (K : Set E) (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, tsupport (fun x => u (t, x)) ⊆ K) (t : s) (x : E) :
    (ofContDiffOnCompactSupport s u hu K hK hsupp).field t x = u (t, x) := rfl

@[simp] theorem ofContDiffOnCompactSupport_jet_apply (s : Set P) [CompactSpace s]
    (u : P × E → V) (hu : ContDiffOn ℝ ∞ u (s ×ˢ univ))
    (K : Set E) (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, tsupport (fun x => u (t, x)) ⊆ K)
    (n : ℕ) (t : s) (x : E) :
    (ofContDiffOnCompactSupport s u hu K hK hsupp).jet n t x =
      iteratedFDeriv ℝ n (fun y => u (t, y)) x := rfl

end SmoothTimeField
