/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.BoundedPathFamily

@[expose] public section

/-! Constructing literal bounded smooth coefficient paths from an actual
smooth path family and uniform bounds on its differentiated evolution. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace SmoothTimeField

open Set EulerSmoothPathTimeJets EulerBoundedPathFamily EulerVolterraConvolution

variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T,V))
  (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)
  (C D : ℕ → ℝ)
  (hC : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => f y t) x‖ ≤ C n)
  (hD : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => q y t) x‖ ≤ D n)

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hC in
private theorem value_bound (t : Icc (0 : ℝ) T) (x : E) : ‖f x t‖ ≤ C 0 := by
  simpa only [norm_iteratedFDeriv_zero] using hC 0 t x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hT hD in
private theorem derivativeBound_nonneg (n : ℕ) : 0 ≤ D n :=
  (norm_nonneg _).trans (hD n ⟨0,le_rfl,hT⟩ 0)

def ofPathFamily : SmoothTimeField (Icc (0 : ℝ) T) E V where
  field := boundedPath T hT f q hf.continuous (C 0) (D 0)
    (value_bound T f C hC) (derivativeBound_nonneg T hT q D hD 0)
    (value_bound T q D hD) hd
  smooth t := by
    change ContDiff ℝ ∞ (fun x => f x t)
    exact (ContinuousMap.evalCLM ℝ t).contDiff.comp hf
  jet n := boundedPath T hT (jetFamily T f n) (jetFamily T q n)
    (jetFamily_contDiff T f hf n).continuous (C n) (D n)
    (fun t x => by rw [jetFamily_apply T f hf]; exact hC n t x)
    (derivativeBound_nonneg T hT q D hD n)
    (fun t x => by rw [jetFamily_apply T q hq]; exact hD n t x)
    (jetFamily_hasDerivWithinAt T hT f q hf hq hd n)
  jet_eq n t x := jetFamily_apply T f hf n x t

@[simp] theorem ofPathFamily_apply (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).field t x = f x t := rfl

@[simp] theorem ofPathFamily_jet_apply (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).jet n t x =
      iteratedFDeriv ℝ n (fun y => f y t) x :=
  jetFamily_apply T f hf n x t

theorem ofPathFamily_jet_norm (n : ℕ) :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).jet n‖ ≤ C n := by
  have hnonneg : 0 ≤ C n := (norm_nonneg _).trans (hC n ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  rw [ofPathFamily_jet_apply]
  exact hC n t x

theorem ofPathFamily_field_norm :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).field‖ ≤ C 0 := by
  have hnonneg : 0 ≤ C 0 := (norm_nonneg _).trans (hC 0 ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  exact value_bound T f C hC t x

end SmoothTimeField
