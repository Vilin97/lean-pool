/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Generation
public import Mathlib.Analysis.Convex.Combination


/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

@[expose] public section

noncomputable section PortComputability

open Filter Set Topology

section

namespace MarkovProcess.Semigroup

/-- A map preserves a set if it sends every member of the set back into it. -/
def PreservesSet {E F : Type*} (T : E → F) (C : Set E) (D : Set F) : Prop :=
  ∀ ⦃x⦄, x ∈ C → T x ∈ D

namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}

theorem id : PreservesSet (fun x : E ↦ x) C C :=
  fun _ hx ↦ hx

theorem comp {S : F → G} {T : E → F}
    (hS : PreservesSet S D K) (hT : PreservesSet T C D) :
    PreservesSet (S ∘ T) C K :=
  fun _ hx ↦ hS (hT hx)

/-- A closed set is preserved by the pointwise limit of preserving maps. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    [TopologicalSpace F] {T : ι → E → F} {S : E → F}
    (hD : IsClosed D) (hT : ∀ i, PreservesSet (T i) C D)
    (hlim : ∀ x, Tendsto (fun i ↦ T i x) l (nhds (S x))) :
    PreservesSet S C D := by
  intro x hx
  exact hD.mem_of_tendsto (hlim x) (Eventually.of_forall fun i ↦ hT i hx)

end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite subprobability barycenter of points in a convex set containing
zero belongs to the set. -/
theorem sum_mem_of_sum_le_one {C : Set E} (hC : Convex ℝ C) (hzero : 0 ∈ C)
    (s : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1)
    (hz : ∀ i ∈ s, z i ∈ C) :
    ∑ i ∈ s, w i • z i ∈ C := by
  classical
  let s' : Finset (Option ι) := insert none (s.image some)
  let w' : Option ι → ℝ
    | none => 1 - ∑ i ∈ s, w i
    | some i => w i
  let z' : Option ι → E
    | none => 0
    | some i => z i
  have hnone : none ∉ s.image some := by
    simp
  have hw' : ∀ i ∈ s', 0 ≤ w' i := by
    intro i hi
    rcases i with _ | i
    · exact sub_nonneg.mpr hsum
    · exact hw i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hz' : ∀ i ∈ s', z' i ∈ C := by
    intro i hi
    rcases i with _ | i
    · exact hzero
    · exact hz i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hsum' : ∑ i ∈ s', w' i = 1 := by
    simp [s', hnone, w']
  have hmem := hC.sum_mem hw' hsum' hz'
  simpa [s', hnone, z', w'] using hmem

/-- A convergent countable subprobability barycenter of points in a closed
convex set containing zero belongs to the set. -/
theorem tsum_mem_of_tsum_le_one {C : Set E} (hclosed : IsClosed C)
    (hC : Convex ℝ C) (hzero : 0 ∈ C) (w : ℕ → ℝ) (z : ℕ → E)
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) (htsum : ∑' n, w n ≤ 1)
    (hz : ∀ n, z n ∈ C) (hweighted : Summable fun n ↦ w n • z n) :
    ∑' n, w n • z n ∈ C := by
  apply hclosed.mem_of_tendsto hweighted.hasSum.tendsto_sum_nat
  exact Eventually.of_forall fun n ↦
    Convex.sum_mem_of_sum_le_one
      hC hzero (Finset.range n) w z
      (fun i _ ↦ hw i)
      ((hsum.sum_le_tsum (Finset.range n) (fun i _ ↦ hw i)).trans htsum)
      (fun i _ ↦ hz i)

end Convex

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Invariance under a normalized resolvent propagates to all of its finite
iterates.  These are the atoms in the Poisson representation of a bounded
Yosida exponential. -/
theorem preservesSet_scaledOperator_pow (R : ContractiveResolvent E)
    (C : Set E) (α : PositiveShift)
    (hQ : PreservesSet (R.scaledOperator α) C C) (n : ℕ) :
    PreservesSet ((R.scaledOperator α) ^ n) C C := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_apply_eq_self] using!
        (PreservesSet.id (C := C))
  | succ n ih =>
      intro x hx
      rw [pow_succ, mul_apply_eq_comp]
      exact ih (hQ hx)

section CompleteSpace

variable [CompleteSpace E]

/-- If every canonical bounded Yosida approximation preserves a closed set,
then the generated strong-limit semigroup preserves it as well.  This theorem
contains no semigroup-level preservation hypothesis: its input is the concrete
approximating family produced from the resolvent. -/
theorem preservesSet_generatedSemigroup_of_yosida
    (R : ContractiveResolvent E) (C : Set E) (hC : IsClosed C)
    (happrox : ∀ n t, PreservesSet
      (R.yosidaOperator (naturalShift n) t) C C) (t : NNReal) :
    PreservesSet (R.generatedSemigroup t) C C := by
  exact PreservesSet.of_tendsto hC (fun n ↦ happrox n t)
    (R.tendsto_yosidaOperator_naturalShift_apply t)

/-- A version exposing all positive shifts, convenient when the Poisson
invariance theorem has been proved uniformly in the shift. -/
theorem preservesSet_generatedSemigroup
    (R : ContractiveResolvent E) (C : Set E) (hC : IsClosed C)
    (happrox : ∀ α t, PreservesSet (R.yosidaOperator α t) C C)
    (t : NNReal) : PreservesSet (R.generatedSemigroup t) C C := by
  exact R.preservesSet_generatedSemigroup_of_yosida C hC
    (fun n s ↦ happrox (naturalShift n) s) t

end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup

end

end PortComputability
