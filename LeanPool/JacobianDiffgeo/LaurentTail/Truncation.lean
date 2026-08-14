/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LaurentTail.TailSpace

/-!
# The truncation map `α_D` and `H¹Tail(D)` (laurent-tails, design §2 D3, §4.2)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

* `alphaFinset D f`: a `Finset` witness containing every point where `α_D f`'s tail component is
  possibly nonzero (`D.support` together with `f`'s pole set).
* `alpha`/`alphaL`: Miranda's truncation `α_D : ℳ X → T[D]`, `α_D f`'s class at `p` is the chart
  restriction of `f` mod `ordGe p (-(D p))` — **at every `p`**, not just on the witness Finset
  (`alpha_apply`, exported per `docs/requests/laurent-tails.md`'s serre-duality-tails ask).
* `ker_alphaL_eq_linSys`: Miranda's `L(D) = ker(α_D)` (PDF 192).
* `H1Tail D := T D ⧸ range(alphaL D)`: Miranda's own definition of `H¹(D)` (the comparison to
  `Cech.H1 D` is `Comparison.lean`'s job).
-/

open scoped ContDiff Manifold
open Set TopologicalSpace

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### `alphaFinset`, `alpha`, `alphaL` -/

open scoped Classical in
/-- A `Finset` witness for `α_D f`'s (possibly) nonzero locus: `D`'s own (finite, compactness)
support, together with `f`'s pole set (finite, compactness + connectedness) when `f ≠ 0`. -/
noncomputable def alphaFinset (D : RS.Divisor X) (f : RS.Mero X) : Finset X :=
  (D.finiteSupport isCompact_univ).toFinset ∪
    (if hf : f = 0 then (∅ : Finset X) else (RS.finite_setOf_ord_neg hf).toFinset)

/-- Every point outside the witness `Finset` is a genuine "good" point: `f`'s chart-restriction
class there already lies in `L(D)`'s local bound. -/
theorem not_mem_alphaFinset (D : RS.Divisor X) (f : RS.Mero X) {p : X} (hp : p ∉ alphaFinset D f) :
    (-(D p) : WithTop ℤ) ≤ f.ord p := by
  rw [alphaFinset, Finset.mem_union, not_or] at hp
  obtain ⟨hD, hf2⟩ := hp
  rw [Set.Finite.mem_toFinset] at hD
  have hDp : D p = 0 := Function.notMem_support.mp hD
  by_cases hf : f = 0
  · subst hf
    rw [RS.MeroGermOn.ord_zero, ite_eq_left ⟨isOpen_univ, Set.mem_univ p⟩]
    exact le_top
  · rw [dite_eq_right hf] at hf2
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at hf2
    rw [hDp]
    simpa using hf2

/-- Miranda's truncation `α_D`, assembled from the witness `Finset` (§2 D3). -/
noncomputable def alpha (D : RS.Divisor X) (f : RS.Mero X) : T D :=
  T.mk D (alphaFinset D f)
    (fun p => TailAt.mk (p : X) D (RS.MeroGermOn.restrict (Set.subset_univ _) f))

/-- `alpha D f`'s value at *every* point `p` (not just the witness Finset) is the chart
restriction of `f` mod `ordGe p (-(D p))` — requested by serre-duality-tails
(`docs/requests/laurent-tails.md`). -/
@[simp] theorem alpha_apply (D : RS.Divisor X) (f : RS.Mero X) (p : X) :
    alpha D f p = TailAt.mk p D (RS.MeroGermOn.restrict (Set.subset_univ _) f) := by
  unfold alpha
  by_cases hp : p ∈ alphaFinset D f
  · exact T.mk_apply_mem hp
  · rw [T.mk_apply_not_mem hp, eq_comm, TailAt.mk_eq_zero_iff,
      RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ p).open_source isOpen_univ
        (mem_chart_source ℂ p)]
    exact not_mem_alphaFinset D f hp

theorem alpha_apply_eq_zero_iff (D : RS.Divisor X) (f : RS.Mero X) (p : X) :
    alpha D f p = 0 ↔ (-(D p) : WithTop ℤ) ≤ f.ord p := by
  rw [alpha_apply, TailAt.mk_eq_zero_iff,
    RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ p).open_source isOpen_univ
      (mem_chart_source ℂ p)]

/-- `α_D : ℳ X →ₗ[ℂ] T D`, Miranda's truncation map. -/
noncomputable def alphaL (D : RS.Divisor X) : RS.Mero X →ₗ[ℂ] T D where
  toFun := alpha D
  map_add' f g := by
    apply DFinsupp.ext
    intro p
    rw [DFinsupp.add_apply, alpha_apply, alpha_apply, alpha_apply, map_add, map_add]
  map_smul' a f := by
    apply DFinsupp.ext
    intro p
    rw [DFinsupp.smul_apply, alpha_apply, alpha_apply, map_smul, map_smul]
    rfl

@[simp] theorem alphaL_apply (D : RS.Divisor X) (f : RS.Mero X) : alphaL D f = alpha D f := rfl

/-- Miranda PDF 192: `L(D) = ker(α_D)`. -/
theorem ker_alphaL_eq_linSys (D : RS.Divisor X) :
    LinearMap.ker (alphaL D) = RS.LinSys D := by
  ext f
  rw [LinearMap.mem_ker, RS.mem_linSys_iff]
  constructor
  · intro hf x
    have hx : alphaL D f x = (0 : T D) x := by rw [hf]
    rw [DFinsupp.zero_apply, alphaL_apply, alpha_apply_eq_zero_iff] at hx
    exact hx
  · intro hf
    apply DFinsupp.ext
    intro x
    rw [DFinsupp.zero_apply, alphaL_apply, alpha_apply_eq_zero_iff]
    exact hf x

/-! ### `H1Tail D` -/

/-- Miranda's `H¹(D) := T[D]/α_D(ℳ)` (PDF 192-193). The comparison to `Cech.H1 D`
(`RS.Cech.H1`) is `Comparison.lean`'s job. -/
noncomputable def H1Tail (D : RS.Divisor X) : Type _ := T D ⧸ LinearMap.range (alphaL D)

noncomputable instance instAddCommGroupH1Tail (D : RS.Divisor X) : AddCommGroup (H1Tail D) :=
  inferInstanceAs (AddCommGroup (T D ⧸ LinearMap.range (alphaL D)))

noncomputable instance instModuleH1Tail (D : RS.Divisor X) : Module ℂ (H1Tail D) :=
  inferInstanceAs (Module ℂ (T D ⧸ LinearMap.range (alphaL D)))

/-- The quotient map onto `H¹Tail(D)`. -/
noncomputable def H1Tail.mk (D : RS.Divisor X) : T D →ₗ[ℂ] H1Tail D := Submodule.mkQ _

theorem H1Tail.mk_surjective (D : RS.Divisor X) : Function.Surjective (H1Tail.mk D) :=
  Submodule.mkQ_surjective _

theorem H1Tail.mk_eq_zero_iff (D : RS.Divisor X) (τ : T D) :
    H1Tail.mk D τ = 0 ↔ τ ∈ LinearMap.range (alphaL D) := by
  change Submodule.Quotient.mk τ = (0 : T D ⧸ LinearMap.range (alphaL D)) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]

end RS.LaurentTail
