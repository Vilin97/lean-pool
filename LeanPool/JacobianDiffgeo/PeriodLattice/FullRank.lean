/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.Nondegeneracy
import LeanPool.JacobianDiffgeo.PeriodLattice.Discreteness
import LeanPool.JacobianDiffgeo.JacobianConstruction.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Full rank and the `IsZLattice` discharge (Forster 21.4(c) shell, §6.6)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.6). `span_real_periodSubgroup`
is the linear-algebra shell around `Nondegeneracy.lean`'s
`form1_eq_zero_of_re_period_eq_zero`: if the period subgroup lay in a proper real subspace, a
nonzero real linear functional vanishing on it would complexify (Forster: "every real linear form
is the real part of a complex linear form") to a nonzero holomorphic form with vanishing real
periods, contradicting nondegeneracy. **Ungated** (uses only `Nondegeneracy.lean` + mathlib).

The `IsZLattice` instance-shaped discharge is gated exactly as `Discreteness.lean`'s
`DiscretenessHyp`, since `IsZLattice`'s class carries `[DiscreteTopology L]`.

Main declarations: `RS.span_real_periodSubgroup`, `RS.isZLattice_periodSubgroup_topologicalClosure`,
`RS.finrank_int_periodSubgroup`.
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Forster 21.4(c)**: the period subgroup spans `Fin (genus X) → ℂ` over `ℝ` (nondegeneracy).
Ungated: uses only `form1_eq_zero_of_re_period_eq_zero` (mathlib + built units). -/
theorem span_real_periodSubgroup :
    Submodule.span ℝ ((periodSubgroup X : Set (Fin (genus X) → ℂ))) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span ℝ (periodSubgroup X : Set (Fin (genus X) → ℂ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  obtain ⟨φ, hφne, hφmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hφΛ : ∀ v ∈ periodSubgroup X, φ v = 0 := by
    intro v hv
    have hmem : φ v ∈ (Submodule.span ℝ (periodSubgroup X : Set (Fin (genus X) → ℂ))).map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span hv)
    rw [hφmap] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  set c : Fin (genus X) → ℂ := fun i =>
    (φ ((Pi.single i (1 : ℂ) : Fin (genus X) → ℂ)) : ℂ) - Complex.I *
        (φ ((Pi.single i Complex.I : Fin (genus X) → ℂ)) : ℂ) with hc_def
  -- The Pi.single decomposition machinery, shared by the two directions we need.
  have hsingle_decomp : ∀ i (w : ℂ),
      Pi.single i w = w.re • (Pi.single i (1 : ℂ) : Fin (genus X) → ℂ) + w.im •
          (Pi.single i Complex.I : Fin (genus X) → ℂ) := by
    intro i w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simp []
    conv_lhs => rw [hw]
    rw [Pi.single_add, Pi.single_smul, Pi.single_smul]
  have hφdecomp : ∀ v : Fin (genus X) → ℂ,
      φ v = ∑ i, ((v i).re * φ ((Pi.single i (1 : ℂ) : Fin (genus X) → ℂ)) + (v i).im * φ
          ((Pi.single i Complex.I : Fin (genus X) → ℂ))) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsingle_decomp i (v i), map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hcomp : ∀ i (w : ℂ),
      (c i * w).re = w.re * φ ((Pi.single i (1 : ℂ) : Fin (genus X) → ℂ)) + w.im * φ
          ((Pi.single i Complex.I : Fin (genus X) → ℂ)) := by
    intro i w
    rw [hc_def]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hkey : ∀ v : Fin (genus X) → ℂ, (∑ i, c i * v i).re = φ v := by
    intro v
    have hresum : (∑ i, c i * v i).re = ∑ i, (c i * v i).re := by
      induction (Finset.univ : Finset (Fin (genus X))) using Finset.induction with
      | empty => simp
      | insert j s hj ih => simp [Finset.sum_insert hj, ih]
    rw [hresum, hφdecomp v]
    exact Finset.sum_congr rfl fun i _ => hcomp i (v i)
  set eta0 : Form1 X := ∑ i, c i • basis X i with heta0_def
  have hetaperiod : ∀ γ : Path (Classical.arbitrary X) (Classical.arbitrary X),
      (period γ eta0).re = 0 := by
    intro γ
    have heq : period γ eta0 = ∑ i, c i * period γ (basis X i) := by
      change pathIntegral γ (∑ i, c i • basis X i) = ∑ i, c i * pathIntegral γ (basis X i)
      induction (Finset.univ : Finset (Fin (genus X))) using Finset.induction with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, pathIntegral_add, pathIntegral_smul, ih]
    rw [heq]
    change (∑ i, c i * periodVector (basis X) γ i).re = 0
    rw [hkey (periodVector (basis X) γ)]
    have hmemPV : periodVector (basis X) γ ∈ periodSubgroup X :=
      AddSubgroup.subset_closure ⟨γ, rfl⟩
    exact hφΛ _ hmemPV
  have heta00 : eta0 = 0 := form1_eq_zero_of_re_period_eq_zero hetaperiod
  have hc0 : c = 0 := by
    have h0 : (∑ i, c i • basis X i) = 0 := heta00
    exact funext (Fintype.linearIndependent_iff.mp (basis X).linearIndependent c h0)
  apply hφne
  apply LinearMap.ext
  intro v
  rw [hφdecomp v]
  have hzero : ∀ i, φ ((Pi.single i (1 : ℂ) : Fin (genus X) → ℂ)) = 0 ∧ φ
      ((Pi.single i Complex.I : Fin (genus X) → ℂ)) = 0 := by
    intro i
    have hci : c i = 0 := congrFun hc0 i
    rw [hc_def] at hci
    constructor
    · have := congrArg Complex.re hci
      simpa using this
    · have := congrArg Complex.im hci
      simpa using this
  simp [hzero]

/-- The gated `IsZLattice` instance-shape the ledger needs, once discreteness discharges
(`DiscretenessHyp`, exactly `Discreteness.lean`'s gate). -/
theorem isZLattice_periodSubgroup_topologicalClosure (hupgrade : DiscretenessHyp X) :
    haveI := discreteTopology_periodSubgroup_topologicalClosure hupgrade
    IsZLattice ℝ (periodSubgroup X).topologicalClosure.toIntSubmodule := by
  have := discreteTopology_periodSubgroup_topologicalClosure hupgrade
  refine ⟨?_⟩
  rw [AddSubgroup.coe_toIntSubmodule, periodSubgroup_topologicalClosure_eq hupgrade]
  by_cases hgen : genus X = 0
  · have hsub : Subsingleton (Fin (genus X) → ℂ) := by rw [hgen]; infer_instance
    apply eq_top_iff.mpr
    intro v _
    rw [hsub.elim v 0]
    exact Submodule.zero_mem _
  · exact span_real_periodSubgroup

/-- **Bonus** (blueprint's "real basis of rank `2g`"): free once the `IsZLattice` instance is
discharged, via mathlib's `ZLattice.rank`. -/
theorem finrank_int_periodSubgroup (hupgrade : DiscretenessHyp X) :
    Module.finrank ℤ (periodSubgroup X).topologicalClosure.toIntSubmodule = 2 * genus X := by
  have := discreteTopology_periodSubgroup_topologicalClosure hupgrade
  have := isZLattice_periodSubgroup_topologicalClosure hupgrade
  rw [ZLattice.rank ℝ, Module.finrank_pi_fintype ℝ]
  simp [Complex.finrank_real_complex, mul_comm]

end RS

end
