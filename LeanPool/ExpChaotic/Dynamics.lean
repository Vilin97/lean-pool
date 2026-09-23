/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Periodic
public import Mathlib.Dynamics.Transitive

/-!
# Escaping points, dense orbits, and Devaney chaos

The remaining dynamical consequences use covering, periodic points, and Baire category.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

@[expose] public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ## Escaping points, transitivity, and dense orbits

The compact-covering theorem makes the remaining conclusions of Shen and Rempe-Gillen's
Theorem 1.1 particularly short. Escaping is expressed directly by eventual escape from every
Euclidean ball. Dense orbits are constructed by applying the Baire theorem to the sets of points
whose orbit visits each member of a fixed countable basis of the plane.
-/

/-- A point escapes to infinity if its orbit eventually leaves every centred Euclidean ball. -/
def EscapesToInfinity (z : ℂ) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, R ≤ ‖expIterate n z‖

/-- The escaping set of the complex exponential map. -/
def escapingSetExp : Set ℂ := {z | EscapesToInfinity z}

/-- Every real point escapes to infinity under iteration of the exponential map. -/
theorem escapesToInfinity_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    EscapesToInfinity z := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (R - z.re)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hre := (expIterate_real_orbit hz n).2
  have hR : R ≤ (expIterate n z).re := by
    linarith
  exact hR.trans <| (le_abs_self _).trans (Complex.abs_re_le_norm _)

/-- Any point whose orbit reaches the real axis subsequently escapes to infinity. -/
theorem escapesToInfinity_of_eventually_onRealAxis {z : ℂ} {m : ℕ}
    (hm : OnRealAxis (expIterate m z)) : EscapesToInfinity z := by
  have htail := escapesToInfinity_of_im_eq_zero hm
  intro R
  obtain ⟨N, hN⟩ := htail R
  refine ⟨m + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := hN (N + k) (Nat.le_add_right N k)
  calc
    R ≤ ‖expIterate (N + k) (expIterate m z)‖ := h
    _ = ‖expIterate (N + k + m) z‖ :=
      congrArg norm (Function.iterate_add_apply exponentialMap (N + k) m z).symm
    _ = ‖expIterate (m + N + k) z‖ := by
      congr 2
      omega

/-- **Theorem 4.1.** The escaping set of the complex exponential map is dense in the plane. -/
theorem dense_escapingSet_exp : Dense escapingSetExp := by
  apply dense_iterated_preimages_real_axis.mono
  rintro z ⟨m, hm⟩
  exact escapesToInfinity_of_eventually_onRealAxis hm

/-- **Theorem 5.1.** The complex exponential map is topologically transitive. -/
theorem topologically_transitive_exp :
    MulAction.IsTopologicallyTransitive (IterateMulAct Complex.exp) ℂ := by
  refine ⟨?_⟩
  intro U V hU hUne hV hVne
  obtain ⟨w, hwV, hw0⟩ := exists_nonzero_mem_open hV hVne
  obtain ⟨n, _, z, hzU, hzw⟩ := exists_iterate_eq_nonzero hU hUne hw0
  exact ⟨⟨n⟩, w, ⟨z, hzU, hzw⟩, hwV⟩

/-- The set of starting points whose orbit visits a specified set. -/
def orbitVisitSet (U : Set ℂ) : Set ℂ :=
  ⋃ n : ℕ, expIterate n ⁻¹' U

/-- The orbit-visit set of a nonempty open set is itself open and dense. -/
theorem isOpen_dense_orbitVisitSet {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    IsOpen (orbitVisitSet U) ∧ Dense (orbitVisitSet U) := by
  constructor
  · exact isOpen_iUnion fun n => hU.preimage (continuous_expIterate n)
  · apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨w, hwU, hw0⟩ := exists_nonzero_mem_open hU hUne
    obtain ⟨n, _, z, hzV, hzw⟩ := exists_iterate_eq_nonzero hV hVne hw0
    refine ⟨z, hzV, ?_⟩
    exact mem_iUnion.2 ⟨n, by simpa [hzw] using hwU⟩

/-- The set of points whose forward orbit under the exponential is dense in the plane. -/
def denseOrbitSetExp : Set ℂ :=
  {z | Dense (MulAction.orbit (IterateMulAct Complex.exp) z)}

/-- Visiting every member of mathlib's countable basis is equivalent to having dense orbit. -/
theorem mem_denseOrbitSetExp_iff_visit_countableBasis {z : ℂ} :
    z ∈ denseOrbitSetExp ↔
      z ∈ ⋂ U : TopologicalSpace.countableBasis ℂ, orbitVisitSet U := by
  constructor
  · intro hz
    rw [mem_iInter]
    intro U
    obtain ⟨w, hwRange, hwU⟩ := hz.exists_mem_open
      (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
      (Set.nonempty_iff_ne_empty.mpr fun hU =>
        TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))
    obtain ⟨n, rfl⟩ := hwRange
    exact mem_iUnion.2 ⟨n.val, hwU⟩
  · intro hz
    apply (TopologicalSpace.isBasis_countableBasis ℂ).dense_iff.mpr
    intro U hUb hUne
    have hzU : z ∈ orbitVisitSet U := by
      rw [mem_iInter] at hz
      exact hz ⟨U, hUb⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hzU
    exact ⟨expIterate n z, hn, ⟨n⟩, rfl⟩

/-- **Corollary 5.6.** Points with dense forward orbit are dense in the plane. -/
theorem dense_denseOrbitSet_exp : Dense denseOrbitSetExp := by
  let _ : Countable (TopologicalSpace.countableBasis ℂ) :=
    (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  apply (dense_iInter_of_isOpen (fun U : TopologicalSpace.countableBasis ℂ =>
    (isOpen_dense_orbitVisitSet
    (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
    (Set.nonempty_iff_ne_empty.mpr fun hU =>
      TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).1) fun U =>
        (isOpen_dense_orbitVisitSet
          (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
          (Set.nonempty_iff_ne_empty.mpr fun hU =>
            TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).2).mono
  intro z hz
  exact mem_denseOrbitSetExp_iff_visit_countableBasis.mpr hz

/-- Removing a countable set still leaves a dense set of points with dense orbit. -/
theorem dense_denseOrbitSet_exp_diff_countable {C : Set ℂ} (hC : C.Countable) :
    Dense (denseOrbitSetExp \ C) := by
  let _ : Countable (TopologicalSpace.countableBasis ℂ) :=
    (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  let _ : Countable C := hC.to_subtype
  let A := (TopologicalSpace.countableBasis ℂ) ⊕ C
  let G : A → Set ℂ := fun a => match a with
    | Sum.inl U => orbitVisitSet U
    | Sum.inr z => ({(z : ℂ)} : Set ℂ)ᶜ
  have hGopen : ∀ a, IsOpen (G a) := by
    rintro (U | z)
    · exact (isOpen_dense_orbitVisitSet
        (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
        (Set.nonempty_iff_ne_empty.mpr fun hU =>
          TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).1
    · exact isOpen_compl_singleton
  have hGdense : ∀ a, Dense (G a) := by
    rintro (U | z)
    · exact (isOpen_dense_orbitVisitSet
        (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
        (Set.nonempty_iff_ne_empty.mpr fun hU =>
          TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).2
    · change Dense ({(z : ℂ)}ᶜ : Set ℂ)
      exact dense_compl_singleton (z : ℂ)
  apply (dense_iInter_of_isOpen hGopen hGdense).mono
  intro z hz
  constructor
  · rw [mem_denseOrbitSetExp_iff_visit_countableBasis, mem_iInter]
    intro U
    exact mem_iInter.mp hz (Sum.inl U)
  · intro hzC
    have hzcompl := mem_iInter.mp hz (Sum.inr (⟨z, hzC⟩ : C))
    exact hzcompl (by simp)

/-- **Corollary 5.6.** The set of points with dense orbit is uncountable. -/
theorem not_countable_denseOrbitSet_exp : ¬ denseOrbitSetExp.Countable := by
  intro hcount
  obtain ⟨z, hz, hznot⟩ :=
    (dense_denseOrbitSet_exp_diff_countable hcount).nonempty
  exact hznot hz

/-- Devaney chaos on the plane: continuity, dense periodic points, and transitivity. -/
def IsDevaneyChaotic (f : ℂ → ℂ) : Prop :=
  Continuous f ∧ Dense (Function.periodicPts f) ∧
    MulAction.IsTopologicallyTransitive (IterateMulAct f) ℂ

/-- **Theorem 1.2.** The complex exponential map is chaotic in Devaney's sense. -/
theorem devaney_chaotic_exp : IsDevaneyChaotic Complex.exp := by
  exact ⟨Complex.continuous_exp, dense_periodicPts_exp, topologically_transitive_exp⟩

end

end ExponentialJuliaSetMisiurewicz
