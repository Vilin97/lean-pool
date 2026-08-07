/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.Membership
import LeanPool.JacobianDiffgeo.Path.Perturb
import LeanPool.JacobianDiffgeo.LocalMultiplicity.ChartBridge
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin

/-!
# Generic points (Forster §21.3)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.2). There are `genus X`
distinct points `a₁,…,a_g ∈ X` such that any `ω ∈ Form1 X` vanishing at all `aⱼ` is identically
zero: Forster's proof is a strict descending induction on `dim ⋂ⱼ ker (evalAt aⱼ)`, using that a
nonzero holomorphic form is nonzero off any finite set (openness of the nonvanishing locus +
`RS.nonempty_open_diff_finite`).

Main declarations: `RS.isOpen_coeffAt_ne_zero`, `RS.exists_coeffAt_ne_zero_notMem`,
`RS.exists_genericPoints`, `RS.det_genericMatrix_ne_zero`.
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `coeffAt x` bundled as a `ℂ`-linear functional. -/
def evalAtₗ (x : X) : Form1 X →ₗ[ℂ] ℂ where
  toFun η := coeffAt x η
  map_add' := coeffAt_add x
  map_smul' := coeffAt_smul x

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp] theorem evalAtₗ_apply (x : X) (η : Form1 X) : evalAtₗ x η = coeffAt x η := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The nonvanishing locus of a form's coefficient is open. -/
theorem isOpen_coeffAt_ne_zero (η : Form1 X) : IsOpen {x : X | coeffAt x η ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set e := chartAt ℂ x₀ with he_def
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x₀
  have hne : coeffIn e η (e x₀) ≠ 0 := hx₀
  have hcont : ContinuousAt (coeffIn e η) (e x₀) :=
    (η.continuousOn_coeffIn he).continuousAt (e.open_target.mem_nhds (mem_chart_target ℂ x₀))
  have hev : ∀ᶠ z in 𝓝 (e x₀), coeffIn e η z ≠ 0 := hcont.eventually_ne hne
  have htend : Tendsto e (𝓝 x₀) (𝓝 (e x₀)) := e.continuousAt (mem_chart_source ℂ x₀)
  have h1 : e.source ∈ 𝓝 x₀ := e.open_source.mem_nhds (mem_chart_source ℂ x₀)
  filter_upwards [htend.eventually hev, h1] with x hx hxsrc
  show coeffAt x η ≠ 0
  have hz : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (e.source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hxsrc, mem_chart_source ℂ x⟩, rfl⟩
  have heq : coeffIn (chartAt ℂ x) η (chartAt ℂ x x) =
      deriv (⇑e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
        coeffIn e η (e ((chartAt ℂ x).symm (chartAt ℂ x x))) :=
    coeffIn_trans he (chart_mem_maximalAtlas x) η hz
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at heq
  change (coeffIn (chartAt ℂ x) η (chartAt ℂ x x) : ℂ) ≠ 0
  rw [heq]
  exact mul_ne_zero
    (analyticAt_transition (chart_mem_maximalAtlas x) he (mem_chart_source ℂ x) hxsrc).2 hx

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- A nonzero form is nonzero somewhere off any finite set (openness + avoidance). -/
theorem exists_coeffAt_ne_zero_notMem {η : Form1 X} (hη : η ≠ 0) (S : Finset X) :
    ∃ x, x ∉ S ∧ coeffAt x η ≠ 0 := by
  have hne : {x : X | coeffAt x η ≠ 0}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    exact hη (Form1.ext_coeffAt fun x => by
      by_contra hx
      exact (Set.eq_empty_iff_forall_notMem.mp hcon) x hx)
  obtain ⟨x, hx⟩ :=
    nonempty_open_diff_finite (isOpen_coeffAt_ne_zero η) hne S.finite_toSet
  exact ⟨x, hx.2, hx.1⟩

variable (X) in
/-- The submodule of forms vanishing at every point of `s`. -/
def genericKernel (s : Finset X) : Submodule ℂ (Form1 X) where
  carrier := {η | ∀ x ∈ s, coeffAt x η = 0}
  zero_mem' x _ := coeffAt_zero x
  add_mem' {η η'} hη hη' x hx := by rw [coeffAt_add, hη x hx, hη' x hx, add_zero]
  smul_mem' c η hη x hx := by rw [coeffAt_smul, hη x hx, mul_zero]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem mem_genericKernel {s : Finset X} {η : Form1 X} :
    η ∈ genericKernel X s ↔ ∀ x ∈ s, coeffAt x η = 0 := Iff.rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem genericKernel_anti {s t : Finset X} (h : s ⊆ t) :
    genericKernel X t ≤ genericKernel X s := fun _ hη x hx => hη x (h hx)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem genericKernel_empty : genericKernel X (∅ : Finset X) = ⊤ := by
  ext η
  simp [mem_genericKernel]

/-- Descending induction: after choosing `k` points, the kernel's finrank has dropped by (at
least) `k`, saturating at `⊥` once `k ≥ genus X`. -/
theorem exists_finset_card_finrank_le (k : ℕ) :
    ∃ s : Finset X, s.card = k ∧ Module.finrank ℂ (genericKernel X s) ≤ genus X - k := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, rfl, ?_⟩
    rw [genericKernel_empty, finrank_top ℂ (Form1 X), Nat.sub_zero]
    exact le_refl _
  | succ k ih =>
    obtain ⟨s, hscard, hsfr⟩ := ih
    by_cases hbot : genericKernel X s = ⊥
    · obtain ⟨x, -, hxs⟩ :=
        nonempty_open_diff_finite isOpen_univ Set.univ_nonempty s.finite_toSet
      refine ⟨insert x s, by rw [Finset.card_insert_of_notMem hxs, hscard], ?_⟩
      have hle : genericKernel X (insert x s) ≤ genericKernel X s :=
        genericKernel_anti (Finset.subset_insert x s)
      rw [hbot, le_bot_iff] at hle
      rw [hle]
      simp
    · obtain ⟨η, hηmem, hηne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨x, hxs, hxne⟩ := exists_coeffAt_ne_zero_notMem hηne s
      have hlt : genericKernel X (insert x s) < genericKernel X s := by
        refine lt_of_le_of_ne (genericKernel_anti (Finset.subset_insert x s)) fun heq => ?_
        exact hxne ((heq ▸ hηmem) x (Finset.mem_insert_self x s))
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      have hklt : k < genus X := by
        by_contra hcon
        push Not at hcon
        exact hbot (Submodule.finrank_eq_zero.mp
          (Nat.le_zero.mp (hsfr.trans_eq (Nat.sub_eq_zero_of_le hcon))))
      refine ⟨insert x s, by rw [Finset.card_insert_of_notMem hxs, hscard], ?_⟩
      omega

/-- **Forster 21.3**: `genus X` distinct points such that any form vanishing at all of them is
identically zero. -/
theorem exists_genericPoints (_hg : 1 ≤ genus X) : ∃ a : Fin (genus X) → X,
    Function.Injective a ∧ ∀ η : Form1 X, (∀ j, coeffAt (a j) η = 0) → η = 0 := by
  obtain ⟨s, hscard, hsfr⟩ := exists_finset_card_finrank_le (X := X) (genus X)
  rw [Nat.sub_self] at hsfr
  have hbot : genericKernel X s = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hsfr)
  set e := Finset.equivFinOfCardEq hscard with he_def
  refine ⟨fun j => ((e.symm j : s) : X), fun j j' hjj' => e.symm.injective (Subtype.ext hjj'), ?_⟩
  intro η hη
  have hηmem : η ∈ genericKernel X s := by
    intro x hx
    have hkey : ((e.symm (e ⟨x, hx⟩) : s) : X) = x := by rw [Equiv.symm_apply_apply]
    rw [← hkey]
    exact hη (e ⟨x, hx⟩)
  rw [hbot] at hηmem
  simpa using hηmem

omit [ConnectedSpace X] in
/-- The generic-point evaluation matrix `A i j := coeffAt (a j) (basis X i)` is invertible
(transpose of the natural evaluation map; §21.4(a)). -/
theorem det_genericMatrix_ne_zero {a : Fin (genus X) → X}
    (ha : ∀ η : Form1 X, (∀ j, coeffAt (a j) η = 0) → η = 0) :
    (Matrix.of fun i j => coeffAt (a j) (basis X i)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hcne, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  apply hcne
  have hη : ∀ j, coeffAt (a j) (∑ i, c i • basis X i) = 0 := by
    intro j
    have hlin : evalAtₗ (a j) (∑ i, c i • basis X i) = ∑ i, c i * coeffAt (a j) (basis X i) := by
      rw [map_sum]
      simp
    have hcol : Matrix.vecMul c (Matrix.of fun i j => coeffAt (a j) (basis X i)) j
        = ∑ i, c i * coeffAt (a j) (basis X i) := rfl
    have := congrFun hc0 j
    rw [hcol] at this
    rw [← evalAtₗ_apply, hlin]
    exact this
  have hη0 : (∑ i, c i • basis X i) = 0 := ha _ hη
  exact funext (Fintype.linearIndependent_iff.mp (basis X).linearIndependent c hη0)

end RS

end
