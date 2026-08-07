/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.GenericPoints
import LeanPool.JacobianDiffgeo.PeriodLattice.Segment
import LeanPool.JacobianDiffgeo.Abel
import LeanPool.JacobianDiffgeo.CanonicalForms
import LeanPool.JacobianDiffgeo.ResidueTheorem
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Discreteness of the period subgroup (Forster 21.4(a)+(b))

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.3). The local Jacobi map (via
the inverse function theorem on `ℂ^g`) plus the Abel `k`-point sufficiency direction plus the
residue theorem show `Λ ∩ W ⊆ {0}` for an explicit neighborhood `W` of `0`, hence `Λ` is discrete.

**GATED**: on `RS.Abel.WeakSolutionUpgradeFinset X ↥S` (Abel's own remaining hypothesis, for
every `S : Finset (Fin (genus X))` that can arise as the "moved-coordinates" index set) — every
theorem here threads it explicitly, exactly as `Jacobian.Abel` does for its own gated exports; it
discharges automatically once that unit's sibling pass proves it unconditionally.

Main declarations: `RS.exists_isolating_nhds_periodSubgroup`, `RS.discreteTopology_periodSubgroup`,
`RS.periodSubgroup_topologicalClosure_eq`, `RS.discreteTopology_periodSubgroup_topologicalClosure`.
-/

open scoped ContDiff Manifold  Topology
open Set Filter Metric IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The upgrade hypothesis this unit consumes, universally over every `Finset`-indexed shape that
can arise (the `k`-point Abel sufficiency direction, threaded exactly as `Jacobian.Abel` states
it). -/
abbrev DiscretenessHyp (X : Type*) [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ S : Finset (Fin (genus X)), RS.Abel.WeakSolutionUpgradeFinset X (↥S : Type)

omit [ConnectedSpace X] in
/-- The coordinate map assembled from the per-chart primitives is strictly differentiable at the
base point, with the generic matrix as its derivative. Split out of
`exists_isolating_nhds_periodSubgroup` for the 200-line proof size we hold ourselves to. -/
private theorem hasStrictFDerivAt_coordMap {e : Fin (genus X) → OpenPartialHomeomorph X ℂ}
    {c₀ : Fin (genus X) → ℂ} {r : Fin (genus X) → ℝ} (hr : ∀ j, 0 < r j)
    {gp : Fin (genus X) → Fin (genus X) → ℂ → ℂ}
    {A : Matrix (Fin (genus X)) (Fin (genus X)) ℂ}
    (hgp : ∀ i j, ∀ z ∈ ball (c₀ j) (r j), HasDerivAt (gp i j) (coeffIn (e j) (basis X i) z) z)
    (hAij : ∀ i j, coeffIn (e j) (basis X i) (c₀ j) = A i j) :
    HasStrictFDerivAt (fun w : Fin (genus X) → ℂ => fun i => ∑ j, gp i j (w j))
      ((Matrix.mulVecLin A).toContinuousLinearMap :
        (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)) c₀ := by
  set 𝔉 : (Fin (genus X) → ℂ) → (Fin (genus X) → ℂ) := fun w i => ∑ j, gp i j (w j) with h𝔉_def
  set proj' : Fin (genus X) → (Fin (genus X) → ℂ) →L[ℂ] ℂ :=
    fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (genus X) => ℂ) j with hproj_def
  change HasStrictFDerivAt 𝔉
    ((Matrix.mulVecLin A).toContinuousLinearMap :
      (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)) c₀
  have happly : ∀ j, HasStrictFDerivAt (fun w : Fin (genus X) → ℂ => w j) (proj' j) c₀ :=
    fun j => hasStrictFDerivAt_apply (F' := fun _ : Fin (genus X) => ℂ) j c₀
  have hcomp : ∀ i j, HasStrictFDerivAt (fun w : Fin (genus X) → ℂ => gp i j (w j))
      (A i j • proj' j) c₀ := by
    intro i j
    have hdiffon : DifferentiableOn ℂ (gp i j) (ball (c₀ j) (r j)) :=
      fun z hz => (hgp i j z hz).differentiableAt.differentiableWithinAt
    have han : AnalyticAt ℂ (gp i j) (c₀ j) :=
      hdiffon.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (hr j)))
    have hstrictderiv : HasStrictDerivAt (gp i j) (deriv (gp i j) (c₀ j)) (c₀ j) :=
      han.hasStrictDerivAt
    have hderiveq : deriv (gp i j) (c₀ j) = A i j := by
      rw [(hgp i j (c₀ j) (mem_ball_self (hr j))).deriv, hAij]
    rw [hderiveq] at hstrictderiv
    exact hstrictderiv.comp_hasStrictFDerivAt c₀ (happly j)
  have hsum : ∀ i, HasStrictFDerivAt (fun w : Fin (genus X) → ℂ => ∑ j, gp i j (w j))
      (∑ j, A i j • proj' j) c₀ := by
    intro i
    have hraw := HasStrictFDerivAt.sum (u := (Finset.univ : Finset (Fin (genus X))))
      (fun j (_ : j ∈ Finset.univ) => hcomp i j)
    have hfun : (∑ j, fun w : Fin (genus X) → ℂ => gp i j (w j))
        = fun w : Fin (genus X) → ℂ => ∑ j, gp i j (w j) := by
      funext w; rw [Finset.sum_apply]
    rwa [hfun] at hraw
  have hpi := hasStrictFDerivAt_pi.mpr hsum
  have heq : ContinuousLinearMap.pi (fun i => ∑ j, A i j • proj' j)
      = (Matrix.mulVecLin A).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    change (∑ j, A i j • proj' j) v = _
    simp [hproj_def, sum_apply, Matrix.mulVec,
      dotProduct]
  rwa [heq] at hpi

open scoped Classical in
omit [ConnectedSpace X] in
/-- The residue of the `k`-th twisted form at the `j`-th base point is the generic-matrix entry
times the local residue. Split out of `exists_isolating_nhds_periodSubgroup` for the 200-line
proof size we hold ourselves to. -/
private theorem resAt_twisted_eq {a x : Fin (genus X) → X}
    {e : Fin (genus X) → OpenPartialHomeomorph X ℂ} (he : ∀ j, e j ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hefun : e = fun j => chartAt ℂ (a j)) {c₀ : Fin (genus X) → ℂ}
    (hc₀_def : c₀ = fun j => e j (a j))
    {A : Matrix (Fin (genus X)) (Fin (genus X)) ℂ}
    (hAij : ∀ i j, coeffIn (e j) (basis X i) (c₀ j) = A i j) {F : RS.Mero X}
    (hFordAll : ∀ j, F.ord (a j) = if x j = a j then 0 else -1) :
    ∀ k j, ((F • MForm.ofForm1 (basis X k) : MForm X)).resAt (a j) =
      A k j * RS.resAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) := by
  subst hc₀_def
  subst hefun
  set e : Fin (genus X) → OpenPartialHomeomorph X ℂ := fun j => chartAt ℂ (a j) with he_def
  set c₀ : Fin (genus X) → ℂ := fun j => e j (a j) with hc₀_def
  set Θ : Fin (genus X) → MForm X := fun k => F • MForm.ofForm1 (basis X k) with hΘ_def
  set c : Fin (genus X) → ℂ := fun j =>
    RS.resAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) with hc_def
  change ∀ k j, (Θ k).resAt (a j) = A k j * c j
  intro k j
  have hcoeffAt : (MFormData.smul F (MFormData.ofForm1 (basis X k))).coeffAt (a j)
      =ᶠ[𝓝 (c₀ j)] fun z => F.holoRepr ((e j).symm z) * coeffIn (e j) (basis X k) z := by
    filter_upwards [(e j).open_target.mem_nhds (mem_chart_target ℂ (a j))] with z hz
    change F.holoRepr ((e j).symm z) *
      (if z ∈ (e j).target then coeffIn (e j) (basis X k) z else 0) = _
    rw [if_pos hz]
  have hresrw : RS.resAt ((MFormData.smul F (MFormData.ofForm1 (basis X k))).coeffAt (a j))
      (c₀ j) = RS.resAt (fun z => F.holoRepr ((e j).symm z) * coeffIn (e j) (basis X k) z)
        (c₀ j) := resAt_congr (hcoeffAt.filter_mono nhdsWithin_le_nhds)
  have hmerF : MeromorphicAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) :=
    (meromorphicAtX_iff_of_mem_source (he j) (mem_chart_source ℂ (a j))).mp
      (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ F (a j) (mem_univ _))
  have hordF : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) := by
    have := Mero.ord_eq_meromorphicOrderAt_holoRepr F (a j)
    rw [hc₀_def]
    change ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (F.holoRepr ∘ ⇑(e j).symm) (e j (a j))
    rw [← this, hFordAll j]
    split_ifs with hcase
    · decide
    · decide
  have hanalytic : AnalyticAt ℂ (coeffIn (e j) (basis X k)) (c₀ j) :=
    (basis X k).analyticAt_coeffAt (a j)
  have hmul := resAt_analyticAt_mul hanalytic hmerF hordF
  have hfun : (fun z => F.holoRepr ((e j).symm z) * coeffIn (e j) (basis X k) z)
      = fun z => coeffIn (e j) (basis X k) z * (F.holoRepr ∘ ⇑(e j).symm) z := by
    funext z; change F.holoRepr ((e j).symm z) * _ = _ * F.holoRepr ((e j).symm z); ring
  change RS.resAt ((MFormData.smul F (MFormData.ofForm1 (basis X k))).coeffAt (a j)) (c₀ j) = _
  rw [hresrw, hfun, hmul]
  have hIcc : Finset.Icc (-1 : ℤ) (-1) = {-1} := rfl
  rw [hIcc, Finset.sum_singleton]
  change taylorCoeffAt (coeffIn (e j) (basis X k)) (c₀ j) (-1 - (-1)).toNat
    * laurentCoeffAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) (-1) = A k j * c j
  norm_num
  rw [hAij k j, hc_def]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Around each base point there is a chart ball whose preimage stays inside the separating
neighbourhood. Split out of `exists_isolating_nhds_periodSubgroup` for the 200-line proof size we
hold ourselves to. -/
private theorem exists_ball_subset_sep {a : Fin (genus X) → X} {U : X → Set X}
    (hUmem' : ∀ j, a j ∈ U (a j) ∧ IsOpen (U (a j))) :
    ∀ j : Fin (genus X), ∃ r : ℝ, 0 < r ∧
      ball (chartAt ℂ (a j) (a j)) r ⊆ (chartAt ℂ (a j)).target ∧
      (chartAt ℂ (a j)).symm '' ball (chartAt ℂ (a j) (a j)) r ⊆ U (a j) := by
  set e : Fin (genus X) → OpenPartialHomeomorph X ℂ := fun j => chartAt ℂ (a j) with he_def
  change ∀ j : Fin (genus X), ∃ r : ℝ, 0 < r ∧ ball (e j (a j)) r ⊆ (e j).target ∧
    (e j).symm '' ball (e j (a j)) r ⊆ U (a j)
  intro j
  have h1 : IsOpen (e j '' (U (a j) ∩ (e j).source)) :=
    (e j).isOpen_image_of_subset_source ((hUmem' j).2.inter (e j).open_source)
      inter_subset_right
  have h2 : e j (a j) ∈ e j '' (U (a j) ∩ (e j).source) :=
    ⟨a j, ⟨(hUmem' j).1, mem_chart_source ℂ (a j)⟩, rfl⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp h1 (e j (a j)) h2
  obtain ⟨ρ', hρ', hρ'sub⟩ :=
    Metric.isOpen_iff.mp (e j).open_target (e j (a j)) (mem_chart_target ℂ (a j))
  refine ⟨min ρ ρ', lt_min hρ hρ', (ball_subset_ball (min_le_right ρ ρ')).trans hρ'sub, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzρ : z ∈ ball (e j (a j)) ρ := (ball_subset_ball (min_le_left ρ ρ')) hz
  obtain ⟨y, ⟨hyU, hysrc⟩, hyz⟩ := hρsub hzρ
  rw [← hyz, (e j).left_inv hysrc]
  exact hyU

open scoped Classical in
omit [ConnectedSpace X] in
/-- Away from the base points the twisted form has no residue. Split out of
`exists_isolating_nhds_periodSubgroup` for the 200-line proof size we hold ourselves to. -/
private theorem resAt_twisted_eq_zero_off_base {S : Finset (Fin (genus X))}
    {a : Fin (genus X) → X} {a' x' : (↥S : Type) → X} (ha'_def : a' = fun i => a i.1)
    {F : RS.Mero X} (hFordx : ∀ i, F.ord (x' i) = 1)
    (hFord0 : ∀ y, (∀ i, y ≠ a' i) → (∀ i, y ≠ x' i) → F.ord y = 0) :
    ∀ k, ∀ y ∉ (Finset.univ.image a : Set X),
      ((F • MForm.ofForm1 (basis X k) : MForm X)).resAt y = 0 := by
  set Θ : Fin (genus X) → MForm X := fun k => F • MForm.ofForm1 (basis X k) with hΘ_def
  change ∀ k, ∀ y ∉ (Finset.univ.image a : Set X), (Θ k).resAt y = 0
  intro k y hy
  have hordΘ : 0 ≤ (Θ k).ord y := by
    rw [hΘ_def]
    change 0 ≤ (F • MForm.ofForm1 (basis X k)).ord y
    rw [MForm.ord_smul_mero]
    by_cases hyx : ∃ i : (↥S : Type), y = x' i
    · obtain ⟨i, hi⟩ := hyx
      have hFy : F.ord y = 1 := hi ▸ hFordx i
      rw [hFy]
      exact add_nonneg (by decide) (MForm.ofForm1_ord_nonneg (basis X k) y)
    · push Not at hyx
      have hya : ∀ i : (↥S : Type), y ≠ a' i := by
        intro i hcon
        exact hy (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, (ha'_def ▸ hcon).symm⟩))
      have hFy : F.ord y = 0 := hFord0 y hya hyx
      rw [hFy]
      simpa using MForm.ofForm1_ord_nonneg (basis X k) y
  exact MForm.resAt_eq_zero_of_ord_nonneg hordΘ

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- A base point where the meromorphic function has a genuine pole contributes a nonzero local
residue. Split out of `exists_isolating_nhds_periodSubgroup` for the 200-line proof size we hold
ourselves to. -/
private theorem local_residue_ne_zero {a : Fin (genus X) → X} {F : RS.Mero X}
    (j₀ : Fin (genus X)) (hordj₀ : F.ord (a j₀) = -1) :
    RS.resAt (F.holoRepr ∘ ⇑(chartAt ℂ (a j₀)).symm) (chartAt ℂ (a j₀) (a j₀)) ≠ 0 := by
  have hordeq : meromorphicOrderAt (F.holoRepr ∘ ⇑(chartAt ℂ (a j₀)).symm)
      (chartAt ℂ (a j₀) (a j₀)) = -1 := by
    rw [← Mero.ord_eq_meromorphicOrderAt_holoRepr, hordj₀]
  have hmerF : MeromorphicAt (F.holoRepr ∘ ⇑(chartAt ℂ (a j₀)).symm) (chartAt ℂ (a j₀) (a j₀)) :=
    (meromorphicAtX_iff_of_mem_source (chart_mem_maximalAtlas (a j₀))
        (mem_chart_source ℂ (a j₀))).mp
      (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ F (a j₀) (mem_univ _))
  have := laurentCoeffAt_order_ne_zero hmerF (by rw [hordeq]; simp)
  rwa [hordeq] at this

open scoped Classical in
/-- **Forster 21.4(a)+(b)**: the local Jacobi map (inverse function theorem) plus the Abel
`k`-point sufficiency direction plus the residue theorem isolate `0` in the period subgroup. -/
theorem exists_isolating_nhds_periodSubgroup (hg : 1 ≤ genus X) (hupgrade : DiscretenessHyp X) :
    ∃ W ∈ 𝓝 (0 : Fin (genus X) → ℂ), ∀ t ∈ periodSubgroup X, t ∈ W → t = 0 := by
  obtain ⟨a, hainj, ha⟩ := exists_genericPoints hg
  set e : Fin (genus X) → OpenPartialHomeomorph X ℂ := fun j => chartAt ℂ (a j) with he_def
  have he : ∀ j, e j ∈ maximalAtlas 𝓘(ℂ) ω X := fun j => chart_mem_maximalAtlas (a j)
  /- **Stage A**: pairwise disjoint chart-ball images around the `a j`. -/
  obtain ⟨U, hUmem, hUdisj⟩ := (Set.finite_range a).t2_separation (X := X)
  have hUmem' : ∀ j, a j ∈ U (a j) ∧ IsOpen (U (a j)) := fun j => hUmem (a j)
  have hex := exists_ball_subset_sep hUmem'
  choose r hr hballsub hVsub using hex
  set V : Fin (genus X) → Set X := fun j => (e j).symm '' ball (e j (a j)) (r j) with hV_def
  have hVdisj : Pairwise (fun j j' => Disjoint (V j) (V j')) := by
    intro j j' hjj'
    apply Disjoint.mono (hVsub j) (hVsub j')
    exact hUdisj (Set.mem_range_self j) (Set.mem_range_self j') (fun h => hjj' (hainj h))
  have haV : ∀ j, a j ∈ V j := fun j =>
    ⟨e j (a j), mem_ball_self (hr j), (e j).left_inv (mem_chart_source ℂ (a j))⟩
  /- **Stage B**: the local Jacobi map, its strict derivative, and the inverse function theorem. -/
  set c₀ : Fin (genus X) → ℂ := fun j => e j (a j) with hc₀_def
  have hgp : ∀ i j : Fin (genus X), ∃ gp : ℂ → ℂ, gp (c₀ j) = 0 ∧
      ∀ z ∈ ball (c₀ j) (r j), HasDerivAt gp (coeffIn (e j) (basis X i) z) z := by
    intro i j
    obtain ⟨gp, hgp0, hgp⟩ := exists_hasDerivAt_ball
      ((basis X i).analyticOnNhd_coeffIn (he j)) (hballsub j) (mem_ball_self (hr j)) (w := 0)
    exact ⟨gp, hgp0, hgp⟩
  choose gp hgp0 hgp using hgp
  set 𝔉 : (Fin (genus X) → ℂ) → (Fin (genus X) → ℂ) := fun w i => ∑ j, gp i j (w j) with h𝔉_def
  set A : Matrix (Fin (genus X)) (Fin (genus X)) ℂ := Matrix.of fun i j => coeffAt (a j) (basis X i)
    with hA_def
  have hAdet : A.det ≠ 0 := det_genericMatrix_ne_zero ha
  have h𝔉c₀ : 𝔉 c₀ = 0 := by
    funext i
    change ∑ j, gp i j (c₀ j) = 0
    simp [hgp0]
  have hAij : ∀ i j, coeffIn (e j) (basis X i) (c₀ j) = A i j := fun i j => rfl
  set proj' : Fin (genus X) → (Fin (genus X) → ℂ) →L[ℂ] ℂ :=
    fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (genus X) => ℂ) j with hproj_def
  -- The strict derivative of `𝔉` at `c₀` is (as a continuous linear map) exactly `A`.
  have hstrict := hasStrictFDerivAt_coordMap hr hgp hAij
  have hACLMdet : ((Matrix.mulVecLin A).toContinuousLinearMap
      : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)).det ≠ 0 := by
    change LinearMap.det ((Matrix.mulVecLin A).toContinuousLinearMap
      : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ)) ≠ 0
    have hcoe : ((Matrix.mulVecLin A).toContinuousLinearMap
        : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ)) = Matrix.mulVecLin A := rfl
    rw [hcoe, ← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact hAdet
  set Aequiv := ((Matrix.mulVecLin A).toContinuousLinearMap
    : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)).toContinuousLinearEquivOfDetNeZero hACLMdet
    with hAequiv_def
  have hstrict' : HasStrictFDerivAt 𝔉 (Aequiv : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)) c₀ :=
      by
    rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  have hmap : Filter.map 𝔉 (𝓝 c₀) = 𝓝 (𝔉 c₀) := hstrict'.map_nhds_eq_of_equiv
  set polydisc : Set (Fin (genus X) → ℂ) := Set.univ.pi (fun j => ball (c₀ j) (r j))
    with hpolydisc_def
  have hpolymem : polydisc ∈ 𝓝 c₀ :=
    set_pi_mem_nhds Set.finite_univ (fun j _ => ball_mem_nhds (c₀ j) (hr j))
  have hWmem : 𝔉 '' polydisc ∈ 𝓝 (0 : Fin (genus X) → ℂ) := by
    rw [← h𝔉c₀, ← hmap]
    exact Filter.image_mem_map hpolymem
  refine ⟨𝔉 '' polydisc, hWmem, ?_⟩
  /- **Stage C**: `Λ ∩ W ⊆ {0}`. -/
  intro t htmem htW
  by_contra htne
  obtain ⟨w, hwpoly, hwt⟩ := htW
  obtain ⟨γ, hγ⟩ := (mem_periodSubgroup_iff X).mp htmem
  have hwj : ∀ j, w j ∈ ball (c₀ j) (r j) := fun j => hwpoly j (Set.mem_univ j)
  set x : Fin (genus X) → X := fun j => (e j).symm (w j) with hx_def
  have hxsrc : ∀ j, x j ∈ (e j).source := fun j => (e j).map_target (hballsub j (hwj j))
  have hexj : ∀ j, e j (x j) = w j := fun j => (e j).right_inv (hballsub j (hwj j))
  have hxball : ∀ j, e j (x j) ∈ ball (c₀ j) (r j) := fun j => by rw [hexj j]; exact hwj j
  set σ : ∀ j, Path (a j) (x j) := fun j =>
    segmentPath (hballsub j) (mem_chart_source ℂ (a j)) (hxsrc j) (mem_ball_self (hr j)) (hxball j)
    with hσ_def
  have hσint : ∀ i j, pathIntegral (σ j) (basis X i) = gp i j (w j) := by
    intro i j
    have hkey := pathIntegral_segmentPath (he j) (hballsub j) (mem_chart_source ℂ (a j)) (hxsrc j)
      (mem_ball_self (hr j)) (hxball j) (hgp i j)
    rw [hexj] at hkey
    rw [hkey, hgp0, sub_zero]
  have hlin : ∀ η : Form1 X, ∑ j, pathIntegral (σ j) η = pathIntegral γ η := by
    have hL : (∑ j, pathIntegralₗ (σ j) : Form1 X →ₗ[ℂ] ℂ) = pathIntegralₗ γ := by
      apply (basis X).ext
      intro i
      have hlhs : (∑ j, pathIntegralₗ (σ j) : Form1 X →ₗ[ℂ] ℂ) (basis X i)
          = ∑ j, pathIntegral (σ j) (basis X i) := by
        simp [LinearMap.sum_apply, pathIntegralₗ]
      rw [hlhs]
      simp only [hσint]
      change ∑ j, gp i j (w j) = pathIntegral γ (basis X i)
      have : ∑ j, gp i j (w j) = 𝔉 w i := rfl
      rw [this, hwt]
      change t i = period γ (basis X i)
      rw [← hγ]; rfl
    intro η
    have := congrFun (congrArg DFunLike.coe hL) η
    simpa [pathIntegralₗ] using this
  -- `t ≠ 0` forces some `x j ≠ a j`.
  have hSne : ∃ j, x j ≠ a j := by
    by_contra hcon
    push Not at hcon
    apply htne
    have hweq : w = c₀ := by
      funext j
      rw [← hexj j, hcon j]
    rw [← hwt, hweq, h𝔉c₀]
  set S : Finset (Fin (genus X)) := Finset.univ.filter (fun j => x j ≠ a j) with hS_def
  have hSmem : ∀ {j}, j ∈ S ↔ x j ≠ a j := by intro j; simp [hS_def]
  obtain ⟨j₀, hj₀⟩ := hSne
  have hSne' : S.Nonempty := ⟨j₀, hSmem.mpr hj₀⟩
  set a' : (↥S : Type) → X := fun i => a i.1 with ha'_def
  set x' : (↥S : Type) → X := fun i => x i.1 with hx'_def
  have ha'inj : Function.Injective a' := fun i i' h => Subtype.ext (hainj h)
  have hVj : ∀ j, x j ∈ V j := fun j => ⟨w j, hwj j, rfl⟩
  have hx'inj : Function.Injective x' := by
    intro i i' h
    by_contra hne
    have h' : x (i : Fin (genus X)) = x (i' : Fin (genus X)) := h
    have hmem2 : x (i : Fin (genus X)) ∈ V (i' : Fin (genus X)) := by rw [h']; exact hVj i'.1
    exact (Set.disjoint_left.mp (hVdisj (Subtype.coe_ne_coe.mpr hne)) (hVj i.1)) hmem2
  have hax' : ∀ i i' : (↥S : Type), a' i ≠ x' i' := by
    intro i i' heq
    have heq' : a (i : Fin (genus X)) = x (i' : Fin (genus X)) := heq
    rcases eq_or_ne (i : Fin (genus X)) (i' : Fin (genus X)) with hii' | hii'
    · rw [hii'] at heq'
      exact (hSmem.mp i'.2) heq'.symm
    · have hmem2 : a (i : Fin (genus X)) ∈ V (i' : Fin (genus X)) := by rw [heq']; exact hVj i'.1
      exact (Set.disjoint_left.mp (hVdisj hii') (haV i.1)) hmem2
  set γ' : ∀ i : (↥S : Type), Path (a' i) (x' i) := fun i => σ i.1 with hγ'_def
  have hmemS : (fun k => ∑ i : (↥S : Type), pathIntegral (γ' i) (basis X k)) ∈ periodSubgroup X :=
      by
    have hSsum : ∀ k, ∑ i : (↥S : Type), pathIntegral (γ' i) (basis X k)
        = ∑ j ∈ S, pathIntegral (σ j) (basis X k) :=
      fun k => Finset.sum_coe_sort S (fun j => pathIntegral (σ j) (basis X k))
    have hcompl0 : ∀ k, ∑ j ∈ Sᶜ, pathIntegral (σ j) (basis X k) = 0 := by
      intro k
      apply Finset.sum_eq_zero
      intro j hj
      have hjnS : j ∉ S := Finset.mem_compl.mp hj
      rw [hSmem] at hjnS
      push Not at hjnS
      have hwj_eq : w j = c₀ j := by rw [← hexj j, hjnS]
      rw [hσint, hwj_eq, hgp0]
    have heqk : ∀ k, ∑ i : (↥S : Type), pathIntegral (γ' i) (basis X k) = t k := by
      intro k
      have hpartition : ∑ j ∈ S, pathIntegral (σ j) (basis X k)
          + ∑ j ∈ Sᶜ, pathIntegral (σ j) (basis X k) = ∑ j, pathIntegral (σ j) (basis X k) :=
        Finset.sum_add_sum_compl S _
      rw [hcompl0 k, add_zero] at hpartition
      rw [hSsum k, hpartition, hlin]
      exact congrFun hγ k
    have hteq : (fun k => ∑ i : (↥S : Type), pathIntegral (γ' i) (basis X k)) = t := funext heqk
    rw [hteq]
    exact htmem
  obtain ⟨F, hFne, hFordx, hForda, hFord0⟩ :=
    RS.Abel.exists_mero_of_periodVector_mem (hupgrade S) a' x' ha'inj hx'inj hax' γ' hmemS
  /- **Stage C.5–6**: the residue-theorem contradiction. -/
  set Θ : Fin (genus X) → MForm X := fun k => F • MForm.ofForm1 (basis X k) with hΘ_def
  set c : Fin (genus X) → ℂ := fun j =>
    RS.resAt (F.holoRepr ∘ ⇑(e j).symm) (c₀ j) with hc_def
  have hFordAll : ∀ j, F.ord (a j) = if x j = a j then 0 else -1 := by
    intro j
    by_cases hj : x j = a j
    · rw [if_pos hj]
      have hjnS : j ∉ S := fun hjS => (hSmem.mp hjS) hj
      have hij_ne : ∀ i : (↥S : Type), (i : Fin (genus X)) ≠ j := by
        intro i hij
        exact hjnS (by rw [← hij]; exact i.2)
      apply hFord0
      · intro i heq
        have heq' : a j = a (i : Fin (genus X)) := heq
        have hmem2 : a j ∈ V (i : Fin (genus X)) := by rw [heq']; exact haV i.1
        exact Set.disjoint_left.mp (hVdisj (hij_ne i).symm) (haV j) hmem2
      · intro i heq
        have heq' : a j = x (i : Fin (genus X)) := heq
        have hmem2 : a j ∈ V (i : Fin (genus X)) := by rw [heq']; exact hVj i.1
        exact Set.disjoint_left.mp (hVdisj (hij_ne i).symm) (haV j) hmem2
    · rw [if_neg hj]
      exact hForda ⟨j, hSmem.mpr hj⟩
  have hΘres : ∀ k j, (Θ k).resAt (a j) = A k j * c j :=
    resAt_twisted_eq he he_def hc₀_def hAij hFordAll
  have hcS : c j₀ ≠ 0 :=
    local_residue_ne_zero j₀ (by rw [hFordAll]; simp [hj₀])
  have hressum : ∀ k, ∀ x' ∉ (Finset.univ.image a : Set X), (Θ k).resAt x' = 0 :=
    resAt_twisted_eq_zero_off_base ha'_def hFordx hFord0
  have hsupp : ∀ k, Function.support (fun x => (Θ k).resAt x) ⊆
      (Finset.univ.image a : Set X) := by
    intro k y hy
    by_contra hcon
    exact hy (hressum k y hcon)
  have hsum0 : ∀ k, ∑ j, A k j * c j = 0 := by
    intro k
    have hthm := residueTheorem (Θ k) (hsupp k)
    rw [Finset.sum_image (fun j _ j' _ h => hainj h)] at hthm
    simp only [hΘres] at hthm
    exact hthm
  have hcne : c ≠ 0 := fun h => hcS (by rw [h]; rfl)
  have hex : ∃ v : Fin (genus X) → ℂ, v ≠ 0 ∧ Matrix.mulVec A v = 0 := by
    refine ⟨c, hcne, ?_⟩
    funext k
    change ∑ j, A k j * c j = 0
    exact hsum0 k
  exact hAdet (Matrix.exists_mulVec_eq_zero_iff.mp hex)

/-- **Discreteness discharge**: `genus X = 0` handled by the subsingleton argument; `genus X ≥ 1`
via `exists_isolating_nhds_periodSubgroup`. -/
theorem discreteTopology_periodSubgroup (hupgrade : DiscretenessHyp X) :
    DiscreteTopology (periodSubgroup X) := by
  by_cases hgen : genus X = 0
  · have hsub : Subsingleton (Fin (genus X) → ℂ) := by rw [hgen]; infer_instance
    have hsubsingle : Subsingleton (periodSubgroup X) :=
        ⟨fun a b => Subtype.ext (hsub.elim a.1 b.1)⟩
    rw [discreteTopology_iff_forall_isOpen]
    intro s
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨p, hp⟩
    · exact isOpen_empty
    · have hsu : s = Set.univ := Set.eq_univ_of_forall fun q => hsubsingle.elim q p ▸ hp
      rw [hsu]; exact isOpen_univ
  · have hg1 : 1 ≤ genus X := Nat.one_le_iff_ne_zero.mpr hgen
    obtain ⟨W, hWmem, hWiso⟩ := exists_isolating_nhds_periodSubgroup hg1 hupgrade
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hUopen : IsOpen ((Subtype.val : periodSubgroup X → Fin (genus X) → ℂ) ⁻¹' interior W) :=
      isOpen_interior.preimage continuous_subtype_val
    have hseteq : (Subtype.val : periodSubgroup X → Fin (genus X) → ℂ) ⁻¹' interior W
        = ({0} : Set (periodSubgroup X)) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro ht
        exact Subtype.ext (hWiso t.1 t.2 (interior_subset ht))
      · intro ht
        rw [ht, AddSubgroup.coe_zero]
        exact mem_interior_iff_mem_nhds.mpr hWmem
    rwa [hseteq] at hUopen

/-- The closure of `periodSubgroup X` is itself, once it is discrete: discreteness implies
closedness (`AddSubgroup.isClosed_of_discrete`). -/
theorem periodSubgroup_topologicalClosure_eq (hupgrade : DiscretenessHyp X) :
    (periodSubgroup X).topologicalClosure = periodSubgroup X := by
  have := discreteTopology_periodSubgroup hupgrade
  exact SetLike.coe_injective (AddSubgroup.isClosed_of_discrete (H := periodSubgroup X)).closure_eq

/-- The gated `DiscreteTopology` instance for the closure, the shape `jacobian-construction`'s
ledger needs directly. -/
theorem discreteTopology_periodSubgroup_topologicalClosure (hupgrade : DiscretenessHyp X) :
    DiscreteTopology (periodSubgroup X).topologicalClosure := by
  rw [periodSubgroup_topologicalClosure_eq hupgrade]
  exact discreteTopology_periodSubgroup hupgrade

end RS

end
