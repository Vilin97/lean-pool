/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.AreaPairing
import LeanPool.JacobianDiffgeo.PlanarStokes.CompactSupport
import LeanPool.JacobianDiffgeo.TailDuality
import LeanPool.JacobianDiffgeo.LaurentTail
import LeanPool.JacobianDiffgeo.DolbeaultComparison

/-!
# abel-theorem: the Serre functional (design §4.3, routing decision #2's "honest integration atom")

Unit: abel-theorem. Namespace `RS.Abel`.

The three analytic/linear-algebraic properties of the area pairing `pairing PU σ θ` built in
`AreaPairing.lean`:

* **`pairing_dbar_eq_zero`** (Forster 19.6's Stokes half, PoU-globalized): `dbar`-exact
  `(0,1)`-forms pair to zero against every holomorphic `1`-form. The proof is the compact-surface
  Stokes argument run entirely through the planar Atom 1 (`integral_wirtingerDbar_eq_zero`):
  per PoU chart, `ψᵢ dbaru θᵢ = dbar(ψᵢ u θᵢ) - dbarψᵢ · u θᵢ`, the first integral dies by
  compact-support Stokes, and the leftover `∑ᵢ ∫ dbarψᵢ · u θ` dies after inserting `∑ⱼ ψⱼ = 1`,
  transporting each `(i,j)` term into chart `j` by the `(1,1)`-density change of variables
  (`integral_eq_integral_transition` — the `conj (deriv τ) · deriv τ = normSq (deriv τ)`
  cancellation against `Form01.compat`-type `conj`-factors and `coeffIn_trans`), and summing
  `∑ᵢ dbarψᵢ = dbar1 = 0` in chart `j`.
* **`conjForm`/`pairingDual_injective`** (Forster 19.5's positivity, localized): the conjugate
  `(0,1)`-form `theta-bar` of a holomorphic `1`-form pairs against `θ` to
  `∑ᵢ ∫ ψᵢ |θᵢ|² ≥ 0`, zero only
  for `θ = 0` — so `θ ↦ pairing · θ` is an INJECTION `Form1 X ↪ Dual (H01 X)`. No Hodge theory:
  this is pointwise positivity of the integrand plus `volume`'s open-positivity.
* **`exists_dbar_of_forall_pairing_eq_zero`** — the integral-pairing Dolbeault bridge: a
  `(0,1)`-form pairing to zero against EVERY holomorphic `1`-form is `dbar`-exact. Gated (exactly
  like `DolbeaultBridge.lean`) only on `serre-duality-tails`'s remaining external fact
  `Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))`: that surjectivity forces
  `finrank (H01 X) = genus X` (`finrank_H01_eq_genus`, via `dolbeaultEquiv` +
  `H1Tail.equivOfSurjective` + `h1T_zero_eq_genus`), whence the positivity injection is onto
  `Dual (H01 X)` by dimension count and `Module.forall_dual_apply_eq_zero_iff` closes.

This gives, for the Abel discharge, a bridge whose hypothesis (`∫∫ η ∧ θ = 0` for all `θ`) is
checkable against the weak-solution packaging (`LogPiece.lean`/`UpgradeDischarge.lean`) by
concrete planar Stokes/residue computations — the shape `DolbeaultBridge.lean`'s abstract
residue-pairing hypothesis does not directly offer.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory


noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The Stokes vanishing: auxiliary integrands

Throughout, for a fixed `u : SmoothC X` and `θ : Form1 X`:
`stokesA PU u θ i` is `dbarψᵢ · u · θ` read in chart `i`; `stokesB PU u θ i j` is its
`ψⱼ`-weighted piece supported on the `(i,j)` overlap, still in chart `i`; `stokesC PU u θ i j`
is the same piece transported to chart `j`. -/

private def stokesA (PU : SurfPoU X) (u : RS.SmoothC X) (θ : RS.Form1 X) (i : Fin PU.n) :
    ℂ → ℂ :=
  ((PU.chart i).target).indicator (fun z =>
    RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
      ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z))

private def stokesB (PU : SurfPoU X) (u : RS.SmoothC X) (θ : RS.Form1 X) (i j : Fin PU.n) :
    ℂ → ℂ :=
  (⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source)).indicator (fun z =>
    PU.ψ j ((PU.chart i).symm z) • (RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
      ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)))

private def stokesC (PU : SurfPoU X) (u : RS.SmoothC X) (θ : RS.Form1 X) (i j : Fin PU.n) :
    ℂ → ℂ :=
  (⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source)).indicator (fun w =>
    PU.ψ j ((PU.chart j).symm w) • (RS.wirtingerDbar (PU.psiC i (PU.chart j)) w *
      ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)))

section StokesLemmas

variable (PU : SurfPoU X) (u : RS.SmoothC X) (θ : RS.Form1 X)

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Membership bookkeeping: reading membership in an overlap image off the source point,
version where the imaging chart is the FIRST overlap component. -/
private theorem mem_image_iff_fst (i j : Fin PU.n) {z : ℂ} (hz : z ∈ (PU.chart i).target) :
    (PU.chart i).symm z ∈ (PU.chart j).source ↔
      z ∈ ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) := by
  constructor
  · intro hj
    exact ⟨(PU.chart i).symm z, ⟨(PU.chart i).map_target hz, hj⟩, (PU.chart i).right_inv hz⟩
  · rintro ⟨q, hq, rfl⟩
    rw [(PU.chart i).left_inv hq.1]
    exact hq.2

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Version where the imaging chart is the SECOND overlap component. -/
private theorem mem_image_iff_snd (i j : Fin PU.n) {w : ℂ} (hw : w ∈ (PU.chart j).target) :
    (PU.chart j).symm w ∈ (PU.chart i).source ↔
      w ∈ ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) := by
  constructor
  · intro hi
    exact ⟨(PU.chart j).symm w, ⟨hi, (PU.chart j).map_target hw⟩, (PU.chart j).right_inv hw⟩
  · rintro ⟨q, hq, rfl⟩
    rw [(PU.chart j).left_inv hq.2]
    exact hq.1

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem image_overlap_subset (i j : Fin PU.n) :
    ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) ⊆ (PU.chart i).target := by
  rintro z ⟨q, hq, rfl⟩
  exact (PU.chart i).map_source hq.1

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem image_overlap_subset' (i j : Fin PU.n) :
    ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) ⊆ (PU.chart j).target := by
  rintro w ⟨q, hq, rfl⟩
  exact (PU.chart j).map_source hq.2

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem isOpen_image_overlap (i j : Fin PU.n) :
    IsOpen (⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source)) :=
  (PU.chart i).isOpen_image_of_subset_source
    ((PU.chart i).open_source.inter (PU.chart j).open_source) inter_subset_left

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem isOpen_image_overlap' (i j : Fin PU.n) :
    IsOpen (⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source)) :=
  (PU.chart j).isOpen_image_of_subset_source
    ((PU.chart i).open_source.inter (PU.chart j).open_source) inter_subset_right

omit [T2Space X] [CompactSpace X] in
/-- `stokesA`'s core vanishes off the compact carrier `PU.K i`. -/
private theorem stokesA_core_zero (i : Fin PU.n) : ∀ z ∈ (PU.chart i).target, z ∉ PU.K i →
    RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
      ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z) = 0 := by
  intro z hz hzK
  have hy : (PU.chart i).symm z ∉ tsupport (PU.ψ i) := by
    intro hmem
    exact hzK ⟨(PU.chart i).symm z, hmem, (PU.chart i).right_inv hz⟩
  rw [PU.wirtingerDbar_psiC_eq_zero i hz hy, zero_mul]

omit [T2Space X] [CompactSpace X] in
private theorem stokesA_core_contDiffOn (i : Fin PU.n) : ContDiffOn ℝ ∞
    (fun z => RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
      ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)) (PU.chart i).target :=
  (RS.contDiffOn_wirtingerDbar _ (PU.chart i).open_target
    (PU.contDiffOn_psiC i (PU.chart_mem_maximalAtlas i))).mul
    ((u.contDiffOn_comp_chartAt_symm (PU.pt i)).mul
      (contDiffOn_coeffIn θ (PU.chart_mem_maximalAtlas i)))

omit [T2Space X] in
private theorem integrable_stokesA (i : Fin PU.n) : Integrable (stokesA PU u θ i) :=
  integrable_indicator_of_eq_zero_off (PU.chart i).open_target (PU.isCompact_K i)
    (PU.K_subset_target i) (stokesA_core_contDiffOn PU u θ i) (stokesA_core_zero PU u θ i)

/-- The joint compact carrier of the `(i,j)` overlap pieces, imaged in chart `i`. -/
private def Kover (PU : SurfPoU X) (i j : Fin PU.n) : Set ℂ :=
  ⇑(PU.chart i) '' (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem isCompact_Kover (i j : Fin PU.n) : IsCompact (Kover PU i j) := by
  have hts : IsCompact (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j)) :=
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _)
      (Set.subset_univ _)).inter_right (isClosed_tsupport _)
  exact hts.image_of_continuousOn ((PU.chart i).continuousOn.mono
    (Set.inter_subset_left.trans (PU.tsupport_subset i)))

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem Kover_subset (i j : Fin PU.n) :
    Kover PU i j ⊆ ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) := by
  rintro z ⟨q, hq, rfl⟩
  exact ⟨q, ⟨PU.tsupport_subset i hq.1, PU.tsupport_subset j hq.2⟩, rfl⟩

omit [T2Space X] [CompactSpace X] in
private theorem stokesB_core_zero (i j : Fin PU.n) :
    ∀ z ∈ ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source), z ∉ Kover PU i j →
      PU.ψ j ((PU.chart i).symm z) • (RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
        ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)) = 0 := by
  intro z hz hzK
  have hzT : z ∈ (PU.chart i).target := image_overlap_subset PU i j hz
  have hyK : (PU.chart i).symm z ∉ tsupport (PU.ψ i) ∩ tsupport (PU.ψ j) := by
    intro hmem
    exact hzK ⟨(PU.chart i).symm z, hmem, (PU.chart i).right_inv hzT⟩
  by_cases hyj : (PU.chart i).symm z ∈ tsupport (PU.ψ j)
  · have hyi : (PU.chart i).symm z ∉ tsupport (PU.ψ i) := fun h => hyK ⟨h, hyj⟩
    rw [PU.wirtingerDbar_psiC_eq_zero i hzT hyi, zero_mul, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hyj, zero_smul]

omit [T2Space X] in
private theorem integrable_stokesB (i j : Fin PU.n) : Integrable (stokesB PU u θ i j) := by
  refine integrable_indicator_of_eq_zero_off (isOpen_image_overlap PU i j)
    (isCompact_Kover PU i j) (Kover_subset PU i j) ?_ (stokesB_core_zero PU u θ i j)
  have h1 : ContDiffOn ℝ ∞ (fun z => PU.ψ j ((PU.chart i).symm z))
      (⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source)) :=
    (contDiffOn_comp_symm_real (PU.contMDiff j) (PU.chart_mem_maximalAtlas i)).mono
      (image_overlap_subset PU i j)
  exact h1.smul ((stokesA_core_contDiffOn PU u θ i).mono (image_overlap_subset PU i j))

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The `stokesC` carrier, imaged in chart `j`. -/
private theorem Kover_subset' (i j : Fin PU.n) :
    ⇑(PU.chart j) '' (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j)) ⊆
      ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) :=
  Set.image_mono (fun _q hq => ⟨PU.tsupport_subset i hq.1, PU.tsupport_subset j hq.2⟩)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem isCompact_Kover' (i j : Fin PU.n) :
    IsCompact (⇑(PU.chart j) '' (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j))) := by
  have hts : IsCompact (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j)) :=
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _)
      (Set.subset_univ _)).inter_right (isClosed_tsupport _)
  exact hts.image_of_continuousOn ((PU.chart j).continuousOn.mono
    (Set.inter_subset_right.trans (PU.tsupport_subset j)))

omit [T2Space X] [CompactSpace X] in
private theorem stokesC_core_zero (i j : Fin PU.n) :
    ∀ w ∈ ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source),
      w ∉ ⇑(PU.chart j) '' (tsupport (PU.ψ i) ∩ tsupport (PU.ψ j)) →
      PU.ψ j ((PU.chart j).symm w) • (RS.wirtingerDbar (PU.psiC i (PU.chart j)) w *
        ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)) = 0 := by
  intro w hw hwK
  have hwT : w ∈ (PU.chart j).target := image_overlap_subset' PU i j hw
  have hyK : (PU.chart j).symm w ∉ tsupport (PU.ψ i) ∩ tsupport (PU.ψ j) := by
    intro hmem
    exact hwK ⟨(PU.chart j).symm w, hmem, (PU.chart j).right_inv hwT⟩
  by_cases hyj : (PU.chart j).symm w ∈ tsupport (PU.ψ j)
  · have hyi : (PU.chart j).symm w ∉ tsupport (PU.ψ i) := fun h => hyK ⟨h, hyj⟩
    rw [PU.wirtingerDbar_psiC_eq_zero i hwT hyi, zero_mul, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hyj, zero_smul]

omit [T2Space X] [CompactSpace X] in
private theorem stokesC_core_contDiffOn (i j : Fin PU.n) : ContDiffOn ℝ ∞
    (fun w => PU.ψ j ((PU.chart j).symm w) • (RS.wirtingerDbar (PU.psiC i (PU.chart j)) w *
      ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)))
    (⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source)) := by
  have hsub := image_overlap_subset' PU i j
  have h1 : ContDiffOn ℝ ∞ (fun w => PU.ψ j ((PU.chart j).symm w))
      (⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source)) :=
    (contDiffOn_comp_symm_real (PU.contMDiff j) (PU.chart_mem_maximalAtlas j)).mono hsub
  exact h1.smul (((RS.contDiffOn_wirtingerDbar _ (PU.chart j).open_target
    (PU.contDiffOn_psiC i (PU.chart_mem_maximalAtlas j))).mul
    ((u.contDiffOn_comp_chartAt_symm (PU.pt j)).mul
      (contDiffOn_coeffIn θ (PU.chart_mem_maximalAtlas j)))).mono hsub)

omit [T2Space X] in
private theorem integrable_stokesC (i j : Fin PU.n) : Integrable (stokesC PU u θ i j) :=
  integrable_indicator_of_eq_zero_off (isOpen_image_overlap' PU i j) (isCompact_Kover' PU i j)
    (Kover_subset' PU i j) (stokesC_core_contDiffOn PU u θ i j) (stokesC_core_zero PU u θ i j)

omit [T2Space X] in
/-- **Step 1** (per-chart planar Stokes): `∫ ψᵢ dbaru θᵢ = -∫ dbarψᵢ u θᵢ`. -/
private theorem stokes_step1 (i : Fin PU.n) :
    ∫ z : ℂ, pairingTerm PU (RS.dbar u) θ i z = -∫ z : ℂ, stokesA PU u θ i z := by
  set hcore : ℂ → ℂ := fun z =>
    PU.ψ i ((PU.chart i).symm z) • ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)
    with hhcore_def
  set hfun : ℂ → ℂ := ((PU.chart i).target).indicator hcore with hhfun_def
  have hhcore0 : ∀ z ∈ (PU.chart i).target, z ∉ PU.K i → hcore z = 0 := by
    intro z hz hzK
    rw [hhcore_def]
    dsimp only
    rw [PU.psi_symm_eq_zero i hz hzK, zero_smul]
  have hhcore_cd : ContDiffOn ℝ ∞ hcore (PU.chart i).target := by
    have h1 : ContDiffOn ℝ ∞ (fun z => PU.ψ i ((PU.chart i).symm z)) (PU.chart i).target :=
      contDiffOn_comp_symm_real (PU.contMDiff i) (PU.chart_mem_maximalAtlas i)
    exact h1.smul ((u.contDiffOn_comp_chartAt_symm (PU.pt i)).mul
      (contDiffOn_coeffIn θ (PU.chart_mem_maximalAtlas i)))
  have hhsmooth : ContDiff ℝ ∞ hfun :=
    contDiff_indicator_of_eq_zero_off (PU.chart i).open_target (PU.isCompact_K i)
      (PU.K_subset_target i) hhcore_cd hhcore0
  have hhcs : HasCompactSupport hfun :=
    hasCompactSupport_indicator_of_eq_zero_off (PU.isCompact_K i) hhcore0
  have hpoint : ∀ z, RS.wirtingerDbar hfun z
      = stokesA PU u θ i z + pairingTerm PU (RS.dbar u) θ i z := by
    intro z
    by_cases hz : z ∈ (PU.chart i).target
    · have hev : hfun =ᶠ[nhds z] (fun w => PU.psiC i (PU.chart i) w *
          ((⇑u ∘ ⇑(PU.chart i).symm) w * RS.coeffIn (PU.chart i) θ w)) := by
        filter_upwards [(PU.chart i).open_target.mem_nhds hz] with w hw
        rw [hhfun_def, Set.indicator_of_mem hw, hhcore_def]
        dsimp only
        rw [Complex.real_smul]
        rfl
      have hucd : DifferentiableAt ℝ (⇑u ∘ ⇑(PU.chart i).symm) z :=
        u.differentiableAt_comp_chartAt_symm _ hz
      have hθcd : DifferentiableAt ℂ (RS.coeffIn (PU.chart i) θ) z :=
        (θ.analyticAt_coeffIn (PU.chart_mem_maximalAtlas i) hz).differentiableAt
      have hmuld : DifferentiableAt ℝ
          (fun w => (⇑u ∘ ⇑(PU.chart i).symm) w * RS.coeffIn (PU.chart i) θ w) z :=
        hucd.mul (hθcd.restrictScalars ℝ)
      have hψd : DifferentiableAt ℝ (PU.psiC i (PU.chart i)) z :=
        PU.differentiableAt_psiC i (PU.chart_mem_maximalAtlas i) hz
      rw [RS.wirtingerDbar_congr_nhds _ _ z hev, RS.wirtingerDbar_mul hψd hmuld,
        RS.wirtingerDbar_mul_of_differentiableAt hucd hθcd]
      have hAz : stokesA PU u θ i z = RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
          ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z) := by
        rw [stokesA, Set.indicator_of_mem hz]
      have hPz : pairingTerm PU (RS.dbar u) θ i z = PU.ψ i ((PU.chart i).symm z) •
          (RS.wirtingerDbar (⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z) := by
        rw [pairingTerm, Set.indicator_of_mem hz, RS.coeffAt_dbar u (PU.pt i) hz]
      rw [hAz, hPz, Complex.real_smul]
      have hψCz : PU.psiC i (PU.chart i) z = ((PU.ψ i ((PU.chart i).symm z) : ℝ) : ℂ) := rfl
      rw [hψCz]
    · have hzK : z ∉ PU.K i := fun h => hz (PU.K_subset_target i h)
      have hev : hfun =ᶠ[nhds z] 0 :=
        indicator_eventuallyEq_zero_of_notMem (PU.isCompact_K i) hhcore0 hzK
      rw [RS.wirtingerDbar_congr_nhds _ _ z hev, stokesA, Set.indicator_of_notMem hz,
        pairingTerm, Set.indicator_of_notMem hz]
      simpa [Pi.zero_def] using RS.wirtingerDbar_const z 0
  have hstokes : ∫ z : ℂ, RS.wirtingerDbar hfun z = 0 :=
    RS.integral_wirtingerDbar_eq_zero isOpen_univ
      ((hhsmooth.of_le (by norm_num)).contDiffOn) hhcs (Set.subset_univ _)
  have hsplit : ∫ z : ℂ, RS.wirtingerDbar hfun z
      = (∫ z : ℂ, stokesA PU u θ i z) + ∫ z : ℂ, pairingTerm PU (RS.dbar u) θ i z := by
    rw [show (fun z => RS.wirtingerDbar hfun z)
        = fun z => stokesA PU u θ i z + pairingTerm PU (RS.dbar u) θ i z from funext hpoint]
    exact MeasureTheory.integral_add (integrable_stokesA PU u θ i)
      (integrable_pairingTerm PU (RS.dbar u) θ i)
  rw [hsplit] at hstokes
  linear_combination hstokes

omit [T2Space X] in
/-- **Step 2** (PoU insertion): `∫ stokesA i = ∑ⱼ ∫ stokesB i j`. -/
private theorem stokes_step2 (i : Fin PU.n) :
    ∫ z : ℂ, stokesA PU u θ i z = ∑ j, ∫ z : ℂ, stokesB PU u θ i j z := by
  have hpoint : ∀ z, stokesA PU u θ i z = ∑ j, stokesB PU u θ i j z := by
    intro z
    by_cases hz : z ∈ (PU.chart i).target
    · have huniform : ∀ j, stokesB PU u θ i j z = PU.ψ j ((PU.chart i).symm z) •
          (RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
            ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)) := by
        intro j
        by_cases hyj : (PU.chart i).symm z ∈ (PU.chart j).source
        · rw [stokesB, Set.indicator_of_mem ((mem_image_iff_fst PU i j hz).mp hyj)]
        · have hzS : z ∉ ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) :=
            fun h => hyj ((mem_image_iff_fst PU i j hz).mpr h)
          rw [stokesB, Set.indicator_of_notMem hzS,
            image_eq_zero_of_notMem_tsupport (fun hmem => hyj (PU.tsupport_subset j hmem)),
            zero_smul]
      rw [stokesA, Set.indicator_of_mem hz]
      calc RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
            ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)
          = (∑ j, PU.ψ j ((PU.chart i).symm z)) •
            (RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
              ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)) := by
            rw [PU.sum_eq_one ((PU.chart i).symm z), one_smul]
        _ = ∑ j, PU.ψ j ((PU.chart i).symm z) •
            (RS.wirtingerDbar (PU.psiC i (PU.chart i)) z *
              ((⇑u ∘ ⇑(PU.chart i).symm) z * RS.coeffIn (PU.chart i) θ z)) :=
            Finset.sum_smul
        _ = ∑ j, stokesB PU u θ i j z := Finset.sum_congr rfl (fun j _ => (huniform j).symm)
    · rw [stokesA, Set.indicator_of_notMem hz]
      refine (Finset.sum_eq_zero (fun j _ => ?_)).symm
      have hzS : z ∉ ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) :=
        fun h => hz (image_overlap_subset PU i j h)
      rw [stokesB, Set.indicator_of_notMem hzS]
  rw [show (fun z => stokesA PU u θ i z) = fun z => ∑ j, stokesB PU u θ i j z from
    funext hpoint]
  exact MeasureTheory.integral_finsetSum _ (fun j _ => integrable_stokesB PU u θ i j)

omit [T2Space X] [CompactSpace X] in
/-- **Step 3** (change of variables): `∫ stokesB i j = ∫ stokesC i j`. -/
private theorem stokes_step3 (i j : Fin PU.n) :
    ∫ z : ℂ, stokesB PU u θ i j z = ∫ w : ℂ, stokesC PU u θ i j w := by
  refine integral_eq_integral_transition (PU.chart_mem_maximalAtlas i)
    (PU.chart_mem_maximalAtlas j) (fun z hz => ?_) (fun w hw => ?_) (fun w hw => ?_)
  · rw [stokesB, Set.indicator_of_notMem hz]
  · rw [stokesC, Set.indicator_of_notMem hw]
  · -- the transported identity on the overlap image in chart `j`
    obtain ⟨q, hq, rfl⟩ := hw
    have hwmem : (PU.chart j) q ∈
        ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) := ⟨q, hq, rfl⟩
    have hwT : (PU.chart j) q ∈ (PU.chart j).target := (PU.chart j).map_source hq.2
    have hyq : (PU.chart j).symm ((PU.chart j) q) = q := (PU.chart j).left_inv hq.2
    set τ : ℂ → ℂ := ⇑(PU.chart i) ∘ ⇑(PU.chart j).symm with hτ_def
    have hτw : τ ((PU.chart j) q) = (PU.chart i) q := by
      rw [hτ_def]
      simp only [Function.comp_apply, hyq]
    have hτmem : τ ((PU.chart j) q) ∈
        ⇑(PU.chart i) '' ((PU.chart i).source ∩ (PU.chart j).source) := by
      rw [hτw]; exact ⟨q, hq, rfl⟩
    have hτT : τ ((PU.chart j) q) ∈ (PU.chart i).target := image_overlap_subset PU i j hτmem
    have hτdiff : DifferentiableAt ℂ τ ((PU.chart j) q) :=
      (RS.analyticAt_trans (PU.chart_mem_maximalAtlas i) (PU.chart_mem_maximalAtlas j)
        hwT (by rw [hyq]; exact hq.1)).differentiableAt
    -- T1: the dbar-chain rule on the transported partition function
    have hT1 : RS.wirtingerDbar (PU.psiC i (PU.chart j)) ((PU.chart j) q)
        = (starRingEnd ℂ) (deriv τ ((PU.chart j) q)) *
          RS.wirtingerDbar (PU.psiC i (PU.chart i)) (τ ((PU.chart j) q)) := by
      have hev : PU.psiC i (PU.chart j) =ᶠ[nhds ((PU.chart j) q)]
          (PU.psiC i (PU.chart i)) ∘ τ := by
        filter_upwards [(isOpen_image_overlap' PU i j).mem_nhds hwmem] with w' hw'
        obtain ⟨q', hq', rfl⟩ := hw'
        have h1 : (PU.chart j).symm ((PU.chart j) q') = q' := (PU.chart j).left_inv hq'.2
        simp only [SurfPoU.psiC, Function.comp_apply, hτ_def, h1,
          (PU.chart i).left_inv hq'.1]
      have hFd : DifferentiableAt ℝ (PU.psiC i (PU.chart i)) (τ ((PU.chart j) q)) :=
        PU.differentiableAt_psiC i (PU.chart_mem_maximalAtlas i) hτT
      rw [RS.wirtingerDbar_congr_nhds _ _ _ hev,
        RS.wirtingerDbar_comp_differentiableAt (PU.psiC i (PU.chart i)) _ hFd hτdiff]
    -- T2: the coefficient transition rule
    have hT2 : RS.coeffIn (PU.chart j) θ ((PU.chart j) q)
        = deriv τ ((PU.chart j) q) *
          RS.coeffIn (PU.chart i) θ (τ ((PU.chart j) q)) := by
      have := RS.coeffIn_trans (PU.chart_mem_maximalAtlas i) (PU.chart_mem_maximalAtlas j) θ
        (z := (PU.chart j) q) hwmem
      rw [this, hτ_def]
      simp only [Function.comp_apply]
    -- assemble
    have hsymm_i : (PU.chart i).symm (τ ((PU.chart j) q)) = q := by
      rw [hτw]; exact (PU.chart i).left_inv hq.1
    rw [hyq, ← hτw, stokesC, Set.indicator_of_mem hwmem, stokesB,
      Set.indicator_of_mem hτmem]
    simp only [Function.comp_apply, hyq, hsymm_i]
    rw [hT1, hT2, Complex.real_smul, Complex.real_smul, Complex.real_smul,
      ← Complex.mul_conj (deriv τ ((PU.chart j) q))]
    ring

omit [T2Space X] [CompactSpace X] in
/-- **Step 4** (the `∑ᵢ dbarψᵢ = 0` cancellation in chart `j`): `∑ᵢ stokesC i j ≡ 0`. -/
private theorem stokes_step4 (j : Fin PU.n) (w : ℂ) :
    ∑ i, stokesC PU u θ i j w = 0 := by
  by_cases hw : w ∈ (PU.chart j).target
  · have huniform : ∀ i, stokesC PU u θ i j w = PU.ψ j ((PU.chart j).symm w) •
        (RS.wirtingerDbar (PU.psiC i (PU.chart j)) w *
          ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)) := by
      intro i
      by_cases hyi : (PU.chart j).symm w ∈ (PU.chart i).source
      · rw [stokesC, Set.indicator_of_mem ((mem_image_iff_snd PU i j hw).mp hyi)]
      · have hwS : w ∉ ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) :=
          fun h => hyi ((mem_image_iff_snd PU i j hw).mpr h)
        rw [stokesC, Set.indicator_of_notMem hwS,
          PU.wirtingerDbar_psiC_eq_zero i hw
            (fun hmem => hyi (PU.tsupport_subset i hmem)),
          zero_mul, smul_zero]
    have hdiffs : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (PU.psiC i (PU.chart j)) w := by
      intro i _
      by_cases hyi : (PU.chart j).symm w ∈ tsupport (PU.ψ i)
      · exact PU.differentiableAt_psiC i (PU.chart_mem_maximalAtlas j) hw
      · exact ((PU.psiC_eventuallyEq_zero i hw hyi).differentiableAt_iff).mpr
          (differentiableAt_const 0)
    have hsum_dbar : ∑ i, RS.wirtingerDbar (PU.psiC i (PU.chart j)) w = 0 := by
      rw [← wirtingerDbar_finset_sum Finset.univ hdiffs,
        RS.wirtingerDbar_congr_nhds _ _ w (PU.sum_psiC_eventuallyEq_one hw)]
      exact RS.wirtingerDbar_const w 1
    calc ∑ i, stokesC PU u θ i j w
        = ∑ i, PU.ψ j ((PU.chart j).symm w) •
          (RS.wirtingerDbar (PU.psiC i (PU.chart j)) w *
            ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)) :=
          Finset.sum_congr rfl (fun i _ => huniform i)
      _ = PU.ψ j ((PU.chart j).symm w) •
          ((∑ i, RS.wirtingerDbar (PU.psiC i (PU.chart j)) w) *
            ((⇑u ∘ ⇑(PU.chart j).symm) w * RS.coeffIn (PU.chart j) θ w)) := by
          rw [← Finset.smul_sum, ← Finset.sum_mul]
      _ = 0 := by rw [hsum_dbar, zero_mul, smul_zero]
  · refine Finset.sum_eq_zero (fun i _ => ?_)
    have hwS : w ∉ ⇑(PU.chart j) '' ((PU.chart i).source ∩ (PU.chart j).source) :=
      fun h => hw (image_overlap_subset' PU i j h)
    rw [stokesC, Set.indicator_of_notMem hwS]

end StokesLemmas

omit [T2Space X] in
/-- **The compact-surface Stokes vanishing** (Forster 19.6's exactness half): for every global
smooth function `u` and holomorphic `1`-form `θ`, `∫∫_X dbaru ∧ θ = 0`. Fully unconditional. -/
theorem pairing_dbar_eq_zero (PU : SurfPoU X) (u : RS.SmoothC X) (θ : RS.Form1 X) :
    pairing PU (RS.dbar u) θ = 0 := by
  rw [pairing]
  calc ∑ i, ∫ z : ℂ, pairingTerm PU (RS.dbar u) θ i z
      = ∑ i, -∫ z : ℂ, stokesA PU u θ i z :=
        Finset.sum_congr rfl (fun i _ => stokes_step1 PU u θ i)
    _ = -∑ i, ∑ j, ∫ z : ℂ, stokesB PU u θ i j z := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [stokes_step2 PU u θ i])
    _ = -∑ i, ∑ j, ∫ w : ℂ, stokesC PU u θ i j w := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun j _ => stokes_step3 PU u θ i j))
    _ = -∑ j, ∑ i, ∫ w : ℂ, stokesC PU u θ i j w := by rw [Finset.sum_comm]
    _ = 0 := by
        rw [neg_eq_zero]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [← MeasureTheory.integral_finsetSum _
          (fun i _ => integrable_stokesC PU u θ i j)]
        rw [show (fun w => ∑ i, stokesC PU u θ i j w) = fun _ => (0 : ℂ) from
          funext (fun w => stokes_step4 PU u θ j w)]
        exact MeasureTheory.integral_zero ℂ ℂ

/-! ## The conjugate `(0,1)`-form and positivity -/

/-- The conjugate `(0,1)`-form `theta-bar` of a holomorphic `1`-form: chart coefficients
`conj (coeffIn e θ)`. The `Form01.compat` law is the conjugate of `coeffIn_trans`. -/
def conjForm (θ : RS.Form1 X) : RS.Form01 X where
  coeffAt x := ((chartAt ℂ x).target).indicator
    (fun z => (starRingEnd ℂ) (RS.coeffIn (chartAt ℂ x) θ z))
  coeffAt_zero_off x z hz := Set.indicator_of_notMem hz _
  contDiffOn_coeffAt x := by
    have h1 : ContDiffOn ℝ ∞
        (⇑Complex.conjCLE ∘ fun z => RS.coeffIn (chartAt ℂ x) θ z) (chartAt ℂ x).target :=
      Complex.conjCLE.contDiff.comp_contDiffOn
        (contDiffOn_coeffIn θ (IsManifold.chart_mem_maximalAtlas x))
    refine ContDiffOn.congr (ContDiffOn.congr h1 (fun z hz => ?_))
      (fun z hz => Set.indicator_of_mem hz _)
    simp []
  compat x y z hz := by
    have hzT : z ∈ (chartAt ℂ y).target := by
      rcases hz with ⟨q, hq, rfl⟩
      exact (chartAt ℂ y).map_source hq.2
    have hxT : chartAt ℂ x ((chartAt ℂ y).symm z) ∈ (chartAt ℂ x).target := by
      rcases hz with ⟨q, hq, rfl⟩
      rw [(chartAt ℂ y).left_inv hq.2]
      exact (chartAt ℂ x).map_source hq.1
    rw [Set.indicator_of_mem hzT, Set.indicator_of_mem hxT,
      RS.coeffIn_trans (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y) θ hz, map_mul]

omit [T2Space X] [CompactSpace X] in
/-- The chart coefficient of the conjugate form. -/
theorem conjForm_coeffAt (θ : RS.Form1 X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (conjForm θ).coeffAt x z = (starRingEnd ℂ) (RS.coeffIn (chartAt ℂ x) θ z) := by
  change ((chartAt ℂ x).target).indicator
    (fun z => (starRingEnd ℂ) (RS.coeffIn (chartAt ℂ x) θ z)) z = _
  exact Set.indicator_of_mem hz _

omit [T2Space X] in
/-- The pairing of `theta-bar` against `θ` is the (complexified) integral of the nonnegative density
`∑ᵢ ψᵢ |θᵢ|²`; if it vanishes, `θ = 0`. -/
theorem eq_zero_of_pairing_conjForm_eq_zero (PU : SurfPoU X) (θ : RS.Form1 X)
    (h : pairing PU (conjForm θ) θ = 0) : θ = 0 := by
  classical
  -- the real densities
  set ρ : Fin PU.n → ℂ → ℝ := fun i => ((PU.chart i).target).indicator
    (fun z => PU.ψ i ((PU.chart i).symm z) * Complex.normSq (RS.coeffIn (PU.chart i) θ z))
    with hρ_def
  have hρ0 : ∀ i, ∀ z ∈ (PU.chart i).target, z ∉ PU.K i →
      PU.ψ i ((PU.chart i).symm z) * Complex.normSq (RS.coeffIn (PU.chart i) θ z) = 0 := by
    intro i z hz hzK
    rw [PU.psi_symm_eq_zero i hz hzK, zero_mul]
  have hρ_cd : ∀ i, ContDiffOn ℝ ∞
      (fun z => PU.ψ i ((PU.chart i).symm z) *
        Complex.normSq (RS.coeffIn (PU.chart i) θ z)) (PU.chart i).target := by
    intro i
    have hθc := contDiffOn_coeffIn θ (PU.chart_mem_maximalAtlas i)
    have hre : ContDiffOn ℝ ∞ (fun z => (RS.coeffIn (PU.chart i) θ z).re)
        (PU.chart i).target := Complex.reCLM.contDiff.comp_contDiffOn hθc
    have him : ContDiffOn ℝ ∞ (fun z => (RS.coeffIn (PU.chart i) θ z).im)
        (PU.chart i).target := Complex.imCLM.contDiff.comp_contDiffOn hθc
    have hns : ContDiffOn ℝ ∞ (fun z => Complex.normSq (RS.coeffIn (PU.chart i) θ z))
        (PU.chart i).target := by
      refine ContDiffOn.congr ((hre.mul hre).add (him.mul him)) (fun z _ => ?_)
      rw [Complex.normSq_apply]
    exact (contDiffOn_comp_symm_real (PU.contMDiff i) (PU.chart_mem_maximalAtlas i)).mul hns
  have hρ_int : ∀ i, Integrable (ρ i) := fun i =>
    integrable_indicator_of_eq_zero_off (PU.chart i).open_target (PU.isCompact_K i)
      (PU.K_subset_target i) (hρ_cd i) (hρ0 i)
  have hρ_nonneg : ∀ i, ∀ z, 0 ≤ ρ i z := by
    intro i z
    rw [hρ_def]
    dsimp only
    by_cases hz : z ∈ (PU.chart i).target
    · rw [Set.indicator_of_mem hz]
      exact mul_nonneg (PU.nonneg i _) (Complex.normSq_nonneg _)
    · exact le_of_eq (Set.indicator_of_notMem hz _).symm
  -- the pairing terms are exactly the complexified densities
  have hterm : ∀ i, ∀ z, pairingTerm PU (conjForm θ) θ i z = ((ρ i z : ℝ) : ℂ) := by
    intro i z
    by_cases hz : z ∈ (PU.chart i).target
    · rw [pairingTerm, Set.indicator_of_mem hz, hρ_def]
      dsimp only
      rw [Set.indicator_of_mem hz]
      have hcoe : (conjForm θ).coeffAt (PU.pt i) z
          = (starRingEnd ℂ) (RS.coeffIn (PU.chart i) θ z) :=
        conjForm_coeffAt θ (PU.pt i) hz
      rw [hcoe, Complex.real_smul]
      push_cast
      rw [← Complex.normSq_eq_conj_mul_self]
    · rw [pairingTerm, Set.indicator_of_notMem hz, hρ_def]
      dsimp only
      rw [Set.indicator_of_notMem hz, Complex.ofReal_zero]
  -- reduce the vanishing pairing to the vanishing of every real integral
  have hsum : ∑ i, ∫ z : ℂ, ρ i z = 0 := by
    have h1 : pairing PU (conjForm θ) θ = ((∑ i, ∫ z : ℂ, ρ i z : ℝ) : ℂ) := by
      rw [pairing, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (fun z => pairingTerm PU (conjForm θ) θ i z)
          = fun z => ((ρ i z : ℝ) : ℂ) from funext (hterm i)]
      exact integral_ofReal
    rw [h1] at h
    exact_mod_cast h
  have hzero : ∀ i, ∫ z : ℂ, ρ i z = 0 := by
    have hnn : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ ∫ z : ℂ, ρ i z := fun i _ =>
      MeasureTheory.integral_nonneg (hρ_nonneg i)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  -- continuous nonnegative functions with vanishing integral vanish identically
  have hρ_eq_zero : ∀ i, ∀ z, ρ i z = 0 := by
    intro i
    have hcont : Continuous (ρ i) :=
      (contDiff_indicator_of_eq_zero_off (PU.chart i).open_target (PU.isCompact_K i)
        (PU.K_subset_target i) (hρ_cd i) (hρ0 i)).continuous
    have hae : ρ i =ᵐ[volume] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg (hρ_nonneg i) (hρ_int i)).mp (hzero i)
    have heq := (Continuous.ae_eq_iff_eq (μ := (volume : Measure ℂ)) hcont
      continuous_const).mp hae
    intro z
    exact congrFun heq z
  -- read off pointwise vanishing of the coefficients
  refine RS.Form1.ext_coeffAt (fun x => ?_)
  rw [RS.coeffAt_zero]
  have hex : ∃ i, PU.ψ i x ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := PU.sum_eq_one x
    rw [Finset.sum_eq_zero (fun i _ => hall i)] at h1
    exact zero_ne_one h1
  obtain ⟨i, hi⟩ := hex
  have hxsrc : x ∈ (PU.chart i).source :=
    PU.tsupport_subset i (subset_tsupport _ (by simpa [Function.mem_support] using hi))
  have hxT : (PU.chart i) x ∈ (PU.chart i).target := (PU.chart i).map_source hxsrc
  have hval := hρ_eq_zero i ((PU.chart i) x)
  rw [hρ_def] at hval
  dsimp only at hval
  rw [Set.indicator_of_mem hxT, (PU.chart i).left_inv hxsrc] at hval
  have hns : Complex.normSq (RS.coeffIn (PU.chart i) θ ((PU.chart i) x)) = 0 := by
    rcases mul_eq_zero.mp hval with h1 | h2
    · exact absurd h1 hi
    · exact h2
  have hcoeff : RS.coeffIn (PU.chart i) θ ((PU.chart i) x) = 0 :=
    Complex.normSq_eq_zero.mp hns
  -- transport the vanishing to the preferred chart at `x`
  have hmem : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' ((PU.chart i).source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hxsrc, mem_chart_source ℂ x⟩, rfl⟩
  have htrans := RS.coeffIn_trans (PU.chart_mem_maximalAtlas i)
    (IsManifold.chart_mem_maximalAtlas x) θ hmem
  rw [RS.coeffAt, htrans, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), hcoeff, mul_zero]

/-! ## The pairing as a linear functional on `H01` and the injection into the dual -/

/-- The pairing against a fixed `θ`, as a linear functional on `(0,1)`-forms. -/
def pairingFunctional (PU : SurfPoU X) (θ : RS.Form1 X) : RS.Form01 X →ₗ[ℂ] ℂ where
  toFun σ := pairing PU σ θ
  map_add' σ σ' := pairing_add_left PU σ σ' θ
  map_smul' c σ := pairing_smul_left PU c σ θ

/-- The pairing descends to the Dolbeault space `H01 X` (by `pairing_dbar_eq_zero`). -/
def pairingH01 (PU : SurfPoU X) (θ : RS.Form1 X) : RS.H01 X →ₗ[ℂ] ℂ :=
  Submodule.liftQ (LinearMap.range (RS.dbar (X := X))) (pairingFunctional PU θ) (by
    rintro _ ⟨u, rfl⟩
    exact pairing_dbar_eq_zero PU u θ)

omit [T2Space X] in
@[simp] theorem pairingH01_mk (PU : SurfPoU X) (θ : RS.Form1 X) (σ : RS.Form01 X) :
    pairingH01 PU θ (RS.H01.mk σ) = pairing PU σ θ := rfl

/-- The Serre functional `θ ↦ ∫∫ · ∧ θ`, as a linear map into the dual of `H01 X`. -/
def pairingDual (PU : SurfPoU X) : RS.Form1 X →ₗ[ℂ] Module.Dual ℂ (RS.H01 X) where
  toFun θ := pairingH01 PU θ
  map_add' θ θ' := by
    refine LinearMap.ext (fun ξ => ?_)
    obtain ⟨σ, rfl⟩ := RS.H01.mk_surjective ξ
    simp only [pairingH01_mk, LinearMap.add_apply]
    exact pairing_add_right PU σ θ θ'
  map_smul' c θ := by
    refine LinearMap.ext (fun ξ => ?_)
    obtain ⟨σ, rfl⟩ := RS.H01.mk_surjective ξ
    simp only [pairingH01_mk, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact pairing_smul_right PU c σ θ

omit [T2Space X] in
/-- **Positivity injection** (Forster 19.5-19.6, Hodge-free): the Serre functional is injective
on holomorphic `1`-forms. Fully unconditional. -/
theorem pairingDual_injective (PU : SurfPoU X) : Function.Injective (pairingDual PU) := by
  rw [injective_iff_map_eq_zero]
  intro θ hθ
  refine eq_zero_of_pairing_conjForm_eq_zero PU θ ?_
  have happ := congrArg (fun φ => φ (RS.H01.mk (conjForm θ))) hθ
  simpa [pairingDual, pairingH01_mk] using happ

/-! ## The gated dimension count and the integral-pairing bridge -/

variable [ConnectedSpace X] [DecidableEq X]

/-- Gated on `serre-duality-tails`'s remaining external fact, the Dolbeault space has dimension
exactly `genus X` (`≥` is the unconditional tail injection; `≤` is the gate). -/
theorem finrank_H01_eq_genus
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))) :
    Module.finrank ℂ (RS.H01 X) = genus X := by
  have e1 : RS.LaurentTail.H1Tail (0 : RS.Divisor X) ≃ₗ[ℂ] RS.H01 X :=
    (RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj).trans
      RS.dolbeaultEquiv
  have h2 : Module.finrank ℂ (RS.LaurentTail.H1Tail (0 : RS.Divisor X)) = genus X :=
    RS.TailDuality.h1T_zero_eq_genus
  rw [← e1.finrank_eq, h2]

/-- **The integral-pairing Dolbeault bridge** (the Serre-functional replacement for
`DolbeaultBridge.lean`'s abstract statement): if a smooth `(0,1)`-form pairs to zero against
EVERY holomorphic `1`-form, it is `dbar`-exact. Gated only on `serre-duality-tails`'s remaining
external fact (the same single gate as `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero`). -/
theorem exists_dbar_of_forall_pairing_eq_zero (PU : SurfPoU X)
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)))
    {η : RS.Form01 X} (h : ∀ θ : RS.Form1 X, pairing PU η θ = 0) :
    ∃ u : RS.SmoothC X, RS.dbar u = η := by
  rw [← RS.H01.mk_eq_zero_iff]
  have : FiniteDimensional ℂ (RS.H01 X) := RS.finiteDimensional_H01
  have hfr : Module.finrank ℂ (RS.Form1 X) = Module.finrank ℂ (Module.Dual ℂ (RS.H01 X)) := by
    rw [Subspace.dual_finrank_eq, finrank_H01_eq_genus hsurj]
    rfl
  have hsurjPsi : Function.Surjective (pairingDual PU) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp
      (pairingDual_injective PU)
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨θ, rfl⟩ := hsurjPsi φ
  change pairingH01 PU θ (RS.H01.mk η) = 0
  rw [pairingH01_mk]
  exact h θ

/-- **The single remaining gate, reformulated as a pure dimension count**: `tailToH1 0` is
surjective iff the Čech `H¹(𝒪_X)` has dimension at most `genus X`. (The `≥` inequality is the
unconditional tail injection `H1Tail.toH1_injective` + `h1T_zero_eq_genus`; classically the
`≤` direction is Forster §17.9's Serre-duality counting — the one fact of this challenge that
remains open, everything else in `Jacobian/Abel` now being reduced to it.) -/
theorem tailToH1_zero_surjective_iff_finrank_le :
    Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)) ↔
      Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) ≤ genus X := by
  constructor
  · intro hsurj
    have e1 := RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj
    rw [← e1.finrank_eq]
    exact le_of_eq RS.TailDuality.h1T_zero_eq_genus
  · intro hle
    have hinj := RS.LaurentTail.H1Tail.toH1_injective (0 : RS.Divisor X)
    have hgen : Module.finrank ℂ (RS.LaurentTail.H1Tail (0 : RS.Divisor X)) = genus X :=
      RS.TailDuality.h1T_zero_eq_genus
    have hfr : Module.finrank ℂ (RS.LaurentTail.H1Tail (0 : RS.Divisor X))
        = Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) := by
      refine le_antisymm ?_ ?_
      · exact LinearMap.finrank_le_finrank_of_injective hinj
      · rw [hgen]
        exact hle
    have hsurj' : Function.Surjective (RS.LaurentTail.H1Tail.toH1 (0 : RS.Divisor X)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
    intro ξ
    obtain ⟨c, hc⟩ := hsurj' ξ
    obtain ⟨z, rfl⟩ := RS.LaurentTail.H1Tail.mk_surjective (0 : RS.Divisor X) c
    refine ⟨z, ?_⟩
    rw [← RS.LaurentTail.H1Tail.toH1_mk]
    exact hc

end RS.Abel

end
