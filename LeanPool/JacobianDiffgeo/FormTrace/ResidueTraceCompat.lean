/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: form-trace-tower. `resAtP1` (D4) and residue-trace compatibility (task item 3,
Miranda Lemma 3.2 globalized).
-/
import LeanPool.JacobianDiffgeo.FormTrace.PairForm
import LeanPool.JacobianDiffgeo.FormTrace.TraceZkForm
import LeanPool.JacobianDiffgeo.MeromorphicTrace.FunctionTrace
import LeanPool.JacobianDiffgeo.MappingDegree.LocalStructure
import LeanPool.JacobianDiffgeo.MappingDegree.Degree
import LeanPool.JacobianDiffgeo.MappingDegree.Ramification

/-!
# Residue-trace compatibility (`form-trace-tower`, file 3/6)

Unit: form-trace-tower (`docs/design/form-trace-tower.md` §2 D4, §4.3, §5 P-main). THE central
theorem: Miranda Lemma 3.2 globalized, `Res_y(Tr ω) = Σ_{x ∈ F⁻¹y} Res_x(ω)`.

**Deviation from the design, forced by `PairForm.lean`'s finding:** the design's own proof plan
(§5 P-main step 2–3) invokes `resAtX_eq_of_mem_source` with the ADAPTED target chart `(S.A i).e'`
in place of `chartAt ℂ y₀` — exactly the FALSE general two-chart invariance documented in
`PairForm.lean`'s module docstring. Tracing through what actually makes the classical theorem
true: `AdaptedChartsAt`'s existence proof (`Jacobian/LocalMultiplicity/AdaptedCharts.lean`,
`exists_adaptedChartsAt`) always builds its target chart as `chartAt ℂ (F x)` shifted by an
ADDITIVE CONSTANT (`e' := (chartAt ℂ (F x) ≫ₕ (Homeomorph.subRight _)) ≫ₕ ofSet _`) — a
TRANSLATION, whose derivative is the honest CONSTANT `1` (not just at one point but identically),
which is exactly the case where changing the target chart costs nothing (no `1/λ`-type
correction, unlike a general — e.g. scaled — target chart). This translation property is a fact
about the *concrete construction*, not exposed as a field of the abstract `AdaptedChartsAt`/
`FiberStack` structures (an adversarial witness could rescale the target chart, which WOULD
introduce a genuine correction — see `PairForm.lean`). Since `resAtP1_trace_eq_sum` takes an
arbitrary `S : FiberStack F y₀` as an explicit parameter, this calibration is recorded as an
EXPLICIT hypothesis `hcal` (satisfied by any stack built via `exists_fiberStack`/
`exists_adaptedChartsAt`, per direct inspection of their construction) rather than assumed away.

* `resAtP1` (D4), `resAtP1_eq_resAtX_id`.
* `resAtP1_trace_eq_sum` — THE main theorem (task item 3), with the `hcal` calibration hypothesis.
* `trace_const_mul_pullback`, `trace_pullback_eq_degree_smul` — the projection-formula facts
  (task item 5, §4.6), NOT gated on the calibration issue at all (pure value/finsum identities).
-/

open scoped ContDiff Manifold
open Filter Topology Metric Function Set

namespace RS.FormTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Residue at `y₀ : ℙ¹` of a function `R : ℙ¹ → ℂ`, viewed as the coefficient of `R·dz`. -/
noncomputable def resAtP1 (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) : ℂ :=
  RS.resAt (R ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀)

theorem resAtP1_def (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) :
    resAtP1 R y₀ = RS.resAt (R ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) := rfl

theorem resAtP1_eq_resAtX_id (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) :
    resAtP1 R y₀ = resAtX (id : OnePoint ℂ → OnePoint ℂ) R y₀ := by
  rw [resAtP1_def, resAtX_def]
  apply resAt_congr
  have hmem : ∀ᶠ z in 𝓝 (chartAt ℂ y₀ y₀), z ∈ (chartAt ℂ y₀).target :=
    (chartAt ℂ y₀).open_target.mem_nhds ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀))
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with z hz
  change R ((chartAt ℂ y₀).symm z) =
    R ((chartAt ℂ y₀).symm z) * deriv (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) z
  have hderiv1 : deriv (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) z = 1 := by
    have heq : (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) =ᶠ[𝓝 z] id := by
      filter_upwards [(chartAt ℂ y₀).open_target.mem_nhds hz] with z' hz'
      change chartAt ℂ y₀ ((chartAt ℂ y₀).symm z') = z'
      rw [(chartAt ℂ y₀).right_inv hz']
    rw [heq.deriv_eq, deriv_id]
  rw [hderiv1, mul_one]

/-! ### Compat: meromorphy is preserved by a translation of the base point -/

private theorem meromorphicAt_comp_sub_const {g : ℂ → ℂ} {c₀ : ℂ} (hg : MeromorphicAt g 0) :
    MeromorphicAt (fun z => g (z - c₀)) c₀ := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  have hφ : AnalyticAt ℂ (fun z : ℂ => z - c₀) c₀ := by fun_prop
  have hcomp := hn.fun_comp_of_eq hφ (by simp : (fun z : ℂ => z - c₀) c₀ = 0)
  simpa using hcomp

/-! ### The per-fibre-point identification, under the calibration hypothesis -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Under the calibration hypothesis (the module docstring's `hcal`), the pair-form residue
computed via an ADAPTED chart pair equals `resAtX` (computed via the PREFERRED chart pair). This
is the corrected replacement for the design's (false, see `PairForm.lean`) general two-chart
`resAtX_eq_of_mem_source`. -/
private theorem resAtX_eq_resAt_adapted {F : X → OnePoint ℂ} {h : X → ℂ} {x : X}
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hh : MeromorphicAtX h x)
    {k : ℕ} (A : RS.AdaptedChartsAt F x k)
    (hcal : ∀ y ∈ A.e'.source, A.e' y = chartAt ℂ (F x) y - chartAt ℂ (F x) (F x)) :
    RS.resAt (fun w => h (A.e.symm w) * deriv (A.e' ∘ F ∘ A.e.symm) w) 0 = resAtX F h x := by
  have hstep1 := resAt_pairForm_source_change A.mem_maximalAtlas A.mem_source
      (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source ℂ x) A.mem_maximalAtlas'
      A.mem_source' hF hh
  rw [A.map_eq_zero] at hstep1
  rw [hstep1, resAtX_def]
  apply resAt_congr
  have hcont : ContinuousAt (fun z => F ((chartAt ℂ x).symm z)) (chartAt ℂ x x) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    have h2 : ContinuousAt F ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hF.continuousAt
    exact h2.comp h1
  have hval : F ((chartAt ℂ x).symm (chartAt ℂ x x)) = F x := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hmemsrc : ∀ᶠ z in 𝓝 (chartAt ℂ x x), F ((chartAt ℂ x).symm z) ∈ A.e'.source := by
    have hnbhd : A.e'.source ∈ 𝓝 (F ((chartAt ℂ x).symm (chartAt ℂ x x))) := by
      rw [hval]; exact A.e'.open_source.mem_nhds A.mem_source'
    exact hcont.eventually hnbhd
  have heqfun : ∀ᶠ z in 𝓝 (chartAt ℂ x x), ∀ᶠ z' in 𝓝 z,
      A.e' (F ((chartAt ℂ x).symm z'))
        = chartAt ℂ (F x) (F ((chartAt ℂ x).symm z')) - chartAt ℂ (F x) (F x) := by
    apply hmemsrc.eventually_nhds.mono
    intro z hz
    filter_upwards [hz] with z' hz'
    exact hcal _ hz'
  have hderiveq : deriv (A.e' ∘ F ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 (chartAt ℂ x x)] deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) := by
    filter_upwards [heqfun] with z hz
    have heq2 : (A.e' ∘ F ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝 z] (fun z' => (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z' - chartAt ℂ (F x) (F x)) :=
      hz
    rw [heq2.deriv_eq, deriv_sub_const]
  filter_upwards [hderiveq.filter_mono nhdsWithin_le_nhds] with z hz
  change h ((chartAt ℂ x).symm z) * deriv (A.e' ∘ F ∘ (chartAt ℂ x).symm) z
    = h ((chartAt ℂ x).symm z) * deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z
  rw [hz]

/-! ### THE main theorem -/

variable {F : X → OnePoint ℂ}

/-- **THE main theorem** (Miranda Lemma 3.2, globalized over an arbitrary fibre via
`FiberStack`). See the module docstring for the calibration hypothesis `hcal`, needed because
the general two-chart `resAtX` invariance the design's own proof plan relied on is false
(`PairForm.lean`); `hcal` is satisfied by any stack produced by `exists_fiberStack` (per direct
inspection of `exists_adaptedChartsAt`'s construction, which always builds a translate of
`chartAt` on the target side). -/
theorem resAtP1_trace_eq_sum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : MeromorphicOnX h Set.univ)
    {y₀ : OnePoint ℂ} (S : RS.FiberStack F y₀)
    (hcal : ∀ i : Fin S.n, ∀ y ∈ (S.A i).e'.source,
      (S.A i).e' y = chartAt ℂ y₀ y - chartAt ℂ y₀ y₀) :
    resAtP1 (RS.MTrace.trace F h) y₀ = ∑ i, resAtX F h (S.pt i) := by
  set c₀ : ℂ := chartAt ℂ y₀ y₀ with hc₀_def
  rw [resAtP1_def]
  -- Step 1: `trace F h`, read through `S`, near `y₀` in the `chartAt ℂ y₀`-variable.
  have hVmem : ∀ᶠ z in 𝓝 c₀, z ∈ (chartAt ℂ y₀).target ∧ (chartAt ℂ y₀).symm z ∈ S.V := by
    have h1 : (chartAt ℂ y₀).target ∈ 𝓝 c₀ :=
      (chartAt ℂ y₀).open_target.mem_nhds ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀))
    have h2 : (chartAt ℂ y₀).symm ⁻¹' S.V ∈ 𝓝 c₀ := by
      apply ContinuousAt.preimage_mem_nhds
        ((chartAt ℂ y₀).continuousAt_symm ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀)))
      rw [(chartAt ℂ y₀).left_inv (mem_chart_source ℂ y₀)]
      exact S.isOpen_V.mem_nhds S.mem_V
    filter_upwards [h1, h2] with z hz1 hz2
    exact ⟨hz1, hz2⟩
  have hstep1 : (RS.MTrace.trace F h ∘ (chartAt ℂ y₀).symm) =ᶠ[𝓝 c₀]
      (fun z => ∑ i, RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) (z - c₀))
          := by
    filter_upwards [hVmem] with z hz
    obtain ⟨hzt, hzV⟩ := hz
    change RS.MTrace.trace F h ((chartAt ℂ y₀).symm z)
      = ∑ i, RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) (z - c₀)
    rw [RS.MTrace.trace_eq_stack_sum hF hne S hzV]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hy₀src : (chartAt ℂ y₀).symm z ∈ (S.A i).e'.source := S.V_subset i hzV
    rw [hcal i _ hy₀src, (chartAt ℂ y₀).right_inv hzt]
  rw [resAt_congr (hstep1.filter_mono nhdsWithin_le_nhds)]
  -- Step 2: distribute `resAt` over the finite sum.
  have hmero : ∀ i : Fin S.n, MeromorphicAt
      (fun z => RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) (z - c₀)) c₀ :=
          by
    intro i
    have h1 : MeromorphicAt (h ∘ (S.A i).e.symm) ((S.A i).e (S.pt i)) :=
      (RS.meromorphicAtX_iff_of_mem_source (S.A i).mem_maximalAtlas
        (S.mem_source_pt i)).1 (hh (S.pt i) (Set.mem_univ _))
    rw [(S.A i).map_eq_zero] at h1
    exact meromorphicAt_comp_sub_const
      (RS.MTrace.meromorphicAt_traceZk h1 (S.mult_ne_zero i))
  rw [resAt_fun_sum (fun i _ => hmero i)]
  -- Step 3: `resAt` of the shifted `RS.MTrace.traceZk` term = `resAt` of the term itself (at `0`).
  have hstep3 : ∀ i : Fin S.n, RS.resAt
      (fun z => RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) (z - c₀)) c₀
      = RS.resAt (RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))) 0 := by
    intro i
    have h1 : MeromorphicAt (h ∘ (S.A i).e.symm) ((S.A i).e (S.pt i)) :=
      (RS.meromorphicAtX_iff_of_mem_source (S.A i).mem_maximalAtlas
        (S.mem_source_pt i)).1 (hh (S.pt i) (Set.mem_univ _))
    rw [(S.A i).map_eq_zero] at h1
    have h2 : MeromorphicAt (RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)))
        0 :=
      RS.MTrace.meromorphicAt_traceZk h1 (S.mult_ne_zero i)
    have hφ : AnalyticAt ℂ (fun z : ℂ => z - c₀) c₀ := by fun_prop
    have hφderiv : deriv (fun z : ℂ => z - c₀) c₀ = 1 := by
      simp
    have hφ' : deriv (fun z : ℂ => z - c₀) c₀ ≠ 0 := by rw [hφderiv]; exact one_ne_zero
    have hkey := resAt_comp_mul_deriv hφ hφ' (by simp : (fun z : ℂ => z - c₀) c₀ = 0) h2
    have heq :
        (fun z => RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) (z - c₀))
        = fun z => RS.MTrace.traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i))
            ((fun w : ℂ => w - c₀) z)
          * deriv (fun w : ℂ => w - c₀) z := by
      funext z
      have hd : deriv (fun w : ℂ => w - c₀) z = 1 := by simp
      rw [hd, mul_one]
    rw [heq]
    exact hkey
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep3 i)]
  -- Step 4: the per-fibre-point identification, `traceZkForm` cancellation + `resAtX`.
  apply Finset.sum_congr rfl
  intro i _
  set k : ℕ := RS.multiplicity F (S.pt i) with hk_def
  have hk0 : k ≠ 0 := S.mult_ne_zero i
  have h1 : MeromorphicAt (h ∘ (S.A i).e.symm) ((S.A i).e (S.pt i)) :=
    (RS.meromorphicAtX_iff_of_mem_source (S.A i).mem_maximalAtlas
      (S.mem_source_pt i)).1 (hh (S.pt i) (Set.mem_univ _))
  rw [(S.A i).map_eq_zero] at h1
  set g_i : ℂ → ℂ := fun v => h ((S.A i).e.symm v) * (k : ℂ) * v ^ ((k : ℤ) - 1) with hgi_def
  have hgimero : MeromorphicAt g_i 0 := by
    have hzp : MeromorphicAt (fun v : ℂ => v ^ ((k : ℤ) - 1)) 0 := by
      simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow ((k : ℤ) - 1)
    have := h1.fun_mul ((MeromorphicAt.const (k : ℂ) 0).fun_mul hzp)
    simpa [hgi_def, mul_assoc] using this
  have hcong : traceZkForm g_i k =ᶠ[𝓝[≠] (0 : ℂ)] RS.MTrace.traceZk (h ∘ (S.A i).e.symm) k := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact traceZkForm_hAdapted_eq_apply hk0 hw
  rw [← resAt_congr hcong, resAt_traceZkForm hgimero hk0]
  -- `g_i` IS `resAtX`'s adapted-chart integrand: `deriv ((S.A i).e' ∘ F ∘ (S.A i).e.symm)` is
  -- `k · w^{k-1}` exactly, by the adapted-chart normal form `eqOn_pow`.
  have hderivpow : deriv ((S.A i).e' ∘ F ∘ (S.A i).e.symm) =ᶠ[𝓝 (0 : ℂ)]
      fun w => (k : ℂ) * w ^ ((k : ℤ) - 1) := by
    have heqfun : ((S.A i).e' ∘ F ∘ (S.A i).e.symm) =ᶠ[𝓝 (0 : ℂ)] fun w => w ^ k := by
      have hmem : (S.A i).e.target ∈ 𝓝 (0 : ℂ) := by
        rw [← (S.A i).map_eq_zero]
        exact (S.A i).e.open_target.mem_nhds ((S.A i).e.map_source (S.mem_source_pt i))
      filter_upwards [hmem] with w hw
      change (S.A i).e' (F ((S.A i).e.symm w)) = w ^ k
      rw [(S.A i).eqOn_pow _ ((S.A i).e.map_target hw), (S.A i).e.right_inv hw]
    have heqfun2 : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ᶠ w' in 𝓝 w,
        ((S.A i).e' ∘ F ∘ (S.A i).e.symm) w' = w' ^ k := heqfun.eventually_nhds
    filter_upwards [heqfun2] with w hw
    have heq2 : ((S.A i).e' ∘ F ∘ (S.A i).e.symm) =ᶠ[𝓝 w] (fun w' : ℂ => w' ^ k) := hw
    rw [heq2.deriv_eq]
    have hk1 : 1 ≤ k := S.one_le_mult i
    have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [deriv_pow_field, ← hcast, zpow_natCast]
  have hgieq : g_i =ᶠ[𝓝[≠] (0 : ℂ)]
      fun w => h ((S.A i).e.symm w) * deriv ((S.A i).e' ∘ F ∘ (S.A i).e.symm) w := by
    filter_upwards [hderivpow.filter_mono nhdsWithin_le_nhds] with w hw
    change h ((S.A i).e.symm w) * (k : ℂ) * w ^ ((k : ℤ) - 1)
      = h ((S.A i).e.symm w) * deriv ((S.A i).e' ∘ F ∘ (S.A i).e.symm) w
    rw [hw, mul_assoc]
  rw [resAt_congr hgieq]
  have hFx : F (S.pt i) = y₀ := S.maps_pt_eq i
  have hcal' : ∀ y ∈ (S.A i).e'.source,
      (S.A i).e' y = chartAt ℂ (F (S.pt i)) y - chartAt ℂ (F (S.pt i)) (F (S.pt i)) := by
    rw [hFx]; exact hcal i
  exact resAtX_eq_resAt_adapted (hF (S.pt i)) (hh (S.pt i) (Set.mem_univ _))
    (A := S.A i) hcal'

/-! ### Projection-formula facts (task item 5, §4.6) — forward-looking, non-blocking exports for
a future `jacobian-functoriality` unit. Pure VALUE identities (no residues, no chart issue). -/

/-- Miranda Problem VIII.3.D (`Tr` is `ℳ(Y)`-linear against pullbacks), value form: TRUE
unconditionally over every `y` — this one goes through mtrace's naive-fibre-sum characterization
`trace_eq_finsum'` directly (no `traceZk`/branch-point subtlety, since `F x = y` for every `x` in
the fibre regardless of ramification). -/
theorem trace_const_mul_pullback (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    {g : OnePoint ℂ → ℂ} (h : X → ℂ) :
    RS.MTrace.trace F (fun x => g (F x) * h x) = fun y => g y * RS.MTrace.trace F h y := by
  funext y
  rw [RS.MTrace.trace_eq_finsum' hF hne, RS.MTrace.trace_eq_finsum' hF hne, mul_finsum_mem]
  apply finsum_mem_congr rfl
  intro x hx
  have hxy : F x = y := hx
  rw [hxy]

/-- Miranda Problem VIII.3.D's `g := 1`/degree specialization, `Tr(F^*g) = deg·g` — **restricted
to regular values** (deviation from the design's unconditional claim, a genuine gap found the
same way as `PairForm.lean`'s: at a BRANCH value, `traceZk`'s own junk convention at `w = 0`
(`traceZk h k 0 = h 0`, NOT `k · h 0` — see `PlanarTrace.lean`'s `traceZk_comp_pow`, explicitly
caveated "genuinely false at `w = 0`") makes `trace F (fun x => g (F x))` compute the NAIVE fibre
CARDINALITY, not the multiplicity-weighted `degree F`, at a branch point — e.g. `F := (·^2)`,
`g := 1`: `trace F (fun _ => 1) 0 = 1` (a single preimage `0`) but `degree F = 2`. Provable, and
still useful, at REGULAR values, where every fibre point has multiplicity `1` so the naive
cardinality IS the degree. -/
theorem trace_pullback_eq_degree_smul_of_regular (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (g : OnePoint ℂ → ℂ) {y₀ : OnePoint ℂ}
    (hy₀ : RS.IsRegularValue F y₀) :
    RS.MTrace.trace F (fun x => g (F x)) y₀ = (RS.degree F : ℂ) * g y₀ := by
  rw [RS.MTrace.trace_of_regular hF hne hy₀]
  have hfin : (F ⁻¹' {y₀}).Finite := RS.fiber_finite hF hne y₀
  have hmult1 : ∀ x ∈ hfin.toFinset, RS.multiplicity F x = 1 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have h1 : 1 ≤ RS.multiplicity F x := RS.one_le_multiplicity_of_not_const hF hne x
    have h2 : ¬ RS.IsRamifiedAt F x := hy₀ x hx
    unfold RS.IsRamifiedAt at h2
    omega
  have hdeg : RS.degree F = hfin.toFinset.card := by
    rw [RS.degree_eq_fiberMultSum hF hne y₀, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_congr rfl hmult1, Finset.sum_const, smul_eq_mul, mul_one]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have heq : ∀ x ∈ hfin.toFinset, g (F x) = g y₀ := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxy : F x = y₀ := hx
    rw [hxy]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul, hdeg]

end RS.FormTrace
