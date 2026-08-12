/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: meromorphic-trace. The planar trace atom `traceZk h k w` (trace of `h` along
`z ↦ z ^ k`), file 4 of the design's 6-file plan.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import LeanPool.JacobianDiffgeo.MappingDegree.RootCounting
import LeanPool.JacobianDiffgeo.LocalMultiplicity.KthRoot
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue

/-!
# The planar trace atom `traceZk` (meromorphic-trace, cluster 2)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D6, §4.4, §5 P4-P6). Purely planar
(mathlib + `MappingDegree.RootCounting` + `LocalMultiplicity.KthRoot` + `ResidueCalculus`); no
manifold content, independent of `ToP1`/`OrderMultiplicity`/`ArgumentPrinciple`.

* `traceZk h k w := ∑ᶠ z ∈ {z | z ^ k = w}, h z` — the trace of `h` over the (generically
  `k`-element) root set of `z ↦ z ^ k` at `w`. Junk `traceZk h k 0 = h 0` (root set is `{0}`).
* Basic API: `traceZk_eq_finset_sum` (the master Finset conversion, any `w`), linearity
  (`traceZk_add`, guarded by `k ≠ 0` — see the deviation note below, `traceZk_const_mul`,
  unconditional), `traceZk_comp_pow`.
* `analyticAt_traceZk` (P4): `traceZk h k` is analytic at any `w₀ ≠ 0` at which all `k`-th roots
  of `w₀` lie in `h`'s domain of analyticity, via local root branches (`AnalyticAt.exists_pow_eq`)
  and a primitive `k`-th root of unity — no monodromy.
* `meromorphicAt_traceZk` (P5): `traceZk h k` is meromorphic at `0` when `h` is, via a growth
  bound on the root-sum and Riemann's removable singularity theorem — no convergent Laurent
  series needed for existence.
* `traceZk_zpow`: closed form for monomial traces, `traceZk (·^e) k w = k * w^(e/k)` if `k ∣ e`,
  `0` otherwise (`w ≠ 0`) — the geometric-sum collapse of `k`-th roots of unity, computed on the
  abstract root set (one root + a primitive root of unity), purely algebraically.
* `laurentCoeffAt_traceZk` (P6): the Laurent-coefficient formula
  `laurentCoeffAt (traceZk h k) 0 m = k * laurentCoeffAt h 0 (k * m)`, `tsum`-free: exact finite
  Taylor remainder of the order presentation's unit factor (cutoff chosen so the remainder
  exponent is an exact multiple of `k`, making the remainder trace factor as
  `w ^ s' * traceZk r k w` with NO second growth bound), `traceZk_zpow` on the finitely many
  monomials, and residue-calculus's presentation-independent `laurentCoeffAt` characterization.
-/

open Filter Set Topology Metric Function

namespace RS.MTrace

variable {h g : ℂ → ℂ} {k : ℕ} {w z : ℂ}

/-- The trace of `h` along `z ↦ z ^ k` at `w`: the sum of `h` over the (generically `k`-element)
root set. Junk-free by convention: at `w = 0` the root set is the singleton `{0}` (for `k ≠ 0`),
giving `h 0`; at `w` with `k = 0` the support is either empty or all of `ℂ`, and `finsum` junks
to `0` in the latter case unless `h` itself has finite support there. -/
noncomputable def traceZk (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  ∑ᶠ z ∈ {z : ℂ | z ^ k = w}, h z

theorem traceZk_def (h : ℂ → ℂ) (k : ℕ) (w : ℂ) :
    traceZk h k w = ∑ᶠ z ∈ {z : ℂ | z ^ k = w}, h z := rfl

/-- Master conversion to a `Finset` sum, valid for every `w` (the root set is always finite once
`k ≠ 0`, regardless of `w`). -/
theorem traceZk_eq_finset_sum (h : ℂ → ℂ) (hk : k ≠ 0) (w : ℂ) :
    traceZk h k w = ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z :=
  finsum_mem_eq_finite_toFinset_sum _ (RS.setOf_pow_eq_finite hk w)

theorem traceZk_apply_of_ne_zero (hk : k ≠ 0) (_hw : w ≠ 0) :
    traceZk h k w = ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z :=
  traceZk_eq_finset_sum h hk w

/-- Honest but junk value at the branch point: `traceZk h k 0 = h 0` (the root set of `z ^ k = 0`
is the singleton `{0}`). Never used to reason about `MeromorphicAt`/`laurentCoeffAt`/`resAt` at
`0`, all of which are `𝓝[≠]0`-germ notions and hence blind to this junk (see the design's junk
ledger, §6). -/
theorem traceZk_zero_apply (hk : k ≠ 0) : traceZk h k 0 = h 0 := by
  rw [traceZk_def, RS.setOf_pow_eq_zero hk, finsum_mem_singleton]

/-! ### Linearity -/

/-- Additivity, guarded by `k ≠ 0` (deviation from the design's unconditional statement: at
`k = 0`, `w = 1` the root set is all of `ℂ`, and additivity fails there whenever one summand has
finite support on `ℂ` and the other does not — e.g. `h₁ = Set.indicator {0} 1`, `h₂ = 1`. With
`k ≠ 0` the root set is always finite, so this is not an issue.). -/
theorem traceZk_add (hk : k ≠ 0) : traceZk (h + g) k = traceZk h k + traceZk g k := by
  funext w
  simp only [Pi.add_apply, traceZk_eq_finset_sum _ hk]
  exact Finset.sum_add_distrib

theorem traceZk_fun_add (hk : k ≠ 0) :
    traceZk (fun z => h z + g z) k = fun w => traceZk h k w + traceZk g k w :=
  traceZk_add hk

/-- Unconditional in `k` (scalar multiplication by `c` does not change support-finiteness, so no
`k ≠ 0` guard is needed, unlike `traceZk_add`). -/
theorem traceZk_const_mul (c : ℂ) (k : ℕ) :
    traceZk (fun z => c * h z) k = fun w => c * traceZk h k w := by
  funext w
  set s : Set ℂ := {z : ℂ | z ^ k = w} with hs_def
  change ∑ᶠ z ∈ s, c * h z = c * ∑ᶠ z ∈ s, h z
  rw [finsum_mem_def, finsum_mem_def]
  have hind : s.indicator (fun z => c * h z) = fun z => c * s.indicator h z := by
    funext z
    by_cases hz : z ∈ s <;> simp [hz]
  rw [hind]
  simpa using (smul_finsum c (s.indicator h)).symm

/-- Trace of a pullback (branch-point caveat: only away from `0`, see the design's junk ledger,
§6 — the identity is genuinely false at `w = 0`). -/
theorem traceZk_comp_pow (g : ℂ → ℂ) (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    traceZk (fun z => g (z ^ k)) k w = k * g w := by
  rw [traceZk_apply_of_ne_zero hk hw]
  have heq : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, g (z ^ k) = g w := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [show z ^ k = w from hz]
  rw [Finset.sum_congr rfl heq, Finset.sum_const]
  have hcard : (RS.setOf_pow_eq_finite hk w).toFinset.card = k := by
    rw [← Set.ncard_eq_toFinset_card _ (RS.setOf_pow_eq_finite hk w), RS.ncard_setOf_pow_eq hk hw]
  rw [hcard, nsmul_eq_mul]

/-! ### Analyticity away from the branch point (P4) -/

/-- `traceZk h k` is analytic at any `w₀ ≠ 0` all of whose `k`-th roots lie in `h`'s domain of
analyticity `ball 0 ρ \ {0}`. Local branches (`AnalyticAt.exists_pow_eq`) witness analyticity;
no monodromy — the branches are never assembled into a global formula across a branch cut. -/
theorem analyticAt_traceZk (hk : k ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρ \ {0})) {w₀ : ℂ} (hw₀ : w₀ ≠ 0)
    (hw₀ρ : ‖w₀‖ < ρ ^ k) : AnalyticAt ℂ (traceZk h k) w₀ := by
  classical
  -- Step 1: one local analytic branch of the `k`-th root of `id` at `w₀`.
  obtain ⟨ψ₁, hψ₁an, hψ₁ne, hψ₁pow⟩ :=
    RS.AnalyticAt.exists_pow_eq (u := id) (analyticAt_id (z := w₀)) hw₀ hk
  -- Step 2: a primitive `k`-th root of unity, and the `k` branches `ζ ^ i * ψ₁`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ k := ⟨_, Complex.isPrimitiveRoot_exp k hk⟩
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk
  set ψ : ℕ → ℂ → ℂ := fun i w => ζ ^ i * ψ₁ w with hψ_def
  have hψan : ∀ i, AnalyticAt ℂ (ψ i) w₀ := fun i => analyticAt_const.mul hψ₁an
  have hψpow : ∀ i, ∀ᶠ w in 𝓝 w₀, ψ i w ^ k = w := by
    intro i
    filter_upwards [hψ₁pow] with w hw
    change (ζ ^ i * ψ₁ w) ^ k = w
    rw [mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hw, id_eq]
  have hψ₁w₀pow : ψ₁ w₀ ^ k = w₀ := by
    have := hψ₁pow.self_of_nhds; rwa [id_eq] at this
  have hψ₁w₀norm : ‖ψ₁ w₀‖ < ρ := RS.norm_lt_of_pow_eq hk hρ.le hψ₁w₀pow hw₀ρ
  have hψnorm0 : ∀ i, ‖ψ i w₀‖ < ρ := by
    intro i
    change ‖ζ ^ i * ψ₁ w₀‖ < ρ
    rw [norm_mul, norm_pow, hζnorm, one_pow, one_mul]
    exact hψ₁w₀norm
  have hψne0 : ∀ i, ψ i w₀ ≠ 0 := fun i => mul_ne_zero (pow_ne_zero i (hζ.ne_zero hk)) hψ₁ne
  have hinj0 : Set.InjOn (fun i => ζ ^ i * ψ₁ w₀) (Finset.range k) := hζ.injOn_pow_mul hψ₁ne
  -- Step 3: persistence of the pointwise facts to a common neighborhood `V` of `w₀`.
  have hall_ne : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ψ i w ≠ 0 := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => (hψan i).continuousAt.eventually_ne (hψne0 i)
  have hall_norm : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ‖ψ i w‖ < ρ := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => (hψan i).continuousAt.norm.eventually (Iio_mem_nhds (hψnorm0 i))
  have hall_pow : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ψ i w ^ k = w := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => hψpow i
  have hall_distinct : ∀ᶠ w in 𝓝 w₀,
      ∀ p ∈ Finset.range k ×ˢ Finset.range k, p.1 ≠ p.2 → ψ p.1 w ≠ ψ p.2 w := by
    rw [Filter.eventually_all_finset]
    rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    rcases eq_or_ne i j with rfl | hij'
    · exact Filter.Eventually.of_forall (fun _ hne => absurd rfl hne)
    · have h0 : ψ i w₀ ≠ ψ j w₀ := fun he => hij'
        (hinj0 (Finset.mem_range.2 hij.1) (Finset.mem_range.2 hij.2) he)
      have hev : ∀ᶠ w in 𝓝 w₀, ψ i w - ψ j w ≠ 0 :=
        ((hψan i).sub (hψan j)).continuousAt.eventually_ne (sub_ne_zero.2 h0)
      exact hev.mono (fun w hw _ => sub_ne_zero.1 hw)
  have hne0 : ∀ᶠ w in 𝓝 w₀, w ≠ 0 := isOpen_ne.mem_nhds hw₀
  -- Step 4: the eventual reindexing of `traceZk h k` as a finite sum over the branches.
  have heq : traceZk h k =ᶠ[𝓝 w₀] (fun w => ∑ i ∈ Finset.range k, h (ψ i w)) := by
    filter_upwards [hne0, hall_ne, hall_norm, hall_pow, hall_distinct]
      with w hw0 hwne hwnorm hwpow hwdist
    have hbij : Set.BijOn (fun i => ψ i w) (↑(Finset.range k) : Set ℕ) {z : ℂ | z ^ k = w} := by
      refine ⟨fun i hi => hwpow i (Finset.mem_coe.mp hi), fun i hi j hj hij => ?_, fun z hz => ?_⟩
      · by_contra hne
        exact hwdist (i, j) (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hi, Finset.mem_coe.mp hj⟩)
          hne hij
      · have hinj : Set.InjOn (fun i => ψ i w) (↑(Finset.range k) : Set ℕ) := by
          intro i hi j hj hij
          by_contra hne
          exact hwdist (i, j)
            (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hi, Finset.mem_coe.mp hj⟩) hne hij
        have hsub : (fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ) ⊆ {z : ℂ | z ^ k = w} := by
          rintro z ⟨i, hi, rfl⟩
          exact hwpow i (Finset.mem_coe.mp hi)
        have hcard1 : ((fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ)).ncard = k := by
          rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
        have hcard2 : ({z : ℂ | z ^ k = w}).ncard = k := RS.ncard_setOf_pow_eq hk hw0
        have heqset : (fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ) = {z : ℂ | z ^ k = w} :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hcard1, hcard2]) (RS.setOf_pow_eq_finite hk w)
        rw [heqset]
        exact hz
    rw [traceZk_def, ← finsum_mem_eq_of_bijOn (fun i => ψ i w) hbij (fun i _ => rfl),
      finsum_mem_coe_finset]
  have hRHSanalytic : AnalyticAt ℂ (fun w => ∑ i ∈ Finset.range k, h (ψ i w)) w₀ := by
    apply Finset.analyticAt_fun_sum
    intro i _
    have hmem : ψ i w₀ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
      ⟨mem_ball_zero_iff.mpr (hψnorm0 i), by simp [hψne0 i]⟩
    exact (hh _ hmem).fun_comp (hψan i)
  exact hRHSanalytic.congr heq.symm

/-! ### Meromorphy at the branch point (P5) -/

/-- `traceZk h k` is meromorphic at `0` whenever `h` is, via a norm/`zpow` growth bound on the
root-sum and Riemann's removable-singularity theorem
(`Complex.differentiableOn_update_limUnder_of_bddAbove`) — no monodromy, no convergent global
Laurent series needed for existence. -/
theorem meromorphicAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZk h k) 0 := by
  classical
  by_cases hordtop : meromorphicOrderAt h 0 = ⊤
  · -- Degenerate case: `h` vanishes identically near `0`, hence so does `traceZk h k`.
    have hh0 : h =ᶠ[𝓝[≠] (0 : ℂ)] 0 := meromorphicOrderAt_eq_top_iff.1 hordtop
    obtain ⟨ρ, hρ0, hρsub⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hh0)
    have htrace0 : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
      have hballmem : Metric.ball (0 : ℂ) (ρ ^ k) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (pow_pos hρ0 k)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hballmem, self_mem_nhdsWithin]
        with w hwball hwne
      have hw0 : w ≠ 0 := hwne
      change traceZk h k w = 0
      rw [traceZk_apply_of_ne_zero hk hw0]
      apply Finset.sum_eq_zero
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have hzpow : z ^ k = w := hz
      have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ0.le hzpow (mem_ball_zero_iff.mp hwball)
      have hzne : z ≠ 0 := by
        rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
      exact hρsub z (mem_ball_zero_iff.mpr hzlt) hzne
    exact analyticAt_const.meromorphicAt.congr htrace0.symm
  · -- Main case: honest order presentation `h =ᶠ[𝓝[≠]0] z ↦ z ^ n₀ * u z`, `u` analytic, `u 0 ≠ 0`.
    obtain ⟨u, hu, hune, hu_eq⟩ := (meromorphicOrderAt_ne_top_iff hh).1 hordtop
    generalize hn₀_def : (meromorphicOrderAt h 0).untop₀ = n₀ at hu_eq
    have hu_eq' : h =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ n₀ * u z := by
      filter_upwards [hu_eq] with z hz
      rw [hz, smul_eq_mul, sub_zero]
    -- Euclidean split of `n₀` by `k`: `n₀ = k * q + r`.
    have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    obtain ⟨q, r, hn₀_eq⟩ : ∃ (q : ℤ) (r : ℕ), n₀ = (k : ℤ) * q + (r : ℤ) := by
      refine ⟨n₀ / (k : ℤ), (n₀ % (k : ℤ)).toNat, ?_⟩
      have hmod_nonneg : 0 ≤ n₀ % (k : ℤ) := Int.emod_nonneg n₀ (by omega)
      rw [Int.toNat_of_nonneg hmod_nonneg]
      exact (Int.mul_ediv_add_emod n₀ (k : ℤ)).symm
    -- `V w := w ^ (-q) * traceZk h k w`; unconditional identity off `0`.
    set V : ℂ → ℂ := fun w => w ^ (-q) * traceZk h k w with hV_def
    have hstep3 : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)] fun w => w ^ q * V w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw0 : w ≠ 0 := hw
      change traceZk h k w = w ^ q * (w ^ (-q) * traceZk h k w)
      rw [← mul_assoc, ← zpow_add₀ hw0, add_neg_cancel, zpow_zero, one_mul]
    -- A single radius `ρ` on which `h` is analytic, presented, and `u` is bounded.
    have hcomb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ h z ∧ h z = z ^ n₀ * u z :=
      hh.eventually_analyticAt.and hu_eq'
    obtain ⟨ρ₁, hρ₁0, hρ₁sub⟩ :=
      Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hcomb)
    set Cu : ℝ := ‖u 0‖ + 1 with hCu_def
    have hCu_bound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u z‖ < Cu :=
      hu.continuousAt.norm.tendsto.eventually (Iio_mem_nhds (by rw [hCu_def]; linarith))
    obtain ⟨ρ₂, hρ₂0, hρ₂sub⟩ := Metric.eventually_nhds_iff_ball.mp hCu_bound
    set ρ : ℝ := min (min ρ₁ ρ₂) 1 with hρ_def
    have hρ0 : 0 < ρ := lt_min (lt_min hρ₁0 hρ₂0) one_pos
    have hρ1 : ρ ≤ 1 := min_le_right _ _
    have hρle1 : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hρle2 : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hh_an : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρ \ {0}) := by
      rintro z ⟨hz1, hz2⟩
      exact (hρ₁sub z (Metric.ball_subset_ball hρle1 hz1) hz2).1
    have hh_pres : ∀ z, z ∈ Metric.ball (0 : ℂ) ρ → z ≠ 0 → h z = z ^ n₀ * u z := fun z hz1 hz2 =>
      (hρ₁sub z (Metric.ball_subset_ball hρle1 hz1) hz2).2
    have hu_bound : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖u z‖ < Cu := fun z hz =>
      hρ₂sub z (Metric.ball_subset_ball hρle2 hz)
    set ρ' : ℝ := ρ ^ k with hρ'_def
    have hρ'0 : 0 < ρ' := pow_pos hρ0 k
    -- Step 4: `V` analytic on `ball 0 ρ' \ {0}`.
    have hVan : ∀ z ∈ Metric.ball (0 : ℂ) ρ' \ {0}, AnalyticAt ℂ V z := by
      rintro z ⟨hz1, hz2⟩
      have hzne : z ≠ 0 := hz2
      have htz : AnalyticAt ℂ (traceZk h k) z :=
        analyticAt_traceZk hk hρ0 hh_an hzne (mem_ball_zero_iff.mp hz1)
      have hzp : AnalyticAt ℂ (fun w : ℂ => w ^ (-q)) z := by
        simpa using (analyticAt_id (𝕜 := ℂ) (z := z)).fun_zpow (n := -q) hzne
      exact hzp.mul htz
    -- Step 5: uniform norm bound on `V` over `ball 0 ρ' \ {0}`.
    have hVbound : ∀ w ∈ Metric.ball (0 : ℂ) ρ' \ {0}, ‖V w‖ ≤ (k : ℝ) * Cu := by
      rintro w ⟨hw1, hw2⟩
      have hw0 : w ≠ 0 := hw2
      have hwlt : ‖w‖ < ρ ^ k := by rwa [mem_ball_zero_iff, hρ'_def] at hw1
      have hbound_term : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖h z‖ ≤ ‖w‖ ^ q * Cu := by
        intro z hz
        rw [Set.Finite.mem_toFinset] at hz
        have hzpow : z ^ k = w := hz
        have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ0.le hzpow hwlt
        have hzne : z ≠ 0 := by
          rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
        have hzr : z ^ n₀ = w ^ q * z ^ (r : ℤ) := by
          have hexp : z ^ n₀ = z ^ ((k : ℤ) * q + (r : ℤ)) := by rw [← hn₀_eq]
          rw [hexp, zpow_add₀ hzne, zpow_mul, zpow_natCast, hzpow]
        rw [hh_pres z (mem_ball_zero_iff.mpr hzlt) hzne, hzr, zpow_natCast]
        calc ‖w ^ q * z ^ r * u z‖ = ‖w‖ ^ q * ‖z‖ ^ r * ‖u z‖ := by
                rw [norm_mul, norm_mul, norm_zpow, norm_pow]
          _ ≤ ‖w‖ ^ q * 1 * Cu := by
                have h1 : ‖z‖ ^ r ≤ 1 := pow_le_one₀ (norm_nonneg z) (by linarith [hzlt, hρ1])
                have h2 : (0 : ℝ) ≤ ‖w‖ ^ q := zpow_nonneg (norm_nonneg w) q
                have h3 : ‖u z‖ ≤ Cu := (hu_bound z (mem_ball_zero_iff.mpr hzlt)).le
                gcongr
          _ = ‖w‖ ^ q * Cu := by ring
      have hsum : ‖traceZk h k w‖ ≤ (RS.setOf_pow_eq_finite hk w).toFinset.card * (‖w‖ ^ q * Cu) :=
          by
        rw [traceZk_apply_of_ne_zero hk hw0]
        calc ‖∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z‖
            ≤ ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖h z‖ := norm_sum_le _ _
          _ ≤ ∑ _z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖w‖ ^ q * Cu :=
              Finset.sum_le_sum hbound_term
          _ = (RS.setOf_pow_eq_finite hk w).toFinset.card * (‖w‖ ^ q * Cu) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (RS.setOf_pow_eq_finite hk w).toFinset.card = k := by
        rw [← Set.ncard_eq_toFinset_card _ (RS.setOf_pow_eq_finite hk w), RS.ncard_setOf_pow_eq hk
            hw0]
      rw [hcard] at hsum
      have hwnorm0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      change ‖w ^ (-q) * traceZk h k w‖ ≤ (k : ℝ) * Cu
      rw [norm_mul, norm_zpow]
      have hzp : (0 : ℝ) ≤ ‖w‖ ^ (-q) := zpow_nonneg (norm_nonneg w) (-q)
      have hcancel : ‖w‖ ^ (-q) * (‖w‖ ^ q * Cu) = Cu := by
        rw [← mul_assoc, ← zpow_add₀ hwnorm0, neg_add_cancel, zpow_zero, one_mul]
      nlinarith [hsum, hzp, mul_le_mul_of_nonneg_left hsum hzp]
    -- Step 6: Riemann's removable singularity theorem.
    have hd : DifferentiableOn ℂ V (Metric.ball (0 : ℂ) ρ' \ {0}) := fun z hz =>
      (hVan z hz).differentiableAt.differentiableWithinAt
    have hb : BddAbove ((norm ∘ V) '' (Metric.ball (0 : ℂ) ρ' \ {0})) :=
      ⟨(k : ℝ) * Cu, by rintro _ ⟨z, hz, rfl⟩; exact hVbound z hz⟩
    have hrep := Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds (0 : ℂ) hρ'0) hd hb
    have hanrep : AnalyticAt ℂ (Function.update V 0 (limUnder (𝓝[≠] (0 : ℂ)) V)) 0 :=
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hrep 0
        (Metric.mem_ball_self hρ'0)
    have hupdate_eq :
        Function.update V 0 (limUnder (𝓝[≠] (0 : ℂ)) V) =ᶠ[𝓝[≠] (0 : ℂ)] V := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact Function.update_of_ne hz _ _
    have hVmero : MeromorphicAt V 0 := hanrep.meromorphicAt.congr hupdate_eq
    -- Step 7: assemble.
    have hzpow_mero : MeromorphicAt (fun w : ℂ => w ^ q) 0 := by
      simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow q
    have hprod : MeromorphicAt (fun w => w ^ q * V w) 0 := hzpow_mero.mul hVmero
    exact hprod.congr hstep3.symm

/-! ### The Laurent-coefficient formula (P6)

Route (`tsum`-free; a sharpening of the file's previously recorded candidate route (b)): expand
the unit factor `u` of `h`'s order presentation `h =ᶠ[𝓝[≠]0] (·)^n₀ * u` by the EXACT pointwise
Taylor remainder `u = P + (·)^M * r` (`RS.AnalyticAt.exists_taylor_remainder`), choosing the
cutoff `M` so that `n₀ + M = k * s'` is an exact multiple of `k` with `s' > m`. Then, summing
over the root set of `z ^ k = w` (`w ≠ 0`):

* each monomial `z ^ (n₀ + d)` traces to the CLOSED FORM `k · w ^ ((n₀+d)/k)` if `k ∣ n₀ + d` and
  `0` otherwise (`traceZk_zpow`, the geometric-sum collapse — computed on the abstract root set
  via a single root and a primitive root of unity, no analytic branches);
* the remainder contributes `z ^ (n₀+M) * r z = w ^ s' * r z` EXACTLY (the whole point of the
  divisibility choice of `M` — `z ^ (k s') = (z^k)^{s'} = w^{s'}` per root), so the remainder
  term is `w ^ s' * traceZk r k w` with NO second growth bound needed; `traceZk r k` has an
  analytic repair at `0` (`exists_analyticAt_traceZk`, the bounded-case removable singularity),
  and `s' > m` makes it invisible to the `m`-th coefficient.

All coefficients are then read off by residue-calculus's presentation-independent
characterization `laurentCoeffAt_of_eventuallyEq` and the built linearity/shift API. -/

/-- Enumeration of the root set: for `w ≠ 0`, any single root `z₁` of `z ^ k = w` and any
primitive `k`-th root of unity `ζ` enumerate the root set bijectively as `i ↦ ζ ^ i * z₁`,
`i < k`. -/
private theorem bijOn_pow_mul_root (hk : k ≠ 0) {w z₁ ζ : ℂ} (hw : w ≠ 0)
    (hz₁ : z₁ ^ k = w) (hζ : IsPrimitiveRoot ζ k) :
    Set.BijOn (fun i : ℕ => ζ ^ i * z₁) ↑(Finset.range k) {z : ℂ | z ^ k = w} := by
  have hz₁0 : z₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk] at hz₁
    exact hw hz₁.symm
  have hmaps : ∀ i : ℕ, (ζ ^ i * z₁) ^ k = w := by
    intro i
    rw [mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hz₁]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i * z₁) ↑(Finset.range k) := hζ.injOn_pow_mul hz₁0
  refine ⟨fun i _ => hmaps i, hinj, fun z hz => ?_⟩
  have hsub : (fun i : ℕ => ζ ^ i * z₁) '' ↑(Finset.range k) ⊆ {z : ℂ | z ^ k = w} := by
    rintro _ ⟨i, _, rfl⟩
    exact hmaps i
  have hcard1 : ((fun i : ℕ => ζ ^ i * z₁) '' ↑(Finset.range k)).ncard = k := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  have heqset : (fun i : ℕ => ζ ^ i * z₁) '' ↑(Finset.range k) = {z : ℂ | z ^ k = w} :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [hcard1, RS.ncard_setOf_pow_eq hk hw]) (RS.setOf_pow_eq_finite hk w)
  rw [heqset]
  exact hz

/-- Closed form for the trace of a `zpow` monomial (`w ≠ 0`): the sum of `z ^ e` over the `k`
roots of `w` collapses by the geometric sum of roots of unity to `k * w ^ (e / k)` when `k ∣ e`
and to `0` otherwise. Purely algebraic — no branches, no analyticity. -/
theorem traceZk_zpow (hk : k ≠ 0) (e : ℤ) {w : ℂ} (hw : w ≠ 0) :
    traceZk (fun z => z ^ e) k w = if (k : ℤ) ∣ e then (k : ℂ) * w ^ (e / (k : ℤ)) else 0 := by
  classical
  obtain ⟨z₁, hz₁⟩ := RS.exists_pow_eq hk hw
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ k := ⟨_, Complex.isPrimitiveRoot_exp k hk⟩
  have hbij := bijOn_pow_mul_root hk hw hz₁ hζ
  have h1 : traceZk (fun z => z ^ e) k w = ∑ i ∈ Finset.range k, (ζ ^ i * z₁) ^ e := by
    rw [traceZk_def,
      ← finsum_mem_eq_of_bijOn (fun i : ℕ => ζ ^ i * z₁) hbij (fun i _ => rfl),
      finsum_mem_coe_finset]
  have h2 : ∀ i ∈ Finset.range k, (ζ ^ i * z₁) ^ e = (ζ ^ e) ^ i * z₁ ^ e := by
    intro i _
    rw [mul_zpow]
    congr 1
    rw [← zpow_natCast ζ i, ← zpow_mul, mul_comm (i : ℤ) e, zpow_mul, zpow_natCast]
  rw [h1, Finset.sum_congr rfl h2, ← Finset.sum_mul]
  by_cases hdvd : (k : ℤ) ∣ e
  · rw [ite_eq_left hdvd]
    have hζe : ζ ^ e = 1 := (hζ.zpow_eq_one_iff_dvd e).2 hdvd
    have hsum : ∑ i ∈ Finset.range k, (ζ ^ e) ^ i = (k : ℂ) := by
      rw [hζe]
      simp
    have hz₁e : z₁ ^ e = w ^ (e / (k : ℤ)) := by
      have hcancel : (k : ℤ) * (e / (k : ℤ)) = e := Int.mul_ediv_cancel' hdvd
      calc z₁ ^ e = z₁ ^ ((k : ℤ) * (e / (k : ℤ))) := by rw [hcancel]
        _ = (z₁ ^ (k : ℤ)) ^ (e / (k : ℤ)) := zpow_mul z₁ _ _
        _ = (z₁ ^ k) ^ (e / (k : ℤ)) := by rw [zpow_natCast]
        _ = w ^ (e / (k : ℤ)) := by rw [hz₁]
    rw [hsum, hz₁e]
  · rw [ite_eq_right hdvd]
    have hζe : ζ ^ e ≠ 1 := fun hone => hdvd ((hζ.zpow_eq_one_iff_dvd e).1 hone)
    have hpow1 : (ζ ^ e) ^ k = 1 := by
      rw [← zpow_natCast (ζ ^ e) k, ← zpow_mul, mul_comm e (k : ℤ), zpow_mul, zpow_natCast,
        hζ.pow_eq_one, one_zpow]
    rw [geom_sum_eq hζe, hpow1, sub_self, zero_div, zero_mul]

/-- Analytic repair of the trace of a bounded analytic function: if `g` is analytic and bounded
on a punctured ball at `0`, then `traceZk g k` agrees off `0` near `0` with a function honestly
analytic AT `0` (Riemann's removable-singularity theorem; the trivial-growth-bound special case
of P5's argument, promoted from a meromorphic to an analytic repair). -/
private theorem exists_analyticAt_traceZk (hk : k ≠ 0) {g : ℂ → ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ρ \ {0}))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) ρ \ {0}, ‖g z‖ ≤ C) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ traceZk g k =ᶠ[𝓝[≠] (0 : ℂ)] G := by
  have hρ'0 : 0 < ρ ^ k := pow_pos hρ k
  have hTan : ∀ w ∈ Metric.ball (0 : ℂ) (ρ ^ k) \ {0}, AnalyticAt ℂ (traceZk g k) w := by
    rintro w ⟨hw1, hw2⟩
    exact analyticAt_traceZk hk hρ hg hw2 (mem_ball_zero_iff.mp hw1)
  have hTbound : ∀ w ∈ Metric.ball (0 : ℂ) (ρ ^ k) \ {0},
      ‖traceZk g k w‖ ≤ (k : ℝ) * C := by
    rintro w ⟨hw1, hw2⟩
    have hw0 : w ≠ 0 := hw2
    have hwlt : ‖w‖ < ρ ^ k := mem_ball_zero_iff.mp hw1
    have hterm : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖g z‖ ≤ C := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have hzpow : z ^ k = w := hz
      have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ.le hzpow hwlt
      have hzne : z ≠ 0 := by
        rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
      exact hb z ⟨mem_ball_zero_iff.mpr hzlt, hzne⟩
    have hcard : (RS.setOf_pow_eq_finite hk w).toFinset.card = k := by
      rw [← Set.ncard_eq_toFinset_card _ (RS.setOf_pow_eq_finite hk w),
        RS.ncard_setOf_pow_eq hk hw0]
    calc ‖traceZk g k w‖ = ‖∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, g z‖ := by
          rw [traceZk_apply_of_ne_zero hk hw0]
      _ ≤ ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖g z‖ := norm_sum_le _ _
      _ ≤ ∑ _z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, C := Finset.sum_le_sum hterm
      _ = (k : ℝ) * C := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hd : DifferentiableOn ℂ (traceZk g k) (Metric.ball (0 : ℂ) (ρ ^ k) \ {0}) := fun z hz =>
    (hTan z hz).differentiableAt.differentiableWithinAt
  have hbdd : BddAbove ((norm ∘ traceZk g k) '' (Metric.ball (0 : ℂ) (ρ ^ k) \ {0})) :=
    ⟨(k : ℝ) * C, by rintro _ ⟨z, hz, rfl⟩; exact hTbound z hz⟩
  have hrep := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) hρ'0) hd hbdd
  refine ⟨Function.update (traceZk g k) 0 (limUnder (𝓝[≠] (0 : ℂ)) (traceZk g k)),
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hrep 0
      (Metric.mem_ball_self hρ'0), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (Function.update_of_ne hz _ _).symm

/-- THE Laurent-coefficient formula for `traceZk` (P6): tracing along `z ↦ z ^ k` keeps exactly
every `k`-th Laurent coefficient, scaled by `k`. See the section header for the proof route. -/
theorem laurentCoeffAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) (m : ℤ) :
    laurentCoeffAt (traceZk h k) 0 m = (k : ℂ) * laurentCoeffAt h 0 (k * m) := by
  classical
  by_cases hordtop : meromorphicOrderAt h 0 = ⊤
  · -- Degenerate case: `h` vanishes near `0`, hence so does `traceZk h k`; both sides are `0`.
    have hh0 : h =ᶠ[𝓝[≠] (0 : ℂ)] 0 := meromorphicOrderAt_eq_top_iff.1 hordtop
    obtain ⟨ρ, hρ0, hρsub⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hh0)
    have htrace0 : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      have hballmem : Metric.ball (0 : ℂ) (ρ ^ k) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (pow_pos hρ0 k)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hballmem, self_mem_nhdsWithin]
        with w hwball hwne
      have hw0 : w ≠ 0 := hwne
      change traceZk h k w = 0
      rw [traceZk_apply_of_ne_zero hk hw0]
      apply Finset.sum_eq_zero
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have hzpow : z ^ k = w := hz
      have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ0.le hzpow (mem_ball_zero_iff.mp hwball)
      have hzne : z ≠ 0 := by
        rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
      exact hρsub z (mem_ball_zero_iff.mpr hzlt) hzne
    rw [laurentCoeffAt_congr htrace0 m, laurentCoeffAt_zero_fun,
      laurentCoeffAt_of_order_eq_top hordtop, mul_zero]
  · -- Main case: order presentation `h =ᶠ[𝓝[≠]0] z ↦ z ^ n₀ * u z`, `u` analytic at `0`.
    obtain ⟨u, hu, -, hu_eq⟩ := (meromorphicOrderAt_ne_top_iff hh).1 hordtop
    generalize hn₀_def : (meromorphicOrderAt h 0).untop₀ = n₀ at hu_eq
    have hpres : h =ᶠ[𝓝[≠] (0 : ℂ)] fun z => (z - 0) ^ n₀ * u z := by
      filter_upwards [hu_eq] with z hz
      rw [hz, smul_eq_mul]
    have hu_eq' : h =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ n₀ * u z := by
      filter_upwards [hpres] with z hz
      rw [hz, sub_zero]
    -- The right-hand side, via the presentation-independent characterization.
    have hRHS : laurentCoeffAt h 0 ((k : ℤ) * m)
        = if n₀ ≤ (k : ℤ) * m then taylorCoeffAt u 0 ((k : ℤ) * m - n₀).toNat else 0 :=
      laurentCoeffAt_of_eventuallyEq hu hpres ((k : ℤ) * m)
    -- Cutoff choice: `n₀ + M = k * s'`, an exact multiple of `k`, with `s' > m`.
    have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    set s' : ℤ := max (m + 1) (max n₀ 0) with hs'_def
    have hms' : m < s' := lt_of_lt_of_le (lt_add_one m) (le_max_left _ _)
    have hs'0 : 0 ≤ s' := le_trans (le_max_right n₀ 0) (le_max_right _ _)
    have hn₀s' : n₀ ≤ s' := le_trans (le_max_left n₀ 0) (le_max_right _ _)
    have hks' : n₀ ≤ (k : ℤ) * s' :=
      le_trans hn₀s' (le_mul_of_one_le_left hs'0 (by omega : (1 : ℤ) ≤ (k : ℤ)))
    set M : ℕ := ((k : ℤ) * s' - n₀).toNat with hM_def
    have hMz : (M : ℤ) = (k : ℤ) * s' - n₀ := Int.toNat_of_nonneg (sub_nonneg.mpr hks')
    have hn₀M : n₀ + (M : ℤ) = (k : ℤ) * s' := by rw [hMz]; ring
    -- Exact Taylor remainder of the unit factor.
    obtain ⟨r, hran, -, hrep⟩ := RS.AnalyticAt.exists_taylor_remainder hu M
    -- Analytic repair `G` of the remainder trace `traceZk r k` at `0`.
    have hrball : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ r z ∧ ‖r z‖ ≤ ‖r 0‖ + 1 := by
      have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ r z := hran.eventually_analyticAt
      have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖r z‖ < ‖r 0‖ + 1 :=
        hran.continuousAt.norm.tendsto.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [h1, h2] with z h1z h2z
      exact ⟨h1z, h2z.le⟩
    obtain ⟨ρ₁, hρ₁0, hρ₁sub⟩ := Metric.eventually_nhds_iff_ball.mp hrball
    obtain ⟨G, hGan, hGeq⟩ := exists_analyticAt_traceZk hk hρ₁0
      (fun z hz => (hρ₁sub z hz.1).1) (fun z hz => (hρ₁sub z hz.1).2)
    -- The monomial-trace main term.
    set T : ℕ → ℂ → ℂ := fun d w => taylorCoeffAt u 0 d *
      (if (k : ℤ) ∣ (n₀ + (d : ℤ)) then (k : ℂ) * w ^ ((n₀ + (d : ℤ)) / (k : ℤ)) else 0)
      with hT_def
    -- Validity ball of the order presentation.
    obtain ⟨ρ₂, hρ₂0, hρ₂sub⟩ :=
      Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hu_eq')
    -- THE master eventual identity.
    have hkey : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)]
        fun w => (∑ d ∈ Finset.range M, T d w) + w ^ s' * G w := by
      have hball : Metric.ball (0 : ℂ) (ρ₂ ^ k) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (pow_pos hρ₂0 k)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin, hGeq]
        with w hwball hwne hGw
      have hw0 : w ≠ 0 := hwne
      have hwlt : ‖w‖ < ρ₂ ^ k := mem_ball_zero_iff.mp hwball
      -- Per-root expansion of `h` through the exact Taylor remainder.
      have hroot : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset,
          h z = (∑ d ∈ Finset.range M, taylorCoeffAt u 0 d * z ^ (n₀ + (d : ℤ)))
            + w ^ s' * r z := by
        intro z hz
        rw [Set.Finite.mem_toFinset] at hz
        have hzpow : z ^ k = w := hz
        have hzlt : ‖z‖ < ρ₂ := RS.norm_lt_of_pow_eq hk hρ₂0.le hzpow hwlt
        have hzne : z ≠ 0 := by
          rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
        have hexp : ∀ d : ℕ, z ^ n₀ * z ^ d = z ^ (n₀ + (d : ℤ)) := by
          intro d
          rw [← zpow_natCast z d, ← zpow_add₀ hzne]
        have hzM : z ^ n₀ * (z ^ M * r z) = w ^ s' * r z := by
          rw [← mul_assoc]
          congr 1
          calc z ^ n₀ * z ^ M = z ^ (n₀ + (M : ℤ)) := hexp M
            _ = z ^ ((k : ℤ) * s') := by rw [hn₀M]
            _ = (z ^ (k : ℤ)) ^ s' := zpow_mul z _ _
            _ = w ^ s' := by rw [zpow_natCast, hzpow]
        calc h z = z ^ n₀ * u z := hρ₂sub z (mem_ball_zero_iff.mpr hzlt) hzne
          _ = z ^ n₀ * ((∑ d ∈ Finset.range M, taylorCoeffAt u 0 d * (z - 0) ^ d)
              + (z - 0) ^ M * r z) := by rw [← hrep z]
          _ = (∑ d ∈ Finset.range M, taylorCoeffAt u 0 d * z ^ (n₀ + (d : ℤ)))
              + w ^ s' * r z := by
            simp only [sub_zero]
            rw [mul_add, Finset.mul_sum, hzM]
            congr 1
            exact Finset.sum_congr rfl fun d _ => by rw [← hexp d]; ring
      -- Assemble the trace as main term + remainder term.
      have hsum : traceZk h k w
          = (∑ d ∈ Finset.range M,
              taylorCoeffAt u 0 d * traceZk (fun z => z ^ (n₀ + (d : ℤ))) k w)
            + w ^ s' * traceZk r k w := by
        rw [traceZk_apply_of_ne_zero hk hw0, Finset.sum_congr rfl hroot,
          Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d _ => by
            rw [traceZk_apply_of_ne_zero hk hw0, Finset.mul_sum]
        · rw [← Finset.mul_sum, traceZk_apply_of_ne_zero hk hw0]
      change traceZk h k w = (∑ d ∈ Finset.range M, T d w) + w ^ s' * G w
      rw [hsum, ← hGw]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [hT_def]
      rw [traceZk_zpow hk (n₀ + (d : ℤ)) hw0]
    -- Meromorphy and Laurent coefficients of the pieces.
    have hterm_mero : ∀ d ∈ Finset.range M, MeromorphicAt (T d) 0 := by
      intro d _
      simp only [hT_def]
      by_cases hdvd : (k : ℤ) ∣ (n₀ + (d : ℤ))
      · simp only [ite_eq_left hdvd]
        have h1 : MeromorphicAt (fun w : ℂ => w ^ ((n₀ + (d : ℤ)) / (k : ℤ))) 0 := by
          simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow ((n₀ + (d : ℤ)) / (k : ℤ))
        exact (MeromorphicAt.const _ _).mul ((MeromorphicAt.const _ _).mul h1)
      · simp only [ite_eq_right hdvd, mul_zero]
        exact MeromorphicAt.const 0 0
    have hterm_coeff : ∀ d ∈ Finset.range M, laurentCoeffAt (T d) 0 m
        = if n₀ + (d : ℤ) = (k : ℤ) * m then (k : ℂ) * taylorCoeffAt u 0 d else 0 := by
      intro d _
      simp only [hT_def]
      by_cases hdvd : (k : ℤ) ∣ (n₀ + (d : ℤ))
      · simp only [ite_eq_left hdvd]
        have hk0' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
        have hmono : laurentCoeffAt (fun w : ℂ => w ^ ((n₀ + (d : ℤ)) / (k : ℤ))) 0 m
            = if m = (n₀ + (d : ℤ)) / (k : ℤ) then 1 else 0 := by
          have hfun : (fun w : ℂ => w ^ ((n₀ + (d : ℤ)) / (k : ℤ)))
              = fun w : ℂ => (w - 0) ^ ((n₀ + (d : ℤ)) / (k : ℤ)) := by
            funext w
            rw [sub_zero]
          rw [hfun, laurentCoeffAt_zpow_monomial]
        rw [laurentCoeffAt_const_mul, laurentCoeffAt_const_mul, hmono]
        by_cases hcase : n₀ + (d : ℤ) = (k : ℤ) * m
        · rw [ite_eq_left hcase,
            ite_eq_left (by rw [hcase, Int.mul_ediv_cancel_left m hk0']), mul_one]
          ring
        · rw [ite_eq_right hcase, ite_eq_right (fun hcon => hcase
            (by rw [hcon]; exact (Int.mul_ediv_cancel' hdvd).symm)), mul_zero, mul_zero]
      · simp only [ite_eq_right hdvd, mul_zero]
        rw [laurentCoeffAt_zero_fun, ite_eq_right]
        intro hcon
        exact hdvd ⟨m, hcon⟩
    have hPmero : MeromorphicAt (fun w => ∑ d ∈ Finset.range M, T d w) 0 :=
      MeromorphicAt.fun_sum hterm_mero
    have hBmero : MeromorphicAt (fun w : ℂ => w ^ s' * G w) 0 := by
      have h1 : MeromorphicAt (fun w : ℂ => w ^ s') 0 := by
        simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow s'
      exact h1.mul hGan.meromorphicAt
    have hB : laurentCoeffAt (fun w : ℂ => w ^ s' * G w) 0 m = 0 := by
      have hBpres : (fun w : ℂ => w ^ s' * G w) =ᶠ[𝓝[≠] (0 : ℂ)]
          fun w => (w - 0) ^ s' * G w := by
        filter_upwards with w
        rw [sub_zero]
      rw [laurentCoeffAt_of_eventuallyEq hGan hBpres m, ite_eq_right (by omega : ¬ s' ≤ m)]
    -- Final assembly.
    rw [laurentCoeffAt_congr hkey m, laurentCoeffAt_fun_add hPmero hBmero m, hB, add_zero,
      laurentCoeffAt_fun_sum hterm_mero m, Finset.sum_congr rfl hterm_coeff, hRHS]
    by_cases hcase : n₀ ≤ (k : ℤ) * m
    · set d₀ : ℕ := ((k : ℤ) * m - n₀).toNat with hd₀_def
      have hd₀z : (d₀ : ℤ) = (k : ℤ) * m - n₀ := Int.toNat_of_nonneg (sub_nonneg.mpr hcase)
      have hd₀M : d₀ < M := by
        have h1 : (d₀ : ℤ) < (M : ℤ) := by
          rw [hd₀z, hMz]
          have hkm : (k : ℤ) * m < (k : ℤ) * s' := mul_lt_mul_of_pos_left hms' hkpos
          linarith
        exact_mod_cast h1
      have hcond : ∀ d : ℕ, (n₀ + (d : ℤ) = (k : ℤ) * m) ↔ d = d₀ := by
        intro d
        constructor
        · intro hcon
          have hz : (d : ℤ) = (d₀ : ℤ) := by rw [hd₀z]; linarith
          exact_mod_cast hz
        · rintro rfl
          rw [hd₀z]; ring
      rw [ite_eq_left hcase]
      calc ∑ d ∈ Finset.range M,
            (if n₀ + (d : ℤ) = (k : ℤ) * m then (k : ℂ) * taylorCoeffAt u 0 d else 0)
          = ∑ d ∈ Finset.range M,
            (if d = d₀ then (k : ℂ) * taylorCoeffAt u 0 d else 0) :=
            Finset.sum_congr rfl fun d _ => by rw [if_congr (hcond d) rfl rfl]
        _ = if d₀ ∈ Finset.range M then (k : ℂ) * taylorCoeffAt u 0 d₀ else 0 :=
            Finset.sum_ite_eq' _ _ _
        _ = (k : ℂ) * taylorCoeffAt u 0 d₀ := by
            rw [ite_eq_left (Finset.mem_range.mpr hd₀M)]
    · rw [ite_eq_right hcase, mul_zero]
      apply Finset.sum_eq_zero
      intro d _
      apply ite_eq_right
      intro hcon
      rw [not_le] at hcase
      have hd0 : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
      linarith

/-- Residue corollary of P6 (design §4.4): the residue of the trace is `k` times `h`'s
coefficient at index `-k` — NOT `h`'s residue unless `k = 1`. (Miranda's residue identity
`Res(Tr(h·ω)) = ∑ Res(h·ω)` needs the form's Jacobian factor to compensate this shift; that is
`form-trace-tower`'s job, confirming the scope split.) -/
theorem resAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    resAt (traceZk h k) 0 = (k : ℂ) * laurentCoeffAt h 0 (-(k : ℤ)) := by
  have h1 := laurentCoeffAt_traceZk hh hk (-1)
  rw [mul_neg_one] at h1
  exact h1

end RS.MTrace
