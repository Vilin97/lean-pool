/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeRetention
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeRoundCheb
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Pruning
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the sharp round: transporting the Efron–Stein
variance to the cube retention

`LeanPool.AsymptoticTrianglePacking.Internal.safeDegCube_variance_le`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpVariance`) is the sharp per-vertex
safe-degree variance bound on the elementary Bernoulli cube.  Here it is transported to the
`LeanPool.AsymptoticTrianglePacking.Internal.BernoulliRetention` carried by that cube
(`LeanPool.AsymptoticTrianglePacking.Internal.cubeRetention`), which is the form the
Chebyshev round `LeanPool.AsymptoticTrianglePacking.Internal.exists_safe_round_cheb` consumes.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The sharp per-vertex safe-degree variance, in integral form.** -/
theorem integral_centered_safeDegree_cube_le
    (K : Finset (Finset V)) {r Δ κ : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform K r) (hΔ : ∀ y : V, degree K y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ) (v : V) :
    ∫ ω, ((safeDegree K (covered (@retainedSet V _ (Finset V → Bool) (Cube.cubeSpace p) K p
              (cubeRetention K hp0 hp1) ω)) v : ℝ)
        - @safeDegMean V _ (Finset V → Bool) (Cube.cubeSpace p) K p (cubeRetention K hp0 hp1) v) ^ 2
        ∂(Cube.cubeMeasure p)
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  have hret : ∀ ω : Finset V → Bool,
      (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        = safeDegCube K v ω := by
    intro ω
    rw [retainedSet_cubeRetention]
    rfl
  have hmean : safeDegMean (cubeRetention K hp0 hp1) v = Cube.Exp p (safeDegCube K v) := by
    rw [← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
    change ∫ ω, (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        ∂(Cube.cubeMeasure p) = _
    rw [Cube.integral_cubeMeasure hp0 hp1]
    exact congrArg _ (funext hret)
  have hrw : ∫ ω, ((safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        - safeDegMean (cubeRetention K hp0 hp1) v) ^ 2 ∂(Cube.cubeMeasure p)
      = Cube.Exp p (fun ω => (safeDegCube K v ω - Cube.Exp p (safeDegCube K v)) ^ 2) := by
    rw [Cube.integral_cubeMeasure hp0 hp1]
    exact congrArg _ (funext fun ω => by rw [hret ω, hmean])
  rw [hrw]
  exact safeDegCube_variance_le hp0 hp1 hr hΔ hκ v


theorem safeDegMean_cubeRetention (K : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : V) :
    @safeDegMean V _ (Finset V → Bool) (Cube.cubeSpace p) K p (cubeRetention K hp0 hp1) v
      = Cube.Exp p (safeDegCube K v) := by
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  change ∫ ω, (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
      ∂(Cube.cubeMeasure p) = _
  rw [Cube.integral_cubeMeasure hp0 hp1]
  refine congrArg _ (funext fun ω => ?_)
  rw [retainedSet_cubeRetention]
  rfl

/-! ## The sharp round on an active set

The whole probabilistic content of the sharp round.  Everything that is not a deterministic
estimate of the MEAN safe degree `Cube.Exp p (safeDegCube K v)` is discharged here: the safe degree
is pinned to within `t` of its mean off an exceptional set of size `< a`, and the round covers more
than `Q/2` vertices, where `Q = |A|·δp(1−p)^{rΔ}` uses the degree floor only on the active set. -/

/-- **The sharp Chebyshev round on an active set.**  Given ANY two-sided estimate `mlo ≤ mean ≤ mhi`
for the mean safe degree on `A`, and the smallness condition, one round leaves every active,
uncovered vertex outside an exceptional set of size `< a` with residual degree in
`[mlo − t, mhi + t]`, and covers more than `Q/2` vertices.

The variance input is the SHARP Efron–Stein bound
`LeanPool.AsymptoticTrianglePacking.Internal.safeDegCube_variance_le`:
`Vs = 2p·r²κΔ²(1 + prΔ + (prΔ)²)`, which carries NO `Δ²` term at `p = γ/(rΔ)`. -/
theorem exists_sharp_round_band {K : Finset (Finset V)} (A : Finset V) {r Δ δ κ : ℕ}
    {p t a mlo : ℝ} {mhi : V → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr1 : 1 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (hδA : ∀ y ∈ A, δ ≤ degree K y)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ)
    (ht : 0 < t) (ha : 0 < a) (hδ0 : 0 < δ) (hA : 0 < A.card)
    (hlo : ∀ v ∈ A, mlo ≤ Cube.Exp p (safeDegCube K v))
    (hhi : ∀ v ∈ A, Cube.Exp p (safeDegCube K v) ≤ mhi v)
    (hsmall :
      ((Fintype.card V : ℝ) *
          ((2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
            * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2)) / t ^ 2)) / a
        + ((Fintype.card V : ℝ) * ((Δ : ℝ) * p)
            + (Fintype.card V : ℝ) ^ 2
              * ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3))
          / ((A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2) ^ 2 < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ K ∧ ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∈ A, v ∉ B → v ∉ covered R' →
        mlo - t ≤ (degree (Hypergraph.residual K R') v : ℝ)
        ∧ (degree (Hypergraph.residual K R') v : ℝ) ≤ mhi v + t) ∧
      (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2 < ((covered R').card : ℝ) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0.le hp1.le
  set ρ := cubeRetention K hp0.le hp1.le with hρ
  have hqlo : ∀ v ∈ A, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate K p v := by
    intro v hv
    refine le_trans ?_ (coverRate_ge hp0.le hp1.le hr hΔ v)
    have hd : (δ : ℝ) ≤ (degree K v : ℝ) := by exact_mod_cast hδA v hv
    exact mul_le_mul_of_nonneg_right hd (mul_nonneg hp0.le (pow_nonneg (by linarith) _))
  have hqlo0 : (0 : ℝ) < (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have : (0 : ℝ) < (1 - p) ^ (r * Δ) := pow_pos (by linarith) _
    positivity
  have hAR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA
  have hQ : (0 : ℝ) < (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) := mul_pos hAR hqlo0
  have hmean : (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) ≤ ∑ v : V, coverRate K p v := by
    have hnn : ∀ v : V, 0 ≤ coverRate K p v := fun v => coverRate_nonneg hp0.le hp1.le v
    calc (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
        = ∑ _v ∈ A, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ A, coverRate K p v := Finset.sum_le_sum hqlo
      _ ≤ ∑ v : V, coverRate K p v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun v _ _ => hnn v)
  have hqhi : ∀ u : V, coverRate K p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0.le hp1.le u) ?_
    have : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0.le
  have hε0 : (0 : ℝ) ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0.le
    have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hp0.le 3)
    linarith
  have hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure (Finset V → Bool)).real ({ω | u ∈ covered (retainedSet K ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet K ρ ω)})
        - coverRate K p u * coverRate K p u'
      ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
    fun u u' huu' => pair_excess_le_codegree ρ hp0.le hp1.le hr hr1 hΔ hκ huu'
  have hvar := coveredCount_variance_le ρ hp0.le hp1.le hqhi hε0 hpair
  have hVs : ∀ v : V, ∫ ω, ((safeDegree K (covered (retainedSet K ρ ω)) v : ℝ)
      - safeDegMean ρ v) ^ 2 ∂(ℙ : Measure (Finset V → Bool))
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) :=
    fun v => integral_centered_safeDegree_cube_le K hp0.le hp1.le hr hΔ hκ v
  obtain ⟨ω, B, hBcard, hband, hcov⟩ :=
    exists_safe_round_cheb ρ ht ha hQ hVs hmean hvar hsmall
  refine ⟨retainedSet K ρ ω, Finset.filter_subset _ _, B, hBcard, ?_, hcov⟩
  intro v hvA hvB hvc
  have hb := hband v hvB
  rw [safeDegree_eq_residual_degree_of_not_covered hvc,
    safeDegMean_cubeRetention K hp0.le hp1.le v] at hb
  have habs := abs_lt.mp hb
  exact ⟨by linarith only [hlo v hvA, habs.1], by linarith only [hhi v hvA, habs.2]⟩


/-! ## The deterministic mean estimates -/

/-- **Floor for the mean safe degree** (union bound on the covering events). -/
theorem Exp_safeDegCube_ge {K : Finset (Finset V)} {r Δ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (v : V) :
    (degree K v : ℝ) * (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p)) ≤ Cube.Exp p (safeDegCube K v) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← safeDegMean_cubeRetention K hp0 hp1 v, ← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  refine le_trans ?_ (safeDegree_expectation_ge (cubeRetention K hp0 hp1) hp0 hp1 v)
  have hqhi : ∀ u : V, coverRate K p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0 hp1 u) ?_
    have : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0
  have hstep : ∀ e ∈ K.filter (fun e => v ∈ e),
      1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p) ≤ 1 - ∑ u ∈ e.erase v, coverRate K p u := by
    intro e he
    rw [Finset.mem_filter] at he
    have hcard : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem he.2, hr e he.1]
    have hsum : ∑ u ∈ e.erase v, coverRate K p u ≤ ((r : ℝ) - 1) * ((Δ : ℝ) * p) := by
      calc ∑ u ∈ e.erase v, coverRate K p u ≤ ∑ _u ∈ e.erase v, (Δ : ℝ) * p :=
            Finset.sum_le_sum fun u _ => hqhi u
        _ = ((e.erase v).card : ℝ) * ((Δ : ℝ) * p) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((r : ℝ) - 1) * ((Δ : ℝ) * p) := by
            rw [hcard]
            congr 1
            have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
              have : (1 : ℕ) ≤ r := hr1
              push_cast [Nat.cast_sub this]
              ring
            exact this
    linarith
  calc (degree K v : ℝ) * (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p))
      = ∑ _e ∈ K.filter (fun e => v ∈ e), (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ e ∈ K.filter (fun e => v ∈ e), (1 - ∑ u ∈ e.erase v, coverRate K p u) :=
        Finset.sum_le_sum hstep

/-- **Ceiling for the mean safe degree** (second Bonferroni inequality), with the degree floor
used only on the active set `A`: the drop is carried by the `deg(v) − lostDegree K Aᶜ v` edges at
`v` that stay inside `A`. -/
theorem Exp_safeDegCube_le {K : Finset (Finset V)} (A : Finset V) {r Δ δ κ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr2 : 2 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (hδA : ∀ y ∈ A, δ ≤ degree K y)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ) (v : V) :
    Cube.Exp p (safeDegCube K v)
      ≤ (degree K v : ℝ)
        - ((degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ))
            * (((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
        + (degree K v : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2))
            * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← safeDegMean_cubeRetention K hp0 hp1 v, ← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  refine le_trans (safeDegree_expectation_le (cubeRetention K hp0 hp1) hp0 hp1 v) ?_
  set S := K.filter (fun e => v ∈ e) with hS
  set G := S.filter (fun e => Disjoint e Aᶜ) with hG
  set W : ℝ := ((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) with hW
  set E : ℝ := (((r : ℝ) - 1) * ((r : ℝ) - 2)) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) with hE
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr2
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    push_cast [Nat.cast_sub hr1]; ring
  have hLnn : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hWnn : 0 ≤ W := by rw [hW]; exact mul_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) δ]) hLnn
  -- the pair correction of a single edge
  have hpair : ∀ e ∈ S, ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
      ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p) ≤ E := by
    intro e he
    rw [hS, Finset.mem_filter] at he
    have hcard : (e.erase v).card = r - 1 := by rw [Finset.card_erase_of_mem he.2, hr e he.1]
    have hterm : ∀ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
        ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
        ≤ ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
      intro u hu
      have hcard2 : ((e.erase v).erase u).card = r - 2 := by
        rw [Finset.card_erase_of_mem hu, hcard]; omega
      have hb : ∀ u' ∈ (e.erase v).erase u,
          ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
            ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by
        intro u' hu'
        have hne : u ≠ u' := (Finset.ne_of_mem_erase hu').symm
        have h1 : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
        have h2 : (degree K u' : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u'
        have h3 : (codegree K u u' : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' hne
        have h4 : (0 : ℝ) ≤ (degree K u : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ (degree K u' : ℝ) := Nat.cast_nonneg _
        have h6 : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
        have hd : (degree K u : ℝ) * (degree K u' : ℝ) ≤ (Δ : ℝ) * (Δ : ℝ) :=
          mul_le_mul h1 h2 h5 (Nat.cast_nonneg _)
        have hc : (codegree K u u' : ℝ) * p ≤ (κ : ℝ) * p :=
          mul_le_mul_of_nonneg_right h3 hp0
        nlinarith only [hd, hc]
      calc ∑ u' ∈ (e.erase v).erase u,
            ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
          ≤ ∑ _u' ∈ (e.erase v).erase u, ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
            Finset.sum_le_sum hb
        _ = (((e.erase v).erase u).card : ℝ) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [hcard2]
            have : (((r - 2 : ℕ)) : ℝ) = (r : ℝ) - 2 := by push_cast [Nat.cast_sub hr2]; ring
            rw [this]
    calc ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
          ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
        ≤ ∑ _u ∈ e.erase v, ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
          Finset.sum_le_sum hterm
      _ = ((r : ℝ) - 1) * (((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard, hcast]
      _ = E := by rw [hE]; ring
  -- the covering-rate floor on good edges
  have hgood : ∀ e ∈ G, W ≤ ∑ u ∈ e.erase v, coverRate K p u := by
    intro e he
    rw [hG, Finset.mem_filter, hS, Finset.mem_filter] at he
    obtain ⟨⟨heK, hve⟩, hdisj⟩ := he
    have hcard : (e.erase v).card = r - 1 := by rw [Finset.card_erase_of_mem hve, hr e heK]
    have hsub : ∀ u ∈ e.erase v, u ∈ A := by
      intro u hu
      by_contra hA
      exact (Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase hu))
        (Finset.mem_compl.mpr hA)
    have hb : ∀ u ∈ e.erase v, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate K p u := by
      intro u hu
      refine le_trans ?_ (coverRate_ge hp0 hp1 hr hΔ u)
      have hd : (δ : ℝ) ≤ (degree K u : ℝ) := by exact_mod_cast hδA u (hsub u hu)
      exact mul_le_mul_of_nonneg_right hd hLnn
    calc W = ((e.erase v).card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) := by
          rw [hcard, hcast, hW]; ring
      _ = ∑ _u ∈ e.erase v, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ e.erase v, coverRate K p u := Finset.sum_le_sum hb
  -- assemble
  have hnonneg : ∀ e ∈ S, (0 : ℝ) ≤ ∑ u ∈ e.erase v, coverRate K p u :=
    fun _ _ => Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hbound : ∀ e ∈ S,
      (1 - ∑ u ∈ e.erase v, coverRate K p u
        + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
            ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p))
      ≤ 1 - (if Disjoint e Aᶜ then W else 0) + E := by
    intro e he
    have h1 := hpair e he
    by_cases hd : Disjoint e Aᶜ
    · have h2 := hgood e (by rw [hG, Finset.mem_filter]; exact ⟨he, hd⟩)
      rw [ite_eq_left hd]; linarith
    · rw [ite_eq_right hd]; linarith [hnonneg e he]
  have hsum : ∑ e ∈ S, (1 - (if Disjoint e Aᶜ then W else 0) + E)
      = (degree K v : ℝ) - (G.card : ℝ) * W + (degree K v : ℝ) * E := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hGcard : (G.card : ℝ) = (degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ) := by
    have hsplit : S.card = G.card + (S.filter (fun e => ¬ Disjoint e Aᶜ)).card := by
      rw [hG]
      exact (Finset.card_filter_add_card_filter_not (p := fun e => Disjoint e Aᶜ)).symm
    have hlost : (S.filter (fun e => ¬ Disjoint e Aᶜ)).card = lostDegree K Aᶜ v := by
      rw [lostDegree, hS, Finset.filter_filter]
    have hSc : S.card = degree K v := rfl
    have : degree K v = G.card + lostDegree K Aᶜ v := by rw [← hSc, hsplit, hlost]
    rw [this]; push_cast; ring
  calc ∑ e ∈ S,
        (1 - ∑ u ∈ e.erase v, coverRate K p u
          + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
              ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p))
      ≤ ∑ e ∈ S, (1 - (if Disjoint e Aᶜ then W else 0) + E) := Finset.sum_le_sum hbound
    _ = (degree K v : ℝ) - (G.card : ℝ) * W + (degree K v : ℝ) * E := hsum
    _ = (degree K v : ℝ)
          - ((degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ))
              * (((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
          + (degree K v : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2))
              * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
        rw [hGcard, hE, hW]; ring

end LeanPool.AsymptoticTrianglePacking.Internal
