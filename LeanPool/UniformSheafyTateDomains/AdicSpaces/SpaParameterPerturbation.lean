/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AffinoidRings

/-!
# Parameter perturbation for rational subsets (Kedlaya Ex. 1.2.2 / Huber's approximation)

The uniform-bound and perturbation lemmas behind Wedhorn Proposition 7.48 /
[Hu2] Proposition 3.9 and Kedlaya (AWS 2017) Exercise 1.2.2: over a topological
ring `B` with a topologically nilpotent unit `ϖ` and a ring of integral elements
`B⁺`,

* `not_one_vle_of_topologicallyNilpotent` — a continuous valuation is `< 1` on a
  topologically nilpotent element (in `vle`-language: `¬ v.vle 1 ϖ`).
* `exists_pow_mul_mem_plusSubring` — for every `x : B` some `ϖ^k · x` lands in
  the (open) `B⁺`.
* `Spv.exists_sum_vle` — the ultrametric maximum principle for finite sums.
* `exists_uniform_spanning_bound` — if a finite `T` spans the unit ideal, there
  is a **uniform** `M` with `v(ϖ^M) ≤ max_{t ∈ T} v(t)` for *every* `v ∈ Spa B B⁺`
  (the coefficients of a spanning combination are absorbed into `B⁺` by `ϖ^M`).
* `indexedRationalSet_perturb_eq` — the **subset-equality half** of Kedlaya
  Exercise 1.2.2: perturbing the parameters of a rational-subset presentation by
  elements of `ϖ^(M+1) · B⁺` (with `M` a uniform spanning bound) does not change
  the subset. The proof is the classical ultrametric argument
  (`Valuation.map_add_of_distinct_val`) run through each point's canonical
  valuation.

**Scope note.** Exercise 1.2.2 also asserts that the *perturbed parameters
still generate the unit ideal*; that span-preservation half is proved in
`SpaSpanPerturbation.lean` (`exists_parameterPerturbation_span_top`,
2026-07-20). This file delivers the subset-equality statement, which is what
the Wedhorn 8.2(2) openness argument consumes; the direct Tate proof of the
rational-subset correspondence (`SpaRationalSubsetCorrespondence.lean`) instead
enforces downstairs span-top by padding with a dominated unit power, so it does
not consume the span-preservation theorem.

These are stated for arbitrary index families (`indexedRationalSet`), with
`indexedRationalSet_eq_rationalOpen` translating to the project's
`rationalOpen (s.image f) g`.

## Reference

Kedlaya, *Sheaves, stacks, and shtukas* (AWS 2017), Exercise 1.2.2; Wedhorn,
*Adic Spaces*, Proposition 7.48 (deferred there to [Hu2] Prop. 3.9); the
uniform bound is the standard "absorb the spanning coefficients" argument.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace ValuationSpectrum

universe u v

variable {B : Type u} [CommRing B] [TopologicalSpace B]

/-! ### `vle` toolkit (per-point wrappers of the `ValuativeRel` calculus) -/

/-- Transitivity of `vle` at a point. -/
theorem Spv.vleTrans {v : Spv B} {a b c : B} (h₁ : v.vle a b) (h₂ : v.vle b c) :
    v.vle a c :=
  @ValuativeRel.vle_trans B _ v.toValuativeRel c b a h₁ h₂

/-- The ultrametric axiom at a point. -/
theorem Spv.vleAdd {v : Spv B} {x y z : B} (hx : v.vle x z) (hy : v.vle y z) :
    v.vle (x + y) z :=
  @ValuativeRel.vle_add B _ v.toValuativeRel x y z hx hy

/-- The ultrametric maximum principle for finite sums: a finite sum is
`vle`-dominated by one of its terms (or the sum is empty and `0 ≤ᵥ` anything). -/
theorem Spv.exists_sum_vle {ι : Type v} (v : Spv B) {s : Finset ι} (hs : s.Nonempty)
    (t : ι → B) : ∃ i ∈ s, v.vle (∑ j ∈ s, t j) (t i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    rcases @ValuativeRel.vle_add_cases B _ v.toValuativeRel (t a) (∑ j ∈ s, t j)
      with h | h
    · exact ⟨a, Finset.mem_cons_self a s, h⟩
    · rcases s.eq_empty_or_nonempty with rfl | hs'
      · refine ⟨a, Finset.mem_cons_self a ∅, ?_⟩
        simp only [Finset.sum_empty, add_zero]
        exact @ValuativeRel.vle_refl B _ v.toValuativeRel (t a)
      · obtain ⟨i, hi, hvle⟩ := ih hs'
        exact ⟨i, Finset.mem_cons_of_mem hi, Spv.vleTrans h hvle⟩

/-- A continuous valuation is `< 1` on a topologically nilpotent element:
`¬ v(1) ≤ v(ϖ)`. (Wedhorn Corollary 7.9-adjacent.) -/
theorem not_one_vle_of_topologicallyNilpotent {v : Spv B} (hv : v.IsContinuous)
    {ϖ : B} (hϖ : IsTopologicallyNilpotent ϖ) : ¬ v.vle 1 ϖ := by
  intro hle
  letI : ValuativeRel B := v.toValuativeRel
  have hopen : IsOpen {a : B | ValuativeRel.valuation B a < 1} := hv 1
  have h0 : (0 : B) ∈ {a : B | ValuativeRel.valuation B a < 1} := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_lt_one
  obtain ⟨k, hk⟩ := (hϖ.eventually_mem (hopen.mem_nhds h0)).exists
  simp only [Set.mem_setOf_eq] at hk
  have h1 := (Valuation.Compatible.vle_iff_le
    (v := ValuativeRel.valuation B) 1 ϖ).mp hle
  rw [map_one] at h1
  have hone := one_le_pow₀ (n := k) h1
  rw [← map_pow] at hone
  exact absurd hk (not_lt.mpr hone)

variable [IsTopologicalRing B]

/-- For every `x : B`, some `ϖ^k · x` lies in the (open) ring of integral
elements `B⁺`. -/
theorem exists_pow_mul_mem_plusSubring [PlusSubring B]
    [IsRingOfIntegralElements (B⁺ : Subring B)]
    {ϖ : B} (hϖ : IsTopologicallyNilpotent ϖ) (x : B) :
    ∃ k : ℕ, ϖ ^ k * x ∈ (B⁺ : Subring B) := by
  have hopen : IsOpen ((B⁺ : Subring B) : Set B) :=
    (inferInstance : IsRingOfIntegralElements (B⁺ : Subring B)).isOpen
  have htend : Tendsto (fun k => ϖ ^ k * x) atTop (𝓝 (0 : B)) := by
    have := hϖ.mul_const x
    rwa [zero_mul] at this
  exact (htend.eventually_mem (hopen.mem_nhds (Subring.zero_mem _))).exists

/-- **The uniform spanning bound** (the heart of Kedlaya Ex. 1.2.2): if the finite
set `T` spans the unit ideal, there is a single `M` such that *every* Spa-point
satisfies `v(ϖ^M) ≤ v(t)` for some `t ∈ T`. (Write `1 = ∑ c_t·t`; choose `M`
absorbing every coefficient into `B⁺`; then
`v(ϖ^M) = v(∑ (ϖ^M c_t)·t) ≤ max_t v(ϖ^M c_t)·v(t) ≤ max_t v(t)`.) -/
theorem exists_uniform_spanning_bound [PlusSubring B]
    [IsRingOfIntegralElements (B⁺ : Subring B)]
    {ϖ : B} (hϖ : IsTopologicallyNilpotent ϖ)
    {T : Finset B} (hspan : Ideal.span (T : Set B) = ⊤) :
    ∃ M : ℕ, ∀ v : Spv B, v ∈ Spa B B⁺ → ∃ t ∈ T, v.vle (ϖ ^ M) t := by
  classical
  have hϖ_mem : ϖ ∈ (B⁺ : Subring B) :=
    topologicallyNilpotent_mem_of_isOpen_integrallyClosed _
      (inferInstance : IsRingOfIntegralElements (B⁺ : Subring B)).isOpen
      (fun a ha => (inferInstance :
        IsRingOfIntegralElements (B⁺ : Subring B)).isIntegrallyClosed a ha) hϖ
  have h1 : (1 : B) ∈ Ideal.span (T : Set B) := hspan ▸ Submodule.mem_top
  obtain ⟨c, -, hsum⟩ := Submodule.mem_span_finset.mp h1
  simp only [smul_eq_mul] at hsum
  choose k hk using fun t => exists_pow_mul_mem_plusSubring hϖ (c t)
  refine ⟨T.sup k, fun v hv => ?_⟩
  rcases T.eq_empty_or_nonempty with rfl | hT
  · -- empty spanning set forces `1 = 0`, contradicting `¬ v(1) ≤ v(0)`
    exfalso
    simp only [Finset.sum_empty] at hsum
    refine v.not_vle_one_zero ?_
    rw [show (0 : B) = 1 from hsum]
    exact @ValuativeRel.vle_refl B _ v.toValuativeRel (1 : B)
  -- absorb every coefficient: `ϖ^M · c t ∈ B⁺`
  have hcoef : ∀ t ∈ T, ϖ ^ T.sup k * c t ∈ (B⁺ : Subring B) := by
    intro t ht
    have hle : k t ≤ T.sup k := Finset.le_sup ht
    have : ϖ ^ T.sup k * c t = ϖ ^ (T.sup k - k t) * (ϖ ^ k t * c t) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖ_mem _) (hk t)
  -- the ultrametric maximum principle picks the dominating term
  obtain ⟨t, ht, hmax⟩ := Spv.exists_sum_vle v hT (fun t => c t * t)
  rw [hsum] at hmax
  refine ⟨t, ht, ?_⟩
  -- `v(ϖ^M) = v(1·ϖ^M) ≤ v((c t · t)·ϖ^M) = v((ϖ^M c t)·t) ≤ v(1·t) = v(t)`
  have h1' := v.mul_vle_mul_left hmax (ϖ ^ T.sup k)
  rw [one_mul] at h1'
  have h2 : v.vle (c t * t * ϖ ^ T.sup k) t := by
    have hmem := vle_one_of_mem_spa hv (hcoef t ht)
    have h2' := v.mul_vle_mul_left hmem t
    rw [one_mul] at h2'
    have heq : c t * t * ϖ ^ T.sup k = ϖ ^ T.sup k * c t * t := by ring
    rw [heq]
    exact h2'
  exact Spv.vleTrans h1' h2

/-! ### Indexed rational sets and the perturbation theorem -/

variable (B) in
/-- The rational subset presented by an indexed family of numerators `f i`
(`i ∈ s`) and denominator `g`, as a subset of `Spa B B⁺`. Translation to the
project's `rationalOpen`: `indexedRationalSet_eq_rationalOpen`. -/
def indexedRationalSet {ι : Type v} [PlusSubring B] (s : Finset ι) (f : ι → B)
    (g : B) : Set (Spv B) :=
  {v ∈ Spa B B⁺ | (∀ i ∈ s, v.vle (f i) g) ∧ ¬ v.vle g 0}

theorem indexedRationalSet_eq_rationalOpen {ι : Type v} [PlusSubring B]
    [DecidableEq B] (s : Finset ι) (f : ι → B) (g : B) :
    indexedRationalSet B s f g = rationalOpen (s.image f) g ∩ Spa B B⁺ := by
  ext v
  constructor
  · rintro ⟨hv, hT, hg⟩
    exact ⟨⟨hv, fun t ht => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact hT i hi, hg⟩, hv⟩
  · rintro ⟨⟨hv, hT, hg⟩, -⟩
    exact ⟨hv, fun i hi => hT (f i) (Finset.mem_image_of_mem f hi), hg⟩

/-- **The perturbation theorem** (Kedlaya Ex. 1.2.2(b) / the approximation step of
Wedhorn 7.48): if `M` is a uniform spanning bound for the presentation
`(f, g)` on `Spa B B⁺`, then perturbing every parameter by an element of
`ϖ^(M+1) · B⁺` leaves the presented subset unchanged. -/
theorem indexedRationalSet_perturb_eq {ι : Type v} [PlusSubring B]
    {ϖ : B} (hϖ_unit : IsUnit ϖ) (hϖ : IsTopologicallyNilpotent ϖ)
    {s : Finset ι} {f f' : ι → B} {g g' : B} {M : ℕ}
    (hbound : ∀ v : Spv B, v ∈ Spa B B⁺ →
      v.vle (ϖ ^ M) g ∨ ∃ i ∈ s, v.vle (ϖ ^ M) (f i))
    (hδf : ∀ i ∈ s, ∃ b ∈ (B⁺ : Subring B), f' i = f i + ϖ ^ (M + 1) * b)
    (hδg : ∃ b ∈ (B⁺ : Subring B), g' = g + ϖ ^ (M + 1) * b) :
    indexedRationalSet B s f g = indexedRationalSet B s f' g' := by
  classical
  -- All comparisons run through the canonical valuation of each point.
  ext v
  simp only [indexedRationalSet, Set.mem_setOf_eq]
  refine and_congr_right fun hv => ?_
  letI : ValuativeRel B := v.toValuativeRel
  set val := ValuativeRel.valuation B with hval
  have hbridge : ∀ x y : B, v.vle x y ↔ val x ≤ val y := fun x y =>
    Valuation.Compatible.vle_iff_le (v := val) x y
  have hzero : ∀ x : B, v.vle x 0 ↔ val x = 0 := fun x => by
    rw [hbridge, map_zero, le_zero_iff]
  -- `v(ϖ) < 1` (continuity + topological nilpotence) and `v(ϖ) ≠ 0` (unit)
  have hϖ_lt_one : val ϖ < 1 := by
    have := not_one_vle_of_topologicallyNilpotent hv.1 hϖ
    rw [hbridge] at this
    simpa using lt_of_not_ge this
  have hϖ_ne : val ϖ ≠ 0 := by
    have := not_vle_zero_of_isUnit hϖ_unit v
    rw [hzero] at this
    exact this
  have hϖpow_ne : ∀ n : ℕ, val (ϖ ^ n) ≠ 0 := fun n => by
    rw [map_pow]; exact pow_ne_zero n hϖ_ne
  have hϖ_succ_lt : val (ϖ ^ (M + 1)) < val (ϖ ^ M) := by
    rw [pow_succ, map_mul]
    exact mul_lt_of_lt_one_right (zero_lt_iff.mpr (hϖpow_ne M)) hϖ_lt_one
  -- the perturbations are `≤ v(ϖ^(M+1))`
  have hδ_le : ∀ b ∈ (B⁺ : Subring B), val (ϖ ^ (M + 1) * b) ≤ val (ϖ ^ (M + 1)) := by
    intro b hb
    have hb1 : val b ≤ 1 := by
      have := vle_one_of_mem_spa hv hb
      rwa [hbridge, map_one] at this
    rw [map_mul]
    calc val (ϖ ^ (M + 1)) * val b ≤ val (ϖ ^ (M + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hb1 zero_le
      _ = _ := mul_one _
  obtain ⟨bg, hbg_mem, hbg⟩ := hδg
  constructor
  · -- forward: membership for `(f, g)` gives membership for `(f', g')`
    rintro ⟨hT, hg_ne⟩
    rw [hzero] at hg_ne
    -- `v(ϖ^M) ≤ v(g)`
    have hMg : val (ϖ ^ M) ≤ val g := by
      rcases hbound v hv with h | ⟨i, hi, h⟩
      · rwa [hbridge] at h
      · rw [hbridge] at h
        exact h.trans ((hbridge _ _).mp (hT i hi))
    have hδg_lt : val (ϖ ^ (M + 1) * bg) < val g :=
      lt_of_le_of_lt (hδ_le bg hbg_mem) (lt_of_lt_of_le hϖ_succ_lt hMg)
    -- `v(g') = v(g)`
    have hg'_eq : val g' = val g := by
      rw [hbg]
      exact Valuation.map_add_eq_of_lt_left _ hδg_lt
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨bf, hbf_mem, hbf⟩ := hδf i hi
      have hδf_lt : val (ϖ ^ (M + 1) * bf) ≤ val g :=
        le_trans (hδ_le bf hbf_mem) (le_trans hϖ_succ_lt.le hMg)
      rw [hbridge, hbf, hg'_eq]
      calc val (f i + ϖ ^ (M + 1) * bf) ≤
            max (val (f i)) (val (ϖ ^ (M + 1) * bf)) := Valuation.map_add _ _ _
        _ ≤ val g := max_le ((hbridge _ _).mp (hT i hi)) hδf_lt
    · rw [hzero, hg'_eq]
      exact hg_ne
  · -- reverse: membership for `(f', g')` gives membership for `(f, g)`
    rintro ⟨hT', hg'_ne⟩
    rw [hzero] at hg'_ne
    -- first: `v(ϖ^M) ≤ v(g')`
    have hMg' : val (ϖ ^ M) ≤ val g' := by
      rcases hbound v hv with h | ⟨i, hi, h⟩
      · -- `v(ϖ^M) ≤ v(g)`; if `v(g') < v(ϖ^M) ≤ v(g)` then `v(δg) = v(g)`… derive directly:
        rw [hbridge] at h
        by_contra hcon
        rw [not_le] at hcon
        -- then `v(g') < v(ϖ^M) ≤ v(g)`, and `v(δg) ≤ v(ϖ^(M+1)) < v(ϖ^M) ≤ v(g)`,
        -- so `v(g') = v(g + δg) = v(g) ≥ v(ϖ^M)` — contradiction.
        have hδlt : val (ϖ ^ (M + 1) * bg) < val g :=
          lt_of_le_of_lt (hδ_le bg hbg_mem) (lt_of_lt_of_le hϖ_succ_lt h)
        have : val g' = val g := by
          rw [hbg]; exact Valuation.map_add_eq_of_lt_left _ hδlt
        rw [this] at hcon
        exact absurd h (not_le.mpr hcon)
      · -- `v(ϖ^M) ≤ v(f i)`: then `v(f' i) = v(f i)`, and membership gives
        -- `v(f' i) ≤ v(g')`.
        rw [hbridge] at h
        obtain ⟨bf, hbf_mem, hbf⟩ := hδf i hi
        have hδlt : val (ϖ ^ (M + 1) * bf) < val (f i) :=
          lt_of_le_of_lt (hδ_le bf hbf_mem) (lt_of_lt_of_le hϖ_succ_lt h)
        have hf'_eq : val (f' i) = val (f i) := by
          rw [hbf]; exact Valuation.map_add_eq_of_lt_left _ hδlt
        have := (hbridge _ _).mp (hT' i hi)
        rw [hf'_eq] at this
        exact h.trans this
    -- `v(δg) < v(g')`, so `v(g) = v(g')`
    have hδg_lt : val (ϖ ^ (M + 1) * bg) < val g' :=
      lt_of_le_of_lt (hδ_le bg hbg_mem) (lt_of_lt_of_le hϖ_succ_lt hMg')
    have hg_eq : val g = val g' := by
      have : g = g' + -(ϖ ^ (M + 1) * bg) := by rw [hbg]; ring
      rw [this]
      have hneg : val (-(ϖ ^ (M + 1) * bg)) < val g' := by rwa [Valuation.map_neg]
      exact Valuation.map_add_eq_of_lt_left _ hneg
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨bf, hbf_mem, hbf⟩ := hδf i hi
      have hδf_lt : val (ϖ ^ (M + 1) * bf) ≤ val g' :=
        le_trans (hδ_le bf hbf_mem) (le_trans hϖ_succ_lt.le hMg')
      rw [hbridge, hg_eq]
      have : f i = f' i + -(ϖ ^ (M + 1) * bf) := by rw [hbf]; ring
      rw [this]
      calc val (f' i + -(ϖ ^ (M + 1) * bf)) ≤
            max (val (f' i)) (val (-(ϖ ^ (M + 1) * bf))) := Valuation.map_add _ _ _
        _ ≤ val g' := by
            rw [Valuation.map_neg]
            exact max_le ((hbridge _ _).mp (hT' i hi)) hδf_lt
    · rw [hzero, hg_eq]
      exact hg'_ne

end ValuationSpectrum
