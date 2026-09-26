/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Compactness.SigmaCompact
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.FunctionSpace
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Hull
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform

/-!
# Holomorphically convex exhaustions and escaping sequences

Separation outside a hull can be amplified by powers to make a function arbitrarily small on the
original set and arbitrarily large at the chosen point. This step is proved. The compact
exhaustion is constructed by repeatedly enlarging compact sets and taking their holomorphic
hulls. The escaping-sequence characterization follows from Baire's theorem in the complete space
of holomorphic functions. Exhaustions use Mathlib's `CompactExhaustion` on the open subtype,
rather than a new topological structure.

References: [Range][Range1986] II §3.2; [Fritzsche–Grauert][FritzscheGrauert2002] II §6;
[Scheidemann][Scheidemann2005] §7.1.

## Main results

`IsHolomorphicallyConvex.exists_compactExhaustion` produces a compact exhaustion by hull-fixed
sets. `isHolomorphicallyConvex_iff_unbounded_on_escaping_sequences` is the escaping-sequence
characterization.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Powers of a separating function give arbitrary smallness on the set and an arbitrary large value
at an exterior hull point. Empty sets are included. -/
theorem exists_small_large_separator {U K : Set E} {a : E}
    (ha : a ∈ U) (hn : a ∉ holomorphicHull U K) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ (∀ z ∈ K, ‖f z‖ < ε) ∧ R < ‖f a‖ := by
  let A : ℝ := max R 0 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hRA : R < A := by dsimp [A]; linarith [le_max_left R 0]
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst K
    exact ⟨fun _ => (A : ℂ), analyticOnNhd_const, by simp,
      by simpa only [Complex.norm_of_nonneg hA.le] using hRA⟩
  obtain ⟨f, hf, M, hM, hMa⟩ := exists_separator_of_notMem_holomorphicHull ha hn
  obtain ⟨z₀, hz₀⟩ := hK
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
  have hfa : 0 < ‖f a‖ := hM0.trans_lt hMa
  have hq : M / ‖f a‖ < 1 := (div_lt_one hfa).mpr hMa
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hA) hq
  refine ⟨fun z => (A : ℂ) * (f z / f a) ^ k,
    analyticOnNhd_const.mul (hf.div_const.pow k), ?_, ?_⟩
  · intro z hz
    rw [norm_mul, Complex.norm_of_nonneg hA.le, norm_pow, norm_div]
    calc
      A * (‖f z‖ / ‖f a‖) ^ k ≤ A * (M / ‖f a‖) ^ k := by
        gcongr
        exact hM z hz
      _ < ε := (lt_div_iff₀ hA).mp hk |> (by simpa [mul_comm] using ·)
  · simpa [div_self (norm_pos_iff.mp hfa), Complex.norm_of_nonneg hA.le, abs_of_pos hA] using hRA

variable [FiniteDimensional ℂ E]

/-- Finite-dimensional source spaces are proper. -/
local instance : ProperSpace E := FiniteDimensional.proper ℂ E

/-- Finite-dimensional source spaces have countable bases. -/
local instance : SecondCountableTopology E :=
  (Module.finBasis ℂ E).equivFunL.toHomeomorph.secondCountableTopology

/-- A holomorphically convex open set has a compact exhaustion by sets fixed by the relative
holomorphic hull, by recursive refinement of a compact exhaustion. -/
theorem IsHolomorphicallyConvex.exists_compactExhaustion {U : Set E}
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) :
    ∃ K : CompactExhaustion U, ∀ j,
      IsHolomorphicallyConvexIn U ((Subtype.val : U → E) '' K j) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  let B := CompactExhaustion.choice U
  let H (S : Set U) : Set U :=
    (Subtype.val : U → E) ⁻¹' holomorphicHull U (Subtype.val '' S)
  have himage (S : Set U) : Subtype.val '' H S = holomorphicHull U (Subtype.val '' S) := by
    apply image_preimage_eq_of_subset
    intro z hz
    exact ⟨⟨z, hz.1⟩, rfl⟩
  have hcompact (S : Set U) (hS : IsCompact S) : IsCompact (H S) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [himage]
    exact hU _ (hS.image continuous_subtype_val) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  have hsubset (S : Set U) : S ⊆ H S := by
    intro z hz
    exact subset_holomorphicHull (by rintro _ ⟨w, _, rfl⟩; exact w.property) ⟨z, hz, rfl⟩
  have hfixed (S : Set U) : IsHolomorphicallyConvexIn U (Subtype.val '' H S) := by
    rw [himage]
    exact isHolomorphicallyConvexIn_holomorphicHull _ _
  let enlarge (S : {S : Set U // IsCompact S}) : {S : Set U // IsCompact S} :=
    ⟨(exists_compact_superset S.property).choose, (exists_compact_superset
      S.property).choose_spec.1⟩
  have henlarge (S : {S : Set U // IsCompact S}) : S.val ⊆ interior (enlarge S).val :=
    (exists_compact_superset S.property).choose_spec.2
  let K : ℕ → {S : Set U // IsCompact S} := fun j =>
    Nat.recOn j ⟨H (B 0), hcompact _ (B.isCompact 0)⟩ fun j S =>
      ⟨H ((enlarge S).val ∪ B (j + 1)), hcompact _ ((enlarge S).property.union (B.isCompact _))⟩
  have hBK (j : ℕ) : B j ⊆ (K j).val := by
    cases j with
    | zero => exact hsubset _
    | succ j => exact subset_union_right.trans (hsubset _)
  refine ⟨{ toFun := fun j => (K j).val
            isCompact' := fun j => (K j).property
            subset_interior_succ' := ?_
            iUnion_eq' := ?_ }, ?_⟩
  · intro j
    exact (henlarge (K j)).trans (interior_mono (subset_union_left.trans (hsubset _)))
  · apply iUnion_eq_univ_iff.mpr
    intro z
    obtain ⟨j, hj⟩ := B.exists_mem z
    exact ⟨j, hBK j hj⟩
  · intro j
    cases j with
    | zero => exact hfixed _
    | succ j => exact hfixed _

/-- A sequence escapes compact subsets when it eventually leaves every compact set in the ambient
domain. Its membership in the domain is a separate hypothesis. -/
@[expose] def EscapesCompactSubsets (U : Set E) (p : ℕ → E) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → ∀ᶠ j in atTop, p j ∉ K

/-- A Baire argument turns functions tending to zero in the compact-open topology, but arbitrarily
large somewhere on a sequence, into one function unbounded there. -/
private theorem exists_unbounded_of_small_functions
    (V : TopologicalSpace.Opens E) (p : ℕ → V)
    (hsmall : ∀ M : ℝ, ∃ F : ℕ → HolomorphicMap V ℂ,
      Tendsto F atTop (𝓝 0) ∧ ∀ n, ∃ j, M < ‖(F n).val (p j)‖) :
    ∃ f : HolomorphicMap V ℂ, ¬ BddAbove (range (fun j => ‖f.val (p j)‖)) := by
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  have : (uniformity C(V, ℂ)).IsCountablyGenerated := inferInstance
  have : (uniformity (HolomorphicMap V ℂ)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (HolomorphicMap V ℂ) :=
    .of_completeSpace_pseudometrizable
  let : BaireSpace (HolomorphicMap V ℂ) := BaireSpace.of_completelyPseudoMetrizable
  by_contra! hb
  let A (n : ℕ) : Set (HolomorphicMap V ℂ) := {f | ∀ j, ‖f.val (p j)‖ ≤ n}
  have hclosed (n : ℕ) : IsClosed (A n) := by
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le
      (continuous_holomorphicMap_eval V (p j)).norm continuous_const
  have hcover : ⋃ n, A n = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro f
    obtain ⟨M, hM⟩ := hb f
    obtain ⟨n, hn⟩ := exists_nat_ge M
    exact ⟨n, fun j => (hM (mem_range_self j)).trans hn⟩
  obtain ⟨N, g, hg⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hgA : g ∈ A N := interior_subset hg
  obtain ⟨F, hlim, hlarge⟩ := hsmall (2 * (N : ℝ))
  have hlim' : Tendsto (fun n => g + F n) atTop (𝓝 g) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlim
  obtain ⟨n, hn⟩ := (hlim'.eventually (mem_interior_iff_mem_nhds.mp hg)).exists
  obtain ⟨j, hj⟩ := hlarge n
  have hsum : ‖g.val (p j) + (F n).val (p j)‖ ≤ N := hn j
  have hgn := hgA j
  have hnorm := norm_sub_le (g.val (p j) + (F n).val (p j)) (g.val (p j))
  simp only [add_sub_cancel_left] at hnorm
  linarith

/-- **Escaping-sequence characterization of holomorphic convexity.** Baire's theorem
and small separating functions give an unbounded holomorphic function on any escaping
sequence; conversely, a noncompact hull contains an escaping sequence. -/
theorem isHolomorphicallyConvex_iff_unbounded_on_escaping_sequences
    {U : Set E} (ho : IsOpen U) :
    IsHolomorphicallyConvex U ↔
      ∀ p : ℕ → E, (∀ j, p j ∈ U) → EscapesCompactSubsets U p →
        ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧
          ¬ BddAbove (Set.range (fun j => ‖f (p j)‖)) := by
  classical
  let V : TopologicalSpace.Opens E := ⟨U, ho⟩
  let : LocallyCompactSpace V := ho.locallyCompactSpace
  let K := CompactExhaustion.choice V
  let C (n : ℕ) : Set E := Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hcofinal {S : Set E} (hS : IsCompact S) (hSU : S ⊆ U) :
      ∃ n, S ⊆ C n := by
    have he : Subtype.val '' ((Subtype.val : V → E) ⁻¹' S) = S :=
      image_preimage_eq_of_subset (by intro z hz; exact ⟨⟨z, hSU hz⟩, rfl⟩)
    have hc : IsCompact ((Subtype.val : V → E) ⁻¹' S) :=
      Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (he.symm ▸ hS)
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hc
    exact ⟨n, fun z hz => ⟨⟨z, hSU hz⟩, hn hz, rfl⟩⟩
  constructor
  · intro hconv p hp hescape
    obtain ⟨g, hg⟩ := exists_unbounded_of_small_functions V (fun j => ⟨p j, hp j⟩) (by
      intro M
      have hsep (n : ℕ) : ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧
          (∀ z ∈ C n, ‖f z‖ < 1 / ((n : ℝ) + 1)) ∧ ∃ j, M < ‖f (p j)‖ := by
        obtain ⟨j, hj⟩ := (hescape (holomorphicHull U (C n))
          (hconv _ (hC n) (hCU n)) (holomorphicHull_subset _ _)).exists
        obtain ⟨f, hf, hs, hl⟩ := exists_small_large_separator (hp j) hj
          (by positivity : 0 < 1 / ((n : ℝ) + 1)) (M)
        exact ⟨f, hf, hs, j, hl⟩
      choose f hf hs j hj using hsep
      let F (n : ℕ) : HolomorphicMap V ℂ :=
        ⟨⟨fun z => f n z, (hf n).continuousOn.domRestrict⟩,
          (hf n).congr ho (fun z hz => by rw [openExtension_apply V _ hz]; rfl)⟩
      have hlim : Tendsto F atTop (𝓝 0) := by
        rw [holomorphicMap_tendsto_iff, tendstoLocallyUniformlyOn_iff_forall_isCompact V.isOpen]
        intro S hSU hS
        obtain ⟨m, hm⟩ := hcofinal hS hSU
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (gt_mem_nhds hε)
        filter_upwards [eventually_ge_atTop m, ht] with n hn hεn
        intro z hz
        rw [openExtension_apply V _ (hSU hz), openExtension_apply V _ (hSU hz)]
        change dist (0 : ℂ) (f n z) < ε
        rw [dist_zero_left]
        exact (hs n z (image_mono (K.subset hn) (hm hz))).trans hεn
      exact ⟨F, hlim, fun n => ⟨j n, hj n⟩⟩)
    refine ⟨openExtension V g.val, g.property, ?_⟩
    simpa only [openExtension_apply V _ (hp _)] using hg
  · intro hseq S hS hSU
    by_contra hn
    have hex (n : ℕ) : ∃ z ∈ holomorphicHull U S, z ∉ C n := by
      by_contra hh
      apply hn
      apply isCompact_holomorphicHull_of_subset_compact (hC n) (hCU n)
      simpa only [not_exists, not_and, not_not, subset_def] using hh
    choose p hp hnC using hex
    have hpU (n : ℕ) : p n ∈ U := (hp n).1
    have he : EscapesCompactSubsets U p := by
      intro T hT hTU
      obtain ⟨n, hn⟩ := hcofinal hT hTU
      filter_upwards [eventually_ge_atTop n] with m hm hpm
      exact hnC m (image_mono (K.subset hm) (hn hpm))
    obtain ⟨f, hf, hnf⟩ := hseq p hpU he
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hf.continuousOn.mono hSU)
    apply hnf
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact (hp n).2 f hf M hM⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
