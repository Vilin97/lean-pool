/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.BanachOMT
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Wedhorn §6.3 — Banach's theorem for Tate rings

This file ports the three results in Wedhorn §6.3 (arXiv:1910.05934, pp. 49-50)
that Wedhorn marks "Proof. Missing", referring out to Huber [Hu3] Lemma 2.4 and
BGR §3.7. Specifically:

* **Wedhorn 6.16** — Banach's open mapping for topological A-modules over a
  Tate-like ring (= Huber [Hu3] Lemma 2.4(i) = direct corollary of
  `AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`).
* **Wedhorn 6.17** — noetherian ⇔ every submodule (resp. ideal) is closed
  (= BGR §3.7.2/2, applied via Wedhorn 6.16).
* **Wedhorn 6.18** — for a complete noetherian Tate ring `A`, every finitely
  generated `A`-module has a unique complete countably-generated `A`-module
  topology; A-linear maps between such modules are continuous and open onto
  image (= BGR §3.7.3/2 + 3.7.3/3 + Corollary 5).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, §6.3 "Banach's theorem for Tate
  rings", pp. 49-50 (statements; proofs marked "Missing").
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994), Lemma 2.4 (p. 16).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §3.7.2/2 (p. 164), §3.7.3/2 + §3.7.3/3 (p. 164), §3.7.3/Cor 5 (p. 165).

## Roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` for the full layered plan,
source quotes, and Lean ↔ source match analysis.
-/

namespace ValuationSpectrum

universe u

/-- **Wedhorn 6.16** = Huber [Hu3] Lemma 2.4(i). Banach's open mapping theorem
applied to topological A-modules over a Tate-like ring.

Let `A` be a topological ring containing a sequence converging to 0 consisting
of units (in particular, any Tate ring). Let `M, N` be Hausdorff topological
`A`-modules with countably-generated uniformities, both complete. Then every
continuous surjective `A`-linear map `f : M →ₗ[A] N` is open.

This is the direct corollary of the underlying group-level
`AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`: an A-linear
map is in particular an additive group homomorphism, and the group-level
result depends only on the group structure (the A-module structure is
inessential — Huber notes this explicitly).

**Source** (Wedhorn 6.16, p. 49):
> "Let `A` be a topological ring that has a sequence converging to 0
> consisting of units of `A` (e.g., if `A` is a Tate ring). Let `M` and `N`
> be Hausdorff topological `A`-modules that have countable fundamental systems
> of open neighborhoods of 0. Assume that `M` is complete. Let `u : M → N` be
> an `A`-linear map. Consider the following properties: (a) `N` is complete;
> (b) `u` is surjective; (c) `u` is open. Then any two of these properties
> imply the third." -/
theorem wedhorn_6_16
    {A : Type u} [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
      [SigmaCompactSpace M]
    {N : Type*} [AddCommGroup N] [Module A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
    (f : M →ₗ[A] N) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  -- Apply the group-level Banach OMT to f.toAddMonoidHom.
  -- The A-linearity is not needed for openness (only the group hom structure).
  -- `[SigmaCompactSpace M]` added per BINDING-RULE (b) — see `BanachOMT.lean`
  -- L1 docstring + `b2_log.jsonl` entry 3.
  AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated f.toAddMonoidHom hf hsurj

/-- **Dilation cover** — the `A`-module input that replaces σ-compactness in Wedhorn 6.16.
For a topological `A`-module `M` with continuous scalar multiplication and a topologically
nilpotent element `ϖ`, every neighbourhood `U` of `0` dilates to cover `M`: every `m : M`
satisfies `ϖ ^ n • m ∈ U` for some `n` (because `ϖ ^ n • m → 0`). This is exactly the
countable cover Baire's theorem needs, and it is what Wedhorn's "sequence of units → 0"
hypothesis supplies — no σ-compactness or separability of `M` required. -/
theorem iUnion_preimage_smul_pow_eq_univ
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [ContinuousSMul A M]
    {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ) {U : Set M} (hU : U ∈ nhds (0 : M)) :
    ⋃ n : ℕ, {m : M | ϖ ^ n • m ∈ U} = Set.univ := by
  refine Set.eq_univ_of_forall fun m => Set.mem_iUnion.2 ?_
  have hT : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (nhds (0 : A)) := hϖ
  have htend : Filter.Tendsto (fun n : ℕ => ϖ ^ n • m) Filter.atTop (nhds (0 : M)) := by
    simpa using hT.smul_const m
  exact (htend.eventually hU).exists

open scoped Pointwise in
/-- **Almost-open half of the faithful Wedhorn 6.16**: a continuous surjective `A`-linear map
between topological `A`-modules (with a topologically nilpotent unit `ϖ` and continuous scalar
multiplication, target a Baire space) has `closure (f '' U)` a neighbourhood of `0` for every
neighbourhood `U` of `0`. The dilation cover `⋃ₙ {m | ϖⁿ•m ∈ V}` replaces σ-compactness in the
Baire step. -/
theorem _omt_almost_open
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]
      [IsTopologicalAddGroup N] [ContinuousSMul A N] [BaireSpace N]
    {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ) (hϖu : IsUnit ϖ)
    (f : M →ₗ[A] N) (hsurj : Function.Surjective f)
    {U : Set M} (hU : U ∈ nhds (0 : M)) :
    closure (f '' U) ∈ nhds (0 : N) := by
  classical
  -- Step 0: symmetric closed nbhd V of 0 with V + V ⊆ U.
  obtain ⟨V, hV_nhds, _hV_closed, hV_symm, hV_add⟩ :=
    AddMonoidHom._sub_sub_lemma_A_1_split_symmetric U hU
  -- `ContinuousConstSMul` instances follow from `ContinuousSMul`.
  haveI : ContinuousConstSMul A M := inferInstance
  haveI : ContinuousConstSMul A N := inferInstance
  -- Step 1: closure (f '' V) has nonempty interior.
  -- The dilation cover sets in M.
  set S : ℕ → Set M := fun n => {m : M | ϖ ^ n • m ∈ V} with hS_def
  -- Cover of N by ⋃ n, closure (f '' S n).
  have h_cover : ⋃ n, closure (f '' S n) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ ⋃ n, S n := by
      rw [iUnion_preimage_smul_pow_eq_univ hϖ hV_nhds]; exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨n, subset_closure (Set.mem_image_of_mem f hn)⟩
  -- Baire: some closure (f '' S n₀) has nonempty interior.
  obtain ⟨n₀, hn₀⟩ := AddMonoidHom._sub_sub_lemma_C_2_baire_nonempty_interior
    (fun n => closure (f '' S n)) (fun _ => isClosed_closure) h_cover
  -- The dilation homeomorphism e := ϖ^n₀ • · on N.
  let e : N ≃ₜ N := ((hϖu.pow n₀).isHomeomorph_smul).homeomorph
  -- The dilation homeomorphism on M (the same scalar, as a self-map of M).
  -- Key identity: e '' (f '' S n₀) = f '' V.
  have h_image_eq : e '' (f '' S n₀) = f '' V := by
    -- e ∘ f = f ∘ (ϖ^n₀ • · on M); pushing through the image of S n₀.
    rw [Set.image_image]
    have h_pt : ∀ m : M, e (f m) = f (ϖ ^ n₀ • m) := by
      intro m
      change (ϖ ^ n₀) • f m = f (ϖ ^ n₀ • m)
      rw [map_smul]
    simp_rw [h_pt]
    rw [← Set.image_image f (fun m => ϖ ^ n₀ • m)]
    congr 1
    -- (ϖ^n₀ • · on M) '' S n₀ = V, because S n₀ = preimage of V under that bijection.
    have hbij : Function.Surjective (fun m : M => ϖ ^ n₀ • m) :=
      ((hϖu.pow n₀).isHomeomorph_smul).surjective
    have : S n₀ = (fun m : M => ϖ ^ n₀ • m) ⁻¹' V := rfl
    rw [this, Set.image_preimage_eq V hbij]
  -- closure (f '' V) = e '' closure (f '' S n₀), which has nonempty interior.
  have h_closure_eq : closure (f '' V) = e '' closure (f '' S n₀) := by
    rw [Homeomorph.image_closure, h_image_eq]
  have h_int_V : (interior (closure (f '' V))).Nonempty := by
    rw [h_closure_eq, ← Homeomorph.image_interior]
    exact hn₀.image e
  -- Step 2: conclude. Let W := closure (f '' V).
  set W : Set N := closure (f '' V) with hW_def
  -- W is symmetric: -W = W.
  have hfV_symm : -(f '' V) = f '' V := by
    rw [← Set.image_neg_eq_neg, ← Set.image_comp]
    have : (fun a => -a) ∘ f = f ∘ (fun m => -m) := by
      ext m; simp
    rw [this, Set.image_comp, Set.image_neg_eq_neg, hV_symm]
  have hW_symm : -W = W := by
    rw [hW_def, neg_closure, hfV_symm]
  -- 0 ∈ interior W + interior W ⊆ interior (W + W), so W + W ∈ nhds 0.
  obtain ⟨w₀, hw₀⟩ := h_int_V
  -- interior (-W) = -(interior W) via the negation homeomorphism.
  have h_int_neg : interior (-W) = -interior W := by
    have h := (Homeomorph.neg N).image_interior W
    rw [Homeomorph.coe_neg, Set.image_neg_eq_neg, Set.image_neg_eq_neg] at h
    exact h.symm
  have hneg_w₀ : -w₀ ∈ interior W := by
    have hmem : -w₀ ∈ -interior W := Set.neg_mem_neg.2 hw₀
    rw [← h_int_neg, hW_symm] at hmem
    exact hmem
  have h0_int : (0 : N) ∈ interior (W + W) := by
    have h_sum : w₀ + (-w₀) ∈ interior W + interior W := Set.add_mem_add hw₀ hneg_w₀
    rw [add_neg_cancel] at h_sum
    exact AddMonoidHom._sub_sub_lemma_A_2_interior_add W W h_sum
  have hWW_nhds : W + W ∈ nhds (0 : N) := mem_interior_iff_mem_nhds.1 h0_int
  -- W + W ⊆ closure (f '' U).
  have hWW_sub : W + W ⊆ closure (f '' U) := by
    -- closure (f '' V) + closure (f '' V) ⊆ closure (f '' V + f '' V).
    have h1 : W + W ⊆ closure (f '' V + f '' V) := by
      rw [hW_def]; exact vadd_set_closure_subset (f '' V) (f '' V)
    -- f '' V + f '' V = f '' (V + V).
    have h2 : (f '' V + f '' V) = f '' (V + V) := (Set.image_add f).symm
    rw [h2] at h1
    -- f '' (V + V) ⊆ f '' U ⊆ closure (f '' U).
    refine h1.trans (closure_mono ?_)
    exact (Set.image_mono hV_add)
  exact Filter.mem_of_superset hWW_nhds hWW_sub

open scoped Pointwise in
/-- **Completion-upgrade half of Wedhorn 6.16**: if `f` is continuous with `M` complete and
`f` is "almost open" (`closure (f '' U) ∈ nhds 0` for every nbhd `U`), then `f` is open at `0`
(`f '' U ∈ nhds 0`). Classical Banach iterated-approximation: build `xₖ ∈ Wₖ` with
`y - f(x₁+…+xₖ) → 0`, sum is Cauchy (shrinking basis), limit `x ∈ closure W₀ ⊆ U`, `f x = y`. -/
theorem _omt_open_at_zero
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated]
    {N : Type*} [AddCommGroup N] [Module A N] [UniformSpace N] [IsUniformAddGroup N]
      [T2Space N]
    (f : M →ₗ[A] N) (hf : Continuous f)
    (h_almost : ∀ U ∈ nhds (0 : M), closure (f '' U) ∈ nhds (0 : N))
    {U : Set M} (hU : U ∈ nhds (0 : M)) :
    f '' U ∈ nhds (0 : N) := by
  classical
  -- Step 1: countable antitone basis `B` of `nhds (0:M)`.
  obtain ⟨B, hB_basis, _hB_anti⟩ := (nhds (0 : M)).exists_antitone_basis
  -- Step 2: build a closed symmetric shrinking cofinal basis `W : ℕ → Set M` by recursion.
  -- `pick P hP` packages a closed symmetric nbhd `V` of `0` with `V + V ⊆ P`.
  let pick : (P : Set M) → P ∈ nhds (0 : M) →
      {V : Set M // V ∈ nhds (0 : M) ∧ IsClosed V ∧ -V = V} := fun P hP =>
    ⟨(AddMonoidHom._sub_sub_lemma_A_1_split_symmetric P hP).choose,
      (AddMonoidHom._sub_sub_lemma_A_1_split_symmetric P hP).choose_spec.1,
      (AddMonoidHom._sub_sub_lemma_A_1_split_symmetric P hP).choose_spec.2.1,
      (AddMonoidHom._sub_sub_lemma_A_1_split_symmetric P hP).choose_spec.2.2.1⟩
  -- The defining add-property of the picked set, kept separately (uniform motive needs it out).
  have pick_add : ∀ (P : Set M) (hP : P ∈ nhds (0 : M)),
      (pick P hP).1 + (pick P hP).1 ⊆ P := fun P hP =>
    (AddMonoidHom._sub_sub_lemma_A_1_split_symmetric P hP).choose_spec.2.2.2
  -- `Wdat n` packages `W n`; at step 0 we cut with `U ∩ B 0`, at step n+1 with `(W n) ∩ B (n+1)`.
  let Wdat : (n : ℕ) → {V : Set M // V ∈ nhds (0 : M) ∧ IsClosed V ∧ -V = V} := fun n =>
    Nat.rec
      (motive := fun _ => {V : Set M // V ∈ nhds (0 : M) ∧ IsClosed V ∧ -V = V})
      (pick (U ∩ B 0) (Filter.inter_mem hU (hB_basis.mem_of_mem trivial)))
      (fun n prev =>
        pick (prev.1 ∩ B (n + 1)) (Filter.inter_mem prev.2.1 (hB_basis.mem_of_mem trivial)))
      n
  set W : ℕ → Set M := fun n => (Wdat n).1 with hW_def
  -- Easy properties from the packaged data.
  have hW_nhds : ∀ n, W n ∈ nhds (0 : M) := fun n => (Wdat n).2.1
  have hW_closed : ∀ n, IsClosed (W n) := fun n => (Wdat n).2.2.1
  have hW_symm : ∀ n, -W n = W n := fun n => (Wdat n).2.2.2
  have hW_zero : ∀ n, (0 : M) ∈ W n := fun n => mem_of_mem_nhds (hW_nhds n)
  -- The defining additive containments (from `pick_add`, matching the `Wdat` definition).
  have hW_add0 : W 0 + W 0 ⊆ U ∩ B 0 :=
    pick_add (U ∩ B 0) (Filter.inter_mem hU (hB_basis.mem_of_mem trivial))
  have hW_addS : ∀ n, W (n + 1) + W (n + 1) ⊆ W n ∩ B (n + 1) := fun n =>
    pick_add ((Wdat n).1 ∩ B (n + 1)) (Filter.inter_mem (Wdat n).2.1 (hB_basis.mem_of_mem trivial))
  -- Shrinking: `W (n+1) + W (n+1) ⊆ W n`.
  have hW_shrink : ∀ n, W (n + 1) + W (n + 1) ⊆ W n := fun n =>
    (hW_addS n).trans Set.inter_subset_left
  -- `W (n) ⊆ W (n) + W (n)` since `0 ∈ W n`.
  have hW_self_subset_add : ∀ n, W n ⊆ W n + W n := fun n x hx =>
    ⟨x, hx, 0, hW_zero n, add_zero x⟩
  -- `W 0 ⊆ U`.
  have hW0_subU : W 0 ⊆ U :=
    (hW_self_subset_add 0).trans (hW_add0.trans Set.inter_subset_left)
  -- `W n ⊆ B n` (cofinality ingredient).
  have hW_subB : ∀ n, W n ⊆ B n := by
    intro n
    cases n with
    | zero => exact (hW_self_subset_add 0).trans (hW_add0.trans Set.inter_subset_right)
    | succ k => exact (hW_self_subset_add (k + 1)).trans ((hW_addS k).trans Set.inter_subset_right)
  -- Cofinality: every nbhd of `0` contains some `W n`.
  have hW_cofinal : ∀ V ∈ nhds (0 : M), ∃ n, W n ⊆ V := by
    intro V hV
    obtain ⟨n, _, hn⟩ := hB_basis.mem_iff.mp hV
    exact ⟨n, (hW_subB n).trans hn⟩
  -- Step 3: closures of `f '' W n` are nbhds of `0` (almost-openness).
  have hclos : ∀ n, closure (f '' W n) ∈ nhds (0 : N) := fun n => h_almost (W n) (hW_nhds n)
  -- Step 4: the key claim — `closure (f '' W 1) ⊆ f '' W 0`.
  -- Auxiliary: `z - C` is a nbhd of `z` whenever `C` is a nbhd of `0`.
  have hnsub : ∀ (z : N) (C : Set N), C ∈ nhds (0 : N) → (fun a => z - a) '' C ∈ nhds z := by
    intro z C hC
    have h1 : (Homeomorph.subLeft z) '' C ∈ nhds (Homeomorph.subLeft z 0) :=
      (Homeomorph.subLeft z).isOpenMap.image_mem_nhds hC
    simpa using h1
  -- Micro-step: an approximant in `closure (f '' W (k+1))` can be improved by an element
  -- of `W (k+1)`, leaving a residual in `closure (f '' W (k+2))`.
  have h_micro : ∀ (z : N) (k : ℕ), z ∈ closure (f '' W (k + 1)) →
      ∃ w ∈ W (k + 1), z - f w ∈ closure (f '' W (k + 2)) := by
    intro z k hz
    have hnbhd : (fun a => z - a) '' closure (f '' W (k + 2)) ∈ nhds z :=
      hnsub z _ (hclos (k + 2))
    obtain ⟨p, hp_mem, hp_im⟩ := (mem_closure_iff_nhds.mp hz) _ hnbhd
    obtain ⟨c, hc_mem, hc_eq⟩ := hp_mem
    obtain ⟨w, hw_mem, hw_eq⟩ := hp_im
    refine ⟨w, hw_mem, ?_⟩
    rw [hw_eq, ← hc_eq]
    simpa using hc_mem
  have h_key : closure (f '' W 1) ⊆ f '' W 0 := by
    intro y hy
    -- Build partial sums `S k` with invariant `y - f (S k) ∈ closure (f '' W (k+1))`.
    let D : (k : ℕ) → {s : M // y - f s ∈ closure (f '' W (k + 1))} := fun k =>
      Nat.rec
        (motive := fun k => {s : M // y - f s ∈ closure (f '' W (k + 1))})
        ⟨0, by simpa using hy⟩
        (fun k prev =>
          ⟨prev.1 + (h_micro (y - f prev.1) k prev.2).choose, by
            have hspec := (h_micro (y - f prev.1) k prev.2).choose_spec.2
            simpa [map_add, sub_add_eq_sub_sub] using hspec⟩)
        k
    set S : ℕ → M := fun k => (D k).1 with hS_def
    -- Invariant.
    have hS_inv : ∀ k, y - f (S k) ∈ closure (f '' W (k + 1)) := fun k => (D k).2
    -- Increment: `S (k+1) - S k ∈ W (k+1)`.
    have hS_incr : ∀ k, S (k + 1) - S k ∈ W (k + 1) := fun k => by
      have hSeq : S (k + 1) = S k + (h_micro (y - f (D k).1) k (D k).2).choose := rfl
      rw [hSeq, add_sub_cancel_left]
      exact (h_micro (y - f (D k).1) k (D k).2).choose_spec.1
    -- `W` is decreasing (each `W (n+1) ⊆ W n`).
    have hW_dec : ∀ n, W (n + 1) ⊆ W n := fun n x hx =>
      hW_shrink n ⟨x, hx, 0, hW_zero (n + 1), add_zero x⟩
    -- `S` is Cauchy (shrinking basis builder D.1).
    have hcauchy : CauchySeq S :=
      AddMonoidHom._sub_sub_lemma_D_1_cauchy_builder W hW_nhds hW_shrink hW_cofinal S
        (fun n => hW_dec n (hS_incr n))
    -- Limit `x` of `S`.
    obtain ⟨x, hx_tend⟩ := cauchySeq_tendsto_of_complete hcauchy
    -- Doubling sum lemma (mirrors the internal `hsum_lemma` of D.1): a sum of terms
    -- `xs i ∈ W (n + 1 + i)` lands in `W n`.
    have hsum_W : ∀ (k : ℕ) (n : ℕ) (xs : Fin k → M),
        (∀ i : Fin k, xs i ∈ W (n + 1 + i)) → ∑ i, xs i ∈ W n := by
      intro k
      induction k with
      | zero =>
        intro n xs _
        simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact hW_zero _
      | succ k ih =>
        intro n xs hxs
        rw [Fin.sum_univ_succ]
        have h0 : xs 0 ∈ W (n + 1) := by simpa using hxs 0
        have hrest : ∑ i, xs (Fin.succ i) ∈ W (n + 1) := by
          apply ih (n + 1)
          intro i
          convert hxs (Fin.succ i) using 2
          simp [Fin.val_succ]; ring
        exact hW_shrink _ (Set.add_mem_add h0 hrest)
    -- Each partial sum `S k` lies in `W 0` (telescoping with offset `0`).
    have hpartial : ∀ k, S k ∈ W 0 := by
      intro k
      have hsum_eq : S k - S 0 =
          ∑ i ∈ Finset.range k, (S (i + 1) - S i) :=
        (Finset.sum_range_sub S k).symm
      have hS0 : S 0 = 0 := rfl
      rw [hS0, sub_zero] at hsum_eq
      rw [hsum_eq, ← Fin.sum_univ_eq_sum_range]
      apply hsum_W k 0
      intro j
      have hji := hS_incr (j : ℕ)
      have : (0 + 1 + (j : ℕ)) = (j : ℕ) + 1 := by ring
      rw [this]
      exact hji
    -- `x ∈ W 0` (closed set containing the convergent sequence).
    have hx_W0 : x ∈ W 0 :=
      (hW_closed 0).mem_of_tendsto hx_tend (Filter.Eventually.of_forall hpartial)
    -- `W` is antitone.
    have hW_anti : Antitone W := antitone_nat_of_succ_le hW_dec
    -- `f x = y`: show `f (S k) → y` (residuals shrink to `0`) and `f (S k) → f x`,
    -- then use uniqueness of limits (`N` is T2).
    have hf_Sx : Filter.Tendsto (fun k => f (S k)) Filter.atTop (nhds (f x)) :=
      (hf.continuousAt (x := x)).tendsto.comp hx_tend
    -- Residual `y - f (S k) → 0` via the closed-neighbourhood basis at `0`.
    have htend0 : Filter.Tendsto (fun k => y - f (S k)) Filter.atTop (nhds (0 : N)) := by
      rw [(closed_nhds_basis (0 : N)).tendsto_right_iff]
      rintro Z ⟨hZ_nhds, hZ_closed⟩
      -- `f ⁻¹' Z` is a nbhd of `0` in `M`.
      have hpre : f ⁻¹' Z ∈ nhds (0 : M) := by
        have h0 : f (0 : M) = 0 := map_zero f
        exact hf.continuousAt (h0 ▸ hZ_nhds)
      obtain ⟨n, hn⟩ := hW_cofinal _ hpre
      -- `closure (f '' W n) ⊆ Z`.
      have hcl_sub : closure (f '' W n) ⊆ Z := by
        refine hZ_closed.closure_subset_iff.mpr ?_
        rintro _ ⟨m, hm, rfl⟩
        exact hn hm
      -- For `k ≥ n`, `y - f (S k) ∈ closure (f '' W (k+1)) ⊆ closure (f '' W n) ⊆ Z`.
      filter_upwards [Filter.eventually_ge_atTop n] with k hk
      have hkn : n ≤ k + 1 := by omega
      have hsub : closure (f '' W (k + 1)) ⊆ closure (f '' W n) :=
        closure_mono (Set.image_mono (hW_anti hkn))
      exact hcl_sub (hsub (hS_inv k))
    have hf_Sy : Filter.Tendsto (fun k => f (S k)) Filter.atTop (nhds y) := by
      have heq : (fun k => f (S k)) = fun k => y - (y - f (S k)) := by
        funext k; abel
      have hlim : Filter.Tendsto (fun k => y - (y - f (S k))) Filter.atTop (nhds (y - 0)) :=
        tendsto_const_nhds.sub htend0
      rw [sub_zero] at hlim
      rw [heq]
      exact hlim
    have hfx_eq : f x = y := tendsto_nhds_unique hf_Sx hf_Sy
    -- Conclude `y = f x ∈ f '' W 0`.
    exact ⟨x, hx_W0, hfx_eq⟩
  -- Conclude: `f '' U ⊇ f '' W 0 ⊇ closure (f '' W 1) ∈ nhds 0`.
  refine Filter.mem_of_superset (hclos 1) (h_key.trans (Set.image_mono hW0_subU))

open scoped Pointwise in
/-- **Wedhorn 6.16, faithful form** — Banach's open mapping theorem for topological `A`-modules
over a ring with a topologically nilpotent *unit* `ϖ`, with NO σ-compactness hypothesis (which is
unfulfillable for the Tate rings of interest: `Aⁿ` over `ℂ_p` / a Tate algebra is not σ-compact).
The "sequence of units → 0" structure supplies the Baire cover by dilation instead. This is the
form Wedhorn actually states (his proof is "Missing", deferring to BGR §3.7.2/1, which uses exactly
this module/units structure). -/
theorem wedhorn_6_16_of_topNilpUnit
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N] [ContinuousSMul A N]
    {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ) (hϖu : IsUnit ϖ)
    (f : M →ₗ[A] N) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f := by
  -- `N` is a Baire space: complete + countably-generated uniformity ⇒ metrizable ⇒ Baire.
  haveI : BaireSpace N := inferInstance
  -- Almost-open half (the dilation-cover Baire step replaces σ-compactness).
  have h_almost : ∀ U ∈ nhds (0 : M), closure (f '' U) ∈ nhds (0 : N) :=
    fun U hU => _omt_almost_open hϖ hϖu f hsurj hU
  -- Completion-upgrade half: almost-open + completeness of `M` ⇒ open at `0`.
  have h_zero : ∀ U ∈ nhds (0 : M), f '' U ∈ nhds (0 : N) :=
    fun U hU => _omt_open_at_zero f hf h_almost hU
  -- Translation invariance: open at `0` ⇒ open everywhere.
  exact AddMonoidHom._sub_lemma_translation f.toAddMonoidHom h_zero

open scoped Pointwise in
/-- **Topological embedding from a closed range via the σ-compact-free OMT.** If
`f : M →ₗ[A] N` is a continuous *injective* `A`-linear map between topological `A`-modules
over a ring with a topologically nilpotent unit `ϖ`, with `M` complete + countably-based and
the range of `f` closed (hence complete) + countably-based, then `f` is a topological
embedding — here phrased as `IsInducing ⇑f`. *Proof.* The corestriction `f̃ : M → range f`
is a continuous bijection (surjective onto its range, injective since `f` is); by Banach's
σ-compact-free OMT (`wedhorn_6_16_of_topNilpUnit`) it is open, hence a homeomorphism, hence
inducing; compose with the closed-subtype inclusion `range f ↪ N`, itself inducing. This is
the embedding half of Wedhorn Thm 8.28(b). -/
theorem isInducing_of_closedRange_of_topNilpUnit
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [ContinuousSMul A N] [T2Space N]
    {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ) (hϖu : IsUnit ϖ)
    (f : M →ₗ[A] N) (hf : Continuous f) (hinj : Function.Injective f)
    (hcl : IsClosed (LinearMap.range f : Set N)) :
    Topology.IsInducing (⇑f) := by
  -- The (closed) range, as a complete + countably-based topological `A`-module.
  haveI : IsUniformAddGroup ↥(LinearMap.range f) :=
    show IsUniformAddGroup ↥(LinearMap.range f).toAddSubgroup from inferInstance
  haveI : T2Space ↥(LinearMap.range f) := inferInstance
  haveI : CompleteSpace ↥(LinearMap.range f) := hcl.completeSpace_coe
  haveI : (uniformity ↥(LinearMap.range f)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  haveI : ContinuousSMul A ↥(LinearMap.range f) := by
    refine ⟨?_⟩
    rw [show (fun p : A × ↥(LinearMap.range f) => p.1 • p.2)
        = fun p => ⟨p.1 • (p.2 : N), Submodule.smul_mem _ p.1 p.2.2⟩ from rfl]
    exact Topology.IsInducing.subtypeVal.continuous_iff.mpr
      (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  -- `f̃ : M → range f`, the corestriction: continuous, bijective, and open by the OMT.
  have hcont : Continuous f.rangeRestrict :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr hf
  have hopen : IsOpenMap f.rangeRestrict :=
    wedhorn_6_16_of_topNilpUnit hϖ hϖu f.rangeRestrict hcont (LinearMap.surjective_rangeRestrict f)
  have hinjRR : Function.Injective f.rangeRestrict := fun x y h => hinj (Subtype.ext_iff.mp h)
  have hindRR : Topology.IsInducing f.rangeRestrict :=
    ((Equiv.ofBijective _ ⟨hinjRR, LinearMap.surjective_rangeRestrict f⟩).toHomeomorphOfContinuousOpen
      hcont hopen).isInducing
  -- `⇑f = Subtype.val ∘ f̃`; compose inducings.
  exact Topology.IsInducing.subtypeVal.comp hindRR

/-! ## Wedhorn 6.17 (= BGR §3.7.2/2) — noetherian iff every (sub)module closed

For a complete Tate-like ring `A` and a complete topological `A`-module `M`
with countably-generated uniformity: `M` is noetherian iff every `A`-submodule
of `M` is closed. In particular, `A` itself is noetherian iff every ideal is closed.

**Source** (Wedhorn 6.17, p. 49):
> "Let `A` be a complete Tate ring, and let `M` be a complete topological
> `A`-module that has a countable fundamental system of open neighborhoods
> of 0. Then `M` is noetherian if and only if every submodule of `M` is
> closed. In particular `A` is noetherian if and only if every ideal is
> closed."

**Proof outline** (BGR 3.7.2/2):
* (→) Noetherian ⇒ every submodule fg ⇒ closed: this is BGR 3.7.2/1 + observation.
* (←) Every submodule closed ⇒ ascending chain `M_1 ⊆ M_2 ⊆ …` has closed
  union `M' = ⋃ M_i`. `M'` is a Baire space; by Baire some `M_i` has nonempty
  interior in `M'`, hence equals `M'`.

### Layer 3 sub-lemmas (L3.1a, L3.1b, L3.2) -/

/-- **Sub-lemma L3.1a — BGR §3.7.2/1: completion of fg normed module is module itself**.

**Source** (BGR §3.7.2/1, p. 163, verbatim):
> "Proposition 1. Let A be a k-Banach algebra and let M be a normed A-module
> such that the completion M̂ of M is a finite A-module. Then M is complete.
> Proof. There are elements x_1, ..., x_n ∈ M̂ such that the homomorphism
> π : A^n → M̂ defined by π(a_1, ..., a_n) := Σᵢ aᵢxᵢ is surjective. By
> BANACH's Theorem, π is open, and therefore Σᵢ Ãx_i = π(Ãⁿ) is a neighborhood
> of 0 in M̂. Since M is dense in M̂, we have x_v ∈ M + Σᵤ Ãx_μ for v = 1, ..., n.
> Now NAKAYAMA's Lemma 1.2.4/6 yields M = M̂."

**Lean statement**: A normed A-module M whose completion `M̂` is finite as A-module
is itself complete (= already equals its completion).

**Discharge route**: `wedhorn_6_16` (Banach OMT for A-modules, Layer 2) +
Nakayama's lemma (mathlib: `Submodule.eq_of_le_of_finrank_eq` style; or direct
via `Module.eq_top_iff` + finiteness).

**Difficulty**: MEDIUM. ~50 lines. The Banach OMT input is the substantive part. -/
theorem _sub_lemma_L3_1a_completion_fg_complete
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [(uniformity M).IsCountablyGenerated] [T2Space M]
    (hM_fg : Module.Finite A M) :
    CompleteSpace M := by
  -- BGR §3.7.2/1 strategy (completion-embedding):
  -- 1. M ⊆ M̂ := UniformSpace.Completion M, where M̂ is complete + cg + T2.
  -- 2. M̂ inherits Module A structure via UniformSpace.Completion.Module instance.
  -- 3. The image of the n generators in M̂ spans a dense subspace which IS the
  --    image of M in M̂ (since span A {generators} = M algebraically).
  -- 4. Apply wedhorn_6_16 to the canonical A-linear ν̂ : Aⁿ → M̂ (which is
  --    surjective: image is dense + closed since fg + ContinuousSMul on M̂).
  --    For ν̂ surjective we need M̂ to be fg over A — not automatic from
  --    Module.Finite A M; requires Nakayama-style argument that the closure
  --    of finite-span-in-M̂ is finite-span-in-M̂ (i.e., span A {m_i} = M̂ in M̂).
  -- 5. Open ν̂ ⇒ image is open in M̂ ⇒ M open + dense + (M̂ T2) ⇒ M = M̂.
  -- 6. Hence M is complete.
  --
  -- Requires:
  -- - [ContinuousSMul A M] (per BINDING-RULE (b); not yet in hypothesis bundle).
  -- - UniformSpace.Completion M's Module A structure (mathlib instance).
  -- - The closure-span = span argument (Nakayama for fg M̂).
  sorry

open scoped Pointwise in
/-- **BGR §3.7.2/1 (faithful, closure form)**: a submodule `N` of a complete Tate-`A`-module `M`
whose topological closure is module-finite over `A` is itself closed. (Wedhorn 6.17/6.18 route;
proof "Missing" in Wedhorn → BGR §3.7.2/1.) The completion `M̂` of `N` is its closure `N̄ ⊆ M`;
`N̄` finite ⟹ via the faithful OMT `π : Aⁿ ↠ N̄` is open, so a top-nilpotent nbhd dilates onto a
nbhd of 0; density of `N` in `N̄` writes each generator `yᵥ = mᵥ + Σ ǎᵥμ yμ` (`ǎ` top-nilp,
`mᵥ ∈ N`); the matrix Nakayama (`eq_zero_of_forall_eq_sum_topNilp_smul`) in `M ⧸ N` forces every
`yᵥ ∈ N`, so `N̄ = N`.

**Source** (BGR §3.7.2/1, p. 163, verbatim): see `_sub_lemma_L3_1a_completion_fg_complete`. -/
theorem fg_topologicalClosure_isClosed
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M] [ContinuousSMul A M]
    (N : Submodule A M) (hfin : Module.Finite A N.topologicalClosure) :
    IsClosed (N : Set M) := by
  classical
  -- It suffices to prove `N̄ ≤ N` (then `N̄ = N`, so `N` is closed).
  set Nbar : Submodule A M := N.topologicalClosure with hNbar_def
  -- `↥N̄` is a complete cg T2 `A`-module (closed subspace of complete `M`).
  have hNbar_closed : IsClosed (Nbar : Set M) := N.isClosed_topologicalClosure
  haveI : IsUniformAddGroup ↥Nbar :=
    show IsUniformAddGroup ↥Nbar.toAddSubgroup from inferInstance
  haveI : (uniformity ↥Nbar).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  haveI : CompleteSpace ↥Nbar := hNbar_closed.completeSpace_coe
  haveI : T2Space ↥Nbar := inferInstance
  haveI : ContinuousSMul A ↥Nbar := ⟨by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp
      ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))⟩
  -- `N` as a submodule of `↥N̄`.
  set N' : Submodule A ↥Nbar := N.comap Nbar.subtype with hN'_def
  -- **Density**: `N'` is dense in `↥N̄`.
  have hN_le_Nbar : N ≤ Nbar := N.le_topologicalClosure
  have hN'_dense : Dense (N' : Set ↥Nbar) := by
    have himg : Subtype.val '' (N' : Set ↥Nbar) = (N : Set M) := by
      ext z
      exact ⟨fun ⟨⟨w, _⟩, hwN, hwz⟩ => hwz ▸ hwN, fun hz => ⟨⟨z, hN_le_Nbar hz⟩, hz, rfl⟩⟩
    intro x
    rw [closure_subtype, himg, ← N.topologicalClosure_coe]
    exact x.2
  -- **Step 1**: generators of `↥N̄` and the OMT-open map `π : Aⁿ → ↥N̄`.
  obtain ⟨n, g, hg_span⟩ := Module.Finite.exists_fin (R := A) (M := ↥Nbar)
  let π : (Fin n → A) →ₗ[A] ↥Nbar :=
    { toFun := fun a => ∑ i, a i • g i
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hπ_cont : Continuous π := by
    change Continuous fun a : (Fin n → A) => ∑ i, a i • g i
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hπ_surj : Function.Surjective π := by
    intro x
    have hx : x ∈ Submodule.span A (Set.range g) := hg_span ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, hc⟩
  -- topologically nilpotent unit `ϖ`.
  obtain ⟨ϖ, hϖ_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hπ_open : IsOpenMap π :=
    wedhorn_6_16_of_topNilpUnit hϖ_nil ϖ.isUnit π hπ_cont hπ_surj
  -- **Step 2**: a top-nilpotent nbhd `W` of `0` in `A`, and the dilation nbhd `Ω` of `0` in `↥N̄`.
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  set W : Set A := (ϖ : A) • (TopologicalRing.powerBoundedSubring A : Set A) with hW_def
  have hW_nhds : W ∈ nhds (0 : A) :=
    (ϖ.isUnit.isOpenMap_smul _ P.isOpen_powerBoundedSubring).mem_nhds
      ⟨0, (TopologicalRing.powerBoundedSubring.toSubring A).zero_mem, smul_zero _⟩
  have hW_tn : ∀ a ∈ W, IsTopologicallyNilpotent a := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [smul_eq_mul]
    rw [mul_comm]
    exact hb.isTopologicallyNilpotent_mul hϖ_nil
  -- The product nbhd in `Aⁿ`.
  set Wpi : Set (Fin n → A) := Set.univ.pi (fun _ => W) with hWpi_def
  have hWpi_nhds : Wpi ∈ nhds (0 : Fin n → A) := by
    rw [hWpi_def]
    exact set_pi_mem_nhds Set.finite_univ (fun i _ => by simpa using hW_nhds)
  set Ω : Set ↥Nbar := π '' Wpi with hΩ_def
  have hΩ_nhds : Ω ∈ nhds (0 : ↥Nbar) := by
    have := hπ_open.image_mem_nhds (x := (0 : Fin n → A)) hWpi_nhds
    rwa [map_zero] at this
  -- **Step 3 + 4 + 5**: density extraction + Nakayama in `M ⧸ N` + conclusion.
  -- The quotient map `q : M →ₗ[A] M ⧸ N`.
  -- For each generator `gᵥ`, density gives `m'ᵥ ∈ N'` with `gᵥ - m'ᵥ ∈ Ω`, i.e.
  -- `(gᵥ : M) - (m'ᵥ : M) = ∑ⱼ aᵥⱼ • (gⱼ : M)` with `aᵥⱼ ∈ W` top-nilp.
  have hgen_in_N : ∀ v : Fin n, ((g v : ↥Nbar) : M) ∈ N := by
    -- **Step 3** (density extraction): for each generator `gᵥ`, write
    -- `gᵥ = m'ᵥ + ∑ⱼ aᵥⱼ • gⱼ` with `m'ᵥ ∈ N'` and every `aᵥⱼ ∈ W` (topologically nilpotent).
    have hextract : ∀ v : Fin n, ∃ (a : Fin n → A), (∀ j, a j ∈ W) ∧
        ∃ m' ∈ N', (g v : ↥Nbar) = m' + ∑ j, a j • g j := by
      intro v
      have hnb : (fun z : ↥Nbar => g v - z) ⁻¹' Ω ∈ nhds (g v) := by
        have hcont : Continuous (fun z : ↥Nbar => g v - z) := continuous_const.sub continuous_id
        refine hcont.continuousAt.preimage_mem_nhds ?_
        show Ω ∈ nhds (g v - g v)
        rw [sub_self]; exact hΩ_nhds
      obtain ⟨w, hwU, hwN'⟩ := mem_closure_iff_nhds.mp (hN'_dense (g v)) _ hnb
      obtain ⟨a, haW, ha_eq⟩ := hwU
      refine ⟨a, fun j => (Set.mem_univ_pi.mp haW) j, w, hwN', ?_⟩
      have hpa : (∑ j, a j • g j) = g v - w := ha_eq
      rw [hpa]; abel
    -- Choose the matrix entries and the `N`-correctors.
    choose a haW m' hm'N' hrel using hextract
    set Atil : Matrix (Fin n) (Fin n) A := fun v j => a v j with hAtil
    set q : M →ₗ[A] M ⧸ N := N.mkQ with hq
    set ybar : Fin n → M ⧸ N := fun v => q ((g v : ↥Nbar) : M) with hybar
    have hmem : ∀ v, ((m' v : ↥Nbar) : M) ∈ N := fun v => hm'N' v
    -- Push the `↥N̄`-relation down to `M`.
    have hrelM : ∀ v, ((g v : ↥Nbar) : M)
        = ((m' v : ↥Nbar) : M) + ∑ j, a v j • ((g j : ↥Nbar) : M) := by
      intro v
      have hcoe := congrArg (Subtype.val) (hrel v)
      rw [Submodule.coe_add, Submodule.coe_sum] at hcoe
      simpa [Submodule.coe_smul] using hcoe
    -- **Step 4** (Nakayama in `M ⧸ N`): the relation becomes `ȳᵥ = ∑ⱼ Ãᵥⱼ • ȳⱼ`.
    have hy : ∀ v, ybar v = ∑ j, Atil v j • ybar j := by
      intro v
      have hq0 : q ((m' v : ↥Nbar) : M) = 0 := (Submodule.Quotient.mk_eq_zero N).2 (hmem v)
      simp only [hybar, hAtil]
      rw [hrelM v, map_add, map_sum, hq0]
      simp only [map_smul]
      exact zero_add _
    -- The matrix `1 - Ã` is invertible (all entries top-nilp), so `ȳ = 0`.
    have hzero := eq_zero_of_forall_eq_sum_topNilp_smul (B := Atil)
      (fun i j => hW_tn _ (haW i j)) hy
    -- `ȳᵥ = q gᵥ = 0` means `gᵥ ∈ N`.
    intro v
    exact (Submodule.Quotient.mk_eq_zero N).1 (hzero v)
  -- **Step 5**: `N̄ ≤ N` from the generators.
  have hNbar_le_N : Nbar ≤ N := by
    intro m hm
    have hx : (⟨m, hm⟩ : ↥Nbar) ∈ Submodule.span A (Set.range g) := hg_span ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have hval : ((∑ i, c i • g i : ↥Nbar) : M) = m := by rw [hc]
    rw [← hval, Submodule.coe_sum]
    exact N.sum_mem fun i _ => by
      rw [Submodule.coe_smul]
      exact N.smul_mem _ (hgen_in_N i)
  -- Conclude.
  have : Nbar = N := le_antisymm hNbar_le_N hN_le_Nbar
  rw [← this]
  exact hNbar_closed

/-- **Sub-lemma L3.1b — fg submodule of complete noeth module is closed**.

Direct corollary of L3.1a applied to the submodule N ⊆ M (with N inheriting
the subspace uniformity from M). The completion `N̂` is fg (= `Module.Finite A N`
when A noeth + N fg over A, by Hilbert), so N is complete, so N is closed in M.

**Discharge**: L3.1a + `IsClosed.of_completeSpace` (for closed subset of T2 space,
complete subspace is closed).

**Difficulty**: EASY. ~25 lines. -/
theorem _sub_lemma_L3_1b_fg_submodule_closed
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
    (N : Submodule A M) (hN_fg : N.FG) :
    IsClosed (N : Set M) := by
  -- ↥N inherits subspace uniform structure from M.
  haveI : IsUniformAddGroup ↥N :=
    show IsUniformAddGroup ↥N.toAddSubgroup from inferInstance
  haveI : (uniformity ↥N).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  haveI : Module.Finite A ↥N := (Module.Finite.iff_fg (N := N)).mpr hN_fg
  -- L3.1a gives CompleteSpace ↥N for the fg subspace.
  haveI : CompleteSpace ↥N := _sub_lemma_L3_1a_completion_fg_complete (A := A) (M := ↥N)
    inferInstance
  -- Complete subset of T2 ambient ⇒ closed.
  exact (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace ↥N›).isClosed

/-! `_sub_lemma_L3_2_baire_chain` (AddSubgroup version) removed (2026-05-18).

The AddSubgroup-level statement was B2 false (`b2_log.jsonl` entry 2,
counterexample: `M = ⊕_n ℤ/2ℤ` with discrete topology — every subgroup is
trivially closed but the chain `⊕_{n ≤ k} ℤ/2ℤ` never stabilises). The
*Submodule* variant below is provable because the `A`-module scalar action
supplies the absorbing structure that the AddGroup-level argument lacks; it
is the variant the consumer (`wedhorn_6_17`) actually uses.
-/

/-- **Sub-lemma L3.2-Submodule — Baire chain stationary for Submodules**.

Variant of L3.2 for `Submodule A M` (not `AddSubgroup M`), needed for the
reverse direction of `wedhorn_6_17`. The argument is the same Baire +
absorbing structure but uses the *A-module* scalar action for the
absorbing step: given a chain k₀ with nonempty interior in M_∞ := ⨆ chain
and any m ∈ M_∞, a topologically nilpotent unit π ∈ A satisfies
π^n • m → 0; eventually π^n • m ∈ chain k₀; then m = π^(-n) • (π^n • m) ∈
chain k₀ since chain k₀ is A-stable and π^n is a unit.

Per BINDING-RULE (b): the absorbing argument requires `[IsTateRing A]`
(for topologically nilpotent units) and `[ContinuousSMul A M]` (for
π^n • m → 0). Without these, the conclusion is false (exotic topologies
on M can have all-submodules-closed without M noeth). -/
theorem _sub_lemma_L3_2_baire_chain_submodule
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    (h_all_closed : ∀ N : Submodule A M, IsClosed (N : Set M))
    (chain : ℕ → Submodule A M) (hchain : Monotone chain) :
    ∃ N : ℕ, ∀ n ≥ N, chain n = chain N := by
  -- M_∞ = union of chain (= iSup since monotone).
  set M_inf : Submodule A M := iSup chain with hM_inf_def
  have hk_le_inf : ∀ k, chain k ≤ M_inf := fun k => le_iSup chain k
  -- M_inf is closed (by hypothesis).
  have hM_inf_closed : IsClosed (M_inf : Set M) := h_all_closed M_inf
  -- ↥M_inf inherits subspace structure.
  haveI : IsUniformAddGroup ↥M_inf :=
    show IsUniformAddGroup ↥M_inf.toAddSubgroup from inferInstance
  haveI : (uniformity ↥M_inf).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  haveI : CompleteSpace ↥M_inf := hM_inf_closed.completeSpace_coe
  haveI : T2Space ↥M_inf := inferInstance
  -- Each chain k is closed in M (hypothesis), hence closed in ↥M_inf via preimage.
  have hk_closed_in_inf : ∀ k, IsClosed
      ((Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M)) := fun k =>
    (h_all_closed (chain k)).preimage continuous_subtype_val
  -- M_inf = ⋃ k, chain k as Sets of M, via directed iSup (monotone ⇒ directed).
  have h_inf_union : (M_inf : Set M) = ⋃ k, (chain k : Set M) :=
    Submodule.coe_iSup_of_directed _ hchain.directed_le
  -- Lift to ↥M_inf: univ = ⋃ k, (preimage of chain k via Subtype.val).
  have h_subtype_univ :
      ⋃ k, ((Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M)) = Set.univ := by
    ext ⟨x, hx⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    have : x ∈ (M_inf : Set M) := hx
    rw [h_inf_union, Set.mem_iUnion] at this
    exact this
  -- Nonempty witness for C.2.
  haveI : Nonempty ↥M_inf := ⟨⟨0, M_inf.zero_mem⟩⟩
  -- Apply C.2 (Baire): some chain k₀ has nonempty interior in ↥M_inf.
  obtain ⟨k₀, hk₀_int⟩ := AddMonoidHom._sub_sub_lemma_C_2_baire_nonempty_interior
    (fun k => (Subtype.val : ↥M_inf → M) ⁻¹' (chain k : Set M))
    hk_closed_in_inf h_subtype_univ
  -- Extract nbhd of 0 in ↥M_inf inside chain k₀'s preimage via translation.
  obtain ⟨y, hy_int⟩ := hk₀_int
  rw [mem_interior] at hy_int
  obtain ⟨V, hV_sub, hV_open, hy_V⟩ := hy_int
  set V₀ : Set ↥M_inf := (· - y) '' V with hV₀_def
  have hV₀_open : IsOpen V₀ := (Homeomorph.subRight y).isOpenMap _ hV_open
  have h0_V₀ : (0 : ↥M_inf) ∈ V₀ := ⟨y, hy_V, sub_self y⟩
  have hV₀_nhds : V₀ ∈ nhds (0 : ↥M_inf) := hV₀_open.mem_nhds h0_V₀
  -- V₀ ⊆ chain k₀'s preimage (chain k₀ is subgroup-closed).
  have hV₀_sub : V₀ ⊆ (Subtype.val : ↥M_inf → M) ⁻¹' (chain k₀ : Set M) := by
    rintro z ⟨w, hwV, rfl⟩
    change ((w - y : ↥M_inf) : M) ∈ chain k₀
    have hwk : (w : M) ∈ chain k₀ := hV_sub hwV
    have hyk : (y : M) ∈ chain k₀ := hV_sub hy_V
    push_cast
    exact (chain k₀).sub_mem hwk hyk
  -- Establish ContinuousSMul A ↥M_inf via the subspace IsInducing.
  haveI : ContinuousSMul A ↥M_inf := ⟨by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp
      ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))⟩
  -- Get topologically nilpotent unit π from IsTateRing.
  obtain ⟨π, hπ_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  -- Show M_inf ⊆ chain k₀ via absorption.
  have h_inf_sub : M_inf ≤ chain k₀ := by
    intro m hm
    -- Lift m to ↥M_inf.
    let m_lift : ↥M_inf := ⟨m, hm⟩
    -- π^n • m_lift → 0 in ↥M_inf via ContinuousSMul + π^n → 0.
    have h_pow_tend : Filter.Tendsto (fun n : ℕ => (π : A) ^ n) Filter.atTop (nhds 0) :=
      hπ_nil
    have h_smul_tend :
        Filter.Tendsto (fun n : ℕ => (π : A) ^ n • m_lift) Filter.atTop (nhds 0) := by
      have h0 : (0 : A) • m_lift = 0 := zero_smul A m_lift
      exact h0 ▸ Filter.Tendsto.smul h_pow_tend tendsto_const_nhds
    -- Eventually π^n • m_lift ∈ V₀.
    obtain ⟨N, hN⟩ := (h_smul_tend.eventually hV₀_nhds).exists
    -- π^N • m_lift ∈ V₀ ⊆ chain k₀ preimage.
    have h_lift_in : ((π : A) ^ N • m_lift : ↥M_inf) ∈
        (Subtype.val : ↥M_inf → M) ⁻¹' (chain k₀ : Set M) := hV₀_sub hN
    -- Equivalently π^N • m ∈ chain k₀.
    have h_pi_m_in : (π : A) ^ N • m ∈ chain k₀ := h_lift_in
    -- m = (π^N)⁻¹ • (π^N • m), and chain k₀ is A-stable.
    have hπN_val : ((π ^ N : Aˣ) : A) = (π : A) ^ N := by
      push_cast; rfl
    have hmem : (((π ^ N : Aˣ)⁻¹ : Aˣ) : A) • ((π : A) ^ N • m) ∈ chain k₀ :=
      (chain k₀).smul_mem _ h_pi_m_in
    have h_eq : m = (((π ^ N : Aˣ)⁻¹ : Aˣ) : A) • ((π : A) ^ N • m) := by
      rw [← smul_assoc, smul_eq_mul, ← hπN_val, ← Units.val_mul]
      simp
    rw [h_eq]
    exact hmem
  -- M_inf = chain k₀ (both directions: ⊆ from h_inf_sub, ⊇ from hk_le_inf).
  have h_inf_eq : M_inf = chain k₀ := le_antisymm h_inf_sub (hk_le_inf k₀)
  -- For n ≥ k₀: chain n ≤ M_inf = chain k₀, and chain k₀ ≤ chain n by monotone.
  refine ⟨k₀, fun n hn => le_antisymm ?_ (hchain hn)⟩
  rw [h_inf_eq] at hk_le_inf
  exact hk_le_inf n

theorem wedhorn_6_17
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [IsNoetherianRing A]
      [IsTopologicalRing A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M] :
    IsNoetherian A M ↔ ∀ N : Submodule A M, IsClosed (N : Set M) := by
  constructor
  · -- Forward: every submodule fg + L3.1b ⇒ every submodule closed.
    intro hM N
    have hN_fg : N.FG := IsNoetherian.noetherian (R := A) N
    exact _sub_lemma_L3_1b_fg_submodule_closed N hN_fg
  · -- Reverse: chain stationary via L3.2 Submodule variant.
    intro h_all_closed
    rw [isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]
    intro chain
    obtain ⟨N, hN⟩ := _sub_lemma_L3_2_baire_chain_submodule h_all_closed
      (fun n => chain n) chain.monotone
    exact ⟨N, fun m hm => (hN m hm).symm⟩

/-- **Wedhorn 6.17 specialised to A itself** — A complete Tate-like noetherian
ring has all ideals closed (and conversely). -/
theorem wedhorn_6_17_ideal
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsTopologicalRing A] [IsTateRing A] :
    IsNoetherianRing A ↔ ∀ I : Ideal A, IsClosed (I : Set A) := by
  -- Specialise wedhorn_6_17 to M = A. Need [IsNoetherianRing A] for forward
  -- direction, but here it appears as iff LHS. Split into two directions.
  constructor
  · intro hA
    haveI : IsNoetherianRing A := hA
    exact (wedhorn_6_17 (A := A) (M := A)).mp hA
  · intro h_all
    -- Reverse: derive IsNoetherian A A from chain stationarity via L3.2 Submodule.
    change IsNoetherian A A
    rw [isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]
    intro chain
    obtain ⟨N, hN⟩ := _sub_lemma_L3_2_baire_chain_submodule h_all
      (fun n => chain n) chain.monotone
    exact ⟨N, fun m hm => (hN m hm).symm⟩

/-! ## Wedhorn 6.18 (= BGR §3.7.3) — unique fg-module topology + maps strict

For a complete noetherian Tate ring `A`, every finitely generated `A`-module
has a unique complete countably-generated A-module topology; A-linear maps
between such modules are continuous and open onto image.

**Source** (Wedhorn 6.18, p. 50):
> "Every finitely generated `A`-module has a unique `A`-module topology that
> is complete and that has a countable fundamental system of open
> neighborhoods of 0. Let `f : M → N` be an `A`-linear map of finitely
> generated modules that are endowed with the topology from (1). Then `f`
> is continuous and the map `f : M → f(M)` is open."

**Decomposition into sub-lemmas L4.1–L4.4**: see below.

### Layer 4 sub-lemmas (Wedhorn 6.18 — BGR §3.7.3) -/

/-- **Sub-lemma L4.1 — Quotient of complete countably-generated is complete countably-generated**.

For a closed subgroup K ⊆ M with M complete + countably-generated uniformity,
the quotient M/K (with quotient topology) is also complete + countably-generated.

**Source**: standard topological group fact. Mathlib has
`AddSubgroup.QuotientAddGroup.CompleteSpace`-style instances.

**Mathlib search**:
- `Quotient.completeSpace` for quotients of complete uniform spaces.
- `Quotient.uniformContinuous_mk` for quotient map continuity.

**Difficulty**: EASY-MEDIUM. ~30 lines. Mostly assembling existing instances. -/
theorem _sub_lemma_L4_1_quotient_complete
    {A : Type u} [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
    (K : Submodule A M) (_hK_closed : IsClosed (K : Set M)) :
    -- Existential: there exists a uniformity on M ⧸ K making the quotient
    -- map continuous + the quotient complete + countably-generated.
    -- (The canonical quotient uniformity from K.toAddSubgroup; existence stated
    -- here, instance derivation done at use site.)
    ∃ (τ : UniformSpace (M ⧸ K)),
      @IsUniformAddGroup _ τ _ ∧
      @CompleteSpace _ τ ∧
      (@uniformity _ τ).IsCountablyGenerated := by
  -- M is first-countable from countably-generated uniformity (mathlib instance)
  haveI : FirstCountableTopology M := UniformSpace.firstCountableTopology M
  -- Quotient is first-countable (mathlib instance, needs explicit subgroup arg)
  haveI : FirstCountableTopology (M ⧸ K) :=
    QuotientAddGroup.instFirstCountableTopology K.toAddSubgroup
  -- Take τ := canonical right uniform space from the topological additive group structure.
  letI τ : UniformSpace (M ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (M ⧸ K)
  refine ⟨τ, ?_, ?_, ?_⟩
  · -- IsUniformAddGroup via abelian-group lemma
    exact isUniformAddGroup_of_addCommGroup
  · -- CompleteSpace: use mathlib's QuotientAddGroup.completeSpace_right instance.
    -- With τ in scope as the default UniformSpace, inferInstance finds it.
    exact QuotientAddGroup.completeSpace_right M K.toAddSubgroup
  · -- IsCountablyGenerated via IsUniformAddGroup.uniformity_countably_generated;
    -- needs IsUniformAddGroup w.r.t. our chosen τ + IsCountablyGenerated (𝓝 0).
    haveI : @IsUniformAddGroup (M ⧸ K) τ _ := isUniformAddGroup_of_addCommGroup
    exact IsUniformAddGroup.uniformity_countably_generated

/-- **Sub-lemma L4.2 — A-linear map between fg modules is continuous**.

**Source** (BGR §3.7.3/2, p. 164, verbatim):
> "Proposition 2. If M, M' are objects of 𝔐_A, each A-linear map φ : M → M' is
> continuous. Proof. Choose an epimorphism π : A^n ↠ M for a suitable n ∈ ℕ.
> Define φ' : A^n → M' by φ' := φ ∘ π. Since addition and scalar multiplication
> are continuous operations in normed modules, both maps π and φ' are continuous.
> Furthermore π is open (by BANACH's Theorem). Hence φ is continuous."

**Lean statement**: identical to `wedhorn_6_18_continuous` below.

**Discharge route**:
- Choose surjection π : A^n ↠ M (via `Module.Finite`).
- π is continuous (sum of coordinate projections × x_i, all continuous in normed
  modules — uses `IsUniformAddGroup` continuity of add + smul).
- π is open by `wedhorn_6_16` (Layer 2).
- φ ∘ π is continuous (composition).
- φ = (φ ∘ π) ∘ π⁻¹ where π⁻¹ is the quotient map (well-defined via open π).

**Difficulty**: MEDIUM. ~60 lines. -/
theorem _sub_lemma_L4_2_continuous_via_OMT
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [SigmaCompactSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    Continuous f := by
  -- BGR §3.7.3/2 proof.
  -- Pick a finite generating set s : Fin n → M.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  -- Define ν : (Fin n → A) →ₗ[A] M by ν a = ∑ i, a i • s i.
  let ν : (Fin n → A) →ₗ[A] M :=
    { toFun := fun a => ∑ i, a i • s i
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul] }
  -- ν continuous via ContinuousSMul A M.
  have hν_cont : Continuous ν := by
    change Continuous fun a : (Fin n → A) => ∑ i, a i • s i
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  -- ν surjective from hs.
  have hν_surj : Function.Surjective ν := by
    intro m
    have hm : m ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, hc⟩
  -- By wedhorn_6_16, ν is open. (Needs T2Space M on target — supplied.)
  have hν_open : IsOpenMap ν := wedhorn_6_16 ν hν_cont hν_surj
  -- ν is a quotient map.
  have hν_quot : Topology.IsQuotientMap ν := hν_open.isQuotientMap hν_cont hν_surj
  -- f ∘ ν continuous via ContinuousSMul A N.
  have hfν_cont : Continuous (f ∘ ν) := by
    change Continuous fun a : (Fin n → A) => f (∑ i, a i • s i)
    simp only [map_sum, map_smul]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  -- f continuous via quotient map.
  exact hν_quot.continuous_iff.mpr hfν_cont

/-- **Sub-lemma L4.3 — A-linear map is open onto image (strict)**.

**Source** (BGR §3.7.3/Proposition 4, p. 165, verbatim):
> "Proposition 4. A continuous k-linear map φ : X → Y between k-Banach spaces is
> strict if and only if φ(X) is closed in Y. From this we immediately conclude
> Corollary 5. Each A-module homomorphism φ : M → M', where M, M' ∈ 𝔐_A, is strict."

**Lean statement**: the rangeFactorization of f is open.

**Discharge route** (faithful, σ-compact-free):
- `f` is continuous (BGR §3.7.3/2 inlined via the faithful OMT
  `wedhorn_6_16_of_topNilpUnit`, using `[IsTateRing A]`'s topologically nilpotent unit).
- Image `f(M)` is fg (image of fg under a linear map); its topological closure is a
  submodule of the noetherian `A`-module `N` (`[IsNoetherianRing A]` + `Module.Finite A N`),
  hence module-finite, hence `f(M)` is closed by `fg_topologicalClosure_isClosed` (BGR §3.7.2/1).
- Image with subspace topology = quotient topology by the faithful Banach OMT
  `wedhorn_6_16_of_topNilpUnit`, applied to `f.rangeRestrict` (surjective onto its image).

**Difficulty**: MEDIUM. ~70 lines. -/
theorem _sub_lemma_L4_3_strict_via_closed_image
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsTateRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) := by
  -- BGR §3.7.3/Cor 5: f.range is fg (image of fg under linear map), so closed in
  -- N by BGR §3.7.2/1 (`fg_topologicalClosure_isClosed`). Then ↥(f.range) inherits
  -- a complete T2 cg uag subspace structure, and the faithful OMT
  -- `wedhorn_6_16_of_topNilpUnit` applied to f.rangeRestrict (= f viewed as map to
  -- its range) gives openness. Set.rangeFactorization = f.rangeRestrict up to type
  -- identity.
  classical
  -- A topologically nilpotent unit `ϖ` of `A` (Tate ring), reused throughout.
  obtain ⟨ϖ, hϖ_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  -- Step 1: f.range as Submodule A N is fg (image of ⊤ under f, which is fg).
  have hrange_fg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f
  -- Step 2: f.range is closed via BGR §3.7.2/1 (`fg_topologicalClosure_isClosed`).
  -- Its topological closure is a submodule of the noetherian module `N`
  -- (`N` finite over the noetherian ring `A`), hence finitely generated, hence
  -- module-finite over `A`.
  have hclos_fin : Module.Finite A ↥((LinearMap.range f).topologicalClosure) :=
    (Module.Finite.iff_fg (N := (LinearMap.range f).topologicalClosure)).mpr
      (IsNoetherian.noetherian (LinearMap.range f).topologicalClosure)
  have hrange_closed : IsClosed (LinearMap.range f : Set N) :=
    fg_topologicalClosure_isClosed (LinearMap.range f) hclos_fin
  -- Step 3: subspace typeclass setup on ↥f.range.
  haveI : IsUniformAddGroup ↥(LinearMap.range f) :=
    show IsUniformAddGroup ↥(LinearMap.range f).toAddSubgroup from inferInstance
  haveI : (uniformity ↥(LinearMap.range f)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  haveI : CompleteSpace ↥(LinearMap.range f) :=
    hrange_closed.completeSpace_coe
  haveI : T2Space ↥(LinearMap.range f) :=
    inferInstance  -- Subtype T2 from T2 N
  haveI : Module.Finite A ↥(LinearMap.range f) :=
    (Module.Finite.iff_fg (N := LinearMap.range f)).mpr hrange_fg
  -- ContinuousSMul on subspace: A × ↥range → ↥range factors through
  -- A × N → N via Subtype.val on the codomain.
  haveI : ContinuousSMul A ↥(LinearMap.range f) := by
    refine ⟨?_⟩
    -- Continuous fun p : A × ↥(LinearMap.range f) => p.1 • p.2 : ↥(LinearMap.range f)
    -- Equivalently, Continuous of (a, x) ↦ ⟨a • x.1, ...⟩.
    -- Use IsInducing.continuous_iff: Subtype.val of the SMul output is the
    -- continuous SMul A × N → N restricted.
    rw [show (fun p : A × ↥(LinearMap.range f) => p.1 • p.2) =
        fun p => ⟨p.1 • (p.2 : N), Submodule.smul_mem _ p.1 p.2.2⟩ from rfl]
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp ((continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd)))
  -- Step 4a: `f` is continuous (BGR §3.7.3/2, inlined with the faithful OMT
  -- `wedhorn_6_16_of_topNilpUnit`, since the σ-compact `_sub_lemma_L4_2_continuous_via_OMT`
  -- is unavailable here). Pick a finite generating set `s : Fin n → M`, build the
  -- surjection `ν : (Fin n → A) → M`, which is open by the faithful OMT, hence a
  -- quotient map; then `f = (f ∘ ν) ∘ ν⁻¹` is continuous.
  have hf_cont : Continuous f := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
    let ν : (Fin n → A) →ₗ[A] M :=
      { toFun := fun a => ∑ i, a i • s i
        map_add' := fun x y => by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a x => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
            smul_smul] }
    have hν_cont : Continuous ν := by
      change Continuous fun a : (Fin n → A) => ∑ i, a i • s i
      exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    have hν_surj : Function.Surjective ν := by
      intro m
      have hm : m ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      exact ⟨c, hc⟩
    have hν_open : IsOpenMap ν :=
      wedhorn_6_16_of_topNilpUnit hϖ_nil ϖ.isUnit ν hν_cont hν_surj
    have hν_quot : Topology.IsQuotientMap ν := hν_open.isQuotientMap hν_cont hν_surj
    have hfν_cont : Continuous (f ∘ ν) := by
      change Continuous fun a : (Fin n → A) => f (∑ i, a i • s i)
      simp only [map_sum, map_smul]
      exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    exact hν_quot.continuous_iff.mpr hfν_cont
  -- Step 4b: `f.rangeRestrict` is continuous (Subtype.val ∘ f.rangeRestrict = f).
  have hf_rangeRestrict_cont : Continuous (f.rangeRestrict : M →ₗ[A] LinearMap.range f) :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr hf_cont
  have hf_rangeRestrict_surj : Function.Surjective f.rangeRestrict :=
    LinearMap.surjective_rangeRestrict f
  -- Step 4c: the faithful OMT gives IsOpenMap (f.rangeRestrict).
  have hf_rangeRestrict_open : IsOpenMap f.rangeRestrict :=
    wedhorn_6_16_of_topNilpUnit hϖ_nil ϖ.isUnit f.rangeRestrict
      hf_rangeRestrict_cont hf_rangeRestrict_surj
  -- `Set.rangeFactorization f` factors through `f.rangeRestrict` via the
  -- (value-preserving) homeomorphism `↥(LinearMap.range f) ≃ₜ ↥(Set.range f)`
  -- (the two subtypes have the same underlying set, `LinearMap.coe_range`).
  let e : ↥(LinearMap.range f) ≃ₜ ↥(Set.range ⇑f) :=
    { toFun := fun x => ⟨x.1, Set.mem_range.mpr (LinearMap.mem_range.mp x.2)⟩
      invFun := fun x => ⟨x.1, LinearMap.mem_range.mpr (Set.mem_range.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  have hcomp : Set.rangeFactorization ⇑f = ⇑e ∘ ⇑f.rangeRestrict := by
    funext a
    exact Subtype.coe_injective rfl
  rw [hcomp]
  exact e.isOpenMap.comp hf_rangeRestrict_open

/-- **Sub-lemma L4.4 — Uniqueness of complete countably-generated A-module topology**.

If τ₁ and τ₂ are two uniform structures on M (both making M into a complete
countably-generated A-module), then they induce the SAME topology.

**Discharge route**: apply L4.2 (continuity of A-linear maps) to id_M in
both directions:
- id : (M, τ₁) → (M, τ₂) is A-linear (trivially) ⇒ continuous by L4.2 ⇒ τ₂ ≤ τ₁.
- id : (M, τ₂) → (M, τ₁) similarly ⇒ τ₁ ≤ τ₂.
- Hence τ₁ = τ₂.

**Difficulty**: EASY. ~25 lines. -/
theorem _sub_lemma_L4_4_unique_topology
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [SigmaCompactSpace A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (τ₁ τ₂ : UniformSpace M)
    (h_top1 : @IsUniformAddGroup M τ₁ _)
    (h_complete1 : @CompleteSpace M τ₁)
    (h_cg1 : (@uniformity M τ₁).IsCountablyGenerated)
    (h_t2_1 : @T2Space M τ₁.toTopologicalSpace)
    (h_csmul_1 : @ContinuousSMul A M _ _ τ₁.toTopologicalSpace)
    (h_top2 : @IsUniformAddGroup M τ₂ _)
    (h_complete2 : @CompleteSpace M τ₂)
    (h_cg2 : (@uniformity M τ₂).IsCountablyGenerated)
    (h_t2_2 : @T2Space M τ₂.toTopologicalSpace)
    (h_csmul_2 : @ContinuousSMul A M _ _ τ₂.toTopologicalSpace) :
    τ₁.toTopologicalSpace = τ₂.toTopologicalSpace := by
  -- Apply L4.2 twice with the identity map in each direction.
  have h12 : @Continuous M M τ₁.toTopologicalSpace τ₂.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _ _
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1 h_t2_1 h_csmul_1
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2 h_t2_2 h_csmul_2 (LinearMap.id (R := A) (M := M))
  have h21 : @Continuous M M τ₂.toTopologicalSpace τ₁.toTopologicalSpace id :=
    @_sub_lemma_L4_2_continuous_via_OMT _ _ _ _ _ _ _ _
      M _ _ _ τ₂ h_top2 h_complete2 h_cg2 h_t2_2 h_csmul_2
      M _ _ _ τ₁ h_top1 h_complete1 h_cg1 h_t2_1 h_csmul_1 (LinearMap.id (R := A) (M := M))
  exact le_antisymm (continuous_id_iff_le.mp h12) (continuous_id_iff_le.mp h21)

theorem wedhorn_6_18_unique
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (τ : UniformSpace M),
      @IsUniformAddGroup M τ _ ∧
      @CompleteSpace M τ ∧
      (uniformity M).IsCountablyGenerated ∧
      ∀ (τ' : UniformSpace M),
        @IsUniformAddGroup M τ' _ →
        @CompleteSpace M τ' →
        (@uniformity M τ').IsCountablyGenerated →
        τ.toTopologicalSpace = τ'.toTopologicalSpace :=
  sorry

/-- **Wedhorn 6.18(1) — EXISTENCE portion only (UAG + complete + cg)**.

Constructs a canonical uniform structure on `M` (the **quotient uniformity**
from a surjection `Aⁿ → M`) that is UAG + complete + countably-generated.
This is the existence half of `wedhorn_6_18_unique`; the uniqueness half is
genuinely false without additional `[T2Space]` + `[ContinuousSMul]` hypotheses
on the alternative uniform structure (counterexample: M = ℤ with discrete vs
indiscrete topology both UAG + complete + cg yet have different topologies),
so the existence is the meaningful unconditional content.

Construction: pick generators `s : Fin n → M`, form `ν : (Fin n → A) →+ M`
surjective, take the quotient `(Fin n → A) ⧸ ker ν`, equip with the
canonical `IsTopologicalAddGroup.rightUniformSpace`, transport back to `M`
via the `AddEquiv` `(Fin n → A) ⧸ ker ν ≃+ M`.

This is BGR §3.7.2/2 existence: every fg `A`-module admits a complete-cg
uniformity. -/
theorem wedhorn_6_18_exists_canonical_topology
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsNoetherianRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (τ : UniformSpace M),
      @IsUniformAddGroup M τ _ ∧
      @CompleteSpace M τ ∧
      (@uniformity M τ).IsCountablyGenerated := by
  classical
  obtain ⟨n, s, hs_span⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let ν : (Fin n → A) →+ M :=
    { toFun := fun a => ∑ i, a i • s i
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hν_surj : Function.Surjective ν := by
    intro m
    have hm : m ∈ Submodule.span A (Set.range s) := by
      rw [hs_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, ha⟩
  let eq : ((Fin n → A) ⧸ ν.ker) ≃+ M :=
    QuotientAddGroup.quotientKerEquivOfSurjective ν hν_surj
  haveI : FirstCountableTopology (Fin n → A) := UniformSpace.firstCountableTopology _
  haveI : FirstCountableTopology ((Fin n → A) ⧸ ν.ker) :=
    QuotientAddGroup.instFirstCountableTopology ν.ker
  letI τQ : UniformSpace ((Fin n → A) ⧸ ν.ker) :=
    IsTopologicalAddGroup.rightUniformSpace ((Fin n → A) ⧸ ν.ker)
  haveI : @IsUniformAddGroup _ τQ _ := isUniformAddGroup_of_addCommGroup
  haveI : @CompleteSpace _ τQ :=
    QuotientAddGroup.completeSpace_right (Fin n → A) ν.ker
  haveI : (@uniformity _ τQ).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  letI τM : UniformSpace M := UniformSpace.comap eq.symm τQ
  refine ⟨τM, ?_, ?_, ?_⟩
  · -- IsUniformAddGroup M via comap of UAG quotient through eq.symm AddMonoidHom.
    exact IsUniformAddGroup.comap eq.symm.toAddMonoidHom
  · -- CompleteSpace via completeSpace_congr applied to eq.symm as IsUniformEmbedding.
    have h_emb : @IsUniformEmbedding _ _ τM τQ eq.symm.toEquiv := by
      apply Equiv.isUniformEmbedding
      · exact uniformContinuous_comap
      · refine uniformContinuous_comap' ?_
        have h_id : (⇑eq.symm ∘ ⇑eq.symm.toEquiv.symm :
            ((Fin n → A) ⧸ ν.ker) → ((Fin n → A) ⧸ ν.ker)) = id := by
          ext x; simp
        rw [h_id]; exact uniformContinuous_id
    exact (completeSpace_congr h_emb).mpr (by infer_instance)
  · -- IsCountablyGenerated via Filter.comap.isCountablyGenerated.
    change (Filter.comap _ _).IsCountablyGenerated
    exact Filter.comap.isCountablyGenerated _ _

/-- **Wedhorn 6.18(2) — continuity part** = BGR §3.7.3/2. For a complete
noetherian Tate ring `A` and two finitely generated `A`-modules `M, N`
equipped with their (unique by 6.18(1)) complete countably-generated
topologies, every `A`-linear map `f : M → N` is continuous.

**Source** (Wedhorn 6.18(2), p. 50, first half):
> "Let `f : M → N` be an `A`-linear map of finitely generated modules that
> are endowed with the topology from (1). Then `f` is continuous..."

**Proof outline** (BGR 3.7.3/2):
* Choose epi `π : Aⁿ ↠ M`. The composite `f ∘ π : Aⁿ → N` is `A`-linear
  hence continuous (sum of coordinate projections, each multiplied by the
  image vectors `f(eᵢ)`).
* By Wedhorn 6.16, `π` is open (continuous surjective between complete
  metric A-modules). Hence `f = (f ∘ π) ∘ π⁻¹` is continuous (where `π⁻¹`
  uses the quotient topology). -/
theorem wedhorn_6_18_continuous
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [SigmaCompactSpace A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    Continuous f :=
  -- Direct citation of L4.2 (same statement).
  _sub_lemma_L4_2_continuous_via_OMT f

/-- **Wedhorn 6.18(2) — open onto image part** = BGR §3.7.3/Corollary 5.
For a complete noetherian Tate ring `A` and two finitely generated `A`-modules
`M, N` equipped with their topologies from 6.18(1), every `A`-linear
`f : M → N` is **strict** (= the image with subspace topology equals the
quotient topology), equivalently, `f : M → f(M)` is open.

**Source** (Wedhorn 6.18(2), p. 50, second half):
> "...and the map `f : M → f(M)` is open."

**Proof outline** (BGR 3.7.3/Cor 5 via Prop 4):
* `f` is continuous by `wedhorn_6_18_continuous`.
* Image `f(M)` is a finitely generated submodule of `N`, hence closed by
  Wedhorn 6.17.
* A continuous A-linear map between complete metric A-modules is strict iff
  its image is closed (BGR 3.7.3/Prop 4, via Banach OMT).
* Hence `f` is strict; equivalently, `f : M → f(M)` is open. -/
theorem wedhorn_6_18_open_onto_image
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated] [T2Space A]
      [IsTateRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [CompleteSpace M] [(uniformity M).IsCountablyGenerated] [T2Space M]
      [ContinuousSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
      [UniformSpace N] [IsUniformAddGroup N]
      [CompleteSpace N] [(uniformity N).IsCountablyGenerated] [T2Space N]
      [ContinuousSMul A N]
    (f : M →ₗ[A] N) :
    IsOpenMap (Set.rangeFactorization f) :=
  -- Direct citation of L4.3 (same statement).
  _sub_lemma_L4_3_strict_via_closed_image f

end ValuationSpectrum
