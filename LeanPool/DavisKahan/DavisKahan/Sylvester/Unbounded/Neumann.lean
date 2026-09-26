/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.Equation
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView

/-!
# Neumann-series Sylvester estimates with one unbounded block

The solution of a Sylvester equation with an invertible unbounded block is the
ideal-gauge limit of a Neumann iteration.  Each iterate lies in the ideal by the
two-sided composition law, the gauges decay geometrically, and completeness of
the gauge produces the limit; the operator-norm contraction identifies it with
the given solution.  Both orientations are proved: the unbounded block on the
left, and the unbounded block on the right.

The constant is one: the estimate is `δ * gauge X ≤ gauge C`, with no loss.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **A geometrically contracting iteration in an ideal has a gauge limit.**

If `T` preserves the ideal and shrinks its gauge by a factor `q < 1`, the partial
sums of the Neumann iterates `T^[k] t₀` are gauge-Cauchy, and completeness of the
gauge produces a limit that is still in the ideal and is also the operator-norm
limit.

**This was written twice**, once for each orientation of the Sylvester estimate
below — seventy-four lines each, differing only in the seed and the pair of
spaces.  `{lane:DK-LONGPROOF-5}`.  Nothing in it is about Sylvester equations;
the callers supply `hTmem` and `hTgauge` and that is the entire interface. -/
theorem exists_mem_and_tendsto_partialSum_of_gauge_geometric
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : Type v}
    [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [CompleteSpace B]
    (T : (A →L[𝕜] B) → (A →L[𝕜] B)) {t₀ : A →L[𝕜] B} (ht₀ : N.Mem t₀)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hTmem : ∀ Y : A →L[𝕜] B, N.Mem Y → N.Mem (T Y))
    (hTgauge : ∀ Y : A →L[𝕜] B, N.Mem Y → N.gaugeReal (T Y) ≤ q * N.gaugeReal Y) :
    ∃ L : A →L[𝕜] B, N.Mem L ∧
      Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, T^[k] t₀)
        Filter.atTop (nhds L) := by
  set t : ℕ → A →L[𝕜] B := fun n => T^[n] t₀ with htdef
  have ht0 : t 0 = t₀ := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := by
    intro n
    simp only [htdef, Function.iterate_succ_apply']
  have htmem : ∀ n, N.Mem (t n) := by
    intro n
    induction n with
    | zero => rw [ht0]; exact ht₀
    | succ n ih => rw [htsucc]; exact hTmem _ ih
  set g₀ : ℝ := N.gaugeReal t₀ with hg₀def
  have htgauge : ∀ n, N.gaugeReal (t n) ≤ q ^ n * g₀ := by
    intro n
    induction n with
    | zero => simp [htdef, hg₀def]
    | succ n ih =>
        rw [htsucc, pow_succ]
        calc N.gaugeReal (T (t n)) ≤ q * N.gaugeReal (t n) := hTgauge _ (htmem n)
          _ ≤ q * (q ^ n * g₀) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * g₀ := by ring
  set P : ℕ → A →L[𝕜] B := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    simp only [hPdef]
    exact N.finset_sum_mem (Finset.range n) t fun k _ => htmem k
  -- the real comparison sequence of geometric partial sums
  set G : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, q ^ k * g₀ with hGdef
  have hgap : ∀ {m n : ℕ}, n ≤ m → N.gaugeReal (P m - P n) ≤ G m - G n :=
    fun {_ _} hnm => N.gaugeReal_sum_range_sub_le htmem htgauge hnm
  have hGcauchy : CauchySeq G := by
    have hsummable : Summable fun k : ℕ => q ^ k * g₀ :=
      (summable_geometric_of_lt_one hq0 hq1).mul_right g₀
    exact hsummable.hasSum.tendsto_sum_nat.cauchySeq
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
      N.gaugeReal (P m - P n) < ε :=
    N.gaugeReal_sub_lt_of_cauchy_majorant hPmem hgap hGcauchy
  obtain ⟨L, hLmem, hLlim⟩ := N.gaugeReal_complete P hPmem hPcauchy
  -- the partial sums converge to `L` in operator norm
  have hPL : Filter.Tendsto P Filter.atTop (nhds L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => N.opNorm_le_gaugeReal (N.sub_mem (hPmem n) hLmem)) ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hLlim ε hε
    refine ⟨N₀, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (N.gaugeReal_nonneg (N.sub_mem (hPmem n) hLmem))]
    exact hN₀ n hn
  exact ⟨L, hLmem, by simpa only [hPdef, htdef] using hPL⟩

/-- One-unbounded version of the bound/inverse Sylvester estimate.

The solution is exhibited as the ideal-gauge limit of the Neumann iteration
`X = J C + J X B + J (J X B) B + ⋯` (with `J` the bounded inverse of the
unbounded block): each iterate lies in the ideal by the two-sided composition
law, the gauges decay geometrically because `‖J‖ ‖B‖ ≤ ρ / (ρ + δ) < 1`, the
`gauge_complete` field produces an ideal member as the gauge limit, and the
operator-norm contraction identifies that limit with `X`.  The gauge estimate
then follows from the fixed-point identity by absorption, exactly as in the
operator-norm shift-and-invert argument. -/
theorem Sylvester_mem_and_gauge_le_of_unbounded_bound_inverse
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →ₗ.[𝕜] E}
    (hAinv : TauCeti.LinearPMap.HasBoundedEverywhereInverse A)
    (B : F →L[𝕜] F) {X C : F →L[𝕜] E}
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hAinv.inv‖ ≤ (ρ + δ)⁻¹)
    (hB : ‖B‖ ≤ ρ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation
      A (B.toLinearMap.toPMap ⊤) X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  set J : E →L[𝕜] E := hAinv.inv with hJdef
  have hρδ : (0 : ℝ) < ρ + δ := by linarith
  set q : ℝ := ρ * (ρ + δ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hρ (inv_nonneg.mpr hρδ.le)
  have hq1 : q < 1 := by
    rw [hqdef, ← div_eq_mul_inv]
    exact (div_lt_one hρδ).mpr (by linarith)
  -- every value of `X` lies in the domain of `A`
  have hdom : ∀ x : F, X x ∈ A.domain := fun x =>
    hEq.mapsTo_domain ⟨x, Submodule.mem_top⟩
  -- the bounded fixed-point identity `X = J (C + X B)`
  have hfix : X = J ∘L (C + X ∘L B) := by
    ext x
    have heq : A ⟨X x, hdom x⟩ - X (B x) = C x :=
      hEq.equation ⟨x, Submodule.mem_top⟩
    have happ : A ⟨X x, hdom x⟩ = C x + X (B x) := by
      rw [← heq]; abel
    have hinv : J (A ⟨X x, hdom x⟩) = X x :=
      hAinv.inv_apply ⟨X x, hdom x⟩
    calc X x = J (A ⟨X x, hdom x⟩) := hinv.symm
      _ = J (C x + X (B x)) := by rw [happ]
      _ = (J ∘L (C + X ∘L B)) x := by
          simp [ContinuousLinearMap.comp_apply]
  -- the Neumann contraction `Y ↦ J Y B`
  set T : (F →L[𝕜] E) → (F →L[𝕜] E) := fun Y => J ∘L Y ∘L B with hTdef
  have hTadd : ∀ Y Z : F →L[𝕜] E, T (Y + Z) = T Y + T Z := by
    intro Y Z
    simp only [hTdef]
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hTnorm : ∀ Y : F →L[𝕜] E, ‖T Y‖ ≤ q * ‖Y‖ := by
    intro Y
    calc ‖T Y‖ ≤ ‖J‖ * ‖Y‖ * ‖B‖ :=
          TauCeti.ContinuousLinearMap.opNorm_comp_comp_le J Y B
      _ ≤ (ρ + δ)⁻¹ * ‖Y‖ * ρ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hInvNorm (norm_nonneg Y))
            hB (norm_nonneg B)
            (mul_nonneg (inv_nonneg.mpr hρδ.le) (norm_nonneg Y))
      _ = q * ‖Y‖ := by rw [hqdef]; ring
  have hTmem : ∀ Y : F →L[𝕜] E, N.Mem Y → N.Mem (T Y) := fun Y hY =>
    N.comp_mem J B hY
  have hTgauge : ∀ Y : F →L[𝕜] E, N.Mem Y →
      N.gaugeReal (T Y) ≤ q * N.gaugeReal Y := by
    intro Y hY
    calc N.gaugeReal (T Y) ≤ ‖J‖ * N.gaugeReal Y * ‖B‖ := N.gaugeReal_comp_le J B hY
      _ ≤ (ρ + δ)⁻¹ * N.gaugeReal Y * ρ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hInvNorm (N.gaugeReal_nonneg hY))
            hB (norm_nonneg B)
            (mul_nonneg (inv_nonneg.mpr hρδ.le) (N.gaugeReal_nonneg hY))
      _ = q * N.gaugeReal Y := by rw [hqdef]; ring
  -- the Neumann iterates and their partial sums
  set t : ℕ → F →L[𝕜] E := fun n => T^[n] (J ∘L C) with htdef
  have ht0 : t 0 = J ∘L C := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := fun n => by
    simp only [htdef, Function.iterate_succ_apply']
  set P : ℕ → F →L[𝕜] E := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  -- The gauge-Cauchy argument is shared with the other orientation and lives in
  -- `exists_mem_and_tendsto_partialSum_of_gauge_geometric`.
  obtain ⟨L, hLmem, hPL⟩ :=
    exists_mem_and_tendsto_partialSum_of_gauge_geometric N T
      (N.comp_left_mem J hC) hq0 hq1 hTmem hTgauge
  -- the partial sums converge to `X` in operator norm
  have hfix' : X = t 0 + T X := by
    conv_lhs => rw [hfix]
    rw [ht0, ContinuousLinearMap.comp_add]
  have hchain : ∀ n, T^[n] X = t n + T^[n + 1] X := by
    intro n
    induction n with
    | zero => simpa using hfix'
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTadd, ← htsucc,
          ← Function.iterate_succ_apply' T (n + 1) X]
  have hXP : ∀ n, X = P n + T^[n] X := by
    intro n
    induction n with
    | zero => simp [hPdef]
    | succ n ih =>
        have hPsucc : P (n + 1) = P n + t n := Finset.sum_range_succ _ _
        rw [hPsucc]
        calc X = P n + T^[n] X := ih
          _ = P n + (t n + T^[n + 1] X) := by rw [hchain n]
          _ = P n + t n + T^[n + 1] X := by abel
  have htail : ∀ n, ‖T^[n] X‖ ≤ q ^ n * ‖X‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc ‖T (T^[n] X)‖ ≤ q * ‖T^[n] X‖ := hTnorm _
          _ ≤ q * (q ^ n * ‖X‖) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * ‖X‖ := by ring
  have hPX : Filter.Tendsto P Filter.atTop (nhds X) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖P n - X‖ ≤ q ^ n * ‖X‖ := by
      intro n
      have hPnX : P n - X = -(T^[n] X) := by
        conv_lhs => rw [hXP n]
        abel
      rw [hPnX, norm_neg]
      exact htail n
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖X‖
  have hXL : X = L := tendsto_nhds_unique hPX hPL
  have hXmem : N.Mem X := by rw [hXL]; exact hLmem
  -- the gauge estimate by absorption through the fixed point
  have hXBmem : N.Mem (X ∘L B) := N.comp_right_mem B hXmem
  have hgauge : N.gaugeReal X ≤ (ρ + δ)⁻¹ * (N.gaugeReal C + N.gaugeReal X * ρ) :=
    N.gaugeReal_le_of_comp_add_comp_fixedPoint hρδ hInvNorm hB hC hXmem hXBmem hfix
  refine ⟨hXmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith

/-- Bundle-shaped compatibility entry point for the raw partial-map Neumann
estimate. -/
theorem sylvester_mem_and_gauge_le_of_unbounded_bound_inverse
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →ₗ.[𝕜] E}
    (hAinv : TauCeti.LinearPMap.HasBoundedEverywhereInverse A)
    (B : F →L[𝕜] F) {X C : F →L[𝕜] E}
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hAinv.inv‖ ≤ (ρ + δ)⁻¹)
    (hB : ‖B‖ ≤ ρ)
    (hEq : HasUnboundedBoundedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C :=
  Sylvester_mem_and_gauge_le_of_unbounded_bound_inverse N hAinv B
    hρ hδ hInvNorm hB hEq hC

omit [CompleteSpace E] [CompleteSpace F] in
/-- Transfer a partial-map Sylvester equation to a bounded realization of its
right block.  Agreement on the dense right domain extends through the closed
graph of the left partial map. -/
theorem SylvesterEquation_boundedRealization
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E} {T : F →L[𝕜] F}
    (hAclosed : A.IsClosed) (hBdense : Dense (B.domain : Set F))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hT : ∀ y : B.domain, T (y : F) = B y) :
    TauCeti.LinearPMap.UnboundedBoundedSylvesterEquation A T X C := by
  have hAclosedRange : IsClosed (Set.range fun z : A.domain => ((z : E), A z)) := by
    have hgraph : (A.graph : Set (E × E)) =
        Set.range (fun z : A.domain => ((z : E), A z)) := by
      ext p
      change p ∈ A.graph ↔ ∃ z : A.domain, ((z : E), A z) = p
      rw [LinearPMap.mem_graph_iff]
      constructor
      · rintro ⟨z, hz, hAz⟩
        exact ⟨z, Prod.ext hz hAz⟩
      · rintro ⟨z, hz⟩
        exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩
    rw [← hgraph]
    exact hAclosed
  have key : ∀ x : F, ∃ hx : X x ∈ A.domain,
      A ⟨X x, hx⟩ = C x + X (T x) := by
    intro x
    have hx_closure : x ∈ closure (B.domain : Set F) := by
      rw [hBdense.closure_eq]
      trivial
    obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hx_closure
    have hgraph_mem : ∀ n, (X (u n), C (u n) + X (T (u n))) ∈
        Set.range (fun z : A.domain => ((z : E), A z)) := by
      intro n
      refine ⟨⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩, Prod.ext rfl ?_⟩
      change A ⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩ =
        C (u n) + X (T (u n))
      have hval : A ⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩ =
          C (u n) + X (B ⟨u n, hu_mem n⟩) :=
        sub_eq_iff_eq_add.mp (hEq.equation ⟨u n, hu_mem n⟩)
      rw [hval, hT ⟨u n, hu_mem n⟩]
    have hconv : Filter.Tendsto (fun n => (X (u n), C (u n) + X (T (u n))))
        Filter.atTop (nhds (X x, C x + X (T x))) := by
      refine Filter.Tendsto.prodMk_nhds ?_ ?_
      · exact (X.continuous.tendsto x).comp hu_tendsto
      · refine Filter.Tendsto.add ?_ ?_
        · exact (C.continuous.tendsto x).comp hu_tendsto
        · exact ((X.comp T).continuous.tendsto x).comp hu_tendsto
    obtain ⟨z, hz⟩ := hAclosedRange.isSeqClosed hgraph_mem hconv
    have hz1 : (z : E) = X x := congrArg Prod.fst hz
    have hz2 : A z = C x + X (T x) := congrArg Prod.snd hz
    refine ⟨hz1 ▸ z.2, ?_⟩
    have hzz : z = ⟨X x, hz1 ▸ z.2⟩ := Subtype.ext hz1
    rw [← hzz]
    exact hz2
  refine ⟨fun x => (key (x : F)).choose, fun x => ?_⟩
  have h := (key (x : F)).choose_spec
  change A ⟨X (x : F), (key (x : F)).choose⟩ - X (T (x : F)) =
    C (x : F)
  rw [h]
  abel

/-- Historical closed-operator presentation of the raw right-unbounded
Neumann contraction. -/
theorem mem_and_gauge_le_of_boundedLeft_exteriorRight
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    {S : F →L[𝕜] F} {Λ : G →ₗ.[𝕜] G}
    {Y C : G →L[𝕜] F} {c ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hSnorm : ‖S‖ ≤ ρ)
    {J : G →L[𝕜] G} (hdom : ∀ z : G, J z ∈ Λ.domain)
    (hres : ∀ z : G,
      Λ ⟨J z, hdom z⟩ - ((c : ℝ) : 𝕜) • J z = z)
    (hJnorm : ‖J‖ ≤ (ρ + δ)⁻¹)
    (hEq : ∀ y : Λ.domain,
      S (Y (y : G)) -
        (Y (Λ y) - ((c : ℝ) : 𝕜) • Y (y : G)) = C (y : G))
    (hC : N.Mem C) :
    N.Mem Y ∧ δ * N.gaugeReal Y ≤ N.gaugeReal C := by
  have hρδ : (0 : ℝ) < ρ + δ := by linarith
  set q : ℝ := ρ * (ρ + δ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hρ (inv_nonneg.mpr hρδ.le)
  have hq1 : q < 1 := by
    rw [hqdef, ← div_eq_mul_inv]
    exact (div_lt_one hρδ).mpr (by linarith)
  -- the bounded fixed-point identity `Y = S Y J - C J`
  have hfix : Y = S ∘L Y ∘L J + -(C ∘L J) := by
    ext z
    have hres' : Λ ⟨J z, hdom z⟩ =
        z + ((c : ℝ) : 𝕜) • J z := sub_eq_iff_eq_add.mp (hres z)
    have h1 := hEq ⟨J z, hdom z⟩
    rw [hres', map_add, map_smul] at h1
    have h2 : S (Y (J z)) - Y z = C (J z) := by
      calc S (Y (J z)) - Y z
          = S (Y (J z)) -
              (Y z + ((c : ℝ) : 𝕜) • Y (J z) -
                ((c : ℝ) : 𝕜) • Y (J z)) := by abel
        _ = C (J z) := h1
    have h3 : S (Y (J z)) = C (J z) + Y z := sub_eq_iff_eq_add.mp h2
    change Y z = (S ∘L Y ∘L J) z + (-(C ∘L J)) z
    simp only [ContinuousLinearMap.comp_apply, neg_apply]
    rw [h3]
    abel
  -- the Neumann contraction `W ↦ S W J`
  set T : (G →L[𝕜] F) → (G →L[𝕜] F) := fun W => S ∘L W ∘L J with hTdef
  have hTadd : ∀ W Z : G →L[𝕜] F, T (W + Z) = T W + T Z := by
    intro W Z
    simp only [hTdef]
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hTnorm : ∀ W : G →L[𝕜] F, ‖T W‖ ≤ q * ‖W‖ := by
    intro W
    calc ‖T W‖ ≤ ‖S‖ * ‖W‖ * ‖J‖ :=
          TauCeti.ContinuousLinearMap.opNorm_comp_comp_le S W J
      _ ≤ ρ * ‖W‖ * (ρ + δ)⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg W))
            hJnorm (norm_nonneg J) (mul_nonneg hρ (norm_nonneg W))
      _ = q * ‖W‖ := by rw [hqdef]; ring
  have hTmem : ∀ W : G →L[𝕜] F, N.Mem W → N.Mem (T W) := fun W hW =>
    N.comp_mem S J hW
  have hTgauge : ∀ W : G →L[𝕜] F, N.Mem W →
      N.gaugeReal (T W) ≤ q * N.gaugeReal W := by
    intro W hW
    calc N.gaugeReal (T W) ≤ ‖S‖ * N.gaugeReal W * ‖J‖ := N.gaugeReal_comp_le S J hW
      _ ≤ ρ * N.gaugeReal W * (ρ + δ)⁻¹ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hSnorm (N.gaugeReal_nonneg hW))
            hJnorm (norm_nonneg J)
            (mul_nonneg hρ (N.gaugeReal_nonneg hW))
      _ = q * N.gaugeReal W := by rw [hqdef]; ring
  -- the Neumann iterates and their partial sums
  have hbasemem : N.Mem (-(C ∘L J)) := N.neg_mem (N.comp_right_mem J hC)
  set t : ℕ → G →L[𝕜] F := fun n => T^[n] (-(C ∘L J)) with htdef
  have ht0 : t 0 = -(C ∘L J) := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := fun n => by
    simp only [htdef, Function.iterate_succ_apply']
  set P : ℕ → G →L[𝕜] F := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  -- The gauge-Cauchy argument is shared with the other orientation and lives in
  -- `exists_mem_and_tendsto_partialSum_of_gauge_geometric`.
  obtain ⟨L, hLmem, hPL⟩ :=
    exists_mem_and_tendsto_partialSum_of_gauge_geometric N T
      (N.neg_mem (N.comp_right_mem J hC)) hq0 hq1 hTmem hTgauge
  -- the partial sums converge to `Y` in operator norm
  have hfix' : Y = t 0 + T Y := by
    conv_lhs => rw [hfix]
    rw [ht0]
    abel
  have hchain : ∀ n, T^[n] Y = t n + T^[n + 1] Y := by
    intro n
    induction n with
    | zero => simpa using hfix'
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTadd, ← htsucc,
          ← Function.iterate_succ_apply' T (n + 1) Y]
  have hYP : ∀ n, Y = P n + T^[n] Y := by
    intro n
    induction n with
    | zero => simp [hPdef]
    | succ n ih =>
        have hPsucc : P (n + 1) = P n + t n := Finset.sum_range_succ _ _
        rw [hPsucc]
        calc Y = P n + T^[n] Y := ih
          _ = P n + (t n + T^[n + 1] Y) := by rw [hchain n]
          _ = P n + t n + T^[n + 1] Y := by abel
  have htail : ∀ n, ‖T^[n] Y‖ ≤ q ^ n * ‖Y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc ‖T (T^[n] Y)‖ ≤ q * ‖T^[n] Y‖ := hTnorm _
          _ ≤ q * (q ^ n * ‖Y‖) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * ‖Y‖ := by ring
  have hPY : Filter.Tendsto P Filter.atTop (nhds Y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖P n - Y‖ ≤ q ^ n * ‖Y‖ := by
      intro n
      have hPnY : P n - Y = -(T^[n] Y) := by
        conv_lhs => rw [hYP n]
        abel
      rw [hPnY, norm_neg]
      exact htail n
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖Y‖
  have hYL : Y = L := tendsto_nhds_unique hPY hPL
  have hYmem : N.Mem Y := by rw [hYL]; exact hLmem
  -- the gauge estimate by absorption through the fixed point
  have hgauge : N.gaugeReal Y ≤ (ρ + δ)⁻¹ * (ρ * N.gaugeReal Y + N.gaugeReal C) := by
    conv_lhs => rw [hfix]
    calc N.gaugeReal (S ∘L Y ∘L J + -(C ∘L J))
        ≤ N.gaugeReal (S ∘L Y ∘L J) + N.gaugeReal (-(C ∘L J)) :=
          N.gaugeReal_add_le (N.comp_mem S J hYmem) hbasemem
      _ ≤ ‖S‖ * N.gaugeReal Y * ‖J‖ + N.gaugeReal (C ∘L J) :=
          add_le_add (N.gaugeReal_comp_le S J hYmem)
            (le_of_eq (N.gaugeReal_neg (N.comp_right_mem J hC)))
      _ ≤ ρ * N.gaugeReal Y * (ρ + δ)⁻¹ + N.gaugeReal C * (ρ + δ)⁻¹ := by
          refine add_le_add
            (mul_le_mul
              (mul_le_mul_of_nonneg_right hSnorm (N.gaugeReal_nonneg hYmem))
              hJnorm (norm_nonneg J)
              (mul_nonneg hρ (N.gaugeReal_nonneg hYmem))) ?_
          exact (N.gaugeReal_comp_right_le_mul J hC).trans
            (mul_le_mul_of_nonneg_left hJnorm (N.gaugeReal_nonneg hC))
      _ = (ρ + δ)⁻¹ * (ρ * N.gaugeReal Y + N.gaugeReal C) := by ring
  refine ⟨hYmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith
end Sylvester
end DavisKahan
end TauCeti
