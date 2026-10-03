/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedReduction
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.GraphCore
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# The complementary graph of a reducing Riccati selection

`ContractiveReducingGraphSelection.reduces` asserts that the angular graph
*reduces* the block core, which is strictly more than invariance: the orthogonal
complement is invariant too.  That second half has not been exploited anywhere,
and it is what supplies the adjoint-side domain compatibility

```
z ∈ dom A₁  →  X* z ∈ dom A₀
```

together with the adjoint Riccati equation.  Both are needed by the sharp
unbounded `tan 2Theta` argument, where the commutator `A₀X*X - X*XA₀` must be
shown bounded; the sharp tan(2Theta) note in Git history (ticket T1.1).

The file mirrors `UnboundedReduction`: first a coordinate characterization of
membership in the complement, then the domain-vector constructor, then the
equation itself.

The key geometric fact is that the orthogonal complement of the graph of `X` is
the graph of `-X*` **taken in the other order**:

```
(u, v) ⟂ {(w, X w)}  ↔  ∀ w, ⟪u, w⟫ + ⟪v, X w⟫ = 0  ↔  u = -X* v
```
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Coordinate characterization of membership in the orthogonal complement of an
unbounded block graph: the complement of the graph of `X` is the graph of `-X†`
read in the opposite coordinate order. -/
theorem mem_unboundedBlockGraph_orthogonal_iff
    (X : E0 →L[𝕜] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedBlockGraph X)ᗮ ↔
      WithLp.fst z = -(ContinuousLinearMap.adjoint X) (WithLp.snd z) := by
  set u : E0 := WithLp.fst z with hu
  set v : E1 := WithLp.snd z with hv
  constructor
  · intro hz
    -- Testing against the graph vector of `w` gives `⟪w, u + X† v⟫ = 0`.
    have hall : ∀ w : E0, ⟪w, u + (ContinuousLinearMap.adjoint X) v⟫_𝕜 = 0 := by
      intro w
      have hmem : WithLp.toLp 2 (w, X w) ∈ unboundedBlockGraph X :=
        (toLp_mem_unboundedBlockGraph_iff X w (X w)).2 rfl
      have h0 := hz _ hmem
      rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right]
      simpa [hu, hv] using h0
    have hzero : u + (ContinuousLinearMap.adjoint X) v = 0 :=
      inner_self_eq_zero.1 (hall _)
    linear_combination (norm := module) hzero
  · intro hzu y hy
    rw [mem_unboundedBlockGraph_iff] at hy
    have hexp : ⟪y, z⟫_𝕜 = ⟪WithLp.fst y, u⟫_𝕜 + ⟪WithLp.snd y, v⟫_𝕜 := by
      simp [hu, hv]
    rw [hexp, hy, hzu, inner_neg_right,
      ContinuousLinearMap.adjoint_inner_right, neg_add_cancel]

/-- The angular operator maps the second diagonal domain into the first.

This is the adjoint-side counterpart of `PreservesRiccatiDomains`, and it has
exactly the same status: a genuine hypothesis, not a consequence of reduction.
`ContractiveReducingGraphSelection` already records the forward version as a
separate field for this reason ("domain preservation is a separate field
because it is not a consequence of the ambient graph equality alone"), and the
adjoint side is no better.

Concretely, reduction *does* give something, just not enough. Writing
`R₀ := (I + X†X)⁻¹`, the projection-preserves-domain half of `ReducesSubspace`
applied to `(u, 0)` and to `(0, z)` yields

```
R₀ preserves dom A₀,      and      R₀ X† z ∈ dom A₀  for z ∈ dom A₁.
```

Recovering `X† z = (I + X†X)(R₀ X† z)` from the second then needs `X†X` to
preserve `dom A₀` — which is `gram_mem_domain`, itself a consequence of the
very statement being derived. The loop does not close, and the symmetric
attempt through `R₁ := (I + XX†)⁻¹` fails the same way: `R₁` preserves
`dom A₁`, but showing it *surjects* onto `dom A₁` again needs `X† z ∈ dom A₀`.

So this is carried as an explicit hypothesis throughout. It is not a hidden
seam: it is the adjoint twin of a hypothesis the repository already assumes. -/
def PreservesAdjointRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ z : H.A1.domain, (ContinuousLinearMap.adjoint X) (z : E1) ∈ H.A0.domain

/-- The complementary-graph vector attached to a vector of the second diagonal
domain, carrying its membership witness in the full block-operator domain. -/
noncomputable def unboundedBlockGraphOrthogonalDomainVector
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (z : H.A1.domain) : (unboundedBlockOperatorCore H).domain :=
  ⟨WithLp.toLp 2 (-(ContinuousLinearMap.adjoint X) (z : E1), (z : E1)), by
    rw [unboundedBlockOperatorCore_domain]
    exact ⟨Submodule.neg_mem _ (hadj z), z.property⟩⟩

/-- Every complementary-graph vector lies in the orthogonal complement of the
angular graph. -/
theorem unboundedBlockGraphOrthogonalDomainVector_mem
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (z : H.A1.domain) :
    ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) : WithLp 2 (E0 × E1)) ∈
      (unboundedBlockGraph X)ᗮ := by
  rw [mem_unboundedBlockGraph_orthogonal_iff]
  rfl

/-- **The adjoint Riccati equation.**

Invariance of the *orthogonal complement* of the angular graph — the half of
`ReducesSubspace` that plain invariance does not give — is exactly the statement
that `X†` intertwines the two diagonal blocks up to the off-diagonal coupling.

Together with `strongSolvesRiccati_iff_pointwise` this is what makes the
commutator `A₀X†X - X†XA₀` bounded, which is the analytic engine of the sharp
unbounded `tan 2Theta` estimate. -/
theorem adjoint_riccati_of_invariant_orthogonal
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (z : H.A1.domain) :
    H.A0 ⟨(ContinuousLinearMap.adjoint X) (z : E1), hadj z⟩ =
      H.B01 (z : E1) + (ContinuousLinearMap.adjoint X) (H.A1 z) -
        (ContinuousLinearMap.adjoint X)
          (H.B10 ((ContinuousLinearMap.adjoint X) (z : E1))) := by
  have hout := hinv (unboundedBlockGraphOrthogonalDomainVector H X hadj z)
    (unboundedBlockGraphOrthogonalDomainVector_mem H X hadj z)
  rw [mem_unboundedBlockGraph_orthogonal_iff,
    unboundedBlockOperatorCore_apply_fst,
    unboundedBlockOperatorCore_apply_snd] at hout
  -- `hout` says `A₀(-X†z) + B₀₁z = -X†(A₁z + B₁₀(-X†z))`.
  have hfst : TauCeti.LinearPMap.directSumDomainFst H.A0 H.A1
      (unboundedBlockGraphOrthogonalDomainVector H X hadj z) =
      ⟨-(ContinuousLinearMap.adjoint X) (z : E1),
        Submodule.neg_mem _ (hadj z)⟩ := rfl
  have hsnd : TauCeti.LinearPMap.directSumDomainSnd H.A0 H.A1
      (unboundedBlockGraphOrthogonalDomainVector H X hadj z) = z := rfl
  rw [hfst, hsnd] at hout
  have hneg : (⟨-(ContinuousLinearMap.adjoint X) (z : E1),
        Submodule.neg_mem _ (hadj z)⟩ : H.A0.domain) =
      -(⟨(ContinuousLinearMap.adjoint X) (z : E1), hadj z⟩ : H.A0.domain) := rfl
  rw [hneg, LinearPMap.map_neg] at hout
  have hfstcoe :
      ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) :
          WithLp 2 (E0 × E1)).fst =
      -(ContinuousLinearMap.adjoint X) (z : E1) := rfl
  have hsndcoe :
      ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) :
          WithLp 2 (E0 × E1)).snd = (z : E1) := rfl
  rw [hfstcoe, hsndcoe, map_add, map_neg, map_neg] at hout
  linear_combination (norm := module) -hout

/-- The commutator of the first diagonal block with the Gram operator `X†X`.

Both Riccati equations conspire so that this commutator, which a priori pairs an
unbounded operator with a bounded one, is itself **bounded**: writing `K = B₀₁X`
and `T = X†X` it is `(I + T)K - K†(I + T)`, so `‖G‖ ≤ 2(‖B₀₁‖ + ‖B₁₀‖)`. -/
noncomputable def riccatiGramCommutator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  H.B01 ∘L X + ((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X) -
    ((ContinuousLinearMap.adjoint X) ∘L H.B10) -
      ((ContinuousLinearMap.adjoint X) ∘L H.B10) ∘L
        ((ContinuousLinearMap.adjoint X) ∘L X)

/-- The Gram operator of a reducing Riccati selection preserves the first
diagonal domain. -/
theorem gram_mem_domain
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
    (hadj : PreservesAdjointRiccatiDomains H X) (x : H.A0.domain) :
    (ContinuousLinearMap.adjoint X) (X (x : E0)) ∈ H.A0.domain :=
  hadj ⟨X (x : E0), hdom x⟩

/-- **The Riccati commutator identity.**

`A₀` commutes with the Gram operator `X†X` up to the *bounded* operator
`riccatiGramCommutator`.  This is ticket T1.2 of the sharp unbounded
`tan 2Theta` lane: it is the reason the whole argument can be run with band
projections of `X†X` while keeping the unbounded block under control. -/
theorem gram_commutator_eq
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
    (hadj : PreservesAdjointRiccatiDomains H X)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (x : H.A0.domain) :
    H.A0 ⟨(ContinuousLinearMap.adjoint X) (X (x : E0)),
        gram_mem_domain H hdom hadj x⟩ =
      (ContinuousLinearMap.adjoint X) (X (H.A0 x)) +
        riccatiGramCommutator H X (x : E0) := by
  have hz := adjoint_riccati_of_invariant_orthogonal H X hadj hinv
    ⟨X (x : E0), hdom x⟩
  have hA1 : H.A1 ⟨X (x : E0), hdom x⟩ =
      X (H.A0 x + H.B01 (X (x : E0))) - H.B10 (x : E0) := by
    rw [← hric x]; abel
  rw [hA1, map_sub, map_add] at hz
  simp only [riccatiGramCommutator, add_apply, sub_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hz]
  simp only [map_add]
  abel

/-- Closedness of a self-adjoint diagonal block in sequential form.

Thin specialisation of `LinearPMap.IsClosed.mem_domain_of_tendsto`
(`ForTauCeti/…/LinearPMap/GraphCore.lean`) to the first diagonal block, whose
closedness comes from self-adjointness.  It is what turns the polynomial
commutator bounds into statements about entire functions of the Gram operator:
the partial sums of a power series lie in `dom A₀` and their `A₀`-images
converge, so the limit is in `dom A₀` too. -/
theorem mem_domain_of_tendsto
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {y : ℕ → E0} {yl w : E0} (hy : ∀ n, y n ∈ H.A0.domain)
    (hlim : Filter.Tendsto y Filter.atTop (nhds yl))
    (hAlim : Filter.Tendsto (fun n => H.A0 ⟨y n, hy n⟩) Filter.atTop (nhds w)) :
    ∃ h : yl ∈ H.A0.domain, H.A0 ⟨yl, h⟩ = w :=
  (IsSelfAdjoint.isClosed H.selfAdjoint0).mem_domain_of_tendsto hy hlim hAlim

/-- The Gram operator `X†X` of a reducing Riccati selection, bundled. -/
noncomputable def riccatiGram (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  (ContinuousLinearMap.adjoint X) ∘L X

section Powers

variable (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
variable {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
variable (hadj : PreservesAdjointRiccatiDomains H X)

include hdom hadj in
/-- Every power of the Gram operator preserves the first diagonal domain. -/
theorem riccatiGram_pow_mem_domain (n : ℕ) (x : H.A0.domain) :
    ((riccatiGram X) ^ n) (x : E0) ∈ H.A0.domain := by
  induction n with
  | zero => simp [x.property]
  | succ n ih =>
      have hstep : ((riccatiGram X) ^ (n + 1)) (x : E0) =
          riccatiGram X (((riccatiGram X) ^ n) (x : E0)) := by
        rw [pow_succ']
        rfl
      rw [hstep]
      exact gram_mem_domain H hdom hadj ⟨_, ih⟩

/-- A contractive Gram operator stays contractive on every power. -/
theorem norm_riccatiGram_pow_apply_le
    {Y : E0 →L[𝕜] E1} (hY : ‖riccatiGram Y‖ ≤ 1) (n : ℕ) (y : E0) :
    ‖((riccatiGram Y) ^ n) y‖ ≤ ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ((riccatiGram Y) ^ (n + 1)) y =
          riccatiGram Y (((riccatiGram Y) ^ n) y) := by
        rw [pow_succ']; rfl
      rw [hstep]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖riccatiGram Y‖ * ‖((riccatiGram Y) ^ n) y‖
          ≤ 1 * ‖((riccatiGram Y) ^ n) y‖ :=
            mul_le_mul_of_nonneg_right hY (norm_nonneg _)
        _ ≤ ‖y‖ := by simpa using ih

include hdom hadj in
/-- **Iterated Riccati commutator bound.**

`A₀` commutes with the `n`-th power of a contractive Gram operator up to an
error of size `n‖G‖`.  Summing this against the exponential series is what shows
that smooth functions of `X†X` preserve `dom A₀` with a uniformly bounded
commutator (ticket T1.3), which is what licenses the band construction: the
factor `n` is exactly what the `1/n!` of the exponential absorbs. -/
theorem norm_riccatiGram_pow_commutator_le
    (hcontr : ‖riccatiGram X‖ ≤ 1)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (n : ℕ) (x : H.A0.domain) :
    ‖H.A0 ⟨((riccatiGram X) ^ n) (x : E0),
          riccatiGram_pow_mem_domain H hdom hadj n x⟩ -
        ((riccatiGram X) ^ n) (H.A0 x)‖ ≤
      n * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  induction n with
  | zero =>
      have h0 : (⟨((riccatiGram X) ^ 0) (x : E0),
          riccatiGram_pow_mem_domain H hdom hadj 0 x⟩ : H.A0.domain) = x := by
        apply Subtype.ext; simp
      rw [h0]
      simp
  | succ n ih =>
      have hmem := riccatiGram_pow_mem_domain H hdom hadj n x
      have hstep : ((riccatiGram X) ^ (n + 1)) (x : E0) =
          riccatiGram X (((riccatiGram X) ^ n) (x : E0)) := by
        rw [pow_succ']; rfl
      have hsub : (⟨((riccatiGram X) ^ (n + 1)) (x : E0),
            riccatiGram_pow_mem_domain H hdom hadj (n + 1) x⟩ : H.A0.domain) =
          ⟨(ContinuousLinearMap.adjoint X) (X (((riccatiGram X) ^ n) (x : E0))),
            gram_mem_domain H hdom hadj ⟨_, hmem⟩⟩ := by
        apply Subtype.ext; exact hstep
      rw [hsub, gram_commutator_eq H hdom hadj hinv hric ⟨_, hmem⟩]
      have hexp : ((riccatiGram X) ^ (n + 1)) (H.A0 x) =
          riccatiGram X (((riccatiGram X) ^ n) (H.A0 x)) := by
        rw [pow_succ']; rfl
      rw [hexp]
      have hrw :
          (ContinuousLinearMap.adjoint X) (X (H.A0 ⟨_, hmem⟩)) +
              riccatiGramCommutator H X (((riccatiGram X) ^ n) (x : E0)) -
            riccatiGram X (((riccatiGram X) ^ n) (H.A0 x)) =
          riccatiGram X (H.A0 ⟨_, hmem⟩ - ((riccatiGram X) ^ n) (H.A0 x)) +
            riccatiGramCommutator H X (((riccatiGram X) ^ n) (x : E0)) := by
        simp only [riccatiGram, map_sub, ContinuousLinearMap.coe_comp,
          Function.comp_apply]
        abel
      rw [hrw]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖riccatiGram X (H.A0 ⟨_, hmem⟩ -
            ((riccatiGram X) ^ n) (H.A0 x))‖ ≤
          n * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        calc ‖riccatiGram X‖ * ‖H.A0 ⟨_, hmem⟩ -
              ((riccatiGram X) ^ n) (H.A0 x)‖
            ≤ 1 * ‖H.A0 ⟨_, hmem⟩ - ((riccatiGram X) ^ n) (H.A0 x)‖ :=
              mul_le_mul_of_nonneg_right hcontr (norm_nonneg _)
          _ ≤ n * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
              simpa using ih
      have h2 : ‖riccatiGramCommutator H X (((riccatiGram X) ^ n) (x : E0))‖ ≤
          ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul_of_nonneg_left
          (norm_riccatiGram_pow_apply_le hcontr n (x : E0)) (norm_nonneg _)
      have hcast : ((n + 1 : ℕ) : ℝ) * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ =
          (n : ℝ) * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ +
            ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
        push_cast; ring
      rw [hcast]
      linarith [h1, h2]

/-- Powers of the Gram operator obey the submultiplicative bound. -/
theorem norm_riccatiGram_pow_apply_le' {Y : E0 →L[𝕜] E1} (n : ℕ) (y : E0) :
    ‖((riccatiGram Y) ^ n) y‖ ≤ ‖riccatiGram Y‖ ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ((riccatiGram Y) ^ (n + 1)) y =
          riccatiGram Y (((riccatiGram Y) ^ n) y) := by
        rw [pow_succ']; rfl
      rw [hstep]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖riccatiGram Y‖ * ‖((riccatiGram Y) ^ n) y‖
          ≤ ‖riccatiGram Y‖ * (‖riccatiGram Y‖ ^ n * ‖y‖) :=
            mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        _ = ‖riccatiGram Y‖ ^ (n + 1) * ‖y‖ := by ring

include hdom hadj in
/-- **Geometric form of the iterated Riccati commutator bound.**

Keeps the `‖T‖ⁿ` decay that `norm_riccatiGram_pow_commutator_le` discards under
its contractivity hypothesis.  The decay is what makes the bound summable
against a *geometric* series, so this — not the contractive form — is what
reaches the Riccati resolvent `(1 - X†X)⁻¹`, where the coefficients are all `1`
and `Σ n` diverges. Indexed at `n + 1` to avoid natural subtraction. -/
theorem norm_riccatiGram_pow_succ_commutator_le
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (n : ℕ) (x : H.A0.domain) :
    ‖H.A0 ⟨((riccatiGram X) ^ (n + 1)) (x : E0),
          riccatiGram_pow_mem_domain H hdom hadj (n + 1) x⟩ -
        ((riccatiGram X) ^ (n + 1)) (H.A0 x)‖ ≤
      (n + 1) * ‖riccatiGram X‖ ^ n *
        ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  induction n with
  | zero =>
      have hone : ((riccatiGram X) ^ (0 + 1)) (x : E0) =
          (ContinuousLinearMap.adjoint X) (X (x : E0)) := by
        simp [riccatiGram]
      have hsub : (⟨((riccatiGram X) ^ (0 + 1)) (x : E0),
            riccatiGram_pow_mem_domain H hdom hadj (0 + 1) x⟩ :
              H.A0.domain) =
          ⟨(ContinuousLinearMap.adjoint X) (X (x : E0)),
            gram_mem_domain H hdom hadj x⟩ := by
        apply Subtype.ext; exact hone
      rw [hsub, gram_commutator_eq H hdom hadj hinv hric x]
      have hexp : ((riccatiGram X) ^ (0 + 1)) (H.A0 x) =
          (ContinuousLinearMap.adjoint X) (X (H.A0 x)) := by
        simp [riccatiGram]
      rw [hexp]
      have : (ContinuousLinearMap.adjoint X) (X (H.A0 x)) +
          riccatiGramCommutator H X (x : E0) -
          (ContinuousLinearMap.adjoint X) (X (H.A0 x)) =
          riccatiGramCommutator H X (x : E0) := by abel
      rw [this]
      simpa using ContinuousLinearMap.le_opNorm (riccatiGramCommutator H X)
        (x : E0)
  | succ n ih =>
      have hmem := riccatiGram_pow_mem_domain H hdom hadj (n + 1) x
      have hstep : ((riccatiGram X) ^ (n + 2)) (x : E0) =
          riccatiGram X (((riccatiGram X) ^ (n + 1)) (x : E0)) := by
        rw [pow_succ']; rfl
      have hsub : (⟨((riccatiGram X) ^ (n + 2)) (x : E0),
            riccatiGram_pow_mem_domain H hdom hadj (n + 2) x⟩ :
              H.A0.domain) =
          ⟨(ContinuousLinearMap.adjoint X)
              (X (((riccatiGram X) ^ (n + 1)) (x : E0))),
            gram_mem_domain H hdom hadj ⟨_, hmem⟩⟩ := by
        apply Subtype.ext; exact hstep
      rw [hsub, gram_commutator_eq H hdom hadj hinv hric ⟨_, hmem⟩]
      have hexp : ((riccatiGram X) ^ (n + 2)) (H.A0 x) =
          riccatiGram X (((riccatiGram X) ^ (n + 1)) (H.A0 x)) := by
        rw [pow_succ']; rfl
      rw [hexp]
      have hrw :
          (ContinuousLinearMap.adjoint X) (X (H.A0 ⟨_, hmem⟩)) +
              riccatiGramCommutator H X
                (((riccatiGram X) ^ (n + 1)) (x : E0)) -
            riccatiGram X (((riccatiGram X) ^ (n + 1)) (H.A0 x)) =
          riccatiGram X (H.A0 ⟨_, hmem⟩ -
              ((riccatiGram X) ^ (n + 1)) (H.A0 x)) +
            riccatiGramCommutator H X
              (((riccatiGram X) ^ (n + 1)) (x : E0)) := by
        simp only [riccatiGram, map_sub, ContinuousLinearMap.coe_comp,
          Function.comp_apply]
        abel
      rw [hrw]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖riccatiGram X (H.A0 ⟨_, hmem⟩ -
            ((riccatiGram X) ^ (n + 1)) (H.A0 x))‖ ≤
          ‖riccatiGram X‖ * ((n + 1) * ‖riccatiGram X‖ ^ n *
            ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
      have h2 : ‖riccatiGramCommutator H X
            (((riccatiGram X) ^ (n + 1)) (x : E0))‖ ≤
          ‖riccatiGramCommutator H X‖ *
            (‖riccatiGram X‖ ^ (n + 1) * ‖(x : E0)‖) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left
            (norm_riccatiGram_pow_apply_le' (n + 1) (x : E0)) (norm_nonneg _))
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) * ‖riccatiGram X‖ ^ (n + 1) *
            ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ =
          ‖riccatiGram X‖ * (((n : ℝ) + 1) * ‖riccatiGram X‖ ^ n *
            ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖) +
            ‖riccatiGramCommutator H X‖ *
              (‖riccatiGram X‖ ^ (n + 1) * ‖(x : E0)‖) := by
        push_cast; ring
      rw [hcast]
      linarith [h1, h2]

include hdom hadj in
/-- The geometric commutator bound with the degree written directly.

`n * ‖T‖^(n-1)` uses natural subtraction, which is exactly right here: at
`n = 0` it reads `0 * ‖T‖^0 = 0`, matching the vanishing commutator, and at
`n ≥ 1` it is the intended `n‖T‖ⁿ⁻¹`.  This is the summand form, so it is what
gets summed over a `Finset` and then over `ℕ`. -/
theorem norm_riccatiGram_pow_commutator_le_geom
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (n : ℕ) (x : H.A0.domain) :
    ‖H.A0 ⟨((riccatiGram X) ^ n) (x : E0),
          riccatiGram_pow_mem_domain H hdom hadj n x⟩ -
        ((riccatiGram X) ^ n) (H.A0 x)‖ ≤
      (n * ‖riccatiGram X‖ ^ (n - 1)) *
        ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  cases n with
  | zero =>
      have h0 : (⟨((riccatiGram X) ^ 0) (x : E0),
          riccatiGram_pow_mem_domain H hdom hadj 0 x⟩ : H.A0.domain) = x := by
        apply Subtype.ext; simp
      rw [h0]
      simp
  | succ n =>
      have h := norm_riccatiGram_pow_succ_commutator_le H hdom hadj hinv hric n x
      simpa using h

end Powers

section Powers'

variable (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
variable {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
variable (hadj : PreservesAdjointRiccatiDomains H X)

include hdom hadj in
/-- A polynomial in the Gram operator, indexed by an arbitrary finite set of
degrees, preserves the first diagonal domain. -/
theorem riccatiGram_finsetPoly_mem_domain (a : ℕ → 𝕜) (s : Finset ℕ)
    (x : H.A0.domain) :
    (∑ n ∈ s, a n • ((riccatiGram X) ^ n)) (x : E0) ∈ H.A0.domain := by
  simp only [FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply]
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.smul_mem _ _ (riccatiGram_pow_mem_domain H hdom hadj n x)

include hdom hadj in
/-- **Riccati commutator bound over an arbitrary finite degree set.**

Stated over a general `Finset` rather than `Finset.range N` so that the
difference of two partial sums of a power series is itself covered: that is
exactly what makes the `A₀`-images of the partial sums Cauchy, which is how
entire functions of the Gram operator are reached. -/
theorem norm_riccatiGram_finsetPoly_commutator_le
    (μ : ℕ → ℝ) (_hμ0 : ∀ n, 0 ≤ μ n)
    (hμ : ∀ (n : ℕ) (y : H.A0.domain),
      ‖H.A0 ⟨((riccatiGram X) ^ n) (y : E0),
            riccatiGram_pow_mem_domain H hdom hadj n y⟩ -
          ((riccatiGram X) ^ n) (H.A0 y)‖ ≤
        μ n * ‖riccatiGramCommutator H X‖ * ‖(y : E0)‖)
    (a : ℕ → 𝕜) (s : Finset ℕ) (x : H.A0.domain) :
    ‖H.A0 ⟨(∑ n ∈ s, a n • ((riccatiGram X) ^ n)) (x : E0),
          riccatiGram_finsetPoly_mem_domain H hdom hadj a s x⟩ -
        (∑ n ∈ s, a n • ((riccatiGram X) ^ n)) (H.A0 x)‖ ≤
      (∑ n ∈ s, ‖a n‖ * μ n) *
        ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (⟨(∑ n ∈ (∅ : Finset ℕ), a n • ((riccatiGram X) ^ n)) (x : E0),
          riccatiGram_finsetPoly_mem_domain H hdom hadj a ∅ x⟩ :
            H.A0.domain) = 0 := by
        apply Subtype.ext; simp
      rw [h0]
      simp
  | insert m s hms ih =>
      have hmemS := riccatiGram_finsetPoly_mem_domain H hdom hadj a s x
      have hmemP := riccatiGram_pow_mem_domain H hdom hadj m x
      have hsplit : (⟨(∑ n ∈ insert m s,
              a n • ((riccatiGram X) ^ n)) (x : E0),
            riccatiGram_finsetPoly_mem_domain H hdom hadj a (insert m s) x⟩ :
              H.A0.domain) =
          a m • (⟨((riccatiGram X) ^ m) (x : E0), hmemP⟩ : H.A0.domain) +
            (⟨(∑ n ∈ s, a n • ((riccatiGram X) ^ n)) (x : E0), hmemS⟩ :
              H.A0.domain) := by
        apply Subtype.ext
        simp [Finset.sum_insert hms]
      rw [hsplit, LinearPMap.map_add, LinearPMap.map_smul]
      have hexp : (∑ n ∈ insert m s,
            a n • ((riccatiGram X) ^ n)) (H.A0 x) =
          a m • (((riccatiGram X) ^ m) (H.A0 x)) +
            (∑ n ∈ s, a n • ((riccatiGram X) ^ n)) (H.A0 x) := by
        simp [Finset.sum_insert hms]
      rw [hexp]
      have hrw : ∀ p q r t : E0, a m • p + q - (a m • r + t) =
          a m • (p - r) + (q - t) := by
        intro p q r t
        rw [smul_sub]
        abel
      rw [hrw]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖a m • (H.A0 ⟨((riccatiGram X) ^ m) (x : E0), hmemP⟩ -
            ((riccatiGram X) ^ m) (H.A0 x))‖ ≤
          ‖a m‖ * (μ m * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖) := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (hμ m x)
          (norm_nonneg _)
      have hcast : (∑ n ∈ insert m s, ‖a n‖ * μ n) *
            ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ =
          ‖a m‖ * (μ m * ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖) +
            (∑ n ∈ s, ‖a n‖ * μ n) *
              ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
        rw [Finset.sum_insert hms]
        ring
      rw [hcast]
      linarith [ih, h1]

include hdom hadj in
/-- **Entire functions of the Gram operator preserve `dom A₀`.**

This completes ticket T1.3.  If `Σ aₙ Tⁿ` converges to `Φ` in operator norm and
`Σ n‖aₙ‖` converges, then `Φ` maps `dom A₀` into itself and the commutator is
bounded by `(Σ n‖aₙ‖)·‖G‖` — a quantity involving only the off-diagonal
coupling.

The intended instance is a Gaussian bump `exp(-(t-λ)²/β²)` in `T = X†X`, whose
coefficients decay super-geometrically, giving a smooth spectral band of `X†X`
that is compatible with the unbounded block.  Sharp band projections cannot be
used in its place: uniform polynomial approximation of an indicator gives no
control on `Σ n‖aₙ‖`. -/
theorem riccatiGram_hasSum_mem_domain
    (μ : ℕ → ℝ) (hμ0 : ∀ n, 0 ≤ μ n)
    (hμ : ∀ (n : ℕ) (y : H.A0.domain),
      ‖H.A0 ⟨((riccatiGram X) ^ n) (y : E0),
            riccatiGram_pow_mem_domain H hdom hadj n y⟩ -
          ((riccatiGram X) ^ n) (H.A0 y)‖ ≤
        μ n * ‖riccatiGramCommutator H X‖ * ‖(y : E0)‖)
    (a : ℕ → 𝕜) {Φ : E0 →L[𝕜] E0}
    (hΦ : HasSum (fun n => a n • ((riccatiGram X) ^ n)) Φ)
    (hsum : Summable fun n => ‖a n‖ * μ n)
    (x : H.A0.domain) :
    ∃ h : Φ (x : E0) ∈ H.A0.domain,
      ‖H.A0 ⟨Φ (x : E0), h⟩ - Φ (H.A0 x)‖ ≤
        (∑' n, ‖a n‖ * μ n) *
          ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  classical
  set S : ℕ → E0 →L[𝕜] E0 :=
    fun N => ∑ n ∈ Finset.range N, a n • ((riccatiGram X) ^ n) with hS
  have hStend : Filter.Tendsto S Filter.atTop (nhds Φ) := hΦ.tendsto_sum_nat
  -- Evaluation at a fixed vector is continuous, so the partial sums converge
  -- pointwise at both `x` and `A₀ x`.
  have heval : ∀ v : E0, Filter.Tendsto (fun N => S N v) Filter.atTop
      (nhds (Φ v)) := fun v =>
    ((ContinuousLinearMap.apply 𝕜 E0 v).continuous.tendsto Φ).comp hStend
  set G := riccatiGramCommutator H X with hG
  set c := ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  set r : ℕ → E0 :=
    fun N => H.A0 ⟨S N (x : E0),
        riccatiGram_finsetPoly_mem_domain H hdom hadj a (Finset.range N) x⟩ -
      S N (H.A0 x) with hr
  -- The commutator errors are Cauchy, by the `Finset.Ico` form of the bound.
  have hrcauchy : CauchySeq r := by
    refine cauchySeq_of_le_tendsto_0
      (fun N => (∑' n, ‖a n‖ * μ n) * c -
        (∑ n ∈ Finset.range N, ‖a n‖ * μ n) * c) ?_ ?_
    · intro N M K hN hM
      wlog hMN : M ≤ N generalizing M N
      · rw [dist_comm]
        exact this M N hM hN (le_of_not_ge hMN)
      have hdiff : r N - r M =
          H.A0 ⟨(∑ n ∈ Finset.Ico M N, a n • ((riccatiGram X) ^ n)) (x : E0),
              riccatiGram_finsetPoly_mem_domain H hdom hadj a
                (Finset.Ico M N) x⟩ -
            (∑ n ∈ Finset.Ico M N, a n • ((riccatiGram X) ^ n)) (H.A0 x) := by
        have hsplit : S N = S M +
            ∑ n ∈ Finset.Ico M N, a n • ((riccatiGram X) ^ n) := by
          rw [hS]
          simp only
          rw [← Finset.sum_range_add_sum_Ico _ hMN]
        have hmemM := riccatiGram_finsetPoly_mem_domain H hdom hadj a
          (Finset.range M) x
        have hmemI := riccatiGram_finsetPoly_mem_domain H hdom hadj a
          (Finset.Ico M N) x
        have hsub : (⟨S N (x : E0),
              riccatiGram_finsetPoly_mem_domain H hdom hadj a
                (Finset.range N) x⟩ : H.A0.domain) =
            (⟨S M (x : E0), hmemM⟩ : H.A0.domain) +
              ⟨(∑ n ∈ Finset.Ico M N,
                a n • ((riccatiGram X) ^ n)) (x : E0), hmemI⟩ := by
          apply Subtype.ext
          simp [hsplit]
        rw [hr]
        simp only
        rw [hsub, LinearPMap.map_add, hsplit]
        simp only [add_apply]
        abel
      have hbound := norm_riccatiGram_finsetPoly_commutator_le H hdom hadj
        μ hμ0 hμ a (Finset.Ico M N) x
      rw [dist_eq_norm, hdiff]
      refine hbound.trans ?_
      have hIco : (∑ n ∈ Finset.Ico M N, ‖a n‖ * μ n) =
          (∑ n ∈ Finset.range N, ‖a n‖ * μ n) -
            ∑ n ∈ Finset.range M, ‖a n‖ * μ n := by
        rw [← Finset.sum_range_add_sum_Ico _ hMN]; ring
      rw [hIco]
      have hnn : ∀ n : ℕ, 0 ≤ ‖a n‖ * μ n := fun n =>
        mul_nonneg (norm_nonneg _) (hμ0 n)
      have hle : (∑ n ∈ Finset.range N, ‖a n‖ * μ n) ≤
          ∑' n, ‖a n‖ * μ n :=
        hsum.sum_le_tsum _ (fun n _ => hnn n)
      have hsubset : Finset.range K ⊆ Finset.range M := by
        intro n hn
        simp only [Finset.mem_range] at hn ⊢
        omega
      have hKM : (∑ n ∈ Finset.range K, ‖a n‖ * μ n) ≤
          ∑ n ∈ Finset.range M, ‖a n‖ * μ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => hnn n)
      have h1 := mul_le_mul_of_nonneg_right hle hc0
      have h2 := mul_le_mul_of_nonneg_right hKM hc0
      nlinarith [hc0]
    · have := hsum.hasSum.tendsto_sum_nat
      have hmul : Filter.Tendsto
          (fun N => (∑ n ∈ Finset.range N, ‖a n‖ * μ n) * c)
          Filter.atTop (nhds ((∑' n, ‖a n‖ * μ n) * c)) :=
        this.mul_const c
      simpa using (tendsto_const_nhds (x := (∑' n, ‖a n‖ * μ n) * c)
        (f := Filter.atTop (α := ℕ))).sub hmul
  obtain ⟨rl, hrl⟩ := cauchySeq_tendsto_of_complete hrcauchy
  have hAtend : Filter.Tendsto
      (fun N => H.A0 ⟨S N (x : E0),
        riccatiGram_finsetPoly_mem_domain H hdom hadj a (Finset.range N) x⟩)
      Filter.atTop (nhds (rl + Φ (H.A0 x))) := by
    have hid : ∀ N, H.A0 ⟨S N (x : E0),
        riccatiGram_finsetPoly_mem_domain H hdom hadj a
          (Finset.range N) x⟩ = r N + S N (H.A0 x) := by
      intro N; rw [hr]; simp
    simpa only [hid] using hrl.add (heval (H.A0 x))
  obtain ⟨hmem, hval⟩ := mem_domain_of_tendsto H
    (y := fun N => S N (x : E0))
    (hy := fun N => riccatiGram_finsetPoly_mem_domain H hdom hadj a
      (Finset.range N) x)
    (heval (x : E0)) hAtend
  refine ⟨hmem, ?_⟩
  rw [hval]
  have hsimp : rl + Φ (H.A0 x) - Φ (H.A0 x) = rl := by abel
  rw [hsimp]
  have hrbound : ∀ N, ‖r N‖ ≤ (∑' n, ‖a n‖ * μ n) * c := by
    intro N
    refine (norm_riccatiGram_finsetPoly_commutator_le H hdom hadj
      μ hμ0 hμ a (Finset.range N) x).trans ?_
    have hle : (∑ n ∈ Finset.range N, ‖a n‖ * μ n) ≤
        ∑' n, ‖a n‖ * μ n :=
      hsum.sum_le_tsum _ (fun n _ =>
        mul_nonneg (norm_nonneg _) (hμ0 n))
    have := mul_le_mul_of_nonneg_right hle hc0
    nlinarith [hc0]
  have := le_of_tendsto hrl.norm (Filter.Eventually.of_forall hrbound)
  simpa [hc, ← mul_assoc] using this

include hdom hadj in
/-- **The Riccati resolvent `(1 - X†X)⁻¹` preserves the first diagonal domain.**

The Neumann series is where the *geometric* commutator bound is indispensable:
its coefficients are all `1`, so the contractive summand `μ n = n` gives the
divergent `Σ n`, while `μ n = n‖T‖ⁿ⁻¹` is summable because `‖T‖ = ‖X‖² < 1`.

This is the domain half of `MapsDomainTo A₁ A₀ tan2Θ` for
`tan2Θ = 2X(1 - X†X)⁻¹`, which is what the unbounded Sylvester estimate
consumes. -/
theorem riccatiGram_resolvent_mem_domain
    (hlt : ‖riccatiGram X‖ < 1)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    {R : E0 →L[𝕜] E0}
    (hR : HasSum (fun n => (riccatiGram X) ^ n) R)
    (x : H.A0.domain) :
    ∃ h : R (x : E0) ∈ H.A0.domain,
      ‖H.A0 ⟨R (x : E0), h⟩ - R (H.A0 x)‖ ≤
        (∑' n : ℕ, ‖(1 : 𝕜)‖ *
            ((n : ℝ) * ‖riccatiGram X‖ ^ (n - 1))) *
          ‖riccatiGramCommutator H X‖ * ‖(x : E0)‖ := by
  have hμ0 : ∀ n : ℕ, 0 ≤ (n : ℝ) * ‖riccatiGram X‖ ^ (n - 1) := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (norm_nonneg _) _)
  have hgeom : Summable fun n : ℕ => (n : ℝ) * ‖riccatiGram X‖ ^ (n - 1) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) * ‖riccatiGram X‖ ^ n := by
      simpa using
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by simpa using hlt)
    have h2 : Summable fun n : ℕ => ‖riccatiGram X‖ ^ n :=
      summable_geometric_of_lt_one (norm_nonneg _) hlt
    have hs1 : Summable fun n : ℕ => ((n : ℝ) + 1) * ‖riccatiGram X‖ ^ n := by
      simpa [add_mul] using h1.add h2
    rw [← summable_nat_add_iff 1]
    simpa using hs1
  have hsum : Summable fun n : ℕ =>
      ‖(1 : 𝕜)‖ * ((n : ℝ) * ‖riccatiGram X‖ ^ (n - 1)) := hgeom.mul_left _
  have hR' : HasSum (fun n : ℕ => (1 : 𝕜) • ((riccatiGram X) ^ n)) R := by
    simpa using hR
  exact riccatiGram_hasSum_mem_domain H hdom hadj
    (fun n => (n : ℝ) * ‖riccatiGram X‖ ^ (n - 1)) hμ0
    (norm_riccatiGram_pow_commutator_le_geom H hdom hadj hinv hric)
    (fun _ => (1 : 𝕜)) hR' hsum x

include hdom hadj in
/-- **The double-angle tangent operator transports the diagonal domains.**

`tan 2Theta = 2X(1 - X†X)⁻¹` maps `dom A₀` into `dom A₁`, which is the
`MapsDomainTo` half of `TauCeti.LinearPMap.SylvesterEquation A₁ A₀ tan2Θ C`.
It follows immediately once the resolvent is known to preserve `dom A₀`:
the tangent operator is the resolvent followed by `X`, and `X` transports the
domains by hypothesis. -/
theorem doubleAngleTangent_mapsDomainTo
    (hlt : ‖riccatiGram X‖ < 1)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    {R : E0 →L[𝕜] E0}
    (hR : HasSum (fun n => (riccatiGram X) ^ n) R)
    (x : H.A0.domain) :
    ((2 : 𝕜) • (X ∘L R)) (x : E0) ∈ H.A1.domain := by
  obtain ⟨hmem, -⟩ :=
    riccatiGram_resolvent_mem_domain H hdom hadj hlt hinv hric hR x
  have hXmem : X (R (x : E0)) ∈ H.A1.domain := hdom ⟨R (x : E0), hmem⟩
  simpa using Submodule.smul_mem _ (2 : 𝕜) hXmem

include hdom in
/-- **Pointwise Sylvester identity for the double-angle tangent.**

For `x ∈ dom A₀` and any `R` preserving `dom A₀`,

```
A₁(X R x) - X R (A₀ x)
   = X (A₀(Rx) - R(A₀x))  +  (X B₀₁ X - B₁₀)(Rx)
```

The first summand is `X` applied to the *resolvent commutator*, which
`riccatiGram_resolvent_mem_domain` bounds by `‖G‖·Σ n‖T‖ⁿ⁻¹`; the second is
manifestly bounded. Multiplying by `2` and taking `R = (1 - X†X)⁻¹` turns this
into the Sylvester equation satisfied by `tan 2Theta`, with a right-hand side
that is `-2B₁₀` plus an explicit defect.

Only the forward Riccati equation is used, at the vector `Rx`. -/
theorem doubleAngleTangent_sylvester_pointwise
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (R : E0 →L[𝕜] E0) (x : H.A0.domain) (hRx : R (x : E0) ∈ H.A0.domain) :
    H.A1 ⟨X (R (x : E0)), hdom ⟨R (x : E0), hRx⟩⟩ - X (R (H.A0 x)) =
      X (H.A0 ⟨R (x : E0), hRx⟩ - R (H.A0 x)) +
        (X (H.B01 (X (R (x : E0)))) - H.B10 (R (x : E0))) := by
  have h := hric ⟨R (x : E0), hRx⟩
  rw [map_add] at h
  rw [map_sub]
  linear_combination (norm := module) h

include hdom hadj in
/-- **The resolvent commutator is explicitly `R G R`.**

`A₀R - RA₀ = R G R` on `dom A₀`, where `R = (1 - X†X)⁻¹` and `G` is the Riccati
commutator.  Formally this is
`A₀R - RA₀ = R(R⁻¹A₀ - A₀R⁻¹)R = R((1-T)A₀ - A₀(1-T))R = R(A₀T - TA₀)R`.

This matters because it makes the right-hand side of the Sylvester equation for
`tan 2Theta` an **explicit bounded operator**:

```
C = 2·(X ∘ R ∘ G  +  X ∘ B₀₁ ∘ X  -  B₁₀) ∘ R
```

with no density extension anywhere — every factor is already a continuous linear
map.  Without it one would have to extend the commutator from `dom A₀` by
density just to name `C`. -/
theorem riccatiGram_resolvent_commutator_eq
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    {R : E0 →L[𝕜] E0}
    (hRmem : ∀ y : H.A0.domain, R (y : E0) ∈ H.A0.domain)
    (hRight : ∀ u : E0, ((1 : E0 →L[𝕜] E0) - riccatiGram X) (R u) = u)
    (hLeft : ∀ u : E0, R (((1 : E0 →L[𝕜] E0) - riccatiGram X) u) = u)
    (x : H.A0.domain) :
    H.A0 ⟨R (x : E0), hRmem x⟩ - R (H.A0 x) =
      R (riccatiGramCommutator H X (R (x : E0))) := by
  set y : H.A0.domain := ⟨R (x : E0), hRmem x⟩ with hy
  have hTy : (riccatiGram X) (y : E0) ∈ H.A0.domain :=
    gram_mem_domain H hdom hadj y
  -- `x = (1 - T) y` as elements of the domain.
  have hxy : x = y - ⟨(riccatiGram X) (y : E0), hTy⟩ := by
    apply Subtype.ext
    have := hRight (x : E0)
    simpa [hy, sub_eq_iff_eq_add] using this.symm
  have hcomm : H.A0 ⟨(riccatiGram X) (y : E0), hTy⟩ =
      (riccatiGram X) (H.A0 y) + riccatiGramCommutator H X (y : E0) := by
    have h := gram_commutator_eq H hdom hadj hinv hric y
    simpa [riccatiGram] using h
  have hA0x : H.A0 x =
      ((1 : E0 →L[𝕜] E0) - riccatiGram X) (H.A0 y) -
        riccatiGramCommutator H X (y : E0) := by
    rw [hxy, LinearPMap.map_sub, hcomm]
    simp only [sub_apply, one_apply_eq_self]
    abel
  rw [hA0x, map_sub, hLeft]
  abel

include hdom hadj in
/-- **The Sylvester equation satisfied by the double-angle tangent, with an
explicit bounded right-hand side.**

For `R = (1 - X†X)⁻¹` and every `x ∈ dom A₀`,

```
A₁(X R x) - (X R)(A₀ x) = C x,
C := (X ∘ R ∘ G  +  X ∘ B₀₁ ∘ X  -  B₁₀) ∘ R
```

Every factor of `C` is a continuous linear map, so this is the `equation` field
of `TauCeti.LinearPMap.SylvesterEquation A₁ A₀ (X ∘ R) C`; the `mapsTo_domain`
field is `doubleAngleTangent_mapsDomainTo`.  Doubling gives `tan 2Theta`.

Feeding this to `kyFan_unbounded_sylvester_le_of_semibounded_direct` with
`c = 0`, `δ = d` yields an unbounded, arbitrary-ideal Ky Fan estimate for
`tan 2Theta`.  Note `C` is *not* `-B₁₀`: the discrepancy is the commutator term
`X ∘ R ∘ G`, and it is exactly why this route gives a defect form rather than
the sharp constant — see the sharp tan(2Theta) note in Git history. -/
theorem doubleAngleTangent_sylvester_eq
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    {R : E0 →L[𝕜] E0}
    (hRmem : ∀ y : H.A0.domain, R (y : E0) ∈ H.A0.domain)
    (hRight : ∀ u : E0, ((1 : E0 →L[𝕜] E0) - riccatiGram X) (R u) = u)
    (hLeft : ∀ u : E0, R (((1 : E0 →L[𝕜] E0) - riccatiGram X) u) = u)
    (x : H.A0.domain) :
    H.A1 ⟨X (R (x : E0)), hdom ⟨R (x : E0), hRmem x⟩⟩ - X (R (H.A0 x)) =
      ((X ∘L R ∘L riccatiGramCommutator H X +
          X ∘L H.B01 ∘L X - H.B10) ∘L R) (x : E0) := by
  rw [doubleAngleTangent_sylvester_pointwise H hdom hric R x (hRmem x),
    riccatiGram_resolvent_commutator_eq H hdom hadj hinv hric hRmem hRight
      hLeft x]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    add_apply, sub_apply]
  abel

include hdom hadj in
/-- **`tan 2Theta` satisfies a genuine unbounded Sylvester equation.**

Packages the two preceding results as the actual
`TauCeti.LinearPMap.SylvesterEquation H.A1 H.A0 (X ∘L R) C` structure, with

```
C = (X ∘ R ∘ G  +  X ∘ B₀₁ ∘ X  -  B₁₀) ∘ R
```

an explicit continuous linear map.  This is the object the unbounded Ky Fan
Sylvester machinery consumes: with `A₁ ≥ d` and `A₀ ≤ 0` it gives

```
d · kyFanApproximationGauge k (X ∘ R) ≤ kyFanApproximationGauge k C
```

and doubling both sides turns `X ∘ R` into `tan 2Theta`.

`C` is *not* `-B₁₀`; the difference is the commutator term `X ∘ R ∘ G`, which is
exactly why this yields a defect form rather than the sharp constant.  See
the sharp tan(2Theta) note in Git history. -/
theorem doubleAngleTangent_sylvesterEquation
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    {R : E0 →L[𝕜] E0}
    (hRmem : ∀ y : H.A0.domain, R (y : E0) ∈ H.A0.domain)
    (hRight : ∀ u : E0, ((1 : E0 →L[𝕜] E0) - riccatiGram X) (R u) = u)
    (hLeft : ∀ u : E0, R (((1 : E0 →L[𝕜] E0) - riccatiGram X) u) = u) :
    TauCeti.LinearPMap.SylvesterEquation H.A1 H.A0 (X ∘L R)
      ((X ∘L R ∘L riccatiGramCommutator H X +
        X ∘L H.B01 ∘L X - H.B10) ∘L R) where
  mapsTo_domain := fun x => hdom ⟨R (x : E0), hRmem x⟩
  equation := fun x =>
    doubleAngleTangent_sylvester_eq H hdom hadj hinv hric hRmem hRight hLeft x

end Powers'

/-- The Riccati commutator is bounded by the off-diagonal coupling alone: no
norm of a diagonal block appears.  This is what allows band projections of
`X†X` to be used against the unbounded blocks. -/
theorem norm_riccatiGramCommutator_le
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : ‖X‖ ≤ 1) :
    ‖riccatiGramCommutator H X‖ ≤ 2 * (‖H.B01‖ + ‖H.B10‖) := by
  have hXa : ‖(ContinuousLinearMap.adjoint X)‖ = ‖X‖ :=
    ContinuousLinearMap.adjoint.norm_map X
  have hX0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
  have hB01 : (0 : ℝ) ≤ ‖H.B01‖ := norm_nonneg _
  have hB10 : (0 : ℝ) ≤ ‖H.B10‖ := norm_nonneg _
  have h1 : ‖H.B01 ∘L X‖ ≤ ‖H.B01‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    nlinarith
  have h2 : ‖((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X)‖ ≤
      ‖H.B01‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hc : ‖(ContinuousLinearMap.adjoint X) ∘L X‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hXa]; nlinarith
    nlinarith [norm_nonneg (H.B01 ∘L X), norm_nonneg
      ((ContinuousLinearMap.adjoint X) ∘L X)]
  have h3 : ‖(ContinuousLinearMap.adjoint X) ∘L H.B10‖ ≤ ‖H.B10‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [hXa]; nlinarith
  have h4 : ‖((ContinuousLinearMap.adjoint X) ∘L H.B10) ∘L
      ((ContinuousLinearMap.adjoint X) ∘L X)‖ ≤ ‖H.B10‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hc : ‖(ContinuousLinearMap.adjoint X) ∘L X‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hXa]; nlinarith
    nlinarith [norm_nonneg ((ContinuousLinearMap.adjoint X) ∘L H.B10),
      norm_nonneg ((ContinuousLinearMap.adjoint X) ∘L X)]
  refine (norm_sub_le _ _).trans ?_
  have h5 := (norm_sub_le
    (H.B01 ∘L X + ((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X))
    ((ContinuousLinearMap.adjoint X) ∘L H.B10))
  have h6 := norm_add_le (H.B01 ∘L X)
    (((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X))
  linarith

end DavisKahanExt
end TauCeti
