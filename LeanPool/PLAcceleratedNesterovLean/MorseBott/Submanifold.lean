/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.IFTProof
import LeanPool.PLAcceleratedNesterovLean.MorseBott.GradAlign
import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL

/-!
# Theorem 2.16: PŁ ⟹ S is a submanifold

If f is C² and satisfies PŁ around x₀, then S = localMinSet f x₀ is
a C¹ submanifold around x₀ with tangent space T = ker(Hess f(x₀)).

## Proof structure

### Core lemmas

1. `hessian_coercive_on_orthogonal_of_MuPL` (§ 2): D²f(x₀) ≥ μ on T⊥.
   From the eigenvalue lower bound (Prop 2.12).
2. `hessian_injective_on_orthogonal` (§ 2): ker(Hess) ∩ ker(Hess)⊥ = {0}.
   Pure linear algebra (Submodule.orthogonal_disjoint).
3. `ift_gives_graph` (§ 4): Given ∇f(x₀) = 0 and Hessian coercivity on
   T⊥, the IFT produces a C¹ graph φ : T → T⊥ characterizing
   {projected gradient = 0}. Pure IFT, no PŁ needed.
4. `gradient_alignment` (§ 4): Under PŁ, Df(x) = 0 ↔ projected gradient
   vanishes on T⊥. Uses constant rank (Cor 2.13) + self-adjointness of
   Hessian + PŁ.

### Composed results

5. `fderiv_eq_zero_of_isLocalMin` (§ 1): Df(x₀) = 0 at any local min.
   Proved directly via Mathlib's `IsLocalMin.fderiv_eq_zero`.
6. `localMinSet_iff_critical_near` (§ 3): proved from PŁ + local min.
   Chains Fermat's theorem with PŁ-based reverse.
7. `critical_set_is_graph` (§ 4): composed from (5) + (1) + (3) + (4).
   Composes IFT graph with gradient alignment.
8. `MuPL.implies_submanifold` (§ 5): composed from (6) + (7).

## Mathematical outline

The projected gradient map G : E → T⊥ is defined by G(x) = π_{T⊥}(∇f(x)),
where ∇f(x) ∈ E is the Riesz representative of Df(x) ∈ E*.

1. G(x₀) = 0 since Df(x₀) = 0 (gradient vanishes at local min, § 1).
2. DG(x₀) = π_{T⊥} ∘ Hess_Riesz(x₀). Under PŁ, the eigenvalue lower
   bound (Prop 2.12) gives DG(x₀)|_{T⊥} invertible (eigenvalues ≥ μ > 0).
   See § 2.
3. The IFT applied to G yields φ : T → T⊥ with φ(0) = 0, Dφ(0) = 0,
   characterizing {G = 0} as a graph. (Dφ(0) = 0 follows from
   DG(x₀)|_T = 0 since T = ker Hess.)
4. Near x₀: x ∈ S iff Df(x) = 0 iff G(x) = 0 (gradient alignment,
   Lemma 2.14, and constant rank, Cor 2.13). See § 3.
5. Combining: S = graph(φ) near x₀, giving the submanifold structure.

## References

- Rebjock & Boumal, Theorem 2.16, Lemmas 2.14–2.15.
- Implicit function theorem: Mathlib `IsContDiffImplicitAt` /
  `ImplicitFunctionData`.
-/

open Filter Topology Metric Submodule Asymptotics

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Gradient vanishes at local minimizers
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- At a local minimum, the Fréchet derivative vanishes (Fermat's theorem). -/
lemma fderiv_eq_zero_of_isLocalMin (f : E → ℝ) (x₀ : E)
    (hmin : IsLocalMin f x₀) :
    fderiv ℝ f x₀ = 0 :=
  hmin.fderiv_eq_zero

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. Hessian coercivity on the normal space (delegated to PLMB.HessianPL)
-- ════════════════════════════════════════════════════════════════════════════

/-- Under μ-PŁ, the Hessian D²f(x₀) is μ-coercive on T⊥ = (hessianKer f x₀)⊥. -/
lemma hessian_coercive_on_orthogonal_of_MuPL (f : E → ℝ) (μ : ℝ) (x₀ : E)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2 :=
  hessian_coercive_on_orthogonal_of_MuPL_impl f μ x₀ hμ hf hmin hPL

omit [FiniteDimensional ℝ E] in
/-- The Hessian is injective on the orthogonal complement of its kernel.

    **Proof**: If v ∈ T⊥ and Hv = 0, then v ∈ T = ker(Hess), so
    v ∈ T ∩ T⊥. In an inner product space T ∩ T⊥ = ⊥
    (`Submodule.orthogonal_disjoint`), hence v = 0.

    This is a corollary of `hessian_coercive_on_orthogonal_of_MuPL`
    (coercivity ⟹ injectivity), but can also be proved directly
    as pure linear algebra without PŁ. -/
lemma hessian_injective_on_orthogonal (f : E → ℝ) (x₀ : E)
    (v : (hessianKer f x₀).orthogonal)
    (hv : (hessian f x₀).toLinearMap (v : E) = 0) :
    (v : E) = 0 := by
  -- v ∈ T⊥ and hv says v ∈ ker(Hess) = T, so v ∈ T ∩ T⊥ = {0}
  have hmem_ker : (v : E) ∈ hessianKer f x₀ := LinearMap.mem_ker.mpr hv
  have hmem_orth : (v : E) ∈ (hessianKer f x₀).orthogonal := v.property
  -- ⟪v, v⟫ = 0 (v ∈ K and v ∈ K⊥), hence v = 0
  exact inner_self_eq_zero.mp
    (Submodule.inner_right_of_mem_orthogonal hmem_ker hmem_orth)

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. Near x₀: localMinSet ↔ critical set
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- Near a local minimizer satisfying μ-PŁ, membership in S = localMinSet f x₀
    is equivalent to being a critical point (Df(x) = 0).

    **Forward** (x ∈ S ⟹ Df(x) = 0): Fermat's theorem — every local
    minimizer has zero derivative (`IsLocalMin.fderiv_eq_zero`).

    **Reverse** (Df(x) = 0 ⟹ x ∈ S, for x near x₀):
    1. μ-PŁ gives f(x) − f(x₀) ≤ (2μ)⁻¹ ‖Df(x)‖² = 0, so f(x) ≤ f(x₀).
    2. x₀ is a local min, so f(y) ≥ f(x₀) for y near x₀. Since x is near
       x₀, f(x) ≥ f(x₀). Combined: f(x) = f(x₀).
    3. x inherits the local-min property: f(y) ≥ f(x₀) = f(x) for y near
       both x and x₀. -/
lemma localMinSet_iff_critical_near (f : E → ℝ) (μ : ℝ) (x₀ : E) (_hμ : 0 < μ)
    (_hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (hPL : MuPL f μ x₀) :
    ∃ V ∈ 𝓝 x₀, ∀ x ∈ V,
      (x ∈ localMinSet f x₀ ↔ fderiv ℝ f x = 0) := by
  -- Unfold PŁ and local-min into neighborhood-level statements
  have hPL' : ∀ᶠ x in 𝓝 x₀, f x - f x₀ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 := hPL
  have hmin_ev : ∀ᶠ y in 𝓝 x₀, f x₀ ≤ f y := hmin
  -- Propagate the local-min property to nearby points
  have hmin_prop : ∀ᶠ x in 𝓝 x₀, ∀ᶠ y in 𝓝 x, f x₀ ≤ f y :=
    hmin_ev.eventually_nhds
  -- Combine and extract a common neighborhood V
  obtain ⟨V, hV, hVprop⟩ := ((hPL'.and hmin_ev).and hmin_prop).exists_mem
  refine ⟨V, hV, fun x hxV => ?_⟩
  obtain ⟨⟨hPL_x, hfx0_le⟩, hmin_x⟩ := hVprop x hxV
  constructor
  · -- Forward: x ∈ S → Df(x) = 0 (Fermat's theorem, § 1)
    rintro ⟨hx_min, -⟩
    exact IsLocalMin.fderiv_eq_zero hx_min
  · -- Reverse: Df(x) = 0 → x ∈ S (using PŁ)
    intro hgrad
    -- PŁ + Df(x) = 0 gives RHS = 0, so f(x) ≤ f(x₀)
    have hrhs : (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 = 0 := by
      simp_all
    -- f(x) = f(x₀) by antisymmetry
    have hfx_eq : f x = f x₀ := le_antisymm (by linarith) hfx0_le
    -- x ∈ localMinSet: IsLocalMin f x ∧ f x = f x₀
    exact ⟨hmin_x.mono fun y hy => by linarith, hfx_eq⟩

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. IFT: critical set is a C¹ graph over T
-- ════════════════════════════════════════════════════════════════════════════

/-- **IFT core step**: Given ∇f(x₀) = 0 and Hessian μ-coercive on T⊥,
    the IFT produces a C¹ graph φ : T → T⊥ characterizing the *projected*
    critical set {G = 0} near x₀, where G(x) = π_{T⊥}(∇f(x)).

    **Setup**: Decompose E ≅ T × T⊥ via the orthogonal direct sum. Define
    the projected gradient map:
      G : T × T⊥ → T⊥,   G(t, n) = π_{T⊥}(∇f(x₀ + t + n))
    In Lean, "G(x) = 0" is expressed as
      `∀ w : T⊥, Df(x)(w) = 0`
    i.e., the Fréchet derivative at x vanishes on all normal vectors.

    **Hypotheses used**:
    • `hgrad`: G(0,0) = π_{T⊥}(∇f(x₀)) = 0.
    • `hcoer`: ∂G/∂n(0,0) = π_{T⊥} ∘ Hess_Riesz(x₀)|_{T⊥} is μ-coercive,
      hence a continuous linear equivalence T⊥ ≃L[ℝ] T⊥.
    • `hf`: f is C², so G is C¹ (`IsContDiffImplicitAt`).

    **IFT output**: φ : T → T⊥ with φ(0) = 0, Dφ(0) = 0, φ is C¹, and
    {G = 0} = graph(φ) near x₀.

    **Important**: This characterizes {G = 0} (projected gradient vanishes
    on T⊥), *not* {Df = 0} (full gradient vanishes). Without PŁ, these
    differ: e.g. f(x,y) = y²/2 + x³/3 has {G = 0} = {y = 0} but
    {Df = 0} = {(0,0)}. The upgrade {G = 0} → {Df = 0} requires
    `gradient_alignment`, which uses PŁ. -/
lemma ift_gives_graph (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (hgrad : fderiv ℝ f x₀ = 0)
    (hcoer : ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2) :
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 1 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U,
        (∀ w : (hessianKer f x₀).orthogonal, fderiv ℝ f x (w : E) = 0) ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) :=
  ift_gives_graph_impl f μ x₀ hμ hf hgrad hcoer

/-- **Gradient alignment** (Lemma 2.14 / Cor 2.13 in the paper).
    Under PŁ, the full gradient vanishes iff its T⊥-projection vanishes.

    **Forward** (trivial): Df(x) = 0 ⟹ Df(x)(w) = 0 for all w ∈ T⊥.

    **Backward** (uses PŁ): If Df(x) vanishes on T⊥, i.e. ∇f(x) ∈ T,
    then ∇f(x) = 0. The key argument uses self-adjointness of the Hessian:
    since H is symmetric and T = ker(H), H maps T⊥ to T⊥, so
      π_T(∇f(x)) = π_T(H(x − x₀) + o(‖x − x₀‖)) = o(‖x − x₀‖).
    Thus ‖Df(x)‖ = o(‖x − x₀‖) when G(x) = 0. Combined with PŁ
    (f(x) − f(x₀) ≤ (2μ)⁻¹ ‖Df(x)‖²) and f(x) ≥ f(x₀), constant rank
    of the Hessian on S (Cor 2.13) forces Df(x) = 0 near x₀. -/
lemma gradient_alignment (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (hPL : MuPL f μ x₀) :
    ∃ W ∈ 𝓝 x₀, ∀ x ∈ W,
      fderiv ℝ f x = 0 ↔
        (∀ w : (hessianKer f x₀).orthogonal, fderiv ℝ f x (w : E) = 0) :=
  gradient_alignment_impl f μ x₀ hμ hf hmin hPL

/-- **IFT for the critical set** (Lemma 2.15 in the paper).

    The critical set {x near x₀ | Df(x) = 0} is locally a C¹ graph over
    T = ker(Hess f(x₀)):  there exist U ∈ 𝓝 x₀ and a C¹ map φ : T → T⊥
    with φ(0) = 0, Dφ(0) = 0, such that for x ∈ U:

      Df(x) = 0  ↔  π_{T⊥}(x − x₀) = φ(π_T(x − x₀))

    **Proof** (composition of §§ 1–2, `ift_gives_graph`, and
    `gradient_alignment`):
    1. `fderiv_eq_zero_of_isLocalMin`: ∇f(x₀) = 0 (Fermat, § 1).
    2. `hessian_coercive_on_orthogonal_of_MuPL`: D²f(x₀) ≥ μ on T⊥ (§ 2).
    3. `ift_gives_graph`: IFT characterizes {projected gradient = 0} as
       graph(φ) from (1) and (2).
    4. `gradient_alignment`: PŁ upgrades {proj. gradient = 0} to {Df = 0}. -/
lemma critical_set_is_graph (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀) (hPL : MuPL f μ x₀) :
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 1 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U, fderiv ℝ f x = 0 ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) := by
  -- Step 1: IFT characterizes {projected gradient = 0} as a graph
  obtain ⟨U₁, hU₁, φ, hφC1, hφ0, hDφ0, hIFT⟩ :=
    ift_gives_graph f μ x₀ hμ hf
      (fderiv_eq_zero_of_isLocalMin f x₀ hmin)
      (hessian_coercive_on_orthogonal_of_MuPL f μ x₀ hμ hf hmin hPL)
  -- Step 2: Gradient alignment upgrades projected-gradient=0 to Df=0
  obtain ⟨W, hW, hAlign⟩ :=
    gradient_alignment f μ x₀ hμ hf hmin hPL
  -- Step 3: Compose on intersection
  exact ⟨U₁ ∩ W, Filter.inter_mem hU₁ hW, φ, hφC1, hφ0, hDφ0,
    fun x hx => (hAlign x hx.2).trans (hIFT x hx.1)⟩

-- ════════════════════════════════════════════════════════════════════════════
-- § 5. Main theorem
-- ════════════════════════════════════════════════════════════════════════════

/-- **Theorem 2.16** (PŁ ⟹ S is a submanifold).

    If f is C² and satisfies PŁ around x₀, then S = localMinSet f x₀ is
    a C¹ submanifold around x₀ with tangent space T = ker(Hess f(x₀)).

    **Proof**: Two parts.
    1. **Membership**: x₀ ∈ S holds by `self_mem_localMinSet`.
    2. **Graph structure**: Chain two equivalences on intersected neighborhoods:
       - `localMinSet_iff_critical_near` (§ 3): x ∈ S  ↔  Df(x) = 0
       - `critical_set_is_graph` (§ 4):        Df(x) = 0  ↔  graph(φ)
       giving x ∈ S ↔ π_{T⊥}(x − x₀) = φ(π_T(x − x₀)). -/
theorem MuPL.implies_submanifold (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    IsLocalSubmanifoldAt (localMinSet f x₀) x₀ (hessianKer f x₀) := by
  -- Part 1: x₀ ∈ S
  refine ⟨self_mem_localMinSet hmin, ?_⟩
  -- Part 2: Obtain the IFT graph structure for the critical set
  obtain ⟨U, hU, φ, hφC1, hφ0, hDφ0, hGraph⟩ :=
    critical_set_is_graph f μ x₀ hμ hf hmin hPL
  -- Part 3: Obtain the local equivalence S ↔ critical set
  obtain ⟨V, hV, hCrit⟩ :=
    localMinSet_iff_critical_near f μ x₀ hμ hf hmin hPL
  -- Part 4: Intersect neighborhoods, chain the two ↔'s via Iff.trans
  exact ⟨U ∩ V, Filter.inter_mem hU hV, φ, hφC1, hφ0, hDφ0,
    fun x hx => (hCrit x hx.2).trans (hGraph x hx.1)⟩

/-- C³ version of `critical_set_is_graph`: yields a C² graph. -/
lemma critical_set_is_graph₂ (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 3 f x₀) (hmin : IsLocalMin f x₀) (hPL : MuPL f μ x₀) :
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U, fderiv ℝ f x = 0 ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) := by
  have hf2 : ContDiffAt ℝ 2 f x₀ := hf.of_le (by norm_num)
  obtain ⟨U₁, hU₁, φ, hφC2, hφ0, hDφ0, hIFT⟩ :=
    ift_gives_graph_impl₂ f μ x₀ hμ hf
      (fderiv_eq_zero_of_isLocalMin f x₀ hmin)
      (hessian_coercive_on_orthogonal_of_MuPL f μ x₀ hμ hf2 hmin hPL)
  obtain ⟨W, hW, hAlign⟩ :=
    gradient_alignment f μ x₀ hμ hf2 hmin hPL
  exact ⟨U₁ ∩ W, Filter.inter_mem hU₁ hW, φ, hφC2, hφ0, hDφ0,
    fun x hx => (hAlign x hx.2).trans (hIFT x hx.1)⟩

/-- C³ version of `MuPL.implies_submanifold`: the local-min set is locally a
    C² graph. -/
theorem MuPL.implies_submanifold_C2_chart (f : E → ℝ) (μ : ℝ) (x₀ : E)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 3 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    x₀ ∈ localMinSet f x₀ ∧
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U, x ∈ localMinSet f x₀ ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) := by
  have hf2 : ContDiffAt ℝ 2 f x₀ := hf.of_le (by norm_num)
  refine ⟨self_mem_localMinSet hmin, ?_⟩
  obtain ⟨U, hU, φ, hφC2, hφ0, hDφ0, hGraph⟩ :=
    critical_set_is_graph₂ f μ x₀ hμ hf hmin hPL
  obtain ⟨V, hV, hCrit⟩ :=
    localMinSet_iff_critical_near f μ x₀ hμ hf2 hmin hPL
  exact ⟨U ∩ V, Filter.inter_mem hU hV, φ, hφC2, hφ0, hDφ0,
    fun x hx => (hCrit x hx.2).trans (hGraph x hx.1)⟩

end PLAcceleratedNesterovLean
