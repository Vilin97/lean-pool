/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.KreinMilman

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Closed convex hull and Straszewicz reductions

This module packages the closed-convex-hull algebra and compact Krein-Milman/Straszewicz-style
interfaces used in the Rockafellar 25.6 route.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- If every point of `s` belongs to a closed convex set `C`, then the closed convex hull of `s`
is contained in `C`. -/
theorem closure_convexHull_subset_of_subset_closed_convex
    {s C : Set E} (hsC : s ⊆ C) (hclosed : IsClosed C) (hconv : Convex ℝ C) :
    closure (convexHull ℝ s) ⊆ C := by
  exact closure_minimal (convexHull_min hsC hconv) hclosed

/-- First inclusion in Rockafellar 25.6, in the local finite-valued setting.

If `u` is convex on `domain`, the sampling region lies in the interior of `domain`, and `u` is
continuous at the base point `y`, then the closed convex hull of gradient cluster values at `y`
is contained in the subdifferential at `y`. -/
theorem closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn
    {domain sample : Set E} {u : E → ℝ} {y : E}
    (hu : ConvexOn ℝ domain u)
    (hsample : sample ⊆ interior domain)
    (hy : y ∈ sample)
    (hcont : ContinuousAt u y) :
    closure
        (convexHull ℝ
          (HasSubgradientLinearizationOnAt.GradientClusterSet
            (differentiabilitySetOn sample u) (gradient u) y)) ⊆
      {q : E | SubgradientOn domain u y q} :=
  closure_convexHull_subset_of_subset_closed_convex
    (fun _ hq =>
      GradientClusterSet.subset_subgradientOn_of_convexOn hu hsample hy hcont hq)
    isClosed_setOf_subgradientOn
    convex_setOf_subgradientOn

/-- Pointwise form of
`closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn`. -/
theorem subgradientOn_of_mem_closure_convexHull_gradientClusterSet_of_convexOn
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hu : ConvexOn ℝ domain u)
    (hsample : sample ⊆ interior domain)
    (hy : y ∈ sample)
    (hcont : ContinuousAt u y)
    (hp :
      p ∈ closure
        (convexHull ℝ
          (HasSubgradientLinearizationOnAt.GradientClusterSet
            (differentiabilitySetOn sample u) (gradient u) y))) :
    SubgradientOn domain u y p :=
  closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn
    hu hsample hy hcont hp

/-- Open-domain version of the first inclusion in Rockafellar 25.6.

For a finite-dimensional finite-valued convex function on an open domain, continuity at interior
points and the inclusion `sample ⊆ interior domain` are automatic from `sample ⊆ domain`. -/
theorem closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn_isOpen
    [FiniteDimensional ℝ E]
    {domain sample : Set E} {u : E → ℝ} {y : E}
    (hopen : IsOpen domain)
    (hsubset : sample ⊆ domain)
    (hu : ConvexOn ℝ domain u)
    (hy : y ∈ sample) :
    closure
        (convexHull ℝ
          (HasSubgradientLinearizationOnAt.GradientClusterSet
            (differentiabilitySetOn sample u) (gradient u) y)) ⊆
      {q : E | SubgradientOn domain u y q} := by
  refine closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn
    hu ?_ hy ?_
  · intro x hx
    simpa [hopen.interior_eq] using hsubset hx
  · exact (hu.continuousOn hopen).continuousAt (hopen.mem_nhds (hsubset hy))

/-- Pointwise open-domain version of the first inclusion in Rockafellar 25.6. -/
theorem subgradientOn_of_mem_closure_convexHull_gradientClusterSet_of_convexOn_isOpen
    [FiniteDimensional ℝ E]
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hopen : IsOpen domain)
    (hsubset : sample ⊆ domain)
    (hu : ConvexOn ℝ domain u)
    (hy : y ∈ sample)
    (hp :
      p ∈ closure
        (convexHull ℝ
          (HasSubgradientLinearizationOnAt.GradientClusterSet
            (differentiabilitySetOn sample u) (gradient u) y))) :
    SubgradientOn domain u y p :=
  closure_convexHull_gradientClusterSet_subset_subgradientOn_of_convexOn_isOpen
    hopen hsubset hu hy hp

omit [CompleteSpace E] in
/-- The closure of a set is contained in the closure of its convex hull. -/
theorem closure_subset_closure_convexHull (s : Set E) :
    closure s ⊆ closure (convexHull ℝ s) :=
  closure_mono (subset_convexHull (𝕜 := ℝ) s)

/-- A nonempty compact exposed face has an extreme point. -/
theorem isCompact_exposedFace_extremePoints_nonempty
    {s : Set E} (hcompact : IsCompact s) (hne : s.Nonempty) (normal : E) :
    ((exposedFace s normal).extremePoints ℝ).Nonempty :=
  (isCompact_exposedFace hcompact normal).extremePoints_nonempty
    (IsCompact.exposedFace_nonempty hcompact hne normal)

/-- A nonempty compact exposed face contains a point which is extreme in the original set. -/
theorem exists_mem_exposedFace_and_mem_extremePoints_of_isCompact
    {s : Set E} (hcompact : IsCompact s) (hne : s.Nonempty) (normal : E) :
    ∃ p : E, p ∈ exposedFace s normal ∧ p ∈ s.extremePoints ℝ := by
  rcases isCompact_exposedFace_extremePoints_nonempty hcompact hne normal with ⟨p, hp⟩
  exact ⟨p, _root_.extremePoints_subset hp,
    exposedFace_extremePoints_subset_extremePoints s normal hp⟩

omit [CompleteSpace E] in
/-- Compact Krein-Milman plus a Straszewicz-style exposed-point approximation hypothesis gives the
closed-convex-hull exposed-point representation.

This theorem uses Mathlib's `closure_convexHull_extremePoints` and leaves only the
Straszewicz-type input explicit: every extreme point belongs to the closed convex hull of exposed
points. In Rockafellar 25.6 this compact form is one ingredient toward the no-lines closed
convex-set representation. -/
theorem subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_convexHull_exposedPoints
    {s : Set E} (hcompact : IsCompact s) (hconv : Convex ℝ s)
    (hstrasz :
      s.extremePoints ℝ ⊆ closure (convexHull ℝ (exposedPoints s))) :
    s ⊆ closure (convexHull ℝ (exposedPoints s)) := by
  have hclosedC : IsClosed (closure (convexHull ℝ (exposedPoints s))) :=
    isClosed_closure
  have hconvC : Convex ℝ (closure (convexHull ℝ (exposedPoints s))) :=
    (convex_convexHull ℝ (exposedPoints s)).closure
  have hhull_subset :
      closure (convexHull ℝ (s.extremePoints ℝ)) ⊆
        closure (convexHull ℝ (exposedPoints s)) :=
    closure_convexHull_subset_of_subset_closed_convex hstrasz hclosedC hconvC
  intro p hp
  exact hhull_subset (by simpa [closure_convexHull_extremePoints hcompact hconv] using hp)

omit [CompleteSpace E] in
/-- Compact Krein-Milman plus the literal Straszewicz-style exposed-point approximation hypothesis.

Here the hypothesis says every extreme point lies in the closure of exposed points, matching the
usual statement that every extreme point is a limit of exposed points. The previous
closed-convex-hull version follows because `closure (exposedPoints s)` is contained in
`closure (convexHull ℝ (exposedPoints s))`. -/
theorem subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_exposedPoints
    {s : Set E} (hcompact : IsCompact s) (hconv : Convex ℝ s)
    (hstrasz : s.extremePoints ℝ ⊆ closure (exposedPoints s)) :
    s ⊆ closure (convexHull ℝ (exposedPoints s)) := by
  exact
    subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_convexHull_exposedPoints
      hcompact hconv (hstrasz.trans (closure_subset_closure_convexHull (exposedPoints s)))

/-- Compact Krein-Milman plus a Mathlib-shaped Straszewicz approximation hypothesis.

This variant accepts Mathlib's `Set.exposedPoints` notation directly and converts it to the
project-local inner-product exposed-point carrier. -/
theorem subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_mathlib_exposedPoints
    {s : Set E} (hcompact : IsCompact s) (hconv : Convex ℝ s)
    (hstrasz : s.extremePoints ℝ ⊆ closure (Set.exposedPoints ℝ s)) :
    s ⊆ closure (convexHull ℝ (exposedPoints s)) := by
  refine subset_closure_convexHull_exposedPoints_of_extreme_subset_closure_exposedPoints
    hcompact hconv ?_
  intro p hp
  simpa [exposedPoints_eq_mathlib_exposedPoints] using hstrasz hp

/-- Finite-dimensional compact-convex Straszewicz theorem, stated as a reusable theorem
boundary.

This is the remaining convex-geometry input in the Rockafellar route: every extreme point of a
compact convex set is a limit of Mathlib exposed points. It is stated separately from
subdifferentials so the source-cube Aleksandrov theorem can depend on the standard compact-convex
form rather than on an ad hoc subgradient-specific hypothesis. -/
def StraszewiczCompactConvexStatement (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Prop :=
  ∀ ⦃s : Set E⦄,
    IsCompact s →
      Convex ℝ s →
        s.extremePoints ℝ ⊆ closure (Set.exposedPoints ℝ s)

omit [CompleteSpace E] in
/-- If every extreme point is already exposed, then the Straszewicz closure conclusion is
immediate. -/
theorem extremePoints_subset_closure_mathlib_exposedPoints_of_subset_mathlib_exposedPoints
    {s : Set E} (h : s.extremePoints ℝ ⊆ Set.exposedPoints ℝ s) :
    s.extremePoints ℝ ⊆ closure (Set.exposedPoints ℝ s) :=
  h.trans subset_closure

omit [CompleteSpace E] in
/-- In a subsingleton space, every point of every set is exposed in Mathlib's sense. -/
theorem mathlib_exposedPoints_eq_self_of_subsingleton
    [Subsingleton E] (s : Set E) :
    Set.exposedPoints ℝ s = s := by
  apply subset_antisymm
  · exact _root_.exposedPoints_subset
  · intro x hx
    refine ⟨hx, 0, ?_⟩
    intro y hy
    refine ⟨by simp, ?_⟩
    intro _hle
    exact Subsingleton.elim y x

omit [CompleteSpace E] in
/-- A singleton is exposed by the zero functional. -/
theorem mathlib_exposedPoints_singleton (p : E) :
    Set.exposedPoints ℝ ({p} : Set E) = {p} := by
  apply subset_antisymm
  · exact _root_.exposedPoints_subset
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨Set.mem_singleton p, 0, ?_⟩
    intro y hy
    refine ⟨by simp, ?_⟩
    intro _hle
    exact Set.mem_singleton_iff.mp hy

omit [CompleteSpace E] in
/-- The compact-convex Straszewicz statement is trivial in a subsingleton ambient space. -/
theorem straszewiczCompactConvexStatement_of_subsingleton
     [Subsingleton E] :
    StraszewiczCompactConvexStatement E := by
  intro s _hcompact _hconv p hp
  rw [mathlib_exposedPoints_eq_self_of_subsingleton (s := s)]
  exact subset_closure (_root_.extremePoints_subset hp)

omit [CompleteSpace E] in
/-- The closure of the exposed points of a compact set is compact. -/
theorem isCompact_closure_mathlib_exposedPoints
    {s : Set E} (hcompact : IsCompact s) :
    IsCompact (closure (Set.exposedPoints ℝ s)) :=
  hcompact.of_isClosed_subset isClosed_closure
    (closure_minimal _root_.exposedPoints_subset hcompact.isClosed)

/-- The weighted sum of a fixed finite tuple of points.

This is the continuous map from `K^(n)` times the standard simplex which will be used to prove
that finite-dimensional convex hulls of compact sets are compact. -/
def convexCombinationTuple (n : ℕ) (xw : (Fin n → E) × (Fin n → ℝ)) : E :=
  ∑ i : Fin n, xw.2 i • xw.1 i

omit [CompleteSpace E] in
/-- The fixed-tuple weighted-sum map is continuous. -/
theorem continuous_convexCombinationTuple (n : ℕ) :
    Continuous (convexCombinationTuple (E := E) n) := by
  unfold convexCombinationTuple
  fun_prop

omit [CompleteSpace E] in
/-- A weighted tuple whose points lie in `s` and whose weights lie in the standard simplex gives a
point of `convexHull ℝ s`. -/
theorem convexCombinationTuple_mem_convexHull
    {s : Set E} {n : ℕ} {xw : (Fin n → E) × (Fin n → ℝ)}
    (hx : ∀ i : Fin n, xw.1 i ∈ s)
    (hw : xw.2 ∈ {f : Fin n → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) :
    convexCombinationTuple n xw ∈ convexHull ℝ s :=
  mem_convexHull_of_exists_fintype xw.2 xw.1 hw.1 hw.2 hx rfl

omit [CompleteSpace E] in
/-- The image of `K^n × Δⁿ` under the weighted-tuple map is contained in `convexHull ℝ K`. -/
theorem convexCombinationTuple_image_subset_convexHull
    {s : Set E} (n : ℕ) :
    convexCombinationTuple (E := E) n ''
        ((Set.pi Set.univ fun _ : Fin n => s) ×ˢ
          {f : Fin n → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) ⊆
      convexHull ℝ s := by
  rintro y ⟨xw, hxw, rfl⟩
  exact convexCombinationTuple_mem_convexHull
    (fun i => hxw.1 i (Set.mem_univ i)) hxw.2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The fixed compact domain `K^n × Δⁿ` for the weighted-tuple map. -/
theorem isCompact_convexCombinationTuple_domain
    {s : Set E} (hcompact : IsCompact s) (n : ℕ) :
    IsCompact ((Set.pi Set.univ fun _ : Fin n => s) ×ˢ
      {f : Fin n → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) := by
  refine (isCompact_univ_pi fun _ : Fin n => hcompact).prod ?_
  have hclosed : IsClosed {f : Fin n → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
    have h₁ : IsClosed (⋂ i : Fin n, {f : Fin n → ℝ | 0 ≤ f i}) :=
      isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h₂ : IsClosed {f : Fin n → ℝ | ∑ i, f i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    convert h₁.inter h₂ using 1
    ext f
    simp
  refine (isCompact_univ_pi fun _ : Fin n =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
  intro f hf i _
  refine ⟨hf.1 i, ?_⟩
  rw [← hf.2]
  exact Finset.single_le_sum (fun j _ => hf.1 j) (Finset.mem_univ i)

omit [CompleteSpace E] in
/-- The fixed-tuple weighted-sum image of a compact set and the standard simplex is compact. -/
theorem isCompact_convexCombinationTuple_image
    {s : Set E} (hcompact : IsCompact s) (n : ℕ) :
    IsCompact
      (convexCombinationTuple (E := E) n ''
        ((Set.pi Set.univ fun _ : Fin n => s) ×ˢ
          {f : Fin n → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1})) :=
  (isCompact_convexCombinationTuple_domain hcompact n).image
    (continuous_convexCombinationTuple (E := E) n)

omit [CompleteSpace E] in
/-- An affinely independent family in a finite-dimensional space can be indexed inside
`Fin (finrank + 1)`.

This is the cardinality bridge used in the Carathéodory-to-fixed-simplex proof: after
Carathéodory gives an affinely independent family, this lemma provides room to pad it with zero
weights in the fixed index type `Fin (Module.finrank ℝ E + 1)`. -/
theorem exists_embedding_finrank_succ_of_affineIndependent
    [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] {z : ι → E}
    (hz : AffineIndependent ℝ z) :
    Nonempty (ι ↪ Fin (Module.finrank ℝ E + 1)) := by
  classical
  let := Fintype.ofFinite ι
  refine Function.Embedding.nonempty_of_card_le ?_
  have hdim :
      Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 ≤
        Module.finrank ℝ E + 1 :=
    Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range z))) 1
  simpa [Fintype.card_fin] using hz.card_le_finrank_succ.trans hdim

/-- Summing an extension-by-zero along an embedding recovers the original finite sum. -/
theorem sum_extend_embedding_zero
    {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ↪ κ) (f : ι → M) :
    (∑ j : κ, Function.extend e f (fun _ => 0) j) = ∑ i : ι, f i := by
  classical
  let image : Finset κ := Finset.univ.image e
  have hsubset : image ⊆ Finset.univ := by
    intro j hj
    exact Finset.mem_univ j
  have hsum_image :
      image.sum (fun j => Function.extend e f (fun _ => 0) j) = ∑ i : ι, f i := by
    rw [show image = Finset.univ.image e from rfl]
    rw [Finset.sum_image]
    · simp [e.injective.extend_apply]
    · exact e.injective.injOn
  calc
    (∑ j : κ, Function.extend e f (fun _ => 0) j)
        = image.sum (fun j => Function.extend e f (fun _ => 0) j) := by
          symm
          refine Finset.sum_subset hsubset ?_
          intro j _hj hjnot
          rw [Function.extend_apply']
          intro hjrange
          rcases hjrange with ⟨i, hi⟩
          exact hjnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    _ = ∑ i : ι, f i := hsum_image

omit [CompleteSpace E] in
/-- Padding scalar weights and points along an embedding with zero weights preserves the weighted
sum. -/
theorem sum_smul_extend_embedding_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (w : ι → ℝ) (z : ι → E) (base : E) :
    (∑ j : κ,
        Function.extend e w (fun _ => 0) j • Function.extend e z (fun _ => base) j) =
      ∑ i : ι, w i • z i := by
  classical
  have hpoint :
      (fun j : κ =>
          Function.extend e w (fun _ => 0) j • Function.extend e z (fun _ => base) j) =
        Function.extend e (fun i : ι => w i • z i) (fun _ => 0) := by
    funext j
    by_cases hj : ∃ i : ι, e i = j
    · rcases hj with ⟨i, rfl⟩
      simp [e.injective.extend_apply]
    · rw [Function.extend_apply' w (fun _ => 0) j hj,
        Function.extend_apply' z (fun _ => base) j hj,
        Function.extend_apply' (fun i : ι => w i • z i) (fun _ => 0) j hj,
        zero_smul]
  rw [hpoint]
  exact sum_extend_embedding_zero e (fun i : ι => w i • z i)

/-- Extending simplex weights by zero along an embedding gives a point of the larger simplex. -/
theorem extend_embedding_mem_stdSimplex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) {w : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    Function.extend e w (fun _ => 0) ∈ {f : κ → ℝ | (∀ j, 0 ≤ f j) ∧ ∑ j, f j = 1} := by
  classical
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : ∃ i : ι, e i = j
    · rcases hj with ⟨i, rfl⟩
      simpa [e.injective.extend_apply] using hw_nonneg i
    · rw [Function.extend_apply' w (fun _ => 0) j hj]
  · simpa [sum_extend_embedding_zero e w] using hw_sum

omit [CompleteSpace E] in
/-- In finite dimension, every point of `convexHull ℝ s` is represented by the fixed
`(finrank + 1)`-tuple weighted-sum image, provided `s` is nonempty.

This is Carathéodory's theorem plus the zero-padding bridge: Carathéodory gives an affinely
independent finite family of positive weights, the cardinality bound embeds that family into
`Fin (finrank + 1)`, and all unused coordinates are filled by a base point of `s` with weight
zero. -/
theorem convexHull_subset_convexCombinationTuple_image_finrank_succ
    [FiniteDimensional ℝ E] {s : Set E} (hsne : s.Nonempty) :
    convexHull ℝ s ⊆
      convexCombinationTuple (E := E) (Module.finrank ℝ E + 1) ''
        ((Set.pi Set.univ fun _ : Fin (Module.finrank ℝ E + 1) => s) ×ˢ
          {f : Fin (Module.finrank ℝ E + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) := by
  classical
  intro x hx
  rcases eq_pos_convex_span_of_mem_convexHull hx with
    ⟨ι, hι, z, w, hzs, haff, hwpos, hwsum, hsum⟩
  let : Fintype ι := hι
  let : Finite ι := Fintype.finite hι
  rcases exists_embedding_finrank_succ_of_affineIndependent (E := E) haff with ⟨e⟩
  rcases hsne with ⟨base, hbase⟩
  let zPad : Fin (Module.finrank ℝ E + 1) → E :=
    Function.extend e z (fun _ => base)
  let wPad : Fin (Module.finrank ℝ E + 1) → ℝ :=
    Function.extend e w (fun _ => 0)
  refine ⟨(zPad, wPad), ?_, ?_⟩
  · constructor
    · intro j _hj
      by_cases hj : ∃ i : ι, e i = j
      · rcases hj with ⟨i, rfl⟩
        have hzi : z i ∈ Set.range z := ⟨i, rfl⟩
        simpa [zPad, e.injective.extend_apply] using hzs hzi
      · simpa [zPad, Function.extend_apply' z (fun _ => base) j hj] using hbase
    · exact extend_embedding_mem_stdSimplex e (fun i => (hwpos i).le) hwsum
  · dsimp [convexCombinationTuple, zPad, wPad]
    exact (sum_smul_extend_embedding_zero e w z base).trans hsum

omit [CompleteSpace E] in
/-- For a nonempty set in finite dimension, the fixed `(finrank + 1)`-tuple simplex image is
exactly the convex hull. -/
theorem convexHull_eq_convexCombinationTuple_image_finrank_succ
    [FiniteDimensional ℝ E] {s : Set E} (hsne : s.Nonempty) :
    convexHull ℝ s =
      convexCombinationTuple (E := E) (Module.finrank ℝ E + 1) ''
        ((Set.pi Set.univ fun _ : Fin (Module.finrank ℝ E + 1) => s) ×ˢ
          {f : Fin (Module.finrank ℝ E + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) :=
  Set.Subset.antisymm (convexHull_subset_convexCombinationTuple_image_finrank_succ hsne)
    (convexCombinationTuple_image_subset_convexHull (E := E) (Module.finrank ℝ E + 1))

omit [CompleteSpace E] in
/-- In finite dimension, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact
    [FiniteDimensional ℝ E] {s : Set E} (hcompact : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [convexHull_empty]
  · rw [convexHull_eq_convexCombinationTuple_image_finrank_succ (E := E) hsne]
    exact isCompact_convexCombinationTuple_image (E := E) hcompact
      (Module.finrank ℝ E + 1)

omit [CompleteSpace E] in
/-- In finite dimension, the convex hull of a compact set is closed. -/
theorem isClosed_convexHull_of_isCompact
    [FiniteDimensional ℝ E] {s : Set E} (hcompact : IsCompact s) :
    IsClosed (convexHull ℝ s) :=
  (isCompact_convexHull_of_isCompact (E := E) hcompact).isClosed

omit [CompleteSpace E] in
/-- For compact `s` in finite dimension, Rockafellar's
`conv (closure exposedPoints)` set is compact. -/
theorem isCompact_convexHull_closure_mathlib_exposedPoints
    [FiniteDimensional ℝ E] {s : Set E} (hcompact : IsCompact s) :
    IsCompact (convexHull ℝ (closure (Set.exposedPoints ℝ s))) :=
  isCompact_convexHull_of_isCompact (E := E)
    (isCompact_closure_mathlib_exposedPoints (E := E) hcompact)

omit [CompleteSpace E] in
/-- For compact `s` in finite dimension, Rockafellar's
`conv (closure exposedPoints)` set is closed. -/
theorem isClosed_convexHull_closure_mathlib_exposedPoints
    [FiniteDimensional ℝ E] {s : Set E} (hcompact : IsCompact s) :
    IsClosed (convexHull ℝ (closure (Set.exposedPoints ℝ s))) :=
  (isCompact_convexHull_closure_mathlib_exposedPoints (E := E) hcompact).isClosed

omit [CompleteSpace E] in
/-- Extreme points remain in the generating set when they lie in a convex hull inside the ambient
convex set.

This is the compact-convex corollary used in Rockafellar's proof of Straszewicz's theorem: if
`x` is extreme in `C`, `A ⊆ C`, and `x ∈ conv A`, then `x ∈ A`. The proof is just extremeness
inherited by the smaller convex hull, followed by Mathlib's
`extremePoints_convexHull_subset`. -/
theorem mem_of_mem_extremePoints_of_mem_convexHull_subset
    {C A : Set E} {x : E}
    (hx : x ∈ C.extremePoints ℝ)
    (hconvC : Convex ℝ C)
    (hAC : A ⊆ C)
    (hxconv : x ∈ convexHull ℝ A) :
    x ∈ A := by
  have hsingleton_extreme_C : IsExtreme ℝ C ({x} : Set E) :=
    isExtreme_singleton.mpr hx
  have hconv_subset_C : convexHull ℝ A ⊆ C :=
    convexHull_min hAC hconvC
  have hsingleton_extreme_hull : IsExtreme ℝ (convexHull ℝ A) ({x} : Set E) :=
    hsingleton_extreme_C.mono hconv_subset_C (by simpa [Set.singleton_subset_iff])
  exact extremePoints_convexHull_subset (hsingleton_extreme_hull.mem_extremePoints)

omit [CompleteSpace E] in
/-- Contrapositive form of `mem_of_mem_extremePoints_of_mem_convexHull_subset`.

In Rockafellar's Straszewicz proof this is applied with `A = closure S`, where `S` is the exposed
point set: if the extreme point `x` is not in `closure S`, then it cannot lie in
`conv (closure S)`. -/
theorem notMem_convexHull_of_mem_extremePoints_of_notMem_subset
    {C A : Set E} {x : E}
    (hx : x ∈ C.extremePoints ℝ)
    (hconvC : Convex ℝ C)
    (hAC : A ⊆ C)
    (hxA : x ∉ A) :
    x ∉ convexHull ℝ A := by
  intro hxconv
  exact hxA (mem_of_mem_extremePoints_of_mem_convexHull_subset hx hconvC hAC hxconv)

omit [CompleteSpace E] in
/-- Rockafellar's `C₀ = conv (closure S)` exclusion, specialized to exposed points.

If `x` is an extreme point of a closed convex set `s` but is not in the closure of the exposed
points of `s`, then `x` is not in the convex hull of that closure. This is the step in the
Straszewicz proof immediately before applying Hahn-Banach separation. -/
theorem notMem_convexHull_closure_mathlib_exposedPoints_of_mem_extremePoints_of_notMem_closure
    {s : Set E} {x : E}
    (hclosed : IsClosed s)
    (hconv : Convex ℝ s)
    (hx : x ∈ s.extremePoints ℝ)
    (hxnot : x ∉ closure (Set.exposedPoints ℝ s)) :
    x ∉ convexHull ℝ (closure (Set.exposedPoints ℝ s)) := by
  refine notMem_convexHull_of_mem_extremePoints_of_notMem_subset hx hconv ?_ hxnot
  exact closure_minimal _root_.exposedPoints_subset hclosed

omit [CompleteSpace E] in
/-- Compact version of
`notMem_convexHull_closure_mathlib_exposedPoints_of_mem_extremePoints_of_notMem_closure`. -/
theorem notMem_convexHull_closure_mathlib_exposedPoints_of_isCompact
    {s : Set E} {x : E}
    (hcompact : IsCompact s)
    (hconv : Convex ℝ s)
    (hx : x ∈ s.extremePoints ℝ)
    (hxnot : x ∉ closure (Set.exposedPoints ℝ s)) :
    x ∉ convexHull ℝ (closure (Set.exposedPoints ℝ s)) :=
  notMem_convexHull_closure_mathlib_exposedPoints_of_mem_extremePoints_of_notMem_closure
    hcompact.isClosed hconv hx hxnot

omit [CompleteSpace E] in
/-- Hahn-Banach separation in the exact compact Straszewicz setup.

If an extreme point of a compact convex set is not in the closure of the exposed points, then it is
strictly separated from `conv (closure exposedPoints)`. This is the separation step in
Rockafellar's proof, with the closedness supplied by finite-dimensional compact convex-hull
compactness rather than left as an assumption. -/
theorem exists_strict_separating_dual_convexHull_closure_mathlib_exposedPoints
    [FiniteDimensional ℝ E] {s : Set E} {x : E}
    (hcompact : IsCompact s) (hconv : Convex ℝ s)
    (hx : x ∈ s.extremePoints ℝ)
    (hxnot : x ∉ closure (Set.exposedPoints ℝ s)) :
    ∃ (l : StrongDual ℝ E) (u : ℝ),
      (∀ a ∈ convexHull ℝ (closure (Set.exposedPoints ℝ s)), l a < u) ∧ u < l x := by
  have hnot_conv :
      x ∉ convexHull ℝ (closure (Set.exposedPoints ℝ s)) :=
    notMem_convexHull_closure_mathlib_exposedPoints_of_isCompact hcompact hconv hx hxnot
  exact geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (closure (Set.exposedPoints ℝ s)))
    (isClosed_convexHull_closure_mathlib_exposedPoints (E := E) hcompact)
    hnot_conv

omit [CompleteSpace E] in
/-- The abstract exposed-point reduction behind Rockafellar 25.6.

If all points of `s` are in the closed convex hull of the exposed points of `s`, and every exposed
point of `s` belongs to a closed convex set `C`, then all points of `s` belong to `C`.

For the subgradient cluster-density theorem, `s` is the subdifferential at a fixed point and
`C` is the closed convex hull of nearby gradient cluster values. Rockafellar's closed-convex-set
structure theorem and Straszewicz's theorem supply the first hypothesis; the exposed-point
outer-semicontinuity argument supplies the second. -/
theorem subset_of_subset_closure_convexHull_exposedPoints_of_exposed_subset_closed_convex
    {s C : Set E}
    (hrepr : ∀ ⦃p : E⦄, p ∈ s → p ∈ closure (convexHull ℝ (exposedPoints s)))
    (hexposedC : exposedPoints s ⊆ C) (hclosedC : IsClosed C) (hconvC : Convex ℝ C) :
    s ⊆ C := by
  intro p hp
  exact
    (closure_convexHull_subset_of_subset_closed_convex hexposedC hclosedC hconvC)
      (hrepr hp)

end AleksandrovDifferentiability
