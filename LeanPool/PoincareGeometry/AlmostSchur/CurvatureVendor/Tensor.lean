/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

/- Adapted from Arthur Freitas Ramos's committed contracted-bianchi formalization.
Source commit: 12cebb809524d0cd185c6cd7bcb5b73d3562bce1
Source blob: 4b887b01c3d90ef1a2b645610f281829c12808a9
Source path: contracted-bianchi/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean
See PROVENANCE.json for the exact extraction and local changes. -/

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Raw
public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.MetricPredicate
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Tensorial curvature

This file packages the raw curvature commutator into a fibrewise multilinear map
by evaluating it on canonical smooth extensions of fibre vectors.

The smooth extensions are built from `extend` sections multiplied by a fixed
smooth bump function chosen inside the base set of `trivializationAt`. This
keeps the construction linear in the fibre input while ensuring the sections are
globally smooth enough for repeated covariant differentiation.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V I]

namespace CovariantDerivative
local notation "TM" => (TangentSpace I : M → Type _)

section SmoothExtend

noncomputable def smoothExtendBumpData (x : M) :
    {φ : SmoothBumpFunction I x // tsupport φ ⊆ (trivializationAt F V x).baseSet} := by
  classical
  let t := trivializationAt F V x
  have ht : t.baseSet ∈ nhds x := by
    exact t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V x)
  have hφ :
      ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ t.baseSet :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp ht
  exact ⟨Classical.choose hφ, (Classical.choose_spec hφ).2⟩

noncomputable def smoothExtendBump (x : M) : SmoothBumpFunction I x :=
  (smoothExtendBumpData (I := I) (F := F) (V := V) x).1

lemma tsupport_smoothExtendBump_subset (x : M) :
    tsupport (smoothExtendBump (I := I) (F := F) (V := V) x) ⊆
      (trivializationAt F V x).baseSet :=
  (smoothExtendBumpData (I := I) (F := F) (V := V) x).2

private lemma smoothBump_eq_zero_of_not_mem
    {x y : M} (φ : SmoothBumpFunction I x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet)
    (hy : y ∉ (trivializationAt F V x).baseSet) : (φ : M → ℝ) y = 0 := by
  by_contra hφ
  exact hy (hφsupp (subset_closure hφ))

lemma contMDiffOn_extend_baseSet_two {x : M} (v : V x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (extend F v)) (trivializationAt F V x).baseSet := by
  let t := trivializationAt F V x
  suffices ContMDiffOn I 𝓘(ℝ, F) 2 (fun y ↦ (t ⟨y, extend F v y⟩).2) t.baseSet by
    intro y hy
    rw [t.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w : F := (t ⟨x, v⟩).2
  have hw : ContMDiffOn I 𝓘(ℝ, F) 2 (fun _y ↦ w) t.baseSet := contMDiffOn_const
  exact hw.congr (fun y hy ↦ by simp [extend, t, w, hy])

lemma contMDiffOn_extend_baseSet_one {x : M} (v : V x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) 1 (T% (extend F v)) (trivializationAt F V x).baseSet :=
  (contMDiffOn_extend_baseSet_two (I := I) (F := F) (V := V) v).of_le (by simp)

lemma extend_add_of_mem {x : M} (v w : V x) {y : M}
    (hy : y ∈ (trivializationAt F V x).baseSet) :
    extend F (v + w) y = extend F v y + extend F w y := by
  let t := trivializationAt F V x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  change t.symm y ((t ⟨x, v + w⟩).2) =
      t.symm y ((t ⟨x, v⟩).2) + t.symm y ((t ⟨x, w⟩).2)
  rw [← t.symmₗ_apply (R := ℝ) hy, ← t.symmₗ_apply (R := ℝ) hy,
    ← t.symmₗ_apply (R := ℝ) hy]
  rw [show (t ⟨x, v + w⟩).2 = (t ⟨x, v⟩).2 + (t ⟨x, w⟩).2 by
    simpa [t.coe_linearMapAt_of_mem hx] using (t.linearMapAt ℝ x).map_add v w]
  exact (t.symmₗ ℝ y).map_add _ _

lemma extend_smul_of_mem {x : M} (c : ℝ) (v : V x) {y : M}
    (hy : y ∈ (trivializationAt F V x).baseSet) :
    extend F (c • v) y = c • extend F v y := by
  let t := trivializationAt F V x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  change t.symm y ((t ⟨x, c • v⟩).2) = c • t.symm y ((t ⟨x, v⟩).2)
  rw [← t.symmₗ_apply (R := ℝ) hy, ← t.symmₗ_apply (R := ℝ) hy]
  have hcv : t.linearMapAt ℝ x (c • v) = (t ⟨x, c • v⟩).2 := by
    simpa using congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hx) (c • v)
  have hv : t.linearMapAt ℝ x v = (t ⟨x, v⟩).2 := by
    simpa using congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hx) v
  rw [← hcv, (t.linearMapAt ℝ x).map_smul, hv]
  exact (t.symmₗ ℝ y).map_smul c _

/-- A canonical smooth global extension of a fibre vector, linear in the fibre input. -/
noncomputable def smoothExtend
    (I : ModelWithCorners ℝ E H) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle 2 F V I]
    (x : M) (v : V x) : Π y : M, V y :=
  ((smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) • extend F v)

/-- A smooth extension built from an explicitly supplied bump function.  This is useful when a
later argument needs a bump with support contained in an additional neighborhood. -/
noncomputable def smoothExtendWithBump
    (x : M) (φ : SmoothBumpFunction I x) (v : V x) : Π y : M, V y :=
  ((φ : M → ℝ) • extend F v)

lemma smoothExtend_apply (x : M) (v : V x) :
    smoothExtend (I := I) (F := F) (V := V) x v x = v := by
  simp [smoothExtend]

lemma smoothExtendWithBump_apply (x : M) (φ : SmoothBumpFunction I x) (v : V x) :
    smoothExtendWithBump (I := I) (F := F) (V := V) x φ v x = v := by
  simp [smoothExtendWithBump]

lemma smoothExtend_eventuallyEq_extend (x : M) (v : V x) :
    ∀ᶠ y in nhds x, smoothExtend (I := I) (F := F) (V := V) x v y = extend F v y := by
  have hφ :
      (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) =ᶠ[nhds x] 1 :=
    (smoothExtendBump (I := I) (F := F) (V := V) x).eventuallyEq_one
  filter_upwards [hφ] with y hy
  simp [smoothExtend, hy]

lemma smoothExtendWithBump_eventuallyEq_extend
    (x : M) (φ : SmoothBumpFunction I x) (v : V x) :
    ∀ᶠ y in nhds x,
      smoothExtendWithBump (I := I) (F := F) (V := V) x φ v y = extend F v y := by
  have hφ : (φ : M → ℝ) =ᶠ[nhds x] 1 := φ.eventuallyEq_one
  filter_upwards [hφ] with y hy
  simp [smoothExtendWithBump, hy]

lemma smoothExtendWithBump_eventuallyEq_smoothExtend
    (x : M) (φ : SmoothBumpFunction I x) (v : V x) :
    ∀ᶠ y in nhds x,
      smoothExtendWithBump (I := I) (F := F) (V := V) x φ v y =
        smoothExtend (I := I) (F := F) (V := V) x v y := by
  filter_upwards [
      smoothExtendWithBump_eventuallyEq_extend (I := I) (F := F) (V := V) x φ v,
      smoothExtend_eventuallyEq_extend (I := I) (F := F) (V := V) x v] with y hφ hsmooth
  exact hφ.trans hsmooth.symm

lemma extend_trivializationAt_localFrame_apply_of_mem_baseSet
    {ι : Type*} (b : Module.Basis ι ℝ F) (x : M) {y : M}
    (hy : y ∈ (trivializationAt F V x).baseSet) (i : ι) :
    extend F ((trivializationAt F V x).localFrame b i x) y =
      (trivializationAt F V x).localFrame b i y := by
  let e := trivializationAt F V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
  rw [e.localFrame_apply_of_mem_baseSet (b := b) hy]
  simp [extend, Bundle.Trivialization.basisAt, e, hx, hy]

lemma smoothExtend_trivializationAt_localFrame_eventuallyEq
    {ι : Type*} (b : Module.Basis ι ℝ F) (x : M) (i : ι) :
    ∀ᶠ y in nhds x,
      smoothExtend (I := I) (F := F) (V := V) x
          ((trivializationAt F V x).localFrame b i x) y =
        (trivializationAt F V x).localFrame b i y := by
  let e := trivializationAt F V x
  have hbase : ∀ᶠ y in nhds x, y ∈ e.baseSet :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V x)
  filter_upwards [
      smoothExtend_eventuallyEq_extend (I := I) (F := F) (V := V) x
        ((trivializationAt F V x).localFrame b i x),
      hbase] with y hsmooth hy
  rw [hsmooth]
  exact extend_trivializationAt_localFrame_apply_of_mem_baseSet
    (F := F) (V := V) b x hy i

lemma eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F)
    (σ : Π x : M, V x) (x : M) :
    ∀ᶠ y in nhds x,
      σ y =
        ∑ i : ι,
          ((trivializationAt F V x).localFrameCoeff I b i y (σ y)) •
            smoothExtend (I := I) (F := F) (V := V) x
              ((trivializationAt F V x).localFrame b i x) y := by
  classical
  let e := trivializationAt F V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  have hsum :
      ∀ᶠ y in nhds x,
        σ y = ∑ i : ι, e.localFrameCoeff I b i y (σ y) • e.localFrame b i y := by
    simpa [e] using
      e.eventually_eq_localFrame_sum_coeff_smul (I := I) (b := b) (s := σ) hx
  have hframes :
      ∀ᶠ y in nhds x,
        ∀ i : ι,
          smoothExtend (I := I) (F := F) (V := V) x (e.localFrame b i x) y =
            e.localFrame b i y := by
    rw [Filter.eventually_all]
    intro i
    simpa [e] using smoothExtend_trivializationAt_localFrame_eventuallyEq
      (I := I) (F := F) (V := V) b x i
  filter_upwards [hsum, hframes] with y hsumy hframey
  calc
    σ y = ∑ i : ι, e.localFrameCoeff I b i y (σ y) • e.localFrame b i y := hsumy
    _ = ∑ i : ι,
          e.localFrameCoeff I b i y (σ y) •
            smoothExtend (I := I) (F := F) (V := V) x (e.localFrame b i x) y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hframey i]
    _ = ∑ i : ι,
          ((trivializationAt F V x).localFrameCoeff I b i y (σ y)) •
            smoothExtend (I := I) (F := F) (V := V) x
              ((trivializationAt F V x).localFrame b i x) y := by
          rfl

lemma smoothExtend_add (x : M) (v w : V x) :
    smoothExtend (I := I) (F := F) (V := V) x (v + w) =
      smoothExtend (I := I) (F := F) (V := V) x v +
        smoothExtend (I := I) (F := F) (V := V) x w := by
  funext y
  by_cases hy : y ∈ (trivializationAt F V x).baseSet
  · simp only [smoothExtend, Pi.add_apply]
    change (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) y •
        extend F (v + w) y =
      (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) y • extend F v y +
        (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) y • extend F w y
    rw [extend_add_of_mem (F := F) (V := V) v w hy]
    exact smul_add _ _ _
  · have hφ := smoothBump_eq_zero_of_not_mem
      (I := I) (F := F) (V := V)
      (smoothExtendBump (I := I) (F := F) (V := V) x)
      (tsupport_smoothExtendBump_subset (I := I) (F := F) (V := V) x) hy
    simp [smoothExtend, hφ]

lemma smoothExtend_smul (x : M) (c : ℝ) (v : V x) :
    smoothExtend (I := I) (F := F) (V := V) x (c • v) =
      c • smoothExtend (I := I) (F := F) (V := V) x v := by
  funext y
  by_cases hy : y ∈ (trivializationAt F V x).baseSet
  · simp only [smoothExtend, Pi.smul_apply]
    change (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) y •
        extend F (c • v) y =
      c • ((smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) y • extend F v y)
    rw [extend_smul_of_mem (F := F) (V := V) c v hy]
    simp [smul_smul, mul_comm]
  · have hφ := smoothBump_eq_zero_of_not_mem
      (I := I) (F := F) (V := V)
      (smoothExtendBump (I := I) (F := F) (V := V) x)
      (tsupport_smoothExtendBump_subset (I := I) (F := F) (V := V) x) hy
    simp [smoothExtend, hφ]

lemma smoothExtendWithBump_add
    (x : M) (φ : SmoothBumpFunction I x) (v w : V x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet) :
    smoothExtendWithBump (I := I) (F := F) (V := V) x φ (v + w) =
      smoothExtendWithBump (I := I) (F := F) (V := V) x φ v +
        smoothExtendWithBump (I := I) (F := F) (V := V) x φ w := by
  funext y
  by_cases hy : y ∈ (trivializationAt F V x).baseSet
  · simp only [smoothExtendWithBump, Pi.add_apply]
    change (φ : M → ℝ) y • extend F (v + w) y =
      (φ : M → ℝ) y • extend F v y + (φ : M → ℝ) y • extend F w y
    rw [extend_add_of_mem (F := F) (V := V) v w hy]
    exact smul_add _ _ _
  · have hφ := smoothBump_eq_zero_of_not_mem (I := I) (F := F) (V := V) φ hφsupp hy
    simp [smoothExtendWithBump, hφ]

lemma smoothExtendWithBump_smul
    (x : M) (φ : SmoothBumpFunction I x) (c : ℝ) (v : V x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet) :
    smoothExtendWithBump (I := I) (F := F) (V := V) x φ (c • v) =
      c • smoothExtendWithBump (I := I) (F := F) (V := V) x φ v := by
  funext y
  by_cases hy : y ∈ (trivializationAt F V x).baseSet
  · simp only [smoothExtendWithBump, Pi.smul_apply]
    change (φ : M → ℝ) y • extend F (c • v) y =
      c • ((φ : M → ℝ) y • extend F v y)
    rw [extend_smul_of_mem (F := F) (V := V) c v hy]
    simp [smul_smul, mul_comm]
  · have hφ := smoothBump_eq_zero_of_not_mem (I := I) (F := F) (V := V) φ hφsupp hy
    simp [smoothExtendWithBump, hφ]

lemma smoothExtend_contMDiff_two (x : M) (v : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦
        TotalSpace.mk' F y (smoothExtend (I := I) (F := F) (V := V) x v y)) := by
  let φ : SmoothBumpFunction I x := smoothExtendBump (I := I) (F := F) (V := V) x
  have hφ : ContMDiff I 𝓘(ℝ) 2 (φ : M → ℝ) := by
    have hφω : ContMDiff I 𝓘(ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (φ : M → ℝ) := φ.contMDiff
    have hle : (2 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hφω.of_le hle
  have hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (extend F v))
      (trivializationAt F V x).baseSet :=
    contMDiffOn_extend_baseSet_two (I := I) (F := F) (V := V) v
  simpa [smoothExtend] using
    ContMDiffOn.smul_section_of_tsupport
      (u := (trivializationAt F V x).baseSet)
      (n := 2) (ψ := (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ))
      hφ.contMDiffOn (trivializationAt F V x).open_baseSet
      (tsupport_smoothExtendBump_subset (I := I) (F := F) (V := V) x) hv

lemma smoothExtendWithBump_contMDiff_two_of_tsupport_subset
    (x : M) (φ : SmoothBumpFunction I x) (v : V x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y
        (smoothExtendWithBump (I := I) (F := F) (V := V) x φ v y)) := by
  have hφ : ContMDiff I 𝓘(ℝ) 2 (φ : M → ℝ) := by
    have hφω : ContMDiff I 𝓘(ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (φ : M → ℝ) := φ.contMDiff
    have hle : (2 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hφω.of_le hle
  have hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (extend F v))
      (trivializationAt F V x).baseSet :=
    contMDiffOn_extend_baseSet_two (I := I) (F := F) (V := V) v
  simpa [smoothExtendWithBump] using
    ContMDiffOn.smul_section_of_tsupport
      (u := (trivializationAt F V x).baseSet)
      (n := 2) (ψ := (φ : M → ℝ))
      hφ.contMDiffOn (trivializationAt F V x).open_baseSet hφsupp hv

lemma smoothExtend_localFrameCoeff_contMDiff_two
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F)
    (x : M) (w : V x) (i : ι) :
    ContMDiff I 𝓘(ℝ) 2
      (fun y ↦
        (trivializationAt F V x).localFrameCoeff I b i y
          (smoothExtend (I := I) (F := F) (V := V) x w y)) := by
  letI := b.finiteDimensional_of_finite
  let e := trivializationAt F V x
  let φ : SmoothBumpFunction I x := smoothExtendBump (I := I) (F := F) (V := V) x
  have hbase :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y
          (smoothExtend (I := I) (F := F) (V := V) x w y)) e.baseSet := by
    have hs :
        ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2
          (fun y ↦ TotalSpace.mk' F y
            (smoothExtend (I := I) (F := F) (V := V) x w y)) e.baseSet :=
      (smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w).contMDiffOn
    simpa [e] using
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        (t := e.baseSet) (k := (2 : WithTop ℕ∞))
        e.open_baseSet (subset_refl _) hs i
  have hcompl :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y
          (smoothExtend (I := I) (F := F) (V := V) x w y)) (tsupport φ)ᶜ := by
    have hzero :
        ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) (tsupport φ)ᶜ :=
      contMDiff_const.contMDiffOn
    refine hzero.congr ?_
    intro y hy
    have hφy : (φ : M → ℝ) y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [smoothExtend, φ, hφy]
  have hcover : e.baseSet ∪ (tsupport φ)ᶜ = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ e.baseSet
    · exact Or.inl hy
    · exact Or.inr fun hysupp ↦
        hy (tsupport_smoothExtendBump_subset (I := I) (F := F) (V := V) x hysupp)
  have hglobal :=
    contMDiff_of_contMDiffOn_union_of_isOpen hbase hcompl hcover e.open_baseSet
      (isOpen_compl_iff.mpr (isClosed_tsupport φ))
  simpa [e] using hglobal

lemma smoothExtend_contMDiff_one (x : M) (v : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 1
      (fun y ↦
        TotalSpace.mk' F y (smoothExtend (I := I) (F := F) (V := V) x v y)) :=
  (smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x v).of_le (by simp)

lemma smoothExtendWithBump_contMDiff_one_of_tsupport_subset
    (x : M) (φ : SmoothBumpFunction I x) (v : V x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 1
      (fun y ↦ TotalSpace.mk' F y
        (smoothExtendWithBump (I := I) (F := F) (V := V) x φ v y)) :=
  (smoothExtendWithBump_contMDiff_two_of_tsupport_subset
    (I := I) (F := F) (V := V) x φ v hφsupp).of_le (by simp)

end SmoothExtend

private lemma contMDiff_extDerivFun_apply
    {f : M → ℝ} {X : Π x : M, TM x}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y))) :
    ContMDiff I 𝓘(ℝ) 1 (fun y ↦ mvfderiv (I := I) f y (X y)) := by
  have htf : ContMDiff I.tangent 𝓘(ℝ).tangent 1 (tangentMap I 𝓘(ℝ) f) :=
    hf.contMDiff_tangentMap (m := 1) (by norm_num)
  have hcomp : ContMDiff I 𝓘(ℝ).tangent 1
      (fun y ↦ tangentMap I 𝓘(ℝ) f (TotalSpace.mk' E y (X y))) :=
    htf.comp hX
  have hsnd : ContMDiff I 𝓘(ℝ) 1
      (fun y ↦ (tangentMap I 𝓘(ℝ) f (TotalSpace.mk' E y (X y))).2) :=
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp hcomp
  change ContMDiff I 𝓘(ℝ) 1
    (fun y ↦ (tangentMap I 𝓘(ℝ) f (TotalSpace.mk' E y (X y))).2)
  exact hsnd

private lemma mdiffAt_extDerivFun_apply
    {f : M → ℝ} {X : Π x : M, TM x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y))) :
    MDiffAt (fun y ↦ mvfderiv (I := I) f y (X y)) x :=
  ((contMDiff_extDerivFun_apply (I := I) (f := f) (X := X) hf hX) x).mdifferentiableAt
    one_ne_zero

private lemma extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin
    {g : M → ℝ} {X : Π x : M, TM x} {x : M} (hg : MDiffAt g x) :
    mvfderiv (I := I) g x (X x) =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x g) (Set.range I)
        ((extChartAt I x) x)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I)
          ((extChartAt I x) x)) := by
  have hmp :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I)
        ((extChartAt I x) x) = X x := by
    change ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm) (Set.range I)
      ((extChartAt I x) x)).inverse) (X ((extChartAt I x).symm ((extChartAt I x) x))) = X x
    have hx : (extChartAt I x).symm ((extChartAt I x) x) = x := by
      simp
    rw [hx]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (v := X x)
  rw [hmp]
  change (NormedSpace.fromTangentSpace (g x)) ((mfderiv% g x) (X x)) = _
  exact congrArg (fun L => (NormedSpace.fromTangentSpace (g x)) (L (X x))) hg.mfderiv

private lemma real_fderivWithin_eq
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {s : Set E} {x : E}
    (hf : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x = f' := hf.fderivWithin hs

private lemma extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin_of_mem
    {g : M → ℝ} {X : Π x : M, TM x} {x y : M}
    (hy : y ∈ (extChartAt I x).source) (hg : MDiffAt g y) :
    mvfderiv (I := I) g y (X y) =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x g) (Set.range I)
        ((extChartAt I x) y)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I)
          ((extChartAt I x) y)) := by
  let φ := extChartAt I x
  let z := φ y
  have hy_eq : φ.symm z = y := by
    simpa [φ, z] using PartialEquiv.left_inv φ hy
  have hz : z ∈ φ.target := by
    simpa [φ, z] using PartialEquiv.map_source φ hy
  have hz_range : z ∈ Set.range I := by
    simpa [φ, z] using extChartAt_target_subset_range x hz
  have hg' : HasMFDerivAt I 𝓘(ℝ) g (φ.symm z) (mfderiv% g y) := by
    rw [hy_eq]
    exact hg.hasMFDerivAt
  have hcomp :
      HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ) (g ∘ φ.symm) (Set.range I) z
        ((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z)) := by
    exact HasMFDerivAt.comp_hasMFDerivWithinAt
      (f := φ.symm) (s := Set.range I) (x := z) hg'
      (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt
  have hFD : HasFDerivWithinAt (g ∘ φ.symm)
      (((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z)) : E →L[ℝ] ℝ)
      (Set.range I) z := hcomp.hasFDerivWithinAt
  have hderiv :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x g) (Set.range I) z =
        (((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z)) : E →L[ℝ] ℝ) := by
    change fderivWithin ℝ (g ∘ φ.symm) (Set.range I) z = _
    exact real_fderivWithin_eq hFD (I.uniqueDiffOn.uniqueDiffWithinAt hz_range)
  have hmp :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (Set.range I) z =
        (mfderiv[Set.range I] φ.symm z).inverse (X y) := by
    change (mfderiv[Set.range I] φ.symm z).inverse (X (φ.symm z)) =
      (mfderiv[Set.range I] φ.symm z).inverse (X y)
    rw [hy_eq]
  rw [hderiv, hmp]
  change (mfderiv% g y) (X y) =
    (((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z))
      ((mfderiv[Set.range I] φ.symm z).inverse (X y)))
  rw [← hy_eq]
  rw [ContinuousLinearMap.comp_apply]
  rcases isInvertible_mfderivWithin_extChartAt_symm hz with ⟨e, he⟩
  rw [← he, ContinuousLinearMap.inverse_equiv]
  have hsymm : e.toContinuousLinearMap (e.symm (X (φ.symm z))) = X (φ.symm z) := by
    exact ContinuousLinearEquiv.apply_symm_apply e (X (φ.symm z))
  have hconv :
      (mfderiv% g (φ.symm z)) (X (φ.symm z)) =
        (mfderiv% g (φ.symm z)) (e.toContinuousLinearMap (e.symm (X (φ.symm z)))) := by
    exact congrArg (fun v => (mfderiv% g (φ.symm z)) v) hsymm.symm
  exact hconv

private lemma writtenInExtChartAt_extDerivFun_apply_eventuallyEq_fderivWithin
    {f : M → ℝ} {X : Π x : M, TM x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y))) :
    writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (X y))
      =ᶠ[nhdsWithin ((extChartAt I x) x) (Set.range I)]
        fun z ↦
          fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) z
            (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I) z) := by
  have hf₁ : MDiff f := fun z ↦ (hf z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
  let y := (extChartAt I x).symm z
  have hy : y ∈ (extChartAt I x).source := (extChartAt I x).map_target hz
  have hz_eq : (extChartAt I x) y = z := by
    simpa [y] using PartialEquiv.right_inv (extChartAt I x) hz
  calc
    writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (X y)) z
      = mvfderiv (I := I) f y (X y) := by
          rfl
    _ = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) ((extChartAt I x) y)
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I)
            ((extChartAt I x) y)) :=
        extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin_of_mem
          (I := I) (g := f) (X := X) (x := x) (y := y) hy (hf₁ y)
    _ = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) z
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I) z) := by
          rw [hz_eq]

/-- Scalar second derivatives commute up to the Lie bracket. -/
lemma extDerivFun_lieBracket_commutator
    {f : M → ℝ} {X Y : Π x : M, TM x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y))) :
    mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (Y y)) x (X x) -
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (X y)) x (Y x) -
      mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) = 0 := by
  let φ := extChartAt I x
  let z : E := φ x
  let F : E → ℝ := writtenInExtChartAt I 𝓘(ℝ) x f
  let X' : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (Set.range I)
  let Y' : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm Y (Set.range I)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    have hsmooth : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
      simpa [minSmoothness] using
        (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)
    exact IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞)) hsmooth
  have hz_range : z ∈ Set.range I := by
    simpa [φ, z] using (mem_range_self (I x) : I x ∈ Set.range I)
  have hz_closure : z ∈ closure (interior (Set.range I)) :=
    I.range_subset_closure_interior hz_range
  have hF :
      ContDiffWithinAt ℝ 2 F (Set.range I) z := by
    simpa [F, writtenInExtChartAt, φ, z] using (contMDiffAt_iff.mp (hf x)).2
  have hXmd : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  have hYmd : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  have hXdiff :
      DifferentiableWithinAt ℝ X' (Set.range I) z := by
    simpa [X', φ, z] using
      (MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
        (I := I) (s := Set.univ) (x := x) (V := X) (by
          change MDiffAt[Set.univ] (T% X) x
          exact hXmd))
  have hYdiff :
      DifferentiableWithinAt ℝ Y' (Set.range I) z := by
    simpa [Y', φ, z] using
      (MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
        (I := I) (s := Set.univ) (x := x) (V := Y) (by
          change MDiffAt[Set.univ] (T% Y) x
          exact hYmd))
  have hEqY :
      writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (Y y))
        =ᶠ[nhdsWithin z (Set.range I)] fun w ↦ fderivWithin ℝ F (Set.range I) w (Y' w) := by
    simpa [F, Y', φ, z] using
      (writtenInExtChartAt_extDerivFun_apply_eventuallyEq_fderivWithin
        (I := I) (f := f) (X := Y) (x := x) hf hY)
  have hEqX :
      writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (X y))
        =ᶠ[nhdsWithin z (Set.range I)] fun w ↦ fderivWithin ℝ F (Set.range I) w (X' w) := by
    simpa [F, X', φ, z] using
      (writtenInExtChartAt_extDerivFun_apply_eventuallyEq_fderivWithin
        (I := I) (f := f) (X := X) (x := x) hf hX)
  have hEqY' :
      fderivWithin ℝ
          (writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (Y y)))
          (Set.range I) z =
        fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (Y' w))
          (Set.range I) z :=
    hEqY.fderivWithin_eq_of_mem hz_range
  have hEqX' :
      fderivWithin ℝ
          (writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (X y)))
          (Set.range I) z =
        fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (X' w))
          (Set.range I) z := by
    exact hEqX.fderivWithin_eq_of_mem hz_range
  have hBracket :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (VectorField.mlieBracket I X Y)
        (Set.range I) z =
        VectorField.lieBracketWithin ℝ X' Y' (Set.range I) z := by
    have hpoint : φ.symm z = x := by
      simp [φ, z]
    have hφ :
        CMDiffAt[Set.range I] 2 φ.symm z := by
      simpa [φ, z] using
        (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target (I := I) x))
    simpa [X', Y', φ, z, VectorField.mlieBracketWithin_eq_lieBracketWithin] using
      (VectorField.mpullbackWithin_mlieBracketWithin
        (I := 𝓘(ℝ, E)) (I' := I) (f := φ.symm) (V := X) (W := Y)
        (x₀ := z) (s := Set.range I) (t := Set.univ)
        (by
          rw [hpoint]
          change MDiffAt[Set.univ] (T% X) x
          exact hXmd)
        (by
          rw [hpoint]
          change MDiffAt[Set.univ] (T% Y) x
          exact hYmd)
        I.uniqueMDiffOn hφ hz_range (by simp) (by simp) hz_closure)
  have hLie :
      fderivWithin ℝ F (Set.range I) z (VectorField.lieBracketWithin ℝ X' Y' (Set.range I) z) =
        fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (Y' w))
          (Set.range I) z (X' z) -
        fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (X' w))
          (Set.range I) z (Y' z) := by
    exact VectorField.fderivWithin_apply_lieBracket
      (f := F) (V := X') (W := Y') hF (by simp) I.uniqueDiffOn hz_closure hz_range
      hYdiff hXdiff
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hgX : MDiffAt (fun y ↦ mvfderiv (I := I) f y (X y)) x :=
    mdiffAt_extDerivFun_apply (I := I) (f := f) (X := X) hf hX
  have hgY : MDiffAt (fun y ↦ mvfderiv (I := I) f y (Y y)) x :=
    mdiffAt_extDerivFun_apply (I := I) (f := f) (X := Y) hf hY
  calc
    mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (Y y)) x (X x) -
        mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (X y)) x (Y x) -
        mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x)
      =
        fderivWithin ℝ
            (writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (Y y)))
            (Set.range I) z (X' z) -
          fderivWithin ℝ
              (writtenInExtChartAt I 𝓘(ℝ) x (fun y ↦ mvfderiv (I := I) f y (X y)))
              (Set.range I) z (Y' z) -
          fderivWithin ℝ F (Set.range I) z
            (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (VectorField.mlieBracket I X Y)
              (Set.range I) z) := by
          rw [extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin
                (I := I) (g := fun y ↦ mvfderiv (I := I) f y (Y y)) (X := X) hgY,
              extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin
                (I := I) (g := fun y ↦ mvfderiv (I := I) f y (X y)) (X := Y) hgX,
              extDerivFun_apply_eq_fderivWithin_writtenInExtChartAt_mpullbackWithin
                (I := I) (g := f) (X := VectorField.mlieBracket I X Y) hfx]
    _ =
        fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (Y' w))
            (Set.range I) z (X' z) -
          fderivWithin ℝ (fun w ↦ fderivWithin ℝ F (Set.range I) w (X' w))
            (Set.range I) z (Y' z) -
          fderivWithin ℝ F (Set.range I) z (VectorField.lieBracketWithin ℝ X' Y' (Set.range I) z) := by
          rw [hEqY', hEqX', hBracket]
    _ = 0 := by
      rw [hLie]
      abel_nf

section CurvatureTensor

variable (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]

private lemma mdifferentiableAt_along_of_contMDiff
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    MDiffAt (T% (cov.along X σ)) x := by
  exact ((cov.contMDiff_along (n := 1) hX hσ) x).mdifferentiableAt one_ne_zero

private lemma mdifferentiableAt_along_of_mdifferentiableAt
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : MDiffAt (T% X) x)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    MDiffAt (T% (cov.along X σ)) x := by
  let Hcov := (inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff
  have hCovSection :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
        (fun y ↦
          TotalSpace.mk' (E →L[ℝ] F)
            (E := fun z : M ↦ TangentSpace I z →L[ℝ] V z) y (cov σ y)) := by
    apply contMDiffOn_univ.mp
    exact Hcov.contMDiff (by
      apply contMDiffOn_univ.mpr
      convert hσ using 1 <;> norm_num)
  simpa [CovariantDerivative.along] using
    ((hCovSection x).mdifferentiableAt one_ne_zero).clm_bundle_apply hX
private lemma second_derivative_inner_of_metricCompatible
    [RiemannianBundle V] [IsContMDiffRiemannianBundle I 2 F V]
    (hmetric :
      ∀ {x : M} {σ τ : Π x : M, V x},
        MDiffAt (T% σ) x → MDiffAt (T% τ) x →
          ∀ u : TangentSpace I x,
            mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
              inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u))
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) x (X x) =
        (inner ℝ (cov.along X (cov.along Y σ) x) (τ x) +
          inner ℝ (cov.along Y σ x) (cov.along X τ x)) +
        (inner ℝ (cov.along X σ x) (cov.along Y τ x) +
          inner ℝ (σ x) (cov.along X (cov.along Y τ) x)) := by
  let f : M → ℝ := fun y ↦ inner ℝ (σ y) (τ y)
  have hσ₁ : ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ TotalSpace.mk' F y (σ y)) :=
    hσ.of_le (by norm_num)
  have hτ₁ : ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y ↦ TotalSpace.mk' F y (τ y)) :=
    hτ.of_le (by norm_num)
  have hσmd : MDiffAt (T% σ) x :=
    (hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hτmd : MDiffAt (T% τ) x :=
    (hτ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hmetric_along {x0 : M} {Z : Π x : M, TM x} {ρ υ : Π x : M, V x}
      (hρ : MDiffAt (T% ρ) x0) (hυ : MDiffAt (T% υ) x0) :
      mvfderiv (I := I) (fun y ↦ inner ℝ (ρ y) (υ y)) x0 (Z x0) =
        inner ℝ (cov.along Z ρ x0) (υ x0) +
          inner ℝ (ρ x0) (cov.along Z υ x0) := by
    simpa [CovariantDerivative.along] using hmetric (x := x0) hρ hυ (Z x0)
  have hYσ :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 1
        (fun y ↦ TotalSpace.mk' F y (cov.along Y σ y)) :=
    cov.contMDiff_along (n := 1) hY hσ
  have hYτ :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 1
        (fun y ↦ TotalSpace.mk' F y (cov.along Y τ y)) :=
    cov.contMDiff_along (n := 1) hY hτ
  have hYσmd : MDiffAt (T% (cov.along Y σ)) x :=
    cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYτmd : MDiffAt (T% (cov.along Y τ)) x :=
    cov.mdifferentiableAt_along_of_contMDiff hY hτ
  have hinnerYστ : MDiffAt
      (fun y ↦ inner ℝ (cov.along Y σ y) (τ y)) x := by
    have h :
        ContMDiff I 𝓘(ℝ) 1
          (fun y ↦ inner ℝ (cov.along Y σ y) (τ y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := F) (E := V) hYσ hτ₁
    exact (h x).mdifferentiableAt one_ne_zero
  have hinnerσYτ : MDiffAt
      (fun y ↦ inner ℝ (σ y) (cov.along Y τ y)) x := by
    have h :
        ContMDiff I 𝓘(ℝ) 1
          (fun y ↦ inner ℝ (σ y) (cov.along Y τ y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := F) (E := V) hσ₁ hYτ
    exact (h x).mdifferentiableAt one_ne_zero
  have hDY_fun :
      (fun y ↦ mvfderiv (I := I) f y (Y y)) =
        fun y ↦ inner ℝ (cov.along Y σ y) (τ y) +
          inner ℝ (σ y) (cov.along Y τ y) := by
    funext y
    have hσy : MDiffAt (T% σ) y :=
      (hσ y).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    have hτy : MDiffAt (T% τ) y :=
      (hτ y).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    simpa [f] using hmetric_along (x0 := y) (Z := Y) hσy hτy
  rw [hDY_fun]
  change mvfderiv (I := I)
      ((fun y ↦ inner ℝ (cov.along Y σ y) (τ y)) +
        fun y ↦ inner ℝ (σ y) (cov.along Y τ y)) x (X x) =
      (inner ℝ (cov.along X (cov.along Y σ) x) (τ x) +
        inner ℝ (cov.along Y σ x) (cov.along X τ x)) +
      (inner ℝ (cov.along X σ x) (cov.along Y τ x) +
        inner ℝ (σ x) (cov.along X (cov.along Y τ) x))
  rw [mvfderiv_add hinnerYστ hinnerσYτ]
  simp only [ContinuousLinearMap.add_apply]
  rw [hmetric_along (x0 := x) (Z := X) hYσmd hτmd,
    hmetric_along (x0 := x) (Z := X) hσmd hYτmd]

/-- Metric compatibility makes the raw curvature commutator skew-adjoint in the bundle
inner product. -/
theorem curvatureAux_inner_add_eq_zero_of_metricCompatible
    [RiemannianBundle V] [IsContMDiffRiemannianBundle I 2 F V]
    (hmetric :
      ∀ {x : M} {σ τ : Π x : M, V x},
        MDiffAt (T% σ) x → MDiffAt (T% τ) x →
          ∀ u : TangentSpace I x,
            mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
              inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u))
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
    inner ℝ (cov.curvatureAux X Y σ x) (τ x) +
      inner ℝ (σ x) (cov.curvatureAux X Y τ x) = 0 := by
  let f : M → ℝ := fun y ↦ inner ℝ (σ y) (τ y)
  have hσmd : MDiffAt (T% σ) x :=
    (hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hτmd : MDiffAt (T% τ) x :=
    (hτ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hinnerσ : ContMDiff I 𝓘(ℝ) 2 f := by
    simpa [f] using
      (ContMDiff.inner_bundle (IM := I) (IB := I) (F := F) (E := V) hσ hτ)
  have hDXY :
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (Y y)) x (X x) =
        (inner ℝ (cov.along X (cov.along Y σ) x) (τ x) +
          inner ℝ (cov.along Y σ x) (cov.along X τ x)) +
        (inner ℝ (cov.along X σ x) (cov.along Y τ x) +
          inner ℝ (σ x) (cov.along X (cov.along Y τ) x)) :=
    cov.second_derivative_inner_of_metricCompatible hmetric (X := X) (Y := Y) hY hσ hτ
  have hDYX :
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (X y)) x (Y x) =
        (inner ℝ (cov.along Y (cov.along X σ) x) (τ x) +
          inner ℝ (cov.along X σ x) (cov.along Y τ x)) +
        (inner ℝ (cov.along Y σ x) (cov.along X τ x) +
          inner ℝ (σ x) (cov.along Y (cov.along X τ) x)) :=
    cov.second_derivative_inner_of_metricCompatible hmetric (X := Y) (Y := X) hX hσ hτ
  have hDbr :
      mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) =
        inner ℝ (cov.along (VectorField.mlieBracket I X Y) σ x) (τ x) +
          inner ℝ (σ x) (cov.along (VectorField.mlieBracket I X Y) τ x) := by
    simpa [f, CovariantDerivative.along] using
      hmetric (x := x) hσmd hτmd (VectorField.mlieBracket I X Y x)
  have hcomm :=
    extDerivFun_lieBracket_commutator (I := I) (f := f) (X := X) (Y := Y)
      (x := x) hinnerσ hX hY
  rw [hDXY, hDYX, hDbr] at hcomm
  abel_nf at hcomm
  simpa [CovariantDerivative.curvatureAux, sub_eq_add_neg, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, add_assoc, add_left_comm, add_comm] using hcomm

private lemma along_add_right_of_contMDiff
    {X : Π x : M, TM x} {σ τ : Π x : M, V x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
    cov.along X (σ + τ) = cov.along X σ + cov.along X τ := by
  funext z
  exact cov.along_add_right_apply (x := z) (X := X)
    ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
    ((hτ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))

private lemma along_const_smul_right_apply
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hσ : MDiffAt (T% σ) x) :
    cov.along X (c • σ) x = c • cov.along X σ x := by
  have hfun : (fun _ : M ↦ c) • σ = c • σ := by
    funext y
    rfl
  rw [← hfun]
  simpa [mvfderiv] using
    (cov.along_smul_right_apply (x := x) (X := X) (f := fun _ ↦ c)
      mdifferentiableAt_const hσ)

private lemma along_const_smul_right_of_contMDiff
    {X : Π x : M, TM x} {σ : Π x : M, V x} (c : ℝ)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.along X (c • σ) = c • cov.along X σ := by
  funext z
  exact cov.along_const_smul_right_apply (x := z) c
    ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))

private lemma curvatureAux_add_left_apply
    {X X' Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (X + X') Y σ x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X' Y σ x := by
  have hYX : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hY'X : MDiffAt (T% (cov.along X' σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX' hσ
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hX'x : MDiffAt (T% X') x := (hX' x).mdifferentiableAt one_ne_zero
  have h1 :
      cov.along (X + X') (cov.along Y σ) x =
        cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_add_left X X' (cov.along Y σ))
  have h2 :
      cov.along Y (cov.along (X + X') σ) x =
        cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x := by
    rw [cov.along_add_left]
    exact cov.along_add_right_apply (x := x) (X := Y) hYX hY'X
  have h3 :
      cov.along (VectorField.mlieBracket I (X + X') Y) σ x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X' Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_add_left hXx hX'x, map_add]
  calc
    cov.curvatureAux (X + X') Y σ x
        = cov.along (X + X') (cov.along Y σ) x -
            cov.along Y (cov.along (X + X') σ) x -
            cov.along (VectorField.mlieBracket I (X + X') Y) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X' Y) σ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X' (cov.along Y σ) x - cov.along Y (cov.along X' σ) x -
          cov.along (VectorField.mlieBracket I X' Y) σ x) := by
            simp [sub_eq_add_neg, smul_smul, neg_smul] <;> abel
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X' Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_left_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (c • X) Y σ x = c • cov.curvatureAux X Y σ x := by
  have hYX : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hXsmul : cov.along (c • X) σ = c • cov.along X σ := by
    have hfun : (fun _ : M ↦ c) • X = c • X := by
      funext y
      rfl
    rw [← hfun]
    exact cov.along_smul_left (f := fun _ ↦ c) X σ
  have h1 :
      cov.along (c • X) (cov.along Y σ) x = c • cov.along X (cov.along Y σ) x := by
    simp [CovariantDerivative.along, map_smul]
  have h2 :
      cov.along Y (cov.along (c • X) σ) x = c • cov.along Y (cov.along X σ) x := by
    rw [hXsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYX
  have h3 :
      cov.along (VectorField.mlieBracket I (c • X) Y) σ x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_const_smul_left hXx, map_smul]
  calc
    cov.curvatureAux (c • X) Y σ x
        = cov.along (c • X) (cov.along Y σ) x -
            cov.along Y (cov.along (c • X) σ) x -
            cov.along (VectorField.mlieBracket I (c • X) Y) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

lemma curvatureAux_smul_fun_left_apply
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : MDiffAt f x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (f • X) Y σ x = f x • cov.curvatureAux X Y σ x := by
  have hYX : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hXsmul : cov.along (f • X) σ = f • cov.along X σ := by
    simpa using (cov.along_smul_left f X σ)
  have h1 :
      cov.along (f • X) (cov.along Y σ) x = f x • cov.along X (cov.along Y σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_smul_left f X (cov.along Y σ))
  have h2 :
      cov.along Y (cov.along (f • X) σ) x =
        f x • cov.along Y (cov.along X σ) x +
          mvfderiv (I := I) f x (Y x) • cov.along X σ x := by
    rw [hXsmul]
    exact cov.along_smul_right_apply (x := x) (f := f) (X := Y) (σ := cov.along X σ) hf hYX
  have h3 :
      cov.along (VectorField.mlieBracket I (f • X) Y) σ x =
        -(mvfderiv (I := I) f x (Y x)) • cov.along X σ x +
          f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
    rw [CovariantDerivative.along, VectorField.mlieBracket_smul_left hf hXx, mvfderiv]
    simp [CovariantDerivative.along, map_add, map_smul]
  calc
    cov.curvatureAux (f • X) Y σ x
        = cov.along (f • X) (cov.along Y σ) x -
            cov.along Y (cov.along (f • X) σ) x -
            cov.along (VectorField.mlieBracket I (f • X) Y) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = f x • cov.along X (cov.along Y σ) x -
          (f x • cov.along Y (cov.along X σ) x +
            mvfderiv (I := I) f x (Y x) • cov.along X σ x) -
          (-(mvfderiv (I := I) f x (Y x)) • cov.along X σ x +
            f x • cov.along (VectorField.mlieBracket I X Y) σ x) := by
              rw [h1, h2, h3]
    _ = f x • cov.along X (cov.along Y σ) x -
          f x • cov.along Y (cov.along X σ) x -
          f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
            simp [sub_eq_add_neg, smul_smul, neg_smul] <;> abel
    _ = f x • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = f x • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_add_middle_apply
    {X Y Y' : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y' y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (Y + Y') σ x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X Y' σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hY'σ : MDiffAt (T% (cov.along Y' σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY' hσ
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hY'x : MDiffAt (T% Y') x := (hY' x).mdifferentiableAt one_ne_zero
  have h1 :
      cov.along X (cov.along (Y + Y') σ) x =
        cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x := by
    rw [cov.along_add_left]
    exact cov.along_add_right_apply (x := x) (X := X) hYσ hY'σ
  have h2 :
      cov.along (Y + Y') (cov.along X σ) x =
        cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_add_left Y Y' (cov.along X σ))
  have h3 :
      cov.along (VectorField.mlieBracket I X (Y + Y')) σ x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X Y') σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_add_right hYx hY'x, map_add]
  calc
    cov.curvatureAux X (Y + Y') σ x
        = cov.along X (cov.along (Y + Y') σ) x -
            cov.along (Y + Y') (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X (Y + Y')) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X Y') σ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X (cov.along Y' σ) x - cov.along Y' (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y') σ x) := by
            abel_nf
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X Y' σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_middle_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (c • Y) σ x = c • cov.curvatureAux X Y σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hYsmul : cov.along (c • Y) σ = c • cov.along Y σ := by
    have hfun : (fun _ : M ↦ c) • Y = c • Y := by
      funext y
      rfl
    rw [← hfun]
    exact cov.along_smul_left (f := fun _ ↦ c) Y σ
  have h1 :
      cov.along X (cov.along (c • Y) σ) x = c • cov.along X (cov.along Y σ) x := by
    rw [hYsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYσ
  have h2 :
      cov.along (c • Y) (cov.along X σ) x = c • cov.along Y (cov.along X σ) x := by
    simp [CovariantDerivative.along, map_smul]
  have h3 :
      cov.along (VectorField.mlieBracket I X (c • Y)) σ x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_const_smul_right hYx, map_smul]
  calc
    cov.curvatureAux X (c • Y) σ x
        = cov.along X (cov.along (c • Y) σ) x -
            cov.along (c • Y) (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X (c • Y)) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

lemma curvatureAux_smul_fun_middle_apply
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : MDiffAt f x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (f • Y) σ x = f x • cov.curvatureAux X Y σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hYsmul : cov.along (f • Y) σ = f • cov.along Y σ := by
    simpa using (cov.along_smul_left f Y σ)
  have h1 :
      cov.along X (cov.along (f • Y) σ) x =
        f x • cov.along X (cov.along Y σ) x +
          mvfderiv (I := I) f x (X x) • cov.along Y σ x := by
    rw [hYsmul]
    exact cov.along_smul_right_apply (x := x) (f := f) (X := X) (σ := cov.along Y σ) hf hYσ
  have h2 :
      cov.along (f • Y) (cov.along X σ) x = f x • cov.along Y (cov.along X σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_smul_left f Y (cov.along X σ))
  have h3 :
      cov.along (VectorField.mlieBracket I X (f • Y)) σ x =
        mvfderiv (I := I) f x (X x) • cov.along Y σ x +
          f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_smul_right hf hYx, mvfderiv,
      map_add, map_smul]
  calc
    cov.curvatureAux X (f • Y) σ x
        = cov.along X (cov.along (f • Y) σ) x -
            cov.along (f • Y) (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X (f • Y)) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (f x • cov.along X (cov.along Y σ) x +
            mvfderiv (I := I) f x (X x) • cov.along Y σ x) -
          f x • cov.along Y (cov.along X σ) x -
          (mvfderiv (I := I) f x (X x) • cov.along Y σ x +
            f x • cov.along (VectorField.mlieBracket I X Y) σ x) := by
              rw [h1, h2, h3]
    _ = f x • cov.along X (cov.along Y σ) x -
          f x • cov.along Y (cov.along X σ) x -
          f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
            simpa [sub_eq_add_neg, smul_smul, add_assoc, add_left_comm, add_comm]
    _ = f x • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = f x • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_add_right_apply
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
    cov.curvatureAux X Y (σ + τ) x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X Y τ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYτ : MDiffAt (T% (cov.along Y τ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hτ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXτ : MDiffAt (T% (cov.along X τ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hτ
  have hYadd : cov.along Y (σ + τ) = cov.along Y σ + cov.along Y τ :=
    cov.along_add_right_of_contMDiff hσ hτ
  have hXadd : cov.along X (σ + τ) = cov.along X σ + cov.along X τ :=
    cov.along_add_right_of_contMDiff hσ hτ
  have h1 :
      cov.along X (cov.along Y (σ + τ)) x =
        cov.along X (cov.along Y σ) x + cov.along X (cov.along Y τ) x := by
    rw [hYadd]
    exact cov.along_add_right_apply (x := x) (X := X) hYσ hYτ
  have h2 :
      cov.along Y (cov.along X (σ + τ)) x =
        cov.along Y (cov.along X σ) x + cov.along Y (cov.along X τ) x := by
    rw [hXadd]
    exact cov.along_add_right_apply (x := x) (X := Y) hXσ hXτ
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) (σ + τ) x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X Y) τ x := by
    exact cov.along_add_right_apply (x := x) (X := VectorField.mlieBracket I X Y)
      ((hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
      ((hτ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
  calc
    cov.curvatureAux X Y (σ + τ) x
        = cov.along X (cov.along Y (σ + τ)) x -
            cov.along Y (cov.along X (σ + τ)) x -
            cov.along (VectorField.mlieBracket I X Y) (σ + τ) x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X (cov.along Y τ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y (cov.along X τ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X Y) τ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X (cov.along Y τ) x - cov.along Y (cov.along X τ) x -
          cov.along (VectorField.mlieBracket I X Y) τ x) := by
            abel_nf
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X Y τ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_right_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X Y (c • σ) x = c • cov.curvatureAux X Y σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hYsmul : cov.along Y (c • σ) = c • cov.along Y σ :=
    cov.along_const_smul_right_of_contMDiff c hσ
  have hXsmul : cov.along X (c • σ) = c • cov.along X σ :=
    cov.along_const_smul_right_of_contMDiff c hσ
  have h1 :
      cov.along X (cov.along Y (c • σ)) x = c • cov.along X (cov.along Y σ) x := by
    rw [hYsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYσ
  have h2 :
      cov.along Y (cov.along X (c • σ)) x = c • cov.along Y (cov.along X σ) x := by
    rw [hXsmul]
    exact cov.along_const_smul_right_apply (x := x) c hXσ
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) (c • σ) x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    exact cov.along_const_smul_right_apply (x := x) c
      ((hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
  calc
    cov.curvatureAux X Y (c • σ) x
        = cov.along X (cov.along Y (c • σ)) x -
            cov.along Y (cov.along X (c • σ)) x -
            cov.along (VectorField.mlieBracket I X Y) (c • σ) x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

lemma curvatureAux_smul_fun_right_apply_of_commutator
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : MDiff f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hgX : MDiffAt (fun y ↦ mvfderiv (I := I) f y (X y)) x)
    (hgY : MDiffAt (fun y ↦ mvfderiv (I := I) f y (Y y)) x)
    (hcomm :
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (Y y)) x (X x) -
        mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (X y)) x (Y x) -
        mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) = 0) :
    cov.curvatureAux X Y (f • σ) x = f x • cov.curvatureAux X Y σ x := by
  let gX : M → ℝ := fun y ↦ mvfderiv (I := I) f y (X y)
  let gY : M → ℝ := fun y ↦ mvfderiv (I := I) f y (Y y)
  have hσx : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hYsmul : cov.along Y (f • σ) = f • cov.along Y σ + gY • σ := by
    funext z
    simpa [gY] using
      (cov.along_smul_right_apply (x := z) (f := f) (X := Y) (σ := σ)
        (hf z) ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)))
  have hXsmul : cov.along X (f • σ) = f • cov.along X σ + gX • σ := by
    funext z
    simpa [gX] using
      (cov.along_smul_right_apply (x := z) (f := f) (X := X) (σ := σ)
        (hf z) ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)))
  have h1 :
      cov.along X (cov.along Y (f • σ)) x =
        f x • cov.along X (cov.along Y σ) x +
          mvfderiv (I := I) f x (X x) • cov.along Y σ x +
          gY x • cov.along X σ x +
          mvfderiv (I := I) gY x (X x) • σ x := by
    rw [hYsmul]
    rw [cov.along_add_right_apply (x := x) (X := X)]
    · rw [cov.along_smul_right_apply (x := x) (f := f) (X := X) (σ := cov.along Y σ)
        (hf x) hYσ]
      rw [cov.along_smul_right_apply (x := x) (f := gY) (X := X) (σ := σ) hgY hσx]
      simp [add_assoc]
    · exact (hf x).smul_section hYσ
    · exact hgY.smul_section hσx
  have h2 :
      cov.along Y (cov.along X (f • σ)) x =
        f x • cov.along Y (cov.along X σ) x +
          mvfderiv (I := I) f x (Y x) • cov.along X σ x +
          gX x • cov.along Y σ x +
          mvfderiv (I := I) gX x (Y x) • σ x := by
    rw [hXsmul]
    rw [cov.along_add_right_apply (x := x) (X := Y)]
    · rw [cov.along_smul_right_apply (x := x) (f := f) (X := Y) (σ := cov.along X σ)
        (hf x) hXσ]
      rw [cov.along_smul_right_apply (x := x) (f := gX) (X := Y) (σ := σ) hgX hσx]
      simp [add_assoc]
    · exact (hf x).smul_section hXσ
    · exact hgX.smul_section hσx
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) (f • σ) x =
        f x • cov.along (VectorField.mlieBracket I X Y) σ x +
          mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) • σ x := by
    exact cov.along_smul_right_apply (x := x) (f := f) (X := VectorField.mlieBracket I X Y)
      (σ := σ) (hf x) hσx
  have hcomm' :
      mvfderiv (I := I) gY x (X x) -
        mvfderiv (I := I) gX x (Y x) -
        mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) = 0 := by
    simpa [gX, gY] using hcomm
  have hcommσ :
      mvfderiv (I := I) gY x (X x) • σ x -
        mvfderiv (I := I) gX x (Y x) • σ x -
        mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) • σ x = 0 := by
    have htmp := congrArg (fun r : ℝ ↦ r • σ x) hcomm'
    simpa [sub_smul] using htmp
  calc
    cov.curvatureAux X Y (f • σ) x
        = cov.along X (cov.along Y (f • σ)) x -
            cov.along Y (cov.along X (f • σ)) x -
            cov.along (VectorField.mlieBracket I X Y) (f • σ) x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (f x • cov.along X (cov.along Y σ) x +
            mvfderiv (I := I) f x (X x) • cov.along Y σ x +
            gY x • cov.along X σ x +
            mvfderiv (I := I) gY x (X x) • σ x) -
          (f x • cov.along Y (cov.along X σ) x +
            mvfderiv (I := I) f x (Y x) • cov.along X σ x +
            gX x • cov.along Y σ x +
            mvfderiv (I := I) gX x (Y x) • σ x) -
          (f x • cov.along (VectorField.mlieBracket I X Y) σ x +
            mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) • σ x) := by
              rw [h1, h2, h3]
    _ = f x • cov.along X (cov.along Y σ) x -
          f x • cov.along Y (cov.along X σ) x -
          f x • cov.along (VectorField.mlieBracket I X Y) σ x +
          (mvfderiv (I := I) gY x (X x) • σ x -
            mvfderiv (I := I) gX x (Y x) • σ x -
            mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) • σ x) := by
              dsimp [gX, gY]
              simp [sub_eq_add_neg, smul_smul, neg_smul] <;> abel
    _ = f x • cov.along X (cov.along Y σ) x -
          f x • cov.along Y (cov.along X σ) x -
          f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
              rw [hcommσ, add_zero]
    _ = f x • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = f x • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

lemma curvatureAux_smul_fun_right_apply_of_commutator_contMDiff
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hcomm :
      mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (Y y)) x (X x) -
        mvfderiv (I := I) (fun y ↦ mvfderiv (I := I) f y (X y)) x (Y x) -
        mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) = 0) :
    cov.curvatureAux X Y (f • σ) x = f x • cov.curvatureAux X Y σ x := by
  have hgX : MDiffAt (fun y ↦ mvfderiv (I := I) f y (X y)) x :=
    mdiffAt_extDerivFun_apply (I := I) (f := f) (X := X) hf hX
  have hgY : MDiffAt (fun y ↦ mvfderiv (I := I) f y (Y y)) x :=
    mdiffAt_extDerivFun_apply (I := I) (f := f) (X := Y) hf hY
  exact cov.curvatureAux_smul_fun_right_apply_of_commutator
    (fun z ↦ (hf z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
    hX hY hσ hgX hgY hcomm

lemma curvatureAux_smul_fun_right_apply
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X Y (f • σ) x = f x • cov.curvatureAux X Y σ x := by
  exact cov.curvatureAux_smul_fun_right_apply_of_commutator_contMDiff hf hX hY hσ
    (extDerivFun_lieBracket_commutator (I := I) (f := f) (X := X) (Y := Y) hf hX hY)

private theorem curvatureAux_tensorial_left
    {Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    TensorialAt I E (fun X ↦ cov.curvatureAux X Y σ x) x := by
  refine ⟨?_, ?_⟩
  · intro f X hf hX
    have hYX : MDiffAt (T% (cov.along X σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hX hσ
    have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
    have hXsmul : cov.along (f • X) σ = f • cov.along X σ := by
      simpa using (cov.along_smul_left f X σ)
    have h1 :
        cov.along (f • X) (cov.along Y σ) x = f x • cov.along X (cov.along Y σ) x := by
      simpa using congrArg (fun s => s x) (cov.along_smul_left f X (cov.along Y σ))
    have h2 :
        cov.along Y (cov.along (f • X) σ) x =
          f x • cov.along Y (cov.along X σ) x +
            mvfderiv (I := I) f x (Y x) • cov.along X σ x := by
      rw [hXsmul]
      exact cov.along_smul_right_apply (x := x) (f := f) (X := Y) (σ := cov.along X σ) hf hYX
    have h3 :
        cov.along (VectorField.mlieBracket I (f • X) Y) σ x =
          -(mvfderiv (I := I) f x (Y x)) • cov.along X σ x +
            f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
      rw [CovariantDerivative.along, VectorField.mlieBracket_smul_left hf hX, mvfderiv]
      simp [CovariantDerivative.along, map_add, map_smul]
    calc
      cov.curvatureAux (f • X) Y σ x
          = cov.along (f • X) (cov.along Y σ) x -
              cov.along Y (cov.along (f • X) σ) x -
              cov.along (VectorField.mlieBracket I (f • X) Y) σ x := by
                simp [CovariantDerivative.curvatureAux]
      _ = f x • cov.along X (cov.along Y σ) x -
            (f x • cov.along Y (cov.along X σ) x +
              mvfderiv (I := I) f x (Y x) • cov.along X σ x) -
            (-(mvfderiv (I := I) f x (Y x)) • cov.along X σ x +
              f x • cov.along (VectorField.mlieBracket I X Y) σ x) := by
                rw [h1, h2, h3]
      _ = f x • cov.along X (cov.along Y σ) x -
            f x • cov.along Y (cov.along X σ) x -
            f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
              simp [sub_eq_add_neg, smul_smul, neg_smul] <;> abel
      _ = f x • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X Y) σ x) := by
              rw [smul_sub, smul_sub]
      _ = f x • cov.curvatureAux X Y σ x := by
            simp [CovariantDerivative.curvatureAux]
  · intro X X' hX hX'
    have hYX : MDiffAt (T% (cov.along X σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hX hσ
    have hY'X : MDiffAt (T% (cov.along X' σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hX' hσ
    have h1 :
        cov.along (X + X') (cov.along Y σ) x =
          cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x := by
      simpa using congrArg (fun s => s x) (cov.along_add_left X X' (cov.along Y σ))
    have h2 :
        cov.along Y (cov.along (X + X') σ) x =
          cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x := by
      rw [cov.along_add_left]
      exact cov.along_add_right_apply (x := x) (X := Y) hYX hY'X
    have h3 :
        cov.along (VectorField.mlieBracket I (X + X') Y) σ x =
          cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X' Y) σ x := by
      simp [CovariantDerivative.along, VectorField.mlieBracket_add_left hX hX', map_add]
    calc
      cov.curvatureAux (X + X') Y σ x
          = cov.along (X + X') (cov.along Y σ) x -
              cov.along Y (cov.along (X + X') σ) x -
              cov.along (VectorField.mlieBracket I (X + X') Y) σ x := by
                simp [CovariantDerivative.curvatureAux]
      _ = (cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x) -
            (cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x) -
            (cov.along (VectorField.mlieBracket I X Y) σ x +
              cov.along (VectorField.mlieBracket I X' Y) σ x) := by
                rw [h1, h2, h3]
      _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X Y) σ x) +
          (cov.along X' (cov.along Y σ) x - cov.along Y (cov.along X' σ) x -
            cov.along (VectorField.mlieBracket I X' Y) σ x) := by
              abel_nf
      _ = cov.curvatureAux X Y σ x + cov.curvatureAux X' Y σ x := by
            simp [CovariantDerivative.curvatureAux]

private theorem curvatureAux_tensorial_middle
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    TensorialAt I E (fun Y ↦ cov.curvatureAux X Y σ x) x := by
  refine ⟨?_, ?_⟩
  · intro f Y hf hY
    have hYσ : MDiffAt (T% (cov.along Y σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hY hσ
    have hYsmul : cov.along (f • Y) σ = f • cov.along Y σ := by
      simpa using (cov.along_smul_left f Y σ)
    have h1 :
        cov.along X (cov.along (f • Y) σ) x =
          f x • cov.along X (cov.along Y σ) x +
            mvfderiv (I := I) f x (X x) • cov.along Y σ x := by
      rw [hYsmul]
      exact cov.along_smul_right_apply (x := x) (f := f) (X := X) (σ := cov.along Y σ) hf hYσ
    have h2 :
        cov.along (f • Y) (cov.along X σ) x = f x • cov.along Y (cov.along X σ) x := by
      simpa using congrArg (fun s => s x) (cov.along_smul_left f Y (cov.along X σ))
    have h3 :
        cov.along (VectorField.mlieBracket I X (f • Y)) σ x =
          mvfderiv (I := I) f x (X x) • cov.along Y σ x +
            f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
      simp [CovariantDerivative.along, VectorField.mlieBracket_smul_right hf hY, mvfderiv,
        map_add, map_smul]
    calc
      cov.curvatureAux X (f • Y) σ x
          = cov.along X (cov.along (f • Y) σ) x -
              cov.along (f • Y) (cov.along X σ) x -
              cov.along (VectorField.mlieBracket I X (f • Y)) σ x := by
                simp [CovariantDerivative.curvatureAux]
      _ = (f x • cov.along X (cov.along Y σ) x +
            mvfderiv (I := I) f x (X x) • cov.along Y σ x) -
            f x • cov.along Y (cov.along X σ) x -
            (mvfderiv (I := I) f x (X x) • cov.along Y σ x +
              f x • cov.along (VectorField.mlieBracket I X Y) σ x) := by
                rw [h1, h2, h3]
      _ = f x • cov.along X (cov.along Y σ) x -
            f x • cov.along Y (cov.along X σ) x -
            f x • cov.along (VectorField.mlieBracket I X Y) σ x := by
              simpa [sub_eq_add_neg, smul_smul, add_assoc, add_left_comm, add_comm]
      _ = f x • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X Y) σ x) := by
              rw [smul_sub, smul_sub]
      _ = f x • cov.curvatureAux X Y σ x := by
            simp [CovariantDerivative.curvatureAux]
  · intro Y Y' hY hY'
    have hYσ : MDiffAt (T% (cov.along Y σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hY hσ
    have hY'σ : MDiffAt (T% (cov.along Y' σ)) x :=
      cov.mdifferentiableAt_along_of_mdifferentiableAt hY' hσ
    have h1 :
        cov.along X (cov.along (Y + Y') σ) x =
          cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x := by
      rw [cov.along_add_left]
      exact cov.along_add_right_apply (x := x) (X := X) hYσ hY'σ
    have h2 :
        cov.along (Y + Y') (cov.along X σ) x =
          cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x := by
      simpa using congrArg (fun s => s x) (cov.along_add_left Y Y' (cov.along X σ))
    have h3 :
        cov.along (VectorField.mlieBracket I X (Y + Y')) σ x =
          cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X Y') σ x := by
      simp [CovariantDerivative.along, VectorField.mlieBracket_add_right hY hY', map_add]
    calc
      cov.curvatureAux X (Y + Y') σ x
          = cov.along X (cov.along (Y + Y') σ) x -
              cov.along (Y + Y') (cov.along X σ) x -
              cov.along (VectorField.mlieBracket I X (Y + Y')) σ x := by
                simp [CovariantDerivative.curvatureAux]
      _ = (cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x) -
            (cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x) -
            (cov.along (VectorField.mlieBracket I X Y) σ x +
              cov.along (VectorField.mlieBracket I X Y') σ x) := by
                rw [h1, h2, h3]
      _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X Y) σ x) +
          (cov.along X (cov.along Y' σ) x - cov.along Y' (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X Y') σ x) := by
              abel_nf
      _ = cov.curvatureAux X Y σ x + cov.curvatureAux X Y' σ x := by
            simp [CovariantDerivative.curvatureAux]

private lemma along_eventuallyEq_left_apply
    {X X' : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hXX' : X =ᶠ[nhds x] X') :
    cov.along X σ x = cov.along X' σ x := by
  simpa [CovariantDerivative.along_apply] using
    congrArg (fun u : TM x => (cov σ x) u) hXX'.self_of_nhds

private lemma along_eventuallyEq_right_apply
    {X : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (hστ : ∀ᶠ z in nhds x, σ z = τ z) :
    cov.along X σ x = cov.along X τ x := by
  have hcov :
      cov σ x = cov τ x :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq
      (hcov := cov.isCovariantDerivativeOnUniv) hσ hτ (by simpa) hστ
  simpa [CovariantDerivative.along_apply] using
    congrArg (fun L : TM x →L[ℝ] V x => L (X x)) hcov

/-- The raw curvature commutator is unchanged at `x` when its left tangent-field slot is replaced
by a `C¹` field that agrees with it near `x`. -/
lemma curvatureAux_eq_of_eventuallyEq_left_apply
    {X X' Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hXX' : X =ᶠ[nhds x] X') :
    cov.curvatureAux X Y σ x = cov.curvatureAux X' Y σ x := by
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hX'σ : MDiffAt (T% (cov.along X' σ)) x :=
    cov.mdifferentiableAt_along_of_contMDiff hX' hσ
  have hAlong :
      ∀ᶠ z in nhds x, cov.along X σ z = cov.along X' σ z := by
    filter_upwards [hXX'] with z hz
    simp [CovariantDerivative.along_apply, hz]
  have hBracket :
      VectorField.mlieBracket I X Y =ᶠ[nhds x] VectorField.mlieBracket I X' Y := by
    simpa using hXX'.mlieBracket_vectorField (Filter.EventuallyEq.rfl : Y =ᶠ[nhds x] Y)
  have h1 :
      cov.along X (cov.along Y σ) x = cov.along X' (cov.along Y σ) x :=
    cov.along_eventuallyEq_left_apply (σ := cov.along Y σ) hXX'
  have h2 :
      cov.along Y (cov.along X σ) x = cov.along Y (cov.along X' σ) x :=
    cov.along_eventuallyEq_right_apply (X := Y) hXσ hX'σ hAlong
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) σ x =
        cov.along (VectorField.mlieBracket I X' Y) σ x :=
    cov.along_eventuallyEq_left_apply (σ := σ) hBracket
  rw [CovariantDerivative.curvatureAux_apply, CovariantDerivative.curvatureAux_apply]
  rw [h1, h2, h3]

/-- The raw curvature commutator depends only on the value of its left tangent-field slot at `x`,
provided the middle tangent-field slot is `C¹` and the bundle-section slot is `C²`. -/
lemma curvatureAux_eq_of_eq_left_apply
    {X X' Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hXX' : X x = X' x) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X' Y σ x := by
  exact (cov.curvatureAux_tensorial_left (x := x) hY hσ).pointwise hX hX' hXX'

/-- The raw curvature commutator is unchanged at `x` when its middle tangent-field slot is
replaced by a `C¹` field that agrees with it near `x`. -/
lemma curvatureAux_eq_of_eventuallyEq_middle_apply
    {X Y Y' : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y' y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hYY' : Y =ᶠ[nhds x] Y') :
    cov.curvatureAux X Y σ x = cov.curvatureAux X Y' σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hY'σ : MDiffAt (T% (cov.along Y' σ)) x :=
    cov.mdifferentiableAt_along_of_contMDiff hY' hσ
  have hAlong :
      ∀ᶠ z in nhds x, cov.along Y σ z = cov.along Y' σ z := by
    filter_upwards [hYY'] with z hz
    simp [CovariantDerivative.along_apply, hz]
  have hBracket :
      VectorField.mlieBracket I X Y =ᶠ[nhds x] VectorField.mlieBracket I X Y' := by
    simpa using
      (Filter.EventuallyEq.rfl : X =ᶠ[nhds x] X).mlieBracket_vectorField hYY'
  have h1 :
      cov.along X (cov.along Y σ) x = cov.along X (cov.along Y' σ) x :=
    cov.along_eventuallyEq_right_apply (X := X) hYσ hY'σ hAlong
  have h2 :
      cov.along Y (cov.along X σ) x = cov.along Y' (cov.along X σ) x :=
    cov.along_eventuallyEq_left_apply (σ := cov.along X σ) hYY'
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) σ x =
        cov.along (VectorField.mlieBracket I X Y') σ x :=
    cov.along_eventuallyEq_left_apply (σ := σ) hBracket
  rw [CovariantDerivative.curvatureAux_apply, CovariantDerivative.curvatureAux_apply]
  rw [h1, h2, h3]

/-- The raw curvature commutator depends only on the value of its middle tangent-field slot at `x`,
provided the left tangent-field slot is `C¹` and the bundle-section slot is `C²`. -/
lemma curvatureAux_eq_of_eq_middle_apply
    {X Y Y' : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hYY' : Y x = Y' x) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X Y' σ x := by
  exact (cov.curvatureAux_tensorial_middle (x := x) hX hσ).pointwise hY hY' hYY'

/-- The raw curvature commutator is unchanged at `x` when its bundle-section slot is replaced by a
`C²` section that agrees with it near `x`. -/
lemma curvatureAux_eq_of_eventuallyEq_right_apply
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y)))
    (hστ : ∀ᶠ z in nhds x, σ z = τ z) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X Y τ x := by
  have hσx : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hτx : MDiffAt (T% τ) x := (hτ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYτ : MDiffAt (T% (cov.along Y τ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hτ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXτ : MDiffAt (T% (cov.along X τ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hτ
  have hAlongY :
      ∀ᶠ z in nhds x, cov.along Y σ z = cov.along Y τ z := by
    filter_upwards [eventually_eventually_nhds.2 hστ] with z hz
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    have hτz : MDiffAt (T% τ) z := (hτ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    have hcovz :
        cov σ z = cov τ z :=
      IsCovariantDerivativeOn.congr_of_eventuallyEq
        (hcov := cov.isCovariantDerivativeOnUniv) hσz hτz (by simpa) hz
    simpa [CovariantDerivative.along_apply] using
      congrArg (fun L : TM z →L[ℝ] V z => L (Y z)) hcovz
  have hAlongX :
      ∀ᶠ z in nhds x, cov.along X σ z = cov.along X τ z := by
    filter_upwards [eventually_eventually_nhds.2 hστ] with z hz
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    have hτz : MDiffAt (T% τ) z := (hτ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
    have hcovz :
        cov σ z = cov τ z :=
      IsCovariantDerivativeOn.congr_of_eventuallyEq
        (hcov := cov.isCovariantDerivativeOnUniv) hσz hτz (by simpa) hz
    simpa [CovariantDerivative.along_apply] using
      congrArg (fun L : TM z →L[ℝ] V z => L (X z)) hcovz
  have h1 :
      cov.along X (cov.along Y σ) x = cov.along X (cov.along Y τ) x :=
    cov.along_eventuallyEq_right_apply (X := X) hYσ hYτ hAlongY
  have h2 :
      cov.along Y (cov.along X σ) x = cov.along Y (cov.along X τ) x :=
    cov.along_eventuallyEq_right_apply (X := Y) hXσ hXτ hAlongX
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) σ x =
        cov.along (VectorField.mlieBracket I X Y) τ x :=
    cov.along_eventuallyEq_right_apply (X := VectorField.mlieBracket I X Y) hσx hτx hστ
  rw [CovariantDerivative.curvatureAux_apply, CovariantDerivative.curvatureAux_apply]
  rw [h1, h2, h3]

/-- Curvature commutes with finite `C²` linear combinations in its bundle-section slot. -/
lemma curvatureAux_sum_smul_right_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {X Y : Π x : M, TM x} {f : ι → M → ℝ} {σs : ι → Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ) 2 (f i))
    (hσs : ∀ i ∈ s,
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σs i y))) :
    cov.curvatureAux X Y (fun y ↦ s.sum (fun i ↦ f i y • σs i y)) x =
      s.sum (fun i ↦ f i x • cov.curvatureAux X Y (σs i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change cov.curvatureAux X Y (0 : Π y : M, V y) x = 0
      have hcov0 : cov (0 : Π y : M, V y) = 0 := CovariantDerivative.zero cov
      have hY0 : cov.along Y (0 : Π y : M, V y) = 0 := by
        funext y
        have hcov0y : cov (0 : Π y : M, V y) y = 0 := by
          simpa using congrFun hcov0 y
        simp [CovariantDerivative.along, hcov0y]
      have hX0 : cov.along X (0 : Π y : M, V y) = 0 := by
        funext y
        have hcov0y : cov (0 : Π y : M, V y) y = 0 := by
          simpa using congrFun hcov0 y
        simp [CovariantDerivative.along, hcov0y]
      have hcov0x : cov (0 : Π y : M, V y) x = 0 := by
        simpa using congrFun hcov0 x
      simp [CovariantDerivative.curvatureAux, hY0, hX0, CovariantDerivative.along, hcov0x]
  | insert a s ha ih =>
      have hterm :
          ContMDiff I (I.prod 𝓘(ℝ, F)) 2
            (fun y ↦ TotalSpace.mk' F y ((f a • σs a) y)) :=
        (hf a (Finset.mem_insert_self a s)).smul_section
          (hσs a (Finset.mem_insert_self a s))
      have hsum :
          ContMDiff I (I.prod 𝓘(ℝ, F)) 2
            (fun y ↦ TotalSpace.mk' F y (s.sum (fun i ↦ f i y • σs i y))) :=
        ContMDiff.sum_section (s := s) fun i hi ↦
          (hf i (Finset.mem_insert_of_mem hi)).smul_section
            (hσs i (Finset.mem_insert_of_mem hi))
      have hih :
          cov.curvatureAux X Y (fun y ↦ s.sum (fun i ↦ f i y • σs i y)) x =
            s.sum (fun i ↦ f i x • cov.curvatureAux X Y (σs i) x) :=
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hσs i (Finset.mem_insert_of_mem hi))
      calc
        cov.curvatureAux X Y (fun y ↦ (insert a s).sum (fun i ↦ f i y • σs i y)) x
            = cov.curvatureAux X Y (f a • σs a + fun y ↦ s.sum (fun i ↦ f i y • σs i y)) x := by
                have hsection :
                    (fun y ↦ (insert a s).sum (fun i ↦ f i y • σs i y)) =
                      (f a • σs a + fun y ↦ s.sum (fun i ↦ f i y • σs i y)) := by
                  funext y
                  simp [Finset.sum_insert, ha, Pi.add_apply]
                rw [hsection]
        _ = cov.curvatureAux X Y (f a • σs a) x +
              cov.curvatureAux X Y (fun y ↦ s.sum (fun i ↦ f i y • σs i y)) x := by
                exact cov.curvatureAux_add_right_apply hX hY hterm hsum
        _ = f a x • cov.curvatureAux X Y (σs a) x +
              s.sum (fun i ↦ f i x • cov.curvatureAux X Y (σs i) x) := by
                rw [cov.curvatureAux_smul_fun_right_apply
                  (hf a (Finset.mem_insert_self a s)) hX hY
                  (hσs a (Finset.mem_insert_self a s)), hih]
        _ = (insert a s).sum (fun i ↦ f i x • cov.curvatureAux X Y (σs i) x) := by
                rw [Finset.sum_insert ha]

/-- A finite `C²` expansion criterion for replacing the bundle-section slot of the raw curvature
commutator.  If two sections have local finite expansions in the same smooth sections with
coefficient functions that agree at the evaluation point, then curvature sees the same right slot. -/
lemma curvatureAux_eq_of_finite_sum_eq_right_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x}
    {f g : ι → M → ℝ} {σs : ι → Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y)))
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) 2 (f i))
    (hg : ∀ i, ContMDiff I 𝓘(ℝ) 2 (g i))
    (hσs : ∀ i,
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σs i y)))
    (hσsum : ∀ᶠ y in nhds x, σ y = ∑ i : ι, f i y • σs i y)
    (hτsum : ∀ᶠ y in nhds x, τ y = ∑ i : ι, g i y • σs i y)
    (hfg : ∀ i, f i x = g i x) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X Y τ x := by
  classical
  let s : Finset ι := Finset.univ
  have hsumf :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2
        (fun y ↦ TotalSpace.mk' F y (∑ i : ι, f i y • σs i y)) := by
    simpa [s] using
      (ContMDiff.sum_section (s := s) fun i _ ↦ (hf i).smul_section (hσs i))
  have hsumg :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2
        (fun y ↦ TotalSpace.mk' F y (∑ i : ι, g i y • σs i y)) := by
    simpa [s] using
      (ContMDiff.sum_section (s := s) fun i _ ↦ (hg i).smul_section (hσs i))
  have hsum_eq :
      (∑ i : ι, f i x • cov.curvatureAux X Y (σs i) x) =
        ∑ i : ι, g i x • cov.curvatureAux X Y (σs i) x := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hfg i]
  calc
    cov.curvatureAux X Y σ x =
        cov.curvatureAux X Y (fun y ↦ ∑ i : ι, f i y • σs i y) x := by
          exact cov.curvatureAux_eq_of_eventuallyEq_right_apply hX hY hσ hsumf hσsum
    _ = ∑ i : ι, f i x • cov.curvatureAux X Y (σs i) x := by
          simpa [s] using
            cov.curvatureAux_sum_smul_right_apply (s := s) hX hY
              (fun i _ ↦ hf i) (fun i _ ↦ hσs i)
    _ = ∑ i : ι, g i x • cov.curvatureAux X Y (σs i) x := hsum_eq
    _ = cov.curvatureAux X Y (fun y ↦ ∑ i : ι, g i y • σs i y) x := by
          simpa [s] using
            (cov.curvatureAux_sum_smul_right_apply (s := s) hX hY
              (fun i _ ↦ hg i) (fun i _ ↦ hσs i)).symm
    _ = cov.curvatureAux X Y τ x := by
          exact (cov.curvatureAux_eq_of_eventuallyEq_right_apply hX hY hτ hsumg hτsum).symm

/-- A local-frame version of the finite right-slot replacement criterion.  Around `x`, every
section expands in the local frame of `trivializationAt F V x`; if the corresponding coefficient
functions are globally `C²` and agree at `x`, then the raw curvature commutator sees the same
right slot. -/
lemma curvatureAux_eq_of_trivializationAt_localFrameCoeff_eq_right_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F)
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y)))
    (hσcoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y ↦ (trivializationAt F V x).localFrameCoeff I b i y (σ y)))
    (hτcoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y ↦ (trivializationAt F V x).localFrameCoeff I b i y (τ y)))
    (hcoeff_eq : ∀ i : ι,
      (trivializationAt F V x).localFrameCoeff I b i x (σ x) =
        (trivializationAt F V x).localFrameCoeff I b i x (τ x)) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X Y τ x := by
  let e := trivializationAt F V x
  let f : ι → M → ℝ := fun i y ↦ e.localFrameCoeff I b i y (σ y)
  let g : ι → M → ℝ := fun i y ↦ e.localFrameCoeff I b i y (τ y)
  let σs : ι → Π y : M, V y :=
    fun i ↦ smoothExtend (I := I) (F := F) (V := V) x (e.localFrame b i x)
  have hσsum :
      ∀ᶠ y in nhds x, σ y = ∑ i : ι, f i y • σs i y := by
    simpa [f, σs, e] using
      eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
        (I := I) (F := F) (V := V) b σ x
  have hτsum :
      ∀ᶠ y in nhds x, τ y = ∑ i : ι, g i y • σs i y := by
    simpa [g, σs, e] using
      eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
        (I := I) (F := F) (V := V) b τ x
  have hf : ∀ i : ι, ContMDiff I 𝓘(ℝ) 2 (f i) := by
    intro i
    simpa [f, e] using hσcoeff i
  have hg : ∀ i : ι, ContMDiff I 𝓘(ℝ) 2 (g i) := by
    intro i
    simpa [g, e] using hτcoeff i
  have hσs : ∀ i : ι,
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σs i y)) := by
    intro i
    simpa [σs, e] using
      smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x (e.localFrame b i x)
  have hfg : ∀ i : ι, f i x = g i x := by
    intro i
    simpa [f, g, e] using hcoeff_eq i
  exact cov.curvatureAux_eq_of_finite_sum_eq_right_apply
    hX hY hσ hτ hf hg hσs hσsum hτsum hfg

/-- Simultaneous locality for the raw curvature commutator in all three slots. -/
lemma curvatureAux_eq_of_eventuallyEq_apply
    {X X' Y Y' : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y' y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y)))
    (hXX' : X =ᶠ[nhds x] X')
    (hYY' : Y =ᶠ[nhds x] Y')
    (hστ : ∀ᶠ z in nhds x, σ z = τ z) :
    cov.curvatureAux X Y σ x = cov.curvatureAux X' Y' τ x := by
  calc
    cov.curvatureAux X Y σ x = cov.curvatureAux X' Y σ x :=
      cov.curvatureAux_eq_of_eventuallyEq_left_apply hX hX' hY hσ hXX'
    _ = cov.curvatureAux X' Y' σ x :=
      cov.curvatureAux_eq_of_eventuallyEq_middle_apply hX' hY hY' hσ hYY'
    _ = cov.curvatureAux X' Y' τ x :=
      cov.curvatureAux_eq_of_eventuallyEq_right_apply hX' hY' hσ hτ hστ

/-- The bundled curvature tensor, built from canonical smooth extensions of fibre vectors. -/
noncomputable def curvatureTensor (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] V x →ₗ[ℝ] V x := by
  refine
    { toFun := fun u ↦
        { toFun := fun v ↦
            { toFun := fun w ↦
                cov.curvatureAux
                  (smoothExtend (I := I) (F := E) (V := TM) x u)
                  (smoothExtend (I := I) (F := E) (V := TM) x v)
                  (smoothExtend (I := I) (F := F) (V := V) x w) x
              map_add' := by
                intro w w'
                simpa [smoothExtend_add] using
                  cov.curvatureAux_add_right_apply
                    (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                    (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                    (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
                    (hτ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w')
              map_smul' := by
                intro c w
                simpa [smoothExtend_smul] using
                  cov.curvatureAux_smul_right_apply c
                    (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                    (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                    (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }
          map_add' := by
            intro v v'
            ext w
            simpa [smoothExtend_add] using
              cov.curvatureAux_add_middle_apply
                (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                (hY' := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v')
                (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
          map_smul' := by
            intro c v
            ext w
            simpa [smoothExtend_smul] using
              cov.curvatureAux_smul_middle_apply c
                (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }
      map_add' := by
        intro u u'
        ext v w
        simpa [smoothExtend_add] using
          cov.curvatureAux_add_left_apply
            (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
            (hX' := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u')
            (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
            (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
      map_smul' := by
        intro c u
        ext v w
        simpa [smoothExtend_smul] using
          cov.curvatureAux_smul_left_apply c
            (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
            (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
            (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }

@[simp]
lemma curvatureTensor_apply (x : M) (u v : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u v w =
      cov.curvatureAux
        (smoothExtend (I := I) (F := E) (V := TM) x u)
        (smoothExtend (I := I) (F := E) (V := TM) x v)
        (smoothExtend (I := I) (F := F) (V := V) x w) x := rfl

/-- Metric compatibility makes the bundled tangent curvature tensor skew-adjoint in its
right two slots. -/
theorem curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
    [RiemannianBundle TM] [IsContMDiffRiemannianBundle I 2 E TM]
    (covTM : CovariantDerivative I E TM) [ContMDiffCovariantDerivative covTM 1]
    (hmetric : covTM.IsMetricCompatibleTangent)
    (x : M) (u v w z : TM x) :
    inner ℝ (curvatureTensor (cov := covTM) x u v w) z +
      inner ℝ w (curvatureTensor (cov := covTM) x u v z) = 0 := by
  have hraw :=
    covTM.curvatureAux_inner_add_eq_zero_of_metricCompatible
      (I := I) (F := E) (V := TM)
      (fun {x} {σ τ} hσ hτ u ↦ hmetric (x := x) (σ := σ) (τ := τ) hσ hτ u)
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (Y := smoothExtend (I := I) (F := E) (V := TM) x v)
      (σ := smoothExtend (I := I) (F := E) (V := TM) x w)
      (τ := smoothExtend (I := I) (F := E) (V := TM) x z)
      (x := x)
      (smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
      (smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x w)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x z)
  simpa [curvatureTensor_apply, smoothExtend_apply] using hraw

/-- A computation rule for the bundled curvature tensor from arbitrary smooth representatives:
the left and middle tangent-field slots may be replaced by their values at `x`, while the
bundle-section slot may be replaced by a locally equal canonical smooth extension. -/
lemma curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    {u v : TM x} {w : V x}
    (hXu : X x = u) (hYv : Y x = v)
    (hσw : ∀ᶠ y in nhds x, σ y =
      smoothExtend (I := I) (F := F) (V := V) x w y) :
    cov.curvatureAux X Y σ x = curvatureTensor (cov := cov) x u v w := by
  let Xcanon : Π y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x u
  let Ycanon : Π y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x v
  let σcanon : Π y : M, V y := smoothExtend (I := I) (F := F) (V := V) x w
  have hXcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Xcanon y)) := by
    simpa [Xcanon] using smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  have hYcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Ycanon y)) := by
    simpa [Ycanon] using smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v
  have hσcanon₂ :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σcanon y)) := by
    simpa [σcanon] using smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w
  have hXat : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hXcanon_at : MDiffAt (T% Xcanon) x :=
    (hXcanon₁ x).mdifferentiableAt one_ne_zero
  have hYat : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hYcanon_at : MDiffAt (T% Ycanon) x :=
    (hYcanon₁ x).mdifferentiableAt one_ne_zero
  have hXeq : X x = Xcanon x := by
    simpa [Xcanon, smoothExtend_apply] using hXu
  have hYeq : Y x = Ycanon x := by
    simpa [Ycanon, smoothExtend_apply] using hYv
  have hσeq : ∀ᶠ y in nhds x, σ y = σcanon y := by
    simpa [σcanon] using hσw
  calc
    cov.curvatureAux X Y σ x = cov.curvatureAux Xcanon Y σ x := by
      exact cov.curvatureAux_eq_of_eq_left_apply hY hσ hXat hXcanon_at hXeq
    _ = cov.curvatureAux Xcanon Ycanon σ x := by
      exact cov.curvatureAux_eq_of_eq_middle_apply hXcanon₁ hσ hYat hYcanon_at hYeq
    _ = cov.curvatureAux Xcanon Ycanon σcanon x := by
      exact cov.curvatureAux_eq_of_eventuallyEq_right_apply hXcanon₁ hYcanon₁ hσ hσcanon₂ hσeq
    _ = curvatureTensor (cov := cov) x u v w := by
      simp [curvatureTensor_apply, Xcanon, Ycanon, σcanon]

/-- A computation rule for the bundled curvature tensor using an explicitly supplied bump in the
right slot.  The supplied bump can be chosen with support in any convenient neighborhood, while the
result agrees with the canonical curvature tensor because all such bump extensions equal `extend`
near the base point. -/
lemma curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_smoothExtendWithBump_right
    {X Y : Π x : M, TM x} {x : M}
    (φ : SmoothBumpFunction I x)
    (hφsupp : tsupport φ ⊆ (trivializationAt F V x).baseSet)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    {u v : TM x} {w : V x}
    (hXu : X x = u) (hYv : Y x = v) :
    cov.curvatureAux X Y
        (smoothExtendWithBump (I := I) (F := F) (V := V) x φ w) x =
      curvatureTensor (cov := cov) x u v w := by
  have hσ :
      ContMDiff I (I.prod 𝓘(ℝ, F)) 2
        (fun y ↦ TotalSpace.mk' F y
          (smoothExtendWithBump (I := I) (F := F) (V := V) x φ w y)) :=
    smoothExtendWithBump_contMDiff_two_of_tsupport_subset
      (I := I) (F := F) (V := V) x φ w hφsupp
  have hσlocal :
      ∀ᶠ y in nhds x,
        smoothExtendWithBump (I := I) (F := F) (V := V) x φ w y =
          smoothExtend (I := I) (F := F) (V := V) x w y :=
    smoothExtendWithBump_eventuallyEq_smoothExtend (I := I) (F := F) (V := V) x φ w
  exact cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
    hX hY hσ hXu hYv hσlocal

/-- Variant of `curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right`
where the local right-slot representative is the raw trivialization `extend` section.  The
canonical smooth extension is eventually equal to `extend` because its bump is eventually `1`
near the base point. -/
lemma curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_extend_right
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    {u v : TM x} {w : V x}
    (hXu : X x = u) (hYv : Y x = v)
    (hσw : ∀ᶠ y in nhds x, σ y = extend F w y) :
    cov.curvatureAux X Y σ x = curvatureTensor (cov := cov) x u v w := by
  have hσsmooth :
      ∀ᶠ y in nhds x, σ y = smoothExtend (I := I) (F := F) (V := V) x w y := by
    filter_upwards [hσw,
      smoothExtend_eventuallyEq_extend (I := I) (F := F) (V := V) x w] with y hσy hsm
    exact hσy.trans hsm.symm
  exact cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
    hX hY hσ hXu hYv hσsmooth

/-- A local-frame coefficient criterion for computing the bundled curvature tensor from
arbitrary smooth left/middle representatives and an arbitrary right-slot representative.

The right-slot representative need not be eventually equal to the canonical smooth extension:
it is enough for its `trivializationAt` frame coefficients to be `C²` and to agree at the
base point with the coefficients of the target fiber vector.  The canonical extension's
coefficient regularity is automatic from the bump-supported extension construction. -/
lemma curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F)
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    {u v : TM x} {w : V x}
    (hXu : X x = u) (hYv : Y x = v)
    (hσcoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y ↦ (trivializationAt F V x).localFrameCoeff I b i y (σ y)))
    (hcoeff_eq : ∀ i : ι,
      (trivializationAt F V x).localFrameCoeff I b i x (σ x) =
        (trivializationAt F V x).localFrameCoeff I b i x w) :
    cov.curvatureAux X Y σ x = curvatureTensor (cov := cov) x u v w := by
  let τ : Π y : M, V y := smoothExtend (I := I) (F := F) (V := V) x w
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y)) := by
    simpa [τ] using smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w
  have hτcoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y ↦ (trivializationAt F V x).localFrameCoeff I b i y (τ y)) := by
    intro i
    simpa [τ] using
      smoothExtend_localFrameCoeff_contMDiff_two
        (I := I) (F := F) (V := V) b x w i
  have hcoeff_eq' : ∀ i : ι,
      (trivializationAt F V x).localFrameCoeff I b i x (σ x) =
        (trivializationAt F V x).localFrameCoeff I b i x (τ x) := by
    intro i
    simpa [τ, smoothExtend_apply] using hcoeff_eq i
  have hright :
      cov.curvatureAux X Y σ x = cov.curvatureAux X Y τ x :=
    cov.curvatureAux_eq_of_trivializationAt_localFrameCoeff_eq_right_apply
      b hX hY hσ hτ hσcoeff hτcoeff hcoeff_eq'
  have hτlocal : ∀ᶠ y in nhds x, τ y = smoothExtend (I := I) (F := F) (V := V) x w y := by
    filter_upwards [] with y
    rfl
  exact hright.trans
    (cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
      hX hY hτ hXu hYv hτlocal)

@[simp]
lemma curvatureTensor_swap (x : M) (u v : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u v w = -curvatureTensor (cov := cov) x v u w := by
  simpa [curvatureTensor_apply] using
    congrArg (fun s => s x) <| cov.curvatureAux_swap
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (Y := smoothExtend (I := I) (F := E) (V := TM) x v)
      (σ := smoothExtend (I := I) (F := F) (V := V) x w)

@[simp]
lemma curvatureTensor_self (x : M) (u : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u u w = 0 := by
  simpa [curvatureTensor_apply] using
    congrArg (fun s => s x) <| cov.curvatureAux_self
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (σ := smoothExtend (I := I) (F := F) (V := V) x w)

end CurvatureTensor


end CovariantDerivative
