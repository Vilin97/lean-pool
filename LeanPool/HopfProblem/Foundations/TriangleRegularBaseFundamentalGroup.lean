/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
public import LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1

/-!
# Hopf problem: foundations · triangle regular base fundamental group

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem SimplyConnectedCover.homotopic_of_mem {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s)
    (hq : ∀ t, q t ∈ s) : Path.Homotopic p q := by
  let : SimplyConnectedSpace s := hs
  have hx : x ∈ s := by simpa using hp 0
  have hy : y ∈ s := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let q' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have h :=
    (SimplyConnectedSpace.paths_homotopic p' q').map
      (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap s X)
  have hp' : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq' : q'.map continuous_subtype_val = q := by ext t; rfl
  exact hp' ▸ hq' ▸ h

public
theorem SimplyConnectedCover.trans_mem {X : Type*} [TopologicalSpace X] {s : Set X} {x y z : X}
    (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, p.trans q t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)

private def
    SimplyConnectedCover.chartPath {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i) (i : ι) (x : X)
    (hx : x ∈ U i) : Path o x :=
  ((hs i).isPathConnected.joinedIn o (ho i) x hx).somePath

private theorem SimplyConnectedCover.chartPath_mem {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i) (i : ι)
    (x : X) (hx : x ∈ U i) (t : (unitInterval)) : chartPath U hs o ho i x hx t ∈ U i :=
  JoinedIn.somePath_mem _ t

private theorem
    SimplyConnectedCover.chartPath_homotopic {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) (i j : ι) (x : X) (hi : x ∈ U i)
    (hj : x ∈ U j) : Path.Homotopic (chartPath U hs o ho i x hi) (chartPath U hs o ho j x hj) := by
  let h := (hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩
  exact
    (homotopic_of_mem (hs i) _ h.somePath (chartPath_mem U hs o ho i x hi)
          (fun t => (h.somePath_mem t).1)).trans
      (homotopic_of_mem (hs j) h.somePath _ (fun t => (h.somePath_mem t).2)
        (chartPath_mem U hs o ho j x hj))

private theorem SimplyConnectedCover.quotient_cast_trans {X : Type*} [TopologicalSpace X]
    {o x y o' x' y' : X} (p : Path.Homotopic.Quotient o x) (q : Path.Homotopic.Quotient x y)
    (ho : o' = o) (hx : x' = x) (hy : y' = y) :
    (p.trans q).cast ho hy = (p.cast ho hx).trans (q.cast hx hy) := by
  cases ho
  cases hx
  cases hy
  simp

private theorem SimplyConnectedCover.quotient_cast_section {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) {x y : X} (h : x = y) : (F y).cast rfl h = F x := by
  cases h
  simp

private theorem
    SimplyConnectedCover.section_subpath_zero_one {X : Type*} [TopologicalSpace X] {o x y : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) (p : Path x y)
    (h :
      Path.Homotopic.Quotient.trans (F (p 0)) (Path.Homotopic.Quotient.mk (p.subpath 0 1)) =
        F (p 1)) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hp :
    (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
      Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have h' := congrArg (fun q : Path.Homotopic.Quotient o (p 1) => q.cast rfl p.target.symm) h
  rw [quotient_cast_trans _ _ rfl p.source.symm p.target.symm,
    quotient_cast_section F p.source.symm, hp, quotient_cast_section F p.target.symm] at h'
  exact h'

private theorem SimplyConnectedCover.section_trans_of_open_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (o : X)
    (F : ∀ x, Path.Homotopic.Quotient o x)
    (hF :
      ∀ i {x y : X} (p : Path x y),
        (∀ t, p t ∈ U i) →
          Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y)
    {x y : X} (p : Path x y) :
    Path.Homotopic.Quotient.trans (F x) (Path.Homotopic.Quotient.mk p) = F y := by
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i => (hopen i).preimage p.continuous)
      hpre
  have hwalk :
    ∀ k : ℕ,
      Path.Homotopic.Quotient.trans (F (p 0)) (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) =
        F (p (t k)) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.trans_refl]
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : ∀ s, p.subpath (t k) (t (k + 1)) s ∈ U i := by
        apply Set.range_subset_iff.mp
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact Set.image_subset_iff.mpr hi
      have hconcat :
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      calc
        Path.Homotopic.Quotient.trans (F (p 0))
              (Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1)))) =
            Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.trans (F (p 0))
                (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))))
              (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by
          rw [Path.Homotopic.Quotient.trans_assoc, hconcat]
        _ =
            Path.Homotopic.Quotient.trans (F (p (t k)))
              (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) := by rw [ih]
        _ = F (p (t (k + 1))) := hF i _ hmem
  have h := hwalk n
  rw [hn n le_rfl] at h
  exact section_subpath_zero_one F p h

private theorem
    simplyConnectedSpace_of_open_cover {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (hsimply : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) : SimplyConnectedSpace X := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  let idx (x : X) : ι := (hcov x).choose
  have hidx (x : X) : x ∈ U (idx x) := (hcov x).choose_spec
  let c (x : X) : Path o x := SimplyConnectedCover.chartPath U hsimply o ho (idx x) x (hidx x)
  let F (x : X) : Path.Homotopic.Quotient o x := Path.Homotopic.Quotient.mk (c x)
  have hFi (i : ι) (x : X) (hx : x ∈ U i) :
    F x = Path.Homotopic.Quotient.mk (SimplyConnectedCover.chartPath U hsimply o ho i x hx) := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.chartPath_homotopic U hsimply o ho hinter (idx x) i x (hidx x) hx
  have hF (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
    (F x).trans (Path.Homotopic.Quotient.mk p) = F y := by
    have hx : x ∈ U i := by simpa using hp 0
    have hy : y ∈ U i := by simpa using hp 1
    rw [hFi i x hx, hFi i y hy, ← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
    exact
      SimplyConnectedCover.homotopic_of_mem (hsimply i) _ _
        (SimplyConnectedCover.trans_mem _ _
          (SimplyConnectedCover.chartPath_mem U hsimply o ho i x hx) hp)
        (SimplyConnectedCover.chartPath_mem U hsimply o ho i y hy)
  have hpc : PathConnectedSpace X :=
    { nonempty := ⟨o⟩
      joined := fun x y => ⟨(c x).symm.trans (c y)⟩ }
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc, ?_⟩
  intro x y p q
  have hp := SimplyConnectedCover.section_trans_of_open_cover U hopen hcover o F hF p
  have hq := SimplyConnectedCover.section_trans_of_open_cover U hopen hcover o F hF q
  apply Path.Homotopic.Quotient.eq.mp
  have h :=
    congrArg (fun r : Path.Homotopic.Quotient o y => (F x).symm.trans r) (hp.trans hq.symm)
  simpa only [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] using h

private theorem TriangleRegularBaseFundamentalGroup.pathClass_property_cast {X : Type*}
    [TopologicalSpace X] (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop) {x y x' y' : X}
    (q : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) (hq : P q) : P (q.cast hx hy) :=
  by
  cases hx
  cases hy
  simpa using hq

private theorem TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop)
    (h_refl : ∀ x, P (Path.Homotopic.Quotient.refl x))
    (h_trans :
      ∀ {x y z : X} {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient y z},
        P p → P q → P (p.trans q))
    (h_local :
      ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i → P (Path.Homotopic.Quotient.mk p)) :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y), P q := by
  intro x y q
  obtain ⟨p⟩ := q
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i => (hopen i).preimage p.continuous)
      hpre
  have hwalk : ∀ k : ℕ, P (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl]
      exact h_refl (p 0)
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : Set.range (p.subpath (t k) (t (k + 1))) ⊆ U i := by
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact Set.image_subset_iff.mpr hi
      have hconcat :
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      rw [← hconcat]
      exact h_trans ih (h_local i _ hmem)
  have hfull := hwalk n
  rw [hn n le_rfl] at hfull
  have hp :
    (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
      Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have htransport := pathClass_property_cast P _ p.source.symm p.target.symm hfull
  rwa [hp] at htransport

private theorem TriangleRegularBaseFundamentalGroup.quotient_symm_trans_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

private theorem TriangleRegularBaseFundamentalGroup.quotient_trans_right_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} {p q : Path.Homotopic.Quotient x y}
    (r : Path.Homotopic.Quotient y z) (h : p.trans r = q.trans r) : p = q := by
  have h' := congrArg (fun a : Path.Homotopic.Quotient x z => a.trans r.symm) h
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using h'

private def TriangleRegularBaseFundamentalGroup.basedLoop {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ x, Path.Homotopic.Quotient o x) {x y : X} (p : Path.Homotopic.Quotient x y) :
    FundamentalGroup X o :=
  ((F x).trans p).trans (F y).symm

private def
    TriangleRegularBaseFundamentalGroup.pathDifference {X : Type*} [TopologicalSpace X] {o x : X}
    (p q : Path.Homotopic.Quotient o x) : FundamentalGroup X o :=
  p.trans q.symm

@[simp]
private theorem TriangleRegularBaseFundamentalGroup.basedLoop_refl {X : Type*} [TopologicalSpace X]
    {o : X} (F : ∀ x, Path.Homotopic.Quotient o x) (x : X) :
    basedLoop F (Path.Homotopic.Quotient.refl x) = 1 := by
  simp only [basedLoop, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

private theorem TriangleRegularBaseFundamentalGroup.basedLoop_trans {X : Type*} [TopologicalSpace X]
    {o x y z : X} (F : ∀ x, Path.Homotopic.Quotient o x) (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : basedLoop F (p.trans q) = basedLoop F q * basedLoop F p :=
  by
  simp only [basedLoop, FundamentalGroup.mul_def, Path.Homotopic.Quotient.trans_assoc,
    quotient_symm_trans_cancel]

private theorem
    TriangleRegularBaseFundamentalGroup.basedLoop_comparison {X : Type*} [TopologicalSpace X]
    {o x y : X} (F : ∀ z, Path.Homotopic.Quotient o z) (a : Path.Homotopic.Quotient o x)
    (b : Path.Homotopic.Quotient o y) (p : Path.Homotopic.Quotient x y) (h : a.trans p = b) :
    basedLoop F p = (pathDifference (F y) b)⁻¹ * pathDifference (F x) a := by
  apply
    (@eq_inv_mul_iff_mul_eq (FundamentalGroup X o) _ (basedLoop F p) (pathDifference (F y) b)
        (pathDifference (F x) a)).2
  apply quotient_trans_right_cancel b
  simp only [basedLoop, pathDifference, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc, quotient_symm_trans_cancel,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  rw [← h, quotient_symm_trans_cancel]

private structure TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover (X : Type*)
    [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  simplyU : IsSimplyConnected (U : Set X)
  simplyV : IsSimplyConnected (V : Set X)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

private def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) : Path D.base x :=
  (D.simplyU.isPathConnected.joinedIn D.base D.baseU x hx).somePath

private def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) : Path D.base x :=
  (D.simplyV.isPathConnected.joinedIn D.base D.baseV x hx).somePath

private theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) (t : (unitInterval)) : D.pathU x hx t ∈ D.U :=
  JoinedIn.somePath_mem _ t

private theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) (t : (unitInterval)) : D.pathV x hx t ∈ D.V :=
  JoinedIn.somePath_mem _ t

private theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathU_trans {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.U) (hy : y ∈ D.U) (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    (Path.Homotopic.Quotient.mk (D.pathU x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathU y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact
    SimplyConnectedCover.homotopic_of_mem D.simplyU _ _
      (SimplyConnectedCover.trans_mem _ _ (D.pathU_mem x hx) hp) (D.pathU_mem y hy)

private theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.pathV_trans {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.V) (hy : y ∈ D.V) (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    (Path.Homotopic.Quotient.mk (D.pathV x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathV y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact
    SimplyConnectedCover.homotopic_of_mem D.simplyV _ _
      (SimplyConnectedCover.trans_mem _ _ (D.pathV_mem x hx) hp) (D.pathV_mem y hy)

private def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V) : FundamentalGroup X D.base :=
  (Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
    (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_eq_of_joinedIn
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) {x y : X} (hxU : x ∈ D.U)
    (hxV : x ∈ D.V) (hyU : y ∈ D.U) (hyV : y ∈ D.V) (hxy : JoinedIn ((D.U : Set X) ∩ D.V) x y) :
    D.switchClass x hxU hxV = D.switchClass y hyU hyV := by
  let p := hxy.somePath
  have hU := D.pathU_trans hxU hyU p (fun t => (hxy.somePath_mem t).1)
  have hV := D.pathV_trans hxV hyV p (fun t => (hxy.somePath_mem t).2)
  apply
    TriangleRegularBaseFundamentalGroup.quotient_trans_right_cancel
      (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  change
    ((Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV)) =
      ((Path.Homotopic.Quotient.mk (D.pathU y hyU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV y hyV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  rw [Path.Homotopic.Quotient.trans_assoc, ← hV,
    TriangleRegularBaseFundamentalGroup.quotient_symm_trans_cancel, hU]
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

@[simp]
private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_base {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) :
    D.switchClass D.base D.baseU D.baseV = 1 := by
  have hU :
    Path.Homotopic.Quotient.mk (D.pathU D.base D.baseU) = Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)
  have hV :
    Path.Homotopic.Quotient.mk (D.pathV D.base D.baseV) = Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyV _ _ (D.pathV_mem _ _) (fun _ => D.baseV)
  simp only [switchClass, hU, hV, Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def]

private theorem
    fundamentalGroup_eq_one_of_path {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (hx : ∀ g : FundamentalGroup X x, g = 1) (g : FundamentalGroup X y) : g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

private theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 :=
  by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y γ
    exact
      Path.Homotopic.Quotient.eq.mp
        (fundamentalGroup_eq_one_of_path (PathConnectedSpace.somePath x y) hx
          (Path.Homotopic.Quotient.mk γ))

private theorem simplyConnectedSpace_of_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x).mpr hx

private theorem PeriodTorusLineBundle.ChernCocycle.simplexFace_comp {n : ℕ} {i j : Fin (n + 2)}
    (h : i ≤ j) :
    (FirstHurewicz.simplexFace (n + 1) j.succ).comp (FirstHurewicz.simplexFace n i) =
      (FirstHurewicz.simplexFace (n + 1) i.castSucc).comp (FirstHurewicz.simplexFace n j) := by
  have hf :=
    congrArg
      (fun f : (SimplexCategory.mk (n)) ⟶ (SimplexCategory.mk (n + 2)) =>
        (SimplexCategory.toTop₀.map f).hom)
      (SimplexCategory.δ_comp_δ h)
  have hl :=
    congrArg
      (fun f :
          SimplexCategory.toTop₀.obj (SimplexCategory.mk (n)) ⟶
            SimplexCategory.toTop₀.obj (SimplexCategory.mk (n + 2)) =>
        f.hom)
      (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ i) (SimplexCategory.δ j.succ))
  have hr :=
    congrArg
      (fun f :
          SimplexCategory.toTop₀.obj (SimplexCategory.mk (n)) ⟶
            SimplexCategory.toTop₀.obj (SimplexCategory.mk (n + 2)) =>
        f.hom)
      (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ j) (SimplexCategory.δ i.castSucc))
  exact hl.symm.trans (hf.trans hr)

private theorem PeriodTorusLineBundle.ChernCocycle.singularSimplex_face_face {X : Type*}
    [TopologicalSpace X] {n : ℕ} (σ : C(FirstHurewicz.Simplex (n + 2), X)) {i j : Fin (n + 2)}
    (h : i ≤ j) :
    (σ.comp (FirstHurewicz.simplexFace (n + 1) j.succ)).comp (FirstHurewicz.simplexFace n i) =
      (σ.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc)).comp
        (FirstHurewicz.simplexFace n j) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex (n + 2)) => σ.comp f)
      (simplexFace_comp h)

end Mathoverflow1973

end
