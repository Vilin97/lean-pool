/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Foundations.Core2

/-!
# Hopf problem: pi 1 · fundamental group van kampen 1

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

private theorem FundamentalGroupVanKampen.subpath_mem_of_mem_Icc {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t ∈ Set.Icc a b, p t ∈ s) : ∀ t, p.subpath a b t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [p.range_subpath_of_le a b hab]
  exact Set.image_subset_iff.mpr hp

private structure
    FundamentalGroupVanKampen.LocalPathValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (G : Type*) [Group G] where
  value : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) → G
  refl : ∀ i (x : X) (hx : ∀ t, Path.refl x t ∈ U i), value i (Path.refl x) hx = 1
  trans :
    ∀ i {x y z : X} (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
      (hpq : ∀ t, p.trans q t ∈ U i), value i (p.trans q) hpq = value i p hp * value i q hq
  subpath_mul :
    ∀ i {x y : X} (p : Path x y) (a b c : (unitInterval)) (_ : a ≤ b) (_ : b ≤ c)
      (hab : ∀ t, p.subpath a b t ∈ U i) (hbc : ∀ t, p.subpath b c t ∈ U i)
      (hac : ∀ t, p.subpath a c t ∈ U i),
      value i (p.subpath a c) hac = value i (p.subpath a b) hab * value i (p.subpath b c) hbc
  compatible :
    ∀ i j {x y : X} (p : Path x y) (hi : ∀ t, p t ∈ U i) (hj : ∀ t, p t ∈ U j),
      value i p hi = value j p hj

private theorem FundamentalGroupVanKampen.LocalPathValue.value_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : ∀ t, p t ∈ U i) (hp' : ∀ t, p.cast hx hy t ∈ U i) :
    L.value i (p.cast hx hy) hp' = L.value i p hp := by
  cases hx
  cases hy
  rfl

private def
    FundamentalGroupVanKampen.LocalPathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i)
    (H : Path.Homotopy p q), (∀ s, H s ∈ U i) → L.value i p hp = L.value i q hq

private structure FundamentalGroupVanKampen.PathValue (X : Type*) [TopologicalSpace X] (G : Type*)
    [Group G] where
  value : ∀ {x y : X}, Path x y → G
  refl : ∀ x, value (Path.refl x) = 1
  trans : ∀ {x y z : X} (p : Path x y) (q : Path y z), value (p.trans q) = value p * value q
  subpath_mul :
    ∀ {x y : X} (p : Path x y) (a b c : (unitInterval)),
      a ≤ b → b ≤ c → value (p.subpath a c) = value (p.subpath a b) * value (p.subpath b c)

private theorem FundamentalGroupVanKampen.PathValue.value_cast {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {x y x' y' : X}
    (p : Path x y) (hx : x' = x) (hy : y' = y) : V.value (p.cast hx hy) = V.value p := by
  cases hx
  cases hy
  rfl

private theorem FundamentalGroupVanKampen.PathValue.value_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} (p : Path x y) : V.value (p.subpath 0 1) = V.value p := by
  rw [Path.subpath_zero_one, V.value_cast]

private def FundamentalGroupVanKampen.PathValue.Extends {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) : Prop :=
  ∀ i {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i), V.value p = L.value i p hp

private def FundamentalGroupVanKampen.PathValue.HomotopyInvariant {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) : Prop :=
  ∀ {x y : X} (p q : Path x y), Path.Homotopic p q → V.value p = V.value q

/-- A pointed two-open cover with a connected overlap for van Kampen's theorem. -/
public
structure FundamentalGroupVanKampen.TwoOpenCover (X : Type*) [TopologicalSpace X] where
  /-- The first open set of the cover. -/
  U : TopologicalSpace.Opens X
  /-- The second open set of the cover. -/
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  pathConnectedU : IsPathConnected (U : Set X)
  pathConnectedV : IsPathConnected (V : Set X)
  pathConnectedIntersection : IsPathConnected ((U : Set X) ∩ V)
  /-- The chosen base point in the overlap. -/
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

private abbrev FundamentalGroupVanKampen.TwoOpenCover.chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : Bool → TopologicalSpace.Opens X
  | false => D.U
  | true => D.V

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.base_mem_chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

private theorem FundamentalGroupVanKampen.TwoOpenCover.chart_open {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : IsOpen (D.chart i : Set X) :=
  (D.chart i).isOpen

private theorem FundamentalGroupVanKampen.TwoOpenCover.chart_cover {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : ⋃ i, (D.chart i : Set X) = Set.univ := by
  apply subset_antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩

private theorem FundamentalGroupVanKampen.TwoOpenCover.mem_U_or_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

private def FundamentalGroupVanKampen.TwoOpenCover.rawPathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical
    exact
    if h : x ∈ (D.U : Set X) ∩ D.V then
      (D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath
    else
      if hU : x ∈ D.U then (D.pathConnectedU.joinedIn D.base D.baseU x hU).somePath
      else
        (D.pathConnectedV.joinedIn D.base D.baseV x ((D.mem_U_or_V x).resolve_left hU)).somePath

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.rawPathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.rawPathTo x t ∈ D.chart i := by
  classical
    cases i with
  | false =>
    change D.rawPathTo x t ∈ D.U
    change x ∈ D.U at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dite_eq_left h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).1
    · rw [dite_eq_right h, dite_eq_left hx]
      exact JoinedIn.somePath_mem _ t
  | true =>
    change D.rawPathTo x t ∈ D.V
    change x ∈ D.V at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dite_eq_left h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).2
    · have hnU : x ∉ D.U := fun hU => h ⟨hU, hx⟩
      rw [dite_eq_right h, dite_eq_right hnU]
      exact JoinedIn.somePath_mem _ t

private def FundamentalGroupVanKampen.TwoOpenCover.pathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

@[simp]
private theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.pathTo D.base = Path.refl D.base := by
  classical simp [pathTo]

private theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

/-- The intersection of the two open sets. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.overlap {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : TopologicalSpace.Opens X :=
  D.U ⊓ D.V

/-- The base point regarded as a point of the first open set. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.baseUPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.U :=
  ⟨D.base, D.baseU⟩

/-- The base point regarded as a point of the second open set. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.baseVPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.V :=
  ⟨D.base, D.baseV⟩

/-- The base point regarded as a point of the overlap. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.baseOverlapPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.overlap :=
  ⟨D.base, D.baseU, D.baseV⟩

private abbrev FundamentalGroupVanKampen.TwoOpenCover.baseChart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.chart i :=
  ⟨D.base, D.base_mem_chart i⟩

/-- The fundamental group of the first open set at the chosen base point. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.UGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.U D.baseUPoint

/-- The fundamental group of the second open set at the chosen base point. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.VGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.V D.baseVPoint

/-- The fundamental group of the overlap at the chosen base point. -/
public
abbrev FundamentalGroupVanKampen.TwoOpenCover.OverlapGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.overlap D.baseOverlapPoint

private def FundamentalGroupVanKampen.TwoOpenCover.overlapToU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.overlap, D.U) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def FundamentalGroupVanKampen.TwoOpenCover.overlapToV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.overlap, D.V) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private def FundamentalGroupVanKampen.TwoOpenCover.inclusionU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def FundamentalGroupVanKampen.TwoOpenCover.inclusionV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def FundamentalGroupVanKampen.TwoOpenCover.overlapHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.UGroup :=
  FundamentalGroup.map D.overlapToU D.baseOverlapPoint

/-- The fundamental-group homomorphism from the overlap into the second open set. -/
public
def FundamentalGroupVanKampen.TwoOpenCover.overlapHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.VGroup :=
  FundamentalGroup.map D.overlapToV D.baseOverlapPoint

/-- The fundamental-group homomorphism induced by including the first open set. -/
public
def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

private def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

private theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHom_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.inclusionHomU.comp D.overlapHomU = D.inclusionHomV.comp D.overlapHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private def FundamentalGroupVanKampen.TwoOpenCover.Compatible {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {G : Type*} [Group G] (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) : Prop :=
  fU.comp D.overlapHomU = fV.comp D.overlapHomV

private def FundamentalGroupVanKampen.pathIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp]
private theorem FundamentalGroupVanKampen.pathIn_apply {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (t : (unitInterval)) :
    (pathIn p hx hy hp t : X) = p t :=
  rfl

@[simp]
private theorem FundamentalGroupVanKampen.pathIn_map {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

@[simp]
private theorem
    FundamentalGroupVanKampen.pathIn_refl {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (hx : x ∈ S) (hp : ∀ t, Path.refl x t ∈ S) :
    pathIn (Path.refl x) hx hx hp = Path.refl (⟨x, hx⟩ : S) := by
  ext t
  rfl

@[simp]
private theorem FundamentalGroupVanKampen.pathIn_trans {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y z : X} (p : Path x y) (q : Path y z) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (hpq : ∀ t, p.trans q t ∈ S) :
    pathIn (p.trans q) hx hz hpq = (pathIn p hx hy hp).trans (pathIn q hy hz hq) := by
  ext t
  simp only [pathIn_apply, Path.trans_apply]
  split_ifs <;> rfl

private def
    FundamentalGroupVanKampen.homotopyIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p q : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S)
    (H : Path.Homotopy p q) (hH : ∀ s, H s ∈ S) :
    Path.Homotopy (pathIn p hx hy hp) (pathIn q hx hy hq)
    where
  toFun s := ⟨H s, hH s⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' s _t ht := Subtype.ext (H.eq_fst s ht)

private theorem
    FundamentalGroupVanKampen.homotopy_trans_mem {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} {p q r : Path x y} (H : Path.Homotopy p q) (K : Path.Homotopy q r)
    (hH : ∀ s, H s ∈ S) (hK : ∀ s, K s ∈ S) : ∀ s, H.trans K s ∈ S := by
  intro s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

private theorem FundamentalGroupVanKampen.homotopy_transRefl_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ S) :
    ∀ s, Path.Homotopy.transRefl p s ∈ S := by
  intro s
  exact hp _

private theorem FundamentalGroupVanKampen.homotopy_subpathTransSubpathRefl_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpathRefl p a b c s ∈ S := by
  intro s
  let m := Set.Icc.convexComb b c s.1
  have ham : a ≤ m := hab.trans (Set.Icc.le_convexComb hbc s.1)
  have hmc : m ≤ c := Set.Icc.convexComb_le hbc s.1
  change ((p.subpath a m).trans (p.subpath m c)) s.2 ∈ S
  apply SimplyConnectedCover.trans_mem
  · exact subpath_mem_of_mem_Icc p ham (fun t ht => hp t ⟨ht.1, ht.2.trans hmc⟩)
  · exact subpath_mem_of_mem_Icc p hmc (fun t ht => hp t ⟨ham.trans ht.1, ht.2⟩)

private theorem FundamentalGroupVanKampen.homotopy_subpathTransSubpath_mem {X : Type*}
    [TopologicalSpace X] {S : Set X} {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) (hp : ∀ t ∈ Set.Icc a c, p t ∈ S) :
    ∀ s, Path.Homotopy.subpathTransSubpath p a b c s ∈ S :=
  homotopy_trans_mem _ _ (homotopy_subpathTransSubpathRefl_mem p a b c hab hbc hp)
    (homotopy_transRefl_mem _ (subpath_mem_of_mem_Icc p (hab.trans hbc) hp))

private theorem FundamentalGroupVanKampen.mem_Icc_of_subpath_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} {x y : X} (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b)
    (hp : ∀ t, p.subpath a b t ∈ S) : ∀ t ∈ Set.Icc a b, p t ∈ S := by
  have hr := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hr
  intro t ht
  exact hr ⟨t, ht, rfl⟩

private def
    FundamentalGroupVanKampen.subpathTransSubpathIn {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (ha : p a ∈ S)
    (hb : p b ∈ S) (hc : p c ∈ S) (hpab : ∀ t, p.subpath a b t ∈ S)
    (hpbc : ∀ t, p.subpath b c t ∈ S) (hpac : ∀ t, p.subpath a c t ∈ S) :
    Path.Homotopy ((pathIn (p.subpath a b) ha hb hpab).trans (pathIn (p.subpath b c) hb hc hpbc))
      (pathIn (p.subpath a c) ha hc hpac) :=
  (homotopyIn _ _ ha hc (SimplyConnectedCover.trans_mem _ _ hpab hpbc) hpac
        (Path.Homotopy.subpathTransSubpath p a b c)
        (homotopy_subpathTransSubpath_mem p a b c hab hbc
          (mem_Icc_of_subpath_mem p (hab.trans hbc) hpac))).cast
    (pathIn_trans _ _ ha hb hc hpab hpbc _) rfl

private theorem FundamentalGroupVanKampen.TwoOpenCover.hom_ext {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (f g : FundamentalGroup X D.base →* G) (hU : f.comp D.inclusionHomU = g.comp D.inclusionHomU)
    (hV : f.comp D.inclusionHomV = g.comp D.inclusionHomV) : f = g := by
  let F (x : X) : Path.Homotopic.Quotient D.base x := Path.Homotopic.Quotient.mk (D.pathTo x)
  have hlocal :
    ∀ (i : Bool) {x y : X} (p : Path x y),
      (∀ t, p t ∈ D.chart i) →
        f (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) =
          g (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) := by
    intro i x y p hp
    have hx : x ∈ D.chart i := by simpa using hp 0
    have hy : y ∈ D.chart i := by simpa using hp 1
    let l : Path D.base D.base := ((D.pathTo x).trans p).trans (D.pathTo y).symm
    have hl : ∀ t, l t ∈ D.chart i :=
      SimplyConnectedCover.trans_mem _ _
        (SimplyConnectedCover.trans_mem _ _ (D.pathTo_mem i x hx) hp)
        (fun t => D.pathTo_mem i y hy (unitInterval.symm t))
    let l' : Path (D.baseChart i) (D.baseChart i) :=
      FundamentalGroupVanKampen.pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap :
      (Path.Homotopic.Quotient.mk l').map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change
        Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
          TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)
      rw [show l'.map continuous_subtype_val = l from
          FundamentalGroupVanKampen.pathIn_map _ _ _ _]
      rfl
    cases i with
    | false =>
      have h := DFunLike.congr_fun hU (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
    | true =>
      have h := DFunLike.congr_fun hV (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
  have hall :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
        g (TriangleRegularBaseFundamentalGroup.basedLoop F q) := by
    apply
      TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover
        (fun i => (D.chart i : Set X)) D.chart_open D.chart_cover
        (fun q =>
          f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
            g (TriangleRegularBaseFundamentalGroup.basedLoop F q))
    · intro x
      simp only [TriangleRegularBaseFundamentalGroup.basedLoop_refl, map_one]
    · intro x y z p q hp hq
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_trans, map_mul, map_mul, hp, hq]
    · intro i x y p hp
      exact hlocal i p (Set.range_subset_iff.mp hp)
  have hbase : F D.base = Path.Homotopic.Quotient.refl D.base := by
    simp only [F, D.pathTo_base, Path.Homotopic.Quotient.mk_refl]
  have hsymm : (Path.Homotopic.Quotient.refl D.base).symm = Path.Homotopic.Quotient.refl D.base :=
    by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  apply MonoidHom.ext
  intro q
  simpa only [TriangleRegularBaseFundamentalGroup.basedLoop, hbase,
    Path.Homotopic.Quotient.refl_trans, hsymm, Path.Homotopic.Quotient.trans_refl] using hall q

end Mathoverflow1973

end
