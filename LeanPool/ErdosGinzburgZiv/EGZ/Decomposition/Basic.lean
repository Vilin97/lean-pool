/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.ConvexHull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Flag decompositions

This file contains the definitions from the beginning of Section 4 of the
paper.  The ambient finite-field space and every lattice fibre use the
coordinate models from `EGZ.Convex.Coordinate`.

There are two different lifted weights.  `hat` is cumulative over all nodes
below `x`; `localLift` uses only the summand based at `x`.  Proper-point
generators are defined from `localLift`.  This distinction is the correction
integrated into the current version of the paper.
-/

open scoped BigOperators

namespace EGZ

universe u

/-! ## Slabs, thinness, and thickness -/

/-- A residue has an integer representative in the interval `[-K, K]`.

This definition remains meaningful without a large-prime hypothesis.  Such a
hypothesis is needed only when uniqueness of the representative is used. -/
def HasBoundedRepresentative (p K : ℕ) (a : ZMod p) : Prop :=
  ∃ z : ℤ, z.natAbs ≤ K ∧ (z : ZMod p) = a

/-- The `K`-slab cut out by an affine functional on `𝔽_p^d`. -/
def slab {p d : ℕ} (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (K : ℕ) :
    Set (FpCoord p d) :=
  {v | HasBoundedRepresentative p K (ξ v)}

/-- The mass of a natural-valued function on a subset of a finite type. -/
noncomputable def natMassOn {α : Type*} [Fintype α] (w : α → ℕ) (S : Set α) : ℕ := by
  classical
  exact ∑ a, if a ∈ S then w a else 0

/-- The total mass of a natural-valued function on a finite type. -/
noncomputable def natMass {α : Type*} [Fintype α] (w : α → ℕ) : ℕ :=
  ∑ a, w a

/-- Mass of an `NNReal`-valued function on a subset of a finite type. -/
noncomputable def nnrealMassOn {α : Type*} [Fintype α]
    (w : α → NNReal) (S : Set α) : NNReal := by
  classical
  exact ∑ a, if a ∈ S then w a else 0

/-- Total mass of an `NNReal`-valued function on a finite type. -/
noncomputable def nnrealMass {α : Type*} [Fintype α] (w : α → NNReal) : NNReal :=
  ∑ a, w a

/-- Definition 4.1 for the nonnegative real weights used in the paper. -/
def IsThinAlongNNReal {p d : ℕ} [NeZero p] (w : FpCoord p d → NNReal)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (K : ℕ) (ε : ℝ) : Prop :=
  (1 - ε) * (nnrealMass w : ℝ) ≤ (nnrealMassOn w (slab ξ K) : ℝ)

/-- Natural-valued specialization used by flag decompositions and
Theorem 4.13. -/
def IsThinAlong {p d : ℕ} [NeZero p] (w : FpCoord p d → ℕ)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (K : ℕ) (ε : ℝ) : Prop :=
  IsThinAlongNNReal (fun v ↦ (w v : NNReal)) ξ K ε

/-- Thickness is the negation of thinness, as in Definition `tt`. -/
def IsThickAlong {p d : ℕ} [NeZero p] (w : FpCoord p d → ℕ)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (K : ℕ) (ε : ℝ) : Prop :=
  ¬ IsThinAlong w ξ K ε

/-! ## Representations of a lattice flag over `𝔽_p` -/

/-- An `𝔽_p`-representation of a convex lattice flag in the ambient affine
space `𝔽_p^d`.

The maps are stored as affine maps on the ambient coordinate space and are
required to be surjective only after restriction to `space x`.  Every affine
map on an affine subspace of this finite-dimensional space extends to the
ambient space, while this representation avoids dependent subtype maps in
all fibre sums below. -/
structure FpRepresentation (p d : ℕ) (F : ConvexFlag) where
  /-- Affine subspace over the finite field represented at each flag node. -/
  space : F.Node → AffineSubspace (ZMod p) (FpCoord p d)
  /-- Affine coordinate map for each represented flag node. -/
  map : (x : F.Node) → FpCoord p d →ᵃ[ZMod p] FpCoord p (F.rank x)
  space_mono : ∀ {x y : F.Node}, x ≤ y → space x ≤ space y
  map_surjective : ∀ x, Set.SurjOn (map x) (space x : Set (FpCoord p d)) Set.univ
  compatible : ∀ {x y : F.Node} (h : x ≤ y) {v : FpCoord p d},
    v ∈ space x → map y v = (F.transition h).modp p (map x v)
  lattice_eq_standard : ∀ (x : F.Node) (q : RealCoord (F.rank x)),
    q ∈ F.lattice x ↔ EGZ.IsIntegral q

namespace FpRepresentation

/-- An affine functional is nonconstant on the fibres of the representation
at `x` if two points in one fibre receive different values. -/
def NonconstantOnFibers {p d : ℕ} {F : ConvexFlag}
    (R : FpRepresentation p d F) (x : F.Node)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) : Prop :=
  ∃ v w, v ∈ R.space x ∧ w ∈ R.space x ∧
    R.map x v = R.map x w ∧ ξ v ≠ ξ w

end FpRepresentation

/-! ## Coordinate lifts -/

/-- Sup norm in the chosen affine-lattice coordinates. -/
def latticeSupNorm {n : ℕ} (z : IntCoord n) : ℕ :=
  Finset.univ.sup fun i ↦ (z i).natAbs

/-- A lattice coordinate lies in the centered representative box modulo
`p`. -/
def IsCenteredLift (p : ℕ) {n : ℕ} (z : IntCoord n) : Prop :=
  latticeSupNorm z ≤ (p - 1) / 2

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- Sum of all local summands at an ambient point. -/
noncomputable def retainedWeight (pieces : F.Node → FpCoord p d → ℕ)
    (v : FpCoord p d) : ℕ :=
  ∑ x, pieces x v

/-- The cumulative function `f_{≼ x}`. -/
noncomputable def cumulativeWeight (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) (v : FpCoord p d) : ℕ := by
  classical
  exact ∑ y, if y ≤ x then pieces y v else 0

/-- Push a finite weight through an affine map whose target rank may vary. -/
noncomputable def affineFibreMass {n : ℕ} (w : FpCoord p d → ℕ)
    (φ : FpCoord p d → FpCoord p n) (c : FpCoord p n) : ℕ := by
  classical
  exact ∑ v, if φ v = c then w v else 0

/-- The local centered lift `f_x°`, using only the summand based at `x`. -/
noncomputable def localLift (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) : ℕ := by
  classical
  exact if IsCenteredLift p q then
      affineFibreMass (pieces x) (R.map x) (q.mod p)
    else 0

/-- The cumulative centered lift `hat f_x`. -/
noncomputable def hat (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) : ℕ := by
  classical
  exact if IsCenteredLift p q then
      affineFibreMass (cumulativeWeight pieces x) (R.map x) (q.mod p)
    else 0

/-- Corrected local generating points.  A generator based at `x` is selected
by positive `localLift`, not by cumulative `hat`. -/
def omegaZero (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) : Set F.Point :=
  {q | ∃ z : IntCoord (F.rank q.base),
    z.real = q.val ∧ localLift R pieces q.base z ≠ 0}

/-- Proper points associated with local decomposition data. -/
def omega (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) : Set F.Point :=
  F.convexHull (omegaZero R pieces)

/-- Proper points whose coordinate at `x` lies on a given face. -/
def pointsOnFace (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (Γ : (F.polytope x).Face) : Set F.Point :=
  {q | q ∈ omega R pieces ∧
    ∃ h : q.base ≤ x, q.coord h ∈ Γ.carrier}

/-- Visibility before packaging the data into a `FlagDecomposition`. -/
def VisibleFace (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (Γ : (F.polytope x).Face) : Prop :=
  (pointsOnFace R pieces x Γ).Nonempty

/-- The proper-point set is convex-closed because it is itself defined as a
flag convex hull. -/
theorem omega_convex_closed (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) :
    F.convexHull (omega R pieces) ⊆ omega R pieces := by
  unfold omega
  exact ConvexFlag.convexHull_convex_closed F _

end FlagDecompositionRaw

/-! ## Flag decompositions -/

/-- A natural-valued flag decomposition of `f`.

The finite lifted support is stored explicitly.  Besides making the later
mass and gap definitions computationally finite, the accompanying fields
record the support/polytope invariant and rule out inactive nodes with empty
cumulative support. -/
structure FlagDecomposition (p d : ℕ) [NeZero p] (f : FpCoord p d → ℕ) where
  /-- Convex flag supporting the decomposition. -/
  flag : ConvexFlag
  /-- Finite-field representation of the decomposition flag. -/
  representation : FpRepresentation p d flag
  /-- Natural-valued weight assigned locally at each flag node. -/
  localWeight : flag.Node → FpCoord p d → ℕ
  local_supported : ∀ x v, localWeight x v ≠ 0 → v ∈ representation.space x
  retained_le : ∀ v, FlagDecompositionRaw.retainedWeight localWeight v ≤ f v
  /-- Finite integral support of the lifted weight at each node. -/
  liftedSupport : (x : flag.Node) → Finset (IntCoord (flag.rank x))
  liftedSupport_spec : ∀ x q,
    q ∈ liftedSupport x ↔ FlagDecompositionRaw.hat representation localWeight x q ≠ 0
  liftedSupport_nonempty : ∀ x, (liftedSupport x).Nonempty
  polytope_eq_liftedSupport : ∀ x,
    (flag.polytope x).carrier =
      convexHull ℝ (IntCoord.real '' (↑(liftedSupport x) : Set (IntCoord (flag.rank x))))
  faces_visible : ∀ x (Γ : (flag.polytope x).Face),
    FlagDecompositionRaw.VisibleFace representation localWeight x Γ

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Total retained function `f^Φ`. -/
noncomputable def retainedWeight (Φ : FlagDecomposition p d f) : FpCoord p d → ℕ :=
  FlagDecompositionRaw.retainedWeight Φ.localWeight

/-- Cumulative function `f_{≼ x}`. -/
noncomputable def cumulativeWeight (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) : FpCoord p d → ℕ :=
  FlagDecompositionRaw.cumulativeWeight Φ.localWeight x

/-- Local centered lifted function `f_x°`. -/
noncomputable def localLift (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) :
    IntCoord (Φ.flag.rank x) → ℕ :=
  FlagDecompositionRaw.localLift Φ.representation Φ.localWeight x

/-- Cumulative centered lifted function `hat f_x`. -/
noncomputable def hat (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) :
    IntCoord (Φ.flag.rank x) → ℕ :=
  FlagDecompositionRaw.hat Φ.representation Φ.localWeight x

/-- Total retained mass `f^Φ(V)`. -/
noncomputable def retainedMass (Φ : FlagDecomposition p d f) : ℕ :=
  natMass Φ.retainedWeight

/-- Mass of `hat f_x` over lattice points whose real coordinates lie in
`S`.  The stored support makes this a finite sum. -/
noncomputable def liftedMassOn (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (S : Set (RealCoord (Φ.flag.rank x))) : ℕ := by
  classical
  exact ∑ q ∈ Φ.liftedSupport x, if q.real ∈ S then Φ.hat x q else 0

/-- Corrected set `Ω₀` of local generating points. -/
def omegaZero (Φ : FlagDecomposition p d f) : Set Φ.flag.Point :=
  FlagDecompositionRaw.omegaZero Φ.representation Φ.localWeight

/-- Corrected proper-point set `Ω = conv Ω₀`. -/
def omega (Φ : FlagDecomposition p d f) : Set Φ.flag.Point :=
  FlagDecompositionRaw.omega Φ.representation Φ.localWeight

/-- The corrected proper points, packaged with convex closure. -/
def properPoints (Φ : FlagDecomposition p d f) : Φ.flag.ProperPointSet where
  carrier := Φ.omega
  convex_closed := FlagDecompositionRaw.omega_convex_closed
    Φ.representation Φ.localWeight

/-- The paper's pointwise local mass `f°` on flag points.  The existential
form avoids choosing integer coordinates; realification is injective, so the
value is unambiguous whenever it is nonzero. -/
def HasLocalPointMass (Φ : FlagDecomposition p d f) (q : Φ.flag.Point)
    (m : ℕ) : Prop :=
  ∃ z : IntCoord (Φ.flag.rank q.base), z.real = q.val ∧ Φ.localLift q.base z = m

/-- Points of `Ω` lying over the face `Γ` at `x`. -/
def pointsOnFace (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Set Φ.flag.Point :=
  FlagDecompositionRaw.pointsOnFace Φ.representation Φ.localWeight x Γ

/-- A face is visible when a proper point lies over it. -/
def IsVisibleFace (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Prop :=
  (Φ.pointsOnFace x Γ).Nonempty

/-- The finite set of bases used to define `x_Γ`. -/
noncomputable def faceBases (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Finset Φ.flag.Node := by
  classical
  exact Finset.univ.filter fun y ↦
    ∃ q, q ∈ Φ.pointsOnFace x Γ ∧ q.base = y

private theorem faceBases_nonempty (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : (Φ.faceBases x Γ).Nonempty := by
  classical
  obtain ⟨q, hq⟩ := Φ.faces_visible x Γ
  refine ⟨q.base, ?_⟩
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨q, hq, rfl⟩

/-- The element `x_Γ`: the supremum of the bases of proper points over a
face.  Every face of a flag decomposition is visible. -/
noncomputable def faceIndex (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Φ.flag.Node :=
  (Φ.faceBases x Γ).sup' (faceBases_nonempty Φ x Γ) id

theorem faceIndex_le (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Φ.faceIndex x Γ ≤ x := by
  classical
  apply Finset.sup'_le
  intro y hy
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact hq.2.choose

/-- A face is realized when the polytope at `x_Γ` maps into it. -/
def IsRealizedFace (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Prop :=
  ∀ q ∈ (Φ.flag.polytope (Φ.faceIndex x Γ)).carrier,
    (Φ.flag.transition (Φ.faceIndex_le x Γ)).real q ∈ Γ.carrier

/-- An element is reduced when some proper point is based exactly there. -/
def IsReducedElement (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) : Prop :=
  ∃ q, q ∈ Φ.omega ∧ q.base = x

/-- Every element of the decomposition is reduced. -/
def IsReduced (Φ : FlagDecomposition p d f) : Prop :=
  ∀ x, Φ.IsReducedElement x

/-- A finite set of lattice points affinely generates the full coordinate
lattice over `ℤ`. -/
def AffineIntSpans {n : ℕ} (S : Finset (IntCoord n)) : Prop :=
  ∀ z : IntCoord n, ∃ c : IntCoord n →₀ ℤ,
    c.support ⊆ S ∧
      (∑ q ∈ c.support, c q) = 1 ∧
      (∑ q ∈ c.support, c q • q) = z

/-- Minimality of the finite-field affine spaces and affine lattices. -/
def IsMinimal (Φ : FlagDecomposition p d f) : Prop :=
  ∀ x,
    Φ.representation.space x =
        affineSpan (ZMod p) {v | Φ.cumulativeWeight x v ≠ 0} ∧
      AffineIntSpans (Φ.liftedSupport x)

/-- The chosen affine-lattice coordinates are bounded by `K` on every
lattice point of every node polytope. -/
def IsKBounded (Φ : FlagDecomposition p d f) (K : Φ.flag.Node → ℕ) : Prop :=
  ∀ x (z : IntCoord (Φ.flag.rank x)),
    z.real ∈ (Φ.flag.polytope x).carrier → latticeSupNorm z ≤ K x

/-- An `ε`-large face, Definition `largef`. -/
def IsLargeFace (Φ : FlagDecomposition p d f) (ε : ℝ) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) : Prop :=
  ε * (Φ.retainedMass : ℝ) ≤ (Φ.liftedMassOn x Γ.carrier : ℝ) ∧
    ∀ Γ' : (Φ.flag.polytope x).Face, Γ'.carrier ⊂ Γ.carrier →
      (Φ.liftedMassOn x Γ'.carrier : ℝ) ≤
        (1 - ε) * (Φ.liftedMassOn x Γ.carrier : ℝ)

/-- An `ε`-large flag element. -/
def IsLargeElement (Φ : FlagDecomposition p d f) (ε : ℝ)
    (x : Φ.flag.Node) : Prop :=
  ε * (Φ.retainedMass : ℝ) ≤
    (Φ.liftedMassOn x (Φ.flag.polytope x).carrier : ℝ)

/-- The minimum positive cumulative lifted mass at a node. -/
noncomputable def gap (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) : ℕ :=
  (Φ.liftedSupport x).image (Φ.hat x) |>.min'
    ((Φ.liftedSupport_nonempty x).image (Φ.hat x))

/-- Completeness of one element: every affine functional which varies on a
representation fibre sees a thick cumulative weight. -/
def IsCompleteElement (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (t : ℕ) (δ : ℝ) : Prop :=
  ∀ ξ : FpCoord p d →ᵃ[ZMod p] ZMod p,
    Φ.representation.NonconstantOnFibers x ξ →
      IsThickAlong (Φ.cumulativeWeight x) ξ t δ

/-- A `(T, ε, δ)`-complete flag decomposition. -/
def IsComplete (Φ : FlagDecomposition p d f) (T : Φ.flag.Node → ℕ)
    (ε δ : ℝ) : Prop :=
  Φ.IsMinimal ∧ Φ.IsReduced ∧
    (∀ x, Φ.IsLargeElement ε x → Φ.IsCompleteElement x (T x) δ) ∧
    (∀ x (Γ : (Φ.flag.polytope x).Face),
      Φ.IsLargeFace ε x Γ → Φ.IsRealizedFace x Γ)

end FlagDecomposition

/-- A growing function is monotone and strictly exceeds the identity. -/
def IsGrowing (g : ℕ → ℕ) : Prop :=
  Monotone g ∧ ∀ n, n < g n

end EGZ
