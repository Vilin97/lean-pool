/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeTransition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension

/-!
# Convex flags from finite lattice-support diagrams

Finite nonempty integer supports and compatible support-preserving integral
transitions already determine a convex flag. No finite-field representation
is required. Choosing the support-generated lattice charts gives a new diagram
and a convex flag in minimal integer lattice coordinates.
-/

@[expose] public section

namespace EGZ

universe u

/-- The discrete data needed to construct a flag of finite support hulls. -/
structure LatticeSupportDiagram where
  /-- The finite ordered indexing type of the lattice support diagram. -/
  Node : Type u
  [nodeFintype : Fintype Node]
  [nodeSemilatticeSup : SemilatticeSup Node]
  [nodeOrderTop : OrderTop Node]
  /-- The number of integral coordinates attached to each node. -/
  rank : Node → ℕ
  /-- The nonempty finite lattice support attached to each node. -/
  support : (x : Node) → Finset (IntCoord (rank x))
  support_nonempty : ∀ x, (support x).Nonempty
  /-- The integral affine map transporting coordinates along an order relation between nodes. -/
  transition : {x y : Node} → x ≤ y → IntegralAffineMap (rank x) (rank y)
  transition_support : ∀ {x y : Node} (h : x ≤ y) {q},
    q ∈ support x → (transition h).integer q ∈ support y
  transition_refl : ∀ x, transition (le_refl x) = IntegralAffineMap.id (rank x)
  transition_trans : ∀ {x y z : Node} (hxy : x ≤ y) (hyz : y ≤ z),
    transition (hxy.trans hyz) = (transition hyz).comp (transition hxy)

namespace LatticeSupportDiagram

attribute [instance] nodeFintype nodeSemilatticeSup nodeOrderTop

variable (D : LatticeSupportDiagram)

/-- The rational hull of the integer support at one node. -/
noncomputable def polytope (x : D.Node) : RationalPolytope (D.rank x) :=
  RationalPolytope.ofFinsetConvexHull ((D.support x).image IntCoord.real)
    ((D.support_nonempty x).image _) (by
      intro q hq
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
      intro i
      exact ⟨(z i : ℚ), by simp⟩)

@[simp]
theorem polytope_carrier (x : D.Node) :
    (D.polytope x).carrier =
      convexHull ℝ (IntCoord.real '' (D.support x : Set (IntCoord (D.rank x)))) := by
  simp only [polytope, RationalPolytope.ofFinsetConvexHull_carrier, Finset.coe_image]

theorem transition_mem {x y : D.Node} (h : x ≤ y) {q : RealCoord (D.rank x)}
    (hq : q ∈ (D.polytope x).carrier) : (D.transition h).real q ∈ (D.polytope y).carrier := by
  rw [D.polytope_carrier] at hq
  apply convexHull_min (t := (D.transition h).real ⁻¹' (D.polytope y).carrier)
    ?_ ((D.polytope y).convex.affine_preimage _) hq
  rintro _ ⟨z, hz, rfl⟩
  change (D.transition h).real z.real ∈ (D.polytope y).carrier
  rw [(D.transition h).real_integer, D.polytope_carrier]
  exact subset_convexHull ℝ _ ⟨(D.transition h).integer z, D.transition_support h hz, rfl⟩

/-- A support diagram always defines a convex flag with standard lattices. -/
noncomputable abbrev toConvexFlag : ConvexFlag where
  Node := D.Node
  rank := D.rank
  polytope := D.polytope
  lattice x := AffineLattice.standard (D.rank x)
  transition := D.transition
  transition_mem h := D.transition_mem h
  transition_lattice h := by
    rintro q ⟨z, rfl⟩
    exact ⟨(D.transition h).integer z, ((D.transition h).real_integer z).symm⟩
  transition_refl := D.transition_refl
  transition_trans := D.transition_trans

variable (C : ∀ x, IntegerLatticeChart (D.support x))

/-- Real, integer, and modular realizations of the chosen lattice chart. -/
noncomputable def chart (x : D.Node) : IntegralAffineMap (C x).rank (D.rank x) :=
  IntegralAffineMap.ofIntAffineMap (C x).map

theorem chart_real_injective (x : D.Node) : Function.Injective (D.chart C x).real :=
  IntegralAffineMap.ofIntAffineMap_real_injective _ (C x).injective

theorem transition_affineSpan {x y : D.Node} (h : x ≤ y) :
    ∀ z ∈ D.support x, (D.transition h).toIntAffineMap z ∈
      affineSpan ℤ (D.support y : Set (IntCoord (D.rank y))) := by
  intro z hz
  exact subset_affineSpan ℤ _ (D.transition_support h hz)

/-- Express the diagram transitions in the support-generated lattice charts. -/
noncomputable def chartedTransition {x y : D.Node} (h : x ≤ y) :
    IntegralAffineMap (C x).rank (C y).rank :=
  IntegralAffineMap.ofIntAffineMap
    ((C x).transition (C y) (D.transition h).toIntAffineMap (D.transition_affineSpan h))

theorem chart_comp_transition {x y : D.Node} (h : x ≤ y) :
    (D.chart C y).comp (D.chartedTransition C h) = (D.transition h).comp (D.chart C x) := by
  apply IntegralAffineMap.ext_integer
  funext q
  exact (C x).map_transition (C y) (D.transition h).toIntAffineMap
    (D.transition_affineSpan h) q

theorem chart_transition_real {x y : D.Node} (h : x ≤ y) (q : RealCoord (C x).rank) :
    (D.chart C y).real ((D.chartedTransition C h).real q) =
      (D.transition h).real ((D.chart C x).real q) :=
  AffineMap.congr_fun (congrArg IntegralAffineMap.real (D.chart_comp_transition C h)) q

theorem chart_transition_modp {x y : D.Node} (h : x ≤ y) (p : ℕ)
    (q : FpCoord p (C x).rank) :
    (D.chart C y).modp p ((D.chartedTransition C h).modp p q) =
      (D.transition h).modp p ((D.chart C x).modp p q) :=
  AffineMap.congr_fun (congrArg (fun A ↦ A.modp p) (D.chart_comp_transition C h)) q

theorem chartedTransition_support {x y : D.Node} (h : x ≤ y) {q : IntCoord (C x).rank}
    (hq : q ∈ (C x).coordinateSupport) :
    (D.chartedTransition C h).integer q ∈ (C y).coordinateSupport := by
  apply (C y).mem_coordinateSupport.mpr
  change (C y).map ((C x).transition (C y) _ _ q) ∈ D.support y
  rw [(C x).map_transition]
  exact D.transition_support h ((C x).mem_coordinateSupport.mp hq)

theorem chartedTransition_refl (x : D.Node) :
    D.chartedTransition C (le_refl x) = IntegralAffineMap.id (C x).rank := by
  apply IntegralAffineMap.ext_integer
  funext q
  apply (C x).injective
  change (C x).map ((C x).transition (C x) _ _ q) = (C x).map q
  rw [(C x).map_transition]
  change (D.transition (le_refl x)).integer ((C x).map q) = (C x).map q
  rw [D.transition_refl]
  rfl

theorem chartedTransition_trans {x y z : D.Node} (hxy : x ≤ y) (hyz : y ≤ z) :
    D.chartedTransition C (hxy.trans hyz) =
      (D.chartedTransition C hyz).comp (D.chartedTransition C hxy) := by
  apply IntegralAffineMap.ext_integer
  funext q
  apply (C z).injective
  change (C z).map ((C x).transition (C z) _ _ q) =
    (C z).map ((C y).transition (C z) _ _ ((C x).transition (C y) _ _ q))
  rw [(C x).map_transition, (C y).map_transition, (C x).map_transition]
  exact congrFun (congrArg IntegralAffineMap.integer (D.transition_trans hxy hyz)) ((C x).map q)

/-- The same support diagram in the new lattice coordinates. -/
noncomputable abbrev rechart : LatticeSupportDiagram where
  Node := D.Node
  rank x := (C x).rank
  support x := (C x).coordinateSupport
  support_nonempty x := (C x).coordinateSupport_nonempty (D.support_nonempty x)
  transition h := D.chartedTransition C h
  transition_support h := D.chartedTransition_support C h
  transition_refl := D.chartedTransition_refl C
  transition_trans := D.chartedTransition_trans C

/-- An actual convex flag in support-generated lattice coordinates. -/
noncomputable abbrev chartedFlag : ConvexFlag := (D.rechart C).toConvexFlag

theorem chartedSupport_affineIntSpans (x : D.Node) :
    FlagDecomposition.AffineIntSpans ((D.rechart C).support x) :=
  (C x).coordinateSupport_affineIntSpans

/-- Every chart maps the new support hull onto the original support hull. -/
theorem chart_image_polytope (x : D.Node) :
    (D.chart C x).real '' ((D.rechart C).polytope x).carrier = (D.polytope x).carrier := by
  rw [(D.rechart C).polytope_carrier, D.polytope_carrier, AffineMap.image_convexHull]
  congr 1
  ext q
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(C x).map z, (C x).mem_coordinateSupport.mp hz, ((D.chart C x).real_integer z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨((C x).coordinates z).real,
      ⟨(C x).coordinates z, (C x).coordinates_mem_coordinateSupport hz, rfl⟩, ?_⟩
    rw [(D.chart C x).real_integer]
    change ((C x).map ((C x).coordinates z)).real = z.real
    rw [(C x).map_coordinates_of_mem hz]

theorem chart_mem_polytope_iff (x : D.Node) (q : RealCoord (C x).rank) :
    (D.chart C x).real q ∈ (D.polytope x).carrier ↔ q ∈ ((D.rechart C).polytope x).carrier := by
  rw [← D.chart_image_polytope C x]
  exact (D.chart_real_injective C x).mem_set_image

/-- Chart box bounds transfer integer-point bounds on the original support
hulls to integer-point bounds on the new hulls. -/
theorem charted_polytope_bound {K B : D.Node → ℕ}
    (hD : ∀ x (z : IntCoord (D.rank x)),
      z.real ∈ (D.polytope x).carrier → latticeSupNorm z ≤ K x)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ B x) :
    ∀ x (q : IntCoord (C x).rank),
      q.real ∈ ((D.rechart C).polytope x).carrier → latticeSupNorm q ≤ B x := by
  intro x q hq
  apply hC
  apply hD
  change ((D.chart C x).integer q).real ∈ (D.polytope x).carrier
  rw [← (D.chart C x).real_integer]
  exact (D.chart_mem_polytope_iff C x q.real).mpr hq

end LatticeSupportDiagram
end EGZ
