/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeTransition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningData

/-!
# The convex flag in minimal lattice coordinates

Choose a support-generated integer lattice chart at every node. Rebuilding
the support polytopes and factoring the old transitions through these charts
gives a convex flag on the same node poset with standard coordinate lattices.
-/

@[expose] public section

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- The original local weights as a collection of surviving weights. -/
noncomputable abbrev originalWeights (Φ : FlagDecomposition p d f) : PrunedWeights Φ where
  weight := Φ.localWeight
  weight_le _ _ := le_rfl
  nonzero := by
    classical
    obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty ⊤
    have hq' := (Φ.liftedSupport_spec ⊤ q).mp hq
    by_contra h
    have hall : ∀ x v, Φ.localWeight x v = 0 := by simpa using h
    apply hq'
    simp [FlagDecompositionRaw.hat, FlagDecompositionRaw.affineFibreMass,
      FlagDecompositionRaw.cumulativeWeight, hall]

/-- Original transitions carry each lifted support into the upper lifted
support, with no additional prime or coordinate-bound hypothesis. -/
theorem transition_mem_liftedSupport (Φ : FlagDecomposition p d f)
    {x y : Φ.flag.Node} (h : x ≤ y) {q : IntCoord (Φ.flag.rank x)}
    (hq : q ∈ Φ.liftedSupport x) :
    (Φ.flag.transition h).integer q ∈ Φ.liftedSupport y := by
  rw [Φ.liftedSupport_eq_hatSupport] at hq ⊢
  exact Φ.originalWeights.transition_mem_support h hq

namespace Rechart

variable (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))

/-- The coordinate chart at a node, with real and modular realizations. -/
noncomputable def chart (x : Φ.flag.Node) : IntegralAffineMap (C x).rank (Φ.flag.rank x) :=
  IntegralAffineMap.ofIntAffineMap (C x).map

theorem chart_real_injective (x : Φ.flag.Node) : Function.Injective (chart Φ C x).real :=
  IntegralAffineMap.ofIntAffineMap_real_injective _ (C x).injective

/-- The new node polytope is the hull of its support in the new coordinates. -/
noncomputable def polytope (x : Φ.flag.Node) : RationalPolytope (C x).rank :=
  RationalPolytope.ofFinsetConvexHull ((C x).coordinateSupport.image IntCoord.real)
    (((C x).coordinateSupport_nonempty (Φ.liftedSupport_nonempty x)).image _)
    (by
      intro q hq
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
      intro i
      exact ⟨(z i : ℚ), by simp⟩)

@[simp]
theorem polytope_carrier (x : Φ.flag.Node) :
    (polytope Φ C x).carrier =
      convexHull ℝ (IntCoord.real '' ((C x).coordinateSupport : Set (IntCoord (C x).rank))) := by
  simp only [polytope, RationalPolytope.ofFinsetConvexHull_carrier, Finset.coe_image]

/-- The chart maps the new polytope onto the original one. -/
theorem chart_image_polytope (x : Φ.flag.Node) :
    (chart Φ C x).real '' (polytope Φ C x).carrier = (Φ.flag.polytope x).carrier := by
  rw [polytope_carrier, AffineMap.image_convexHull, Φ.polytope_eq_liftedSupport]
  congr 1
  ext q
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(C x).map z, (C x).mem_coordinateSupport.mp hz,
      ((chart Φ C x).real_integer z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨((C x).coordinates z).real,
      ⟨(C x).coordinates z, (C x).coordinates_mem_coordinateSupport hz, rfl⟩, ?_⟩
    rw [(chart Φ C x).real_integer]
    change ((C x).map ((C x).coordinates z)).real = z.real
    rw [(C x).map_coordinates_of_mem hz]

@[simp]
theorem chart_mem_polytope_iff (x : Φ.flag.Node) (q : RealCoord (C x).rank) :
    (chart Φ C x).real q ∈ (Φ.flag.polytope x).carrier ↔ q ∈ (polytope Φ C x).carrier := by
  rw [← chart_image_polytope Φ C x]
  exact (chart_real_injective Φ C x).mem_set_image

/-- The uniform chart box bounds transfer boundedness of the original
decomposition to every lattice point of each new polytope. -/
theorem polytope_bound {K B : Φ.flag.Node → ℕ} (hΦ : Φ.IsKBounded K)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ B x) :
    ∀ x (q : IntCoord (C x).rank),
      q.real ∈ (polytope Φ C x).carrier → latticeSupNorm q ≤ B x := by
  intro x q hq
  apply hC
  apply hΦ
  change ((chart Φ C x).integer q).real ∈ (Φ.flag.polytope x).carrier
  rw [← (chart Φ C x).real_integer]
  exact (chart_mem_polytope_iff Φ C x q.real).mpr hq

/-- Support membership supplies the target-lattice condition for factoring
the original transition through the chosen charts. -/
theorem transition_support {x y : Φ.flag.Node} (h : x ≤ y) :
    ∀ z ∈ Φ.liftedSupport x, (Φ.flag.transition h).toIntAffineMap z ∈
      affineSpan ℤ (Φ.liftedSupport y : Set (IntCoord (Φ.flag.rank y))) := by
  intro z hz
  exact subset_affineSpan ℤ _ (Φ.transition_mem_liftedSupport h hz)

/-- Original transitions expressed in the chosen lattice charts. -/
noncomputable def transition {x y : Φ.flag.Node} (h : x ≤ y) :
    IntegralAffineMap (C x).rank (C y).rank :=
  IntegralAffineMap.ofIntAffineMap
    ((C x).transition (C y) (Φ.flag.transition h).toIntAffineMap (transition_support Φ h))

/-- Chart maps intertwine new and old transitions as integral-affine maps. -/
theorem chart_comp_transition {x y : Φ.flag.Node} (h : x ≤ y) :
    (chart Φ C y).comp (transition Φ C h) = (Φ.flag.transition h).comp (chart Φ C x) := by
  apply IntegralAffineMap.ext_integer
  funext q
  exact (C x).map_transition (C y) (Φ.flag.transition h).toIntAffineMap
    (transition_support Φ h) q

theorem chart_transition_real {x y : Φ.flag.Node} (h : x ≤ y)
    (q : RealCoord (C x).rank) :
    (chart Φ C y).real ((transition Φ C h).real q) =
      (Φ.flag.transition h).real ((chart Φ C x).real q) :=
  AffineMap.congr_fun (congrArg IntegralAffineMap.real (chart_comp_transition Φ C h)) q

theorem chart_transition_modp {x y : Φ.flag.Node} (h : x ≤ y) (r : ℕ)
    (q : FpCoord r (C x).rank) :
    (chart Φ C y).modp r ((transition Φ C h).modp r q) =
      (Φ.flag.transition h).modp r ((chart Φ C x).modp r q) :=
  AffineMap.congr_fun
    (congrArg (fun A ↦ A.modp r) (chart_comp_transition Φ C h)) q

theorem transition_mem {x y : Φ.flag.Node} (h : x ≤ y) {q : RealCoord (C x).rank}
    (hq : q ∈ (polytope Φ C x).carrier) :
    (transition Φ C h).real q ∈ (polytope Φ C y).carrier := by
  apply (chart_mem_polytope_iff Φ C y _).mp
  rw [chart_transition_real]
  exact Φ.flag.transition_mem h ((chart_mem_polytope_iff Φ C x q).mpr hq)

theorem transition_refl (x : Φ.flag.Node) :
    transition Φ C (le_refl x) = IntegralAffineMap.id (C x).rank := by
  apply IntegralAffineMap.ext_integer
  funext q
  apply (C x).injective
  change (C x).map ((C x).transition (C x) _ _ q) = (C x).map q
  rw [(C x).map_transition]
  change (Φ.flag.transition (le_refl x)).integer ((C x).map q) = (C x).map q
  rw [Φ.flag.transition_refl]
  rfl

theorem transition_trans {x y z : Φ.flag.Node} (hxy : x ≤ y) (hyz : y ≤ z) :
    transition Φ C (hxy.trans hyz) = (transition Φ C hyz).comp (transition Φ C hxy) := by
  apply IntegralAffineMap.ext_integer
  funext q
  apply (C z).injective
  change (C z).map ((C x).transition (C z) _ _ q) =
    (C z).map ((C y).transition (C z) _ _ ((C x).transition (C y) _ _ q))
  rw [(C x).map_transition, (C y).map_transition, (C x).map_transition]
  exact congrFun (congrArg IntegralAffineMap.integer (Φ.flag.transition_trans hxy hyz))
    ((C x).map q)

/-- The convex flag obtained by replacing every fibre with its
support-generated lattice coordinates. -/
noncomputable abbrev flag : ConvexFlag where
  Node := Φ.flag.Node
  rank x := (C x).rank
  polytope := polytope Φ C
  lattice x := AffineLattice.standard (C x).rank
  transition h := transition Φ C h
  transition_mem h := transition_mem Φ C h
  transition_lattice h := by
    rintro q ⟨z, rfl⟩
    exact ⟨(transition Φ C h).integer z, ((transition Φ C h).real_integer z).symm⟩
  transition_refl := transition_refl Φ C
  transition_trans hxy hyz := transition_trans Φ C hxy hyz

end Rechart

end EGZ.FlagDecomposition
