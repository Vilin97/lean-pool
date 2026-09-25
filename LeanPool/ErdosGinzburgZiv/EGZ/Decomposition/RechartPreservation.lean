/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartDecomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation

/-!
# Properties preserved by changing lattice coordinates

The chart and its affine left inverse identify the node polytopes and their
proper points.  These maps preserve reducedness, realized faces, and
completeness of individual elements.
-/

@[expose] public section

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))

/-- An affine inverse of the real chart, extended to the old ambient space. -/
noncomputable def inverseChart (x : Φ.flag.Node) :
    RealCoord (Φ.flag.rank x) →ᵃ[ℝ] RealCoord (C x).rank :=
  affineLeftInverse (chart Φ C x).real

@[simp]
theorem inverseChart_chart (x : Φ.flag.Node) (q : RealCoord (C x).rank) :
    inverseChart Φ C x ((chart Φ C x).real q) = q :=
  affineLeftInverse_apply _ (chart_real_injective Φ C x) q

theorem chart_inverseChart (x : Φ.flag.Node) (q : RealCoord (Φ.flag.rank x))
    (hq : q ∈ (Φ.flag.polytope x).carrier) :
    (chart Φ C x).real (inverseChart Φ C x q) = q := by
  apply affineLeftInverse_retract _ (chart_real_injective Φ C x)
  rw [← chart_image_polytope Φ C x] at hq
  obtain ⟨r, _, rfl⟩ := hq
  exact ⟨r, rfl⟩

theorem inverseChart_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (inverseChart Φ C x) (Φ.flag.polytope x).carrier (polytope Φ C x).carrier := by
  intro q hq
  apply (chart_mem_polytope_iff Φ C x _).mp
  rw [chart_inverseChart Φ C x q hq]
  exact hq

theorem chart_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (chart Φ C x).real (polytope Φ C x).carrier (Φ.flag.polytope x).carrier :=
  fun _ hq ↦ (chart_mem_polytope_iff Φ C x _).mpr hq

/-- Inverse charts commute with transitions on the old source polytope. -/
theorem inverseChart_transition {x y : Φ.flag.Node} (h : x ≤ y)
    (q : RealCoord (Φ.flag.rank x)) (hq : q ∈ (Φ.flag.polytope x).carrier) :
    inverseChart Φ C y ((Φ.flag.transition h).real q) =
      (transition Φ C h).real (inverseChart Φ C x q) := by
  apply chart_real_injective Φ C y
  rw [chart_inverseChart Φ C y _ (Φ.flag.transition_mem h hq), chart_transition_real,
    chart_inverseChart Φ C x q hq]

/-- Map a point in the new coordinates to its original flag point. -/
noncomputable def forwardPoint (q : (flag Φ C).Point) : Φ.flag.Point :=
  q.map (SupHom.id _) (fun x ↦ (chart Φ C x).real) (chart_mem_polytope Φ C)

/-- Express an original flag point in the new coordinates. -/
noncomputable def inversePoint (q : Φ.flag.Point) : (flag Φ C).Point :=
  q.map (SupHom.id _) (inverseChart Φ C) (inverseChart_mem_polytope Φ C)

@[simp]
theorem inversePoint_forwardPoint (q : (flag Φ C).Point) :
    inversePoint Φ C (forwardPoint Φ C q) = q := by
  cases q with
  | mk x v hv =>
    change (⟨x, inverseChart Φ C x ((chart Φ C x).real v), _⟩ : (flag Φ C).Point) = ⟨x, v, hv⟩
    congr 1
    exact inverseChart_chart Φ C x v

@[simp]
theorem forwardPoint_inversePoint (q : Φ.flag.Point) :
    forwardPoint Φ C (inversePoint Φ C q) = q := by
  cases q with
  | mk x v hv =>
    change (⟨x, (chart Φ C x).real (inverseChart Φ C x v), _⟩ : Φ.flag.Point) = ⟨x, v, hv⟩
    congr 1
    exact chart_inverseChart Φ C x v hv

variable [Fact p.Prime] (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

include hp hinj hcenter

theorem forwardPoint_mem_omegaZero {q : (flag Φ C).Point}
    (hq : q ∈ (decomposition Φ C hp hinj hcenter).omegaZero) :
    forwardPoint Φ C q ∈ Φ.omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  refine ⟨(C q.base).map z, ?_, ?_⟩
  · change ((C q.base).map z).real = (chart Φ C q.base).real q.val
    rw [← hz, (chart Φ C q.base).real_integer]
    rfl
  · change (decomposition Φ C hp hinj hcenter).localLift q.base z ≠ 0 at hw
    rwa [decomposition_localLift] at hw

theorem inversePoint_mem_omegaZero {q : Φ.flag.Point} (hq : q ∈ Φ.omegaZero) :
    inversePoint Φ C q ∈ (decomposition Φ C hp hinj hcenter).omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  have hw' : Φ.localLift q.base z ≠ 0 := hw
  have hzS : z ∈ Φ.liftedSupport q.base :=
    (Φ.liftedSupport_spec q.base z).mpr
      (ne_of_gt ((Nat.pos_of_ne_zero hw').trans_le (Φ.localLift_le_hat q.base z)))
  have hcoords := (C q.base).map_coordinates_of_mem hzS
  refine ⟨(C q.base).coordinates z, ?_, ?_⟩
  · change ((C q.base).coordinates z).real = inverseChart Φ C q.base q.val
    have hreal : (chart Φ C q.base).real ((C q.base).coordinates z).real = z.real := by
      rw [(chart Φ C q.base).real_integer]
      exact congrArg IntCoord.real hcoords
    rw [← hz, ← hreal, inverseChart_chart]
  · change (decomposition Φ C hp hinj hcenter).localLift q.base ((C q.base).coordinates z) ≠ 0
    rw [decomposition_localLift, hcoords]
    exact hw'

/-- Forward charts preserve the full proper-point set. -/
theorem forwardPoint_mem_omega {q : (flag Φ C).Point}
    (hq : q ∈ (decomposition Φ C hp hinj hcenter).omega) :
    forwardPoint Φ C q ∈ Φ.omega := by
  obtain ⟨n, points, weight, hpoints, hcomb⟩ := hq
  refine ⟨n, fun i ↦ forwardPoint Φ C (points i), weight,
    fun i ↦ forwardPoint_mem_omegaZero Φ C hp hinj hcenter (hpoints i), ?_⟩
  exact hcomb.map (F := flag Φ C) (G := Φ.flag) (SupHom.id _) (fun x ↦ (chart Φ C x).real)
    (chart_mem_polytope Φ C) (chart_transition_real Φ C)

/-- The inverse charts preserve proper points even though their transition
commutation is only required on the polytopes. -/
theorem inversePoint_mem_omega {q : Φ.flag.Point} (hq : q ∈ Φ.omega) :
    inversePoint Φ C q ∈ (decomposition Φ C hp hinj hcenter).omega := by
  obtain ⟨n, points, weight, hpoints, hcomb⟩ := hq
  refine ⟨n, fun i ↦ inversePoint Φ C (points i), weight,
    fun i ↦ inversePoint_mem_omegaZero Φ C hp hinj hcenter (hpoints i), ?_⟩
  exact hcomb.map_on_polytope (F := Φ.flag) (G := flag Φ C) (SupHom.id _) (inverseChart Φ C)
    (inverseChart_mem_polytope Φ C) (inverseChart_transition Φ C)

/-- The new decomposition is a subdivision of the old one through its
coordinate charts. -/
noncomputable def subdivisionMap :
    SubdivisionMap Φ (decomposition Φ C hp hinj hcenter) :=
  SubdivisionMap.ofLocalGenerators (SupHom.id _) (fun x ↦ (chart Φ C x).real)
    (chart_mem_polytope Φ C) (chart_transition_real Φ C)
    (fun _ hq ↦ forwardPoint_mem_omegaZero Φ C hp hinj hcenter hq)

/-- Recharting preserves every base occurring among the proper points. -/
theorem decomposition_isReduced (hΦ : Φ.IsReduced) :
    (decomposition Φ C hp hinj hcenter).IsReduced := by
  intro x
  obtain ⟨q, hq, hbase⟩ := hΦ x
  exact ⟨inversePoint Φ C q, inversePoint_mem_omega Φ C hp hinj hcenter hq, hbase⟩

theorem decomposition_isReduced_iff :
    (decomposition Φ C hp hinj hcenter).IsReduced ↔ Φ.IsReduced := by
  constructor
  · intro hnew x
    obtain ⟨q, hq, hbase⟩ := hnew x
    exact ⟨forwardPoint Φ C q, forwardPoint_mem_omega Φ C hp hinj hcenter hq, hbase⟩
  · exact decomposition_isReduced Φ C hp hinj hcenter

omit hp hinj hcenter [Fact p.Prime] in
/-- Every old face has a nonempty pullback under a chart. -/
theorem face_preimage_nonempty (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    ((polytope Φ C x).carrier ∩ (chart Φ C x).real ⁻¹' Γ.carrier).Nonempty := by
  obtain ⟨q, hq⟩ := Γ.nonempty
  refine ⟨inverseChart Φ C x q, inverseChart_mem_polytope Φ C x (Γ.subset_polytope hq), ?_⟩
  change (chart Φ C x).real (inverseChart Φ C x q) ∈ Γ.carrier
  rw [chart_inverseChart Φ C x q (Γ.subset_polytope hq)]
  exact hq

/-- Every previously realized face is still realized in the new coordinates. -/
theorem decomposition_isRealizedFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (hΓ : Φ.IsRealizedFace x Γ) :
    (decomposition Φ C hp hinj hcenter).IsRealizedFace x
      ((subdivisionMap Φ C hp hinj hcenter).face x Γ (face_preimage_nonempty Φ C x Γ)) :=
  (subdivisionMap Φ C hp hinj hcenter).isRealizedFace x Γ
    (face_preimage_nonempty Φ C x Γ) hΓ

omit hcenter in
/-- A functional varying on new representation fibres already varies on
old representation fibres. -/
theorem nonconstantOnFibers_original (x : Φ.flag.Node)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hξ : (representation Φ C hp hinj).NonconstantOnFibers x ξ) :
    Φ.representation.NonconstantOnFibers x ξ := by
  obtain ⟨v, w, hv, hw, hmap, hne⟩ := hξ
  refine ⟨v, w, space_le_original Φ x hv, space_le_original Φ x hw, ?_, hne⟩
  change map Φ C x v = map Φ C x w at hmap
  calc
    Φ.representation.map x v = (chart Φ C x).modp p (map Φ C x v) :=
      (chart_map Φ C hp hinj x v hv).symm
    _ = (chart Φ C x).modp p (map Φ C x w) := congrArg _ hmap
    _ = Φ.representation.map x w := chart_map Φ C hp hinj x w hw

/-- Element completeness is preserved with exactly the same thresholds. -/
theorem decomposition_isCompleteElement (x : Φ.flag.Node) (t : ℕ) (δ : ℝ)
    (hcomplete : Φ.IsCompleteElement x t δ) :
    (decomposition Φ C hp hinj hcenter).IsCompleteElement x t δ := by
  intro ξ hξ
  exact hcomplete ξ (nonconstantOnFibers_original Φ C hp hinj x ξ hξ)

end EGZ.FlagDecomposition.Rechart
