/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction

/-!
# The initial flag decomposition

Every nonzero weight has a singleton flag decomposition with a rank-zero
lattice fibre.  Its ambient affine space is the affine span of the support.
It retains all the input mass and is reduced and minimal.  This is the
starting object for the refinement argument.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

/-- The unique polytope in the rank-zero coordinate space. -/
noncomputable def rankZeroPolytope : RationalPolytope 0 where
  carrier := Set.univ
  generators := {0}
  generators_nonempty := by simp
  generators_rational := by intro q _ i; exact Fin.elim0 i
  carrier_eq_convexHull := by
    ext q
    simp [Subsingleton.elim q 0]
  finite_integral := Set.toFinite _

/-- A singleton flag with a rank-zero lattice fibre. -/
noncomputable abbrev rankZeroFlag : ConvexFlag where
  Node := Fin 1
  rank := fun _ ↦ 0
  polytope := fun _ ↦ rankZeroPolytope
  lattice := fun _ ↦ AffineLattice.standard 0
  transition := fun _ ↦ IntegralAffineMap.id 0
  transition_mem := by intro x y h q hq; exact hq
  transition_lattice := by intro x y h q hq; exact hq
  transition_refl := by intro x; rfl
  transition_trans := by intro x y z hxy hyz; rfl

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p]

private theorem exists_weight_ne_zero {f : FpCoord p d → ℕ} (hf : f ≠ 0) :
    ∃ v, f v ≠ 0 := by
  by_contra! h
  exact hf (funext h)

private theorem natMass_ne_zero {f : FpCoord p d → ℕ} (hf : f ≠ 0) :
    natMass f ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_weight_ne_zero hf
  have hle : f v ≤ natMass f :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
  exact ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le hle)

/-- The initial representation collapses the affine span of the support
onto the unique rank-zero finite-field vector. -/
noncomputable def initialRepresentation (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    FpRepresentation p d rankZeroFlag where
  space := fun _ ↦ affineSpan (ZMod p) {v | f v ≠ 0}
  map := fun _ ↦ 0
  space_mono := fun _ ↦ le_rfl
  map_surjective := by
    intro x c _
    obtain ⟨v, hv⟩ := exists_weight_ne_zero hf
    exact ⟨v, subset_affineSpan (ZMod p) _ hv, Subsingleton.elim _ _⟩
  compatible := by intro x y h v hv; exact Subsingleton.elim _ _
  lattice_eq_standard := by intro x q; rfl

omit [NeZero p] in
private theorem initial_cumulativeWeight (f : FpCoord p d → ℕ)
    (x : rankZeroFlag.Node) (v : FpCoord p d) :
    FlagDecompositionRaw.cumulativeWeight (F := rankZeroFlag) (fun _ ↦ f) x v = f v := by
  classical
  unfold FlagDecompositionRaw.cumulativeWeight
  simp [rankZeroFlag]

private theorem initial_hat (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (x : rankZeroFlag.Node) (z : IntCoord (rankZeroFlag.rank x)) :
    FlagDecompositionRaw.hat (initialRepresentation f hf) (fun _ ↦ f) x z =
      natMass f := by
  classical
  have hz : IsCenteredLift p z := by
    change Finset.univ.sup (fun i : Fin 0 ↦ (z i).natAbs) ≤ _
    simp
  unfold FlagDecompositionRaw.hat
  rw [ite_eq_left hz]
  unfold FlagDecompositionRaw.affineFibreMass natMass
  apply Finset.sum_congr rfl
  intro v _
  rw [ite_eq_left (Subsingleton.elim _ _)]
  exact initial_cumulativeWeight f x v

private theorem initial_localLift (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (x : rankZeroFlag.Node) (z : IntCoord 0) :
    FlagDecompositionRaw.localLift (initialRepresentation f hf) (fun _ ↦ f) x z =
      natMass f := by
  classical
  have hz : IsCenteredLift p z := by
    unfold IsCenteredLift latticeSupNorm
    simp
  unfold FlagDecompositionRaw.localLift
  rw [ite_eq_left hz]
  unfold FlagDecompositionRaw.affineFibreMass natMass
  apply Finset.sum_congr rfl
  intro v _
  rw [ite_eq_left (Subsingleton.elim _ _)]

/-- The singleton initial decomposition retains all of a nonzero input
weight.  No lower bound on the modulus is needed for its rank-zero lifts. -/
noncomputable def initial (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    FlagDecomposition p d f := by
  classical
  exact {
  flag := rankZeroFlag
  representation := initialRepresentation f hf
  localWeight := fun _ ↦ f
  local_supported := by
    intro x v hv
    exact subset_affineSpan (ZMod p) _ hv
  retained_le := by
    intro v
    change (∑ _ : Fin 1, f v) ≤ f v
    simp
  liftedSupport := fun _ ↦ {0}
  liftedSupport_spec := by
    intro x z
    rw [initial_hat f hf]
    simp [Subsingleton.elim z 0, natMass_ne_zero hf]
  liftedSupport_nonempty := by intro x; simp
  polytope_eq_liftedSupport := by
    intro x
    change Set.univ = _
    rw [Finset.coe_singleton, Set.image_singleton, convexHull_singleton]
    ext q
    simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
    exact Subsingleton.elim _ _
  faces_visible := by
    intro x Γ
    obtain ⟨q, hq⟩ := Γ.nonempty
    let Q : rankZeroFlag.Point := ⟨x, q, Set.mem_univ _⟩
    refine ⟨Q, ConvexFlag.subset_convexHull rankZeroFlag _ ?_, le_rfl, ?_⟩
    · refine ⟨0, Subsingleton.elim _ _, ?_⟩
      exact (initial_localLift f hf x 0).trans_ne (natMass_ne_zero hf)
    · simpa [Q] using hq
  }

@[simp]
theorem initial_retainedWeight (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    (initial f hf).retainedWeight = f := by
  funext v
  change (∑ _ : Fin 1, f v) = f v
  simp

@[simp]
theorem initial_cumulative (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (x : (initial f hf).flag.Node) : (initial f hf).cumulativeWeight x = f := by
  funext v
  exact initial_cumulativeWeight f x v

@[simp]
theorem initial_retainedMass (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    (initial f hf).retainedMass = natMass f := by
  rw [retainedMass, initial_retainedWeight]

/-- The initial flag has exactly one node. -/
@[simp]
theorem initial_card (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    Fintype.card (initial f hf).flag.Node = 1 := by
  change Fintype.card (Fin 1) = 1
  simp

/-- Every coordinate of the initial fibre is zero, so every coordinate
bound is valid. -/
theorem initial_isKBounded (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (K : (initial f hf).flag.Node → ℕ) : (initial f hf).IsKBounded K := by
  intro x z hz
  change Finset.univ.sup (fun i : Fin 0 ↦ (z i).natAbs) ≤ K x
  simp

/-- The unique initial node is reduced. -/
theorem initial_isReduced (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    (initial f hf).IsReduced := by
  intro x
  apply (initial f hf).isReducedElement_of_localLift_ne_zero x 0
  exact (initial_localLift f hf x 0).trans_ne (natMass_ne_zero hf)

/-- The initial affine space and rank-zero affine lattice are minimal. -/
theorem initial_isMinimal (f : FpCoord p d → ℕ) (hf : f ≠ 0) :
    (initial f hf).IsMinimal := by
  classical
  intro x
  constructor
  · rw [initial_cumulative]
    rfl
  · intro z
    refine ⟨Finsupp.single 0 1, ?_, ?_, ?_⟩
    · change (Finsupp.single (0 : IntCoord 0) (1 : ℤ)).support ⊆ {0}
      simp
    · simp
    · change (_ : IntCoord 0) = z
      exact Subsingleton.elim _ _

/-- The unique positive lifted mass of the initial decomposition is the
entire input mass. -/
@[simp]
theorem initial_gap (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (x : (initial f hf).flag.Node) : (initial f hf).gap x = natMass f := by
  classical
  unfold gap
  change (({0} : Finset (IntCoord 0)).image
    (FlagDecompositionRaw.hat (initialRepresentation f hf) (fun _ ↦ f) x)).min' _ = natMass f
  simp only [Finset.image_singleton, Finset.min'_singleton]
  exact initial_hat f hf x 0

/-- Every face of the initial polytope is realized. -/
theorem initial_isRealizedFace (f : FpCoord p d → ℕ) (hf : f ≠ 0)
    (x : (initial f hf).flag.Node) (Γ : ((initial f hf).flag.polytope x).Face) :
    (initial f hf).IsRealizedFace x Γ := by
  intro q hq
  obtain ⟨z, hz⟩ := Γ.nonempty
  have h : ((initial f hf).flag.transition ((initial f hf).faceIndex_le x Γ)).real q = z := by
    change (_ : RealCoord 0) = z
    exact Subsingleton.elim _ _
  rwa [h]

/-- In ambient dimension zero every affine functional is constant, so the
initial node satisfies completeness for all parameters. -/
theorem initial_isComplete_dimZero (f : FpCoord p 0 → ℕ) (hf : f ≠ 0)
    (T : (initial f hf).flag.Node → ℕ) (ε δ : ℝ) :
    (initial f hf).IsComplete T ε δ := by
  refine ⟨initial_isMinimal f hf, initial_isReduced f hf, ?_, ?_⟩
  · intro x hx ξ hξ
    obtain ⟨v, w, _, _, _, hne⟩ := hξ
    exact (hne (congrArg ξ (Subsingleton.elim v w))).elim
  · intro x Γ hΓ
    exact initial_isRealizedFace f hf x Γ

end FlagDecomposition

end EGZ
