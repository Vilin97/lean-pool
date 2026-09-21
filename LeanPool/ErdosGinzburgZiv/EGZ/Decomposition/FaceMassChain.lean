/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AffineImages
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CommonMeasure
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMap
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup

/-!
# Counting large faces along a stable lineage

Coherent injective coordinate maps place all lineage polytopes in the first
coordinate space. Stable node maps transport their masses and bound their
loss by global mass loss. Passing to the final cumulative weight then gives
the uniform common-measure large-face bound.
-/

open scoped BigOperators

namespace EGZ

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

theorem cumulativeMass_le_retainedMass (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) :
    natMass (Φ.cumulativeWeight x) ≤ Φ.retainedMass := by
  apply natMass_mono
  intro v
  unfold cumulativeWeight FlagDecompositionRaw.cumulativeWeight
    retainedWeight FlagDecompositionRaw.retainedWeight
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Positive lifted mass witnesses an actual point of the node polytope. -/
theorem liftedMassOn_pos_nonempty (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (S : Set (RealCoord (Φ.flag.rank x))) (hS : 0 < Φ.liftedMassOn x S) :
    ((Φ.flag.polytope x).carrier ∩ S).Nonempty := by
  classical
  obtain ⟨q, hq, hmass⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hS)
  have hqS : q.real ∈ S := by
    by_contra hnot
    exact hmass (ite_eq_right hnot)
  refine ⟨q.real, ?_, hqS⟩
  rw [Φ.polytope_eq_liftedSupport]
  exact subset_convexHull ℝ _ ⟨q, hq, rfl⟩

namespace NodeMassMap

variable {Φ Ψ : FlagDecomposition p d f} {x : Φ.flag.Node} {y : Ψ.flag.Node}

/-- Express image-set mass in the original node's centered coordinates. -/
theorem weightedMass_image (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (hM : Function.Injective M.coord.real) (S : Set (RealCoord (Ψ.flag.rank y))) :
    WeightedIncidence.mass (fun v ↦ (Ψ.cumulativeWeight y v : ℝ))
      ((fun v ↦ (FpCoord.centeredLift (Φ.representation.map x v)).real) ⁻¹'
        (M.coord.real '' S)) = (Ψ.liftedMassOn y S : ℝ) := by
  rw [WeightedIncidence.mass_natCast]
  have h := M.liftedMassOn_preimage hp (M.coord.real '' S)
  rw [Set.preimage_image_eq _ hM] at h
  exact congrArg (fun a : ℕ ↦ (a : ℝ)) h.symm

end NodeMassMap

namespace StableNodeMap

variable {Φ Ψ : FlagDecomposition p d f} {x : Φ.flag.Node} {y : Ψ.flag.Node}

theorem cumulativeMass_loss_nonneg (M : StableNodeMap Φ Ψ x y) :
    0 ≤ (natMass (Φ.cumulativeWeight x) : ℝ) - natMass (Ψ.cumulativeWeight y) :=
  sub_nonneg.mpr (Nat.cast_le.mpr (natMass_mono M.cumulative_le))

theorem retainedMass_le (M : StableNodeMap Φ Ψ x y) : Ψ.retainedMass ≤ Φ.retainedMass := by
  have h := M.cumulativeMass_loss_nonneg.trans M.mass_loss_le
  exact Nat.cast_le.mp (sub_nonneg.mp h)

/-- The tail estimate ensures that every old large face has a nonempty
pullback in a later node polytope. This supplies the nonemptiness needed
when applying preservation of realized faces. -/
theorem largeFace_preimage_nonempty (M : StableNodeMap Φ Ψ x y)
    (hp : Odd p) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (Γ : (Φ.flag.polytope x).Face) (hlarge : Φ.IsLargeFace ε x Γ)
    (htail : (Φ.retainedMass : ℝ) - Ψ.retainedMass ≤ ε ^ 2 / 4 * Φ.retainedMass) :
    ((Ψ.flag.polytope y).carrier ∩ M.coord.real ⁻¹' Γ.carrier).Nonempty := by
  have hpos : (0 : ℝ) < Φ.retainedMass := by exact_mod_cast Φ.retainedMass_pos hp
  have h := CommonMeasure.mass_tail_estimates
    (b := (Ψ.liftedMassOn y (M.coord.real ⁻¹' Γ.carrier) : ℝ))
    hε hεhalf hpos M.cumulativeMass_loss_nonneg (M.mass_loss_le.trans htail) hlarge.1
    (by linarith [M.toNodeMassMap.liftedMassOn_loss_le hp Γ.carrier])
  apply Ψ.liftedMassOn_pos_nonempty y _
  exact_mod_cast h.1

end StableNodeMap

end FlagDecomposition

/-- The explicit large-face bound is monotone in the ambient dimension. -/
theorem largeFaceBound_mono_dimension {ε : ℝ} (hε : 0 < ε) {r d : ℕ} (hrd : r ≤ d) :
    ((ε ^ 3)⁻¹ + (r : ℝ) + 2) ^ (r + 2) ≤
      ((ε ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2) := by
  have hinv : 0 ≤ (ε ^ 3)⁻¹ := by positivity
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hbase : 1 ≤ (ε ^ 3)⁻¹ + (d : ℝ) + 2 := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact (pow_le_pow_left₀ (by positivity) (by linarith :
    (ε ^ 3)⁻¹ + (r : ℝ) + 2 ≤ (ε ^ 3)⁻¹ + (d : ℝ) + 2) _).trans
    (pow_le_pow_right₀ hbase (Nat.add_le_add_right hrd 2))

namespace FlagDecomposition

variable {p d N : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- The face-counting step for one surviving lineage. Coordinate injectivity
and the pullback no-repeat condition are explicit geometric inputs; all
common-measure and dimension bookkeeping is proved here. -/
theorem card_largeFaceChain_le
    (Φ : Fin (N + 1) → FlagDecomposition p d f) (x : ∀ i, (Φ i).flag.Node)
    (M : ∀ {i j : Fin (N + 1)}, i ≤ j → StableNodeMap (Φ i) (Φ j) (x i) (x j))
    (hinj : ∀ {i j} (h : i ≤ j), Function.Injective (M h).coord.real)
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (M (hij.trans hjk)).coord = (M hij).coord.comp (M hjk).coord)
    (hp : Odd p) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (Γ : ∀ i, ((Φ i).flag.polytope (x i)).Face)
    (hlarge : ∀ i, (Φ i).IsLargeFace ε (x i) (Γ i))
    (hdistinct : ∀ i j (hij : i < j),
      ((Φ j).flag.polytope (x j)).carrier ∩ (M hij.le).coord.real ⁻¹' (Γ i).carrier ≠
        (Γ j).carrier)
    (htail : ∀ i, ((Φ i).retainedMass : ℝ) - (Φ (Fin.last N)).retainedMass ≤
      ε ^ 2 / 4 * (Φ i).retainedMass) :
    ((N + 1 : ℕ) : ℝ) ≤ (((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2) := by
  classical
  let A (i : Fin (N + 1)) := (M (Fin.zero_le i)).coord
  let P (i : Fin (N + 1)) := ((Φ i).flag.polytope (x i)).image (A i)
  let F (i : Fin (N + 1)) : (P i).Face := (Γ i).image (A i) (hinj (Fin.zero_le i))
  let q (v : FpCoord p d) := (FpCoord.centeredLift ((Φ 0).representation.map (x 0) v)).real
  let w (i : Fin (N + 1)) (v : FpCoord p d) : ℝ := (Φ i).cumulativeWeight (x i) v
  let u := w (Fin.last N)
  let R (i : Fin (N + 1)) : ℝ := (Φ i).retainedMass
  have hcoord {i j : Fin (N + 1)} (hij : i ≤ j) :
      A j = (A i).comp (M hij).coord := hcomp (Fin.zero_le i) hij
  have hmass (i : Fin (N + 1)) (S : Set (RealCoord ((Φ i).flag.rank (x i)))) :
      WeightedIncidence.mass (w i) (q ⁻¹' ((A i).real '' S)) =
        ((Φ i).liftedMassOn (x i) S : ℝ) :=
    (M (Fin.zero_le i)).toNodeMassMap.weightedMass_image hp (hinj (Fin.zero_le i)) S
  have hnested : ∀ i j, i < j → (P j).carrier ⊆ (P i).carrier := by
    intro i j hij
    apply RationalPolytope.affineImage_subset _ _ (A j).real (A i).real
      (M hij.le).coord.real _ _ (M hij.le).polytope_mem
    intro z _
    rw [hcoord hij.le]
    rfl
  have hdistinct' : ∀ i j, i < j → (F i).carrier ∩ (P j).carrier ≠ (F j).carrier := by
    intro i j hij
    change (A i).real '' (Γ i).carrier ∩ (A j).real ''
      ((Φ j).flag.polytope (x j)).carrier ≠ (A j).real '' (Γ j).carrier
    rw [hcoord hij.le]
    exact fun heq ↦ hdistinct i j hij ((affineImage_inter_comp_eq_iff
      (A i).real (M hij.le).coord.real (hinj (Fin.zero_le i)) (hinj hij.le)
      (Γ i).carrier ((Φ j).flag.polytope (x j)).carrier (Γ j).carrier).mp heq)
  have hle : ∀ i v, u v ≤ w i v := by
    intro i v
    dsimp only [u, w]
    exact_mod_cast (M (Fin.le_last i)).cumulative_le v
  have hR : ∀ i, 0 < R i := by
    intro i
    dsimp only [R]
    exact_mod_cast (Φ i).retainedMass_pos hp
  have htotal : ∀ i, (∑ v, w i v) ≤ R i := by
    intro i
    simpa only [w, R, natMass, Nat.cast_sum] using
      (Nat.cast_le.mpr ((Φ i).cumulativeMass_le_retainedMass (x i)) :
        (natMass ((Φ i).cumulativeWeight (x i)) : ℝ) ≤ (Φ i).retainedMass)
  have hloss : ∀ i, (∑ v, (w i v - u v)) ≤ ε ^ 2 / 4 * R i := by
    intro i
    have h := (M (Fin.le_last i)).mass_loss_le.trans (htail i)
    simpa only [w, u, R, Finset.sum_sub_distrib, natMass, Nat.cast_sum] using h
  have hlarge' : ∀ i, ε * R i ≤ WeightedIncidence.mass (w i) (q ⁻¹' (F i).carrier) := by
    intro i
    change ε * R i ≤ WeightedIncidence.mass (w i) (q ⁻¹' ((A i).real '' (Γ i).carrier))
    rw [hmass]
    exact (hlarge i).1
  have hproper : ∀ i (Δ : (P i).Face), Δ.carrier ⊂ (F i).carrier →
      WeightedIncidence.mass (w i) (q ⁻¹' Δ.carrier) ≤
        (1 - ε) * WeightedIncidence.mass (w i) (q ⁻¹' (F i).carrier) := by
    intro i Δ hΔ
    let Δ₀ := Δ.affineImagePullback (A i).real (fun _ ↦ (A i).real_isRational)
    have himage : (Δ₀.image (A i) (hinj (Fin.zero_le i))).carrier = Δ.carrier :=
      congrArg RationalPolytope.Face.carrier
        (Δ.affineImage_affineImagePullback (A i).real
          (fun _ ↦ (A i).real_isRational) (hinj (Fin.zero_le i)))
    have hsub : Δ₀.carrier ⊂ (Γ i).carrier :=
      (Δ₀.affineImage_ssubset_iff (Γ i) (A i).real
        (fun _ ↦ (A i).real_isRational) (hinj (Fin.zero_le i))).mp
          (by simpa only [himage] using hΔ)
    rw [← himage]
    change WeightedIncidence.mass (w i) (q ⁻¹' ((A i).real '' Δ₀.carrier)) ≤
      (1 - ε) * WeightedIncidence.mass (w i) (q ⁻¹' ((A i).real '' (Γ i).carrier))
    rw [hmass, hmass]
    exact (hlarge i).2 Δ₀ hsub
  have hbound := card_largeFaceSequence_of_mass_loss q u
    (fun v ↦ Nat.cast_nonneg ((Φ (Fin.last N)).cumulativeWeight (x (Fin.last N)) v))
    w R hle hR htotal P F hnested hdistinct' ε hε hεhalf hloss hlarge' hproper
  exact hbound.trans (largeFaceBound_mono_dimension (by positivity : 0 < ε / 2)
    ((Φ 0).representation.rank_le (x 0)))

end FlagDecomposition
end EGZ
