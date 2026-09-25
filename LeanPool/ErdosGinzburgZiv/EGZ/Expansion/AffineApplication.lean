/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Affine
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag

/-!
# Applying relative expansion to affine fibres

The relative expansion statement implies an affine-subspace version with
uniform thresholds in the original ambient dimension.  Translating the
integer centre doubles the box radius and changes the weighted sum to zero.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ
namespace Expansion

theorem AffineModel.apply_relativeExpansion {p d r t K T : ℕ}
    [NeZero p] [Fact p.Prime] {δ : ℝ}
    {V : AffineSubspace (ZMod p) (FpCoord p d)}
    {φ : FpCoord p d →ᵃ[ZMod p] FpCoord p r}
    (S : Finset (IntCoord r)) (c : IntCoord r)
    (M : AffineModel V φ (c.mod p) t)
    (hexp : RelativeExpansionAt r t (2 * K) δ T p)
    (w : FpCoord p d → ℕ) (α : S → ℕ)
    (hbox : ∀ q ∈ S, latticeSupNorm q ≤ K) (hc : latticeSupNorm c ≤ K)
    (hw : ∀ v, w v ≠ 0 → v ∈ V)
    (hs : ∀ v, w v ≠ 0 → ∃ q ∈ S, φ v = q.mod p)
    (hz : (∑ q : S, α q • (q : IntCoord r)) = p • c)
    (hm : (∑ q : S, α q) = p)
    (ha : ∀ q : S, δ * p ≤ (α q : ℝ) ∧
      (α q : ℝ) ≤ (pushWeight φ w ((q : IntCoord r).mod p) : ℝ) - δ * p)
    (hthick : IsThickRelativeOn w V φ T δ) : HasZeroSumMultiplicity w := by
  classical
  let E : IntCoord r ↪ IntCoord r := ⟨fun q ↦ q - c, fun _ _ h ↦ sub_left_injective h⟩
  let S' := S.map E
  let e : S ≃ S' := Finset.equivMap E S
  let β : S' → ℕ := α ∘ e.symm
  have he (q : S) : (e q : IntCoord r) = (q : IntCoord r) - c := rfl
  have hb (q : S) : β (e q) = α q := by simp [β]
  have hmod (q : IntCoord r) : (q - c).mod p = q.mod p - c.mod p := by
    ext i
    simp [IntCoord.mod]
  apply M.hasZeroSumMultiplicity_of_coordinates w hw
  apply hexp.of_nat_coefficients S' (w ∘ M.chart) β
  · intro q hq
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_map.mp hq
    apply latticeSupNorm_le_iff.mpr
    intro i
    exact (Int.natAbs_sub_le (z i) (c i)).trans (by
      have hzi := latticeSupNorm_le_iff.mp (hbox z hzS) i
      have hci := latticeSupNorm_le_iff.mp hc i
      change (z i).natAbs + (c i).natAbs ≤ 2 * K
      omega)
  · intro v hv
    obtain ⟨q, hq, hφq⟩ := hs (M.chart v) hv
    refine ⟨q - c, Finset.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    rw [hmod]
    apply eq_sub_iff_add_eq.mpr
    rwa [← M.projection]
  · calc
      (∑ q : S', β q • (q : IntCoord r)) =
          ∑ q : S, α q • ((q : IntCoord r) - c) := by
        rw [← e.sum_comp]
        simp only [hb, he]
      _ = (∑ q : S, α q • (q : IntCoord r)) - (∑ q : S, α q) • c := by
        simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = 0 := by rw [hz, hm, sub_self]
  · rw [← e.sum_comp]
    simpa only [hb] using hm
  · intro q
    obtain ⟨z, rfl⟩ := e.surjective q
    rw [hb, he, hmod, M.fibreWeight w hw]
    exact ha z
  · exact M.thickRelative w hw hthick

/-- The expansion conclusion for an arbitrary affine surjection on the
affine subspace carrying a weight.  The centre and support share one box. -/
def AffineExpansionAt (d K : ℕ) (δ : ℝ) (T p : ℕ) [NeZero p] : Prop :=
  ∀ r : ℕ, r ≤ d →
    ∀ (V : AffineSubspace (ZMod p) (FpCoord p d))
      (φ : FpCoord p d →ᵃ[ZMod p] FpCoord p r),
    Set.SurjOn φ V Set.univ →
    ∀ (S : Finset (IntCoord r)) (c : IntCoord r)
      (w : FpCoord p d → ℕ) (α : S → ℕ),
    (∀ q ∈ S, latticeSupNorm q ≤ K) → latticeSupNorm c ≤ K →
    (∀ v, w v ≠ 0 → v ∈ V) →
    (∀ v, w v ≠ 0 → ∃ q ∈ S, φ v = q.mod p) →
    (∑ q : S, α q • (q : IntCoord r)) = p • c →
    (∑ q : S, α q) = p →
    (∀ q : S, δ * p ≤ (α q : ℝ) ∧
      (α q : ℝ) ≤ (pushWeight φ w ((q : IntCoord r).mod p) : ℝ) - δ * p) →
    IsThickRelativeOn w V φ T δ → HasZeroSumMultiplicity w

/-- Uniformity over the finitely many possible quotient and kernel
dimensions gives thresholds depending only on `d`, `K`, and `δ`. -/
theorem RelativeExpansionStatement.affine_thresholds
    (h : RelativeExpansionStatement) (d K : ℕ) (hK : 1 ≤ K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ p₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → ∀ p : ℕ,
      ∀ (_ : Fact p.Prime) (_ : NeZero p), p₀ ≤ p →
        AffineExpansionAt d K δ T p := by
  classical
  have hparam (i : Fin (d + 1) × Fin (d + 1)) :=
    h.thresholds i.1 i.2 (2 * K) (by omega) δ hδ
  choose Ts Ps hPs hAt using hparam
  let T₀ := Finset.univ.sup Ts
  let p₀ := Finset.univ.sup Ps
  refine ⟨T₀, p₀, ?_⟩
  intro T hT p hpprime hpzero hpp r hr V φ hφ S c w α hbox hc hw hs hz hm ha ht
  obtain ⟨t, hrt, ⟨M⟩⟩ := exists_affineModel V φ hφ (c.mod p)
  let i : Fin (d + 1) × Fin (d + 1) := ⟨⟨r, by omega⟩, ⟨t, by omega⟩⟩
  have hTi : Ts i ≤ T := (Finset.le_sup (f := Ts) (Finset.mem_univ i)).trans hT
  have hPi : Ps i ≤ p := (Finset.le_sup (f := Ps) (Finset.mem_univ i)).trans hpp
  exact M.apply_relativeExpansion S c (hAt i T hTi p hpprime hpzero hPi)
    w α hbox hc hw hs hz hm ha ht

/-- The expansion interface applies directly to a complete decomposition
node.  Its conclusion is a zero sum in the original multiplicity function. -/
theorem AffineExpansionAt.decomposition {p d K T : ℕ}
    [NeZero p] {δ δ₀ : ℝ}
    (h : AffineExpansionAt d K δ T p)
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (hr : Φ.flag.rank x ≤ d)
    (hbox : ∀ q ∈ Φ.liftedSupport x, latticeSupNorm q ≤ K)
    (c : IntCoord (Φ.flag.rank x)) (hc : latticeSupNorm c ≤ K)
    (α : Φ.liftedSupport x → ℕ)
    (hz : (∑ q : Φ.liftedSupport x, α q • (q : IntCoord (Φ.flag.rank x))) = p • c)
    (hm : (∑ q : Φ.liftedSupport x, α q) = p)
    (ha : ∀ q : Φ.liftedSupport x, δ * p ≤ (α q : ℝ) ∧
      (α q : ℝ) ≤ (Φ.hat x q : ℝ) - δ * p)
    (ht : Φ.IsCompleteElement x T δ₀) (hδ : δ ≤ δ₀) :
    HasZeroSumMultiplicity f := by
  classical
  have hfibre (q : Φ.liftedSupport x) : Φ.hat x q =
      pushWeight (Φ.representation.map x) (Φ.cumulativeWeight x)
        ((q : IntCoord (Φ.flag.rank x)).mod p) := by
    have hq := ((Φ.originalWeights.hat_ne_zero_iff x q).mp
      ((Φ.liftedSupport_spec x q).mp q.property)).1
    change (if IsCenteredLift p (q : IntCoord (Φ.flag.rank x)) then _ else 0) = _
    rw [ite_eq_left hq]
    simp only [FlagDecompositionRaw.affineFibreMass, pushWeight,
      FlagDecomposition.cumulativeWeight]
    apply Finset.sum_congr
    · ext v
      simp
    · intro v _
      split_ifs <;> rfl
  have hzero : HasZeroSumMultiplicity (Φ.cumulativeWeight x) := by
    apply h (Φ.flag.rank x) hr (Φ.representation.space x) (Φ.representation.map x)
      (Φ.representation.map_surjective x) (Φ.liftedSupport x) c (Φ.cumulativeWeight x) α
      hbox hc
    · exact fun v hv ↦ Φ.originalWeights.cumulative_supported x v hv
    · intro v hv
      exact ⟨FpCoord.centeredLift (Φ.representation.map x v),
        Φ.centeredLift_mem_liftedSupport hp x hv, (FpCoord.mod_centeredLift _).symm⟩
    · exact hz
    · exact hm
    · intro q
      simpa only [hfibre] using ha q
    · intro ξ hξ hthin
      exact ht ξ hξ (hthin.mono_error hδ)
  apply hzero.mono
  intro v
  apply le_trans _ (Φ.retained_le v)
  apply Finset.sum_le_sum
  intro y _
  change (if y ≤ x then Φ.localWeight y v else 0) ≤ Φ.localWeight y v
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

end Expansion
end EGZ
