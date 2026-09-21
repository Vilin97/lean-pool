/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag

/-!
# Uniform parameters for minimal lattice coordinates

The coordinate growth function depends only on the ambient dimension. A
single prime threshold depending on that dimension and the old uniform box
bound makes all chosen chart reductions injective and all new supports
centered, simultaneously for every input decomposition.
-/

namespace EGZ

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Boundedness on the polytope bounds every lifted support generator. -/
theorem IsKBounded.liftedSupport_bound {Φ : FlagDecomposition p d f}
    {K : Φ.flag.Node → ℕ} (hΦ : Φ.IsKBounded K) (x : Φ.flag.Node)
    (z : IntCoord (Φ.flag.rank x)) (hz : z ∈ Φ.liftedSupport x) :
    latticeSupNorm z ≤ K x := by
  apply hΦ
  rw [Φ.polytope_eq_liftedSupport]
  exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

end FlagDecomposition

/-- Uniform choices for replacing all node lattices with their generated
coordinate lattices. The prime threshold is chosen before the prime, input
weight, decomposition, and nodewise bounds. -/
theorem exists_uniform_rechart_parameters (d : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ BK : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (K : Φ.flag.Node → ℕ), Φ.IsKBounded K → (∀ x, K x ≤ BK) →
            ∃ C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x),
              (∀ x, Function.Injective ((FlagDecomposition.Rechart.chart Φ C x).modp p)) ∧
              (∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q) ∧
              (∀ x (q : IntCoord (C x).rank),
                latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ A (K x)) ∧
              (∀ x (q : IntCoord (C x).rank),
                q.real ∈ (FlagDecomposition.Rechart.polytope Φ C x).carrier →
                  latticeSupNorm q ≤ A (K x)) := by
  classical
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_integerLatticeChart_bound d
  refine ⟨A, hAmono, hAge, ?_⟩
  intro BK
  obtain ⟨B, hB⟩ := exists_uniform_integerLatticeChart_mod_injective d BK
  let p₀ := max 2 (max B (2 * A BK))
  refine ⟨p₀, le_max_left _ _, ?_⟩
  intro p _ _ hpp f Φ K hΦ hBK
  have hBp : B < p := (le_max_right 2 _ |>.trans_lt hpp).trans_le' (le_max_left _ _)
  have hAp : 2 * A BK < p :=
    (le_max_right B _).trans_lt ((le_max_right 2 _).trans_lt hpp)
  have hsupport (x : Φ.flag.Node) :
      ∀ z ∈ Φ.liftedSupport x, latticeSupNorm z ≤ K x := hΦ.liftedSupport_bound x
  choose C hC using fun x ↦ hA (K x) (Φ.flag.rank x)
    (Φ.representation.rank_le x) (Φ.liftedSupport x)
    (Φ.liftedSupport_nonempty x) (hsupport x)
  refine ⟨C, ?_, ?_, hC, FlagDecomposition.Rechart.polytope_bound Φ C hΦ hC⟩
  · intro x u v huv
    have hcongr :
        ((C x).map (FpCoord.centeredLift u)).mod p =
          ((C x).map (FpCoord.centeredLift v)).mod p := by
      change ((FlagDecomposition.Rechart.chart Φ C x).integer (FpCoord.centeredLift u)).mod p =
        ((FlagDecomposition.Rechart.chart Φ C x).integer (FpCoord.centeredLift v)).mod p
      rw [← (FlagDecomposition.Rechart.chart Φ C x).mod_integer,
        ← (FlagDecomposition.Rechart.chart Φ C x).mod_integer,
        FpCoord.mod_centeredLift, FpCoord.mod_centeredLift]
      exact huv
    have hresult := hB (Fact.out : p.Prime) hBp (Φ.flag.rank x)
      (Φ.representation.rank_le x) (Φ.liftedSupport x)
      (fun z hz ↦ (hsupport x z hz).trans (hBK x)) (C x) _ _ hcongr
    simpa only [FpCoord.mod_centeredLift] using hresult
  · intro x q hq
    have hnorm := (C x).coordinateSupport_bound (hsupport x) (hC x) q hq
    have hnorm' : latticeSupNorm q ≤ A BK := hnorm.trans (hAmono (hBK x))
    change latticeSupNorm q ≤ (p - 1) / 2
    omega

end EGZ
