/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagram
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Uniform chart parameters for support diagrams

These bounds apply before a finite-field representation has been constructed.
Only the ranks and integer support boxes enter the coordinate growth function
and the prime threshold.
-/

@[expose] public section

namespace EGZ

theorem convexHull_subset_coordinateBox {n K : ℕ} {S : Set (IntCoord n)}
    (hS : ∀ z ∈ S, latticeSupNorm z ≤ K) :
    convexHull ℝ (IntCoord.real '' S) ⊆
      Set.Icc (fun _ : Fin n ↦ -(K : ℝ)) (fun _ ↦ (K : ℝ)) := by
  apply convexHull_min _ (convex_Icc _ _)
  rintro _ ⟨z, hz, rfl⟩
  constructor
  · intro i
    have hi := latticeSupNorm_le_iff.mp (hS z hz) i
    have hlow : -(K : ℤ) ≤ z i := by omega
    change -(K : ℝ) ≤ (z i : ℝ)
    exact_mod_cast hlow
  · intro i
    have hi := latticeSupNorm_le_iff.mp (hS z hz) i
    have hupp : z i ≤ (K : ℤ) := by omega
    change (z i : ℝ) ≤ (K : ℝ)
    exact_mod_cast hupp

theorem latticeSupNorm_le_of_mem_convexHull {n K : ℕ} {S : Set (IntCoord n)}
    (hS : ∀ z ∈ S, latticeSupNorm z ≤ K) (q : IntCoord n)
    (hq : q.real ∈ convexHull ℝ (IntCoord.real '' S)) : latticeSupNorm q ≤ K := by
  have hb := convexHull_subset_coordinateBox hS hq
  rw [latticeSupNorm_le_iff]
  intro i
  have hlow : -(K : ℤ) ≤ q i := by
    have h := hb.1 i
    change -(K : ℝ) ≤ (q i : ℝ) at h
    exact_mod_cast h
  have hupp : q i ≤ (K : ℤ) := by
    have h := hb.2 i
    change (q i : ℝ) ≤ (K : ℝ) at h
    exact_mod_cast h
  omega

namespace LatticeSupportDiagram

theorem polytope_bound (D : LatticeSupportDiagram) {K : D.Node → ℕ}
    (hS : ∀ x q, q ∈ D.support x → latticeSupNorm q ≤ K x)
    (x : D.Node) (q : IntCoord (D.rank x)) (hq : q.real ∈ (D.polytope x).carrier) :
    latticeSupNorm q ≤ K x := by
  rw [D.polytope_carrier] at hq
  exact latticeSupNorm_le_of_mem_convexHull (hS x) q hq

end LatticeSupportDiagram

theorem exists_uniform_supportChart_parameters (r : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ BK : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (D : LatticeSupportDiagram) (K : D.Node → ℕ),
            (∀ x, D.rank x ≤ r) →
            (∀ x q, q ∈ D.support x → latticeSupNorm q ≤ K x) →
            (∀ x, K x ≤ BK) →
            ∃ C : ∀ x, IntegerLatticeChart (D.support x),
              (∀ x, Function.Injective ((D.chart C x).modp p)) ∧
              (∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q) ∧
              (∀ x (q : IntCoord (C x).rank),
                latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ A (K x)) ∧
              (∀ x (q : IntCoord (C x).rank),
                q.real ∈ ((D.chartedFlag C).polytope x).carrier →
                  latticeSupNorm q ≤ A (K x)) := by
  classical
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_integerLatticeChart_bound r
  refine ⟨A, hAmono, hAge, ?_⟩
  intro BK
  obtain ⟨B, hB⟩ := exists_uniform_integerLatticeChart_mod_injective r BK
  let p₀ := max 2 (max B (2 * A BK))
  refine ⟨p₀, le_max_left _ _, ?_⟩
  intro p _ _ hpp D K hr hsupport hBK
  have hBp : B < p := (le_max_left B _).trans_lt ((le_max_right 2 _).trans_lt hpp)
  have hAp : 2 * A BK < p :=
    (le_max_right B _).trans_lt ((le_max_right 2 _).trans_lt hpp)
  choose C hC using fun x ↦ hA (K x) (D.rank x) (hr x) (D.support x)
    (D.support_nonempty x) (hsupport x)
  refine ⟨C, ?_, ?_, hC, ?_⟩
  · intro x u v huv
    have hcongr :
        ((C x).map (FpCoord.centeredLift u)).mod p =
          ((C x).map (FpCoord.centeredLift v)).mod p := by
      change ((D.chart C x).integer (FpCoord.centeredLift u)).mod p =
        ((D.chart C x).integer (FpCoord.centeredLift v)).mod p
      rw [← (D.chart C x).mod_integer, ← (D.chart C x).mod_integer,
        FpCoord.mod_centeredLift, FpCoord.mod_centeredLift]
      exact huv
    have hresult := hB (Fact.out : p.Prime) hBp (D.rank x) (hr x) (D.support x)
      (fun z hz ↦ (hsupport x z hz).trans (hBK x)) (C x) _ _ hcongr
    simpa only [FpCoord.mod_centeredLift] using hresult
  · intro x q hq
    have hnorm := (C x).coordinateSupport_bound (hsupport x) (hC x) q hq
    have hnorm' : latticeSupNorm q ≤ A BK := hnorm.trans (hAmono (hBK x))
    change latticeSupNorm q ≤ (p - 1) / 2
    omega
  · exact D.charted_polytope_bound C (D.polytope_bound hsupport) hC

end EGZ
