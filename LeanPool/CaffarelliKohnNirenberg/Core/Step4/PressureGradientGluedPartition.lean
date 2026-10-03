/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A finite smooth partition of unity on a compact set

Elementary construction of finitely many smooth compactly supported functions,
each supported inside one member of a given open cover of a compact set, whose
sum equals `1` on that compact set.  The construction multiplies bump functions
telescopically, so no manifold partition-of-unity machinery is needed.
-/

public section

open Metric Set
noncomputable section
namespace CKN

/-- Telescoping identity: the weighted sum of the successive complementary
products `∏_{l < k} (1 - f l)` collapses to `1` minus the full product. -/
private lemma sum_prod_telescope (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, f k * ∏ l ∈ Finset.range k, (1 - f l)
      = 1 - ∏ k ∈ Finset.range N, (1 - f k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ih]
      ring

/-- On a compact set covered by open sets there are finitely many smooth
compactly supported functions, each supported inside one member of the cover,
whose sum is identically one on the compact set. -/
theorem exists_smooth_partition_of_unity_of_isCompact {d : ℕ} {ι : Type*}
    {K : Set (Vec d)} (hK : IsCompact K) (V : ι → Set (Vec d))
    (hV : ∀ b, IsOpen (V b)) (hcover : K ⊆ ⋃ b, V b) :
    ∃ (N : ℕ) (χ : ℕ → Vec d → ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (χ k)) ∧
      (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k ∈ Finset.range N, ∃ b, tsupport (χ k) ⊆ V b) ∧
      (∀ x ∈ K, ∑ k ∈ Finset.range N, χ k x = 1) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨0, fun _ _ => 0, ?_, ?_, ?_, ?_⟩
    · intro k; exact contDiff_const
    · intro k
      exact HasCompactSupport.intro' isCompact_empty isClosed_empty (fun _ _ => rfl)
    · intro k hk; simp at hk
    · intro x hx; simp at hx
  · -- Each point of the compact set has a small ball inside some member of the cover.
    have hb : ∀ a : K, ∃ (b : ι) (e : ℝ), 0 < e ∧ Metric.ball (a : Vec d) e ⊆ V b := by
      intro a
      obtain ⟨b, hb⟩ := mem_iUnion.mp (hcover a.2)
      obtain ⟨e, he0, hesub⟩ := Metric.isOpen_iff.mp (hV b) (a : Vec d) hb
      exact ⟨b, e, he0, hesub⟩
    choose bb ee hee0 heesub using hb
    -- A bump function concentrated in the ball, supported in the corresponding `V b`.
    let β : (a : K) → ContDiffBump (a : Vec d) :=
      fun a => ⟨ee a / 3, ee a / 2, div_pos (hee0 a) (by norm_num),
        by show ee a / 3 < ee a / 2; linarith only [hee0 a]⟩
    have hβsub : ∀ a : K, tsupport (β a) ⊆ V (bb a) := by
      intro a
      rw [(β a).tsupport_eq]
      exact (Metric.closedBall_subset_ball
        (by change ee a / 2 < ee a; linarith only [hee0 a])).trans (heesub a)
    -- Finitely many of those balls already cover the compact set.
    have hsub : K ⊆ ⋃ a : K, Metric.ball (a : Vec d) (ee a / 3) := by
      intro x hx
      exact mem_iUnion.mpr
        ⟨⟨x, hx⟩, Metric.mem_ball_self (div_pos (hee0 ⟨x, hx⟩) (by norm_num))⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : K => Metric.ball (a : Vec d) (ee a / 3))
      (fun _ => Metric.isOpen_ball) hsub
    obtain ⟨a₀, ha₀⟩ := hKne
    let N : ℕ := t.card
    -- Enumerate the selected centres by `Fin N`, extended to all of `ℕ`.
    let pt : ℕ → K :=
      fun n => if h : n < N then ((t.equivFin.symm ⟨n, h⟩ : ↥t) : K) else ⟨a₀, ha₀⟩
    let ψ : ℕ → Vec d → ℝ := fun n x => if n < N then (β (pt n)) x else 0
    let χ : ℕ → Vec d → ℝ := fun n x => ψ n x * ∏ l ∈ Finset.range n, (1 - ψ l x)
    have hψeq : ∀ n, n < N → ψ n = ⇑(β (pt n)) := by
      intro n hn
      funext x
      simp only [ψ]
      rw [ite_eq_left hn]
    have hψzero : ∀ n, ¬ n < N → ψ n = fun _ => (0 : ℝ) := by
      intro n hn
      funext x
      simp only [ψ]
      rw [ite_eq_right hn]
    have hψsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := by
      intro n
      by_cases hn : n < N
      · rw [hψeq n hn]; exact (β (pt n)).contDiff
      · rw [hψzero n hn]; exact contDiff_const
    have hψcs : ∀ n, HasCompactSupport (ψ n) := by
      intro n
      by_cases hn : n < N
      · rw [hψeq n hn]; exact (β (pt n)).hasCompactSupport
      · rw [hψzero n hn]
        exact HasCompactSupport.intro' isCompact_empty isClosed_empty (fun _ _ => rfl)
    have hχsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) := by
      intro n
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x => ψ n x * ∏ l ∈ Finset.range n, (1 - ψ l x))
      exact (hψsmooth n).mul (contDiff_prod fun l _ => contDiff_const.sub (hψsmooth l))
    have hχcs : ∀ n, HasCompactSupport (χ n) := by
      intro n
      exact (hψcs n).mul_right
    have hsupp : ∀ k ∈ Finset.range N, ∃ b, tsupport (χ k) ⊆ V b := by
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      refine ⟨bb (pt k), ?_⟩
      have htsupp : tsupport (χ k) ⊆ tsupport (ψ k) := by
        apply closure_mono
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h
        exact hx (by change ψ k x * ∏ l ∈ Finset.range k, (1 - ψ l x) = 0; rw [h, zero_mul])
      calc tsupport (χ k) ⊆ tsupport (ψ k) := htsupp
        _ = tsupport ⇑(β (pt k)) := by rw [hψeq k hkN]
        _ ⊆ V (bb (pt k)) := hβsub (pt k)
    refine ⟨N, χ, hχsmooth, hχcs, hsupp, ?_⟩
    -- On `K` one of the selected bumps equals one, so the telescoping product vanishes.
    intro x hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat, hxa⟩ := mem_iUnion.mp hxa
    let n : ℕ := ((t.equivFin ⟨a, hat⟩ : Fin N) : ℕ)
    have hn : n < N := (t.equivFin ⟨a, hat⟩).isLt
    have hfin : (⟨n, hn⟩ : Fin N) = t.equivFin ⟨a, hat⟩ := by
      apply Fin.ext
      change n = ((t.equivFin ⟨a, hat⟩ : Fin N) : ℕ)
      simp only [n]
    have hsymm : t.equivFin.symm (⟨n, hn⟩ : Fin N) = ⟨a, hat⟩ := by
      rw [hfin, Equiv.symm_apply_apply]
    have hpt : pt n = a := by
      have h1 : pt n = ((t.equivFin.symm (⟨n, hn⟩ : Fin N) : ↥t) : K) := by
        simp only [pt]
        rw [dite_eq_left hn]
      rw [h1, hsymm]
    have hψn : ψ n x = 1 := by
      rw [hψeq n hn, hpt]
      exact (β a).one_of_mem_closedBall (Metric.ball_subset_closedBall hxa)
    have hprod0 : ∏ k ∈ Finset.range N, (1 - ψ k x) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by rw [hψn]; ring)
    calc ∑ k ∈ Finset.range N, χ k x
        = ∑ k ∈ Finset.range N, ψ k x * ∏ l ∈ Finset.range k, (1 - ψ l x) := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [χ]
      _ = 1 - ∏ k ∈ Finset.range N, (1 - ψ k x) := sum_prod_telescope (fun k => ψ k x) N
      _ = 1 := by rw [hprod0]; ring

end CKN
