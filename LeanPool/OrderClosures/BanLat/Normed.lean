/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence


/-!
# Normed vector lattices and Banach lattices

A **normed vector lattice** is a real vector lattice whose norm satisfies the solid
axiom: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. This single condition encodes compatibility
between the norm and the lattice structure. A **Banach lattice** is a normed vector
lattice whose norm is complete. This file develops the basic topology of normed
vector lattices, including continuity of lattice operations, closedness of the
positive cone, boundedness of order intervals, and monotone convergence facts.
-/

@[expose] public section

/-- A normed vector lattice is a real vector lattice equipped with a lattice norm:
a norm satisfying `|x| ≤ |y| → ‖x‖ ≤ ‖y‖`. -/
class NormedVectorLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends VectorLattice X, HasSolidNorm X, NormSMulClass ℝ X

namespace NormedVectorLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- A normed vector lattice is a normed space over `ℝ`. -/
instance instNormedSpace : NormedSpace ℝ X where
  norm_smul_le a x := (norm_smul a x).le

/-! ### Continuity of lattice operations -/

/-- Supremum is jointly norm-continuous. -/
theorem continuous_sup : Continuous (fun p : X × X => p.1 ⊔ p.2) :=
  ContinuousSup.continuous_sup

/-- Infimum is jointly norm-continuous. -/
theorem continuous_inf : Continuous (fun p : X × X => p.1 ⊓ p.2) :=
  ContinuousInf.continuous_inf

/-- The absolute value map is Lipschitz with constant 1; in particular it is continuous. -/
theorem lipschitzWith_abs : LipschitzWith 1 (|·| : X → X) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_abs_sub_abs a b

/-- The norm of the positive part is bounded by the norm. -/
theorem norm_posPart_le (x : X) : ‖x⁺‖ ≤ ‖x‖ := by
  refine norm_le_norm_of_abs_le_abs ?_
  rw [abs_of_nonneg (posPart_nonneg x)]
  exact posPart_le_abs x

/-! ### Archimedean property -/

/-- Every normed vector lattice is Archimedean in the vector-lattice sense: the only
non-negative element all of whose multiples are bounded is zero. -/
instance instIsVLArchimedean : IsVLArchimedean X := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx h
  by_contra hne
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
  obtain ⟨n, hn⟩ := exists_lt_nsmul hxpos ‖y‖
  have h1 : ‖n • x‖ ≤ ‖y‖ := by
    apply norm_le_norm_of_abs_le_abs
    calc |n • x| = n • x := abs_of_nonneg (nsmul_nonneg hx n)
      _ ≤ y := h n
      _ ≤ |y| := le_abs_self y
  rw [show (n • x : X) = (↑n : ℝ) • x from (Nat.cast_smul_eq_nsmul ℝ n x).symm,
      norm_smul, Real.norm_natCast] at h1
  simp only [nsmul_eq_mul] at hn
  linarith

/-! ### Closed positive cone and order topology -/

/-- The order relation is closed in a normed vector lattice. -/
instance instOrderClosedTopology : OrderClosedTopology X :=
  HasSolidNorm.orderClosedTopology

/-- The positive cone `{x | 0 ≤ x}` is norm-closed. -/
theorem isClosed_nonneg_cone : IsClosed {x : X | 0 ≤ x} := isClosed_nonneg

/-- Inequalities are preserved under norm limits: if `u n ≤ v n` for all `n`, and
`u n → a`, `v n → b` in norm, then `a ≤ b`. -/
theorem le_of_tendsto_of_tendsto {u v : ℕ → X} {a b : X}
    (hu : Filter.Tendsto u Filter.atTop (nhds a))
    (hv : Filter.Tendsto v Filter.atTop (nhds b))
    (h : ∀ n, u n ≤ v n) : a ≤ b :=
  le_of_tendsto_of_tendsto' hu hv h

/-! ### Monotone Convergence Lemma -/

/-- Monotone Convergence Lemma: an increasing sequence converging in norm is a least
upper bound for its range. -/
theorem isLUB_of_monotone_tendsto {u : ℕ → X} {l : X}
    (hmono : Monotone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsLUB (Set.range u) l :=
  isLUB_of_tendsto_atTop hmono hlim

/-- Antitone Convergence Lemma: a decreasing sequence converging in norm is a greatest
lower bound for its range. -/
theorem isGLB_of_antitone_tendsto {u : ℕ → X} {l : X}
    (hanti : Antitone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsGLB (Set.range u) l :=
  isGLB_of_tendsto_atTop hanti hlim

/-! ### Closed and bounded intervals -/

/-- Order intervals are norm-closed. -/
theorem isClosed_interval (a b : X) : IsClosed (Set.Icc a b) := isClosed_Icc

/-- Every element `x ∈ [a, b]` satisfies `‖x‖ ≤ ‖|a| ⊔ |b|‖`. In particular, every
order interval is norm-bounded. -/
theorem norm_le_norm_abs_sup_abs_of_mem_Icc {a b x : X} (hx : x ∈ Set.Icc a b) :
    ‖x‖ ≤ ‖|a| ⊔ |b|‖ := by
  rw [← norm_abs_eq_norm x]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (le_sup_of_le_left (abs_nonneg a))]
  rw [abs]
  apply sup_le
  · rw [abs]
    apply sup_le
    · exact le_trans hx.2 (le_trans (le_abs_self b) le_sup_right)
    · exact le_trans (neg_le_neg hx.1) (le_trans (neg_le_abs a) le_sup_left)
  · exact le_trans (neg_nonpos_of_nonneg (abs_nonneg x))
      (le_sup_of_le_left (abs_nonneg a))

/-- Order-bounded sets are norm-bounded. -/
theorem isBounded_of_bddBelow_bddAbove {s : Set X}
    (hl : BddBelow s) (hu : BddAbove s) : Bornology.IsBounded s := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  rw [Metric.isBounded_iff_subset_closedBall (0 : X)]
  exact ⟨‖|a| ⊔ |b|‖, fun x hx => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_norm_abs_sup_abs_of_mem_Icc ⟨ha hx, hb hx⟩⟩

end NormedVectorLattice

/-!
## Banach lattices
-/

/-- A Banach lattice is a normed vector lattice with a complete norm. -/
class BanachLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends NormedVectorLattice X, CompleteSpace X

/-- The real numbers form a normed vector lattice over themselves. -/
noncomputable instance : NormedVectorLattice ℝ where

/-- The real numbers form a Banach lattice over themselves. -/
noncomputable instance : BanachLattice ℝ where

/-!
## Completion of a normed vector lattice

The metric completion of a normed vector lattice carries a compatible lattice structure
making it again a normed vector lattice; being complete, it is a Banach lattice.
-/

section Completion

open UniformSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

private lemma uniformContinuous₂_sup_completion :
    UniformContinuous fun p : X × X => p.1 ⊔ p.2 := by
  have h : (fun p : X × X => p.1 ⊔ p.2) = fun p : X × X => p.1 + (p.2 - p.1)⁺ := by
    funext p
    exact sup_eq_add_posPart p.1 p.2
  rw [h]
  exact uniformContinuous_fst.add
    (lipschitzWith_posPart.uniformContinuous.comp (uniformContinuous_snd.sub uniformContinuous_fst))

private lemma uniformContinuous₂_inf_completion :
    UniformContinuous fun p : X × X => p.1 ⊓ p.2 := by
  have h : (fun p : X × X => p.1 ⊓ p.2) = fun p : X × X => -((-p.1) ⊔ (-p.2)) := by
    funext p
    rw [neg_sup, neg_neg, neg_neg]
  rw [h]
  exact (uniformContinuous₂_sup_completion.comp
    (uniformContinuous_fst.neg.prodMk uniformContinuous_snd.neg)).neg

/-- The completion of a normed vector lattice is a lattice. -/
noncomputable instance instLatticeCompletion : Lattice (Completion X) := by
  letI : Max (Completion X) := ⟨Completion.map₂ (fun x y : X => x ⊔ y)⟩
  letI : Min (Completion X) := ⟨Completion.map₂ (fun x y : X => x ⊓ y)⟩
  have coe_sup : ∀ x y : X, ((x ⊔ y : X) : Completion X) =
      (x : Completion X) ⊔ (y : Completion X) := fun x y => by
    rw [show (x : Completion X) ⊔ (y : Completion X) =
        Completion.map₂ (fun x y : X => x ⊔ y) x y from rfl,
      Completion.map₂_coe_coe x y (fun x y : X => x ⊔ y) uniformContinuous₂_sup_completion]
  have coe_inf : ∀ x y : X, ((x ⊓ y : X) : Completion X) =
      (x : Completion X) ⊓ (y : Completion X) := fun x y => by
    rw [show (x : Completion X) ⊓ (y : Completion X) =
        Completion.map₂ (fun x y : X => x ⊓ y) x y from rfl,
      Completion.map₂_coe_coe x y (fun x y : X => x ⊓ y) uniformContinuous₂_inf_completion]
  refine Lattice.mk' ?sup_comm ?sup_assoc ?inf_comm ?inf_assoc ?sup_inf_self ?inf_sup_self
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq (Completion.continuous_map₂ continuous_fst continuous_snd)
        (Completion.continuous_map₂ continuous_snd continuous_fst)
    · intro x y
      rw [← coe_sup, ← coe_sup, sup_comm]
  · intro x y z
    refine Completion.induction_on₃ x y z ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂
          (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd)))
    · intro x y z
      rw [← coe_sup, ← coe_sup, ← coe_sup, ← coe_sup, sup_assoc]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq (Completion.continuous_map₂ continuous_fst continuous_snd)
        (Completion.continuous_map₂ continuous_snd continuous_fst)
    · intro x y
      rw [← coe_inf, ← coe_inf, inf_comm]
  · intro x y z
    refine Completion.induction_on₃ x y z ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂
          (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd)))
    · intro x y z
      rw [← coe_inf, ← coe_inf, ← coe_inf, ← coe_inf, inf_assoc]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ continuous_fst continuous_snd))
        continuous_fst
    · intro x y
      rw [← coe_inf, ← coe_sup, sup_inf_self]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ continuous_fst continuous_snd))
        continuous_fst
    · intro x y
      rw [← coe_sup, ← coe_inf, inf_sup_self]

/-- The inclusion of a normed vector lattice into its completion preserves suprema. -/
@[norm_cast]
theorem coe_sup_completion (x y : X) :
    ((x ⊔ y : X) : Completion X) = (x : Completion X) ⊔ (y : Completion X) := by
  rw [show (x : Completion X) ⊔ (y : Completion X) =
      Completion.map₂ (fun x y : X => x ⊔ y) x y from rfl,
    Completion.map₂_coe_coe x y (fun x y : X => x ⊔ y) uniformContinuous₂_sup_completion]

/-- The inclusion of a normed vector lattice into its completion preserves infima. -/
@[norm_cast]
theorem coe_inf_completion (x y : X) :
    ((x ⊓ y : X) : Completion X) = (x : Completion X) ⊓ (y : Completion X) := by
  rw [show (x : Completion X) ⊓ (y : Completion X) =
      Completion.map₂ (fun x y : X => x ⊓ y) x y from rfl,
    Completion.map₂_coe_coe x y (fun x y : X => x ⊓ y) uniformContinuous₂_inf_completion]

/-- The inclusion of a normed vector lattice into its completion preserves absolute values. -/
@[norm_cast]
theorem coe_abs_completion (x : X) :
    ((|x| : X) : Completion X) = |(x : Completion X)| := by
  rw [abs, abs, ← Completion.coe_neg, ← coe_sup_completion]

private theorem completion_sup_add (x y z : Completion X) :
    (x + z) ⊔ (y + z) = (x ⊔ y) + z := by
  refine Completion.induction_on₃ x y z ?_ ?_
  · exact isClosed_eq
      (Completion.continuous_map₂
        (Completion.continuous_map₂ continuous_fst (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd)))
      (Completion.continuous_map₂
        (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
  · intro x y z
    rw [← Completion.coe_add, ← Completion.coe_add, ← coe_sup_completion,
      ← coe_sup_completion, ← Completion.coe_add, add_comm x z, add_comm y z,
      add_comm (x ⊔ y) z, ← add_sup]

/-- The order on the completion of a normed vector lattice is compatible with addition. -/
noncomputable instance instIsOrderedAddMonoidCompletion :
    IsOrderedAddMonoid (Completion X) := by
  refine
    { add_le_add_left := fun x y hxy z => ?_
      add_le_add_right := fun x y hxy z => ?_ }
  · rw [← sup_eq_right] at hxy ⊢
    rw [completion_sup_add, hxy]
  · rw [← sup_eq_right] at hxy ⊢
    rw [add_comm z x, add_comm z y, completion_sup_add, hxy]

private theorem completion_smul_sup_of_nonneg {r : ℝ} (hr : 0 ≤ r)
    (x y : Completion X) : r • (x ⊔ y) = r • x ⊔ r • y := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((Completion.continuous_map₂ continuous_fst continuous_snd).const_smul r)
      (Completion.continuous_map₂ (continuous_fst.const_smul r) (continuous_snd.const_smul r))
  · intro x y
    rw [← coe_sup_completion, ← Completion.coe_smul, ← Completion.coe_smul,
      ← Completion.coe_smul, ← coe_sup_completion, nonneg_smul_sup x y r hr]

noncomputable instance instVectorLatticeCompletion : VectorLattice (Completion X) where
  smul_le_smul_of_nonneg_left := by
    intro r hr x y hxy
    rw [← sup_eq_right] at hxy ⊢
    rw [← completion_smul_sup_of_nonneg hr, hxy]

private theorem continuous_sup_completion :
    Continuous fun p : Completion X × Completion X => p.1 ⊔ p.2 :=
  Completion.continuous_map₂ continuous_fst continuous_snd

private theorem continuous_inf_completion :
    Continuous fun p : Completion X × Completion X => p.1 ⊓ p.2 :=
  Completion.continuous_map₂ continuous_fst continuous_snd

private theorem continuous_abs_completion :
    Continuous (|·| : Completion X → Completion X) := by
  change Continuous fun x : Completion X => x ⊔ -x
  exact continuous_sup_completion.comp (continuous_id.prodMk continuous_neg)

omit [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X] in
private lemma exists_seq_coe_tendsto (a : Completion X) :
    ∃ u : ℕ → X, Filter.Tendsto (fun n => ((u n : Completion X))) Filter.atTop (nhds a) := by
  have ha : a ∈ closure (Set.range ((↑) : X → Completion X)) := by
    rw [(Completion.denseRange_coe (α := X)).closure_range]
    exact Set.mem_univ a
  obtain ⟨x, hxr, hxl⟩ := mem_closure_iff_seq_limit.mp ha
  choose u hu using hxr
  exact ⟨u, by simpa only [hu] using hxl⟩

/-- The completion of a normed vector lattice has a solid norm. -/
noncomputable instance instHasSolidNormCompletion : HasSolidNorm (Completion X) where
  solid := by
    intro a b hab
    have ha_le : a ≤ |b| := (abs_le'.mp hab).1
    have ha_ge : -|b| ≤ a := neg_le.mp (abs_le'.mp hab).2
    obtain ⟨u, hu⟩ := exists_seq_coe_tendsto a
    obtain ⟨v, hv⟩ := exists_seq_coe_tendsto b
    have hclampcont : Continuous fun p : Completion X × Completion X =>
        (p.1 ⊔ -|p.2|) ⊓ |p.2| := by
      have habs2 : Continuous fun p : Completion X × Completion X => |p.2| :=
        continuous_abs_completion.comp continuous_snd
      have hsup : Continuous fun p : Completion X × Completion X => p.1 ⊔ -|p.2| :=
        continuous_sup_completion.comp (continuous_fst.prodMk habs2.neg)
      exact continuous_inf_completion.comp (hsup.prodMk habs2)
    have hcoe : ∀ n, ((((u n ⊔ -|v n|) ⊓ |v n| : X)) : Completion X)
        = (↑(u n) ⊔ -|↑(v n)|) ⊓ |↑(v n)| := fun n => by
      rw [coe_inf_completion, coe_sup_completion, Completion.coe_neg, coe_abs_completion]
    have hprod : Filter.Tendsto (fun n => ((↑(u n), ↑(v n)) : Completion X × Completion X))
        Filter.atTop (nhds (a, b)) := hu.prodMk_nhds hv
    have hclamp := (hclampcont.tendsto (a, b)).comp hprod
    change Filter.Tendsto (fun n => (↑(u n) ⊔ -|↑(v n)|) ⊓ |↑(v n)|)
      Filter.atTop (nhds ((a ⊔ -|b|) ⊓ |b|)) at hclamp
    rw [sup_eq_left.mpr ha_ge, inf_eq_left.mpr ha_le] at hclamp
    have hwlim : Filter.Tendsto
        (fun n => (((u n ⊔ -|v n|) ⊓ |v n| : X) : Completion X)) Filter.atTop (nhds a) := by
      simpa only [hcoe] using hclamp
    have hnorm_w : Filter.Tendsto
        (fun n => ‖(((u n ⊔ -|v n|) ⊓ |v n| : X) : Completion X)‖) Filter.atTop (nhds ‖a‖) :=
      (continuous_norm.tendsto a).comp hwlim
    have hnorm_v : Filter.Tendsto (fun n => ‖((v n : Completion X))‖) Filter.atTop (nhds ‖b‖) :=
      (continuous_norm.tendsto b).comp hv
    refine le_of_tendsto_of_tendsto' hnorm_w hnorm_v (fun n => ?_)
    rw [Completion.norm_coe, Completion.norm_coe]
    refine HasSolidNorm.solid ?_
    have hc_le : (u n ⊔ -|v n|) ⊓ |v n| ≤ |v n| := inf_le_right
    have hneg_le : -|v n| ≤ (u n ⊔ -|v n|) ⊓ |v n| :=
      le_inf le_sup_right (le_trans (neg_nonpos_of_nonneg (abs_nonneg (v n))) (abs_nonneg (v n)))
    rw [abs_le']
    exact ⟨hc_le, by rwa [neg_le]⟩

/-- The completion of a normed vector lattice is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeCompletion :
    NormedVectorLattice (Completion X) where

/-- **The completion of a normed vector lattice is a Banach lattice.** -/
noncomputable instance instBanachLatticeCompletion : BanachLattice (Completion X) where

/-- The canonical inclusion into the completion preserves the isometry to `toComplₗᵢ`; it is
an isometry from `X` into its completion. -/
theorem isometry_coe_completion : Isometry ((↑) : X → Completion X) := by
  rw [← Completion.coe_toComplₗᵢ (𝕜 := ℝ)]
  exact (Completion.toComplₗᵢ (𝕜 := ℝ)).isometry

end Completion
