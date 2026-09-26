/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.BanLat.Pi
public import LeanPool.OrderClosures.BanLat.OrderContinuous.MeyerNieberg
public import LeanPool.OrderClosures.BanLat.LatticeSeminorm
public import LeanPool.OrderClosures.BanLat.Substructures.Sublattice
public import LeanPool.OrderClosures.BanLat.Tactic.LLexpr
public import LeanPool.OrderClosures.BanLat.Examples.CofK.Basic
public import LeanPool.OrderClosures.BanLat.Operators.Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic


/-!
# Order adherence

Shared definitions and results about order convergence, unbounded-order convergence,
solid hulls, and iterated order adherence used throughout the formalization.
-/

@[expose] public section

open Set

namespace OrderClosures

universe u v

section Convergence

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Unbounded-order convergence, defined using BanLat's `OrderConvergesTo`. -/
def UOConvergesTo {ι : Type v} [Preorder ι] (f : ι → X) (x : X) : Prop :=
  ∀ a : X, 0 ≤ a → OrderConvergesTo (fun i ↦ |f i - x| ⊓ a) 0

/-- The order adherence of a set: limits of order-convergent nets in the set. -/
def orderAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ OrderConvergesTo f x}

/-- The unbounded-order adherence of a set. -/
def uoAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ UOConvergesTo f x}

/-- A set is order closed when it contains the order limits of all its nets. -/
def IsOrderClosed (A : Set X) : Prop := orderAdherence A ⊆ A

/-- A set is unbounded-order closed when it contains the uo-limits of all its nets. -/
def IsUOClosed (A : Set X) : Prop := uoAdherence A ⊆ A

/-- The least order-closed set containing `A`. -/
def orderClosure (A : Set X) : Set X :=
  ⋂₀ {B : Set X | A ⊆ B ∧ IsOrderClosed B}

/-- The paper's directed-supremum description of the positive part of order adherence. -/
def directedPositiveAdherence (A : Set X) : Set X :=
  {x | 0 ≤ x ∧ ∃ B : Set X,
    B ⊆ A ∩ {y | 0 ≤ y} ∧ B.Nonempty ∧ DirectedOn (· ≤ ·) B ∧ IsLUB B x}

/-- For a solid set, order adherence is the solid hull of its directed positive suprema. -/
def solidOrderAdherence (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure (directedPositiveAdherence A)

/-- Finite iteration of order adherence. -/
def iteratedOrderAdherence (A : Set X) : ℕ → Set X
  | 0 => A
  | n + 1 => orderAdherence (iteratedOrderAdherence A n)

/-- A transfinite order-adherence tower. At limit stages it is the union of earlier stages. -/
structure OrderAdherenceTower (A : Set X) where
  /-- The set reached at each ordinal stage. -/
  stage : Ordinal.{u} → Set X
  stage_zero : stage 0 = A
  stage_succ : ∀ ξ, stage (Order.succ ξ) = orderAdherence (stage ξ)
  stage_limit : ∀ ξ, Order.IsSuccLimit ξ →
    stage ξ = ⋃ η : Set.Iio ξ, stage η.1

/-- At least `ξ` stages are needed when every earlier adherence step is proper. -/
def NeedsOrderAdherenceIterations (A : Set X) (ξ : Ordinal.{u}) : Prop :=
  ∃ T : OrderAdherenceTower A,
    ∀ η < ξ, T.stage η ⊂ T.stage (Order.succ η)

omit [VectorLattice X] in
/-- The generic net definition and the directed-positive definition agree for solid sets. -/
theorem orderAdherence_eq_solidOrderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    orderAdherence A = solidOrderAdherence A := by
  ext x
  constructor
  · rintro ⟨ι, hpre, hdir, hne, f, hfA, hf⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    rcases hf with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
    let : Preorder κ := hκpre
    let : IsDirected κ (· ≤ ·) := hκdir
    let : Nonempty κ := hκne
    let y : κ → X := fun k ↦ (|x| - r k)⁺
    have hy_mono : Monotone y := by
      intro k l hkl
      exact posPart_mono (sub_le_sub_left (hranti hkl) |x|)
    have hy_mem : ∀ k, y k ∈ A := by
      intro k
      obtain ⟨i, hi⟩ := (hbound k).exists
      have hx_le : |x| ≤ |f i| + r k := by
        calc
          |x| = |(x - f i) + f i| := by congr 1; abel
          _ ≤ |x - f i| + |f i| := abs_add_le _ _
          _ = |f i| + |x - f i| := add_comm _ _
          _ ≤ |f i| + r k := add_le_add_right (by simpa [abs_sub_comm] using hi) _
      have hsub : |x| - r k ≤ |f i| := sub_le_iff_le_add.mpr hx_le
      have hy_le : y k ≤ |f i| :=
        show (|x| - r k) ⊔ 0 ≤ |f i| from sup_le hsub (abs_nonneg _)
      exact hA (hfA i) (by simpa [y, abs_of_nonneg (posPart_nonneg _)] using hy_le)
    have hy_lub : IsLUB (Set.range y) |x| := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨k, rfl⟩
        exact show (|x| - r k) ⊔ 0 ≤ |x| from
          sup_le (sub_le_self _ (hrnonneg k)) (abs_nonneg _)
      · intro c hc
        have hlow : |x| - c ∈ lowerBounds (Set.range r) := by
          rintro _ ⟨k, rfl⟩
          have hraw : |x| - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
          exact sub_le_iff_le_add.mpr (by
            simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
        exact sub_nonpos.mp (hrglb.2 hlow)
    refine ⟨|x|, ?_, ?_⟩
    · refine ⟨abs_nonneg x, Set.range y, ?_, ?_, ?_, hy_lub⟩
      · rintro _ ⟨k, rfl⟩
        exact ⟨hy_mem k, posPart_nonneg _⟩
      · exact Set.range_nonempty y
      · rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
        obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k l
        exact ⟨y m, ⟨m, rfl⟩, hy_mono hkm, hy_mono hlm⟩
    · simp
  · rintro ⟨z, hz, hxz⟩
    rcases hz with ⟨hz, B, hBA, hBne, hBdir, hBlub⟩
    have hxz' : |x| ≤ z := by simpa [abs_of_nonneg hz] using hxz
    let : Nonempty B := hBne.to_subtype
    let : IsDirectedOrder B := hBdir.isDirectedOrder
    let b : B → X := fun w ↦ w.1
    have hb_mono : Monotone b := by
      intro p q hpq
      exact hpq
    have hb_range : Set.range b = B := by
      ext w
      simp [b]
    have hb_order : OrderConvergesTo b z :=
      orderConvergesTo_of_monotone_isLUB hb_mono (by simpa [hb_range] using hBlub)
    let g : B → X := fun w ↦ (x ⊓ b w) ⊔ (-b w)
    have hg_mem : ∀ w, g w ∈ A := by
      intro w
      have hw := hBA w.2
      have hg_upper : g w ≤ b w := by
        exact sup_le inf_le_right ((neg_nonpos.mpr hw.2).trans hw.2)
      have hg_lower : -g w ≤ b w := by
        simpa using neg_le_neg (show -b w ≤ g w from le_sup_right)
      have hg_abs : |g w| ≤ b w := (abs_le').2 ⟨hg_upper, hg_lower⟩
      exact hA hw.1 (by simpa [b, abs_of_nonneg hw.2] using hg_abs)
    have hxbounds : x ≤ z ∧ -x ≤ z := (abs_le').mp hxz'
    have hnegzx : -z ≤ x := by simpa using neg_le_neg hxbounds.2
    have hlim : x ⊓ z ⊔ -z = x := by
      rw [inf_eq_left.mpr hxbounds.1, sup_eq_left.mpr hnegzx]
    have hg_order : OrderConvergesTo g x := by
      have h := ((orderConvergesTo_const (X := X) (ι := B) x).inf hb_order).sup hb_order.neg
      simpa [g, hlim] using h
    exact ⟨B, inferInstance, inferInstance, inferInstance, g, hg_mem, hg_order⟩

omit [VectorLattice X] in
/-- Order adherence is extensive. -/
theorem subset_orderAdherence (A : Set X) : A ⊆ orderAdherence A := by
  intro x hx
  exact ⟨ULift.{u} PUnit, inferInstance, inferInstance, inferInstance,
    fun _ ↦ x, fun _ ↦ hx, orderConvergesTo_const x⟩

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Order adherence is monotone. -/
theorem orderAdherence_mono : Monotone (orderAdherence : Set X → Set X) := by
  intro A B hAB x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  exact ⟨ι, hpre, hdir, hne, f, fun i ↦ hAB (hf i), hfx⟩

omit [VectorLattice X] in
/-- Uo-adherence is extensive. -/
theorem subset_uoAdherence (A : Set X) : A ⊆ uoAdherence A := by
  intro x hx
  refine ⟨ULift.{u} PUnit, inferInstance, inferInstance, inferInstance,
    fun _ ↦ x, fun _ ↦ hx, ?_⟩
  intro a ha
  simpa [inf_eq_left.mpr ha] using
    (orderConvergesTo_const (ι := ULift.{u} PUnit) (0 : X))

omit [VectorLattice X] in
/-- Order convergence implies unbounded-order convergence. -/
theorem OrderConvergesTo.uoConvergesTo {ι : Type v} [Preorder ι]
      {f : ι → X} {x : X}
    (h : OrderConvergesTo f x) : UOConvergesTo f x := by
  intro a ha
  have hsub := h.sub (orderConvergesTo_const (ι := ι) x)
  have hinf := hsub.abs.inf (orderConvergesTo_const (ι := ι) a)
  simpa [inf_eq_left.mpr ha] using hinf

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Converts domination by an order-null net into order convergence to zero;
used to pass from uo-convergence to convergence of lattice clamps. -/
private theorem orderConvergesTo_zero_of_abs_le {ι : Type v} [Preorder ι]
    {f g : ι → X} (hg : OrderConvergesTo g 0) (hfg : ∀ i, |f i| ≤ |g i|) :
    OrderConvergesTo f 0 := by
  rcases hg with ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, hbound⟩
  refine ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, ?_⟩
  intro k
  exact (hbound k).mono fun i hi ↦ by
    simpa using (hfg i).trans (by simpa using hi)

omit [VectorLattice X] in
/-- Bounds the change of a lattice clamp by the clamped difference; used by
`UOConvergesTo.clamp` to obtain its controlling order-null net. -/
private theorem abs_clamp_le (x a : X) (ha : 0 ≤ a) :
    |(x ⊓ a) ⊔ (-a)| ≤ a := by
  apply (abs_le').2
  exact ⟨sup_le inf_le_right ((neg_nonpos.mpr ha).trans ha),
    by simpa using neg_le_neg (show -a ≤ (x ⊓ a) ⊔ (-a) from le_sup_right)⟩

omit [VectorLattice X] in
/-- Shows that clamping a uo-convergent net to a fixed order interval gives
order convergence; this is the key reduction in the adherence comparison. -/
private theorem UOConvergesTo.clamp {ι : Type v} [Preorder ι]
      {f : ι → X} {x : X}
    (h : UOConvergesTo f x) (a : X) (ha : 0 ≤ a) :
    OrderConvergesTo (fun i ↦ (f i ⊓ a) ⊔ (-a)) ((x ⊓ a) ⊔ (-a)) := by
  let c : X := (x ⊓ a) ⊔ (-a)
  let d : ι → X := fun i ↦ ((f i ⊓ a) ⊔ (-a)) - c
  have ht := h (a + a) (add_nonneg ha ha)
  have hd_bound : ∀ i, |d i| ≤ |(|f i - x| ⊓ (a + a))| := by
    intro i
    have hfirst : |d i| ≤ |f i - x| := by
      exact (abs_sup_sub_sup_le_abs (f i ⊓ a) (x ⊓ a) (-a)).trans
        (abs_inf_sub_inf_le_abs (f i) x a)
    have hsecond : |d i| ≤ a + a := by
      calc
        |d i| = |((f i ⊓ a) ⊔ (-a)) + -((x ⊓ a) ⊔ (-a))| := by
          simp [d, c, sub_eq_add_neg]
        _ ≤ |(f i ⊓ a) ⊔ (-a)| + |(x ⊓ a) ⊔ (-a)| := by
          simpa using abs_add_le ((f i ⊓ a) ⊔ (-a)) (-((x ⊓ a) ⊔ (-a)))
        _ ≤ a + a := add_le_add (abs_clamp_le _ _ ha) (abs_clamp_le _ _ ha)
    have ht_nonneg : 0 ≤ |f i - x| ⊓ (a + a) :=
      le_inf (abs_nonneg _) (add_nonneg ha ha)
    simpa [abs_of_nonneg ht_nonneg] using (le_inf hfirst hsecond)
  have hd : OrderConvergesTo d 0 := orderConvergesTo_zero_of_abs_le ht hd_bound
  have hsum := hd.add (orderConvergesTo_const (ι := ι) c)
  simpa [d, c] using hsum

/-- Gao--Leung, Lemma 2.1: the two adherences lie within two order-adherence steps. -/
theorem orderAdherence_subset_uoAdherence_subset {Y : VectorSublattice X} :
    orderAdherence (Y : Set X) ⊆ uoAdherence (Y : Set X) ∧
      uoAdherence (Y : Set X) ⊆ orderAdherence (orderAdherence (Y : Set X)) := by
  constructor
  · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    exact ⟨ι, inferInstance, inferInstance, inferInstance, f, hf,
      OrderConvergesTo.uoConvergesTo hfx⟩
  · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    let g : ι → X := fun i ↦ (x ⊓ |f i|) ⊔ (-|f i|)
    have hg_mem : ∀ i, g i ∈ orderAdherence (Y : Set X) := by
      intro i
      have hai : |f i| ∈ Y := Y.abs_mem (hf i)
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun j ↦ (f j ⊓ |f i|) ⊔ (-|f i|), ?_, ?_⟩
      · intro j
        exact Y.sup_mem (Y.inf_mem (hf j) hai) (Y.toSubmodule.neg_mem hai)
      · exact hfx.clamp |f i| (abs_nonneg _)
    have ht := hfx |x| (abs_nonneg x)
    have hdiff : OrderConvergesTo (fun i ↦ g i - x) 0 := by
      apply orderConvergesTo_zero_of_abs_le ht
      intro i
      dsimp [g]
      llarith
    have hg_order := hdiff.add (orderConvergesTo_const (ι := ι) x)
    refine ⟨ι, inferInstance, inferInstance, inferInstance, g, hg_mem, ?_⟩
    simpa [g] using hg_order

/-- If the uo-adherence is order closed, it is the order closure. -/
theorem uoAdherence_eq_orderClosure_of_isOrderClosed {Y : VectorSublattice X}
    (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderClosure (Y : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [orderClosure]
    apply Set.mem_sInter.mpr
    intro B hB
    rcases hB with ⟨hYB, hBclosed⟩
    have hadhYB : orderAdherence (Y : Set X) ⊆ B :=
      fun _ hz ↦ hBclosed (orderAdherence_mono hYB hz)
    have hdoubleYB : orderAdherence (orderAdherence (Y : Set X)) ⊆ B :=
      fun _ hz ↦ hBclosed (orderAdherence_mono hadhYB hz)
    exact hdoubleYB ((orderAdherence_subset_uoAdherence_subset (Y := Y)).2 hx)
  · intro x hx
    rw [orderClosure] at hx
    exact Set.mem_sInter.mp hx (uoAdherence (Y : Set X))
      ⟨subset_uoAdherence (Y : Set X), hY⟩

/-- The remaining equalities and stabilization stated after Gao--Leung Lemma 2.1. -/
theorem uoAdherence_eq_double_orderAdherence_and_stabilizes
    {Y : VectorSublattice X} (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderAdherence (orderAdherence (Y : Set X)) ∧
      orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (orderAdherence (Y : Set X)) := by
  have heq : uoAdherence (Y : Set X) =
      orderAdherence (orderAdherence (Y : Set X)) := by
    apply Set.Subset.antisymm
    · exact (orderAdherence_subset_uoAdherence_subset (Y := Y)).2
    · exact fun _ hx ↦ hY (orderAdherence_mono
        (orderAdherence_subset_uoAdherence_subset (Y := Y)).1 hx)
  refine ⟨heq, ?_⟩
  calc
    orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (uoAdherence (Y : Set X)) := congrArg orderAdherence heq.symm
    _ = uoAdherence (Y : Set X) := Set.Subset.antisymm hY
      (subset_orderAdherence (uoAdherence (Y : Set X)))
    _ = orderAdherence (orderAdherence (Y : Set X)) := heq

omit [VectorLattice X] in
/-- The order adherence of a solid set is solid. -/
theorem isSolid_orderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    LatticeOrderedAddCommGroup.IsSolid (orderAdherence A) := by
  rw [orderAdherence_eq_solidOrderAdherence hA]
  exact LatticeOrderedAddCommGroup.isSolid_solidClosure (directedPositiveAdherence A)

end Convergence

section Solidity

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- The least solid set containing `A`, using Mathlib's solid closure. -/
abbrev solidHull (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure A

/-- The interval-union description of the solid hull used in the paper. -/
theorem solidHull_eq_iUnion_Icc (A : Set X) :
    solidHull A = ⋃ a ∈ A, Set.Icc (-|a|) |a| := by
  ext x
  simp only [solidHull, LatticeOrderedAddCommGroup.solidClosure, Set.mem_ofPred_eq,
    Set.mem_iUnion, Set.mem_Icc]
  constructor
  · rintro ⟨a, ha, hxa⟩
    have hx_bounds := (abs_le').mp hxa
    refine ⟨a, ha, ?_, hx_bounds.1⟩
    simpa using neg_le_neg hx_bounds.2
  · rintro ⟨a, ha, hlow, hupp⟩
    refine ⟨a, ha, (abs_le').2 ⟨hupp, ?_⟩⟩
    simpa using neg_le_neg hlow

/-- The least cardinality of a set whose solid hull is `S`. -/
noncomputable def solidGeneratorNumber (S : Set X) : Cardinal :=
  sInf {κ : Cardinal | ∃ A : Set X, Cardinal.mk A = κ ∧ solidHull A = S}

/-- Scalar dilation of a set. -/
def scaleSet (a : ℝ) (A : Set X) [SMul ℝ X] : Set X :=
  (fun x ↦ a • x) '' A

/-- A set-theoretic unit ball for a specified real-valued norm. -/
def unitBallFor (p : X → ℝ) : Set X := {x | p x ≤ 1}

end Solidity

section CompletenessAndNorms

/-- Order completeness, stated without installing a second lattice instance. -/
def IsOrderComplete (X : Type u) [Preorder X] : Prop :=
  ∀ A : Set X, A.Nonempty → BddAbove A → ∃ x, IsLUB A x

/-- Install BanLat's order-complete lattice structure locally from the paper's
set-theoretic order-completeness predicate. -/
@[reducible]
noncomputable def conditionallyCompleteLatticeOfIsOrderComplete
    (X : Type u) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (hX : IsOrderComplete X) : ConditionallyCompleteLattice X :=
  conditionallyCompleteLatticeOfPosSet X fun _ hne hbdd => hX _ hne hbdd

/-- Density character: the least cardinality of a dense subset. -/
noncomputable def densityCharacter (X : Type u) [TopologicalSpace X] : Cardinal :=
  sInf {κ : Cardinal | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [Module ℝ X]

/-- A real lattice norm recorded independently of the ambient typeclass norm. -/
structure PaperLatticeNorm (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [Module ℝ X] where
  /-- The real-valued lattice norm. -/
  toFun : X → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  eq_zero_iff : ∀ x, toFun x = 0 ↔ x = 0
  add_le : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
  smul : ∀ (a : ℝ) x, toFun (a • x) = |a| * toFun x
  solid : ∀ {x y}, |x| ≤ |y| → toFun x ≤ toFun y

/-- Allows a bundled paper lattice norm to be applied as a function; used by
all subsequent Fatou and norm-comparison statements. -/
instance : CoeFun (PaperLatticeNorm X) (fun _ ↦ X → ℝ) := ⟨PaperLatticeNorm.toFun⟩

/-- Sequential completeness for the metric induced by `p`. -/
def IsCompleteFor (p : X → ℝ) : Prop :=
  ∀ f : ℕ → X,
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, p (f m - f n) < ε) →
      ∃ x, ∀ ε > 0, ∃ N, ∀ n ≥ N, p (f n - x) < ε

/-- Fatou's property for a specified lattice norm. -/
def HasFatouProperty (p : X → ℝ) : Prop :=
  ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → IsLUB (p '' Set.range f) (p x)

/-- Weak Fatou property with constant `K` for a specified lattice norm. -/
def HasWeakFatouProperty (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → ∀ c, (∀ i, p (f i) ≤ c) → p x ≤ K * c

/-- Equivalence of two norms through two positive comparison constants. -/
def EquivalentNorms (p q : X → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * p x ≤ q x ∧ q x ≤ C * p x

/-- The ambient norm as a paper lattice norm. -/
noncomputable def ambientLatticeNorm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] : PaperLatticeNorm Y where
  toFun := norm
  nonneg := norm_nonneg
  eq_zero_iff := fun _ ↦ norm_eq_zero
  add_le := norm_add_le
  smul := norm_smul
  solid := fun h ↦ HasSolidNorm.solid h

end CompletenessAndNorms

end OrderClosures
