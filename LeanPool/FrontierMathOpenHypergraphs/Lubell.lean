/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Replicate
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.FrontierMathOpenHypergraphs.Basic
import LeanPool.FrontierMathOpenHypergraphs.Substitution
import LeanPool.FrontierMathOpenHypergraphs.Uniform

/-!
# Lubell frames and asymptotic context
-/

namespace HypergraphLowerBound

open private WitnessStrong WitnessStrong.toWitnessData apply_frameData ws_singleton
  exists_cover_subset_card_le_of_noLargePartition
  from LeanPool.FrontierMathOpenHypergraphs.Uniform

/-! ## The Lubell frame -/

/-- M_t = lcm { C(t-1, r) : 1 ≤ r ≤ t-1 }. -/
noncomputable def M (t : ℕ) : ℕ :=
  (Finset.Icc 1 (t - 1)).lcm (fun r => Nat.choose (t - 1) r)

/-- The multiplicity attached to each `j`-subset in the Lubell family. -/
noncomputable def lubellMultiplicity (t j : ℕ) : ℕ :=
  M t / Nat.choose (t - 1) (j - 1)

/-- The constant capacity vector of the Lubell frame. -/
noncomputable def lubellCap (t : ℕ) : Fin t → ℕ := Function.const (Fin t) (M t)

/-- Embed a `j`-subset of `[t]` into the type of support patterns. -/
private def supportPatternEmbedding {t j : ℕ} (hj : 2 ≤ j) :
    {S // S ∈ (((Finset.univ : Finset (Fin t)).powersetCard j).val)} ↪ SupportPattern t where
  toFun := fun S =>
    ⟨S.1, by
      have hmem : S.1 ∈ (Finset.univ : Finset (Fin t)).powersetCard j := by
        simp
      have hcard : S.1.card = j := (Finset.mem_powersetCard.mp hmem).2
      omega
    ⟩
  inj' := by
    intro a b h
    exact Subtype.ext <| congrArg (fun x : SupportPattern t => x.1) h

/-- All support patterns of size `j` on `[t]`, each occurring once. -/
noncomputable def supportPatternsOfCard (t j : ℕ) : Multiset (SupportPattern t) :=
  if hj : 2 ≤ j then
    ((((Finset.univ : Finset (Fin t)).powersetCard j).val.attach).map
      (supportPatternEmbedding (t := t) (j := j) hj))
  else
    0

/-- The `j`-subsets in the Lubell multiset, each with the prescribed multiplicity. -/
noncomputable def lubellLayer (t j : ℕ) : Multiset (SupportPattern t) :=
  (supportPatternsOfCard t j).bind fun S =>
    Multiset.replicate (lubellMultiplicity t j) S

/-- The Lubell support multiset on `[t]`. -/
noncomputable def lubellFrame (t : ℕ) : Multiset (SupportPattern t) :=
  (Finset.Icc 2 t).val.bind (lubellLayer t)

/-- The explicit cardinality expression for the Lubell frame. -/
noncomputable def lubellCardSum (t : ℕ) : ℕ :=
  (Finset.Icc 2 t).sum (fun j => Nat.choose t j * lubellMultiplicity t j)

private lemma supportPatternsOfCard_card (t j : ℕ) (hj : 2 ≤ j) :
    (supportPatternsOfCard t j).card = Nat.choose t j := by
  simp only [supportPatternsOfCard, hj, dite_true]
  rw [Multiset.card_map, Multiset.card_attach]
  simp [Finset.card_powersetCard, Fintype.card_fin]

private lemma lubellLayer_card (t j : ℕ) (hj : 2 ≤ j) :
    (lubellLayer t j).card = Nat.choose t j * lubellMultiplicity t j := by
  simp only [lubellLayer]
  rw [Multiset.card_bind]
  simp only [Function.comp, Multiset.card_replicate, Multiset.map_const',
    Multiset.sum_replicate, Nat.nsmul_eq_mul, supportPatternsOfCard_card t j hj]

/-- The omegaCount of a multiset is bounded by the count of elements satisfying
    the predicate times the maximum multiplicity. This is proved at the level of
    list indexing used in omegaCount. -/
private lemma omegaCount_le_card_filter {t : ℕ}
    (F : Multiset (SupportPattern t)) (T I : Finset (Fin t)) :
    omegaCount F T I ≤ F.card := by
  change ((Finset.univ : Finset (Fin F.card)).filter fun s =>
      (supportPatternAt F s).1 ⊆ T ∧ ((supportPatternAt F s).1 ∩ I).card = 1).card ≤ F.card
  calc ((Finset.univ.filter _).card : ℕ) ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = F.card := by simp [Fintype.card_fin]

/-! ### Vandermonde-Chu identity for the frame bound -/

/-- The divisibility property of M: C(t-1, r) divides M(t) for 1 ≤ r ≤ t-1. -/
private lemma M_dvd (t : ℕ) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ t - 1) :
    Nat.choose (t - 1) r ∣ M t :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hr1, hr2⟩)

/-- When I ⊆ T ⊆ Fin t, no support pattern S ⊆ T with |S| ≥ 2 has |S ∩ T| = 1
    when T = I (so T \ I = ∅). -/
private lemma omegaCount_eq_zero_of_sdiff_empty {t : ℕ}
    (F : Multiset (SupportPattern t)) (T I : Finset (Fin t))
    (hIT : I ⊆ T) (hTI : T \ I = ∅) :
    omegaCount F T I = 0 := by
  have hTeqI : T = I := by
    ext x; constructor
    · intro hx
      by_contra hxI
      exact Finset.notMem_empty x (hTI ▸ Finset.mem_sdiff.mpr ⟨hx, hxI⟩)
    · exact fun hx => hIT hx
  unfold omegaCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro s _
  push Not
  intro hST
  -- S ⊆ T = I, so S ∩ I = S, and |S| ≥ 2
  have hSI : supportSetAt F s ∩ I = supportSetAt F s :=
    Finset.inter_eq_left.mpr <| hTeqI ▸ hST
  rw [hSI]
  have h2 : 2 ≤ (supportSetAt F s).card := (supportPatternAt F s).2
  omega

/-! ### Infrastructure for the frame bound -/

/-- Counting list indices satisfying a predicate equals list countP. -/
private lemma list_filter_fin_eq_countP {α : Type*} (L : List α)
    (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin L.length)).filter (fun i => P (L.get i))).card =
    L.countP (fun b => decide (P b)) :=
  card_filter_univ_get_eq_countP_prop L P

/-- Index-based counting on a multiset equals filter cardinality. -/
private lemma multiset_index_filter_eq {α : Type*} (F : Multiset α)
    (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin F.card)).filter
      (fun i => P (F.toList.get ⟨i.val, by rw [Multiset.length_toList]; exact i.isLt⟩))).card =
    (Multiset.filter P F).card := by
  set L := F.toList
  have hlen : L.length = F.card := Multiset.length_toList F
  have rhs : (Multiset.filter P F).card = L.countP (fun b => decide (P b)) := by
    have : F = (L : Multiset α) := (Multiset.coe_toList F).symm
    rw [this, Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]
  rw [rhs]
  exact card_filter_univ_multiset_toList_eq_countP_prop F P

/-- omegaCount equals the cardinality of the filtered multiset. -/
private lemma oc_eq_filter_card {t : ℕ} (F : Multiset (SupportPattern t))
    (T I : Finset (Fin t)) :
    omegaCount F T I =
      (F.filter (fun S : SupportPattern t => S.1 ⊆ T ∧ (S.1 ∩ I).card = 1)).card := by
  unfold omegaCount supportSetAt
  exact multiset_index_filter_eq F (fun S : SupportPattern t => S.1 ⊆ T ∧ (S.1 ∩ I).card = 1)

/-- Filter of replicate gives conditional replicate. -/
private lemma filter_replicate_eq {α : Type*} (P : α → Prop) [DecidablePred P]
    (n : ℕ) (a : α) :
    Multiset.filter P (Multiset.replicate n a) =
      if P a then Multiset.replicate n a else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.filter_cons]
    simp only [ih]
    split <;> simp

/-! ### Vandermonde-Chu identity ingredients -/

/-- Hockey-stick identity, reindexed: Σ_{r=0}^{z} C(n-r, z-r) = C(n+1, z). -/
private lemma sum_choose_antidiag (n z : ℕ) (hz : z ≤ n) :
    (Finset.range (z + 1)).sum (fun r => Nat.choose (n - r) (z - r)) =
      Nat.choose (n + 1) z := by
  have step1 : ∀ r ∈ Finset.range (z + 1),
      Nat.choose (n - r) (z - r) = Nat.choose (n - r) (n - z) := by
    intro r hr; rw [Finset.mem_range] at hr
    have : n - r - (n - z) = z - r := by omega
    rw [← this]; exact Nat.choose_symm (by omega)
  rw [Finset.sum_congr rfl step1]
  have hockey := Nat.sum_Icc_choose n (n - z)
  have hchoose_eq : Nat.choose (n + 1) (n - z + 1) = Nat.choose (n + 1) z := by
    rw [← show n + 1 - z = n - z + 1 from by omega, Nat.choose_symm (by omega : z ≤ n + 1)]
  rw [hchoose_eq] at hockey; rw [← hockey]
  apply Finset.sum_nbij (fun r => n - r)
  · intro r hr
    have : r ≤ z := by simp [Finset.mem_range] at hr; omega
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro r₁ hr₁ r₂ hr₂ h
    have h1 : r₁ ≤ z := by simp at hr₁; omega
    have h2 : r₂ ≤ z := by simp at hr₂; omega
    dsimp at h; omega
  · intro m hm
    simp only [Set.mem_image, Finset.mem_coe]
    have hm' := hm; rw [Finset.mem_coe, Finset.mem_Icc] at hm'
    exact ⟨n - m, Finset.mem_range.mpr (by omega), by omega⟩
  · intros; rfl

/-- Binomial identity: C(t,z) * (t-z) = t * C(t-1,z) for 1 ≤ z ≤ t. -/
private lemma choose_mul_sub (t z : ℕ) (hz : z ≤ t) (hz1 : 1 ≤ z) :
    Nat.choose t z * (t - z) = t * Nat.choose (t - 1) z := by
  cases t with
  | zero => omega
  | succ t =>
    cases z with
    | zero => omega
    | succ z =>
      simp only [Nat.succ_sub_succ_eq_sub]
      have hpascal := Nat.choose_succ_succ t z
      have habsorb := Nat.choose_succ_right_eq t z
      calc Nat.choose (t + 1) (z + 1) * (t - z)
          = (Nat.choose t z + Nat.choose t (z + 1)) * (t - z) := by rw [hpascal]
        _ = Nat.choose t z * (t - z) + Nat.choose t (z + 1) * (t - z) := by ring
        _ = Nat.choose t (z + 1) * (z + 1) + Nat.choose t (z + 1) * (t - z) := by rw [habsorb]
        _ = Nat.choose t (z + 1) * (z + 1 + (t - z)) := by ring
        _ = Nat.choose t (z + 1) * (t + 1) := by congr 1; omega
        _ = (t + 1) * Nat.choose t (z + 1) := by ring

/-- Term identity: C(z,r) * (M/C(n,r)) * C(n,z) = M * C(n-r,z-r). -/
private lemma term_identity (n z r M : ℕ) (hr : r ≤ z)
    (hdvd : Nat.choose n r ∣ M) :
    Nat.choose z r * (M / Nat.choose n r) * Nat.choose n z =
    M * Nat.choose (n - r) (z - r) := by
  have hcm := @Nat.choose_mul (n := n) (k := z) (s := r) hr
  calc Nat.choose z r * (M / Nat.choose n r) * Nat.choose n z
      = (M / Nat.choose n r) * (Nat.choose n z * Nat.choose z r) := by ring
    _ = (M / Nat.choose n r) * (Nat.choose n r * Nat.choose (n - r) (z - r)) := by rw [hcm]
    _ = (M / Nat.choose n r * Nat.choose n r) * Nat.choose (n - r) (z - r) := by ring
    _ = (Nat.choose n r * (M / Nat.choose n r)) * Nat.choose (n - r) (z - r) := by ring
    _ = M * Nat.choose (n - r) (z - r) := by rw [Nat.mul_div_cancel' hdvd]

/-- Sum identity: [Σ_{r=0}^{z} C(z,r)*(M/C(n,r))] * C(n,z) = M * C(n+1,z). -/
private lemma sum_mul_choose_identity (n z M : ℕ) (hz : z ≤ n)
    (hdvd : ∀ r, r ≤ z → Nat.choose n r ∣ M) :
    (Finset.range (z + 1)).sum (fun r => Nat.choose z r * (M / Nat.choose n r)) *
      Nat.choose n z = M * Nat.choose (n + 1) z := by
  rw [Finset.sum_mul]
  have h1 : ∀ r ∈ Finset.range (z + 1),
      Nat.choose z r * (M / Nat.choose n r) * Nat.choose n z =
      M * Nat.choose (n - r) (z - r) := by
    intro r hr; rw [Finset.mem_range] at hr
    exact term_identity n z r M (by omega) (hdvd r (by omega))
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_choose_antidiag n z hz]

/-- Product identity: [Σ_{r=0}^{z} C(z,r)*(M/C(n,r))] * (n+1-z) = M*(n+1)
    when C(n,z) > 0, using the sum identity and C(n+1,z)*(n+1-z) = (n+1)*C(n,z). -/
private lemma full_sum_product_identity (n z M : ℕ) (hz : 1 ≤ z) (hzn : z ≤ n)
    (hdvd : ∀ r, r ≤ z → Nat.choose n r ∣ M) :
    (Finset.range (z + 1)).sum (fun r => Nat.choose z r * (M / Nat.choose n r)) *
      (n + 1 - z) = M * (n + 1) := by
  have hcnz_pos : 0 < Nat.choose n z := Nat.choose_pos hzn
  have hsum := sum_mul_choose_identity n z M hzn hdvd
  -- hsum: Σ * C(n,z) = M * C(n+1,z)
  have hcms := choose_mul_sub (n + 1) z (by omega) hz
  -- hcms: C(n+1,z) * (n+1-z) = (n+1) * C(n,z)
  -- We need: Σ * (n+1-z) = M * (n+1)
  -- From hsum: Σ * C(n,z) = M * C(n+1,z)
  -- Multiply by (n+1-z): Σ * C(n,z) * (n+1-z) = M * C(n+1,z) * (n+1-z) = M * (n+1) * C(n,z)
  -- Cancel C(n,z): Σ * (n+1-z) = M * (n+1)
  have h1 : (Finset.range (z + 1)).sum (fun r => Nat.choose z r * (M / Nat.choose n r)) *
      (n + 1 - z) * Nat.choose n z = M * (n + 1) * Nat.choose n z := by
    calc _ = (Finset.range (z + 1)).sum (fun r => Nat.choose z r * (M / Nat.choose n r)) *
            Nat.choose n z * (n + 1 - z) := by ring
      _ = M * Nat.choose (n + 1) z * (n + 1 - z) := by rw [hsum]
      _ = M * (Nat.choose (n + 1) z * (n + 1 - z)) := by ring
      _ = M * ((n + 1) * Nat.choose n z) := by
            rw [show (n + 1 - 1 : ℕ) = n from by omega] at hcms; rw [hcms]
      _ = M * (n + 1) * Nat.choose n z := by ring
  exact Nat.eq_of_mul_eq_mul_right hcnz_pos h1

/-- Counting bound: the number of j-subsets of T that intersect I in exactly 1 element
    is at most I.card * C(|T\I|, j-1). -/
private lemma good_subsets_le {t : ℕ} (j : ℕ)
    (T I : Finset (Fin t)) (_hIT : I ⊆ T) :
    ((T.powersetCard j).filter (fun S => (S ∩ I).card = 1)).card ≤
      I.card * Nat.choose ((T \ I).card) (j - 1) := by
  set goodSet := (T.powersetCard j).filter (fun S => (S ∩ I).card = 1) with hgood_def
  -- Cover goodSet by fibers indexed by elements of I
  have h_sub : goodSet ⊆ I.biUnion fun i => goodSet.filter fun S => i ∈ S := by
    intro S hS
    have hSmem := Finset.mem_filter.mp hS
    have hSI := hSmem.2
    have hne : (S ∩ I).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_biUnion]
    exact ⟨x, (Finset.mem_inter.mp hx).2,
      Finset.mem_filter.mpr ⟨hS, (Finset.mem_inter.mp hx).1⟩⟩
  -- Each fiber has card ≤ C(|T\I|, j-1) via injection S ↦ S.erase i
  have h_fib : ∀ i ∈ I,
      (goodSet.filter fun S => i ∈ S).card ≤ Nat.choose ((T \ I).card) (j - 1) := by
    intro i hi
    rw [show Nat.choose ((T \ I).card) (j - 1) =
        ((T \ I).powersetCard (j - 1)).card from
        (Finset.card_powersetCard (j - 1) (T \ I)).symm]
    apply Finset.card_le_card_of_injOn (Finset.erase · i)
    · -- MapsTo: S.erase i ∈ (T\I).powersetCard (j-1)
      intro S hS
      rw [Finset.mem_coe] at hS
      have hSmem := Finset.mem_filter.mp hS
      have hiS := hSmem.2
      have hSgood := Finset.mem_filter.mp hSmem.1
      have hSpow := Finset.mem_powersetCard.mp hSgood.1
      have hST := hSpow.1
      have hScard := hSpow.2
      have hSI := hSgood.2
      -- S ∩ I = {i}
      have hSI_eq : S ∩ I = {i} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hSI
        have : i ∈ ({a} : Finset (Fin t)) := ha ▸ Finset.mem_inter.mpr ⟨hiS, hi⟩
        rw [Finset.mem_singleton] at this; subst this; exact ha
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      constructor
      · -- S.erase i ⊆ T \ I
        intro v hv
        rw [Finset.mem_sdiff]
        constructor
        · exact hST (Finset.mem_of_mem_erase hv)
        · intro hvI
          have : v ∈ S ∩ I := Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hv, hvI⟩
          rw [hSI_eq, Finset.mem_singleton] at this
          exact absurd this (Finset.ne_of_mem_erase hv)
      · -- |S.erase i| = j - 1
        rw [Finset.card_erase_of_mem hiS, hScard]
    · -- InjOn: S₁.erase i = S₂.erase i → S₁ = S₂
      intro S₁ hS₁ S₂ hS₂ heq
      rw [Finset.mem_coe] at hS₁ hS₂
      have h1 := (Finset.mem_filter.mp hS₁).2
      have h2 := (Finset.mem_filter.mp hS₂).2
      dsimp at heq
      rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, heq]
  -- Combine
  calc goodSet.card
      ≤ (I.biUnion fun i => goodSet.filter fun S => i ∈ S).card := Finset.card_le_card h_sub
    _ ≤ I.card * Nat.choose ((T \ I).card) (j - 1) :=
        Finset.card_biUnion_le_card_mul I _ _ h_fib

/-- Sum of (if P then c else 0) over a multiset = c * (filter P).card. -/
private lemma sum_ite_eq_mul_filter_card {α : Type*} (m : Multiset α)
    (P : α → Prop) [DecidablePred P] (c : ℕ) :
    (m.map (fun a => if P a then c else 0)).sum = c * (m.filter P).card := by
  rw [← Multiset.countP_eq_card_filter]
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih]
    split <;> ring

/-- Filter cardinality of supportPatternsOfCard equals filter cardinality of powersetCard. -/
private lemma spoc_filter_card {t j : ℕ} (hj : 2 ≤ j)
    (Q : Finset (Fin t) → Prop) [DecidablePred Q] :
    ((supportPatternsOfCard t j).filter (fun S : SupportPattern t => Q S.1)).card =
      ((Finset.univ.powersetCard j).filter Q).card := by
  simp only [supportPatternsOfCard, hj, dite_true]
  rw [Multiset.filter_map, Multiset.card_map]
  set s := (Finset.univ : Finset (Fin t)).powersetCard j
  -- Both sides equal (s.val.filter Q).card
  have lhs : (Multiset.filter (((fun S : SupportPattern t => Q S.1) ∘
      ⇑(supportPatternEmbedding hj))) s.val.attach).card = (s.val.filter Q).card := by
    rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
    exact (Multiset.countP_congr rfl (fun x _ => rfl)).trans (Multiset.countP_attach Q s.val)
  exact lhs

/-- Splitting a range sum: (range (n+1)).sum f = f 0 + (range n).sum (fun i => f (i+1)). -/
private lemma sum_range_shift (f : ℕ → ℕ) (n : ℕ) :
    (Finset.range (n + 1)).sum f = f 0 + (Finset.range n).sum (fun i => f (i + 1)) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

/-- Per-layer bound: the filtered card of a Lubell layer is bounded. -/
private lemma layer_filter_card_bound {t : ℕ} (j : ℕ) (hj : 2 ≤ j)
    (T I : Finset (Fin t)) (hIT : I ⊆ T) :
    ((lubellLayer t j).filter
      (fun S : SupportPattern t => S.1 ⊆ T ∧ (S.1 ∩ I).card = 1)).card ≤
      I.card * Nat.choose ((T \ I).card) (j - 1) * (M t / Nat.choose (t - 1) (j - 1)) := by
  set c := M t / Nat.choose (t - 1) (j - 1) with hc_def
  set Q : Finset (Fin t) → Prop := fun S => S ⊆ T ∧ (S ∩ I).card = 1 with hQ_def
  change ((lubellLayer t j).filter (fun S : SupportPattern t => Q S.1)).card ≤ _
  simp only [lubellLayer]
  rw [Multiset.filter_bind]
  -- Fold c back into the goal
  change ((supportPatternsOfCard t j).bind fun a =>
    Multiset.filter (fun S : SupportPattern t => Q S.1) (Multiset.replicate c a)).card ≤ _
  simp_rw [filter_replicate_eq (fun S : SupportPattern t => Q S.1) c]
  rw [Multiset.card_bind]
  simp only [Function.comp, apply_ite Multiset.card, Multiset.card_replicate,
    Multiset.card_zero]
  rw [sum_ite_eq_mul_filter_card (supportPatternsOfCard t j)
    (fun S : SupportPattern t => Q S.1) c]
  rw [spoc_filter_card hj Q]
  have h_sub : ((Finset.univ.powersetCard j).filter Q) ⊆
      (T.powersetCard j).filter (fun S => (S ∩ I).card = 1) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard, hQ_def] at hS ⊢
    exact ⟨⟨hS.2.1, hS.1.2⟩, hS.2.2⟩
  calc c * ((Finset.univ.powersetCard j).filter Q).card
      ≤ c * ((T.powersetCard j).filter (fun S => (S ∩ I).card = 1)).card :=
        Nat.mul_le_mul_left c (Finset.card_le_card h_sub)
    _ ≤ c * (I.card * Nat.choose ((T \ I).card) (j - 1)) :=
        Nat.mul_le_mul_left c (good_subsets_le j T I hIT)
    _ = I.card * Nat.choose ((T \ I).card) (j - 1) * c := by ring

/-- The omegaCount of the Lubell frame is bounded by |T\I| * M(t).
    This is the core combinatorial lemma, using the Vandermonde-Chu identity
    ∑_{r=0}^{z} C(z,r)/C(n,r) = (n+1)/(n+1-z)
    to show ω_{L_t}(T,I) = |I| · M_t · z/(t-z) ≤ z · M_t. -/
private lemma lubell_omega_bound (t : ℕ) (ht : 2 ≤ t)
    (T I : Finset (Fin t)) (hIT : I ⊆ T) :
    omegaCount (lubellFrame t) T I ≤ (T \ I).card * M t := by
  -- Handle the case T \ I = ∅
  by_cases hTI : T \ I = ∅
  · rw [Finset.card_eq_zero.mpr hTI, Nat.zero_mul]
    exact Nat.le_of_eq (omegaCount_eq_zero_of_sdiff_empty _ T I hIT hTI)
  -- Now T \ I ≠ ∅, so z = |T\I| ≥ 1
  set z := (T \ I).card with hz_def
  have hz_pos : 1 ≤ z := by
    rw [hz_def]; exact Finset.one_le_card.mpr (Finset.nonempty_of_ne_empty hTI)
  -- z ≤ t - 1 (since T ⊆ Fin t and I is nonempty or not, but T\I ⊊ T ⊆ Fin t)
  have hzt : z ≤ t := by
    exact card_finset_fin_le (T \ I)
  -- |I| + z = |T|, so |I| ≤ t - z
  have hIz : I.card + z = T.card := by
    rw [hz_def]; have := Finset.card_sdiff_add_card_eq_card hIT; omega
  have hI_le : I.card ≤ t - z := by
    have hT_le : T.card ≤ t := by
      exact card_finset_fin_le T
    omega
  -- Case split: I empty or not
  by_cases hIcard : I.card = 0
  · -- I empty → omegaCount = 0
    suffices omegaCount (lubellFrame t) T I = 0 by omega
    rw [oc_eq_filter_card, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro S _ ⟨_, hSI⟩
    rw [Finset.card_eq_zero.mp hIcard, Finset.inter_empty, Finset.card_empty] at hSI
    exact absurd hSI (by omega)
  · -- I nonempty: z ≤ t - 1
    have hzt1 : z ≤ t - 1 := by omega
    -- Divisibility for the Vandermonde identity
    have hdvd : ∀ r, r ≤ z → Nat.choose (t - 1) r ∣ M t := by
      intro r hr
      by_cases hr0 : r = 0; · simp [hr0]
      simpa [hr0] using M_dvd t r (by omega) (by omega)
    -- Define f and tail_sum
    set f : ℕ → ℕ := fun r => Nat.choose z r * (M t / Nat.choose (t - 1) r) with hf_def
    have hf0 : f 0 = M t := by simp [hf_def]
    set tail_sum := (Finset.range z).sum (fun i => f (i + 1)) with hts_def
    -- Vandermonde identity: (range (z+1)).sum f * (t - z) = M t * t
    have hfull := full_sum_product_identity (t - 1) z (M t) hz_pos hzt1 hdvd
    rw [show t - 1 + 1 = t from by omega] at hfull
    -- Split the sum: (range (z+1)).sum f = M t + tail_sum
    have hsplit : (Finset.range (z + 1)).sum f = M t + tail_sum := by
      simpa [hf0] using sum_range_shift f z
    -- Key identity: tail_sum * (t - z) = z * M t
    have hkey : (t - z) * tail_sum = z * M t := by
      rw [hsplit, Nat.add_mul] at hfull
      have h2 : M t * t = M t * (t - z) + M t * z := by
        rw [← Nat.mul_add]; congr 1; omega
      lia
    -- omegaCount ≤ I.card * tail_sum (layer decomposition + per-layer bounds)
    have hoc_le : omegaCount (lubellFrame t) T I ≤ I.card * tail_sum := by
      rw [oc_eq_filter_card]
      show ((lubellFrame t).filter
        (fun S : SupportPattern t => S.1 ⊆ T ∧ (S.1 ∩ I).card = 1)).card ≤ _
      simp only [lubellFrame]
      rw [Multiset.filter_bind, Multiset.card_bind]
      -- Per-layer bound function
      set bound := fun j : ℕ =>
        I.card * Nat.choose z (j - 1) * (M t / Nat.choose (t - 1) (j - 1))
      -- Step 1: pointwise per-layer bounds
      apply le_trans
      · simpa using Multiset.sum_map_le_sum_map _ bound (fun j hj =>
          layer_filter_card_bound j ((Finset.mem_Icc.mp hj).1) T I hIT)
      -- Step 2: factor out I.card and identify f
      change ((Finset.Icc 2 t).val.map bound).sum ≤ I.card * tail_sum
      have h_bound_eq : ∀ j, bound j = I.card * f (j - 1) := by
        intro j; simp only [bound, hf_def]; ring
      simp_rw [h_bound_eq]
      rw [show (Multiset.map (fun j => I.card * f (j - 1)) (Finset.Icc 2 t).val).sum =
          (Finset.Icc 2 t).sum (fun j => I.card * f (j - 1)) from rfl,
        ← Finset.mul_sum]
      -- Step 3: (Icc 2 t).sum (fun j => f(j-1)) = tail_sum (reindexing)
      suffices h_eq : (Finset.Icc 2 t).sum (fun j => f (j - 1)) = tail_sum by
        rw [h_eq]
      rw [hts_def]
      -- Vanishing terms: f r = 0 for r > z
      have h_vanish : ∀ r : ℕ, z < r → f r = 0 := by
        intro r hr; simp only [hf_def, Nat.choose_eq_zero_of_lt hr, Nat.zero_mul]
      -- Reduce Icc 2 t to Icc 2 (z+1) by Finset.sum_subset (extra terms vanish)
      have h_sub : Finset.Icc 2 (z + 1) ⊆ Finset.Icc 2 t := by
        intro x hx; simp only [Finset.mem_Icc] at *; omega
      rw [← Finset.sum_subset h_sub (fun j hj1 hj2 => by
        apply h_vanish; simp only [Finset.mem_Icc] at hj1 hj2; omega)]
      -- Reindex: (Icc 2 (z+1)).sum (fun j => f(j-1)) = (range z).sum (fun i => f(i+1))
      -- Use Finset.sum_map with embedding (· + 2)
      have h_map : Finset.Icc 2 (z + 1) =
          (Finset.range z).map ⟨(· + 2), fun a b h => Nat.add_right_cancel h⟩ := by
        ext j; simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Icc,
          Function.Embedding.coeFn_mk]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨j - 2, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩; omega
      rw [h_map, Finset.sum_map]
      assumption
    -- Final calc
    calc omegaCount (lubellFrame t) T I
        ≤ I.card * tail_sum := hoc_le
      _ ≤ (t - z) * tail_sum := Nat.mul_le_mul_right _ hI_le
      _ = z * M t := hkey

/-- The Lubell multiset L_t is an (M_t, ..., M_t)-frame with
    |L_t| = M_t * t * (h_t - 1). -/
theorem lubell_is_frame (t : ℕ) (ht : 2 ≤ t) :
    IsFrame (lubellFrame t) (lubellCap t) ∧
    (lubellFrame t).card = lubellCardSum t := by
  constructor
  · -- Frame property: IsFrame (lubellFrame t) (lubellCap t)
    intro T I hIT
    simpa [lubellCap, Finset.sum_const, smul_eq_mul] using
      lubell_omega_bound t ht T I hIT
  · -- Cardinality
    change Multiset.card ((Finset.Icc 2 t).val.bind (lubellLayer t)) = lubellCardSum t
    rw [lubellCardSum]
    rw [Multiset.card_bind]
    congr 1
    apply Multiset.map_congr rfl
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    exact lubellLayer_card t j hj2

/-! ## Digit sum formula for k_n -/

/-- Sum of binary digits of m. -/
def s2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + s2 ((n + 1) / 2)
termination_by n => n
decreasing_by simp_all; omega

/-- The prefix sum of binary digit counts appearing in the formula for `k n`. -/
def digitSumPrefix (n : ℕ) : ℕ :=
  (Finset.range n).sum s2

private lemma s2_two_mul (m : ℕ) : s2 (2 * m) = s2 m := by
  cases m with
  | zero => rfl
  | succ n =>
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    conv_lhs => rw [h]; unfold s2
    have hmod : (2 * n + 2) % 2 = 0 := by omega
    have hdiv : (2 * n + 2) / 2 = n + 1 := by omega
    rw [hmod, hdiv]
    simp

private lemma s2_two_mul_add_one (m : ℕ) : s2 (2 * m + 1) = 1 + s2 m := by
  conv_lhs => unfold s2
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hmod, hdiv]

private lemma k_two_mul (m : ℕ) (hm : 1 ≤ m) : k (2 * m) = m + 2 * k m := by
  cases m with
  | zero => omega
  | succ n =>
    have h : 2 * (n + 1) = 2 * n + 2 := by ring
    conv_lhs => rw [h]; unfold k
    have hdiv1 : (2 * n + 2) / 2 = n + 1 := by omega
    have hdiv2 : (2 * n + 3) / 2 = n + 1 := by omega
    rw [hdiv1, hdiv2]
    simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private lemma k_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) :
    k (2 * m + 1) = m + k m + k (m + 1) := by
  cases m with
  | zero => omega
  | succ n =>
    have h : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    conv_lhs => rw [h]; unfold k
    have hdiv1 : (2 * n + 3) / 2 = n + 1 := by omega
    have hdiv2 : (2 * n + 4) / 2 = n + 2 := by omega
    rw [hdiv1, hdiv2]

-- Helper to avoid .sum vs ∑ notation mismatch
private lemma sum_range_succ' (f : ℕ → ℕ) (n : ℕ) :
    (Finset.range (n + 1)).sum f = (Finset.range n).sum f + f n :=
  @Finset.sum_range_succ ℕ _ f n

private lemma sum_s2_double (m : ℕ) :
    (Finset.range (2 * m)).sum s2 = m + 2 * (Finset.range m).sum s2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by omega,
        sum_range_succ', s2_two_mul_add_one,
        show 2 * n + 1 = (2 * n) + 1 from by omega,
        sum_range_succ', ih, s2_two_mul, sum_range_succ']
    omega

/-- k_n = n + Σ_{j=0}^{n-1} s_2(j), and k_n / (n log_2 n) → 1/2. -/
theorem digit_sum_formula (n : ℕ) (hn : 1 ≤ n) :
    k n = n + digitSumPrefix n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1
      simp [k, digitSumPrefix, s2]
    · have hn2 : 2 ≤ n := by omega
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- Even: n = m + m
        have hm2 : n = 2 * m := by omega
        subst hm2
        have hprefix : digitSumPrefix (2 * m) = m + 2 * digitSumPrefix m := by
          simpa [digitSumPrefix] using sum_s2_double m
        rw [k_two_mul m (by omega), ih m (by omega) (by omega), hprefix]
        omega
      · -- Odd: n = 2 * m + 1
        have hm2 : n = 2 * m + 1 := by omega
        subst hm2
        have hm_pos : 1 ≤ m := by omega
        rw [k_two_mul_add_one m hm_pos, ih m (by omega) (by omega),
            ih (m + 1) (by omega) (by omega)]
        have h_sum : digitSumPrefix (2 * m + 1) =
            m + 2 * digitSumPrefix m + s2 m := by
          rw [digitSumPrefix, sum_range_succ', sum_s2_double, s2_two_mul]
          simp [digitSumPrefix]
        rw [h_sum,
          show digitSumPrefix (m + 1) = digitSumPrefix m + s2 m by
            simp [digitSumPrefix, sum_range_succ']]
        omega

/-- The asymptotic coefficient `(h_t - 1) / log_2 t` appearing in the fixed-`t` bound. -/
noncomputable def fixedTCoeff (t : ℕ) : ℝ :=
  (((harmonic t : ℚ) : ℝ) - 1) / Real.logb 2 (t : ℝ)

private lemma IsFrame.mono {t : ℕ} {F : Multiset (SupportPattern t)}
    {cap₁ cap₂ : Fin t → ℕ} (hF : IsFrame F cap₁) (hcap : ∀ i, cap₁ i ≤ cap₂ i) :
    IsFrame F cap₂ := by
  intro T I hIT
  exact le_trans (hF T I hIT) <| Finset.sum_le_sum fun i _ => hcap i

private lemma omegaCount_nsmul {t : ℕ} (q : ℕ) (F : Multiset (SupportPattern t))
    (T I : Finset (Fin t)) :
    omegaCount (q • F) T I = q * omegaCount F T I := by
  rw [oc_eq_filter_card, Multiset.filter_nsmul, Multiset.card_nsmul, oc_eq_filter_card]

private lemma IsFrame.nsmul {t : ℕ} (q : ℕ)
    {F : Multiset (SupportPattern t)} {cap : Fin t → ℕ}
    (hF : IsFrame F cap) :
    IsFrame (q • F) (fun i => q * cap i) := by
  intro T I hIT
  rw [omegaCount_nsmul]
  calc
    q * omegaCount F T I ≤ q * (T \ I).sum cap := Nat.mul_le_mul_left q (hF T I hIT)
    _ = (T \ I).sum (fun i => q * cap i) := by rw [Finset.mul_sum]

private def exactWitnessSet (n : ℕ) : Set ℕ := {v : ℕ | WitnessStrong n v}

private noncomputable def exactWitnessSup (n : ℕ) : ℕ := sSup (exactWitnessSet n)

private theorem witnessStrong_le_H {n v : ℕ} (hw : WitnessStrong n v) : v ≤ H n := by
  let w : Witness n v := Classical.choose hw
  unfold H
  exact le_csSup (H_set_bddAbove n) ⟨w.edges, w.vertexCard, w.noLargePartition⟩

private theorem exactWitnessSet_bddAbove (n : ℕ) :
    BddAbove (exactWitnessSet n) := by
  refine ⟨H n, ?_⟩
  intro v hv
  exact witnessStrong_le_H hv

private theorem exactWitnessSup_spec (n : ℕ) (hn : 1 ≤ n) :
    WitnessStrong n (exactWitnessSup n) :=
  Nat.sSup_mem ⟨n, ws_singleton n hn⟩ (exactWitnessSet_bddAbove n)

private theorem exactWitnessSup_ge {n v : ℕ} (hw : WitnessStrong n v) :
    v ≤ exactWitnessSup n := by
  exact le_csSup (exactWitnessSet_bddAbove n) hw

private theorem exactWitnessSup_le_H (n : ℕ) (hn : 1 ≤ n) :
    exactWitnessSup n ≤ H n :=
  csSup_le ⟨n, ws_singleton n hn⟩ fun _ hv => witnessStrong_le_H hv

private theorem exactWitnessSup_singleton_lower (n : ℕ) (hn : 1 ≤ n) :
    n ≤ exactWitnessSup n :=
  exactWitnessSup_ge (ws_singleton n hn)

private lemma harmonic_sub_one_eq_sum_Icc (t : ℕ) (ht : 2 ≤ t) :
    (((harmonic t : ℚ) : ℝ) - 1) = ∑ j ∈ Finset.Icc 2 t, (j : ℝ)⁻¹ := by
  have hIcc : Finset.Icc 1 t = insert 1 (Finset.Icc 2 t) := by
    ext j
    simp [Finset.mem_Icc]
    omega
  calc
    (((harmonic t : ℚ) : ℝ) - 1)
        = (∑ j ∈ Finset.Icc 1 t, (j : ℝ)⁻¹) - 1 := by
            rw [harmonic_eq_sum_Icc, Rat.cast_sum]
            simp_rw [Rat.cast_inv, Rat.cast_natCast]
    _ = (1 : ℝ) + ∑ j ∈ Finset.Icc 2 t, (j : ℝ)⁻¹ - 1 := by
            rw [hIcc, Finset.sum_insert]
            · simp
            · simp
    _ = ∑ j ∈ Finset.Icc 2 t, (j : ℝ)⁻¹ := by ring

private lemma M_ne_zero (t : ℕ) (_ht : 2 ≤ t) : M t ≠ 0 := by
  intro hM
  rw [M, Finset.lcm_eq_zero_iff] at hM
  rcases hM with ⟨r, hr, hr0⟩
  exact (Nat.choose_pos (Finset.mem_Icc.mp hr).2).ne' hr0

private lemma M_pos (t : ℕ) (ht : 2 ≤ t) : 0 < M t :=
  Nat.pos_of_ne_zero (M_ne_zero t ht)

private lemma lubellCard_real (t : ℕ) (ht : 2 ≤ t) :
    (((lubellFrame t).card : ℕ) : ℝ) =
      (M t : ℝ) * (t : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
  have hcardNat : (lubellFrame t).card = lubellCardSum t := (lubell_is_frame t ht).2
  calc
    (((lubellFrame t).card : ℕ) : ℝ) = (lubellCardSum t : ℝ) := by exact_mod_cast hcardNat
    _ = ∑ j ∈ Finset.Icc 2 t, ((Nat.choose t j * lubellMultiplicity t j : ℕ) : ℝ) := by
          rw [lubellCardSum, Nat.cast_sum]
    _ = ∑ j ∈ Finset.Icc 2 t, (M t : ℝ) * (t : ℝ) / j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rcases Finset.mem_Icc.mp hj with ⟨hj2, hjt⟩
          have hdvd : Nat.choose (t - 1) (j - 1) ∣ M t := M_dvd t (j - 1) (by omega) (by omega)
          have hchoose_pos : 0 < Nat.choose (t - 1) (j - 1) := by
            exact Nat.choose_pos (by omega)
          have hden_ne : (((Nat.choose (t - 1) (j - 1) : ℕ) : ℝ)) ≠ 0 := by
            exact_mod_cast hchoose_pos.ne'
          have hj_ne : (j : ℝ) ≠ 0 := by positivity
          have hratio :
              (Nat.choose t j : ℝ) / Nat.choose (t - 1) (j - 1) = (t : ℝ) / j := by
              have hchoose_nat :
                  t * Nat.choose (t - 1) (j - 1) = Nat.choose t j * j := by
                have h := Nat.add_one_mul_choose_eq (t - 1) (j - 1)
                have ht_sub : t - 1 + 1 = t := by omega
                have hj_sub : j - 1 + 1 = j := by omega
                simpa [ht_sub, hj_sub] using h
              have hchoose :
                  (t : ℝ) * (Nat.choose (t - 1) (j - 1) : ℝ) =
                    (Nat.choose t j : ℝ) * j := by
                exact_mod_cast hchoose_nat
              exact (div_eq_div_iff hden_ne hj_ne).mpr (id (Eq.symm hchoose))
          calc
            ((Nat.choose t j * lubellMultiplicity t j : ℕ) : ℝ)
                = (Nat.choose t j : ℝ) * (lubellMultiplicity t j : ℝ) := by norm_num
            _ = (Nat.choose t j : ℝ) * ((M t : ℝ) / Nat.choose (t - 1) (j - 1)) := by
                  rw [lubellMultiplicity, Nat.cast_div_charZero hdvd]
            _ = (M t : ℝ) * ((Nat.choose t j : ℝ) / Nat.choose (t - 1) (j - 1)) := by ring
            _ = (M t : ℝ) * ((t : ℝ) / j) := by rw [hratio]
            _ = (M t : ℝ) * (t : ℝ) / j := by ring
    _ = (M t : ℝ) * (t : ℝ) * ∑ j ∈ Finset.Icc 2 t, (j : ℝ)⁻¹ := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.mul_sum]
    _ = (M t : ℝ) * (t : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
          rw [harmonic_sub_one_eq_sum_Icc t ht]

private lemma fixedTCoeff_eq_log_ratio (t : ℕ) (ht : 2 ≤ t) :
    fixedTCoeff t =
      Real.log 2 * ((((harmonic t : ℚ) : ℝ) - 1)) / Real.log (t : ℝ) := by
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)
  have ht_ne_one_nat : t ≠ 1 := by omega
  have ht_ne_one : (t : ℝ) ≠ 1 := by exact_mod_cast ht_ne_one_nat
  have hlogt_ne : Real.log (t : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) ht_ne_one
  rw [fixedTCoeff, Real.logb]
  calc
    ((((harmonic t : ℚ) : ℝ) - 1) / (Real.log (t : ℝ) / Real.log 2))
        = ((((harmonic t : ℚ) : ℝ) - 1) * Real.log 2) / Real.log (t : ℝ) := by
            field_simp [hlog2_ne, hlogt_ne]
    _ = Real.log 2 * ((((harmonic t : ℚ) : ℝ) - 1)) / Real.log (t : ℝ) := by ring

private lemma fixedTCoeff_mul_logb_eq (t : ℕ) (ht : 2 ≤ t) (x : ℕ) :
    fixedTCoeff t * (x : ℝ) * Real.logb 2 (x : ℝ) =
      ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) * (x : ℝ) * Real.log (x : ℝ) := by
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)
  have ht_ne_one_nat : t ≠ 1 := by omega
  have ht_ne_one : (t : ℝ) ≠ 1 := by exact_mod_cast ht_ne_one_nat
  have hlogt_ne : Real.log (t : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) ht_ne_one
  rw [fixedTCoeff_eq_log_ratio t ht, Real.logb]
  field_simp [hlog2_ne, hlogt_ne]

private lemma fixedTCoeff_nonneg (t : ℕ) (ht : 2 ≤ t) : 0 ≤ fixedTCoeff t := by
  rw [fixedTCoeff_eq_log_ratio t ht]
  have hlogt_pos : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  rw [harmonic_sub_one_eq_sum_Icc t ht]
  positivity

private lemma log_le_harmonic (t : ℕ) (ht : 2 ≤ t) :
    Real.log (t : ℝ) ≤ ((harmonic t : ℚ) : ℝ) := by
  have hmain :
      Real.log (t : ℝ) ≤ ((harmonic (t - 1) : ℚ) : ℝ) := by
    have h := log_add_one_le_harmonic (t - 1)
    have ht' : t - 1 + 1 = t := by omega
    rw [ht'] at h
    exact h
  have hsucc :
      ((harmonic t : ℚ) : ℝ) = ((harmonic (t - 1) : ℚ) : ℝ) + (t : ℝ)⁻¹ := by
    have hsuccq : harmonic t = harmonic (t - 1) + (↑t : ℚ)⁻¹ := by
      have h := harmonic_succ (t - 1)
      have ht' : t - 1 + 1 = t := by omega
      rw [ht'] at h
      exact h
    simpa [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) hsuccq
  have hnonneg : 0 ≤ (t : ℝ)⁻¹ := by positivity
  calc
    Real.log (t : ℝ) ≤ ((harmonic (t - 1) : ℚ) : ℝ) := hmain
    _ ≤ ((harmonic (t - 1) : ℚ) : ℝ) + (t : ℝ)⁻¹ := by linarith
    _ = ((harmonic t : ℚ) : ℝ) := by rw [hsucc]

private lemma fixedTCoeff_lower (t : ℕ) (ht : 2 ≤ t) :
    Real.log 2 * (1 - 1 / Real.log (t : ℝ)) ≤ fixedTCoeff t := by
  have hlogt_pos : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  have hlogt_ne : Real.log (t : ℝ) ≠ 0 := hlogt_pos.ne'
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hnum_lower : Real.log (t : ℝ) - 1 ≤ (((harmonic t : ℚ) : ℝ) - 1) := by
    have hlog_le_harmonic :
        Real.log (t : ℝ) ≤ ((harmonic t : ℚ) : ℝ) :=
      log_le_harmonic t ht
    linarith
  calc
    Real.log 2 * (1 - 1 / Real.log (t : ℝ))
        = Real.log 2 * (Real.log (t : ℝ) - 1) / Real.log (t : ℝ) := by
            field_simp [hlogt_ne]
    _ ≤ Real.log 2 * ((((harmonic t : ℚ) : ℝ) - 1)) / Real.log (t : ℝ) := by
          have hmul :
              Real.log 2 * (Real.log (t : ℝ) - 1) ≤
                Real.log 2 * ((((harmonic t : ℚ) : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left hnum_lower hlog2_pos.le
          exact (div_le_div_of_nonneg_right hmul hlogt_pos.le)
    _ = fixedTCoeff t := (fixedTCoeff_eq_log_ratio t ht).symm

private noncomputable def lubellQ (t n : ℕ) : ℕ := n / (t * M t)

private noncomputable def lubellR (t n : ℕ) : ℕ := n % (t * M t)

private noncomputable def lubellRem (t n : ℕ) (i : Fin t) : ℕ :=
  lubellR t n / t + if i.1 < lubellR t n % t then 1 else 0

private noncomputable def lubellPart (t n : ℕ) (i : Fin t) : ℕ :=
  lubellQ t n * M t + lubellRem t n i

private lemma lubell_decomp (t n : ℕ) :
    n = t * (lubellQ t n * M t) + lubellR t n := by
  unfold lubellQ lubellR
  calc
    n = n % (t * M t) + (t * M t) * (n / (t * M t)) := by
          symm
          exact Nat.mod_add_div n (t * M t)
    _ = n % (t * M t) + t * (n / (t * M t) * M t) := by ring
    _ = t * (n / (t * M t) * M t) + n % (t * M t) := by ring

private lemma lubellRem_sum (t n : ℕ) (ht : 2 ≤ t) :
    ((Finset.univ : Finset (Fin t)).sum (lubellRem t n)) = lubellR t n := by
  have ht_pos : 0 < t := by omega
  have hcount :
      ((Finset.univ : Finset (Fin t)).filter fun i => i.1 < lubellR t n % t).card =
        lubellR t n % t := by
    simpa [min_eq_right (Nat.mod_lt _ ht_pos).le] using
      (Fin.card_filter_val_lt (n := t) (m := lubellR t n % t))
  have hsum_ite :
      ((Finset.univ : Finset (Fin t)).sum fun i => if i.1 < lubellR t n % t then 1 else 0) =
        lubellR t n % t := by
    simp [hcount]
  calc
    ((Finset.univ : Finset (Fin t)).sum (lubellRem t n))
        = ((Finset.univ : Finset (Fin t)).sum fun _ => lubellR t n / t) +
            ((Finset.univ : Finset (Fin t)).sum
              fun i => if i.1 < lubellR t n % t then 1 else 0) := by
              simp [lubellRem, Finset.sum_add_distrib]
    _ = t * (lubellR t n / t) + lubellR t n % t := by
          rw [hsum_ite]
          simp [Finset.sum_const, Fintype.card_fin]
    _ = lubellR t n := by
          exact Nat.div_add_mod (lubellR t n) t

private lemma lubellPart_sum (t n : ℕ) (ht : 2 ≤ t) :
    ((Finset.univ : Finset (Fin t)).sum (lubellPart t n)) = n := by
  calc
    ((Finset.univ : Finset (Fin t)).sum (lubellPart t n))
        = t * (lubellQ t n * M t) + ((Finset.univ : Finset (Fin t)).sum (lubellRem t n)) := by
            simp [lubellPart, Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin]
    _ = t * (lubellQ t n * M t) + lubellR t n := by rw [lubellRem_sum t n ht]
    _ = n := by exact (lubell_decomp t n).symm

private lemma lubellPart_ge_qM (t n : ℕ) (i : Fin t) :
    lubellQ t n * M t ≤ lubellPart t n i := by
  simp [lubellPart, lubellRem]

private lemma lubellQ_pos (t n : ℕ) (ht : 2 ≤ t) (hn : t * M t ≤ n) :
    1 ≤ lubellQ t n := by
  unfold lubellQ
  exact
    (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (M_pos t ht))).2
      (by simpa [one_mul] using hn)

private lemma lubellRem_le_M (t n : ℕ) (ht : 2 ≤ t) (i : Fin t) :
    lubellRem t n i ≤ M t := by
  have ht_pos : 0 < t := by omega
  have hM_pos : 0 < M t := M_pos t ht
  have hr_lt : lubellR t n < t * M t := by
    unfold lubellR
    exact Nat.mod_lt _ (Nat.mul_pos ht_pos hM_pos)
  have hdiv_lt : lubellR t n / t < M t := by
    exact
      (Nat.div_lt_iff_lt_mul ht_pos).2
        (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hr_lt)
  by_cases hi : i.1 < lubellR t n % t
  · simp only [lubellRem, hi, ↓reduceIte, ge_iff_le]
    exact Nat.succ_le_of_lt hdiv_lt
  · simp [lubellRem, hi, le_of_lt hdiv_lt]

private lemma lubellPart_pos (t n : ℕ) (ht : 2 ≤ t) (hq : 1 ≤ lubellQ t n) (i : Fin t) :
    1 ≤ lubellPart t n i := by
  have hM_pos : 0 < M t := M_pos t ht
  calc
    1 ≤ lubellQ t n * M t := by
          exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) hM_pos)
    _ ≤ lubellPart t n i := lubellPart_ge_qM t n i

private lemma lubellPart_lt (t n : ℕ) (ht : 2 ≤ t) (hn : t * M t ≤ n)
    (i : Fin t) : lubellPart t n i < n := by
  have hq : 1 ≤ lubellQ t n := lubellQ_pos t n ht hn
  have hqM_pos : 0 < lubellQ t n * M t := Nat.mul_pos (by omega) (M_pos t ht)
  have hqM_ge_M : M t ≤ lubellQ t n * M t := by
    simpa using Nat.mul_le_mul_right (M t) hq
  by_cases hr0 : lubellR t n = 0
  · have hrem0 : lubellRem t n i = 0 := by simp [lubellRem, hr0]
    have hdecomp : n = t * (lubellQ t n * M t) := by simpa [hr0] using lubell_decomp t n
    set x := lubellQ t n * M t
    have hx_pos : 0 < x := by simpa [x] using hqM_pos
    have hlt : x < n := by
      have hxt : x < x * t := by
        exact (Nat.lt_mul_iff_one_lt_right hx_pos).2 (by omega)
      lia
    simpa [lubellPart, hrem0, x] using hlt
  · have hpart_le : lubellPart t n i ≤ lubellQ t n * M t + M t := by
      simpa [lubellPart] using Nat.add_le_add_left (lubellRem_le_M t n ht i) (lubellQ t n * M t)
    have htwo_le : lubellQ t n * M t + M t ≤ t * (lubellQ t n * M t) := by
      have h2 :
          lubellQ t n * M t + M t ≤
            lubellQ t n * M t + lubellQ t n * M t :=
        Nat.add_le_add_left hqM_ge_M _
      have h3 :
          lubellQ t n * M t + lubellQ t n * M t = 2 * (lubellQ t n * M t) := by ring
      have h4 : 2 * (lubellQ t n * M t) ≤ t * (lubellQ t n * M t) := by
        exact Nat.mul_le_mul_right _ ht
      exact le_trans (h3 ▸ h2) h4
    have htx_lt_n : t * (lubellQ t n * M t) < n := by
      have hr_pos : 0 < lubellR t n := Nat.pos_of_ne_zero hr0
      have hdecomp := lubell_decomp t n
      omega
    exact lt_of_le_of_lt (le_trans hpart_le htwo_le) htx_lt_n

private lemma lubellPart_sum_mul_log (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log ((n : ℝ) / t) ≤
      ((Finset.univ : Finset (Fin t)).sum
        fun i => (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) := by
  have ht_pos : 0 < (t : ℝ) := by positivity
  have ht_ne : (t : ℝ) ≠ 0 := ht_pos.ne'
  have hsumParts :
      (∑ i ∈ (Finset.univ : Finset (Fin t)), (lubellPart t n i : ℝ)) = n := by
    exact_mod_cast lubellPart_sum t n ht
  have hJensen :=
    Real.convexOn_mul_log.map_sum_le
      (t := (Finset.univ : Finset (Fin t)))
      (w := fun _ => (1 : ℝ) / t)
      (p := fun i => (lubellPart t n i : ℝ))
      (by
        exact fun i a => Nat.one_div_cast_nonneg t)
      (by
        rw [Finset.sum_const, nsmul_eq_mul]
        have h : (t : ℝ) * (1 / t) = 1 := by
          field_simp [ht_ne]
        simpa using h)
      (by
        intro i hi
        change 0 ≤ (lubellPart t n i : ℝ)
        positivity)
  have havg :
      (∑ i ∈ (Finset.univ : Finset (Fin t)), (1 : ℝ) / t * (lubellPart t n i : ℝ)) =
        (n : ℝ) / t := by
    rw [← Finset.mul_sum, hsumParts]
    ring
  have hJensen' :
      ((n : ℝ) / t) * Real.log ((n : ℝ) / t) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin t)),
          (1 : ℝ) / t * ((lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) := by
    have hJensen'' :
        (∑ i ∈ (Finset.univ : Finset (Fin t)),
            (1 : ℝ) / t * (lubellPart t n i : ℝ)) *
            Real.log (∑ i ∈ (Finset.univ : Finset (Fin t)),
              (1 : ℝ) / t * (lubellPart t n i : ℝ)) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin t)),
            (1 : ℝ) / t * ((lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) := by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hJensen
    lia
  calc
    (n : ℝ) * Real.log ((n : ℝ) / t)
        = (t : ℝ) * (((n : ℝ) / t) * Real.log ((n : ℝ) / t)) := by
            field_simp [ht_ne]
    _ ≤ (t : ℝ) *
          ∑ i ∈ (Finset.univ : Finset (Fin t)),
            (1 : ℝ) / t * ((lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hJensen' ht_pos.le
    _ = ((Finset.univ : Finset (Fin t)).sum
          fun i => (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp [ht_ne]

private lemma lubell_bonus_lower (t n : ℕ) (ht : 2 ≤ t) :
    (lubellQ t n : ℝ) * ((((lubellFrame t).card : ℕ) : ℝ)) ≥
      (n : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) - ((((lubellFrame t).card : ℕ) : ℝ)) := by
  let b : ℝ := (((harmonic t : ℚ) : ℝ) - 1)
  have hcard :
      ((((lubellFrame t).card : ℕ) : ℝ)) = ((t * M t : ℕ) : ℝ) * b := by
    dsimp [b]
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using lubellCard_real t ht
  have hdecomp :
      (n : ℝ) * b =
        (lubellQ t n : ℝ) * (((t * M t : ℕ) : ℝ) * b) + (lubellR t n : ℝ) * b := by
    have hnat : (n : ℝ) = (t * (lubellQ t n * M t) : ℕ) + lubellR t n := by
      exact_mod_cast lubell_decomp t n
    rw [hnat]
    norm_num
    ring
  have hrle :
      (lubellR t n : ℝ) * b ≤ ((t * M t : ℕ) : ℝ) * b := by
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      rw [harmonic_sub_one_eq_sum_Icc t ht]
      positivity
    gcongr
    exact_mod_cast (Nat.mod_lt n (Nat.mul_pos (by omega) (M_pos t ht))).le
  have hmain :
      (n : ℝ) * b ≤
        (lubellQ t n : ℝ) * ((((lubellFrame t).card : ℕ) : ℝ)) +
          ((((lubellFrame t).card : ℕ) : ℝ)) := by
    calc
      (n : ℝ) * b
          = (lubellQ t n : ℝ) * (((t * M t : ℕ) : ℝ) * b) +
              (lubellR t n : ℝ) * b := hdecomp
      _ = (lubellQ t n : ℝ) * ((((lubellFrame t).card : ℕ) : ℝ)) +
            (lubellR t n : ℝ) * b := by rw [← hcard]
      _ ≤ (lubellQ t n : ℝ) * ((((lubellFrame t).card : ℕ) : ℝ)) +
            ((((lubellFrame t).card : ℕ) : ℝ)) := by
            linarith
  linarith

private theorem exactWitnessSup_lubell_step (t n : ℕ) (ht : 2 ≤ t) (hn : t * M t ≤ n) :
    exactWitnessSup n ≥
      ((Finset.univ : Finset (Fin t)).sum fun i => exactWitnessSup (lubellPart t n i)) +
        lubellQ t n * (lubellFrame t).card := by
  classical
  have hq : 1 ≤ lubellQ t n := lubellQ_pos t n ht hn
  have hw : ∀ i, WitnessStrong (lubellPart t n i) (exactWitnessSup (lubellPart t n i)) :=
    fun i => exactWitnessSup_spec (lubellPart t n i) (lubellPart_pos t n ht hq i)
  have hframe0 : IsFrame (lubellFrame t) (lubellCap t) := (lubell_is_frame t ht).1
  have hframeQ : IsFrame (lubellQ t n • lubellFrame t) (fun _ => lubellQ t n * M t) := by
    simpa [lubellCap, smul_eq_mul] using IsFrame.nsmul (q := lubellQ t n) hframe0
  have hframePart : IsFrame (lubellQ t n • lubellFrame t) (lubellPart t n) :=
    IsFrame.mono hframeQ (lubellPart_ge_qM t n)
  have happly :=
    apply_frameData (lubellQ t n • lubellFrame t) (lubellPart t n)
      (fun i => exactWitnessSup (lubellPart t n i))
      (lubellQ t n * (lubellFrame t).card)
      (Multiset.card_nsmul (lubellFrame t) (lubellQ t n))
      hframePart hw
  have hwit :
      WitnessStrong n
        (((Finset.univ : Finset (Fin t)).sum fun i => exactWitnessSup (lubellPart t n i)) +
          lubellQ t n * (lubellFrame t).card) := by
    simpa [lubellPart_sum t n ht] using happly
  exact exactWitnessSup_ge hwit

private theorem fixed_t_bound_exact (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (exactWitnessSup n : ℝ) ≥
        fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) - C * ((n : ℝ) - 1) := by
  let N : ℕ := t * M t
  let B : ℝ := (((lubellFrame t).card : ℕ) : ℝ)
  let C : ℝ := fixedTCoeff t * (N : ℝ) * Real.logb 2 (N : ℝ) + B + 1
  have hcoeff_nonneg : 0 ≤ fixedTCoeff t := fixedTCoeff_nonneg t ht
  have hN_two : 2 ≤ N := by
    have hM_one : 1 ≤ M t := Nat.succ_le_of_lt (M_pos t ht)
    exact le_mul_of_le_of_one_le ht hM_one
  have hN_one : 1 ≤ N := by omega
  have hlogN_nonneg : 0 ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hN_one)
  have hB_nonneg : 0 ≤ B := by
    positivity
  have hcoeff_term_nonneg : 0 ≤ fixedTCoeff t * (N : ℝ) * Real.logb 2 (N : ℝ) := by
    positivity
  have hC_pos : 0 < C := by
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hsmall : n < N
      · by_cases hn1 : n = 1
        · subst hn1
          norm_num [Real.logb]
        · have hW : (n : ℝ) ≤ exactWitnessSup n := by
            exact_mod_cast exactWitnessSup_singleton_lower n hn
          have hlog_le :
              Real.logb 2 (n : ℝ) ≤ Real.logb 2 (N : ℝ) := by
            apply Real.logb_le_logb_of_le one_lt_two
            · positivity
            · exact_mod_cast (Nat.le_of_lt hsmall)
          have hn_nat_le : n ≤ N * (n - 1) := by
            have hn2 : 2 ≤ n := by omega
            have hN_ge_n1 : n + 1 ≤ N := by omega
            calc
              n = n * 1 := by ring
              _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
              _ ≤ (n + 1) * (n - 1) := Nat.mul_le_mul_right (n - 1) (by omega)
              _ ≤ N * (n - 1) := Nat.mul_le_mul_right (n - 1) hN_ge_n1
          have hn_le : (n : ℝ) ≤ (N : ℝ) * ((n : ℝ) - 1) := by
            exact_mod_cast hn_nat_le
          have hstep1 :
              fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) ≤
                fixedTCoeff t * (n : ℝ) * Real.logb 2 (N : ℝ) := by
            gcongr
          have hstep2 :
              fixedTCoeff t * (n : ℝ) * Real.logb 2 (N : ℝ) ≤
                fixedTCoeff t * ((N : ℝ) * ((n : ℝ) - 1)) * Real.logb 2 (N : ℝ) := by
            gcongr
          have hcoef_le :
              fixedTCoeff t * (N : ℝ) * Real.logb 2 (N : ℝ) ≤ C := by
            dsimp [C]
            nlinarith [hB_nonneg]
          have hbase :
              fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) ≤ C * ((n : ℝ) - 1) := by
            have htmp :
                fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) ≤
                  (fixedTCoeff t * (N : ℝ) * Real.logb 2 (N : ℝ)) * ((n : ℝ) - 1) := by
              calc
                fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ)
                    ≤ fixedTCoeff t * (n : ℝ) * Real.logb 2 (N : ℝ) := hstep1
                _ ≤ fixedTCoeff t * ((N : ℝ) * ((n : ℝ) - 1)) *
                    Real.logb 2 (N : ℝ) := hstep2
                _ = (fixedTCoeff t * (N : ℝ) * Real.logb 2 (N : ℝ)) * ((n : ℝ) - 1) := by
                      ring
            have hn1_nonneg : 0 ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
            exact le_mul_of_le_mul_of_nonneg_right htmp hcoef_le hn1_nonneg
          linarith
      · have hlarge : N ≤ n := by omega
        have hstep_nat := exactWitnessSup_lubell_step t n ht hlarge
        have hstep :
            (exactWitnessSup n : ℝ) ≥
              ((Finset.univ : Finset (Fin t)).sum
                fun i => (exactWitnessSup (lubellPart t n i) : ℝ)) +
                (lubellQ t n : ℝ) * B := by
          have hstep' :
              (exactWitnessSup n : ℝ) ≥
                ((Finset.univ : Finset (Fin t)).sum
                  fun i => (exactWitnessSup (lubellPart t n i) : ℝ)) +
                  (lubellQ t n : ℝ) * ((((lubellFrame t).card : ℕ) : ℝ)) := by
            exact_mod_cast hstep_nat
          simpa [B] using hstep'
        have hterm :
            ∀ i : Fin t,
              (exactWitnessSup (lubellPart t n i) : ℝ) ≥
                ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
                    (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ) -
                  C * ((lubellPart t n i : ℝ) - 1) := by
          intro i
          have hih := ih (lubellPart t n i) (lubellPart_lt t n ht hlarge i)
            (lubellPart_pos t n ht (lubellQ_pos t n ht hlarge) i)
          rwa [fixedTCoeff_mul_logb_eq t ht (lubellPart t n i)] at hih
        set S : ℝ :=
          ((Finset.univ : Finset (Fin t)).sum
            fun i => (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ))
        have hsumIH :
            ((Finset.univ : Finset (Fin t)).sum fun i => (exactWitnessSup (lubellPart t n i) : ℝ))
              ≥ ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) * S -
                C * ((n : ℝ) - t) := by
          let A : Fin t → ℝ := fun i =>
            ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
              (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ) -
                C * ((lubellPart t n i : ℝ) - 1)
          have hsum :
              (∑ i : Fin t, A i) ≤
                (∑ i : Fin t,
                  (exactWitnessSup (lubellPart t n i) : ℝ)) :=
            Finset.sum_le_sum fun i _ => hterm i
          rw [Finset.sum_sub_distrib] at hsum
          have hsumA :
              (∑ i : Fin t,
                  ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
                    (lubellPart t n i : ℝ) * Real.log (lubellPart t n i : ℝ)) =
                ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) * S := by
            let a : ℝ := (((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)
            have ha :
                (∑ i : Fin t,
                    a * ((lubellPart t n i : ℝ) *
                      Real.log (lubellPart t n i : ℝ))) = a * S := by
              exact Eq.symm
                (Finset.mul_sum Finset.univ
                  (fun i => ↑(lubellPart t n i) * Real.log ↑(lubellPart t n i)) a)
            simpa [a, mul_assoc] using ha
          have hsumParts :
              (∑ i : Fin t, (lubellPart t n i : ℝ)) = n := by
            exact_mod_cast lubellPart_sum t n ht
          have hsumC :
              (∑ i : Fin t,
                  C * ((lubellPart t n i : ℝ) - 1)) = C * ((n : ℝ) - t) := by
            have hsumSub :
                (∑ i : Fin t, ((lubellPart t n i : ℝ) - 1)) = (n : ℝ) - t := by
              rw [Finset.sum_sub_distrib, hsumParts]
              simp [Finset.sum_const, Fintype.card_fin]
            rw [← Finset.mul_sum, hsumSub]
          lia
        have hcoeff_natlog_nonneg :
            0 ≤ ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) := by
          rw [harmonic_sub_one_eq_sum_Icc t ht]
          positivity
        have hJ := lubellPart_sum_mul_log t n ht hn
        have hscaled :
            ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) * S ≥
              fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) -
                (n : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
          have hmul := mul_le_mul_of_nonneg_left hJ hcoeff_natlog_nonneg
          have hrewrite :
              ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
                  ((n : ℝ) * Real.log ((n : ℝ) / t)) =
                fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) -
                  (n : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
            have hlogdiv :
                Real.log ((n : ℝ) / t) = Real.log (n : ℝ) - Real.log (t : ℝ) := by
              rw [Real.log_div (by positivity) (by positivity)]
            have hdist :
                (n : ℝ) * (Real.log (n : ℝ) - Real.log (t : ℝ)) =
                  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * Real.log (t : ℝ) := by
              ring
            have hlogt_pos : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
            have hlogt_ne : Real.log (t : ℝ) ≠ 0 := hlogt_pos.ne'
            rw [hlogdiv, hdist]
            calc
              ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
                  ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) * Real.log (t : ℝ))
                  = ((((harmonic t : ℚ) : ℝ) - 1) / Real.log (t : ℝ)) *
                      ((n : ℝ) * Real.log (n : ℝ)) -
                    (n : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
                        field_simp [hlogt_ne]
              _ = fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) -
                    (n : ℝ) * ((((harmonic t : ℚ) : ℝ) - 1)) := by
                        rw [fixedTCoeff_mul_logb_eq t ht n]
                        ring
          exact le_of_eq_of_le (id (Eq.symm hrewrite)) hmul
        have hbonus := lubell_bonus_lower t n ht
        have hC_ge_B : B ≤ C := by
          dsimp [C]
          nlinarith [hcoeff_term_nonneg]
        have hCt : B ≤ C * ((t : ℝ) - 1) := by
          have hC_nonneg : 0 ≤ C := hC_pos.le
          have ht1 : (1 : ℝ) ≤ (t : ℝ) - 1 := by
            have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
            linarith
          calc
            B ≤ C := hC_ge_B
            _ ≤ C * ((t : ℝ) - 1) := by nlinarith
        linarith

/-! ## The fixed-t lower bound -/

/-- For fixed t ≥ 2, H(n) ≥ (h_t - 1) / log_2(t) · n log_2(n) - C_t · n. -/
theorem fixed_t_bound (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (H n : ℝ) ≥
        fixedTCoeff t *
          (n : ℝ) * Real.logb 2 (n : ℝ) - C * (n : ℝ) := by
  rcases fixed_t_bound_exact t ht with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro n hn
  have hsup : (exactWitnessSup n : ℝ) ≤ H n := by exact_mod_cast exactWitnessSup_le_H n hn
  calc
    (H n : ℝ) ≥ exactWitnessSup n := hsup
    _ ≥ fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) - C * ((n : ℝ) - 1) := hC n hn
    _ ≥ fixedTCoeff t * (n : ℝ) * Real.logb 2 (n : ℝ) - C * (n : ℝ) := by
          nlinarith [hC_pos]

private lemma s2_add_pow_two (k m : ℕ) (hm : m < 2 ^ k) :
    s2 (2 ^ k + m) = 1 + s2 m := by
  induction k generalizing m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      norm_num [s2]
  | succ k ih =>
      rcases Nat.even_or_odd m with ⟨r, hr_even⟩ | ⟨r, hr_odd⟩
      · have hm_even : m = 2 * r := by omega
        have hr : r < 2 ^ k := by omega
        rw [hm_even]
        have hrewrite : 2 ^ (k + 1) + 2 * r = 2 * (2 ^ k + r) := by
          lia
        calc
          s2 (2 ^ (k + 1) + 2 * r) = s2 (2 * (2 ^ k + r)) := by rw [hrewrite]
          _ = s2 (2 ^ k + r) := by rw [s2_two_mul]
          _ = 1 + s2 r := ih r hr
          _ = 1 + s2 (2 * r) := by rw [s2_two_mul]
      · have hm_odd : m = 2 * r + 1 := by omega
        have hr : r < 2 ^ k := by omega
        rw [hm_odd]
        have hrewrite : 2 ^ (k + 1) + (2 * r + 1) = 2 * (2 ^ k + r) + 1 := by
          lia
        calc
          s2 (2 ^ (k + 1) + (2 * r + 1)) = s2 (2 * (2 ^ k + r) + 1) := by rw [hrewrite]
          _ = 1 + s2 (2 ^ k + r) := by rw [s2_two_mul_add_one]
          _ = 1 + (1 + s2 r) := by rw [ih r hr]
          _ = 1 + s2 (2 * r + 1) := by rw [s2_two_mul_add_one]

private lemma digitSumPrefix_add_pow_two (k m : ℕ) (hm : m ≤ 2 ^ k) :
    digitSumPrefix (2 ^ k + m) =
      digitSumPrefix (2 ^ k) + m + digitSumPrefix m := by
  calc
    digitSumPrefix (2 ^ k + m)
        = digitSumPrefix (2 ^ k) + ∑ x ∈ Finset.range m, s2 (2 ^ k + x) := by
            rw [digitSumPrefix, Finset.sum_range_add, digitSumPrefix]
    _ = digitSumPrefix (2 ^ k) + ∑ x ∈ Finset.range m, (1 + s2 x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          rw [s2_add_pow_two k x]
          exact lt_of_lt_of_le (Finset.mem_range.mp hx) hm
    _ = digitSumPrefix (2 ^ k) + (m + digitSumPrefix m) := by
          rw [Finset.sum_add_distrib]
          simp [digitSumPrefix]
    _ = digitSumPrefix (2 ^ k) + m + digitSumPrefix m := by
          omega

private lemma digitSumPrefix_pow_two_succ (k : ℕ) :
    digitSumPrefix (2 ^ (k + 1)) =
      2 ^ k + 2 * digitSumPrefix (2 ^ k) := by
  simpa [Nat.pow_succ, Nat.mul_comm, two_mul, add_assoc, add_left_comm, add_comm] using
    digitSumPrefix_add_pow_two k (2 ^ k) le_rfl

private lemma digitSumPrefix_pow_two_exact (k : ℕ) :
    digitSumPrefix (2 ^ (k + 1)) = (k + 1) * 2 ^ k := by
  induction k with
  | zero =>
      rw [digitSumPrefix]
      norm_num [s2, Finset.sum_range_succ]
  | succ k ih =>
      rw [digitSumPrefix_pow_two_succ (k + 1), ih]
      ring_nf

private lemma digitSumPrefix_pow_two_exact' {k : ℕ} (hk : 1 ≤ k) :
    digitSumPrefix (2 ^ k) = k * 2 ^ (k - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
  simpa [Nat.add_comm] using digitSumPrefix_pow_two_exact m

private lemma digitSumPrefix_pow_two_real {k : ℕ} (hk : 1 ≤ k) :
    (digitSumPrefix (2 ^ k) : ℝ) = (2 ^ k : ℝ) * ((k : ℝ) / 2) := by
  have hnat : digitSumPrefix (2 ^ k) = k * 2 ^ (k - 1) := digitSumPrefix_pow_two_exact' hk
  have hk_sub_add : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hpow : (2 ^ k : ℝ) = (2 ^ (k - 1) : ℝ) * 2 := by
    lia
  calc
    (digitSumPrefix (2 ^ k) : ℝ) = (k : ℝ) * (2 ^ (k - 1) : ℝ) := by exact_mod_cast hnat
    _ = (2 ^ k : ℝ) * ((k : ℝ) / 2) := by
          rw [hpow]
          ring

private theorem digitSumPrefix_upper (n : ℕ) (hn : 1 ≤ n) :
    (digitSumPrefix n : ℝ) ≤ (n : ℝ) * (((Nat.log 2 n : ℕ) : ℝ) / 2 + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn1 : n = 1
      · subst hn1
        simp [digitSumPrefix, s2]
      · have hn2 : 2 ≤ n := by omega
        let k : ℕ := Nat.log 2 n
        let r : ℕ := n - 2 ^ k
        have hk_pos : 1 ≤ k := by
          dsimp [k]
          exact Nat.le_log_of_pow_le one_lt_two (by simpa using hn2)
        have hn0 : n ≠ 0 := by omega
        have hk_pow_le : 2 ^ k ≤ n := by
          exact Nat.pow_log_le_self 2 hn0
        have hr_eq : n = 2 ^ k + r := by
          exact Eq.symm (Nat.add_sub_of_le hk_pow_le)
        have hr_lt_pow : r < 2 ^ k := by
          have hlt : n < 2 ^ (k + 1) := by
            dsimp [k]
            exact Nat.lt_pow_succ_log_self one_lt_two n
          lia
        have hr_le_pow : r ≤ 2 ^ k := hr_lt_pow.le
        have hsmall :
            (digitSumPrefix r : ℝ) ≤
              (r : ℝ) * (((k - 1 : ℕ) : ℝ) / 2 + 1) := by
          by_cases hr0 : r = 0
          · simp [hr0]
          · have hr_pos : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)
            have hr_lt_n : r < n := by
              exact Nat.lt_of_lt_of_le hr_lt_pow hk_pow_le
            have hlog_r_lt : Nat.log 2 r < k :=
              Nat.log_lt_of_lt_pow (by omega : r ≠ 0) (by simpa using hr_lt_pow)
            have hlog_r_le : Nat.log 2 r ≤ k - 1 := by omega
            calc
              (digitSumPrefix r : ℝ) ≤ (r : ℝ) * (((Nat.log 2 r : ℕ) : ℝ) / 2 + 1) :=
                ih r hr_lt_n hr_pos
              _ ≤ (r : ℝ) * (((k - 1 : ℕ) : ℝ) / 2 + 1) := by
                    gcongr
        have hk_sub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
          rw [Nat.cast_pred hk_pos]
        have hdecomp :
            digitSumPrefix n = digitSumPrefix (2 ^ k) + r + digitSumPrefix r := by
          rw [hr_eq, digitSumPrefix_add_pow_two k r hr_le_pow]
        calc
          (digitSumPrefix n : ℝ)
              = (digitSumPrefix (2 ^ k) : ℝ) + (r : ℝ) + (digitSumPrefix r : ℝ) := by
                  exact_mod_cast hdecomp
          _ ≤ (digitSumPrefix (2 ^ k) : ℝ) + (r : ℝ) +
                (r : ℝ) * (((k - 1 : ℕ) : ℝ) / 2 + 1) := by
                  gcongr
          _ = (2 ^ k : ℝ) * ((k : ℝ) / 2) + (r : ℝ) +
                (r : ℝ) * (((k - 1 : ℕ) : ℝ) / 2 + 1) := by
                  rw [digitSumPrefix_pow_two_real hk_pos]
          _ ≤ (n : ℝ) * ((k : ℝ) / 2 + 1) := by
                rw [hk_sub]
                have hnr : (n : ℝ) = (2 ^ k : ℝ) + (r : ℝ) := by exact_mod_cast hr_eq
                have hr_cast_le : (r : ℝ) ≤ (2 ^ k : ℝ) := by exact_mod_cast hr_le_pow
                rw [hnr]
                nlinarith
          _ = (n : ℝ) * (((Nat.log 2 n : ℕ) : ℝ) / 2 + 1) := by
                dsimp [k]

private theorem k_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (k n : ℝ) ≤ (n : ℝ) * (Real.logb 2 (n : ℝ) / 2 + 2) := by
  have hdigits : (digitSumPrefix n : ℝ) ≤ (n : ℝ) * (((Nat.log 2 n : ℕ) : ℝ) / 2 + 1) :=
    digitSumPrefix_upper n hn
  have hlog : (((Nat.log 2 n : ℕ) : ℝ)) ≤ Real.logb 2 (n : ℝ) := by
    simpa using (Real.natLog_le_logb n 2)
  calc
    (k n : ℝ) = (n : ℝ) + (digitSumPrefix n : ℝ) := by
                  exact_mod_cast digit_sum_formula n hn
    _ ≤ (n : ℝ) + (n : ℝ) * ((((Nat.log 2 n : ℕ) : ℝ) / 2) + 1) := by
          gcongr
    _ = (n : ℝ) * ((((Nat.log 2 n : ℕ) : ℝ) / 2) + 2) := by ring
    _ ≤ (n : ℝ) * (Real.logb 2 (n : ℝ) / 2 + 2) := by
          gcongr

section HarmonicUpper

open Finset

/-- The number of edges in `edges` containing the vertex `v`. -/
noncomputable def degree (edges : Finset (Finset ℕ)) (v : ℕ) : ℕ :=
  (edges.filter fun e => v ∈ e).card

private lemma card_degreeOneSubsets_eq
    (edges : Finset (Finset ℕ)) (r v : ℕ) (hr : 1 ≤ r) :
    (((edges.powersetCard r).filter fun A => degree A v = 1).card : ℕ) =
      (edges.filter fun e => v ∈ e).card *
        ((edges.filter fun e => v ∉ e).powersetCard (r - 1)).card := by
  classical
  let inc : Finset (Finset ℕ) := edges.filter fun e => v ∈ e
  let non : Finset (Finset ℕ) := edges.filter fun e => v ∉ e
  let pieces : Finset (Finset (Finset ℕ)) :=
    inc.biUnion fun e => ((non.powersetCard (r - 1)).image (insert e))
  have hpieces : pieces = (edges.powersetCard r).filter fun A => degree A v = 1 := by
    ext A
    constructor
    · intro hA
      rcases mem_biUnion.mp hA with ⟨e, he, hAe⟩
      rw [mem_image] at hAe
      rcases hAe with ⟨B, hB, rfl⟩
      refine mem_filter.mpr ?_
      refine ⟨?_, ?_⟩
      · refine mem_powersetCard.mpr ?_
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases mem_insert.mp hx with rfl | hx
          · exact (mem_filter.mp he).1
          · exact (mem_filter.mp ((mem_powersetCard.mp hB).1 hx)).1
        · have he_not_mem : e ∉ B := by
            intro heB
            exact (mem_filter.mp ((mem_powersetCard.mp hB).1 heB)).2 ((mem_filter.mp he).2)
          have hBcard : B.card = r - 1 := (mem_powersetCard.mp hB).2
          have : r - 1 + 1 = r := by omega
          simp [he_not_mem, hBcard, this]
      · have hfilter_insert : (insert e B).filter (fun e' => v ∈ e') = {e} := by
          ext x
          constructor
          · intro hx
            rcases mem_insert.mp (mem_filter.mp hx).1 with rfl | hxB
            · simp
            · exact False.elim
                ((mem_filter.mp ((mem_powersetCard.mp hB).1 hxB)).2 (mem_filter.mp hx).2)
          · intro hx
            rw [mem_singleton] at hx
            subst hx
            exact mem_filter.mpr ⟨mem_insert_self _ _, (mem_filter.mp he).2⟩
        rw [degree, hfilter_insert]
        simp
    · intro hA
      rcases mem_filter.mp hA with ⟨hAcard, hdeg⟩
      have hincident_card : (A.filter fun e => v ∈ e).card = 1 := by
        simpa [degree] using hdeg
      rcases Finset.card_eq_one.mp hincident_card with ⟨e, he_singleton⟩
      have he_mem_filter : e ∈ A.filter fun e => v ∈ e := by simp [he_singleton]
      have heA : e ∈ A := (mem_filter.mp he_mem_filter).1
      have hev : v ∈ e := (mem_filter.mp he_mem_filter).2
      have hBsub_non : A.erase e ⊆ non := by
        intro x hx
        refine mem_filter.mpr ⟨?_, ?_⟩
        · exact (mem_powersetCard.mp hAcard).1 ((mem_erase.mp hx).2)
        · intro hvx
          have hx_filter : x ∈ A.filter fun e => v ∈ e :=
            mem_filter.mpr ⟨(mem_erase.mp hx).2, hvx⟩
          rw [he_singleton] at hx_filter
          exact (mem_erase.mp hx).1 (by simpa using hx_filter)
      have hBcard : (A.erase e).card = r - 1 := by
        have hAcard' : A.card = r := (mem_powersetCard.mp hAcard).2
        rw [Finset.card_erase_of_mem heA, hAcard']
      have hinsert : insert e (A.erase e) = A := insert_erase heA
      refine mem_biUnion.mpr ⟨e, ?_, ?_⟩
      · exact mem_filter.mpr ⟨(mem_powersetCard.mp hAcard).1 heA, hev⟩
      · exact mem_image.mpr ⟨A.erase e, mem_powersetCard.mpr ⟨hBsub_non, hBcard⟩, hinsert⟩
  rw [← hpieces]
  rw [card_biUnion]
  · calc
      ∑ e ∈ inc, #(image (insert e) (powersetCard (r - 1) non))
          = ∑ e ∈ inc, #(non.powersetCard (r - 1)) := by
              refine sum_congr rfl ?_
              intro e he
              symm
              refine Finset.card_bij (fun B hB => insert e B) ?_ ?_ ?_
              · intro B hB
                exact mem_image.mpr ⟨B, hB, rfl⟩
              · intro B1 hB1 B2 hB2 hEq
                have he_not_mem1 : e ∉ B1 := fun heB =>
                  (mem_filter.mp ((mem_powersetCard.mp hB1).1 heB)).2 ((mem_filter.mp he).2)
                have he_not_mem2 : e ∉ B2 := fun heB =>
                  (mem_filter.mp ((mem_powersetCard.mp hB2).1 heB)).2 ((mem_filter.mp he).2)
                simpa [he_not_mem1, he_not_mem2] using congrArg (fun s => s.erase e) hEq
              · intro C hC
                rcases mem_image.mp hC with ⟨B, hB, rfl⟩
                exact ⟨B, hB, rfl⟩
      _ = inc.card * (non.powersetCard (r - 1)).card := by
              rw [Finset.sum_const_nat (m := (non.powersetCard (r - 1)).card) (fun _ _ => rfl)]
      _ = (edges.filter fun e => v ∈ e).card *
            ((edges.filter fun e => v ∉ e).powersetCard (r - 1)).card := by
              simp [inc, non]
  · intro e1 he1 e2 he2 hne
    refine disjoint_left.2 ?_
    intro A hA1 hA2
    rw [mem_image] at hA1 hA2
    rcases hA1 with ⟨B1, hB1, rfl⟩
    rcases hA2 with ⟨B2, hB2, hEq⟩
    have hv1 : v ∈ e1 := (mem_filter.mp he1).2
    have he1_not_B2 : e1 ∉ B2 := fun he => (mem_filter.mp ((mem_powersetCard.mp hB2).1 he)).2 hv1
    have : e1 = e2 := by
      have he1_mem : e1 ∈ insert e2 B2 := by simp [hEq]
      rcases mem_insert.mp he1_mem with h | h
      · exact h
      · exact False.elim (he1_not_B2 h)
    exact hne this

private lemma degree_pos_of_mem_vertexSet {edges : Finset (Finset ℕ)} {v : ℕ}
    (hv : v ∈ vertexSet edges) : 1 ≤ degree edges v := by
  rw [degree]
  rcases Finset.mem_biUnion.mp hv with ⟨e, he, hvE⟩
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hvE⟩⟩

private lemma degree_le_card_edges (edges : Finset (Finset ℕ)) (v : ℕ) :
    degree edges v ≤ edges.card :=
  Finset.card_filter_le _ _

private lemma choose_cross_identity (m k r : ℕ)
    (hk : 1 ≤ k) (hkm : k ≤ m) (hr : 1 ≤ r) (hrm : r ≤ m) :
    (Nat.choose (m - 1) (r - 1) : ℚ) * Nat.choose (m - r) (k - 1)
      = Nat.choose (m - 1) (k - 1) * Nat.choose (m - k) (r - 1) := by
  by_cases hbig : k + r ≤ m + 1
  · let t := r + k - 2
    have hrt : r - 1 ≤ t := by
      lia
    have hkt : k - 1 ≤ t := by
      lia
    have h1 := Nat.choose_mul (n := m - 1) (k := t) (s := r - 1) hrt
    have h2 := Nat.choose_mul (n := m - 1) (k := t) (s := k - 1) hkt
    have ht_eq : t = (r - 1) + (k - 1) := by
      lia
    have hsymm : Nat.choose t (r - 1) = Nat.choose t (k - 1) := by
      exact Nat.choose_symm_of_eq_add ht_eq
    have hmr : m - 1 - (r - 1) = m - r := by omega
    have hmk : m - 1 - (k - 1) = m - k := by omega
    have htr : t - (r - 1) = k - 1 := by
      exact (Nat.sub_eq_iff_eq_add' hrt).mpr ht_eq
    have htk : t - (k - 1) = r - 1 := by
      exact (Nat.sub_eq_iff_eq_add hkt).mpr ht_eq
    have h1' : Nat.choose (m - 1) t * Nat.choose t (r - 1)
        = Nat.choose (m - 1) (r - 1) * Nat.choose (m - r) (k - 1) := by
      simpa [hmr, htr] using h1
    have h2' : Nat.choose (m - 1) t * Nat.choose t (k - 1)
        = Nat.choose (m - 1) (k - 1) * Nat.choose (m - k) (r - 1) := by
      simpa [hmk, htk] using h2
    have h1q : ((Nat.choose (m - 1) t : ℚ) * Nat.choose t (r - 1))
        = Nat.choose (m - 1) (r - 1) * Nat.choose (m - r) (k - 1) := by
      exact_mod_cast h1'
    have h2q : ((Nat.choose (m - 1) t : ℚ) * Nat.choose t (k - 1))
        = Nat.choose (m - 1) (k - 1) * Nat.choose (m - k) (r - 1) := by
      exact_mod_cast h2'
    rw [← h1q, hsymm, h2q]
  · have hrbig : m - k < r - 1 := by omega
    have hkbig : m - r < k - 1 := by omega
    simp [Nat.choose_eq_zero_of_lt hrbig, Nat.choose_eq_zero_of_lt hkbig]

private lemma degree_weighted_sum (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ∑ r ∈ Icc 1 m,
      (((k : ℚ) * Nat.choose (m - k) (r - 1)) / Nat.choose (m - 1) (r - 1)) = m := by
  have hden_nat : 0 < Nat.choose (m - 1) (k - 1) := Nat.choose_pos (by omega : k - 1 ≤ m - 1)
  have hden : (Nat.choose (m - 1) (k - 1) : ℚ) ≠ 0 := by
    exact_mod_cast hden_nat.ne'
  have hterm : ∀ r ∈ Icc 1 m,
      (((k : ℚ) * Nat.choose (m - k) (r - 1)) / Nat.choose (m - 1) (r - 1))
        = ((k : ℚ) / Nat.choose (m - 1) (k - 1)) * Nat.choose (m - r) (k - 1) := by
    intro r hr
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    have hrm : r ≤ m := (mem_Icc.mp hr).2
    have hrden_nat : 0 < Nat.choose (m - 1) (r - 1) := Nat.choose_pos (by omega : r - 1 ≤ m - 1)
    have hrden : (Nat.choose (m - 1) (r - 1) : ℚ) ≠ 0 := by exact_mod_cast hrden_nat.ne'
    have hcross := choose_cross_identity m k r hk hkm hr1 hrm
    field_simp [hden, hrden]
    ring_nf
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross.symm
  calc
    ∑ r ∈ Icc 1 m,
        (((k : ℚ) * Nat.choose (m - k) (r - 1)) / Nat.choose (m - 1) (r - 1))
      = ∑ r ∈ Icc 1 m,
          (((k : ℚ) / Nat.choose (m - 1) (k - 1)) * Nat.choose (m - r) (k - 1)) := by
            refine sum_congr rfl hterm
    _ = ((k : ℚ) / Nat.choose (m - 1) (k - 1)) *
          ∑ r ∈ Icc 1 m, (Nat.choose (m - r) (k - 1) : ℚ) := by
          rw [← mul_sum]
    _ = ((k : ℚ) / Nat.choose (m - 1) (k - 1)) * Nat.choose m k := by
          congr 1
          have hsum1 :
              ∑ r ∈ Icc 1 m, (Nat.choose (m - r) (k - 1) : ℚ)
                = ∑ j ∈ range m, (Nat.choose ((m - 1) - j) (k - 1) : ℚ) := by
              rw [← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
              lia
          rw [hsum1]
          have hreflect :
              ∑ j ∈ range m, (Nat.choose ((m - 1) - j) (k - 1) : ℚ)
                = ∑ j ∈ range m, (Nat.choose j (k - 1) : ℚ) := by
              simpa using (Finset.sum_range_reflect (f := fun j => (Nat.choose j (k - 1) : ℚ)) m)
          rw [hreflect]
          have hsplit :=
            Finset.sum_range_add_sum_Ico
              (fun j => (Nat.choose j (k - 1) : ℚ)) (by omega : k - 1 ≤ m)
          have hzero : ∑ j ∈ range (k - 1), (Nat.choose j (k - 1) : ℚ) = 0 := by
            refine sum_eq_zero ?_
            intro j hj
            have hjlt : j < k - 1 := by simpa using hj
            simp [Nat.choose_eq_zero_of_lt hjlt]
          have hIco :
              ∑ j ∈ Ico (k - 1) m, (Nat.choose j (k - 1) : ℚ)
                = ∑ i ∈ range (m - k + 1), (Nat.choose (i + (k - 1)) (k - 1) : ℚ) := by
              rw [Finset.sum_Ico_eq_sum_range]
              have hlen : m - (k - 1) = m - k + 1 := by omega
              simp [hlen, Nat.add_comm]
          have hshift :
              ∑ i ∈ range (m - k + 1),
                (Nat.choose (i + (k - 1)) (k - 1) : ℚ) = Nat.choose m k := by
              have hmkk : (m - k) + (k - 1) + 1 = m := by omega
              have hk1 : (k - 1) + 1 = k := by omega
              simpa [hmkk, hk1, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                (show
                    (∑ i ∈ range ((m - k) + 1), ((i + (k - 1)).choose (k - 1) : ℚ)) =
                      Nat.choose ((m - k) + (k - 1) + 1) ((k - 1) + 1) by
                  exact_mod_cast Nat.sum_range_add_choose (m - k) (k - 1))
          linarith [hsplit, hzero, hIco, hshift]
    _ = m := by
          have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
          have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
          have hchooseNat : m * Nat.choose (m - 1) (k - 1) = Nat.choose m k * k := by
            simpa [hm', hk'] using Nat.add_one_mul_choose_eq (m - 1) (k - 1)
          have hchoose : ((m : ℚ) * Nat.choose (m - 1) (k - 1)) = Nat.choose m k * k := by
            exact_mod_cast hchooseNat
          field_simp [hden]
          ring_nf
          simpa [mul_comm, mul_left_comm, mul_assoc] using hchoose.symm

private theorem vertex_card_le_harmonic
    (edges : Finset (Finset ℕ)) (n : ℕ) (hm : 1 ≤ edges.card)
    (hpart : NoLargePartition edges n) :
    ((vertexSet edges).card : ℚ) ≤ n * harmonic edges.card := by
  let m := edges.card
  let W : ℚ := ∑ r ∈ Icc 1 m,
      ∑ A ∈ edges.powersetCard r,
        ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
  have hr_bound :
      ∀ r ∈ Icc 1 m,
        ∑ A ∈ edges.powersetCard r,
          ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
            ≤ (n : ℚ) * m / r := by
    intro r hr
    have hpoint :
        ∀ A ∈ edges.powersetCard r,
          ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
            ≤ (n : ℚ) / Nat.choose (m - 1) (r - 1) := by
      intro A hA
      have hsub : A ⊆ edges := (mem_powersetCard.mp hA).1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hpart A hsub) (by positivity)
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    have hrm : r ≤ m := (mem_Icc.mp hr).2
    have hrden_nat : 0 < Nat.choose (m - 1) (r - 1) := Nat.choose_pos (by omega : r - 1 ≤ m - 1)
    have hrden : (Nat.choose (m - 1) (r - 1) : ℚ) ≠ 0 := by
      exact_mod_cast hrden_nat.ne'
    calc
      ∑ A ∈ edges.powersetCard r, ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
          ≤ ∑ A ∈ edges.powersetCard r, ((n : ℚ) / Nat.choose (m - 1) (r - 1)) :=
            Finset.sum_le_sum hpoint
      _ = ((edges.powersetCard r).card : ℚ) * ((n : ℚ) / Nat.choose (m - 1) (r - 1)) := by
            simp
      _ = (Nat.choose m r : ℚ) * ((n : ℚ) / Nat.choose (m - 1) (r - 1)) := by
            rw [Finset.card_powersetCard]
      _ = (n : ℚ) * m / r := by
            have hchooseNat : m * Nat.choose (m - 1) (r - 1) = Nat.choose m r * r := by
              have hm' : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
              have hr' : r - 1 + 1 = r := Nat.sub_add_cancel hr1
              simpa [hm', hr'] using Nat.add_one_mul_choose_eq (m - 1) (r - 1)
            have hchoose : ((m : ℚ) * Nat.choose (m - 1) (r - 1)) = Nat.choose m r * r := by
              exact_mod_cast hchooseNat
            have hratio :
                ((Nat.choose m r : ℚ) / Nat.choose (m - 1) (r - 1)) = m / r := by
              field_simp [hrden, show (r : ℚ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hr1]
              simpa [mul_comm, mul_left_comm, mul_assoc] using hchoose.symm
            calc
              (Nat.choose m r : ℚ) * ((n : ℚ) / Nat.choose (m - 1) (r - 1))
                  = (n : ℚ) *
                      (((Nat.choose m r : ℚ) / Nat.choose (m - 1) (r - 1))) := by
                        ring
              _ = (n : ℚ) * (m / r) := by rw [hratio]
              _ = (n : ℚ) * m / r := by ring
  have hW_upper : W ≤ (n : ℚ) * m * harmonic m := by
    dsimp [W]
    calc
      ∑ r ∈ Icc 1 m,
          ∑ A ∈ edges.powersetCard r,
            ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
        ≤ ∑ r ∈ Icc 1 m, (n : ℚ) * m / r := Finset.sum_le_sum hr_bound
      _ = (n : ℚ) * m * ∑ r ∈ Icc 1 m, ((r : ℚ)⁻¹) := by
            rw [mul_sum]
            lia
      _ = (n : ℚ) * m * harmonic m := by
            rw [harmonic_eq_sum_Icc]
  have hucov_nat (A : Finset (Finset ℕ)) :
      uniqueCoverage edges A =
        ∑ v ∈ vertexSet edges, if degree A v = 1 then 1 else 0 := by
    unfold uniqueCoverage degree
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hucov (A : Finset (Finset ℕ)) :
      (uniqueCoverage edges A : ℚ) =
        ∑ v ∈ vertexSet edges, if degree A v = 1 then (1 : ℚ) else 0 := by
    exact_mod_cast hucov_nat A
  have hswap (r : ℕ) :
      ∑ A ∈ edges.powersetCard r,
        ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
        = ∑ v ∈ vertexSet edges,
            ((((edges.powersetCard r).filter fun A => degree A v = 1).card : ℚ) /
              Nat.choose (m - 1) (r - 1)) := by
    let den : ℚ := Nat.choose (m - 1) (r - 1)
    calc
      ∑ A ∈ edges.powersetCard r, ((uniqueCoverage edges A : ℚ) / den)
          = ∑ A ∈ edges.powersetCard r,
              ∑ v ∈ vertexSet edges, (if degree A v = 1 then ((1 : ℚ) / den) else 0) := by
                refine sum_congr rfl ?_
                intro A hA
                rw [hucov A, div_eq_mul_inv, Finset.sum_mul]
                refine sum_congr rfl ?_
                intro v hv
                split_ifs <;> simp [div_eq_mul_inv]
      _ = ∑ v ∈ vertexSet edges,
              ∑ A ∈ edges.powersetCard r,
                (if degree A v = 1 then ((1 : ℚ) / den) else 0) := by
                rw [Finset.sum_comm]
      _ = ∑ v ∈ vertexSet edges,
              (((edges.powersetCard r).filter fun A => degree A v = 1).card : ℚ) / den := by
                refine sum_congr rfl ?_
                intro v hv
                rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
                ring
  have hW_eq : W = (m : ℚ) * (vertexSet edges).card := by
    dsimp [W]
    calc
      ∑ r ∈ Icc 1 m,
          ∑ A ∈ edges.powersetCard r,
            ((uniqueCoverage edges A : ℚ) / Nat.choose (m - 1) (r - 1))
        = ∑ v ∈ vertexSet edges,
            ∑ r ∈ Icc 1 m,
              ((((edges.powersetCard r).filter fun A => degree A v = 1).card : ℚ) /
              Nat.choose (m - 1) (r - 1)) := by
          rw [Finset.sum_comm]
          exact sum_congr rfl fun x a => hswap x
    _ = ∑ v ∈ vertexSet edges, (m : ℚ) := by
          refine sum_congr rfl ?_
          intro v hv
          have hvpos : 1 ≤ degree edges v := degree_pos_of_mem_vertexSet hv
          have hvle : degree edges v ≤ m := by simpa [m] using degree_le_card_edges edges v
          calc
            ∑ r ∈ Icc 1 m,
                ((((edges.powersetCard r).filter fun A => degree A v = 1).card : ℚ) /
                  Nat.choose (m - 1) (r - 1))
              = ∑ r ∈ Icc 1 m,
                  (((degree edges v : ℚ) * Nat.choose (m - degree edges v) (r - 1)) /
                    Nat.choose (m - 1) (r - 1)) := by
                      refine sum_congr rfl ?_
                      intro r hr
                      have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
                      have hsplitCard :
                          (edges.filter fun e => v ∈ e).card +
                            (edges.filter fun e => v ∉ e).card = edges.card := by
                        simpa using
                          (Finset.card_filter_add_card_filter_not (s := edges)
                            (p := fun e => v ∈ e))
                      have hnoncard :
                          (edges.filter fun e => v ∉ e).card = m - degree edges v := by
                        dsimp [m, degree]
                        omega
                      rw [card_degreeOneSubsets_eq edges r v hr1,
                        Finset.card_powersetCard, hnoncard]
                      simp [m, degree]
            _ = m := degree_weighted_sum m (degree edges v) (by simpa [m] using hm) hvpos hvle
    _ = (m : ℚ) * (vertexSet edges).card := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hineq : (m : ℚ) * (vertexSet edges).card ≤ (m : ℚ) * ((n : ℚ) * harmonic m) := by
    simpa [hW_eq, mul_assoc, mul_left_comm, mul_comm] using hW_upper
  exact le_of_mul_le_mul_left hineq hmq

private lemma harmonic_monotone : Monotone harmonic := by
  refine monotone_nat_of_le_succ ?_
  intro m
  rw [harmonic_succ]
  exact le_add_of_nonneg_right (by positivity)

private theorem vertexSet_card_le_harmonic_of_noLargePartition
    (edges : Finset (Finset ℕ)) (n : ℕ) (hpart : NoLargePartition edges n) :
    ((vertexSet edges).card : ℚ) ≤ n * harmonic n := by
  obtain ⟨C, hCsub, hCcover, hCcard⟩ :=
    exists_cover_subset_card_le_of_noLargePartition edges n hpart
  by_cases hCempty : C = ∅
  · have hVempty : vertexSet edges = ∅ := by
      rw [← hCcover, hCempty]
      simp [vertexSet]
    have hharm_nonneg : (0 : ℚ) ≤ harmonic n := by
      simpa using harmonic_monotone (Nat.zero_le n)
    have hnonneg : (0 : ℚ) ≤ (n : ℚ) * harmonic n := mul_nonneg (by positivity) hharm_nonneg
    simpa [hVempty] using hnonneg
  · have hCpos : 1 ≤ C.card := by
      rcases Finset.nonempty_iff_ne_empty.mpr hCempty with ⟨e, he⟩
      exact Finset.card_pos.mpr ⟨e, he⟩
    have hpartC : NoLargePartition C n := by
      intro P hP
      have hPe : P ⊆ edges := fun e he => hCsub (hP he)
      simpa [uniqueCoverage, hCcover] using hpart P hPe
    calc
      ((vertexSet edges).card : ℚ) = (vertexSet C).card := by rw [hCcover]
      _ ≤ n * harmonic C.card := vertex_card_le_harmonic C n hCpos hpartC
      _ ≤ n * harmonic n := by
            gcongr
            exact harmonic_monotone hCcard

private theorem H_upper_harmonic (n : ℕ) (hn : 1 ≤ n) :
    (H n : ℚ) ≤ n * harmonic n := by
  have hnonempty :
      {k : ℕ | ∃ (edges : Finset (Finset ℕ)),
        (vertexSet edges).card = k ∧ NoLargePartition edges n}.Nonempty := by
    rcases A_witness n hn with ⟨edges, -, hcard, hpart⟩
    exact ⟨(vertexSet edges).card, ⟨edges, rfl, hpart⟩⟩
  rcases Nat.sSup_mem hnonempty (H_set_bddAbove n) with ⟨edges, hcard, hpart⟩
  unfold H
  simpa [hcard] using vertexSet_card_le_harmonic_of_noLargePartition edges n hpart

private lemma le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := by
              lia
        _ = 2 ^ (n + 1) := by
              rw [Nat.pow_succ, Nat.mul_comm, two_mul]

private lemma k_pow_two_real {m : ℕ} (hm : 1 ≤ m) :
    (k (2 ^ m) : ℝ) = (2 ^ m : ℝ) * ((m : ℝ) / 2 + 1) := by
  have hpow_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  calc
    (k (2 ^ m) : ℝ) = (2 ^ m : ℝ) + digitSumPrefix (2 ^ m) := by
          exact_mod_cast digit_sum_formula (2 ^ m) hpow_pos
    _ = (2 ^ m : ℝ) + (2 ^ m : ℝ) * ((m : ℝ) / 2) := by
          rw [digitSumPrefix_pow_two_real hm]
    _ = (2 ^ m : ℝ) * ((m : ℝ) / 2 + 1) := by
          ring

private theorem H_div_k_pow_two_le_two {m : ℕ} (hm : 1 ≤ m) :
    (H (2 ^ m) : ℝ) / (k (2 ^ m) : ℝ) ≤ 2 := by
  have hHq := H_upper_harmonic (2 ^ m) Nat.one_le_two_pow
  have hH : (H (2 ^ m) : ℝ) ≤ (2 ^ m : ℝ) * (((harmonic (2 ^ m) : ℚ) : ℝ)) := by
    exact_mod_cast hHq
  have hharm : (((harmonic (2 ^ m) : ℚ) : ℝ)) ≤ 1 + Real.log (2 ^ m : ℝ) := by
    simpa using (harmonic_le_one_add_log (2 ^ m))
  have hlog2_lt_one : Real.log 2 < 1 := by
    linarith [Real.log_lt_sub_one_of_pos (by positivity : 0 < (2 : ℝ))
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hlog : Real.log (2 ^ m : ℝ) ≤ m := by
    rw [Real.log_pow]
    nlinarith
  have hharm_le : (((harmonic (2 ^ m) : ℚ) : ℝ)) ≤ (m : ℝ) + 1 := by
    linarith
  have hk_eq := k_pow_two_real hm
  have hk_pos : 0 < (k (2 ^ m) : ℝ) := by
    rw [hk_eq]
    positivity
  apply (div_le_iff₀ hk_pos).2
  calc
    (H (2 ^ m) : ℝ) ≤ (2 ^ m : ℝ) * ((m : ℝ) + 1) := by
      calc
        (H (2 ^ m) : ℝ) ≤ (2 ^ m : ℝ) * (((harmonic (2 ^ m) : ℚ) : ℝ)) := hH
        _ ≤ (2 ^ m : ℝ) * ((m : ℝ) + 1) := by
              gcongr
    _ ≤ 2 * (k (2 ^ m) : ℝ) := by
      rw [hk_eq]
      have hpow_nonneg : (0 : ℝ) ≤ (2 ^ m : ℝ) := by positivity
      nlinarith

private theorem ratio_isCobounded :
    Filter.atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ => (H n : ℝ) / (k n : ℝ)) := by
  refine Filter.IsCoboundedUnder.of_frequently_le (a := 2) ?_
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨2 ^ (a + 1), ?_, ?_⟩
  · exact le_trans (Nat.le_succ a) (le_two_pow (a + 1))
  · exact H_div_k_pow_two_le_two (m := a + 1) (Nat.succ_le_succ (Nat.zero_le a))

end HarmonicUpper

/-! ## The asymptotic theorem -/

/-- The asymptotic lower bound: liminf H(n)/k_n ≥ 2 ln 2. -/
theorem asymptotic_lower_bound :
    2 * Real.log 2 ≤
      Filter.atTop.liminf (fun n : ℕ => (H n : ℝ) / (k n : ℝ)) := by
  have hratio_bddBelow :
      Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => (H n : ℝ) / (k n : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0) <|
      Filter.Eventually.of_forall fun _ => by positivity
  rw [Filter.le_liminf_iff' (h₁ := ratio_isCobounded) (h₂ := hratio_bddBelow)]
  intro y hy
  by_cases hy0 : y ≤ 0
  · exact Filter.Eventually.of_forall fun n => by
      have hratio_nonneg : 0 ≤ (H n : ℝ) / (k n : ℝ) := by positivity
      linarith
  · have hy_pos : 0 < y := lt_of_not_ge hy0
    let ε : ℝ := 1 - y / (2 * Real.log 2)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog2_ne : Real.log 2 ≠ 0 := hlog2_pos.ne'
    have htwo_log2_pos : 0 < 2 * Real.log 2 := by nlinarith
    have hε_pos : 0 < ε := by
      dsimp [ε]
      have hy_div_lt_one : y / (2 * Real.log 2) < 1 := by
        exact (div_lt_one₀ htwo_log2_pos).mpr hy
      linarith
    have hlog_tendsto :
        Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    rcases Filter.eventually_atTop.1 (hlog_tendsto.eventually_gt_atTop (1 / ε)) with ⟨N, hN⟩
    let t : ℕ := max N 2
    have ht : 2 ≤ t := by simp [t]
    have htlog : 1 / ε < Real.log (t : ℝ) := by
      apply hN
      exact Nat.le_max_left N 2
    have hlogt_pos : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
    have hinv : 1 / Real.log (t : ℝ) < ε := (one_div_lt hε_pos hlogt_pos).1 htlog
    have hyhalf : y / 2 < fixedTCoeff t := by
      calc
        y / 2 = Real.log 2 * (1 - ε) := by
                  dsimp [ε]
                  field_simp [hlog2_ne]
                  ring
        _ < Real.log 2 * (1 - 1 / Real.log (t : ℝ)) := by
              exact mul_lt_mul_of_pos_left (by linarith [hinv]) hlog2_pos
        _ ≤ fixedTCoeff t := fixedTCoeff_lower t ht
    rcases fixed_t_bound t ht with ⟨C, hC_pos, hC⟩
    let a : ℝ := fixedTCoeff t
    have hdelta_pos : 0 < a - y / 2 := by simpa [a] using sub_pos.mpr hyhalf
    have hlogb_tendsto :
        Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) Filter.atTop Filter.atTop :=
      (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
    let B : ℝ := (C + 2 * y) / (a - y / 2)
    filter_upwards [Filter.eventually_ge_atTop 1,
      hlogb_tendsto.eventually_ge_atTop B] with n hn hlog
    have hk_pos_nat : 1 ≤ k n := by
      simpa [digit_sum_formula n hn] using le_trans hn (Nat.le_add_right n (digitSumPrefix n))
    have hk_pos : 0 < (k n : ℝ) := by exact_mod_cast hk_pos_nat
    have hH : (H n : ℝ) ≥ a * (n : ℝ) * Real.logb 2 (n : ℝ) - C * (n : ℝ) := by
      simpa [a] using hC n hn
    have hk_upper : (k n : ℝ) ≤ (n : ℝ) * (Real.logb 2 (n : ℝ) / 2 + 2) :=
      k_upper_bound n hn
    have haux : y * (Real.logb 2 (n : ℝ) / 2 + 2) ≤ a * Real.logb 2 (n : ℝ) - C := by
      have hmul : C + 2 * y ≤ Real.logb 2 (n : ℝ) * (a - y / 2) := by
        dsimp [B] at hlog
        exact (div_le_iff₀ hdelta_pos).1 hlog
      linarith
    have hyk : y * (k n : ℝ) ≤ (H n : ℝ) := by
      calc
        y * (k n : ℝ) ≤ y * ((n : ℝ) * (Real.logb 2 (n : ℝ) / 2 + 2)) := by
              gcongr
        _ = (n : ℝ) * (y * (Real.logb 2 (n : ℝ) / 2 + 2)) := by ring
        _ ≤ (n : ℝ) * (a * Real.logb 2 (n : ℝ) - C) := by
              gcongr
        _ = a * (n : ℝ) * Real.logb 2 (n : ℝ) - C * (n : ℝ) := by ring
        _ ≤ (H n : ℝ) := hH
    exact (le_div_iff₀ hk_pos).2 hyk

/-- The asymptotic theorem of `frontier.tex`, packaging the fixed-`t` lower bound and
    its consequence for the liminf ratio `H(n) / k_n`. -/
theorem thm_asymptotic :
    (∀ t : ℕ, 2 ≤ t →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (H n : ℝ) ≥
          fixedTCoeff t *
            (n : ℝ) * Real.logb 2 (n : ℝ) - C * (n : ℝ)) ∧
    2 * Real.log 2 ≤
      Filter.atTop.liminf (fun n : ℕ => (H n : ℝ) / (k n : ℝ)) := by
  refine ⟨?_, asymptotic_lower_bound⟩
  exact fun t a => fixed_t_bound t a


end HypergraphLowerBound
