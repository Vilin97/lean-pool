/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Transport

/-!
# The classification theorem (A7)

Statements split from the original `Statements.lean` skeleton (one file per proving task).
The mathematics is AUDIT-NOTES A7 and `papers/.../sections/13-classification.tex`.

The four theorems below are proved by assembling the results of the other files in this
directory, together with the bridging lemmas of the first three sections: connectivity of the
named cycle and path scenarios, the fact that a target passing the order-`t` test is a law,
the total variation cost of a local flip, and the passage to a connected component.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## A7: the classification theorem -/

/-! ### Bridging lemmas: connectivity of the named scenarios -/

/-- Consecutive residues are adjacent in the cycle. -/
private theorem cycleAdj_adj_mod (m : ℕ) (hm : 3 ≤ m) (n : ℕ) :
    (cycleAdj m).Adj ⟨n % m, Nat.mod_lt _ (by omega)⟩ ⟨(n + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
  have key : (n % m + 1) % m = (n + 1) % m := Nat.mod_add_mod n m 1
  refine ⟨?_, Or.inl key⟩
  intro h
  have h' : n % m = (n + 1) % m := congrArg Fin.val h
  rcases lt_or_ge (n % m + 1) m with hlt | hge
  · rw [← key, Nat.mod_eq_of_lt hlt] at h'; omega
  · have he : n % m + 1 = m := by
      have : n % m < m := Nat.mod_lt _ (by omega)
      omega
    rw [← key, he, Nat.mod_self] at h'
    omega

private theorem cycle_reachable_zero (m : ℕ) (hm : 3 ≤ m) (n : ℕ) :
    (cycleAdj m).Reachable ⟨0, by omega⟩ ⟨n % m, Nat.mod_lt _ (by omega)⟩ := by
  induction n with
  | zero => simp
  | succ k ih => exact ih.trans (cycleAdj_adj_mod m hm k).reachable

/-- The cycle graph is connected. -/
theorem cycleAdj_connected (m : ℕ) (hm : 3 ≤ m) : (cycleAdj m).Connected := by
  have key : ∀ v : Fin m, (cycleAdj m).Reachable ⟨0, by omega⟩ v := by
    intro v
    have h := cycle_reachable_zero m hm v.val
    simpa [Nat.mod_eq_of_lt v.isLt] using h
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact ⟨fun u v => (key u).symm.trans (key v)⟩

/-- The five-vertex path graph is connected. -/
theorem pathAdj_five_connected : (pathAdj 5).Connected := by
  have a01 : (pathAdj 5).Adj 0 1 := Or.inl rfl
  have a12 : (pathAdj 5).Adj 1 2 := Or.inl rfl
  have a23 : (pathAdj 5).Adj 2 3 := Or.inl rfl
  have a34 : (pathAdj 5).Adj 3 4 := Or.inl rfl
  have r0 : (pathAdj 5).Reachable 0 0 := SimpleGraph.Reachable.refl _
  have r1 : (pathAdj 5).Reachable 0 1 := a01.reachable
  have r2 : (pathAdj 5).Reachable 0 2 := r1.trans a12.reachable
  have r3 : (pathAdj 5).Reachable 0 3 := r2.trans a23.reachable
  have r4 : (pathAdj 5).Reachable 0 4 := r3.trans a34.reachable
  have key : ∀ v : Fin 5, (pathAdj 5).Reachable 0 v := by
    intro v; fin_cases v
    exacts [r0, r1, r2, r3, r4]
  exact ⟨fun u v => (key u).symm.trans (key v)⟩



/-! ### Bridging lemmas: pushforwards, laws and total variation -/

private theorem pushforward_nonneg {α β : Type*} [Fintype α] [DecidableEq β] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (F : α → β) (b : β) : 0 ≤ pushforward w F b :=
  Finset.sum_nonneg fun a _ => by by_cases h : F a = b <;> simp [h, hw a]

private theorem sum_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) : ∑ b, pushforward w F b = ∑ a, w a := by
  simp only [pushforward]
  rw [Finset.sum_comm]
  simp

private theorem pushforward_apply_of_injective {α β : Type*} [Fintype α] [DecidableEq β]
    (w : α → ℝ) (F : α → β) (hF : Function.Injective F) (a : α) :
    pushforward w F (F a) = w a := by
  simp only [pushforward]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hF.ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

private theorem gPartyRead_copySet_injective (ι : Γ.Edge → Fin t) :
    Function.Injective (gPartyRead (copySet ι) : (Γ.V → Bool) → (copySet ι) → Bool) := by
  intro w w' h
  funext v
  have hv : copyObs ι v ∈ copySet ι := by
    simp only [copySet, Finset.mem_image]
    exact ⟨v, Finset.mem_univ v, rfl⟩
  exact congrFun h ⟨copyObs ι v, hv⟩

/-- A target that passes the order-`t` ancestral-independence test, `t ≥ 1`, is a law: the
witness restricted to one copied original scenario has the target as its law. -/
theorem isLaw_of_gAIFeasible (Γ : PairGraph) (t : ℕ) (ht : 1 ≤ t) (P : GTarget Γ)
    (h : GAIFeasible Γ t P) : IsLaw P := by
  obtain ⟨Δ, hΔ, -, -, hinj, -⟩ := h
  have htp : 0 < t := ht
  set ι : Γ.Edge → Fin t := fun _ => ⟨0, htp⟩ with hι
  have hS : GInjectable (copySet ι) := ⟨ι, Finset.Subset.refl _⟩
  have key := hinj (copySet ι) hS
  constructor
  · intro w
    have h1 : pushforward P (gPartyRead (copySet ι)) (gPartyRead (copySet ι) w) = P w :=
      pushforward_apply_of_injective _ _ (gPartyRead_copySet_injective ι) w
    rw [← h1, ← key]
    exact pushforward_nonneg _ hΔ.1 _ _
  · calc ∑ w, P w = ∑ b, pushforward P (gPartyRead (copySet ι)) b := (sum_pushforward _ _).symm
      _ = ∑ b, pushforward Δ (gRestrict (copySet ι)) b := by rw [key]
      _ = ∑ ω, Δ ω := sum_pushforward _ _
      _ = 1 := hΔ.2

private theorem dTV_nonneg {α : Type*} [Fintype α] (P Q : α → ℝ) : 0 ≤ dTV P Q := by
  unfold dTV
  have : (0:ℝ) ≤ ∑ a, |P a - Q a| := Finset.sum_nonneg fun a _ => abs_nonneg _
  linarith

/-- The distance to the compatible set is at most the distance to any compatible law. -/
theorem distToCompatible_le (Γ : PairGraph) (P Q : GTarget Γ) (hQ : GCompatible Γ Q) :
    distToCompatible Γ P ≤ dTV P Q := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro d ⟨R, -, rfl⟩
    exact dTV_nonneg _ _
  · exact ⟨Q, hQ, rfl⟩

/-! ### Bridging lemmas: how far a local flip moves a law -/

private theorem flipKernel_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {η : ℝ}
    (h0 : 0 ≤ η) (h1 : η ≤ 1) (x y : ι → Bool) : 0 ≤ flipKernel η x y :=
  Finset.prod_nonneg fun i _ => by
    rcases eq_or_ne (x i) (y i) with h | h
    · rw [ite_eq_left h]; linarith
    · rw [ite_eq_right h]; linarith

private theorem sum_flipKernel {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (x : ι → Bool) :
    ∑ y : ι → Bool, flipKernel η x y = 1 := by
  have h := (Fintype.prod_sum (κ := fun _ : ι => Bool)
      (fun i (b : Bool) => if x i = b then 1 - η else η)).symm
  simp only [flipKernel]
  rw [h]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Fintype.sum_bool]
  cases x i <;> simp

private theorem flipKernel_self {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (x : ι → Bool) :
    flipKernel η x x = (1 - η) ^ Fintype.card ι := by
  simp [flipKernel]

/-- Independent flips with probability `η` move a law by at most `|ι| η` in total variation. -/
theorem dTV_flipLaw_le {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (P : (ι → Bool) → ℝ) (hP : IsLaw P) :
    dTV P (flipLaw η P) ≤ Fintype.card ι * η := by
  have hK0 : ∀ x y : ι → Bool, 0 ≤ flipKernel η x y := fun x y => flipKernel_nonneg h0 h1 x y
  have hself1 : ∀ x : ι → Bool, flipKernel η x x ≤ 1 := by
    intro x
    rw [flipKernel_self]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hlow : ∀ x : ι → Bool, 1 - Fintype.card ι * η ≤ flipKernel η x x := by
    intro x
    rw [flipKernel_self]
    have hb := one_add_mul_le_pow (a := -η) (by linarith) (Fintype.card ι)
    have he : (1 : ℝ) + -η = 1 - η := by ring
    rw [he] at hb
    have : (1:ℝ) - Fintype.card ι * η = 1 + Fintype.card ι * (-η) := by ring
    rw [this]
    exact hb
  have hrow : ∀ x : ι → Bool,
      ∑ y : ι → Bool, |(if x = y then (1:ℝ) else 0) - flipKernel η x y|
        ≤ 2 * (Fintype.card ι * η) := by
    intro x
    have hsplit : ∑ y : ι → Bool, |(if x = y then (1:ℝ) else 0) - flipKernel η x y|
        = |1 - flipKernel η x x| + ∑ y ∈ Finset.univ.erase x, flipKernel η x y := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
      congr 1
      · rw [ite_eq_left rfl]
      · refine Finset.sum_congr rfl fun y hy => ?_
        have hne : ¬ x = y := fun h => (Finset.ne_of_mem_erase hy) h.symm
        rw [ite_eq_right hne, zero_sub, abs_neg, abs_of_nonneg (hK0 x y)]
    have herase : ∑ y ∈ Finset.univ.erase x, flipKernel η x y = 1 - flipKernel η x x := by
      have := Finset.add_sum_erase Finset.univ (flipKernel η x) (Finset.mem_univ x)
      rw [sum_flipKernel] at this
      linarith
    rw [hsplit, herase, abs_of_nonneg (by linarith [hself1 x] : (0:ℝ) ≤ 1 - flipKernel η x x)]
    linarith [hlow x]
  have hdiff : ∀ y : ι → Bool, |P y - flipLaw η P y|
      ≤ ∑ x : ι → Bool, P x * |(if x = y then (1:ℝ) else 0) - flipKernel η x y| := by
    intro y
    have hrw : P y - flipLaw η P y
        = ∑ x : ι → Bool, P x * ((if x = y then (1:ℝ) else 0) - flipKernel η x y) := by
      simp only [mul_sub, Finset.sum_sub_distrib, flipLaw]
      congr 1
      simp
    rw [hrw]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (hP.1 x)]
  have hmain : ∑ y : ι → Bool, |P y - flipLaw η P y| ≤ 2 * (Fintype.card ι * η) := by
    calc ∑ y : ι → Bool, |P y - flipLaw η P y|
        ≤ ∑ y : ι → Bool, ∑ x : ι → Bool,
            P x * |(if x = y then (1:ℝ) else 0) - flipKernel η x y| :=
          Finset.sum_le_sum fun y _ => hdiff y
      _ = ∑ x : ι → Bool, P x * ∑ y : ι → Bool,
            |(if x = y then (1:ℝ) else 0) - flipKernel η x y| := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ x : ι → Bool, P x * (2 * (Fintype.card ι * η)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hP.1 x)
      _ = 2 * (Fintype.card ι * η) := by rw [← Finset.sum_mul, hP.2, one_mul]
  unfold dTV
  linarith


/-! ### Bridging lemmas: passing to a connected component -/

private theorem exists_liftWalk {W : Type} {G : SimpleGraph W} (C : G.ConnectedComponent) :
    ∀ {u v : W} (p : G.Walk u v) (hu : u ∈ C) (hv : v ∈ C),
      ∃ q : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩, q.map C.toSimpleGraph_hom = p := by
  intro u v p
  induction p with
  | nil => intro hu hv; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a b c hab p ih =>
      intro hu hv
      have hb : b ∈ C := C.mem_supp_of_adj_mem_supp hu hab
      obtain ⟨q, hq⟩ := ih hb hv
      refine ⟨SimpleGraph.Walk.cons (show C.toSimpleGraph.Adj ⟨a, hu⟩ ⟨b, hb⟩ from hab) q, ?_⟩
      simp only [SimpleGraph.Walk.map_cons, hq]
      rfl

private theorem component_not_isAcyclic {W : Type} {G : SimpleGraph W} {v : W}
    (c : G.Walk v v) (hc : c.IsCycle) :
    ¬ (G.connectedComponentMk v).toSimpleGraph.IsAcyclic := by
  intro hac
  obtain ⟨q, hq⟩ := exists_liftWalk (G.connectedComponentMk v) c
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  exact hac q (SimpleGraph.Walk.IsCycle.of_map (hq ▸ hc))

private theorem component_dist_le {W : Type} {G : SimpleGraph W} (C : G.ConnectedComponent)
    {u v : W} (hu : u ∈ C) (hv : v ∈ C) :
    G.dist u v ≤ C.toSimpleGraph.dist ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨p, hp⟩ := (C.reachable_toSimpleGraph hu hv).exists_walk_length_eq_dist
  have h := SimpleGraph.dist_le (p.map C.toSimpleGraph_hom)
  rw [SimpleGraph.Walk.length_map, hp] at h
  exact h

/-- If no connected component is a double star, neither is the graph. -/
theorem exists_bad_component (Γ : PairGraph) (hnot : ¬ IsDoubleStarForest Γ.G) :
    ∃ C : Γ.G.ConnectedComponent, ¬ IsDoubleStarForest C.toSimpleGraph := by
  by_contra hall
  push Not at hall
  refine hnot ⟨fun v c hc => component_not_isAcyclic c hc (hall _).1, fun u v huv => ?_⟩
  have hu : u ∈ Γ.G.connectedComponentMk u :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ Γ.G.connectedComponentMk u := SimpleGraph.ConnectedComponent.sound huv.symm
  refine le_trans (component_dist_le _ hu hv) ?_
  exact (hall (Γ.G.connectedComponentMk u)).2 _ _
    ((SimpleGraph.ConnectedComponent.connected_toSimpleGraph _).preconnected _ _)

/-- The pair-source scenario carried by one connected component. -/
noncomputable def componentPairGraph (Γ : PairGraph) (C : Γ.G.ConnectedComponent) :
    PairGraph where
  V := C
  fintypeV := Fintype.ofFinite _
  decEqV := Classical.decEq _
  G := C.toSimpleGraph
  decAdj := Classical.decRel _
  no_isolated := by
    rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := Γ.no_isolated v
    exact ⟨⟨w, C.mem_supp_of_adj_mem_supp hv hw⟩, hw⟩

/-- The inclusion of a component scenario into the ambient scenario is an induced embedding. -/
theorem componentPairGraph_embed (Γ : PairGraph) (C : Γ.G.ConnectedComponent) :
    ∃ ρ : (componentPairGraph Γ C).V → Γ.V, Function.Injective ρ ∧
      ∀ a b, (componentPairGraph Γ C).G.Adj a b ↔ Γ.G.Adj (ρ a) (ρ b) :=
  ⟨fun a => a.1, fun _ _ h => Subtype.ext h, fun _ _ => Iff.rfl⟩

end TriangleInflation.Graph
