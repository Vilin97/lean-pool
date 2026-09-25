/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeRankFormula

/-!
# Semibreak divisors on banana graphs

A semibreak divisor is represented by an optional interior chip on each
strand.  This representation is definitionally effective, puts no chips at
the two core vertices, and makes both its degree and its Dhar burn explicit.

The main result is `rank_semibreak_sub_vertex_eq_neg_one`: if `E` has degree
at most the genus and `w` is outside its support, then `E - w` is `w`-reduced
with debt, hence has rank `-1`.  This is the support lemma needed by the
length-two cross-exception argument.

The last sections prove the reducedness and rank formula for a supplied
endpoint/semibreak normal form, extract that form from every left-reduced
divisor, and hence construct one in every linear-equivalence class.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The divisor with the selected optional interior chip on each strand and no chips at the core
vertices. -/
def semibreakDivisor {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1))) : CFDiv B.graph
  | Sum.inl _ => 0
  | Sum.inr ⟨γ, offset⟩ => if chips γ = some offset then 1 else 0

/-- A divisor represented by at most one selected interior chip per strand and none at the core
vertices. -/
def IsSemibreak {g : ℕ} (B : Banana g) (E : CFDiv B.graph) : Prop :=
  ∃ chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)),
    E = semibreakDivisor B chips

@[simp] theorem semibreakDivisor_coreVertex {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1))) (v : Fin 2) :
    semibreakDivisor B chips (B.coreVertex v) = 0 := by
  rfl

@[simp] theorem semibreakDivisor_interiorVertex {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (γ : Fin (g + 1)) (offset : Fin (B.length γ - 1)) :
    semibreakDivisor B chips (B.interiorVertex γ offset) =
      if chips γ = some offset then 1 else 0 := by
  rfl

theorem effective_semibreakDivisor {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1))) :
    effective (semibreakDivisor B chips) := by
  intro v
  rcases v with v | ⟨γ, offset⟩
  · change 0 ≤ (0 : ℤ)
    omega
  · change 0 ≤ if chips γ = some offset then (1 : ℤ) else 0
    split <;> omega

namespace IsSemibreak

theorem effective {g : ℕ} {B : Banana g} {E : CFDiv B.graph}
    (hE : IsSemibreak B E) : effective E := by
  rcases hE with ⟨chips, rfl⟩
  exact effective_semibreakDivisor B chips

theorem coreVertex_eq_zero {g : ℕ} {B : Banana g}
    {E : CFDiv B.graph} (hE : IsSemibreak B E) (v : Fin 2) :
    E (B.coreVertex v) = 0 := by
  rcases hE with ⟨chips, rfl⟩
  rfl

theorem interiorVertex_le_one {g : ℕ} {B : Banana g}
    {E : CFDiv B.graph} (hE : IsSemibreak B E) (γ : Fin (g + 1))
    (offset : Fin (B.length γ - 1)) :
    E (B.interiorVertex γ offset) ≤ 1 := by
  rcases hE with ⟨chips, rfl⟩
  simp only [semibreakDivisor_interiorVertex]
  split <;> omega

theorem eq_of_interiorVertex_eq_one {g : ℕ} {B : Banana g}
    {E : CFDiv B.graph} (hE : IsSemibreak B E) (γ : Fin (g + 1))
    (p q : Fin (B.length γ - 1))
    (hp : E (B.interiorVertex γ p) = 1)
    (hq : E (B.interiorVertex γ q) = 1) : p = q := by
  rcases hE with ⟨chips, rfl⟩
  rw [semibreakDivisor_interiorVertex] at hp hq
  have hpChip : chips γ = some p := by
    by_contra h
    rw [if_neg h] at hp
    omega
  have hqChip : chips γ = some q := by
    by_contra h
    rw [if_neg h] at hq
    omega
  exact Option.some.inj (hpChip.symm.trans hqChip)

/-- Restricting a semibreak divisor to a set of vertices cannot increase its
degree. -/
theorem sum_le_degree {g : ℕ} {B : Banana g}
    {E : CFDiv B.graph} (hE : IsSemibreak B E) (S : Finset B.graph.V) :
    (∑ z ∈ S, E z) ≤ deg E := by
  have hSubset : S ⊆ (Finset.univ : Finset B.graph.V) := by simp
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun z _ _ => hE.effective z)
  simpa only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hSum

end IsSemibreak

theorem degree_semibreakDivisor {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1))) :
    deg (semibreakDivisor B chips) =
      ∑ γ : Fin (g + 1), if (chips γ).isSome then (1 : ℤ) else 0 := by
  classical
  simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_sum_type,
    Fintype.sum_sigma]
  change (∑ _v : Fin 2, (0 : ℤ)) +
      (∑ γ : Fin (g + 1), ∑ offset : Fin (B.length γ - 1),
        (if chips γ = some offset then (1 : ℤ) else 0)) = _
  simp only [Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro γ _
  cases chips γ with
  | none => simp
  | some chip =>
      simp only [Option.isSome_some, if_true]
      simp

theorem exists_free_strand_of_degree_le_genus {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (hdeg : deg (semibreakDivisor B chips) ≤ (g : ℤ)) :
    ∃ γ : Fin (g + 1), chips γ = none := by
  by_contra hFree
  push Not at hFree
  have hTerm : ∀ γ : Fin (g + 1),
      (if (chips γ).isSome then (1 : ℤ) else 0) = 1 := by
    intro γ
    cases hchip : chips γ with
    | none => exact (hFree γ hchip).elim
    | some chip => simp
  have hDegree := degree_semibreakDivisor B chips
  rw [hDegree] at hdeg
  have hSum : (∑ γ : Fin (g + 1),
      if (chips γ).isSome then (1 : ℤ) else 0) = (g : ℤ) + 1 := by
    calc
      _ = ∑ _γ : Fin (g + 1), (1 : ℤ) := by
        exact Finset.sum_congr rfl fun γ _ => hTerm γ
      _ = (g : ℤ) + 1 := by simp
  omega

@[simp] theorem semibreakDivisor_pathVertex_of_none {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (γ : Fin (g + 1)) (hchip : chips γ = none) (p : B.PathPosition γ) :
    semibreakDivisor B chips (B.pathVertex γ p) = 0 := by
  by_cases hp0 : p.val = 0
  · have hp : p = ⟨0, by omega⟩ := Fin.ext hp0
    rw [hp, B.pathVertex_zero]
    rfl
  · by_cases hpLast : p.val = B.length γ
    · have hp : p = ⟨B.length γ, by omega⟩ := Fin.ext hpLast
      rw [hp, B.pathVertex_length]
      rfl
    · have hpInterior : B.IsInteriorPosition γ p := by
        change 0 < p.val ∧ p.val < B.length γ
        have hpBound := p.isLt
        omega
      rw [B.pathVertex_eq_interiorVertex γ p hpInterior]
      simp [hchip]

theorem semibreakDivisor_pathVertex_eq_zero_of_ne_chip {g : ℕ}
    (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (γ : Fin (g + 1)) (chip : Fin (B.length γ - 1))
    (hchip : chips γ = some chip) (p : B.PathPosition γ)
    (hp : p.val ≠ chip.val + 1) :
    semibreakDivisor B chips (B.pathVertex γ p) = 0 := by
  by_cases hp0 : p.val = 0
  · have hpos := chip.isLt
    have hp' : p = ⟨0, by omega⟩ := Fin.ext hp0
    rw [hp', B.pathVertex_zero]
    rfl
  · by_cases hpLast : p.val = B.length γ
    · have hp' : p = ⟨B.length γ, by omega⟩ := Fin.ext hpLast
      rw [hp', B.pathVertex_length]
      rfl
    · have hpInterior : B.IsInteriorPosition γ p := by
        change 0 < p.val ∧ p.val < B.length γ
        have hpBound := p.isLt
        omega
      rw [B.pathVertex_eq_interiorVertex γ p hpInterior]
      have hOffset : chip ≠ B.interiorOffsetOfPosition γ p hpInterior := by
        intro h
        apply hp
        have hval := congrArg Fin.val h
        simp only [interiorOffsetOfPosition] at hval
        omega
      simp [hchip, hOffset]

private theorem neighbor_mem_of_no_burn_zero
    (G : CFGraph) (q : G.V) (E : CFDiv G) (S : Finset G.V)
    (hS : S ⊆ Finset.univ.filter (· ≠ q))
    (hNoBurn : ∀ z ∈ S,
      ¬ (E - oneChip q) z <
        ∑ y ∈ (Finset.univ.filter fun x => x ∉ S), (numEdges G z y : ℤ))
    {z : G.V} (hz : z ∈ S) (hEz : E z = 0)
    {y : G.V} (hEdge : 0 < numEdges G z y) :
    y ∈ S := by
  by_contra hy
  have hqz : z ≠ q := by
    intro hzq
    have := hS hz
    simp [hzq] at this
  have hyFilter : y ∈ Finset.univ.filter fun x => x ∉ S := by
    simp [hy]
  have hTerm : (1 : ℤ) ≤ (numEdges G z y : ℤ) := by
    exact_mod_cast hEdge
  have hTermLe : (numEdges G z y : ℤ) ≤
      ∑ x ∈ (Finset.univ.filter fun t => t ∉ S), (numEdges G z x : ℤ) := by
    exact Finset.single_le_sum
      (fun x _ => Int.natCast_nonneg (numEdges G z x)) hyFilter
  apply hNoBurn z hz
  have hValue : (E - oneChip q) z = 0 := by
    simp [Pi.sub_apply, oneChip, hqz, hEz]
  rw [hValue]
  omega

private theorem neighbor_mem_of_no_burn_zero_direct
    (G : CFGraph) (D : CFDiv G) (S : Finset G.V)
    (hNoBurn : ∀ z ∈ S,
      ¬ D z < ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
        (numEdges G z y : ℤ))
    {z : G.V} (hz : z ∈ S) (hDz : D z = 0)
    {y : G.V} (hEdge : 0 < numEdges G z y) :
    y ∈ S := by
  by_contra hy
  have hyFilter : y ∈ Finset.univ.filter fun x => x ∉ S := by
    simp [hy]
  have hTerm : (1 : ℤ) ≤ (numEdges G z y : ℤ) := by
    exact_mod_cast hEdge
  have hTermLe : (numEdges G z y : ℤ) ≤
      ∑ x ∈ (Finset.univ.filter fun t => t ∉ S),
        (numEdges G z x : ℤ) := by
    exact Finset.single_le_sum
      (fun x _ => Int.natCast_nonneg (numEdges G z x)) hyFilter
  apply hNoBurn z hz
  rw [hDz]
  omega

private theorem path_mem_forward_of_zero
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph) (S : Finset B.graph.V)
    (hClosed : ∀ {z : B.graph.V}, z ∈ S → E z = 0 →
      ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S)
    (γ : Fin (g + 1)) (lo hi : B.PathPosition γ) (hlt : lo.val < hi.val)
    (hlo : B.pathVertex γ lo ∈ S)
    (hzero : ∀ p : B.PathPosition γ, lo.val ≤ p.val → p.val < hi.val →
      E (B.pathVertex γ p) = 0) :
    B.pathVertex γ hi ∈ S := by
  by_contra hhi
  obtain ⟨offset, hOffsetLo, hOffsetHi, hLeft, hRight⟩ :=
    B.exists_crossing_step_between S γ lo hi hlt hlo hhi
  have hSourceZero :=
    hzero (B.stepLeftPosition γ offset) hOffsetLo hOffsetHi
  rw [B.pathVertex_stepLeftPosition] at hSourceZero
  have hEdge : 0 < numEdges B.graph (B.stepLeft γ offset)
      (B.stepRight γ offset) := by
    simpa using B.consecutive_num_edges_pos γ offset
  have hNext := hClosed hLeft hSourceZero hEdge
  exact hRight hNext

private theorem path_mem_reverse_of_zero
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph) (S : Finset B.graph.V)
    (hClosed : ∀ {z : B.graph.V}, z ∈ S → E z = 0 →
      ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S)
    (γ : Fin (g + 1)) (lo hi : B.PathPosition γ) (hlt : lo.val < hi.val)
    (hhi : B.pathVertex γ hi ∈ S)
    (hzero : ∀ p : B.PathPosition γ, lo.val < p.val → p.val ≤ hi.val →
      E (B.pathVertex γ p) = 0) :
    B.pathVertex γ lo ∈ S := by
  by_contra hlo
  have hloComp : B.pathVertex γ lo ∈ Sᶜ := Finset.mem_compl.mpr hlo
  have hhiComp : B.pathVertex γ hi ∉ Sᶜ := by simpa using hhi
  obtain ⟨offset, hOffsetLo, hOffsetHi, hLeftComp, hRightComp⟩ :=
    B.exists_crossing_step_between Sᶜ γ lo hi hlt hloComp hhiComp
  have hLeftOut : B.stepLeft γ offset ∉ S := by
    simpa using hLeftComp
  have hRightIn : B.stepRight γ offset ∈ S := by
    by_contra hRightOut
    exact hRightComp (Finset.mem_compl.mpr hRightOut)
  have hSourceZero :=
    hzero (B.stepRightPosition γ offset) (by simp [stepRightPosition]; omega)
      (by simp [stepRightPosition]; omega)
  rw [B.pathVertex_stepRightPosition] at hSourceZero
  have hEdge : 0 < numEdges B.graph (B.stepRight γ offset)
      (B.stepLeft γ offset) := by
    rw [num_edges_symmetric]
    simpa using B.consecutive_num_edges_pos γ offset
  have hPrevious := hClosed hRightIn hSourceZero hEdge
  exact hLeftOut hPrevious

private theorem fin_two_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  fin_cases v <;> simp

private theorem not_both_core_mem_of_no_burn
    {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (S : Finset B.graph.V) (w : B.graph.V)
    (hw : semibreakDivisor B chips w = 0) (hwS : w ∉ S)
    (hClosed : ∀ {z : B.graph.V}, z ∈ S →
      semibreakDivisor B chips z = 0 →
      ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S) :
    ¬ (B.coreVertex (0 : Fin 2) ∈ S ∧ B.coreVertex (1 : Fin 2) ∈ S) := by
  intro hBoth
  rcases w with core | interior
  · rcases fin_two_cases core with hcore | hcore
    · apply hwS
      change B.coreVertex core ∈ S
      rw [hcore]
      exact hBoth.1
    · apply hwS
      change B.coreVertex core ∈ S
      rw [hcore]
      exact hBoth.2
  · rcases interior with ⟨γ, q⟩
    let qpos : B.PathPosition γ :=
      ⟨q.val + 1, by have := q.isLt; have hpos := B.length_pos γ; omega⟩
    have hqInterior : B.IsInteriorPosition γ qpos := by
      change 0 < qpos.val ∧ qpos.val < B.length γ
      dsimp [qpos]
      have := q.isLt
      have hpos := B.length_pos γ
      omega
    have hqVertex : B.pathVertex γ qpos = B.interiorVertex γ q := by
      rw [B.pathVertex_eq_interiorVertex γ qpos hqInterior]
      congr 2
    have hqOut : B.pathVertex γ qpos ∉ S := by
      rwa [hqVertex]
    have hTail : B.pathVertex γ ⟨0, by omega⟩ ∈ S := by
      rw [B.pathVertex_zero]
      rcases fin_two_cases (B.core.tail γ) with h | h
      · simpa [h] using hBoth.1
      · simpa [h] using hBoth.2
    have hHead : B.pathVertex γ ⟨B.length γ, by omega⟩ ∈ S := by
      rw [B.pathVertex_length]
      rcases fin_two_cases (B.core.head γ) with h | h
      · simpa [h] using hBoth.1
      · simpa [h] using hBoth.2
    cases hchip : chips γ with
    | none =>
        apply hqOut
        apply path_mem_forward_of_zero B (semibreakDivisor B chips) S hClosed
          γ ⟨0, by omega⟩ qpos (by simp [qpos]) hTail
        intro p _ _
        exact semibreakDivisor_pathVertex_of_none B chips γ hchip p
    | some chip =>
        have hchipNe : chip ≠ q := by
          intro h
          subst chip
          change semibreakDivisor B chips (B.interiorVertex γ q) = 0 at hw
          have hOne : semibreakDivisor B chips (B.interiorVertex γ q) = 1 := by
            simp [hchip]
          omega
        have hvalNe : chip.val ≠ q.val := fun h => hchipNe (Fin.ext h)
        by_cases hchipLeft : chip.val < q.val
        · apply hqOut
          apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S hClosed
            γ qpos ⟨B.length γ, by omega⟩ (by
              have := q.isLt
              simp [qpos]
              omega) hHead
          intro p hpLo _
          apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
            B chips γ chip hchip p
          dsimp [qpos] at hpLo
          omega
        · have hqLeft : q.val < chip.val := by omega
          apply hqOut
          apply path_mem_forward_of_zero B (semibreakDivisor B chips) S hClosed
            γ ⟨0, by omega⟩ qpos (by simp [qpos]) hTail
          intro p _ hpHi
          apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
            B chips γ chip hchip p
          dsimp [qpos] at hpHi
          omega

private theorem core_mem_iff_of_free_strand
    {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (S : Finset B.graph.V)
    (hClosed : ∀ {z : B.graph.V}, z ∈ S →
      semibreakDivisor B chips z = 0 →
      ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S)
    (γ : Fin (g + 1)) (hchip : chips γ = none) :
    B.coreVertex (0 : Fin 2) ∈ S ↔ B.coreVertex (1 : Fin 2) ∈ S := by
  have hRaw : B.coreVertex (B.core.tail γ) ∈ S ↔
      B.coreVertex (B.core.head γ) ∈ S := by
    constructor
    · intro hTail
      have hTail' : B.pathVertex γ ⟨0, by omega⟩ ∈ S := by
        rw [B.pathVertex_zero]
        exact hTail
      have hHead := path_mem_forward_of_zero B (semibreakDivisor B chips) S
        hClosed γ ⟨0, by omega⟩ ⟨B.length γ, by omega⟩
        (B.length_pos γ) hTail' (fun p _ _ =>
          semibreakDivisor_pathVertex_of_none B chips γ hchip p)
      rw [B.pathVertex_length] at hHead
      exact hHead
    · intro hHead
      have hHead' : B.pathVertex γ ⟨B.length γ, by omega⟩ ∈ S := by
        rw [B.pathVertex_length]
        exact hHead
      have hTail := path_mem_reverse_of_zero B (semibreakDivisor B chips) S
        hClosed γ ⟨0, by omega⟩ ⟨B.length γ, by omega⟩
        (B.length_pos γ) hHead' (fun p _ _ =>
          semibreakDivisor_pathVertex_of_none B chips γ hchip p)
      rw [B.pathVertex_zero] at hTail
      exact hTail
  rcases fin_two_cases (B.core.tail γ) with hTail | hTail <;>
    rcases fin_two_cases (B.core.head γ) with hHead | hHead
  · exact (B.core_loopless γ (hTail.trans hHead.symm)).elim
  · simpa [hTail, hHead] using hRaw
  · simpa [hTail, hHead] using hRaw.symm
  · exact (B.core_loopless γ (hTail.trans hHead.symm)).elim

private theorem false_of_no_burn_with_two_outside_neighbors
    (G : CFGraph) (q : G.V) (E : CFDiv G) (S : Finset G.V)
    (hS : S ⊆ Finset.univ.filter (· ≠ q))
    (hNoBurn : ∀ z ∈ S,
      ¬ (E - oneChip q) z <
        ∑ y ∈ (Finset.univ.filter fun x => x ∉ S), (numEdges G z y : ℤ))
    {z y₁ y₂ : G.V} (hz : z ∈ S) (hEz : E z = 1)
    (hyNe : y₁ ≠ y₂) (hy₁ : y₁ ∉ S) (hy₂ : y₂ ∉ S)
    (hEdge₁ : 0 < numEdges G z y₁) (hEdge₂ : 0 < numEdges G z y₂) :
    False := by
  have hSubset : ({y₁, y₂} : Finset G.V) ⊆
      Finset.univ.filter fun x => x ∉ S := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp [hy₁, hy₂]
  have hBound := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun y _ _ => Int.natCast_nonneg (numEdges G z y))
  have hPair : (numEdges G z y₁ : ℤ) + (numEdges G z y₂ : ℤ) ≤
      ∑ y ∈ (Finset.univ.filter fun x => x ∉ S), (numEdges G z y : ℤ) := by
    simpa [Finset.sum_pair hyNe] using hBound
  have hOne₁ : (1 : ℤ) ≤ (numEdges G z y₁ : ℤ) := by
    exact_mod_cast hEdge₁
  have hOne₂ : (1 : ℤ) ≤ (numEdges G z y₂ : ℤ) := by
    exact_mod_cast hEdge₂
  have hqz : z ≠ q := by
    intro hzq
    have := hS hz
    simp [hzq] at this
  apply hNoBurn z hz
  have hValue : (E - oneChip q) z = 1 := by
    simp [Pi.sub_apply, oneChip, hqz, hEz]
  rw [hValue]
  omega

private theorem false_of_no_burn_with_two_outside_neighbors_direct
    (G : CFGraph) (D : CFDiv G) (S : Finset G.V)
    (hNoBurn : ∀ z ∈ S,
      ¬ D z < ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
        (numEdges G z y : ℤ))
    {z y₁ y₂ : G.V} (hz : z ∈ S) (hDz : D z = 1)
    (hyNe : y₁ ≠ y₂) (hy₁ : y₁ ∉ S) (hy₂ : y₂ ∉ S)
    (hEdge₁ : 0 < numEdges G z y₁) (hEdge₂ : 0 < numEdges G z y₂) :
    False := by
  have hSubset : ({y₁, y₂} : Finset G.V) ⊆
      Finset.univ.filter fun x => x ∉ S := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp [hy₁, hy₂]
  have hBound := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun y _ _ => Int.natCast_nonneg (numEdges G z y))
  have hPair : (numEdges G z y₁ : ℤ) + (numEdges G z y₂ : ℤ) ≤
      ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
        (numEdges G z y : ℤ) := by
    simpa [Finset.sum_pair hyNe] using hBound
  have hOne₁ : (1 : ℤ) ≤ (numEdges G z y₁ : ℤ) := by
    exact_mod_cast hEdge₁
  have hOne₂ : (1 : ℤ) ≤ (numEdges G z y₂ : ℤ) := by
    exact_mod_cast hEdge₂
  apply hNoBurn z hz
  rw [hDz]
  omega

/-- Once both core vertices are outside a non-burning set, the path geometry
and the one-chip-per-strand condition force that set to be empty. -/
private theorem false_of_no_burn_semibreak_of_core_out
    {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (D : CFDiv B.graph) (S : Finset B.graph.V)
    (hNoBurn : ∀ z ∈ S,
      ¬ D z < ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
        (numEdges B.graph z y : ℤ))
    (hCoreZeroOut : B.coreVertex (0 : Fin 2) ∉ S)
    (hCoreOneOut : B.coreVertex (1 : Fin 2) ∉ S)
    (hInteriorValue : ∀ (γ : Fin (g + 1))
      (q : Fin (B.length γ - 1)),
      D (B.interiorVertex γ q) =
        semibreakDivisor B chips (B.interiorVertex γ q))
    (hNonempty : S.Nonempty) : False := by
  have hClosed : ∀ {z : B.graph.V}, z ∈ S →
      semibreakDivisor B chips z = 0 →
      ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S := by
    intro z hz hEz y hEdge
    rcases z with core | interior
    · rcases fin_two_cases core with hcore | hcore
      · apply (hCoreZeroOut (by
          change B.coreVertex core ∈ S at hz
          simpa [hcore] using hz)).elim
      · apply (hCoreOneOut (by
          change B.coreVertex core ∈ S at hz
          simpa [hcore] using hz)).elim
    · rcases interior with ⟨γ, q⟩
      apply neighbor_mem_of_no_burn_zero_direct B.graph D S hNoBurn hz
      change D (B.interiorVertex γ q) = 0
      rw [hInteriorValue]
      simpa [SubdivisionGraph.Spec.interiorVertex] using hEz
      exact hEdge
  obtain ⟨z, hz⟩ := hNonempty
  rcases z with core | interior
  · rcases fin_two_cases core with hcore | hcore
    · apply hCoreZeroOut
      change B.coreVertex core ∈ S at hz
      simpa [hcore] using hz
    · apply hCoreOneOut
      change B.coreVertex core ∈ S at hz
      simpa [hcore] using hz
  · rcases interior with ⟨γ, q⟩
    let qpos : B.PathPosition γ :=
      ⟨q.val + 1, by have := q.isLt; have hpos := B.length_pos γ; omega⟩
    have hqInterior : B.IsInteriorPosition γ qpos := by
      change 0 < qpos.val ∧ qpos.val < B.length γ
      dsimp [qpos]
      have := q.isLt
      have hpos := B.length_pos γ
      omega
    have hqVertex : B.pathVertex γ qpos = B.interiorVertex γ q := by
      rw [B.pathVertex_eq_interiorVertex γ qpos hqInterior]
      congr 2
    have hzPath : B.pathVertex γ qpos ∈ S := by
      rwa [hqVertex]
    have hTailOut : B.pathVertex γ ⟨0, by omega⟩ ∉ S := by
      rw [B.pathVertex_zero]
      rcases fin_two_cases (B.core.tail γ) with h | h
      · simpa [h] using hCoreZeroOut
      · simpa [h] using hCoreOneOut
    have hHeadOut : B.pathVertex γ ⟨B.length γ, by omega⟩ ∉ S := by
      rw [B.pathVertex_length]
      rcases fin_two_cases (B.core.head γ) with h | h
      · simpa [h] using hCoreZeroOut
      · simpa [h] using hCoreOneOut
    cases hchip : chips γ with
    | none =>
        apply hTailOut
        apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S hClosed
          γ ⟨0, by omega⟩ qpos (by simp [qpos]) hzPath
        intro p _ _
        exact semibreakDivisor_pathVertex_of_none B chips γ hchip p
    | some chip =>
        by_cases hqChip : q = chip
        · subst chip
          let previous : B.PathPosition γ :=
            B.previousPathPosition γ qpos hqInterior.1
          let next : B.PathPosition γ :=
            B.nextPathPosition γ qpos hqInterior.2
          have hPreviousOut : B.pathVertex γ previous ∉ S := by
            intro hPrevious
            by_cases hPreviousZero : previous.val = 0
            · apply hTailOut
              have hp : previous = ⟨0, by omega⟩ := Fin.ext hPreviousZero
              simpa [hp] using hPrevious
            · apply hTailOut
              apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S
                hClosed γ ⟨0, by omega⟩ previous
                (Nat.pos_of_ne_zero hPreviousZero) hPrevious
              intro p _ hpHi
              apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                B chips γ q hchip p
              dsimp [previous, qpos, previousPathPosition] at hpHi
              omega
          have hNextOut : B.pathVertex γ next ∉ S := by
            intro hNext
            by_cases hNextLast : next.val = B.length γ
            · apply hHeadOut
              have hp : next = ⟨B.length γ, by omega⟩ := Fin.ext hNextLast
              simpa [hp] using hNext
            · apply hHeadOut
              apply path_mem_forward_of_zero B (semibreakDivisor B chips) S
                hClosed γ next ⟨B.length γ, by omega⟩ (by
                  change next.val < B.length γ
                  have hNextBound := next.isLt
                  omega) hNext
              intro p hpLo _
              apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                B chips γ q hchip p
              dsimp [next, qpos, nextPathPosition] at hpLo
              omega
          have hPreviousNeNext : B.pathVertex γ previous ≠
              B.pathVertex γ next := by
            intro hEq
            have hPos := congrArg Fin.val (B.pathVertex_injective γ hEq)
            dsimp [previous, next, qpos, previousPathPosition,
              nextPathPosition] at hPos
            omega
          have hPreviousEdge : 0 < numEdges B.graph
              (B.pathVertex γ qpos) (B.pathVertex γ previous) :=
            (B.pathVertex_num_edges_pos_iff γ qpos hqInterior
              (B.pathVertex γ previous)).2 (Or.inl rfl)
          have hNextEdge : 0 < numEdges B.graph
              (B.pathVertex γ qpos) (B.pathVertex γ next) :=
            (B.pathVertex_num_edges_pos_iff γ qpos hqInterior
              (B.pathVertex γ next)).2 (Or.inr rfl)
          have hSemibreakValue :
              semibreakDivisor B chips (B.interiorVertex γ q) = 1 := by
            simp [hchip]
          have hValue : D (B.pathVertex γ qpos) = 1 := by
            rw [hqVertex, hInteriorValue]
            exact hSemibreakValue
          exact false_of_no_burn_with_two_outside_neighbors_direct B.graph
            D S hNoBurn hzPath hValue hPreviousNeNext hPreviousOut hNextOut
            hPreviousEdge hNextEdge
        · have hvalNe : q.val ≠ chip.val := fun h => hqChip (Fin.ext h)
          by_cases hqLeft : q.val < chip.val
          · apply hTailOut
            apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S
              hClosed γ ⟨0, by omega⟩ qpos (by simp [qpos]) hzPath
            intro p _ hpHi
            apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
              B chips γ chip hchip p
            dsimp [qpos] at hpHi
            omega
          · have hchipLeft : chip.val < q.val := by omega
            apply hHeadOut
            apply path_mem_forward_of_zero B (semibreakDivisor B chips) S
              hClosed γ qpos ⟨B.length γ, by omega⟩ (by
                have := q.isLt
                simp [qpos]
                omega) hzPath
            intro p hpLo _
            apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
              B chips γ chip hchip p
            dsimp [qpos] at hpLo
            omega

theorem q_reduced_semibreak_sub_vertex {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E ≤ (g : ℤ))
    (w : B.graph.V) (hw : E w = 0) :
    qReduced B.graph w (E - oneChip w) := by
  rcases hE with ⟨chips, rfl⟩
  refine ⟨?_, ?_⟩
  · intro z hzw
    have hEff := effective_semibreakDivisor B chips z
    simpa [Pi.sub_apply, oneChip, hzw] using hEff
  · intro S hwS hNonempty hLegal
    have hS : S ⊆ Finset.univ.filter (· ≠ w) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hzw
      exact hwS (hzw ▸ hz)
    have hNoBurn : ∀ z ∈ S,
        ¬ (semibreakDivisor B chips - oneChip w) z <
          ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
            (numEdges B.graph z y : ℤ) := by
      intro z hz
      rw [← outdeg_S_eq_sum_filter]
      exact not_lt.mpr (hLegal z hz)
    have hwS : w ∉ S := by
      intro hwMem
      have := hS hwMem
      simp at this
    have hClosed : ∀ {z : B.graph.V}, z ∈ S →
        semibreakDivisor B chips z = 0 →
        ∀ {y : B.graph.V}, 0 < numEdges B.graph z y → y ∈ S := by
      intro z hz hEz y hEdge
      exact neighbor_mem_of_no_burn_zero B.graph w (semibreakDivisor B chips)
        S hS hNoBurn hz hEz hEdge
    have hNotBoth := not_both_core_mem_of_no_burn B chips S w hw hwS hClosed
    obtain ⟨free, hfree⟩ :=
      exists_free_strand_of_degree_le_genus B chips hdeg
    have hCoreIff := core_mem_iff_of_free_strand B chips S hClosed free hfree
    have hCoreZeroOut : B.coreVertex (0 : Fin 2) ∉ S := by
      intro hZero
      exact hNotBoth ⟨hZero, hCoreIff.mp hZero⟩
    have hCoreOneOut : B.coreVertex (1 : Fin 2) ∉ S := by
      intro hOne
      exact hNotBoth ⟨hCoreIff.mpr hOne, hOne⟩
    obtain ⟨z, hz⟩ := hNonempty
    rcases z with core | interior
    · rcases fin_two_cases core with hcore | hcore
      · apply hCoreZeroOut
        change B.coreVertex core ∈ S at hz
        rwa [hcore] at hz
      · apply hCoreOneOut
        change B.coreVertex core ∈ S at hz
        rwa [hcore] at hz
    · rcases interior with ⟨γ, q⟩
      let qpos : B.PathPosition γ :=
        ⟨q.val + 1, by have := q.isLt; have hpos := B.length_pos γ; omega⟩
      have hqInterior : B.IsInteriorPosition γ qpos := by
        change 0 < qpos.val ∧ qpos.val < B.length γ
        dsimp [qpos]
        have := q.isLt
        have hpos := B.length_pos γ
        omega
      have hqVertex : B.pathVertex γ qpos = B.interiorVertex γ q := by
        rw [B.pathVertex_eq_interiorVertex γ qpos hqInterior]
        congr 2
      have hzPath : B.pathVertex γ qpos ∈ S := by
        rwa [hqVertex]
      have hTailOut : B.pathVertex γ ⟨0, by omega⟩ ∉ S := by
        rw [B.pathVertex_zero]
        rcases fin_two_cases (B.core.tail γ) with h | h
        · simpa [h] using hCoreZeroOut
        · simpa [h] using hCoreOneOut
      have hHeadOut : B.pathVertex γ ⟨B.length γ, by omega⟩ ∉ S := by
        rw [B.pathVertex_length]
        rcases fin_two_cases (B.core.head γ) with h | h
        · simpa [h] using hCoreZeroOut
        · simpa [h] using hCoreOneOut
      cases hchip : chips γ with
      | none =>
          apply hTailOut
          apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S hClosed
            γ ⟨0, by omega⟩ qpos (by simp [qpos]) hzPath
          intro p _ _
          exact semibreakDivisor_pathVertex_of_none B chips γ hchip p
      | some chip =>
          by_cases hqChip : q = chip
          · subst chip
            let previous : B.PathPosition γ :=
              B.previousPathPosition γ qpos hqInterior.1
            let next : B.PathPosition γ :=
              B.nextPathPosition γ qpos hqInterior.2
            have hPreviousOut : B.pathVertex γ previous ∉ S := by
              intro hPrevious
              by_cases hPreviousZero : previous.val = 0
              · apply hTailOut
                have hp : previous = ⟨0, by omega⟩ := Fin.ext hPreviousZero
                simpa [hp] using hPrevious
              · apply hTailOut
                apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S
                  hClosed γ ⟨0, by omega⟩ previous
                  (Nat.pos_of_ne_zero hPreviousZero) hPrevious
                intro p _ hpHi
                apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                  B chips γ q hchip p
                dsimp [previous, qpos, previousPathPosition] at hpHi
                omega
            have hNextOut : B.pathVertex γ next ∉ S := by
              intro hNext
              by_cases hNextLast : next.val = B.length γ
              · apply hHeadOut
                have hp : next = ⟨B.length γ, by omega⟩ := Fin.ext hNextLast
                simpa [hp] using hNext
              · apply hHeadOut
                apply path_mem_forward_of_zero B (semibreakDivisor B chips) S
                  hClosed γ next ⟨B.length γ, by omega⟩ (by
                    change next.val < B.length γ
                    have hNextBound := next.isLt
                    omega) hNext
                intro p hpLo _
                apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                  B chips γ q hchip p
                dsimp [next, qpos, nextPathPosition] at hpLo
                omega
            have hPreviousNeNext : B.pathVertex γ previous ≠
                B.pathVertex γ next := by
              intro hEq
              have hPos := congrArg Fin.val (B.pathVertex_injective γ hEq)
              dsimp [previous, next, qpos, previousPathPosition,
                nextPathPosition] at hPos
              omega
            have hPreviousEdge : 0 < numEdges B.graph
                (B.pathVertex γ qpos) (B.pathVertex γ previous) :=
              (B.pathVertex_num_edges_pos_iff γ qpos hqInterior
                (B.pathVertex γ previous)).2 (Or.inl rfl)
            have hNextEdge : 0 < numEdges B.graph
                (B.pathVertex γ qpos) (B.pathVertex γ next) :=
              (B.pathVertex_num_edges_pos_iff γ qpos hqInterior
                (B.pathVertex γ next)).2 (Or.inr rfl)
            have hValue : semibreakDivisor B chips (B.pathVertex γ qpos) = 1 := by
              rw [hqVertex]
              simp [hchip]
            exact false_of_no_burn_with_two_outside_neighbors B.graph w
              (semibreakDivisor B chips) S hS hNoBurn hzPath hValue
              hPreviousNeNext hPreviousOut hNextOut hPreviousEdge hNextEdge
          · have hvalNe : q.val ≠ chip.val := fun h => hqChip (Fin.ext h)
            by_cases hqLeft : q.val < chip.val
            · apply hTailOut
              apply path_mem_reverse_of_zero B (semibreakDivisor B chips) S
                hClosed γ ⟨0, by omega⟩ qpos (by simp [qpos]) hzPath
              intro p _ hpHi
              apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                B chips γ chip hchip p
              dsimp [qpos] at hpHi
              omega
            · have hchipLeft : chip.val < q.val := by omega
              apply hHeadOut
              apply path_mem_forward_of_zero B (semibreakDivisor B chips) S
                hClosed γ qpos ⟨B.length γ, by omega⟩ (by
                  have := q.isLt
                  simp [qpos]
                  omega) hzPath
              intro p hpLo _
              apply semibreakDivisor_pathVertex_eq_zero_of_ne_chip
                B chips γ chip hchip p
              dsimp [qpos] at hpLo
              omega

theorem rank_semibreak_sub_vertex_eq_neg_one {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E ≤ (g : ℤ))
    (w : B.graph.V) (hw : E w = 0) :
    rank B.graph (E - oneChip w) = -1 := by
  apply rank_eq_neg_one_of_qReduced_debt B.graph w
    (E - oneChip w) (q_reduced_semibreak_sub_vertex B E hE hdeg w hw)
  simp [Pi.sub_apply, oneChip, hw]

/-- A semibreak divisor of degree at most the genus has rank exactly zero. -/
theorem rank_semibreak_eq_zero {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E ≤ (g : ℤ)) :
    rank B.graph E = 0 := by
  have hEffective := hE.effective
  have hNonneg : 0 ≤ rank B.graph E := by
    apply (rank_geq_iff B.graph E 0).mp
    exact (rank_nonneg_iff_winnable B.graph E).mpr
      (winnable_of_effective B.graph E hEffective)
  have hLeft : E (leftEndpoint B) = 0 := by
    simpa [leftEndpoint] using hE.coreVertex_eq_zero (0 : Fin 2)
  have hSub := rank_semibreak_sub_vertex_eq_neg_one B E hE hdeg
    (leftEndpoint B) hLeft
  have hNotOne : ¬ 1 ≤ rank B.graph E := by
    intro hOne
    have hWin := (rank_ge_one_iff_winnable_sub_one_chip B.graph E).mp hOne
      (leftEndpoint B)
    have hSubNonneg : 0 ≤ rank B.graph (E - oneChip (leftEndpoint B)) := by
      apply (rank_geq_iff B.graph _ 0).mp
      exact (rank_nonneg_iff_winnable B.graph _).mpr hWin
    rw [hSub] at hSubNonneg
    omega
  omega

/-! ## The endpoint/semibreak normal-form interface -/

/-- The divisor `a·L + b·R + E` occurring in the banana reduced-divisor
normal form. -/
noncomputable def bananaNormalForm {g : ℕ} (B : Banana g) (a b : ℤ)
    (E : CFDiv B.graph) : CFDiv B.graph :=
  a • oneChip (leftEndpoint B) + b • oneChip (rightEndpoint B) + E

/-- The numerical side condition in the paper's banana normal form. -/
def IsBananaNormalForm {g : ℕ} (B : Banana g) (b : ℤ)
    (E : CFDiv B.graph) : Prop :=
  IsSemibreak B E ∧ 0 ≤ b ∧ b + deg E ≤ (g : ℤ)

@[simp] theorem degree_bananaNormalForm {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) :
    deg (bananaNormalForm B a b E) = a + b + deg E := by
  rw [bananaNormalForm, deg.map_add, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip]
  simp

@[simp] theorem bananaNormalForm_leftEndpoint {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E) :
    bananaNormalForm B a b E (leftEndpoint B) = a := by
  have hELeft : E (leftEndpoint B) = 0 := by
    simpa [leftEndpoint] using hE.coreVertex_eq_zero (0 : Fin 2)
  change E (Sum.inl (0 : Fin 2)) = 0 at hELeft
  simp [bananaNormalForm, leftEndpoint, rightEndpoint, oneChip,
    SubdivisionGraph.Spec.coreVertex, hELeft]

@[simp] theorem bananaNormalForm_rightEndpoint {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E) :
    bananaNormalForm B a b E (rightEndpoint B) = b := by
  have hERight : E (rightEndpoint B) = 0 := by
    simpa [rightEndpoint] using hE.coreVertex_eq_zero (1 : Fin 2)
  change E (Sum.inl (1 : Fin 2)) = 0 at hERight
  simp [bananaNormalForm, leftEndpoint, rightEndpoint, oneChip,
    SubdivisionGraph.Spec.coreVertex, hERight]

theorem effective_bananaNormalForm {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    effective (bananaNormalForm B a b E) := by
  intro z
  have hEz := hE.effective z
  have hLeft : 0 ≤ (a • oneChip (leftEndpoint B)) z := by
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = leftEndpoint B <;> simp [oneChip, hz, ha]
  have hRight : 0 ≤ (b • oneChip (rightEndpoint B)) z := by
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = rightEndpoint B <;> simp [oneChip, hz, hb]
  change 0 ≤ (a • oneChip (leftEndpoint B)) z +
    (b • oneChip (rightEndpoint B)) z + E z
  omega

theorem q_effective_bananaNormalForm {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) :
    qEffective (leftEndpoint B) (bananaNormalForm B a b E) := by
  intro z hzLeft
  have hEz := hE.effective z
  have hLeft : (a • oneChip (leftEndpoint B)) z = 0 := by
    simp [Pi.smul_apply, oneChip, hzLeft]
  have hRight : 0 ≤ (b • oneChip (rightEndpoint B)) z := by
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = rightEndpoint B <;> simp [oneChip, hz, hb]
  change 0 ≤ (a • oneChip (leftEndpoint B)) z +
    (b • oneChip (rightEndpoint B)) z + E z
  rw [hLeft]
  omega

/-- Every divisor in the paper's endpoint/semibreak normal-form range is
reduced at the left endpoint.  The coefficient at the reducing endpoint is
unrestricted, as reducedness only asks for effectivity away from it. -/
theorem q_reduced_bananaNormalForm {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    qReduced B.graph (leftEndpoint B) (bananaNormalForm B a b E) := by
  rcases hE with ⟨chips, rfl⟩
  let E : CFDiv B.graph := semibreakDivisor B chips
  have hE : IsSemibreak B E := ⟨chips, rfl⟩
  have hQE : qEffective (leftEndpoint B) (bananaNormalForm B a b E) :=
    q_effective_bananaNormalForm B a b E hE hb
  refine ⟨hQE, ?_⟩
  intro S hqS hNonempty hLegal
  have hS : S ⊆ Finset.univ.filter (· ≠ leftEndpoint B) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hzq
    exact hqS (hzq ▸ hz)
  have hNoBurn : ∀ z ∈ S,
      ¬ bananaNormalForm B a b E z <
        ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ) := by
    intro z hz
    rw [← outdeg_S_eq_sum_filter]
    exact not_lt.mpr (hLegal z hz)
  have hLeftOut : leftEndpoint B ∉ S := by
    intro hLeft
    have := hS hLeft
    simp at this
  have hRightOut : rightEndpoint B ∉ S := by
    intro hRight
    have hCross := strands_le_crossingSteps_of_core_separated B S (Or.inr ⟨by
      simpa [leftEndpoint] using hLeftOut, by
      simpa [rightEndpoint] using hRight⟩)
    have hCutLower : (g : ℤ) + 1 ≤
        ∑ z ∈ S, ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ) := by
      have hCrossInt : (g : ℤ) + 1 ≤ ((B.crossingSteps S).card : ℤ) := by
        exact_mod_cast hCross
      rw [← B.cutMultiplicity_eq_card_crossingSteps S] at hCrossInt
      unfold cutMultiplicity at hCrossInt
      simp_rw [outdeg_S_eq_sum_filter] at hCrossInt
      exact hCrossInt
    have hPointwise : ∀ z ∈ S,
        (∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ)) ≤ bananaNormalForm B a b E z := by
      intro z hz
      exact le_of_not_gt (hNoBurn z hz)
    have hCutLe :
        (∑ z ∈ S, ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ)) ≤
          ∑ z ∈ S, bananaNormalForm B a b E z := by
      exact Finset.sum_le_sum fun z hz => hPointwise z hz
    have hSumNormal :
        (∑ z ∈ S, bananaNormalForm B a b E z) =
          b + ∑ z ∈ S, E z := by
      simp [bananaNormalForm, Finset.sum_add_distrib, oneChip,
        hLeftOut, hRight]
    have hSumE := hE.sum_le_degree S
    have hdegE : b + deg E ≤ (g : ℤ) := by
      simpa [E] using hdeg
    rw [hSumNormal] at hCutLe
    omega
  exact (false_of_no_burn_semibreak_of_core_out B chips
    (bananaNormalForm B a b E) S hNoBurn
    (by simpa [leftEndpoint] using hLeftOut)
    (by simpa [rightEndpoint] using hRightOut) (by
      intro γ q
      simp [bananaNormalForm, E, leftEndpoint, rightEndpoint, oneChip,
        SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex]) hNonempty).elim

/-- The endpoint coefficients and semibreak divisor of two linearly equivalent
normal forms in the numerical range agree.  This is the uniqueness half of
the normal-form statement. -/
theorem bananaNormalForm_parameters_unique {g : ℕ} (B : Banana g)
    (a b a' b' : ℤ) (E E' : CFDiv B.graph)
    (hE : IsSemibreak B E) (hE' : IsSemibreak B E')
    (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hdeg : b + deg E ≤ (g : ℤ))
    (hdeg' : b' + deg E' ≤ (g : ℤ))
    (hLinear : linearEquiv B.graph (bananaNormalForm B a b E)
      (bananaNormalForm B a' b' E')) :
    a = a' ∧ b = b' ∧ E = E' := by
  have hEqual := q_reduced_unique B.graph (leftEndpoint B)
    (bananaNormalForm B a b E) (bananaNormalForm B a' b' E') ⟨
      q_reduced_bananaNormalForm B a b E hE hb hdeg,
      q_reduced_bananaNormalForm B a' b' E' hE' hb' hdeg', hLinear⟩
  have ha : a = a' := by
    have := congrFun hEqual (leftEndpoint B)
    simpa [bananaNormalForm_leftEndpoint B a b E hE,
      bananaNormalForm_leftEndpoint B a' b' E' hE'] using this
  have hbEq : b = b' := by
    have := congrFun hEqual (rightEndpoint B)
    simpa [bananaNormalForm_rightEndpoint B a b E hE,
      bananaNormalForm_rightEndpoint B a' b' E' hE'] using this
  refine ⟨ha, hbEq, ?_⟩
  funext z
  have hz := congrFun hEqual z
  rw [ha, hbEq] at hz
  unfold bananaNormalForm at hz
  simp only [Pi.add_apply, Pi.smul_apply] at hz
  omega

/-- The endpoint-swapped effectivity statement used for reduction at the
right endpoint. -/
theorem q_effective_bananaNormalForm_right {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (ha : 0 ≤ a) :
    qEffective (rightEndpoint B) (bananaNormalForm B a b E) := by
  intro z hzRight
  have hEz := hE.effective z
  have hRight : (b • oneChip (rightEndpoint B)) z = 0 := by
    simp [Pi.smul_apply, oneChip, hzRight]
  have hLeft : 0 ≤ (a • oneChip (leftEndpoint B)) z := by
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = leftEndpoint B <;> simp [oneChip, hz, ha]
  change 0 ≤ (a • oneChip (leftEndpoint B)) z +
    (b • oneChip (rightEndpoint B)) z + E z
  rw [hRight]
  omega

/-- Symmetrically, bounding the left-endpoint coefficient makes the same
normal-form divisor reduced at the right endpoint. -/
theorem q_reduced_bananaNormalForm_right {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (ha : 0 ≤ a) (hdeg : a + deg E ≤ (g : ℤ)) :
    qReduced B.graph (rightEndpoint B) (bananaNormalForm B a b E) := by
  rcases hE with ⟨chips, rfl⟩
  let E : CFDiv B.graph := semibreakDivisor B chips
  have hE : IsSemibreak B E := ⟨chips, rfl⟩
  have hQE : qEffective (rightEndpoint B) (bananaNormalForm B a b E) :=
    q_effective_bananaNormalForm_right B a b E hE ha
  refine ⟨hQE, ?_⟩
  intro S hqS hNonempty hLegal
  have hS : S ⊆ Finset.univ.filter (· ≠ rightEndpoint B) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hzq
    exact hqS (hzq ▸ hz)
  have hNoBurn : ∀ z ∈ S,
      ¬ bananaNormalForm B a b E z <
        ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ) := by
    intro z hz
    rw [← outdeg_S_eq_sum_filter]
    exact not_lt.mpr (hLegal z hz)
  have hRightOut : rightEndpoint B ∉ S := by
    intro hRight
    have := hS hRight
    simp at this
  have hLeftOut : leftEndpoint B ∉ S := by
    intro hLeft
    have hCross := strands_le_crossingSteps_of_core_separated B S (Or.inl ⟨by
      simpa [leftEndpoint] using hLeft, by
      simpa [rightEndpoint] using hRightOut⟩)
    have hCutLower : (g : ℤ) + 1 ≤
        ∑ z ∈ S, ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ) := by
      have hCrossInt : (g : ℤ) + 1 ≤ ((B.crossingSteps S).card : ℤ) := by
        exact_mod_cast hCross
      rw [← B.cutMultiplicity_eq_card_crossingSteps S] at hCrossInt
      unfold cutMultiplicity at hCrossInt
      simp_rw [outdeg_S_eq_sum_filter] at hCrossInt
      exact hCrossInt
    have hPointwise : ∀ z ∈ S,
        (∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ)) ≤ bananaNormalForm B a b E z := by
      intro z hz
      exact le_of_not_gt (hNoBurn z hz)
    have hCutLe :
        (∑ z ∈ S, ∑ y ∈ (Finset.univ.filter fun x => x ∉ S),
          (numEdges B.graph z y : ℤ)) ≤
          ∑ z ∈ S, bananaNormalForm B a b E z := by
      exact Finset.sum_le_sum fun z hz => hPointwise z hz
    have hSumNormal :
        (∑ z ∈ S, bananaNormalForm B a b E z) =
          a + ∑ z ∈ S, E z := by
      simp [bananaNormalForm, Finset.sum_add_distrib, oneChip,
        hLeft, hRightOut]
    have hSumE := hE.sum_le_degree S
    have hdegE : a + deg E ≤ (g : ℤ) := by
      simpa [E] using hdeg
    rw [hSumNormal] at hCutLe
    omega
  exact (false_of_no_burn_semibreak_of_core_out B chips
    (bananaNormalForm B a b E) S hNoBurn
    (by simpa [leftEndpoint] using hLeftOut)
    (by simpa [rightEndpoint] using hRightOut) (by
      intro γ q
      simp [bananaNormalForm, E, leftEndpoint, rightEndpoint, oneChip,
        SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex]) hNonempty).elim

/-- Once reducedness is established, the sign criterion in banana normal
form follows from the generic reduced-divisor API. -/
theorem rank_bananaNormalForm_neg_iff_of_q_reduced {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b)
    (hReduced : qReduced B.graph (leftEndpoint B)
      (bananaNormalForm B a b E)) :
    rank B.graph (bananaNormalForm B a b E) = -1 ↔ a < 0 := by
  constructor
  · intro hRank
    by_contra haNeg
    have ha : 0 ≤ a := by omega
    have hEffective := effective_bananaNormalForm B a b E hE ha hb
    have hNonneg : 0 ≤ rank B.graph (bananaNormalForm B a b E) := by
      apply (rank_geq_iff B.graph _ 0).mp
      exact (rank_nonneg_iff_winnable B.graph _).mpr
        (winnable_of_effective B.graph _ hEffective)
    rw [hRank] at hNonneg
    omega
  · intro ha
    apply rank_eq_neg_one_of_qReduced_debt B.graph (leftEndpoint B)
      (bananaNormalForm B a b E) hReduced
    rw [bananaNormalForm_leftEndpoint B a b E hE]
    exact ha

/-- In the numerical normal-form range, the rank is negative exactly when the
unrestricted left-endpoint coefficient is negative. -/
theorem rank_bananaNormalForm_neg_iff {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    rank B.graph (bananaNormalForm B a b E) = -1 ↔ a < 0 := by
  exact rank_bananaNormalForm_neg_iff_of_q_reduced B a b E hE hb
    (q_reduced_bananaNormalForm B a b E hE hb hdeg)

/-- An effective test divisor whose subtraction has rank `-1` gives a strict
upper bound on rank. -/
private theorem rank_lt_of_effective_sub_rank_neg_one
    (G : CFGraph) (D A : CFDiv G) (k : ℤ)
    (hEffective : effective A) (hDegree : deg A = k)
    (hResidual : rank G (D - A) = -1) :
    rank G D < k := by
  by_contra hNot
  have hRank : k ≤ rank G D := by omega
  have hWinnable :=
    ((rank_geq_iff G D k).mpr hRank) A ⟨hEffective, hDegree⟩
  exact (rank_neg_one_iff_unwinnable G (D - A)).mp hResidual hWinnable

/-- Rank of a supplied banana normal form.  The semibreak inequalities bound
the right-endpoint coefficient; the left coefficient need only be at least
`-1`. -/
theorem rank_bananaNormalForm {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (ha : -1 ≤ a) (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    rank B.graph (bananaNormalForm B a b E) =
      max (min a b) (a + b + deg E - (g : ℤ)) := by
  by_cases haNonneg : 0 ≤ a
  · have hMinNonneg : 0 ≤ min a b := by omega
    let m : ℕ := (min a b).toNat
    let F : CFDiv B.graph :=
      bananaNormalForm B (a - min a b) (b - min a b) E
    have hm : (m : ℤ) = min a b := by
      simp [m, Int.toNat_of_nonneg hMinNonneg]
    have hFEffective : effective F := by
      apply effective_bananaNormalForm B (a - min a b)
        (b - min a b) E hE <;> omega
    have hDecomp :
        bananaNormalForm B a b E = m • endpointPencilDivisor B + F := by
      dsimp [F]
      unfold bananaNormalForm endpointPencilDivisor
      ext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [nsmul_eq_mul]
      rw [hm]
      ring
    have hLowerMin :
        min a b ≤ rank B.graph (bananaNormalForm B a b E) := by
      rw [hDecomp]
      have hLower := rank_add_effective_ge B.graph
        (m • endpointPencilDivisor B) F hFEffective (m : ℤ)
        (rank_endpointPencil_nsmul_ge B m)
      simpa [hm] using hLower
    have hRR := riemann_roch_for_graphs (graphConnected B)
      (bananaNormalForm B a b E)
    have hDual := rank_geq_neg_one B.graph
      (canonicalDivisor B.graph - bananaNormalForm B a b E)
    have hLowerRR :
        a + b + deg E - (g : ℤ) ≤
          rank B.graph (bananaNormalForm B a b E) := by
      rw [degree_bananaNormalForm, B.genus_graph] at hRR
      omega
    by_cases haBound : a + deg E ≤ (g : ℤ)
    · by_cases hab : a ≤ b
      · let A : CFDiv B.graph := (a + 1) • oneChip (leftEndpoint B)
        have hAEffective : effective A := by
          exact effective_zsmul_one_chip_of_nonneg B.graph
            (leftEndpoint B) (a + 1) (by omega)
        have hADegree : deg A = a + 1 := by
          dsimp [A]
          rw [map_zsmul, deg_one_chip]
          ring
        have hResidual :
            bananaNormalForm B a b E - A = bananaNormalForm B (-1) b E := by
          dsimp [A]
          unfold bananaNormalForm
          ext z
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have hResidualRank :
            rank B.graph (bananaNormalForm B a b E - A) = -1 := by
          rw [hResidual]
          exact (rank_bananaNormalForm_neg_iff B (-1) b E hE hb hdeg).2
            (by omega)
        have hUpper := rank_lt_of_effective_sub_rank_neg_one B.graph
          (bananaNormalForm B a b E) A (a + 1)
          hAEffective hADegree hResidualRank
        have hMin : min a b = a := min_eq_left hab
        have hRRLe : a + b + deg E - (g : ℤ) ≤ a := by omega
        rw [hMin, max_eq_left hRRLe]
        omega
      · have hba : b ≤ a := by omega
        let A : CFDiv B.graph := (b + 1) • oneChip (rightEndpoint B)
        have hAEffective : effective A := by
          exact effective_zsmul_one_chip_of_nonneg B.graph
            (rightEndpoint B) (b + 1) (by omega)
        have hADegree : deg A = b + 1 := by
          dsimp [A]
          rw [map_zsmul, deg_one_chip]
          ring
        have hResidual :
            bananaNormalForm B a b E - A = bananaNormalForm B a (-1) E := by
          dsimp [A]
          unfold bananaNormalForm
          ext z
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have hReduced := q_reduced_bananaNormalForm_right B a (-1) E hE
          haNonneg haBound
        have hResidualRank :
            rank B.graph (bananaNormalForm B a b E - A) = -1 := by
          rw [hResidual]
          apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
            (bananaNormalForm B a (-1) E) hReduced
          rw [bananaNormalForm_rightEndpoint B a (-1) E hE]
          omega
        have hUpper := rank_lt_of_effective_sub_rank_neg_one B.graph
          (bananaNormalForm B a b E) A (b + 1)
          hAEffective hADegree hResidualRank
        have hMin : min a b = b := min_eq_right hba
        have hRRLe : a + b + deg E - (g : ℤ) ≤ b := by omega
        rw [hMin, max_eq_left hRRLe]
        omega
    · have hLeftCoeff : 0 ≤ a - (g : ℤ) + deg E := by omega
      let A : CFDiv B.graph :=
        (a - (g : ℤ) + deg E) • oneChip (leftEndpoint B) +
          (b + 1) • oneChip (rightEndpoint B)
      have hAEffective : effective A := by
        apply (Eff B.graph).add_mem
        · exact effective_zsmul_one_chip_of_nonneg B.graph
            (leftEndpoint B) (a - (g : ℤ) + deg E) hLeftCoeff
        · exact effective_zsmul_one_chip_of_nonneg B.graph
            (rightEndpoint B) (b + 1) (by omega)
      have hADegree :
          deg A = a + b + deg E - (g : ℤ) + 1 := by
        dsimp [A]
        rw [deg.map_add, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip]
        ring
      have hResidual :
          bananaNormalForm B a b E - A =
            bananaNormalForm B ((g : ℤ) - deg E) (-1) E := by
        dsimp [A]
        unfold bananaNormalForm
        ext z
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hRightCoeff : 0 ≤ (g : ℤ) - deg E := by omega
      have hReduced := q_reduced_bananaNormalForm_right B
        ((g : ℤ) - deg E) (-1) E hE hRightCoeff (by omega)
      have hResidualRank :
          rank B.graph (bananaNormalForm B a b E - A) = -1 := by
        rw [hResidual]
        apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
          (bananaNormalForm B ((g : ℤ) - deg E) (-1) E) hReduced
        rw [bananaNormalForm_rightEndpoint B ((g : ℤ) - deg E) (-1) E hE]
        omega
      have hUpper := rank_lt_of_effective_sub_rank_neg_one B.graph
        (bananaNormalForm B a b E) A
        (a + b + deg E - (g : ℤ) + 1)
        hAEffective hADegree hResidualRank
      have hMinLe : min a b ≤ a + b + deg E - (g : ℤ) := by
        have := min_le_right a b
        omega
      rw [max_eq_right hMinLe]
      omega
  · have haEq : a = -1 := by omega
    have hRank : rank B.graph (bananaNormalForm B a b E) = -1 :=
      (rank_bananaNormalForm_neg_iff B a b E hE hb hdeg).2 (by omega)
    have hMin : min a b = a := min_eq_left (by omega)
    have hRRLe : a + b + deg E - (g : ℤ) ≤ a := by omega
    rw [hRank, hMin, max_eq_left hRRLe]
    exact haEq.symm

@[simp] theorem rank_bananaNormalForm_zero_zero {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E ≤ (g : ℤ)) :
    rank B.graph (bananaNormalForm B 0 0 E) = 0 := by
  simpa [bananaNormalForm] using rank_semibreak_eq_zero B E hE hdeg

/-! ## Extraction of normal-form parameters from a reduced divisor -/

/-- The coefficient at the right endpoint of a left-reduced divisor is
nonnegative. -/
theorem q_reduced_rightEndpoint_nonneg {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D) :
    0 ≤ D (rightEndpoint B) := by
  apply hD.1
  simp [leftEndpoint, rightEndpoint,
    SubdivisionGraph.Spec.coreVertex]

/-- Every interior coefficient of a left-reduced divisor is nonnegative. -/
theorem q_reduced_interiorVertex_nonneg {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D)
    (γ : Fin (g + 1)) (offset : Fin (B.length γ - 1)) :
    0 ≤ D (B.interiorVertex γ offset) := by
  apply hD.1
  simp [leftEndpoint, SubdivisionGraph.Spec.coreVertex,
    SubdivisionGraph.Spec.interiorVertex]

/-- The singleton Dhar cut at a two-valent interior vertex bounds its
coefficient by one. -/
theorem q_reduced_interiorVertex_le_one {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D)
    (γ : Fin (g + 1)) (offset : Fin (B.length γ - 1)) :
    D (B.interiorVertex γ offset) ≤ 1 := by
  let v : B.graph.V := B.interiorVertex γ offset
  have hvLeft : v ≠ leftEndpoint B := by
    simp [v, leftEndpoint, SubdivisionGraph.Spec.coreVertex,
      SubdivisionGraph.Spec.interiorVertex]
  have hLeftNotMem : leftEndpoint B ∉ ({v} : Finset B.graph.V) := by
    simpa using hvLeft.symm
  obtain ⟨z, hz, hBurn⟩ :=
    hD.exists_lt_outdeg hLeftNotMem ⟨v, by simp⟩
  have hzv : z = v := by simpa using hz
  subst z
  have hDegree : vertexDegree B.graph v = 2 := by
    simpa [v] using B.vertex_degree_interiorVertex_eq_two γ offset
  rw [vertex_degree_eq_internalDegree_add_outdeg_S B.graph {v} v] at hDegree
  have hOut : outdegreeSet B.graph {v} v = 2 := by
    simpa [internalDegree] using hDegree
  change D v < outdegreeSet B.graph {v} v at hBurn
  rw [hOut] at hBurn
  dsimp [v] at hBurn
  omega
/-- A reduced divisor cannot have positive coefficients at two ordered,
distinct interior positions of the same strand. -/
private theorem false_of_q_reduced_two_positive_same_strand_of_lt
    {g : ℕ} {B : Banana g} {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D)
    (γ : Fin (g + 1)) (p q : Fin (B.length γ - 1))
    (hpq : p.val < q.val)
    (hp : 0 < D (B.interiorVertex γ p))
    (hq : 0 < D (B.interiorVertex γ q)) : False := by
  let ppos : B.PathPosition γ := ⟨p.val + 1, by
    have hpBound := p.isLt
    omega⟩
  let qpos : B.PathPosition γ := ⟨q.val + 1, by
    have hqBound := q.isLt
    omega⟩
  have hpInterior : B.IsInteriorPosition γ ppos := by
    change 0 < ppos.val ∧ ppos.val < B.length γ
    dsimp [ppos]
    have hpBound := p.isLt
    omega
  have hqInterior : B.IsInteriorPosition γ qpos := by
    change 0 < qpos.val ∧ qpos.val < B.length γ
    dsimp [qpos]
    have hqBound := q.isLt
    omega
  have hpqpos : ppos.val < qpos.val := by
    dsimp [ppos, qpos]
    omega
  have hpVertex : B.pathVertex γ ppos = B.interiorVertex γ p := by
    rw [B.pathVertex_eq_interiorVertex γ ppos hpInterior]
    congr 2
  have hqVertex : B.pathVertex γ qpos = B.interiorVertex γ q := by
    rw [B.pathVertex_eq_interiorVertex γ qpos hqInterior]
    congr 2
  let S : Finset B.graph.V := Finset.univ.filter fun z =>
    ∃ r : B.PathPosition γ,
      ppos.val ≤ r.val ∧ r.val ≤ qpos.val ∧ z = B.pathVertex γ r
  have hSubset : S ⊆ Finset.univ.filter (· ≠ leftEndpoint B) := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨r, hrLo, hrHi, rfl⟩ := hz
    have hrInterior : B.IsInteriorPosition γ r := by
      exact ⟨lt_of_lt_of_le hpInterior.1 hrLo,
        lt_of_le_of_lt hrHi hqInterior.2⟩
    rw [B.pathVertex_eq_interiorVertex γ r hrInterior]
    change Sum.inr _ ∈ Finset.univ.filter (fun x : B.graph.V => x ≠ Sum.inl 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
  have hNonempty : S.Nonempty := by
    refine ⟨B.pathVertex γ ppos, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ppos, le_rfl, hpqpos.le, rfl⟩
  have hLeftNotMem : leftEndpoint B ∉ S := by
    intro hLeft
    have := hSubset hLeft
    simp at this
  obtain ⟨z, hz, hBurn⟩ := hD.exists_lt_outdeg hLeftNotMem hNonempty
  have hzInterval := hz
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzInterval
  obtain ⟨r, hrLo, hrHi, rfl⟩ := hzInterval
  change D (B.pathVertex γ r) <
    outdegreeSet B.graph S (B.pathVertex γ r) at hBurn
  have hrInterior : B.IsInteriorPosition γ r := by
    exact ⟨lt_of_lt_of_le hpInterior.1 hrLo,
      lt_of_le_of_lt hrHi hqInterior.2⟩
  have hDegree : vertexDegree B.graph (B.pathVertex γ r) = 2 := by
    rw [B.pathVertex_eq_interiorVertex γ r hrInterior]
    exact B.vertex_degree_interiorVertex_eq_two γ
      (B.interiorOffsetOfPosition γ r hrInterior)
  rw [vertex_degree_eq_internalDegree_add_outdeg_S
    B.graph S (B.pathVertex γ r)] at hDegree
  by_cases hrP : r = ppos
  · subst r
    let next : B.PathPosition γ :=
      B.nextPathPosition γ ppos hpInterior.2
    have hNextMem : B.pathVertex γ next ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨next, ?_, ?_, rfl⟩
      · dsimp [next, nextPathPosition]
        exact Nat.le_succ _
      · dsimp [next, ppos, qpos, nextPathPosition]
        omega
    have hNextEdge : 0 < numEdges B.graph
        (B.pathVertex γ ppos) (B.pathVertex γ next) :=
      (B.pathVertex_num_edges_pos_iff γ ppos hpInterior
        (B.pathVertex γ next)).2 (Or.inr rfl)
    have hTerm : (1 : ℤ) ≤
        (numEdges B.graph (B.pathVertex γ ppos)
          (B.pathVertex γ next) : ℤ) := by
      exact_mod_cast hNextEdge
    have hTermLe :
        (numEdges B.graph (B.pathVertex γ ppos)
          (B.pathVertex γ next) : ℤ) ≤
          internalDegree B.graph S (B.pathVertex γ ppos) := by
      unfold internalDegree
      exact Finset.single_le_sum
        (fun y _ => Int.natCast_nonneg
          (numEdges B.graph (B.pathVertex γ ppos) y)) hNextMem
    have hDp : 1 ≤ D (B.pathVertex γ ppos) := by
      rw [hpVertex]
      omega
    omega
  · by_cases hrQ : r = qpos
    · subst r
      let previous : B.PathPosition γ :=
        B.previousPathPosition γ qpos hqInterior.1
      have hPreviousMem : B.pathVertex γ previous ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨previous, ?_, ?_, rfl⟩
        · dsimp [previous, ppos, qpos, previousPathPosition]
          omega
        · dsimp [previous, previousPathPosition]
          exact Nat.sub_le _ _
      have hPreviousEdge : 0 < numEdges B.graph
          (B.pathVertex γ qpos) (B.pathVertex γ previous) :=
        (B.pathVertex_num_edges_pos_iff γ qpos hqInterior
          (B.pathVertex γ previous)).2 (Or.inl rfl)
      have hTerm : (1 : ℤ) ≤
          (numEdges B.graph (B.pathVertex γ qpos)
            (B.pathVertex γ previous) : ℤ) := by
        exact_mod_cast hPreviousEdge
      have hTermLe :
          (numEdges B.graph (B.pathVertex γ qpos)
            (B.pathVertex γ previous) : ℤ) ≤
            internalDegree B.graph S (B.pathVertex γ qpos) := by
        unfold internalDegree
        exact Finset.single_le_sum
          (fun y _ => Int.natCast_nonneg
            (numEdges B.graph (B.pathVertex γ qpos) y)) hPreviousMem
      have hDq : 1 ≤ D (B.pathVertex γ qpos) := by
        rw [hqVertex]
        omega
      omega
    · have hrLoStrict : ppos.val < r.val := by
        have hne : r.val ≠ ppos.val := fun h => hrP (Fin.ext h)
        omega
      have hrHiStrict : r.val < qpos.val := by
        have hne : r.val ≠ qpos.val := fun h => hrQ (Fin.ext h)
        omega
      let previous : B.PathPosition γ :=
        B.previousPathPosition γ r hrInterior.1
      let next : B.PathPosition γ :=
        B.nextPathPosition γ r hrInterior.2
      have hPreviousMem : B.pathVertex γ previous ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨previous, ?_, ?_, rfl⟩
        · dsimp [previous, previousPathPosition]
          omega
        · dsimp [previous, previousPathPosition]
          omega
      have hNextMem : B.pathVertex γ next ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨next, ?_, ?_, rfl⟩
        · dsimp [next, nextPathPosition]
          omega
        · dsimp [next, nextPathPosition]
          omega
      have hPreviousNeNext : B.pathVertex γ previous ≠
          B.pathVertex γ next := by
        intro hEq
        have hPos := congrArg Fin.val (B.pathVertex_injective γ hEq)
        dsimp [previous, next, previousPathPosition, nextPathPosition] at hPos
        omega
      have hPreviousEdge : 0 < numEdges B.graph
          (B.pathVertex γ r) (B.pathVertex γ previous) :=
        (B.pathVertex_num_edges_pos_iff γ r hrInterior
          (B.pathVertex γ previous)).2 (Or.inl rfl)
      have hNextEdge : 0 < numEdges B.graph
          (B.pathVertex γ r) (B.pathVertex γ next) :=
        (B.pathVertex_num_edges_pos_iff γ r hrInterior
          (B.pathVertex γ next)).2 (Or.inr rfl)
      have hPreviousTerm : (1 : ℤ) ≤
          (numEdges B.graph (B.pathVertex γ r)
            (B.pathVertex γ previous) : ℤ) := by
        exact_mod_cast hPreviousEdge
      have hNextTerm : (1 : ℤ) ≤
          (numEdges B.graph (B.pathVertex γ r)
            (B.pathVertex γ next) : ℤ) := by
        exact_mod_cast hNextEdge
      have hPairSubset :
          ({B.pathVertex γ previous, B.pathVertex γ next} :
            Finset B.graph.V) ⊆ S := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hPreviousMem
        · exact hNextMem
      have hPairLe := Finset.sum_le_sum_of_subset_of_nonneg hPairSubset
        (fun y _ _ => Int.natCast_nonneg
          (numEdges B.graph (B.pathVertex γ r) y))
      have hInternal : (2 : ℤ) ≤
          internalDegree B.graph S (B.pathVertex γ r) := by
        unfold internalDegree
        have hPair :
            (numEdges B.graph (B.pathVertex γ r)
                (B.pathVertex γ previous) : ℤ) +
              (numEdges B.graph (B.pathVertex γ r)
                (B.pathVertex γ next) : ℤ) ≤
              ∑ y ∈ S,
                (numEdges B.graph (B.pathVertex γ r) y : ℤ) := by
          simpa [Finset.sum_pair hPreviousNeNext] using hPairLe
        omega
      have hDrNonneg : 0 ≤ D (B.pathVertex γ r) := by
        rw [B.pathVertex_eq_interiorVertex γ r hrInterior]
        exact q_reduced_interiorVertex_nonneg hD γ
          (B.interiorOffsetOfPosition γ r hrInterior)
      omega

/-- On a fixed strand, two positive interior coefficients of a reduced
divisor must occur at the same offset. -/
theorem q_reduced_positive_interiorVertex_unique {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D)
    (γ : Fin (g + 1)) (p q : Fin (B.length γ - 1))
    (hp : 0 < D (B.interiorVertex γ p))
    (hq : 0 < D (B.interiorVertex γ q)) : p = q := by
  by_contra hpq
  have hval : p.val ≠ q.val := fun h => hpq (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hpqLt | hqpLt
  · exact false_of_q_reduced_two_positive_same_strand_of_lt
      hD γ p q hpqLt hp hq
  · exact false_of_q_reduced_two_positive_same_strand_of_lt
      hD γ q p hqpLt hq hp

/-- The optional interior chip selected on each strand of a left-reduced
divisor.  If the strand has a positive interior coefficient, its unique such
offset is chosen; otherwise the strand is empty. -/
noncomputable def reducedSemibreakChips {g : ℕ} (B : Banana g)
    (D : CFDiv B.graph) :
    ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)) := fun γ =>
  if h : ∃ offset : Fin (B.length γ - 1),
      0 < D (B.interiorVertex γ offset) then
    some (Classical.choose h)
  else
    none

/-- The semibreak divisor extracted from a left-reduced divisor. -/
noncomputable def reducedSemibreakDivisor {g : ℕ} (B : Banana g)
    (D : CFDiv B.graph) : CFDiv B.graph :=
  semibreakDivisor B (reducedSemibreakChips B D)

/-- The selected chip family reproduces every interior coefficient of the
left-reduced divisor. -/
theorem reducedSemibreakDivisor_interiorVertex_eq {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D)
    (γ : Fin (g + 1)) (offset : Fin (B.length γ - 1)) :
    reducedSemibreakDivisor B D (B.interiorVertex γ offset) =
      D (B.interiorVertex γ offset) := by
  by_cases hPositive : 0 < D (B.interiorVertex γ offset)
  · have hExists : ∃ q : Fin (B.length γ - 1),
        0 < D (B.interiorVertex γ q) := ⟨offset, hPositive⟩
    have hChosenPositive :
        0 < D (B.interiorVertex γ (Classical.choose hExists)) :=
      Classical.choose_spec hExists
    have hChosen : Classical.choose hExists = offset :=
      q_reduced_positive_interiorVertex_unique hD γ
        (Classical.choose hExists) offset hChosenPositive hPositive
    have hValue : D (B.interiorVertex γ offset) = 1 := by
      have hUpper := q_reduced_interiorVertex_le_one hD γ offset
      omega
    simp [reducedSemibreakDivisor, reducedSemibreakChips, hExists,
      hChosen, hValue]
  · have hValue : D (B.interiorVertex γ offset) = 0 := by
      have hLower := q_reduced_interiorVertex_nonneg hD γ offset
      omega
    by_cases hExists : ∃ q : Fin (B.length γ - 1),
        0 < D (B.interiorVertex γ q)
    · have hChosenPositive :
          0 < D (B.interiorVertex γ (Classical.choose hExists)) :=
        Classical.choose_spec hExists
      have hChosenNe : Classical.choose hExists ≠ offset := by
        intro h
        subst offset
        exact hPositive hChosenPositive
      simp [reducedSemibreakDivisor, reducedSemibreakChips, hExists,
        hChosenNe, hValue]
    · simp [reducedSemibreakDivisor, reducedSemibreakChips, hExists, hValue]

/-- The divisor extracted from a left-reduced divisor is semibreak. -/
theorem isSemibreak_reducedSemibreakDivisor {g : ℕ} (B : Banana g)
    (D : CFDiv B.graph) : IsSemibreak B (reducedSemibreakDivisor B D) := by
  exact ⟨reducedSemibreakChips B D, rfl⟩

/-- A left-reduced divisor is exactly its two endpoint coefficients plus the
semibreak divisor extracted from its interior coefficients. -/
theorem eq_bananaNormalForm_reducedSemibreakDivisor {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D) :
    D = bananaNormalForm B (D (leftEndpoint B))
      (D (rightEndpoint B)) (reducedSemibreakDivisor B D) := by
  funext z
  rcases z with core | interior
  · fin_cases core <;>
      simp [bananaNormalForm, reducedSemibreakDivisor, semibreakDivisor,
        leftEndpoint, rightEndpoint, oneChip,
        SubdivisionGraph.Spec.coreVertex]
  · rcases interior with ⟨γ, offset⟩
    change D (B.interiorVertex γ offset) =
      bananaNormalForm B (D (leftEndpoint B)) (D (rightEndpoint B))
        (reducedSemibreakDivisor B D) (B.interiorVertex γ offset)
    simp only [bananaNormalForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hLeft : oneChip (leftEndpoint B)
        (B.interiorVertex γ offset) = 0 := by
      simp [oneChip, leftEndpoint, SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex]
    have hRight : oneChip (rightEndpoint B)
        (B.interiorVertex γ offset) = 0 := by
      simp [oneChip, rightEndpoint, SubdivisionGraph.Spec.coreVertex,
        SubdivisionGraph.Spec.interiorVertex]
    simpa [hLeft, hRight] using
      (reducedSemibreakDivisor_interiorVertex_eq hD γ offset).symm

/-- Existential form of semibreak extraction from a left-reduced divisor. -/
theorem exists_semibreak_bananaNormalForm_of_q_reduced {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D) :
    ∃ E : CFDiv B.graph, IsSemibreak B E ∧
      D = bananaNormalForm B (D (leftEndpoint B))
        (D (rightEndpoint B)) E := by
  exact ⟨reducedSemibreakDivisor B D,
    isSemibreak_reducedSemibreakDivisor B D,
    eq_bananaNormalForm_reducedSemibreakDivisor hD⟩

/-- Adding any number of chips at the reducing vertex does not change
reducedness: both q-effectivity and every Dhar inequality are evaluated away
from that vertex. -/
theorem q_reduced_add_zsmul_one_chip_at_reducing_vertex
    {G : CFGraph} {q : G.V} {D : CFDiv G}
    (hD : qReduced G q D) (k : ℤ) :
    qReduced G q (D + k • oneChip q) := by
  refine ⟨?_, ?_⟩
  · intro v hvq
    have hDv := hD.1 v hvq
    simpa [Pi.add_apply, Pi.smul_apply, oneChip, hvq] using hDv
  · intro S hqS hNonempty hLegal
    obtain ⟨v, hvS, hBurn⟩ := hD.exists_lt_outdeg hqS hNonempty
    apply (not_lt_of_ge (hLegal v hvS))
    have hvq : v ≠ q := by
      intro hvq
      exact hqS (hvq ▸ hvS)
    simpa [Pi.add_apply, Pi.smul_apply, oneChip, hvq] using hBurn

/-- The endpoint coefficient and extracted semibreak degree of a left-reduced
divisor satisfy the numerical normal-form bound. -/
theorem q_reduced_rightEndpoint_add_reducedSemibreakDivisor_degree_le_genus
    {g : ℕ} {B : Banana g} {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D) :
    D (rightEndpoint B) + deg (reducedSemibreakDivisor B D) ≤ (g : ℤ) := by
  let debt : CFDiv B.graph :=
    D + (-1 - D (leftEndpoint B)) • oneChip (leftEndpoint B)
  have hDebtReduced : qReduced B.graph (leftEndpoint B) debt := by
    exact q_reduced_add_zsmul_one_chip_at_reducing_vertex hD
      (-1 - D (leftEndpoint B))
  have hDebtValue : debt (leftEndpoint B) = -1 := by
    dsimp [debt]
    simp [oneChip]
  have hDebtRank : rank B.graph debt = -1 := by
    exact rank_eq_neg_one_of_qReduced_debt B.graph (leftEndpoint B)
      debt hDebtReduced (by omega)
  have hNormal := eq_bananaNormalForm_reducedSemibreakDivisor hD
  have hDegD := congrArg deg hNormal
  rw [degree_bananaNormalForm] at hDegD
  have hDebtDegree :
      deg debt = D (rightEndpoint B) +
        deg (reducedSemibreakDivisor B D) - 1 := by
    dsimp [debt]
    rw [deg.map_add, map_zsmul, deg_one_chip, hDegD]
    ring
  have hInequality := rank_degree_inequality (graphConnected B) debt
  have hResidualLower := rank_geq_neg_one B.graph
    (canonicalDivisor B.graph - debt)
  rw [hDebtDegree, B.genus_graph, hDebtRank] at hInequality
  omega

/-- Full converse normal-form statement for a left-reduced divisor. -/
theorem exists_bananaNormalForm_of_q_reduced {g : ℕ} {B : Banana g}
    {D : CFDiv B.graph}
    (hD : qReduced B.graph (leftEndpoint B) D) :
    ∃ E : CFDiv B.graph, IsSemibreak B E ∧
      0 ≤ D (rightEndpoint B) ∧
      D (rightEndpoint B) + deg E ≤ (g : ℤ) ∧
      D = bananaNormalForm B (D (leftEndpoint B))
        (D (rightEndpoint B)) E := by
  refine ⟨reducedSemibreakDivisor B D,
    isSemibreak_reducedSemibreakDivisor B D,
    q_reduced_rightEndpoint_nonneg hD,
    q_reduced_rightEndpoint_add_reducedSemibreakDivisor_degree_le_genus hD,
    eq_bananaNormalForm_reducedSemibreakDivisor hD⟩

/-- Every divisor class on a banana graph has a representative in banana
normal form with the required semibreak and numerical conditions. -/
theorem exists_linearly_equiv_bananaNormalForm {g : ℕ} (B : Banana g)
    (D : CFDiv B.graph) :
    ∃ (a b : ℤ) (E : CFDiv B.graph),
      IsSemibreak B E ∧ 0 ≤ b ∧ b + deg E ≤ (g : ℤ) ∧
      linearEquiv B.graph D (bananaNormalForm B a b E) := by
  obtain ⟨Dred, hLinear, hReduced⟩ :=
    exists_q_reduced_representative (graphConnected B) (leftEndpoint B) D
  obtain ⟨E, hE, hb, hdeg, hNormal⟩ :=
    exists_bananaNormalForm_of_q_reduced hReduced
  refine ⟨Dred (leftEndpoint B), Dred (rightEndpoint B), E,
    hE, hb, hdeg, ?_⟩
  rw [← hNormal]
  exact hLinear

/-- TeX label: Lemma 2.23 (unlabeled), final clause: `r(D) ≥ 0` iff `a ≥ 0`. -/
theorem banana_normalForm_rank_nonneg_iff {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    0 ≤ rank B.graph (bananaNormalForm B a b E) ↔ 0 ≤ a := by
  have hLower := rank_geq_neg_one B.graph (bananaNormalForm B a b E)
  have hIff := rank_bananaNormalForm_neg_iff B a b E hE hb hdeg
  constructor
  · intro hNonneg
    by_contra ha
    have : rank B.graph (bananaNormalForm B a b E) = -1 := hIff.2 (by omega)
    omega
  · intro ha
    by_contra hNeg
    have : rank B.graph (bananaNormalForm B a b E) = -1 := by omega
    exact absurd (hIff.1 this) (by omega)

end Bananas
