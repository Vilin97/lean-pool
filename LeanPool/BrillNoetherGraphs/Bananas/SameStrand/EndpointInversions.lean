/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
public import LeanPool.BrillNoetherGraphs.Utilities.Segments.SegmentReflection
public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Demazure.Submodular

/-!
# Endpoint transmission on banana graphs

This file proves the abstract existence/periodicity facts for transmission
permutations from the rank slipface.  The endpoint-specific rank calculation
and inversion count are developed separately from this generic layer.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

private noncomputable def rankSlipFunction (M : TwiceMarked) (D : CFDiv M.graph) :
    ℤ → ℤ → ℤ :=
  fun a b => rank M.graph (D + a • oneChip M.u - b • oneChip M.v) + 1

private theorem rankSlipFunction_D_props (M : TwiceMarked)
    (D : CFDiv M.graph) :
    SlipFace.D_props (rankSlipFunction M D) := by
  constructor
  · intro a b
    have h := rank_add_one_chip_ge
      (D + a • oneChip M.u - b • oneChip M.v) M.u
      (rank M.graph (D + a • oneChip M.u - b • oneChip M.v)) le_rfl
    have hDiv :
        D + (a + 1) • oneChip M.u - b • oneChip M.v =
          (D + a • oneChip M.u - b • oneChip M.v) + oneChip M.u := by
      rw [add_smul, one_smul]
      abel
    simpa only [rankSlipFunction, hDiv, add_le_add_iff_right] using h
  · intro a b
    have h := rank_add_one_chip_ge
      (D + a • oneChip M.u - (b + 1) • oneChip M.v) M.v
      (rank M.graph (D + a • oneChip M.u - (b + 1) • oneChip M.v)) le_rfl
    have hDiv :
        (D + a • oneChip M.u - (b + 1) • oneChip M.v) + oneChip M.v =
          D + a • oneChip M.u - b • oneChip M.v := by
      rw [add_smul, one_smul]
      abel
    simpa only [rankSlipFunction, hDiv, add_le_add_iff_right] using h
  · intro a
    refine ⟨deg D + a + 1, ?_⟩
    intro b hb
    unfold rankSlipFunction
    rw [rank_neg_one_of_deg_neg]
    · norm_num
    · rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
        deg_one_chip, deg_one_chip]
      simp only [smul_eq_mul, mul_one]
      omega
  · intro b
    refine ⟨b - deg D - 1, ?_⟩
    intro a ha
    unfold rankSlipFunction
    rw [rank_neg_one_of_deg_neg]
    · norm_num
    · rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
        deg_one_chip, deg_one_chip]
      simp only [smul_eq_mul, mul_one]
      omega

private theorem rankSlip_duality (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : graphConnected M.graph)
    (a b : ℤ) :
    rankSlipFunction M D a b -
        rankSlipFunction (mark M.graph M.v M.u) (canonicalDivisor M.graph - D) b a =
      a - b + (deg D - genus M.graph + 1) := by
  have hRR := riemann_roch_for_graphs hconn
    (D + a • oneChip M.u - b • oneChip M.v)
  have hComplement :
      canonicalDivisor M.graph -
          (D + a • oneChip M.u - b • oneChip M.v) =
        (canonicalDivisor M.graph - D) + b • oneChip M.v - a • oneChip M.u := by
    abel
  rw [hComplement] at hRR
  unfold rankSlipFunction
  change rank M.graph (D + a • oneChip M.u - b • oneChip M.v) + 1 -
      (rank M.graph
        ((canonicalDivisor M.graph - D) + b • oneChip M.v - a • oneChip M.u) + 1) = _
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip] at hRR
  simp only [smul_eq_mul, mul_one] at hRR
  omega

/-- The rank function of a twice-marked divisor, shifted by one, is a
slipface. -/
noncomputable def rankSlipFace (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : graphConnected M.graph) : SlipFace :=
  Classical.choose (show ∃ sf : SlipFace,
    (sf.func = rankSlipFunction M D ∧ sf.χ = deg D - genus M.graph + 1) ∧
      sf.dual.func = rankSlipFunction (mark M.graph M.v M.u) (canonicalDivisor M.graph - D)
    from by
      exact SlipFace.sf_of_D_props (rankSlip_duality M D hconn)
        ⟨rankSlipFunction_D_props M D,
          rankSlipFunction_D_props (mark M.graph M.v M.u)
            (canonicalDivisor M.graph - D)⟩)

@[simp] theorem rankSlipFace_apply (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : graphConnected M.graph)
    (a b : ℤ) :
    rankSlipFace M D hconn a b =
      rank M.graph (D + a • oneChip M.u - b • oneChip M.v) + 1 := by
  have h := Classical.choose_spec (SlipFace.sf_of_D_props (rankSlip_duality M D hconn)
    ⟨rankSlipFunction_D_props M D,
      rankSlipFunction_D_props (mark M.graph M.v M.u)
        (canonicalDivisor M.graph - D)⟩)
  exact congrFun (congrFun h.1.1 a) b

@[simp] theorem rankSlipFace_chi (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : graphConnected M.graph) :
    (rankSlipFace M D hconn).χ = deg D - genus M.graph + 1 := by
  exact (Classical.choose_spec (SlipFace.sf_of_D_props (rankSlip_duality M D hconn)
    ⟨rankSlipFunction_D_props M D,
      rankSlipFunction_D_props (mark M.graph M.v M.u)
        (canonicalDivisor M.graph - D)⟩)).1.2

theorem rankSlipFace_Delta (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : graphConnected M.graph)
    (a b : ℤ) :
    (rankSlipFace M D hconn).Δ a b =
      rankDelta M (D + (a + 1) • oneChip M.u - b • oneChip M.v) := by
  unfold SlipFace.Δ rankDelta
  simp only [rankSlipFace_apply]
  have hU :
      D + (a + 1) • oneChip M.u - b • oneChip M.v - oneChip M.u =
        D + a • oneChip M.u - b • oneChip M.v := by
    rw [add_smul, one_smul]
    abel
  have hV :
      D + (a + 1) • oneChip M.u - b • oneChip M.v - oneChip M.v =
        D + (a + 1) • oneChip M.u - (b + 1) • oneChip M.v := by
    rw [add_smul, one_smul]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring_nf
  have hUV :
      D + (a + 1) • oneChip M.u - b • oneChip M.v - oneChip M.u - oneChip M.v =
        D + a • oneChip M.u - (b + 1) • oneChip M.v := by
    rw [add_smul, one_smul]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring_nf
  have hLast :
      D + a • oneChip M.u - b • oneChip M.v - oneChip M.v =
        D + a • oneChip M.u - (b + 1) • oneChip M.v := by
    rw [add_smul, one_smul]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring_nf
  rw [hU, hV, hLast]
  ring

/-- Submodularity recovers the transmission permutation of a divisor. -/
theorem exists_transmissionPermutation_of_submodular
    (M : TwiceMarked) (D : CFDiv M.graph) (hconn : graphConnected M.graph)
    (hD : Submodular M D) :
    ∃ τ : ℤ → ℤ, IsTransmissionPermutation M D τ := by
  have hsub : (rankSlipFace M (D - oneChip M.u) hconn).submodular := by
    intro a b
    rw [rankSlipFace_Delta]
    have hDiv :
        D - oneChip M.u + (a + 1) • oneChip M.u - b • oneChip M.v =
          twist M D a (-b) := by
      unfold twist
      simp only [neg_smul]
      rw [add_smul, one_smul]
      abel
    rw [hDiv]
    exact hD a (-b)
  obtain ⟨σ, hσ⟩ := (Submodular.submodular_iff_asp
    (rankSlipFace M (D - oneChip M.u) hconn)).mp hsub
  refine ⟨σ, σ.bijective, ?_⟩
  intro a b
  rw [← σ.Delta_eq a b, hσ, rankSlipFace_Delta]
  have hDiv :
      D - oneChip M.u + (a + 1) • oneChip M.u - b • oneChip M.v =
        D + a • oneChip M.u - b • oneChip M.v := by
    rw [add_smul, one_smul]
    abel
  rw [hDiv]

private theorem linearEquiv_sub_fixed {M : TwiceMarked} {D E : CFDiv M.graph}
    (hDE : linearEquiv M.graph D E) (A : CFDiv M.graph) :
    linearEquiv M.graph (D - A) (E - A) := by
  unfold linearEquiv at hDE ⊢
  have hDifference : (E - A) - (D - A) = E - D := by abel
  rw [hDifference]
  exact hDE

theorem rankDelta_eq_of_linearEquiv {M : TwiceMarked} {D E : CFDiv M.graph}
    (hDE : linearEquiv M.graph D E) :
    rankDelta M D = rankDelta M E := by
  unfold rankDelta
  rw [rank_eq_of_linear_equiv M.graph hDE]
  rw [rank_eq_of_linear_equiv M.graph
    (linearEquiv_sub_fixed hDE (oneChip M.u))]
  rw [rank_eq_of_linear_equiv M.graph
    (linearEquiv_sub_fixed hDE (oneChip M.v))]
  rw [rank_eq_of_linear_equiv M.graph
    (linearEquiv_sub_fixed
      (linearEquiv_sub_fixed hDE (oneChip M.u)) (oneChip M.v))]

theorem rankDelta_marked_twist_add_torsion
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (a b : ℤ) :
      rankDelta M
        (D + (a + k) • oneChip M.u - (b + k) • oneChip M.v) =
      rankDelta M (D + a • oneChip M.u - b • oneChip M.v) := by
  rcases hk with ⟨_, hk⟩
  have hEquiv : linearEquiv M.graph
      (D + (a + k) • oneChip M.u - (b + k) • oneChip M.v)
      (D + a • oneChip M.u - b • oneChip M.v) := by
    unfold linearEquiv at hk ⊢
    have hDifference :
        (D + a • oneChip M.u - b • oneChip M.v) -
            (D + (a + k) • oneChip M.u - (b + k) • oneChip M.v) =
          0 - (k : ℤ) • (oneChip M.u - oneChip M.v) := by
      ext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring_nf
      simp
    rw [hDifference]
    exact hk
  exact rankDelta_eq_of_linearEquiv
    hEquiv

/-- A transmission permutation recovered from a submodular divisor is affine
at every torsion witness. -/
theorem exists_affineTransmissionPermutation_of_submodular
    (M : TwiceMarked) (D : CFDiv M.graph) (hconn : graphConnected M.graph)
    {k : ℕ} (hD : Submodular M D) (hk : TorsionWitness M k) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation M D τ ∧ IsKAffine k τ := by
  obtain ⟨τ, hτ⟩ := exists_transmissionPermutation_of_submodular M D hconn hD
  refine ⟨τ, hτ, ?_⟩
  intro n
  have hBase := hτ.2 (τ n) n
  simp only [ite_true] at hBase
  have hShift := hτ.2 (τ n + k) (n + k)
  rw [rankDelta_marked_twist_add_torsion hk D (τ n) n] at hShift
  rw [← hBase] at hShift
  by_contra hne
  rw [ite_eq_right hne] at hShift
  norm_num at hShift

/-! ## The endpoint pencil -/

private theorem banana_core_connected {g : ℕ} (B : Banana g) :
    B.core.Connected := by
  intro S hSplit
  obtain ⟨v, w, hv, hw⟩ := hSplit
  let edge : Fin (g + 1) := ⟨0, by omega⟩
  have hvw : v ≠ w := by
    intro hvw
    subst w
    exact hw hv
  have hEnds : B.core.tail edge ≠ B.core.head edge := B.core_loopless edge
  have hvwVals :
      (v.val = 0 ∧ w.val = 1) ∨ (v.val = 1 ∧ w.val = 0) := by
    have hvLt := v.isLt
    have hwLt := w.isLt
    have hvwVal : v.val ≠ w.val := by
      intro h
      exact hvw (Fin.ext h)
    omega
  have hEndVals :
      ((B.core.tail edge).val = 0 ∧ (B.core.head edge).val = 1) ∨
      ((B.core.tail edge).val = 1 ∧ (B.core.head edge).val = 0) := by
    have htLt := (B.core.tail edge).isLt
    have hhLt := (B.core.head edge).isLt
    have hneVal : (B.core.tail edge).val ≠ (B.core.head edge).val := by
      intro h
      exact hEnds (Fin.ext h)
    omega
  refine ⟨edge, ?_⟩
  rcases hvwVals with hvwVals | hvwVals <;>
    rcases hEndVals with hEndVals | hEndVals
  · left
    have ht : B.core.tail edge = v := Fin.ext (by omega)
    have hh : B.core.head edge = w := Fin.ext (by omega)
    simpa [ht, hh] using And.intro hv hw
  · right
    have hh : B.core.head edge = v := Fin.ext (by omega)
    have ht : B.core.tail edge = w := Fin.ext (by omega)
    simpa [ht, hh] using And.intro hv hw
  · right
    have hh : B.core.head edge = v := Fin.ext (by omega)
    have ht : B.core.tail edge = w := Fin.ext (by omega)
    simpa [ht, hh] using And.intro hv hw
  · left
    have ht : B.core.tail edge = v := Fin.ext (by omega)
    have hh : B.core.head edge = w := Fin.ext (by omega)
    simpa [ht, hh] using And.intro hv hw

theorem banana_graph_connected {g : ℕ} (B : Banana g) :
    graphConnected B.graph :=
  B.graph_connected_of_coreConnected (banana_core_connected B)

@[simp] theorem banana_genus {g : ℕ} (B : Banana g) :
    genus B.graph = (g : ℤ) := by
  rw [B.genus_graph]
  push_cast
  omega

/-- The literal divisor consisting of one chip at each multivalent endpoint. -/
def endpointPencilDivisor {g : ℕ} (B : Banana g) : CFDiv B.graph :=
  oneChip (leftEndpoint B) + oneChip (rightEndpoint B)

@[simp] theorem degree_endpointPencilDivisor {g : ℕ} (B : Banana g) :
    deg (endpointPencilDivisor B) = 2 := by
  simp [endpointPencilDivisor]

/-- The literal endpoint divisor (not merely some divisor supplied by
`BNExists`) has rank at least one. -/
theorem rank_endpointPencilDivisor_ge_one {g : ℕ} (B : Banana g) :
    1 ≤ rank B.graph (endpointPencilDivisor B) := by
  classical
  have hEffective : effective (endpointPencilDivisor B) :=
    (Eff B.graph).add_mem (eff_one_chip (leftEndpoint B))
      (eff_one_chip (rightEndpoint B))
  have hCoreValue (vertex : Fin 2) :
      1 ≤ endpointPencilDivisor B (B.coreVertex vertex) := by
    have hCases : vertex.val = 0 ∨ vertex.val = 1 := by omega
    rcases hCases with hLeft | hRight
    · have hEq : vertex = (0 : Fin 2) := Fin.ext hLeft
      subst vertex
      simp [endpointPencilDivisor, leftEndpoint, rightEndpoint,
        oneChip, Spec.coreVertex]
    · have hEq : vertex = (1 : Fin 2) := Fin.ext hRight
      subst vertex
      simp [endpointPencilDivisor, leftEndpoint, rightEndpoint,
        oneChip, Spec.coreVertex]
  change rank B.graph (endpointPencilDivisor B) ≥ 1
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro vertex
  rcases vertex with vertex | interior
  · apply winnable_of_effective
    intro q
    by_cases hq : q = B.coreVertex vertex
    · subst q
      simpa [oneChip, Spec.coreVertex] using
        (sub_nonneg.mpr (hCoreValue vertex))
    · change q ≠ Sum.inl vertex at hq
      simpa [oneChip, hq] using hEffective q
  · rcases interior with ⟨edge, offset⟩
    let position : B.PathPosition edge :=
      ⟨offset.val + 1, by have := offset.isLt; omega⟩
    have hPosition :
        B.pathVertex edge position = B.interiorVertex edge offset := by
      unfold Spec.pathVertex
      rw [dite_eq_right (by simp [position]), dite_eq_right (by
        have := offset.isLt
        simp only [position]
        omega)]
      congr 3
    change winnable B.graph
      (endpointPencilDivisor B - oneChip (B.interiorVertex edge offset))
    rw [← hPosition]
    exact SegmentReflection.reaches_pathPosition B (endpointPencilDivisor B)
      edge position hEffective (hCoreValue (B.core.tail edge))
      (hCoreValue (B.core.head edge))

/-- Public form of rank superadditivity.  The dependency proves this
internally for Clifford's theorem but keeps that lemma private. -/
theorem rank_add_ge_add_rank
    (G : CFGraph) (D E : CFDiv G)
    (hD : 0 ≤ rank G D) (hE : 0 ≤ rank G E) :
    rank G (D + E) ≥ rank G D + rank G E := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = rank G D :=
    ⟨_, Int.toNat_of_nonneg hD⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = rank G E :=
    ⟨_, Int.toNat_of_nonneg hE⟩
  have hRankGeq : rankGeq G (D + E) (r + s) := by
    rintro A ⟨hAEffective, hADegree⟩
    obtain ⟨A₁, A₂, hA₁Effective, hA₂Effective, hA₁Degree, hA₂Degree, rfl⟩ :=
      effective_divisor_decomposition G A r s hAEffective hADegree
    have hDWin := (rank_geq_iff G D r).mpr (le_of_eq hr) A₁
      ⟨hA₁Effective, hA₁Degree⟩
    have hEWin := (rank_geq_iff G E s).mpr (le_of_eq hs) A₂
      ⟨hA₂Effective, hA₂Degree⟩
    have hWin := winnable_add_winnable G (D - A₁) (E - A₂) hDWin hEWin
    convert hWin using 1 ; abel
  have h := (rank_geq_iff G (D + E) (r + s)).mp hRankGeq
  omega

/-- Every positive multiple of the endpoint pencil has at least the expected
hyperelliptic rank. -/
theorem rank_endpointPencil_nsmul_ge {g : ℕ} (B : Banana g) (b : ℕ) :
    (b : ℤ) ≤ rank B.graph (b • endpointPencilDivisor B) := by
  induction b with
  | zero => simp [zero_divisor_rank]
  | succ b ih =>
      have hPencil := rank_endpointPencilDivisor_ge_one B
      have hAdd := rank_add_ge_add_rank B.graph
        (b • endpointPencilDivisor B) (endpointPencilDivisor B)
        (by omega) (by omega)
      calc
        ((b + 1 : ℕ) : ℤ) = (b : ℤ) + 1 := by push_cast; rfl
        _ ≤ rank B.graph (b • endpointPencilDivisor B) +
            rank B.graph (endpointPencilDivisor B) := by omega
        _ ≤ rank B.graph
            (b • endpointPencilDivisor B + endpointPencilDivisor B) := hAdd
        _ = rank B.graph ((b + 1) • endpointPencilDivisor B) := by
          rw [add_nsmul, one_nsmul]

/-- Up through the genus, the `b`-fold endpoint pencil has rank exactly `b`. -/
theorem rank_endpointPencil_nsmul_eq {g : ℕ} (B : Banana g) (b : ℕ)
    (hb : b ≤ g) :
    rank B.graph (b • endpointPencilDivisor B) = (b : ℤ) := by
  have hLower := rank_endpointPencil_nsmul_ge B b
  have hDegree : deg (b • endpointPencilDivisor B) = (2 * b : ℕ) := by
    rw [map_nsmul, degree_endpointPencilDivisor]
    push_cast
    ring
  by_cases hbg : b < g
  · have hRange := (rank_nonspecial_range (banana_graph_connected B)
        (b • endpointPencilDivisor B)).2.1
    have hUpperQ := hRange (by
      constructor
      · rw [hDegree]
        positivity
      · rw [hDegree, banana_genus]
        have hsuccQ : ((b + 1 : ℕ) : ℚ) ≤ (g : ℚ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hbg)
        push_cast
        push_cast at hsuccQ
        linarith)
    rw [hDegree] at hUpperQ
    norm_num at hUpperQ
    have hUpper : rank B.graph (b • endpointPencilDivisor B) ≤ (b : ℤ) := by
      exact_mod_cast hUpperQ
    omega
  · have hbgEq : b = g := by omega
    subst b
    have hExact := (rank_nonspecial_range (banana_graph_connected B)
      (g • endpointPencilDivisor B)).2.2 (by
        rw [hDegree, banana_genus]
        push_cast
        omega)
    rw [hDegree, banana_genus] at hExact
    push_cast at hExact
    omega

private theorem rank_endpointPencil_nsmul_sub_endpoint_eq
    {g : ℕ} (B : Banana g) (w other : B.graph.V)
    (hPencil : endpointPencilDivisor B = oneChip w + oneChip other)
    (b : ℕ) (hbPos : 0 < b) (hb : b ≤ g) :
    rank B.graph (b • endpointPencilDivisor B - oneChip w) = (b : ℤ) - 1 := by
  have hbPred : b - 1 ≤ g := by omega
  have hBase := rank_endpointPencil_nsmul_eq B (b - 1) hbPred
  have hDiv :
      b • endpointPencilDivisor B - oneChip w =
        (b - 1) • endpointPencilDivisor B + oneChip other := by
    have hbDecomp : b = (b - 1) + 1 := by omega
    conv_lhs => rw [hbDecomp, add_nsmul, one_nsmul]
    rw [hPencil]
    abel
  have hBase' : rank B.graph ((b - 1) • endpointPencilDivisor B) =
      (b : ℤ) - 1 := by
    rw [hBase]
    omega
  have hLower := rank_add_effective_ge B.graph
    ((b - 1) • endpointPencilDivisor B) (oneChip other)
    (eff_one_chip other) ((b : ℤ) - 1) hBase'.ge
  rw [← hDiv] at hLower
  have hDegree :
      deg (b • endpointPencilDivisor B - oneChip w) = 2 * (b : ℤ) - 1 := by
    rw [deg.map_sub, map_nsmul, degree_endpointPencilDivisor, deg_one_chip]
    ring
  by_cases hbg : b < g
  · have hUpperQ := (rank_nonspecial_range (banana_graph_connected B)
      (b • endpointPencilDivisor B - oneChip w)).2.1 (by
        constructor
        · rw [hDegree]
          have hbQ : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hbPos
          push_cast
          linarith
        · rw [hDegree, banana_genus]
          have hsuccQ : ((b + 1 : ℕ) : ℚ) ≤ (g : ℚ) := by
            exact_mod_cast (Nat.succ_le_iff.mpr hbg)
          push_cast
          push_cast at hsuccQ
          linarith)
    rw [hDegree] at hUpperQ
    push_cast at hUpperQ
    have hUpper : rank B.graph
        (b • endpointPencilDivisor B - oneChip w) < (b : ℤ) := by
      by_contra hnot
      have hRankGe : (b : ℤ) ≤
          rank B.graph (b • endpointPencilDivisor B - oneChip w) := by omega
      have hRankGeQ : (b : ℚ) ≤
          (rank B.graph (b • endpointPencilDivisor B - oneChip w) : ℚ) := by
        exact_mod_cast hRankGe
      linarith
    omega
  · have hbgEq : b = g := by omega
    subst b
    have hgPos : 0 < g := hbPos
    have hExact := (rank_nonspecial_range (banana_graph_connected B)
      (g • endpointPencilDivisor B - oneChip w)).2.2 (by
        rw [hDegree, banana_genus]
        omega)
    rw [hDegree, banana_genus] at hExact
    omega

theorem rank_endpointPencil_nsmul_sub_left_eq
    {g : ℕ} (B : Banana g) (b : ℕ) (hbPos : 0 < b) (hb : b ≤ g) :
    rank B.graph (b • endpointPencilDivisor B - oneChip (leftEndpoint B)) =
      (b : ℤ) - 1 :=
  rank_endpointPencil_nsmul_sub_endpoint_eq B (leftEndpoint B) (rightEndpoint B)
    rfl b hbPos hb

theorem rank_endpointPencil_nsmul_sub_right_eq
    {g : ℕ} (B : Banana g) (b : ℕ) (hbPos : 0 < b) (hb : b ≤ g) :
    rank B.graph (b • endpointPencilDivisor B - oneChip (rightEndpoint B)) =
      (b : ℤ) - 1 :=
  rank_endpointPencil_nsmul_sub_endpoint_eq B (rightEndpoint B) (leftEndpoint B)
    (by simp [endpointPencilDivisor, add_comm]) b hbPos hb

/-- The marked rank second difference of every endpoint-pencil multiple up
to the genus is one.  This is the rank calculation which produces the
decreasing endpoint block in the transmission permutation. -/
theorem rankDelta_endpointPencil_nsmul_eq_one
    {g : ℕ} (B : Banana g) (b : ℕ) (hb : b ≤ g) :
    rankDelta (mark B.graph (leftEndpoint B) (rightEndpoint B))
      (b • endpointPencilDivisor B) = 1 := by
  by_cases hbZero : b = 0
  · subst b
    have hLeftDeg : deg ((0 : CFDiv B.graph) - oneChip (leftEndpoint B)) < 0 := by
      simp
    have hRightDeg : deg ((0 : CFDiv B.graph) - oneChip (rightEndpoint B)) < 0 := by
      simp
    have hBothDeg : deg ((0 : CFDiv B.graph) - oneChip (leftEndpoint B) -
        oneChip (rightEndpoint B)) < 0 := by
      simp
    unfold rankDelta
    simp only [zero_nsmul]
    change rank B.graph 0 - rank B.graph (0 - oneChip (leftEndpoint B)) -
        rank B.graph (0 - oneChip (rightEndpoint B)) +
          rank B.graph (0 - oneChip (leftEndpoint B) -
            oneChip (rightEndpoint B)) = 1
    rw [zero_divisor_rank]
    rw [rank_neg_one_of_deg_neg B.graph _ hLeftDeg,
      rank_neg_one_of_deg_neg B.graph _ hRightDeg,
      rank_neg_one_of_deg_neg B.graph _ hBothDeg]
    norm_num
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    have hRank := rank_endpointPencil_nsmul_eq B b hb
    have hLeft := rank_endpointPencil_nsmul_sub_left_eq B b hbPos hb
    have hRight := rank_endpointPencil_nsmul_sub_right_eq B b hbPos hb
    have hBothDiv :
        b • endpointPencilDivisor B - oneChip (leftEndpoint B) -
            oneChip (rightEndpoint B) =
          (b - 1) • endpointPencilDivisor B := by
      have hbDecomp : b = (b - 1) + 1 := by omega
      rw [hbDecomp, add_nsmul, one_nsmul]
      simp [endpointPencilDivisor]
      abel
    have hBothRank := rank_endpointPencil_nsmul_eq B (b - 1) (by omega)
    unfold rankDelta
    change rank B.graph (b • endpointPencilDivisor B) -
        rank B.graph (b • endpointPencilDivisor B - oneChip (leftEndpoint B)) -
        rank B.graph (b • endpointPencilDivisor B - oneChip (rightEndpoint B)) +
          rank B.graph (b • endpointPencilDivisor B - oneChip (leftEndpoint B) -
            oneChip (rightEndpoint B)) = 1
    rw [hRank, hLeft, hRight, hBothDiv, hBothRank]
    omega

end Bananas
