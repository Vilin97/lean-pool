/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import LeanPool.BKARForestFormula.BKAR.PartialDeriv

/-! # Active edges and one-edge forest extensions

The differential combinatorics of the forest induction.  An edge of the
complete graph is *active* for a forest `F` when its endpoints lie in
different `F`-components, so that inserting it yields again a forest.
Defines `activeEdges`, the insertion characterization of acyclicity, and
the direction data `activeDirection` used by the one-edge expansion step of
the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges whose endpoints lie in different `F`-components. -/
noncomputable def activeEdges (F : Forest V) : Finset (Edge V) :=
  (Finset.univ : Finset (Edge V)).filter
    (fun e => ¬ F.inSameComponent e.left e.right)

theorem mem_activeEdges_iff (F : Forest V) {e : Edge V} :
    e ∈ F.activeEdges ↔ ¬ F.inSameComponent e.left e.right := by
  rw [activeEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

theorem mem_activeEdges_of_not_inSameComponent (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∈ F.activeEdges :=
  (F.mem_activeEdges_iff).mpr he

theorem not_inSameComponent_of_mem_activeEdges (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    ¬ F.inSameComponent e.left e.right :=
  (F.mem_activeEdges_iff).mp he

theorem empty_activeEdges :
    (Forest.empty V).activeEdges = (Finset.univ : Finset (Edge V)) := by
  ext e
  rw [(Forest.empty V).mem_activeEdges_iff]
  constructor
  · intro _
    exact Finset.mem_univ e
  · intro _ hcomp
    exact e.left_ne_right (Forest.empty_inSameComponent_iff.mp hcomp)

/-- View any edge as an active edge of the empty forest. -/
noncomputable def emptyActiveEdge (e : Edge V) :
    {e // e ∈ (Forest.empty V).activeEdges} :=
  ⟨e, by
    rw [empty_activeEdges]
    exact Finset.mem_univ e⟩

@[simp]
theorem emptyActiveEdge_val (e : Edge V) :
    (emptyActiveEdge e : Edge V) = e :=
  rfl

theorem not_mem_edges_of_not_inSameComponent (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∉ F.edges := by
  intro hmem
  exact he (F.edge_inSameComponent hmem)

theorem not_mem_edges_of_mem_activeEdges (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    e ∉ F.edges :=
  F.not_mem_edges_of_not_inSameComponent
    (F.not_inSameComponent_of_mem_activeEdges he)

theorem acyclic_insert_iff_edge (F : Forest V) {e : Edge V}
    (he : e ∉ F.edges) :
    IsAcyclicEdgeSet (insert e F.edges) ↔
      ¬ F.inSameComponent e.left e.right := by
  have hmk : Edge.mk e.left e.right e.left_ne_right = e := by
    apply Subtype.ext
    rw [Edge.mk_val, e.mk_left_right_eq]
  have hnotmk : Edge.mk e.left e.right e.left_ne_right ∉ F.edges := by
    rw [hmk]
    exact he
  simpa [hmk] using F.acyclic_insert_iff e.left_ne_right hnotmk

theorem isAcyclicEdgeSet_insert_of_mem_activeEdges (F : Forest V)
    {e : Edge V} (he : e ∈ F.activeEdges) :
    IsAcyclicEdgeSet (insert e F.edges) :=
  (F.acyclic_insert_iff_edge (F.not_mem_edges_of_mem_activeEdges he)).mpr
    (F.not_inSameComponent_of_mem_activeEdges he)

/-- Direction in parameter space selected by the active edges of `F`. -/
noncomputable def activeDirection (F : Forest V) : Edge V → ℝ :=
  Finset.sum F.activeEdges edgeBasis

theorem activeDirection_apply_of_mem (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    F.activeDirection e = 1 := by
  rw [activeDirection]
  rw [Finset.sum_apply]
  classical
  calc
    (Finset.sum F.activeEdges fun e' => edgeBasis e' e) =
        edgeBasis e e := by
          exact Finset.sum_eq_single_of_mem e he (fun e' _ hne => by
            exact edgeBasis_of_ne hne.symm)
    _ = 1 := edgeBasis_self e

theorem activeDirection_apply_of_not_mem (F : Forest V) {e : Edge V}
    (he : e ∉ F.activeEdges) :
    F.activeDirection e = 0 := by
  rw [activeDirection]
  rw [Finset.sum_apply]
  classical
  exact Finset.sum_eq_zero fun e' he' => by
    have hne : e ≠ e' := by
      intro h
      exact he (h.symm ▸ he')
    exact edgeBasis_of_ne hne

theorem empty_activeDirection :
    (Forest.empty V).activeDirection = oneConfig := by
  funext e
  rw [(Forest.empty V).activeDirection_apply_of_mem]
  · rfl
  · rw [empty_activeEdges]
    exact Finset.mem_univ e

theorem interpWithFill_of_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = F.pathMin u (F.pathInF e.left e.right he) := by
  rw [interpWithFill, dite_eq_left he]

theorem interpWithFill_of_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    F.interpWithFill u t e = t :=
  F.interpWithFill_of_not_inSameComponent u t
    (F.not_inSameComponent_of_mem_activeEdges he)

theorem deriv_interpWithFill_apply_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) = fun s : ℝ => s := by
    funext s
    exact F.interpWithFill_of_not_inSameComponent u s he
  rw [hfun]
  change deriv (id : ℝ → ℝ) t = 1
  exact deriv_id (𝕜 := ℝ) (x := t)

theorem deriv_interpWithFill_apply_of_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 :=
  F.deriv_interpWithFill_apply_of_not_inSameComponent u
    (F.not_inSameComponent_of_mem_activeEdges he) t

theorem deriv_interpWithFill_apply_of_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : F.inSameComponent e.left e.right) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 0 := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) =
        fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right he) := by
    funext s
    exact F.interpWithFill_of_inSameComponent u s he
  rw [hfun]
  exact deriv_const t _

theorem hasDerivAt_interpWithFill_apply_of_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 1 t := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) = fun s : ℝ => s := by
    funext s
    exact F.interpWithFill_of_mem_activeEdges u s he
  rw [hfun]
  exact hasDerivAt_id t

theorem hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∉ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 0 t := by
  have hsame : F.inSameComponent e.left e.right := by
    by_contra hdiff
    exact he ((F.mem_activeEdges_iff).mpr hdiff)
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) =
        fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right hsame) := by
    funext s
    exact F.interpWithFill_of_inSameComponent u s hsame
  rw [hfun]
  exact hasDerivAt_const t _

theorem hasDerivAt_interpWithFill (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s)
      F.activeDirection t := by
  rw [hasDerivAt_pi]
  intro e
  by_cases he : e ∈ F.activeEdges
  · rw [F.activeDirection_apply_of_mem he]
    exact F.hasDerivAt_interpWithFill_apply_of_mem_activeEdges u he t
  · rw [F.activeDirection_apply_of_not_mem he]
    exact F.hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges u he t

/-- Right-hand side of the differential identity. -/
noncomputable def activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) : ℝ :=
  Finset.sum F.activeEdges fun e => partialDeriv e ρ (F.interpWithFill u t)

theorem activeEdgePartialSum_def (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    F.activeEdgePartialSum u ρ t =
      Finset.sum F.activeEdges
        (fun e => partialDeriv e ρ (F.interpWithFill u t)) :=
  rfl

theorem empty_activeEdgePartialSum
    (u : (Forest.empty V).EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    (Forest.empty V).activeEdgePartialSum u ρ t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by
  rw [activeEdgePartialSum, empty_activeEdges, Forest.empty_interpWithFill u t]

/-- The proposition targeted by the chain-rule argument. -/
def ActiveEdgeDerivIdentityAt (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) : Prop :=
  deriv (fun s : ℝ => ρ (F.interpWithFill u s)) t =
    F.activeEdgePartialSum u ρ t

theorem activeEdgePartialSum_empty_activeEdges (F : Forest V)
    (hF : F.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    F.activeEdgePartialSum u ρ t = 0 := by
  rw [activeEdgePartialSum, hF]
  exact Finset.sum_empty

theorem apply_activeDirection_eq_activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    ρ' F.activeDirection = F.activeEdgePartialSum u ρ t := by
  rw [activeEdgePartialSum]
  calc
    ρ' F.activeDirection =
        Finset.sum F.activeEdges (fun e => ρ' (edgeBasis e)) := by
          rw [activeDirection, map_sum]
    _ = Finset.sum F.activeEdges
        (fun e => partialDeriv e ρ (F.interpWithFill u t)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [partialDeriv_of_hasFDerivAt e hρ]

theorem hasDerivAt_rho_interpWithFill_of_hasFDerivAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t := by
  change HasDerivAt (ρ ∘ fun s : ℝ => F.interpWithFill u s)
    (F.activeEdgePartialSum u ρ t) t
  rw [← F.apply_activeDirection_eq_activeEdgePartialSum u hρ]
  exact hρ.comp_hasDerivAt t (F.hasDerivAt_interpWithFill u t)

theorem hasDerivAt_rho_interpWithFill_of_differentiableAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t :=
  F.hasDerivAt_rho_interpWithFill_of_hasFDerivAt u hρ.hasFDerivAt

theorem differentialIdentityAt_of_hasFDerivAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    F.ActiveEdgeDerivIdentityAt u ρ t := by
  rw [ActiveEdgeDerivIdentityAt, activeEdgePartialSum]
  calc
    deriv (fun s : ℝ => ρ (F.interpWithFill u s)) t =
        ρ' F.activeDirection := by
          exact (hρ.comp_hasDerivAt t (F.hasDerivAt_interpWithFill u t)).deriv
    _ = F.activeEdgePartialSum u ρ t :=
          F.apply_activeDirection_eq_activeEdgePartialSum u hρ

theorem differentialIdentityAt_of_differentiableAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    F.ActiveEdgeDerivIdentityAt u ρ t :=
  F.differentialIdentityAt_of_hasFDerivAt u hρ.hasFDerivAt

theorem differentialIdentityAt_empty
    (u : (Forest.empty V).EdgeParam → ℝ)
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by
  have hρ' :
      DifferentiableAt ℝ ρ ((Forest.empty V).interpWithFill u t) := by
    rw [Forest.empty_interpWithFill u t]
    exact hρ
  have hidentity :=
    (Forest.empty V).differentialIdentityAt_of_differentiableAt u hρ'
  rw [ActiveEdgeDerivIdentityAt] at hidentity
  have hcurve :
      (fun s : ℝ => ρ ((Forest.empty V).interpWithFill u s)) =
        fun s : ℝ => ρ (constantConfig s) := by
    funext s
    rw [Forest.empty_interpWithFill u s]
  rw [hcurve, empty_activeEdgePartialSum u ρ t] at hidentity
  exact hidentity

theorem differentialIdentityAt_emptyParam
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) :=
  differentialIdentityAt_empty emptyParam hρ

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
