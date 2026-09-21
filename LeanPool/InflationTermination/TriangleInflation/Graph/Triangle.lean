/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.RootSink

/-!
# The triangle specialization

Statements split from the original `Statements.lean` skeleton (one file per proving task).
See AUDIT-NOTES for the mathematics.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## The triangle specialization

`triangleGraph = cycle 3` is the scenario of `TriangleInflation`, with vertex `0` the
party `A`, vertex `1` the party `B` and vertex `2` the party `C`. -/

/-! ### The triangle bridge

The named sources of `C₃`, the induced bijections of copied observations, assignments, sets
and copied latent sources, and the transport lemmas used by the four theorems below. The
naming follows the file header of `InflationGraph.Defs`: the source `{0,1}` is the paper's
`X`, the source `{1,2}` is `Y` and the source `{0,2}` is `Z`. -/

universe u

def triEdgeX : triangleGraph.Edge := ⟨s((0 : Fin 3), (1 : Fin 3)), by decide⟩
def triEdgeY : triangleGraph.Edge := ⟨s((1 : Fin 3), (2 : Fin 3)), by decide⟩
def triEdgeZ : triangleGraph.Edge := ⟨s((0 : Fin 3), (2 : Fin 3)), by decide⟩

def triInc0X : (triangleGraph.inc (0 : Fin 3)) := ⟨triEdgeX, by decide⟩
def triInc0Z : (triangleGraph.inc (0 : Fin 3)) := ⟨triEdgeZ, by decide⟩
def triInc1X : (triangleGraph.inc (1 : Fin 3)) := ⟨triEdgeX, by decide⟩
def triInc1Y : (triangleGraph.inc (1 : Fin 3)) := ⟨triEdgeY, by decide⟩
def triInc2Z : (triangleGraph.inc (2 : Fin 3)) := ⟨triEdgeZ, by decide⟩
def triInc2Y : (triangleGraph.inc (2 : Fin 3)) := ⟨triEdgeY, by decide⟩

theorem triInc0_cases :
    ∀ e : triangleGraph.inc (0 : Fin 3), e = triInc0X ∨ e = triInc0Z := by decide
theorem triInc1_cases :
    ∀ e : triangleGraph.inc (1 : Fin 3), e = triInc1X ∨ e = triInc1Y := by decide
theorem triInc2_cases :
    ∀ e : triangleGraph.inc (2 : Fin 3), e = triInc2Z ∨ e = triInc2Y := by decide

def triObs {t : ℕ} (o : GObs triangleGraph t) : Obs t :=
  match o with
  | ⟨⟨0, _⟩, f⟩ => Obs.A (f triInc0X) (f triInc0Z)
  | ⟨⟨1, _⟩, f⟩ => Obs.B (f triInc1X) (f triInc1Y)
  | ⟨⟨2, _⟩, f⟩ => Obs.C (f triInc2Z) (f triInc2Y)
  | ⟨⟨_+3, h⟩, _⟩ => absurd h (by omega)

def triObsInv {t : ℕ} : Obs t → GObs triangleGraph t
  | Obs.A i j => ⟨(0 : Fin 3), fun e => if e = triInc0X then i else j⟩
  | Obs.B i k => ⟨(1 : Fin 3), fun e => if e = triInc1X then i else k⟩
  | Obs.C j k => ⟨(2 : Fin 3), fun e => if e = triInc2Z then j else k⟩

def triEquiv (t : ℕ) : GObs triangleGraph t ≃ Obs t where
  toFun := triObs
  invFun := triObsInv
  left_inv := by
    rintro ⟨v, f⟩
    fin_cases v
    · show (⟨(0 : Fin 3), fun e => if e = triInc0X then f triInc0X else f triInc0Z⟩ :
        GObs triangleGraph t) = ⟨_, f⟩
      congr 1
      funext e
      rcases triInc0_cases e with h | h <;> subst h <;>
        simp [show ¬ (triInc0Z = triInc0X) by decide]
    · show (⟨(1 : Fin 3), fun e => if e = triInc1X then f triInc1X else f triInc1Y⟩ :
        GObs triangleGraph t) = ⟨_, f⟩
      congr 1
      funext e
      rcases triInc1_cases e with h | h <;> subst h <;>
        simp [show ¬ (triInc1Y = triInc1X) by decide]
    · show (⟨(2 : Fin 3), fun e => if e = triInc2Z then f triInc2Z else f triInc2Y⟩ :
        GObs triangleGraph t) = ⟨_, f⟩
      congr 1
      funext e
      rcases triInc2_cases e with h | h <;> subst h <;>
        simp [show ¬ (triInc2Y = triInc2Z) by decide]
  right_inv := by
    rintro (⟨i, j⟩ | ⟨i, k⟩ | ⟨j, k⟩) <;>
      simp [triObsInv, triObs, show ¬ (triInc0Z = triInc0X) by decide,
        show ¬ (triInc1Y = triInc1X) by decide, show ¬ (triInc2Y = triInc2Z) by decide]


/-! ## The permutation correspondence -/


theorem triEdge_cases :
    ∀ e : triangleGraph.Edge, e = triEdgeX ∨ e = triEdgeZ ∨ e = triEdgeY := by decide
theorem triEdge_eq_Y :
    ∀ e : triangleGraph.Edge, ¬ e = triEdgeX → ¬ e = triEdgeZ → e = triEdgeY := by decide

def triPiEdgeEquiv (L : triangleGraph.Edge → Type u) :
    (∀ e, L e) ≃ (L triEdgeX × L triEdgeZ × L triEdgeY) where
  toFun x := (x triEdgeX, x triEdgeZ, x triEdgeY)
  invFun p := fun e =>
    if h : e = triEdgeX then cast (congrArg L h.symm) p.1
    else if h2 : e = triEdgeZ then cast (congrArg L h2.symm) p.2.1
    else cast (congrArg L (triEdge_eq_Y e h h2).symm) p.2.2
  left_inv x := by
    funext e
    rcases triEdge_cases e with h | h | h <;> subst h <;>
      simp [show ¬ (triEdgeZ = triEdgeX) by decide, show ¬ (triEdgeY = triEdgeX) by decide,
        show ¬ (triEdgeY = triEdgeZ) by decide]
  right_inv p := rfl

/-- The three copy-index permutation families of the triangle. -/
def triPermEquiv (t : ℕ) : (triangleGraph.Edge → Equiv.Perm (Fin t)) ≃
    (Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :=
  triPiEdgeEquiv (fun _ => Equiv.Perm (Fin t))

theorem triObs_gPerm {t : ℕ} (π : triangleGraph.Edge → Equiv.Perm (Fin t))
    (o : GObs triangleGraph t) :
    triObs (gPerm π o) = Obs.perm (triPermEquiv t π) (triObs o) := by
  obtain ⟨v, f⟩ := o
  fin_cases v <;> rfl

theorem tri_partyBit {t : ℕ} (o : GObs triangleGraph t) (w : ThreeBit) :
    partyBit (triObs o).party w = threeBitEquiv.symm w o.1 := by
  obtain ⟨v, f⟩ := o
  fin_cases v <;> rfl

/-! ## Transport of witnesses -/

/-- The induced bijection of assignments. -/
def triAssignEquiv (t : ℕ) : GAssign triangleGraph t ≃ Assign t :=
  Equiv.arrowCongr (triEquiv t) (Equiv.refl Bool)

theorem tri_assign_symm_apply {t : ℕ} (ω : Assign t) (o : GObs triangleGraph t) :
    (triAssignEquiv t).symm ω o = ω (triObs o) := rfl

theorem tri_assign_apply {t : ℕ} (ω : GAssign triangleGraph t) (v : Obs t) :
    (triAssignEquiv t) ω v = ω ((triEquiv t).symm v) := rfl

theorem tri_pushforward_equiv {α β γ δ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    [DecidableEq δ] (eab : α ≃ β) (ecd : γ ≃ δ) (w : α → ℝ) (F : α → γ)
    (F' : β → δ)
    (h : ∀ a, F' (eab a) = ecd (F a)) :
    pushforward (fun b => w (eab.symm b)) F' = fun d => pushforward w F (ecd.symm d) := by
  funext d
  simp only [pushforward]
  rw [← Equiv.sum_comp eab (fun b => if F' b = d then w (eab.symm b) else 0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.symm_apply_apply, h a]
  by_cases hh : F a = ecd.symm d
  · rw [if_pos (by rw [hh, Equiv.apply_symm_apply]), if_pos hh]
  · rw [if_neg (fun hc => hh (by rw [← hc, Equiv.symm_apply_apply])), if_neg hh]

theorem tri_sum_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ) :
    ∑ ω : Assign t, Δ ((triAssignEquiv t).symm ω) = ∑ ω : GAssign triangleGraph t, Δ ω :=
  Equiv.sum_comp (triAssignEquiv t).symm Δ

theorem tri_isLaw_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ) :
    IsLaw (fun ω => Δ ((triAssignEquiv t).symm ω)) ↔ IsLaw Δ := by
  unfold IsLaw
  rw [tri_sum_transport]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 ((triAssignEquiv t) a), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => h1 _, h2⟩

theorem tri_assign_symm_relabel {t : ℕ} (π : triangleGraph.Edge → Equiv.Perm (Fin t))
    (ω : Assign t) :
    (triAssignEquiv t).symm (relabel (triPermEquiv t π) ω)
      = gRelabel π ((triAssignEquiv t).symm ω) := by
  funext o
  show ω (Obs.perm (triPermEquiv t π) (triObs o)) = ω (triObs (gPerm π o))
  rw [triObs_gPerm]

theorem tri_sym_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ) :
    SymmetricLaw t (fun ω => Δ ((triAssignEquiv t).symm ω)) ↔ GSymmetric t Δ := by
  constructor
  · intro h π ω
    have hh : Δ ((triAssignEquiv t).symm (relabel (triPermEquiv t π) ((triAssignEquiv t) ω)))
        = Δ ((triAssignEquiv t).symm ((triAssignEquiv t) ω)) :=
      h (triPermEquiv t π) ((triAssignEquiv t) ω)
    rw [tri_assign_symm_relabel, Equiv.symm_apply_apply] at hh
    exact hh
  · intro h π' ω'
    have hh := h ((triPermEquiv t).symm π') ((triAssignEquiv t).symm ω')
    show Δ ((triAssignEquiv t).symm (relabel π' ω')) = Δ ((triAssignEquiv t).symm ω')
    rw [show π' = triPermEquiv t ((triPermEquiv t).symm π') from
      (Equiv.apply_symm_apply _ _).symm, tri_assign_symm_relabel]
    exact hh

/-- The bijection of diagonal reads. -/
def triDiagEquiv (t : ℕ) : (Fin t → (triangleGraph.V → Bool)) ≃ (Fin t → ThreeBit) :=
  Equiv.arrowCongr (Equiv.refl (Fin t)) threeBitEquiv

theorem tri_symm_diag_A {t : ℕ} (r : Fin t) :
    (triEquiv t).symm (Obs.A r r) = copyObs (fun _ => r) (0 : Fin 3) :=
  (triEquiv t).symm_apply_eq.mpr rfl
theorem tri_symm_diag_B {t : ℕ} (r : Fin t) :
    (triEquiv t).symm (Obs.B r r) = copyObs (fun _ => r) (1 : Fin 3) :=
  (triEquiv t).symm_apply_eq.mpr rfl
theorem tri_symm_diag_C {t : ℕ} (r : Fin t) :
    (triEquiv t).symm (Obs.C r r) = copyObs (fun _ => r) (2 : Fin 3) :=
  (triEquiv t).symm_apply_eq.mpr rfl

theorem tri_readDiagonal_map {t : ℕ} (ω : GAssign triangleGraph t) :
    readDiagonal ((triAssignEquiv t) ω) = triDiagEquiv t (readDiag ω) := by
  funext r
  show (ω ((triEquiv t).symm (Obs.A r r)), ω ((triEquiv t).symm (Obs.B r r)),
    ω ((triEquiv t).symm (Obs.C r r))) = _
  rw [tri_symm_diag_A, tri_symm_diag_B, tri_symm_diag_C]
  rfl

theorem tri_diag_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ) (P : ThreeBit → ℝ) :
    pushforward (fun ω => Δ ((triAssignEquiv t).symm ω)) readDiagonal = tensorPow t P ↔
      pushforward Δ readDiag = gTensorPow t (fun w => P (threeBitEquiv w)) := by
  rw [tri_pushforward_equiv (triAssignEquiv t) (triDiagEquiv t) Δ readDiag readDiagonal
    (fun ω => tri_readDiagonal_map ω)]
  constructor
  · intro h
    funext v
    have hv : pushforward Δ readDiag ((triDiagEquiv t).symm ((triDiagEquiv t) v))
        = tensorPow t P ((triDiagEquiv t) v) :=
      congrFun h (triDiagEquiv t v)
    rw [Equiv.symm_apply_apply] at hv
    rw [hv]
    simp only [tensorPow, gTensorPow, triDiagEquiv, Equiv.arrowCongr, Equiv.coe_fn_mk,
      Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq]
    rfl
  · intro h
    funext d
    rw [h]
    simp only [tensorPow, gTensorPow, triDiagEquiv, Equiv.arrowCongr, Equiv.coe_fn_symm_mk,
      Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq]
    rfl

/-! ## Sets of copied observations -/

def triFinsetEquiv (t : ℕ) : Finset (GObs triangleGraph t) ≃ Finset (Obs t) :=
  Equiv.finsetCongr (triEquiv t)

def triSubEquiv {t : ℕ} (S : Finset (GObs triangleGraph t)) :
    ↥S ≃ ↥((triFinsetEquiv t) S) :=
  Equiv.subtypeEquiv (triEquiv t) (fun a => by
    simp [triFinsetEquiv, Equiv.finsetCongr_apply])

def triBoolEquiv {t : ℕ} (S : Finset (GObs triangleGraph t)) :
    (↥S → Bool) ≃ (↥((triFinsetEquiv t) S) → Bool) :=
  Equiv.arrowCongr (triSubEquiv S) (Equiv.refl Bool)

theorem tri_restrictAssign_map {t : ℕ} (S : Finset (GObs triangleGraph t))
    (ω : GAssign triangleGraph t) :
    restrictAssign ((triFinsetEquiv t) S) ((triAssignEquiv t) ω)
      = (triBoolEquiv S) (gRestrict S ω) := rfl

theorem tri_partyRead_map {t : ℕ} (S : Finset (GObs triangleGraph t)) (w : Fin 3 → Bool) :
    partyRead ((triFinsetEquiv t) S) (threeBitEquiv w) = (triBoolEquiv S) (gPartyRead S w) := by
  funext v
  show partyBit v.1.party (threeBitEquiv w) = w ((triEquiv t).symm v.1).1
  have h1 := tri_partyBit ((triEquiv t).symm v.1) (threeBitEquiv w)
  have h2 : triObs ((triEquiv t).symm v.1) = v.1 := (triEquiv t).apply_symm_apply v.1
  rw [h2, Equiv.symm_apply_apply] at h1
  exact h1

theorem tri_copySet_map {t : ℕ} (ι : triangleGraph.Edge → Fin t) :
    (triFinsetEquiv t) (copySet ι) = copiedTriangle (ι triEdgeX) (ι triEdgeZ) (ι triEdgeY) := by
  ext u
  simp only [triFinsetEquiv, Equiv.finsetCongr_apply, Finset.mem_map, copySet, Finset.mem_image,
    Equiv.coe_toEmbedding, copiedTriangle, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨o, ⟨v, -, rfl⟩, rfl⟩
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨copyObs ι (0 : Fin 3), ⟨(0 : Fin 3), Finset.mem_univ _, rfl⟩, rfl⟩
    · exact ⟨copyObs ι (1 : Fin 3), ⟨(1 : Fin 3), Finset.mem_univ _, rfl⟩, rfl⟩
    · exact ⟨copyObs ι (2 : Fin 3), ⟨(2 : Fin 3), Finset.mem_univ _, rfl⟩, rfl⟩

theorem tri_gInjectable_map {t : ℕ} (S : Finset (GObs triangleGraph t)) :
    Injectable ((triFinsetEquiv t) S) ↔ GInjectable S := by
  constructor
  · rintro ⟨i, j, k, hsub⟩
    refine ⟨(triPiEdgeEquiv (fun _ => Fin t)).symm (i, j, k), ?_⟩
    have h1 : (triFinsetEquiv t) (copySet ((triPiEdgeEquiv (fun _ => Fin t)).symm (i, j, k)))
        = copiedTriangle i j k := tri_copySet_map _
    have h2 : (triFinsetEquiv t) S
        ⊆ (triFinsetEquiv t) (copySet ((triPiEdgeEquiv (fun _ => Fin t)).symm (i, j, k))) := by
      rw [h1]; exact hsub
    simpa [triFinsetEquiv, Equiv.finsetCongr_apply, Finset.map_subset_map] using h2
  · rintro ⟨ι, hsub⟩
    refine ⟨ι triEdgeX, ι triEdgeZ, ι triEdgeY, ?_⟩
    rw [← tri_copySet_map ι]
    simpa [triFinsetEquiv, Equiv.finsetCongr_apply, Finset.map_subset_map] using hsub

/-! ## Copied latent sources -/

def triLatentEquiv (t : ℕ) : GLatent triangleGraph t ≃ Latent t where
  toFun p :=
    if p.1 = triEdgeX then Latent.X p.2
    else if p.1 = triEdgeZ then Latent.Z p.2 else Latent.Y p.2
  invFun
    | .X i => (triEdgeX, i)
    | .Z j => (triEdgeZ, j)
    | .Y k => (triEdgeY, k)
  left_inv p := by
    obtain ⟨e, i⟩ := p
    rcases triEdge_cases e with h | h | h <;> subst h <;>
      simp [show ¬ (triEdgeZ = triEdgeX) by decide, show ¬ (triEdgeY = triEdgeX) by decide,
        show ¬ (triEdgeY = triEdgeZ) by decide]
  right_inv p := by
    cases p <;>
      simp [show ¬ (triEdgeZ = triEdgeX) by decide, show ¬ (triEdgeY = triEdgeX) by decide,
        show ¬ (triEdgeY = triEdgeZ) by decide]

theorem tri_gAncestors_map {t : ℕ} (o : GObs triangleGraph t) :
    (gAncestors o).map (triLatentEquiv t).toEmbedding = Obs.ancestors (triObs o) := by
  obtain ⟨v, f⟩ := o
  fin_cases v
  · rw [gAncestors,
      show (Finset.univ : Finset (triangleGraph.inc (0 : Fin 3))) = {triInc0X, triInc0Z} from
      by decide]
    simp only [Finset.image_insert, Finset.image_singleton, Finset.map_insert,
      Finset.map_singleton]
    rfl
  · rw [gAncestors,
      show (Finset.univ : Finset (triangleGraph.inc (1 : Fin 3))) = {triInc1X, triInc1Y} from
      by decide]
    simp only [Finset.image_insert, Finset.image_singleton, Finset.map_insert,
      Finset.map_singleton]
    rfl
  · rw [gAncestors,
      show (Finset.univ : Finset (triangleGraph.inc (2 : Fin 3))) = {triInc2Z, triInc2Y} from
      by decide]
    simp only [Finset.image_insert, Finset.image_singleton, Finset.map_insert,
      Finset.map_singleton]
    rfl

theorem tri_mem_ancestorsOf_map {t : ℕ} (S : Finset (GObs triangleGraph t)) (a : Latent t) :
    a ∈ ancestorsOf ((triFinsetEquiv t) S) ↔ (triLatentEquiv t).symm a ∈ gAncestorsOf S := by
  have key : ∀ o : GObs triangleGraph t,
      (a ∈ Obs.ancestors (triObs o) ↔ (triLatentEquiv t).symm a ∈ gAncestors o) := by
    intro o
    rw [← tri_gAncestors_map o]
    exact Finset.mem_map_equiv
  simp only [ancestorsOf, gAncestorsOf, Finset.mem_biUnion, triFinsetEquiv, Equiv.finsetCongr_apply,
    Finset.mem_map]
  constructor
  · rintro ⟨u, ⟨o, ho, rfl⟩, ha⟩
    exact ⟨o, ho, (key o).1 ha⟩
  · rintro ⟨o, ho, ha⟩
    exact ⟨triObs o, ⟨o, ho, rfl⟩, (key o).2 ha⟩

theorem tri_gAI_map {t : ℕ} (S T : Finset (GObs triangleGraph t)) :
    AncestrallyIndependent ((triFinsetEquiv t) S) ((triFinsetEquiv t) T)
      ↔ GAncestrallyIndependent S T := by
  simp only [AncestrallyIndependent, GAncestrallyIndependent, Finset.disjoint_left,
    tri_mem_ancestorsOf_map]
  constructor
  · intro h x hx hx'
    exact h (a := (triLatentEquiv t) x) (by simpa using hx) (by simpa using hx')
  · intro h a ha ha'
    exact h ha ha'


/-! ## Transport of the injectable and ancestral prescriptions -/

theorem tri_restrict_pushforward {t : ℕ} (S : Finset (GObs triangleGraph t))
    (Δ : GAssign triangleGraph t → ℝ) :
    pushforward (fun ω => Δ ((triAssignEquiv t).symm ω)) (restrictAssign ((triFinsetEquiv t) S))
      = fun d => pushforward Δ (gRestrict S) ((triBoolEquiv S).symm d) :=
  tri_pushforward_equiv (triAssignEquiv t) (triBoolEquiv S) Δ (gRestrict S)
    (restrictAssign ((triFinsetEquiv t) S))
    (fun ω => tri_restrictAssign_map S ω)

theorem tri_partyRead_pushforward {t : ℕ} (S : Finset (GObs triangleGraph t))
    (P : ThreeBit → ℝ) :
    pushforward P (partyRead ((triFinsetEquiv t) S))
      = fun d =>
        pushforward (fun w => P (threeBitEquiv w)) (gPartyRead S) ((triBoolEquiv S).symm d) := by
  have h := tri_pushforward_equiv threeBitEquiv (triBoolEquiv S) (fun w => P (threeBitEquiv w))
    (gPartyRead S) (partyRead ((triFinsetEquiv t) S)) (fun w => tri_partyRead_map S w)
  simpa using h

theorem tri_injMarg_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ)
    (P : ThreeBit → ℝ) :
    InjectableMarginals t (fun ω => Δ ((triAssignEquiv t).symm ω)) P
      ↔ GInjectableMarginals t Δ (fun w => P (threeBitEquiv w)) := by
  constructor
  · intro H S hS
    have h := H ((triFinsetEquiv t) S) ((tri_gInjectable_map S).2 hS)
    rw [tri_restrict_pushforward, tri_partyRead_pushforward] at h
    funext φ
    have h2 := congrFun h ((triBoolEquiv S) φ)
    rw [Equiv.symm_apply_apply] at h2
    exact h2
  · intro H S' hS'
    obtain ⟨S, rfl⟩ : ∃ S, (triFinsetEquiv t) S = S' :=
      ⟨(triFinsetEquiv t).symm S', Equiv.apply_symm_apply _ _⟩
    rw [tri_restrict_pushforward, tri_partyRead_pushforward, H S ((tri_gInjectable_map S).1 hS')]
    rfl

def triPiEquiv {t : ℕ} {n : ℕ} (S : Fin n → Finset (GObs triangleGraph t)) :
    (∀ m, ↥(S m) → Bool) ≃ (∀ m, ↥((triFinsetEquiv t) (S m)) → Bool) :=
  Equiv.piCongrRight (fun m => triBoolEquiv (S m))

theorem tri_ancProd_transport {t : ℕ} (Δ : GAssign triangleGraph t → ℝ)
    (P : ThreeBit → ℝ) :
    AncestralProducts t (fun ω => Δ ((triAssignEquiv t).symm ω)) P
      ↔ GAncestralProducts t Δ (fun w => P (threeBitEquiv w)) := by
  constructor
  · intro H n S hinj hai
    have h := H n (fun m => (triFinsetEquiv t) (S m))
      (fun m => (tri_gInjectable_map (S m)).2 (hinj m))
      (fun m m' hm => (tri_gAI_map (S m) (S m')).2 (hai m m' hm))
    rw [tri_pushforward_equiv (triAssignEquiv t) (triPiEquiv S) Δ (fun ω m => gRestrict (S m) ω)
      (fun ω m => restrictAssign ((triFinsetEquiv t) (S m)) ω)
      (fun ω => by funext m; exact tri_restrictAssign_map (S m) ω)] at h
    funext φ
    have h2 := congrFun h ((triPiEquiv S) φ)
    rw [Equiv.symm_apply_apply] at h2
    rw [h2]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [tri_partyRead_pushforward]
    show pushforward (fun w => P (threeBitEquiv w)) (gPartyRead (S m))
      ((triBoolEquiv (S m)).symm ((triBoolEquiv (S m)) (φ m))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · intro H n S' hinj hai
    obtain ⟨S, rfl⟩ : ∃ S : Fin n → Finset (GObs triangleGraph t),
        (fun m => (triFinsetEquiv t) (S m)) = S' :=
      ⟨fun m => (triFinsetEquiv t).symm (S' m), by funext m; exact Equiv.apply_symm_apply _ _⟩
    have h := H n S (fun m => (tri_gInjectable_map (S m)).1 (hinj m))
      (fun m m' hm => (tri_gAI_map (S m) (S m')).1 (hai m m' hm))
    rw [tri_pushforward_equiv (triAssignEquiv t) (triPiEquiv S) Δ (fun ω m => gRestrict (S m) ω)
      (fun ω m => restrictAssign ((triFinsetEquiv t) (S m)) ω)
      (fun ω => by funext m; exact tri_restrictAssign_map (S m) ω)]
    funext d
    rw [h]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [tri_partyRead_pushforward]
    rfl


theorem triInc0_ne :
    ∀ e : triangleGraph.inc (0 : Fin 3), ¬ e = triInc0X → e = triInc0Z := by decide
theorem triInc1_ne :
    ∀ e : triangleGraph.inc (1 : Fin 3), ¬ e = triInc1X → e = triInc1Y := by decide
theorem triInc2_ne :
    ∀ e : triangleGraph.inc (2 : Fin 3), ¬ e = triInc2Z → e = triInc2Y := by decide


def triInc0Equiv (L : triangleGraph.Edge → Type u) :
    ((e : triangleGraph.inc (0:Fin 3)) → L e.1) ≃ (L triEdgeX × L triEdgeZ) where
  toFun c := (c triInc0X, c triInc0Z)
  invFun p := fun e =>
    if h : e = triInc0X then
      cast (congrArg (fun a : triangleGraph.inc (0 : Fin 3) => L a.1) h.symm) p.1
    else cast (congrArg (fun a : triangleGraph.inc (0:Fin 3) => L a.1) (triInc0_ne e h).symm) p.2
  left_inv c := by
    funext e
    rcases triInc0_cases e with h | h <;> subst h <;>
      simp [show ¬ (triInc0Z = triInc0X) by decide]
  right_inv p := rfl

def triInc1Equiv (L : triangleGraph.Edge → Type u) :
    ((e : triangleGraph.inc (1:Fin 3)) → L e.1) ≃ (L triEdgeX × L triEdgeY) where
  toFun c := (c triInc1X, c triInc1Y)
  invFun p := fun e =>
    if h : e = triInc1X then
      cast (congrArg (fun a : triangleGraph.inc (1 : Fin 3) => L a.1) h.symm) p.1
    else cast (congrArg (fun a : triangleGraph.inc (1:Fin 3) => L a.1) (triInc1_ne e h).symm) p.2
  left_inv c := by
    funext e
    rcases triInc1_cases e with h | h <;> subst h <;>
      simp [show ¬ (triInc1Y = triInc1X) by decide]
  right_inv p := rfl

def triInc2Equiv (L : triangleGraph.Edge → Type u) :
    ((e : triangleGraph.inc (2:Fin 3)) → L e.1) ≃ (L triEdgeZ × L triEdgeY) where
  toFun c := (c triInc2Z, c triInc2Y)
  invFun p := fun e =>
    if h : e = triInc2Z then
      cast (congrArg (fun a : triangleGraph.inc (2 : Fin 3) => L a.1) h.symm) p.1
    else cast (congrArg (fun a : triangleGraph.inc (2:Fin 3) => L a.1) (triInc2_ne e h).symm) p.2
  left_inv c := by
    funext e
    rcases triInc2_cases e with h | h <;> subst h <;>
      simp [show ¬ (triInc2Y = triInc2Z) by decide]
  right_inv p := rfl


theorem tri_prod_edge {M : Type*} [CommMonoid M] (F : triangleGraph.Edge → M) :
    ∏ e, F e = F triEdgeX * F triEdgeZ * F triEdgeY := by
  rw [show (Finset.univ : Finset triangleGraph.Edge) = {triEdgeX, triEdgeZ, triEdgeY} from
    by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    mul_assoc]

theorem tri_sum_edgePi {M : Type*} [AddCommMonoid M] (L : triangleGraph.Edge → Type)
    [∀ e, Fintype (L e)] (F : (∀ e, L e) → M) :
    ∑ x : (∀ e, L e), F x
      = ∑ a : L triEdgeX, ∑ b : L triEdgeZ, ∑ c : L triEdgeY,
          F ((triPiEdgeEquiv L).symm (a, b, c)) := by
  rw [← Equiv.sum_comp (triPiEdgeEquiv L).symm F, Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type]

@[simp] theorem triPiEdge_symm_X (L : triangleGraph.Edge → Type u)
    (p : L triEdgeX × L triEdgeZ × L triEdgeY) :
    (triPiEdgeEquiv L).symm p triEdgeX = p.1 := rfl
@[simp] theorem triPiEdge_symm_Z (L : triangleGraph.Edge → Type u)
    (p : L triEdgeX × L triEdgeZ × L triEdgeY) :
    (triPiEdgeEquiv L).symm p triEdgeZ = p.2.1 := rfl
@[simp] theorem triPiEdge_symm_Y (L : triangleGraph.Edge → Type u)
    (p : L triEdgeX × L triEdgeZ × L triEdgeY) :
    (triPiEdgeEquiv L).symm p triEdgeY = p.2.2 := rfl

@[simp] theorem triInc0_symm_X (L : triangleGraph.Edge → Type u) (p : L triEdgeX × L triEdgeZ) :
    (triInc0Equiv L).symm p triInc0X = p.1 := rfl
@[simp] theorem triInc0_symm_Z (L : triangleGraph.Edge → Type u) (p : L triEdgeX × L triEdgeZ) :
    (triInc0Equiv L).symm p triInc0Z = p.2 := rfl
@[simp] theorem triInc1_symm_X (L : triangleGraph.Edge → Type u) (p : L triEdgeX × L triEdgeY) :
    (triInc1Equiv L).symm p triInc1X = p.1 := rfl
@[simp] theorem triInc1_symm_Y (L : triangleGraph.Edge → Type u) (p : L triEdgeX × L triEdgeY) :
    (triInc1Equiv L).symm p triInc1Y = p.2 := rfl
@[simp] theorem triInc2_symm_Z (L : triangleGraph.Edge → Type u) (p : L triEdgeZ × L triEdgeY) :
    (triInc2Equiv L).symm p triInc2Z = p.1 := rfl
@[simp] theorem triInc2_symm_Y (L : triangleGraph.Edge → Type u) (p : L triEdgeZ × L triEdgeY) :
    (triInc2Equiv L).symm p triInc2Y = p.2 := rfl

theorem tri_tb0 (w : Fin 3 → Bool) : (threeBitEquiv w).1 = w 0 := rfl
theorem tri_tb1 (w : Fin 3 → Bool) : (threeBitEquiv w).2.1 = w 1 := rfl
theorem tri_tb2 (w : Fin 3 → Bool) : (threeBitEquiv w).2.2 = w 2 := rfl

theorem tri_restrict_inc0 (L : triangleGraph.Edge → Type u) (x : ∀ e, L e) :
    (fun e : triangleGraph.inc (0 : Fin 3) => x e.1)
      = (triInc0Equiv L).symm (x triEdgeX, x triEdgeZ) :=
  (triInc0Equiv L).eq_symm_apply.mpr rfl
theorem tri_restrict_inc1 (L : triangleGraph.Edge → Type u) (x : ∀ e, L e) :
    (fun e : triangleGraph.inc (1 : Fin 3) => x e.1)
      = (triInc1Equiv L).symm (x triEdgeX, x triEdgeY) :=
  (triInc1Equiv L).eq_symm_apply.mpr rfl
theorem tri_restrict_inc2 (L : triangleGraph.Edge → Type u) (x : ∀ e, L e) :
    (fun e : triangleGraph.inc (2 : Fin 3) => x e.1)
      = (triInc2Equiv L).symm (x triEdgeZ, x triEdgeY) :=
  (triInc2Equiv L).eq_symm_apply.mpr rfl

theorem tri_prod_vertex {M : Type*} [CommMonoid M] (F : triangleGraph.V → M) :
    ∏ v, F v = F (0 : Fin 3) * F (1 : Fin 3) * F (2 : Fin 3) := Fin.prod_univ_three F


/-- The observed law of a triangle `GModel`, as a triple sum. -/
theorem tri_gmodel_law_eq (M : GModel triangleGraph) (w : Fin 3 → Bool) :
    M.law w = ∑ a : M.L triEdgeX, ∑ b : M.L triEdgeZ, ∑ c : M.L triEdgeY,
      M.μ triEdgeX a * M.μ triEdgeZ b * M.μ triEdgeY c *
        respMass (M.resp (0 : Fin 3) ((triInc0Equiv M.L).symm (a, b))) (w 0) *
        respMass (M.resp (1 : Fin 3) ((triInc1Equiv M.L).symm (a, c))) (w 1) *
        respMass (M.resp (2 : Fin 3) ((triInc2Equiv M.L).symm (b, c))) (w 2) := by
  simp only [GModel.law]
  rw [tri_sum_edgePi]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [tri_prod_edge, tri_prod_vertex, tri_restrict_inc0, tri_restrict_inc1, tri_restrict_inc2]
  simp only [triPiEdge_symm_X, triPiEdge_symm_Z, triPiEdge_symm_Y]
  ring


end TriangleInflation.Graph

namespace TriangleInflation.Graph
open Finset TriangleInflation


theorem tri_tbs0 (w : ThreeBit) : threeBitEquiv.symm w (0 : Fin 3) = w.1 := rfl
theorem tri_tbs1 (w : ThreeBit) : threeBitEquiv.symm w (1 : Fin 3) = w.2.1 := rfl
theorem tri_tbs2 (w : ThreeBit) : threeBitEquiv.symm w (2 : Fin 3) = w.2.2 := rfl

/-- The triangle model of a triangle `GModel`. -/
def triToModel (M : GModel triangleGraph) : TriangleModel where
  X := M.L triEdgeX
  Z := M.L triEdgeZ
  Y := M.L triEdgeY
  fintypeX := M.fintypeL triEdgeX
  fintypeZ := M.fintypeL triEdgeZ
  fintypeY := M.fintypeL triEdgeY
  μX := M.μ triEdgeX
  μZ := M.μ triEdgeZ
  μY := M.μ triEdgeY
  f := fun p => M.resp (0 : Fin 3) ((triInc0Equiv M.L).symm p)
  g := fun p => M.resp (1 : Fin 3) ((triInc1Equiv M.L).symm p)
  h := fun p => M.resp (2 : Fin 3) ((triInc2Equiv M.L).symm p)

/-- The latent alphabets of the triangle `GModel` of a triangle model. -/
def triL (A B C : Type) : triangleGraph.Edge → Type :=
  fun e => if e = triEdgeX then A else if e = triEdgeZ then B else C

/-- The triangle `GModel` of a triangle model. -/
def triOfModel (N : TriangleModel) : GModel triangleGraph where
  L := triL N.X N.Z N.Y
  fintypeL := (triPiEdgeEquiv (fun e => Fintype (triL N.X N.Z N.Y e))).symm
    (N.fintypeX, N.fintypeZ, N.fintypeY)
  μ := (triPiEdgeEquiv (fun e => triL N.X N.Z N.Y e → ℝ)).symm (N.μX, N.μZ, N.μY)
  resp := fun v => match v with
    | ⟨0, _⟩ => fun c => N.f (triInc0Equiv (triL N.X N.Z N.Y) c)
    | ⟨1, _⟩ => fun c => N.g (triInc1Equiv (triL N.X N.Z N.Y) c)
    | ⟨2, _⟩ => fun c => N.h (triInc2Equiv (triL N.X N.Z N.Y) c)
    | ⟨_+3, hh⟩ => absurd hh (by omega)

theorem triToModel_law (M : GModel triangleGraph) (w : ThreeBit) :
    (triToModel M).law w = M.law (threeBitEquiv.symm w) := by
  rw [tri_gmodel_law_eq]
  simp only [TriangleModel.law, triToModel, tri_tbs0, tri_tbs1, tri_tbs2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem triOfModel_law (N : TriangleModel) (w : Fin 3 → Bool) :
    (triOfModel N).law w = N.law (threeBitEquiv w) := by
  rw [tri_gmodel_law_eq]
  simp only [TriangleModel.law, triOfModel, triPiEdge_symm_X, triPiEdge_symm_Z, triPiEdge_symm_Y,
    tri_tb0, tri_tb1, tri_tb2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  show N.μX a * N.μZ b * N.μY c * respMass (N.f (a, b)) (w 0) * respMass (N.g (a, c)) (w 1) *
      respMass (N.h (b, c)) (w 2) = _
  ring




/-- AUDIT-NOTES A1/A2. The copied observations of the order-`t` inflation of `C₃` are in
bijection with `TriangleInflation.Obs t`, by a bijection that intertwines the per-source copy-index
actions and matches the vertex of a copied observation with the party of its image. -/
theorem exists_triObsEquiv (t : ℕ) :
    ∃ (e : GObs triangleGraph t ≃ TriangleInflation.Obs t)
      (σ : (triangleGraph.Edge → Equiv.Perm (Fin t)) ≃
        (Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))),
      (∀ (o : GObs triangleGraph t) (w : ThreeBit),
          TriangleInflation.partyBit (e o).party w = threeBitEquiv.symm w o.1) ∧
        (∀ (π : triangleGraph.Edge → Equiv.Perm (Fin t)) (o : GObs triangleGraph t),
          e (gPerm π o) = TriangleInflation.Obs.perm (σ π) (e o)) :=
  ⟨triEquiv t, triPermEquiv t, tri_partyBit, triObs_gPerm⟩

/-- The pair-source Navascués–Wolfe test on `C₃` is the triangle test of
`TriangleInflation`, under the re-encoding `threeBitEquiv` of three-bit outcomes as
functions on `Fin 3`. -/
theorem gNWFeasible_triangle_iff (t : ℕ) (P : ThreeBit → ℝ) :
    GNWFeasible triangleGraph t (fun w => P (threeBitEquiv w)) ↔ TriangleInflation.NWFeasible t P := by

  constructor
  · rintro ⟨Δ, h1, h2, h3⟩
    exact ⟨fun ω => Δ ((triAssignEquiv t).symm ω), (tri_isLaw_transport Δ).2 h1,
      (tri_sym_transport Δ).2 h2, (tri_diag_transport Δ P).2 h3⟩
  · rintro ⟨Γ, h1, h2, h3⟩
    refine ⟨fun ω => Γ ((triAssignEquiv t) ω), ?_, ?_, ?_⟩
    · exact (tri_isLaw_transport (fun ω => Γ ((triAssignEquiv t) ω))).1 (by simpa using h1)
    · exact (tri_sym_transport (fun ω => Γ ((triAssignEquiv t) ω))).1 (by simpa using h2)
    · exact (tri_diag_transport (fun ω => Γ ((triAssignEquiv t) ω)) P).1 (by simpa using h3)

/-- The pair-source AI test on `C₃` is the triangle AI test. -/
theorem gAIFeasible_triangle_iff (t : ℕ) (P : ThreeBit → ℝ) :
    GAIFeasible triangleGraph t (fun w => P (threeBitEquiv w)) ↔ TriangleInflation.AIFeasible t P := by

  constructor
  · rintro ⟨Δ, h1, h2, h3, h4, h5⟩
    exact ⟨fun ω => Δ ((triAssignEquiv t).symm ω), (tri_isLaw_transport Δ).2 h1,
      (tri_sym_transport Δ).2 h2, (tri_diag_transport Δ P).2 h3,
      (tri_injMarg_transport Δ P).2 h4, (tri_ancProd_transport Δ P).2 h5⟩
  · rintro ⟨Γ, h1, h2, h3, h4, h5⟩
    refine ⟨fun ω => Γ ((triAssignEquiv t) ω), (tri_isLaw_transport _).1 (by simpa using h1),
      (tri_sym_transport _).1 (by simpa using h2), (tri_diag_transport _ P).1 (by simpa using h3),
      (tri_injMarg_transport _ P).1 (by simpa using h4),
      (tri_ancProd_transport _ P).1 (by simpa using h5)⟩

/-- The pair-source compatible set of `C₃` is `TriangleInflation.TriangleCompatible`, both with finite
latent alphabets (AUDIT-NOTES D1). -/
theorem gCompatible_triangle_iff (P : ThreeBit → ℝ) :
    GCompatible triangleGraph (fun w => P (threeBitEquiv w)) ↔
      TriangleInflation.TriangleCompatible P := by

  constructor
  · rintro ⟨M, hV, hlaw⟩
    refine ⟨triToModel M, ⟨hV.1 triEdgeX, hV.1 triEdgeY, hV.1 triEdgeZ, fun p => hV.2 _ _,
      fun p => hV.2 _ _, fun p => hV.2 _ _⟩, ?_⟩
    funext w
    rw [triToModel_law]
    simp only [hlaw, Equiv.apply_symm_apply]
  · rintro ⟨N, hV, hlaw⟩
    refine ⟨triOfModel N, ⟨?_, ?_⟩, ?_⟩
    · intro e
      rcases triEdge_cases e with h | h | h <;> subst h
      · exact hV.1
      · exact hV.2.2.1
      · exact hV.2.1
    · intro v
      fin_cases v
      · exact fun c => hV.2.2.2.1 _
      · exact fun c => hV.2.2.2.2.1 _
      · exact fun c => hV.2.2.2.2.2 _
    · funext w
      exact (triOfModel_law N w).trans (congrFun hlaw _)


end TriangleInflation.Graph
