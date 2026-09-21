/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Triangle

/-!
# Double-star reconstruction (A3)

AUDIT-NOTES A3 and paper Section `sec:doublestar`, in the binary case `T = 2`.

The analytic content of the reconstruction is proved here in full.  Everything rests on one
identity about a Navascués–Wolfe witness at order two, `gTwist_law`: after relabelling the copy
indices of each source by an arbitrary permutation, the `t` rows read on the diagonal are still
`t` independent copies of the target.  From it follow, in order,

* `blockMarg_union_of_sourceDisjoint` — source-disjoint blocks of vertices are independent
  under the target (step (i) of the paper proof, and the pair-source form of
  AUDIT-NOTES A3(i)), and its iterate `blockMarg_biUnion_of_sourceDisjoint`;
* `centreLeaf_mass` — conditioning on the event that each leaf's two copies list the prescribed
  array, the joint law of the two centre observations is the conditional law of the two centres
  given the leaf values (steps (ii)–(iii), the finite-order step);
* `DSStruct.ctrFactor_mul` — the component identity that the reconstruction needs;
* `gCompatible_of_localDecoder` — a model whose responses are deterministic local readings of a
  decoder, packaged so that no dependent latent types appear;
* `DSStruct.gCompatible_of_dsStruct` — the reconstruction (step (iv)).

What is *not* proved here is the purely graph-theoretic step `exists_dsStruct`: that a
double-star forest carries the combinatorial data `DSStruct`.  That step, `exists_dsStruct`, and the theorem `doubleStar_terminates` assembled from it, live in `InflationGraphOpen/DoubleStar.lean`; everything in this file is proved.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## Relabelling the copy indices

The whole finite-order content of the double-star reconstruction is a single identity about a
Navascués–Wolfe witness: after relabelling the copy indices of each source by a permutation
`π`, the `t` diagonal rows are still `t` independent copies of the target.  Sections (i)–(iii)
of the paper proof are all read off from it. -/

/-- Relabelling copied observations composes. -/
theorem gPerm_gPerm (π ρ : Γ.Edge → Equiv.Perm (Fin t)) (o : GObs Γ t) :
    gPerm π (gPerm ρ o) = gPerm (fun e => (ρ e).trans (π e)) o := rfl

/-- Relabelling assignments composes. -/
theorem gRelabel_gRelabel (π ρ : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t) :
    gRelabel π (gRelabel ρ ω) = gRelabel (fun e => (π e).trans (ρ e)) ω := rfl

/-- The identity relabelling. -/
theorem gRelabel_refl (ω : GAssign Γ t) :
    gRelabel (fun _ => Equiv.refl (Fin t)) ω = ω := rfl

/-- Relabelling by `π` is a bijection of assignments, with inverse the relabelling by
`π⁻¹`. -/
def gRelabelEquiv (π : Γ.Edge → Equiv.Perm (Fin t)) : GAssign Γ t ≃ GAssign Γ t where
  toFun := gRelabel π
  invFun := gRelabel (fun e => (π e)⁻¹)
  left_inv ω := by
    rw [gRelabel_gRelabel]
    have h : (fun e => ((π e)⁻¹).trans (π e)) = fun _ : Γ.Edge => Equiv.refl (Fin t) := by
      funext e; ext x; simp
    rw [h, gRelabel_refl]
  right_inv ω := by
    rw [gRelabel_gRelabel]
    have h : (fun e => (π e).trans ((π e)⁻¹)) = fun _ : Γ.Edge => Equiv.refl (Fin t) := by
      funext e; ext x; simp
    rw [h, gRelabel_refl]

@[simp] theorem gRelabelEquiv_apply (π : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t) :
    gRelabelEquiv π ω = gRelabel π ω := rfl

/-- A symmetric witness has the same pushforward along `F` and along `F ∘ gRelabel π`. -/
theorem pushforward_comp_gRelabel {β : Type*} [DecidableEq β] {Δ : GAssign Γ t → ℝ}
    (hsym : GSymmetric t Δ) (π : Γ.Edge → Equiv.Perm (Fin t)) (F : GAssign Γ t → β) :
    pushforward Δ (fun ω => F (gRelabel π ω)) = pushforward Δ F := by
  funext b
  simp only [pushforward]
  rw [← Equiv.sum_comp (gRelabelEquiv π) (fun ω => if F ω = b then Δ ω else 0)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [gRelabelEquiv_apply]
  exact if_congr Iff.rfl (hsym π ω).symm rfl



/-- The rows read by a table after relabelling the copy indices of each source: row `r` reads,
at every vertex, the copy `π_e r` of each incident source `e`.  For `π = 1` these are the `t`
diagonal rows. -/
def gTwist (π : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t) : Fin t → (Γ.V → Bool) :=
  fun r v => ω ⟨v, fun e => π e.1 r⟩

theorem gTwist_eq_readDiag (π : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t) :
    gTwist π ω = readDiag (gRelabel π ω) := rfl

theorem gTwist_refl (ω : GAssign Γ t) :
    gTwist (fun _ => Equiv.refl (Fin t)) ω = readDiag ω := rfl

/-- **The twisted-row law.**  For a symmetric witness whose diagonal law is the `t`-fold
tensor power of the target, the `t` rows read after *any* relabelling of the copy indices are
again `t` independent copies of the target.  This is the only property of the witness that the
double-star reconstruction uses. -/
theorem gTwist_law {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hsym : GSymmetric t Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow t P) (π : Γ.Edge → Equiv.Perm (Fin t)) :
    pushforward Δ (gTwist π) = gTensorPow t P := by
  have : (gTwist π : GAssign Γ t → Fin t → (Γ.V → Bool))
      = fun ω => readDiag (gRelabel π ω) := rfl
  rw [this, pushforward_comp_gRelabel hsym, hdiag]

/-! ## Reading an expectation off a pushforward -/

/-- Expectations only see the pushforward. -/
theorem sum_mul_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Δ : α → ℝ) (F : α → β) (g : β → ℝ) :
    ∑ a : α, g (F a) * Δ a = ∑ b : β, g b * pushforward Δ F b := by
  simp only [pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ (F a)) h

/-- The expectation of a function of the twisted rows. -/
theorem sum_gTwist {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hsym : GSymmetric t Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow t P) (π : Γ.Edge → Equiv.Perm (Fin t))
    (g : (Fin t → (Γ.V → Bool)) → ℝ) :
    ∑ ω : GAssign Γ t, g (gTwist π ω) * Δ ω
      = ∑ u : Fin t → (Γ.V → Bool), g u * gTensorPow t P u := by
  rw [sum_mul_pushforward, gTwist_law hsym hdiag]

/-- Sums over `Fin 2 → α` as double sums. -/
theorem sum_fin_two_pi {α M : Type*} [Fintype α] [AddCommMonoid M] (F : (Fin 2 → α) → M) :
    ∑ u : Fin 2 → α, F u = ∑ a : α, ∑ b : α, F ![a, b] := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv α).symm F, Fintype.sum_prod_type]
  rfl


/-- A vertex whose incident sources are all relabelled so that row `r` becomes row `s` reads,
in the twisted row `r`, exactly what it reads in the diagonal row `s`. -/
theorem gTwist_apply_eq_readDiag {π : Γ.Edge → Equiv.Perm (Fin t)} {ω : GAssign Γ t}
    {r s : Fin t} {v : Γ.V} (h : ∀ e ∈ Γ.inc v, π e r = s) :
    gTwist π ω r v = readDiag ω s v := by
  have hf : (fun e : Γ.inc v => π e.1 r) = (fun _ : Γ.inc v => s) := by
    funext e; exact h e.1 e.2
  show ω ⟨v, fun e => π e.1 r⟩ = ω ⟨v, fun _ => s⟩
  rw [hf]

/-- **The two-row identity at order two.**  Twisting by `π` and reading the two rows gives a
pair of independent draws from the target. -/
theorem twoRow_law {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (π : Γ.Edge → Equiv.Perm (Fin 2))
    (g : (Γ.V → Bool) → (Γ.V → Bool) → ℝ) :
    ∑ ω : GAssign Γ 2, g (gTwist π ω 0) (gTwist π ω 1) * Δ ω
      = ∑ a : Γ.V → Bool, ∑ b : Γ.V → Bool, g a b * (P a * P b) := by
  rw [sum_gTwist hsym hdiag π (fun u => g (u 0) (u 1)), sum_fin_two_pi]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : gTensorPow 2 P ![a, b] = P a * P b := by
    simp [gTensorPow, Fin.prod_univ_two]
  rw [this]
  rfl

/-! ## Marginals of the target on blocks of vertices -/

/-- The marginal of a target on a set of vertices, presented as a function of a full outcome
vector; it depends on `w` only through the coordinates in `A`. -/
def blockMarg (A : Finset Γ.V) (P : GTarget Γ) : GTarget Γ :=
  fun w => ∑ w' : Γ.V → Bool, if ∀ v ∈ A, w' v = w v then P w' else 0

theorem blockMarg_congr (A : Finset Γ.V) (P : GTarget Γ) {w w' : Γ.V → Bool}
    (h : ∀ v ∈ A, w v = w' v) : blockMarg A P w = blockMarg A P w' := by
  simp only [blockMarg]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine if_congr ⟨fun hu v hv => (hu v hv).trans (h v hv), fun hu v hv => (hu v hv).trans
    (h v hv).symm⟩ rfl rfl

@[simp] theorem blockMarg_univ (P : GTarget Γ) : blockMarg Finset.univ P = P := by
  funext w
  simp only [blockMarg, Finset.mem_univ, forall_const]
  rw [Finset.sum_eq_single w]
  · simp
  · intro u _ hu
    have : ¬ (∀ v, u v = w v) := fun h => hu (funext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem blockMarg_empty {P : GTarget Γ} (hP : IsLaw P) (w : Γ.V → Bool) :
    blockMarg ∅ P w = 1 := by
  simp [blockMarg, hP.2]

/-- **Source-disjoint blocks of the target are independent.**  If no source touches both `A`
and `B` then the joint marginal of the target on `A ∪ B` is the product of its marginals on
`A` and on `B`.  This is step (i) of the paper proof, and it needs only order two. -/
theorem blockMarg_union_of_sourceDisjoint {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ}
    (hP : IsLaw P) (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (A B : Finset Γ.V)
    (hAB : Disjoint (A.biUnion Γ.inc) (B.biUnion Γ.inc)) (w : Γ.V → Bool) :
    blockMarg (A ∪ B) P w = blockMarg A P w * blockMarg B P w := by
  classical
  set π : Γ.Edge → Equiv.Perm (Fin 2) :=
    fun e => if e ∈ B.biUnion Γ.inc then Equiv.swap 0 1 else Equiv.refl _ with hπ
  -- the twisted row `0` reads `A` on the diagonal row `0` and `B` on the diagonal row `1`
  have hA : ∀ (ω : GAssign Γ 2) (v : Γ.V), v ∈ A → gTwist π ω 0 v = readDiag ω 0 v := by
    intro ω v hv
    refine gTwist_apply_eq_readDiag fun e he => ?_
    have hmem : e ∈ A.biUnion Γ.inc := Finset.mem_biUnion.2 ⟨v, hv, he⟩
    have hnot : e ∉ B.biUnion Γ.inc := fun hB => (Finset.disjoint_left.1 hAB hmem) hB
    have : π e = Equiv.refl (Fin 2) := by rw [hπ]; exact if_neg hnot
    rw [this]; rfl
  have hB : ∀ (ω : GAssign Γ 2) (v : Γ.V), v ∈ B → gTwist π ω 0 v = readDiag ω 1 v := by
    intro ω v hv
    refine gTwist_apply_eq_readDiag fun e he => ?_
    have hmem : e ∈ B.biUnion Γ.inc := Finset.mem_biUnion.2 ⟨v, hv, he⟩
    have : π e = Equiv.swap 0 1 := by rw [hπ]; exact if_pos hmem
    rw [this]; exact Equiv.swap_apply_left 0 1
  set g : (Γ.V → Bool) → (Γ.V → Bool) → ℝ :=
    fun a _ => if ∀ v ∈ A ∪ B, a v = w v then 1 else 0 with hg
  set g' : (Γ.V → Bool) → (Γ.V → Bool) → ℝ :=
    fun a b => (if ∀ v ∈ A, a v = w v then 1 else 0) * (if ∀ v ∈ B, b v = w v then 1 else 0)
    with hg'
  have hrewrite : ∀ ω : GAssign Γ 2,
      g (gTwist π ω 0) (gTwist π ω 1) = g' (readDiag ω 0) (readDiag ω 1) := by
    intro ω
    have hiff : (∀ v ∈ A ∪ B, gTwist π ω 0 v = w v)
        ↔ ((∀ v ∈ A, readDiag ω 0 v = w v) ∧ (∀ v ∈ B, readDiag ω 1 v = w v)) := by
      constructor
      · intro h
        exact ⟨fun v hv => (hA ω v hv) ▸ h v (Finset.mem_union_left _ hv),
          fun v hv => (hB ω v hv) ▸ h v (Finset.mem_union_right _ hv)⟩
      · rintro ⟨h1, h2⟩ v hv
        rcases Finset.mem_union.1 hv with hv | hv
        · rw [hA ω v hv]; exact h1 v hv
        · rw [hB ω v hv]; exact h2 v hv
    simp only [hg, hg']
    by_cases h : ∀ v ∈ A ∪ B, gTwist π ω 0 v = w v
    · obtain ⟨h1, h2⟩ := hiff.1 h
      rw [if_pos h, if_pos h1, if_pos h2, one_mul]
    · rw [if_neg h]
      have hn := (not_iff_not.2 hiff).1 h
      rw [not_and_or] at hn
      rcases hn with h1 | h1
      · rw [if_neg h1, zero_mul]
      · rw [if_neg h1, mul_zero]
  -- evaluate the same expectation in two ways
  have e1 : ∑ ω : GAssign Γ 2, g (gTwist π ω 0) (gTwist π ω 1) * Δ ω
      = blockMarg (A ∪ B) P w := by
    rw [twoRow_law hsym hdiag π g]
    simp only [hg, blockMarg]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : ∀ v ∈ A ∪ B, a v = w v
    · rw [if_pos h, if_pos h]
      rw [show (∑ b : Γ.V → Bool, (1 : ℝ) * (P a * P b)) = P a * ∑ b : Γ.V → Bool, P b from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring]
      rw [hP.2, mul_one]
    · rw [if_neg h, if_neg h]; simp
  have e2 : ∑ ω : GAssign Γ 2, g' (readDiag ω 0) (readDiag ω 1) * Δ ω
      = blockMarg A P w * blockMarg B P w := by
    have hr : ∀ ω : GAssign Γ 2, readDiag ω = gTwist (fun _ => Equiv.refl (Fin 2)) ω :=
      fun ω => (gTwist_refl ω).symm
    simp only [hr]
    rw [twoRow_law hsym hdiag _ g']
    simp only [hg', blockMarg, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : ∀ v ∈ A, a v = w v
    · by_cases h2 : ∀ v ∈ B, b v = w v
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]; ring
      · rw [if_neg h2, if_neg h2]; ring
    · rw [if_neg h1, if_neg h1]; ring
  calc blockMarg (A ∪ B) P w
      = ∑ ω : GAssign Γ 2, g (gTwist π ω 0) (gTwist π ω 1) * Δ ω := e1.symm
    _ = ∑ ω : GAssign Γ 2, g' (readDiag ω 0) (readDiag ω 1) * Δ ω :=
        Finset.sum_congr rfl fun ω _ => by rw [hrewrite ω]
    _ = blockMarg A P w * blockMarg B P w := e2


/-- The iterated form of `blockMarg_union_of_sourceDisjoint`: pairwise source-disjoint blocks
are mutually independent under the target. -/
theorem blockMarg_biUnion_of_sourceDisjoint {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ}
    (hP : IsLaw P) (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) {ι : Type*} [DecidableEq ι]
    (A : ι → Finset Γ.V)
    (hA : ∀ i j, i ≠ j → Disjoint ((A i).biUnion Γ.inc) ((A j).biUnion Γ.inc)) :
    ∀ (S : Finset ι) (w : Γ.V → Bool),
      blockMarg (S.biUnion A) P w = ∏ i ∈ S, blockMarg (A i) P w := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro w; simp [blockMarg_empty hP]
  | insert i S hi ih =>
      intro w
      rw [Finset.biUnion_insert, Finset.prod_insert hi, ← ih w]
      refine blockMarg_union_of_sourceDisjoint hP hsym hdiag _ _ ?_ w
      rw [Finset.biUnion_biUnion]
      refine Finset.disjoint_biUnion_right _ _ _ |>.2 fun j hj => ?_
      exact hA i j (fun h => hi (h ▸ hj))

/-! ## The conditioning event and the conditional law of the centres -/

/-- The relabelling that moves the copy index `j e` of each source to the index `0` (and
back). -/
def swapTwist (j : Γ.Edge → Fin 2) : Γ.Edge → Equiv.Perm (Fin 2) := fun e => Equiv.swap 0 (j e)

/-- The other of the two copy indices. -/
def flipIdx : Fin 2 → Fin 2 := fun r => if r = 0 then 1 else 0

@[simp] theorem swapTwist_zero (j : Γ.Edge → Fin 2) (e : Γ.Edge) : swapTwist j e 0 = j e :=
  Equiv.swap_apply_left 0 (j e)

@[simp] theorem swapTwist_one (j : Γ.Edge → Fin 2) (e : Γ.Edge) :
    swapTwist j e 1 = flipIdx (j e) := by
  have : ∀ r : Fin 2, Equiv.swap (0 : Fin 2) r 1 = flipIdx r := by decide
  exact this (j e)

theorem forall_fin_two_of_flip (r : Fin 2) (p : Fin 2 → Prop) :
    (∀ m, p m) ↔ (p r ∧ p (flipIdx r)) := by
  revert p
  have : ∀ (r : Fin 2) (p : Fin 2 → Bool), (∀ m, p m = true) ↔ (p r = true ∧ p (flipIdx r) = true) := by
    decide
  intro p
  classical
  have h := this r (fun m => decide (p m))
  simpa using h

/-- **Two-row block masses.**  The probability that the first twisted row matches `w₀` on `A₀`
and the second matches `w₁` on `A₁` is the product of the two target marginals: this is the
one computation the reconstruction performs. -/
theorem twoRow_blockMass {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (π : Γ.Edge → Equiv.Perm (Fin 2))
    (A₀ A₁ : Finset Γ.V) (w₀ w₁ : Γ.V → Bool) :
    ∑ ω : GAssign Γ 2,
        ((if ∀ v ∈ A₀, gTwist π ω 0 v = w₀ v then (1 : ℝ) else 0) *
          (if ∀ v ∈ A₁, gTwist π ω 1 v = w₁ v then (1 : ℝ) else 0)) * Δ ω
      = blockMarg A₀ P w₀ * blockMarg A₁ P w₁ := by
  classical
  rw [twoRow_law hsym hdiag π
    (fun a b => (if ∀ v ∈ A₀, a v = w₀ v then (1 : ℝ) else 0) *
      (if ∀ v ∈ A₁, b v = w₁ v then (1 : ℝ) else 0))]
  simp only [blockMarg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : ∀ v ∈ A₀, a v = w₀ v
  · by_cases h2 : ∀ v ∈ A₁, b v = w₁ v
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]; ring
    · rw [if_neg h2, if_neg h2]; ring
  · rw [if_neg h1, if_neg h1]; ring


theorem ind_mul_ind (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then (1 : ℝ) else 0) * (if q then (1 : ℝ) else 0)) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ind_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℝ) else 0) = if q then 1 else 0 := if_congr h rfl rfl

/-- A leaf reads, in the twisted row `0`, the copy `j` of its unique source. -/
theorem gTwist_leaf_zero {j : Γ.Edge → Fin 2} {ω : GAssign Γ 2} {leafEdge : Γ.V → Γ.Edge}
    {ℓ : Γ.V} (h : Γ.inc ℓ = {leafEdge ℓ}) :
    gTwist (swapTwist j) ω 0 ℓ = readDiag ω (j (leafEdge ℓ)) ℓ := by
  refine gTwist_apply_eq_readDiag fun e he => ?_
  rw [h, Finset.mem_singleton] at he
  rw [he, swapTwist_zero]

/-- A leaf reads, in the twisted row `1`, the other copy of its unique source. -/
theorem gTwist_leaf_one {j : Γ.Edge → Fin 2} {ω : GAssign Γ 2} {leafEdge : Γ.V → Γ.Edge}
    {ℓ : Γ.V} (h : Γ.inc ℓ = {leafEdge ℓ}) :
    gTwist (swapTwist j) ω 1 ℓ = readDiag ω (flipIdx (j (leafEdge ℓ))) ℓ := by
  refine gTwist_apply_eq_readDiag fun e he => ?_
  rw [h, Finset.mem_singleton] at he
  rw [he, swapTwist_one]

/-- **The conditional marginal of the centres** (step (iii) of the paper proof).

Fix a copy index `j e` for every source.  Condition a Navascués–Wolfe witness at order two on
the event `E` that each leaf's two copies read a prescribed array `x`.  Then the joint mass of
`E` together with the event that the vertices of `C` — in practice the two centres — read, on
the copy `j` of each of their leaf sources and the copy `0` of every other source, the values
`w`, is the corresponding two-block marginal of the target.  Dividing by the same identity with
`C = ∅` turns this into the conditional law of the centres given the leaf values, which is the
only fact about the witness the reconstruction uses. -/
theorem centreLeaf_mass {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P)
    (Lf : Finset Γ.V) (leafEdge : Γ.V → Γ.Edge)
    (hinc : ∀ ℓ ∈ Lf, Γ.inc ℓ = {leafEdge ℓ})
    (j : Γ.Edge → Fin 2) (C : Finset Γ.V) (hC : Disjoint C Lf)
    (x : Γ.V → Fin 2 → Bool) (w : Γ.V → Bool) :
    ∑ ω : GAssign Γ 2,
        ((if ∀ v ∈ C, gTwist (swapTwist j) ω 0 v = w v then (1 : ℝ) else 0) *
          (if ∀ ℓ ∈ Lf, ∀ m : Fin 2, readDiag ω m ℓ = x ℓ m then (1 : ℝ) else 0)) * Δ ω
      = blockMarg (C ∪ Lf) P (fun v => if v ∈ Lf then x v (j (leafEdge v)) else w v)
          * blockMarg Lf P (fun v => x v (flipIdx (j (leafEdge v)))) := by
  classical
  set w₀ : Γ.V → Bool := fun v => if v ∈ Lf then x v (j (leafEdge v)) else w v with hw₀
  set w₁ : Γ.V → Bool := fun v => x v (flipIdx (j (leafEdge v))) with hw₁
  rw [← twoRow_blockMass hsym hdiag (swapTwist j) (C ∪ Lf) Lf w₀ w₁]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  rw [ind_mul_ind, ind_mul_ind]
  refine ind_congr ?_
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun ℓ hℓ => ?_⟩
    · rcases Finset.mem_union.1 hv with hv | hv
      · have hvL : v ∉ Lf := Finset.disjoint_left.1 hC hv
        rw [hw₀]; simp only [hvL, if_false]; exact h1 v hv
      · rw [gTwist_leaf_zero (hinc v hv), hw₀]
        simp only [hv, if_true]
        exact h2 v hv _
    · rw [gTwist_leaf_one (hinc ℓ hℓ), hw₁]
      exact h2 ℓ hℓ _
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun ℓ hℓ m => ?_⟩
    · have hvL : v ∉ Lf := Finset.disjoint_left.1 hC hv
      have := h1 v (Finset.mem_union_left _ hv)
      rw [hw₀] at this; simpa [hvL] using this
    · refine (forall_fin_two_of_flip (j (leafEdge ℓ)) (fun m => readDiag ω m ℓ = x ℓ m)).2
        ⟨?_, ?_⟩ m
      · have hz := h1 ℓ (Finset.mem_union_right _ hℓ)
        rw [gTwist_leaf_zero (hinc ℓ hℓ), hw₀] at hz
        simpa [hℓ] using hz
      · have ho := h2 ℓ hℓ
        rw [gTwist_leaf_one (hinc ℓ hℓ), hw₁] at ho
        exact ho


/-! ## Models with deterministic local responses

The reconstruction builds a model whose sources are independent and whose responses are
deterministic functions of the incident sources.  It is convenient to package such a model as a
single *decoder* `dec` from source values to outcomes, subject to the locality requirement that
the outcome at `v` depend only on the sources incident to `v`. -/

/-- `respMass` of a deterministic response is the indicator of the prescribed outcome. -/
theorem respMass_ite (d b : Bool) :
    respMass (if d then 0 else 1) b = if b = d then 1 else 0 := by
  cases d <;> cases b <;> simp [respMass]

/-- **A deterministic local decoder gives a model.**  If every source `e` carries an
independent law `ν e` and the outcome at each vertex `v` is a function `dec` of the source
values that depends only on the sources incident to `v`, then the pushforward of the product
law along `dec` is compatible. -/
theorem gCompatible_of_localDecoder {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    (ν : Γ.Edge → A → ℝ) (hν : ∀ e, IsLaw (ν e)) (dec : (Γ.Edge → A) → (Γ.V → Bool))
    (hloc : ∀ (z z' : Γ.Edge → A) (v : Γ.V), (∀ e ∈ Γ.inc v, z e = z' e) → dec z v = dec z' v)
    (P : GTarget Γ)
    (hP : pushforward (fun z : Γ.Edge → A => ∏ e : Γ.Edge, ν e (z e)) dec = P) :
    GCompatible Γ P := by
  classical
  refine ⟨⟨fun _ => A, fun _ => inferInstance, ν,
    fun v c => if dec (fun e => if h : e ∈ Γ.inc v then c ⟨e, h⟩ else default) v then 0 else 1⟩,
    ⟨hν, fun v c => ?_⟩, ?_⟩
  · by_cases h : dec (fun e => if h : e ∈ Γ.inc v then c ⟨e, h⟩ else default) v <;> simp [h]
  · funext w
    show (∑ z : Γ.Edge → A, (∏ e : Γ.Edge, ν e (z e)) *
      ∏ v : Γ.V, respMass
        (if dec (fun e => if h : e ∈ Γ.inc v then (fun e' : Γ.inc v => z e'.1) ⟨e, h⟩
          else default) v then 0 else 1) (w v)) = P w
    rw [← hP]
    simp only [pushforward]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hdec : ∀ v : Γ.V,
        dec (fun e => if h : e ∈ Γ.inc v then (fun e' : Γ.inc v => z e'.1) ⟨e, h⟩ else default) v
          = dec z v := by
      intro v
      refine hloc _ _ v fun e he => ?_
      simp [he]
    simp only [hdec, respMass_ite]
    have hb : (∏ v : Γ.V, if w v = dec z v then (1 : ℝ) else 0) = if dec z = w then 1 else 0 := by
      have hiff : (∀ v ∈ (Finset.univ : Finset Γ.V), w v = dec z v) ↔ dec z = w := by
        constructor
        · intro h; funext v; exact (h v (Finset.mem_univ v)).symm
        · intro h v _; rw [h]
      rw [Finset.prod_boole]
      simp only [hiff]
    rw [hb]
    by_cases h : dec z = w
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]


/-- A sum over a function space of a product of per-coordinate weights is the product of the
coordinate sums. -/
theorem sum_prod_pi {ι A R : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [CommRing R]
    (g : ι → A → R) : ∑ z : ι → A, ∏ i : ι, g i (z i) = ∏ i : ι, ∑ a : A, g i a := by
  rw [← Finset.sum_prod_piFinset]
  refine Finset.sum_congr ?_ fun z _ => rfl
  simp [Fintype.piFinset_univ]

/-! ## Reconstruction: the source-disjoint fibre case

A double-star forest whose components are single sources — a perfect matching — is already
covered by the machinery above: the source of a component carries the outcomes of its two
endpoints.  This is the degenerate case `p = q = 0` of the paper's Theorem, and it is recorded
here because it exercises the whole pipeline (twisted rows, block independence, deterministic
local decoder) end to end. -/

/-- **Reconstruction when the vertex fibres of the sources are source-disjoint.**  Choose for
each vertex `v` an incident source `edgeAt v`.  If the vertex sets `{v | edgeAt v = e}` are
pairwise source-disjoint, every target passing the order-two Navascués–Wolfe test is
compatible: the source `e` carries the joint outcome of the vertices that read it, which by
source-disjoint block independence is exactly the right marginal. -/
theorem gCompatible_of_fibre_sourceDisjoint {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ}
    (hP : IsLaw P) (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P)
    (edgeAt : Γ.V → Γ.Edge) (hmem : ∀ v, edgeAt v ∈ Γ.inc v)
    (hdisj : ∀ e e' : Γ.Edge, e ≠ e' →
      Disjoint ((Finset.univ.filter fun v => edgeAt v = e).biUnion Γ.inc)
        ((Finset.univ.filter fun v => edgeAt v = e').biUnion Γ.inc)) :
    GCompatible Γ P := by
  classical
  refine gCompatible_of_localDecoder (A := Γ.V → Bool) (fun _ => P) (fun _ => hP)
    (fun z v => z (edgeAt v) v) (fun z z' v h => by rw [h (edgeAt v) (hmem v)]) P ?_
  funext w
  simp only [pushforward]
  have key : ∀ z : Γ.Edge → (Γ.V → Bool),
      (if (fun v => z (edgeAt v) v) = w then (∏ e : Γ.Edge, P (z e)) else 0)
        = ∏ e : Γ.Edge, (P (z e) *
            ∏ v ∈ Finset.univ.filter (fun v => edgeAt v = e),
              (if z e v = w v then (1 : ℝ) else 0)) := by
    intro z
    rw [Finset.prod_mul_distrib]
    have h2 : (∏ e : Γ.Edge, ∏ v ∈ Finset.univ.filter (fun v => edgeAt v = e),
          (if z e v = w v then (1 : ℝ) else 0))
        = ∏ v : Γ.V, (if z (edgeAt v) v = w v then (1 : ℝ) else 0) := by
      rw [← Finset.prod_fiberwise Finset.univ edgeAt
        (fun v => if z (edgeAt v) v = w v then (1 : ℝ) else 0)]
      refine Finset.prod_congr rfl fun e _ => Finset.prod_congr rfl fun v hv => ?_
      rw [(Finset.mem_filter.1 hv).2]
    rw [h2, Finset.prod_boole]
    have hiff : (∀ v ∈ (Finset.univ : Finset Γ.V), z (edgeAt v) v = w v)
        ↔ (fun v => z (edgeAt v) v) = w := by
      constructor
      · intro h; funext v; exact h v (Finset.mem_univ v)
      · intro h v _; exact congrFun h v
    simp only [hiff]
    by_cases h : (fun v => z (edgeAt v) v) = w
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  simp only [key]
  rw [sum_prod_pi (fun e a => P a *
    ∏ v ∈ Finset.univ.filter (fun v => edgeAt v = e), (if a v = w v then (1 : ℝ) else 0))]
  have hfac : ∀ e : Γ.Edge,
      (∑ a : Γ.V → Bool, P a *
        ∏ v ∈ Finset.univ.filter (fun v => edgeAt v = e), (if a v = w v then (1 : ℝ) else 0))
        = blockMarg (Finset.univ.filter fun v => edgeAt v = e) P w := by
    intro e
    simp only [blockMarg, Finset.prod_boole]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : ∀ v ∈ Finset.univ.filter (fun v => edgeAt v = e), a v = w v
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  simp only [hfac]
  have hcov : (Finset.univ : Finset Γ.Edge).biUnion
      (fun e => Finset.univ.filter fun v => edgeAt v = e) = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, iff_true]
    exact ⟨edgeAt v, rfl⟩
  rw [← blockMarg_biUnion_of_sourceDisjoint hP hsym hdiag _
    (fun e e' hee => hdisj e e' hee) Finset.univ w, hcov, blockMarg_univ]


/-! ## The combinatorics of a double-star forest -/

/-- The combinatorial data of a double-star forest.  Every vertex is a *leaf* or a *centre*;
a leaf carries a single source joining it to its centre; a centre has a partner centre, and the
two share the centre source of their component.  `root v` names the centre source of the
component of `v`, so the components are the fibres of `root`. -/
structure DSStruct (Γ : PairGraph) where
  /-- Is the vertex a leaf? -/
  leaf : Γ.V → Bool
  /-- For a leaf, its unique source; for a centre, the centre source of its component. -/
  edgeAt : Γ.V → Γ.Edge
  /-- For a leaf, its centre; for a centre, its partner. -/
  mate : Γ.V → Γ.V
  /-- The centre source of the component of a vertex. -/
  root : Γ.V → Γ.Edge
  /-- A vertex whose `edgeAt` is the given source. -/
  vtx : Γ.Edge → Γ.V
  vtx_edgeAt : ∀ e, edgeAt (vtx e) = e
  edgeAt_inc : ∀ v, edgeAt v ∈ Γ.inc v
  edgeAt_inc_mate : ∀ v, edgeAt v ∈ Γ.inc (mate v)
  /-- The source `edgeAt v` touches only `v` and `mate v`. -/
  edgeAt_mem : ∀ v u : Γ.V, edgeAt v ∈ Γ.inc u → u = v ∨ u = mate v
  mate_not_leaf : ∀ v, leaf (mate v) = false
  mate_ne : ∀ v, mate v ≠ v
  leaf_inc : ∀ v, leaf v = true → Γ.inc v = {edgeAt v}
  fib_leaf : ∀ v, leaf v = true →
      (Finset.univ.filter fun u => edgeAt u = edgeAt v) = {v}
  fib_ctr : ∀ v, leaf v = false →
      (Finset.univ.filter fun u => edgeAt u = edgeAt v) = {v, mate v}
  root_leaf : ∀ v, leaf v = true → root v = edgeAt (mate v)
  root_ctr : ∀ v, leaf v = false → root v = edgeAt v
  comp_sourceDisjoint : ∀ y y' : Γ.Edge, y ≠ y' →
      Disjoint ((Finset.univ.filter fun v => root v = y).biUnion Γ.inc)
        ((Finset.univ.filter fun v => root v = y').biUnion Γ.inc)

/-- The latent alphabet used by the reconstruction: a response table together with a bit.  The
same type serves every source; the source law is what distinguishes leaf sources, which carry
the bit, from centre sources, which carry the table. -/
abbrev DSLat (Γ : PairGraph) : Type := ((Γ.V → Bool) → (Γ.V → Bool)) × Bool

/-- The table that unsupported arguments are sent to. -/
def dfltTable (Γ : PairGraph) : (Γ.V → Bool) → (Γ.V → Bool) := fun _ _ => false

noncomputable section

/-- The one-vertex marginal of the target. -/
def vMarg (P : GTarget Γ) (v : Γ.V) (β : Bool) : ℝ := blockMarg {v} P (Function.const Γ.V β)

/-- The array of two symbols listed at each leaf: both symbols when both are supported, and
otherwise the supported symbol twice. -/
def xarr (P : GTarget Γ) (ℓ : Γ.V) (m : Fin 2) : Bool :=
  if vMarg P ℓ false = 0 then true
  else if vMarg P ℓ true = 0 then false else decide (m = 1)

/-- A copy index at which the leaf `ℓ` reads the symbol `β`. -/
def pick (P : GTarget Γ) (ℓ : Γ.V) (β : Bool) : Fin 2 := if xarr P ℓ 0 = β then 0 else 1

namespace DSStruct

variable (D : DSStruct Γ)

/-- The leaves of the component whose centre source is `y`. -/
def leaves (y : Γ.Edge) : Finset Γ.V :=
  Finset.univ.filter fun v => D.leaf v = true ∧ D.root v = y

/-- All the leaves. -/
def allLeaves : Finset Γ.V := Finset.univ.filter fun v => D.leaf v = true

/-- The vertices of the component whose centre source is `y`. -/
def comp (y : Γ.Edge) : Finset Γ.V := Finset.univ.filter fun v => D.root v = y

/-- The two centres of the component whose centre source is `y`. -/
def ctrs (y : Γ.Edge) : Finset Γ.V := {D.vtx y, D.mate (D.vtx y)}

/-- The leaf values that a vertex sees among its sources. -/
def locVec (z : Γ.Edge → DSLat Γ) (v : Γ.V) : Γ.V → Bool :=
  fun u => if D.leaf u = true ∧ D.mate u = v then (z (D.edgeAt u)).2 else false

/-- The same vector read off an outcome vector. -/
def locOut (w : Γ.V → Bool) (v : Γ.V) : Γ.V → Bool :=
  fun u => if D.leaf u = true ∧ D.mate u = v then w u else false

/-- The decoder of the reconstructed model: a leaf copies its source, a centre evaluates its
half of the centre table on the values of its leaf sources. -/
def dec (z : Γ.Edge → DSLat Γ) : Γ.V → Bool :=
  fun v => if D.leaf v = true then (z (D.edgeAt v)).2
    else (z (D.edgeAt v)).1 (D.locVec z v) v

/-- The relabelling index attached to each source by a vector of leaf values. -/
def jOf (P : GTarget Γ) (ξ : Γ.V → Bool) (e : Γ.Edge) : Fin 2 :=
  if D.leaf (D.vtx e) = true then pick P (D.vtx e) (ξ (D.vtx e)) else 0

/-- The response table read off a witness table: on the leaf values `ξ` it returns the
observations that read, at each leaf source, the copy showing `ξ`. -/
def tableOf (P : GTarget Γ) (ω : GAssign Γ 2) : (Γ.V → Bool) → (Γ.V → Bool) :=
  fun ξ => gTwist (swapTwist (D.jOf P ξ)) ω 0

/-- The conditioning event of the component with centre source `y`: every leaf of that
component has its two copies reading the prescribed array. -/
def evt (P : GTarget Γ) (y : Γ.Edge) (ω : GAssign Γ 2) : Prop :=
  ∀ ℓ ∈ D.leaves y, ∀ m : Fin 2, readDiag ω m ℓ = xarr P ℓ m

instance (P : GTarget Γ) (y : Γ.Edge) (ω : GAssign Γ 2) : Decidable (D.evt P y ω) := by
  unfold DSStruct.evt; infer_instance

/-- The mass of the conditioning event. -/
def evtMass (P : GTarget Γ) (Δ : GAssign Γ 2 → ℝ) (y : Γ.Edge) : ℝ :=
  ∑ ω : GAssign Γ 2, (if D.evt P y ω then (1 : ℝ) else 0) * Δ ω

/-- The law of the pair of response tables, read off the witness conditioned on `evt`. -/
def tabLaw (P : GTarget Γ) (Δ : GAssign Γ 2 → ℝ) (y : Γ.Edge)
    (T : (Γ.V → Bool) → (Γ.V → Bool)) : ℝ :=
  (∑ ω : GAssign Γ 2,
      ((if D.evt P y ω then (1 : ℝ) else 0) * (if D.tableOf P ω = T then (1 : ℝ) else 0)) * Δ ω)
    / D.evtMass P Δ y

/-- The source law of the reconstructed model. -/
def lat (P : GTarget Γ) (Δ : GAssign Γ 2 → ℝ) (e : Γ.Edge) : DSLat Γ → ℝ :=
  fun a => if D.leaf (D.vtx e) = true then (if a.1 = dfltTable Γ then vMarg P (D.vtx e) a.2
    else 0) else (if a.2 = false then D.tabLaw P Δ e a.1 else 0)

end DSStruct

end


/-! ### One-vertex marginals and the listed arrays -/

noncomputable section

theorem vMarg_eq (P : GTarget Γ) (v : Γ.V) (β : Bool) :
    vMarg P v β = ∑ u : Γ.V → Bool, if u v = β then P u else 0 := by
  unfold vMarg blockMarg
  refine Finset.sum_congr rfl fun u _ => ?_
  exact if_congr (by simp [Function.const]) rfl rfl

theorem blockMarg_singleton (P : GTarget Γ) (v : Γ.V) (w : Γ.V → Bool) :
    blockMarg {v} P w = vMarg P v (w v) :=
  blockMarg_congr _ _ (by simp [Function.const])

theorem vMarg_nonneg {P : GTarget Γ} (hP : IsLaw P) (v : Γ.V) (β : Bool) :
    0 ≤ vMarg P v β := by
  rw [vMarg_eq]
  refine Finset.sum_nonneg fun u _ => ?_
  by_cases h : u v = β
  · rw [if_pos h]; exact hP.1 u
  · rw [if_neg h]

theorem vMarg_sum {P : GTarget Γ} (hP : IsLaw P) (v : Γ.V) :
    vMarg P v false + vMarg P v true = 1 := by
  rw [vMarg_eq, vMarg_eq, ← Finset.sum_add_distrib, ← hP.2]
  refine Finset.sum_congr rfl fun u _ => ?_
  cases u v <;> simp

theorem vMarg_xarr_pos {P : GTarget Γ} (hP : IsLaw P) (ℓ : Γ.V) (m : Fin 2) :
    0 < vMarg P ℓ (xarr P ℓ m) := by
  have h0 := vMarg_nonneg hP ℓ false
  have h1 := vMarg_nonneg hP ℓ true
  have hs := vMarg_sum hP ℓ
  unfold xarr
  by_cases hf : vMarg P ℓ false = 0
  · rw [if_pos hf]; linarith
  · rw [if_neg hf]
    by_cases ht : vMarg P ℓ true = 0
    · rw [if_pos ht]; rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · exact absurd h.symm hf
    · rw [if_neg ht]
      cases hm : (decide (m = 1)) with
      | false => exact lt_of_le_of_ne h0 (Ne.symm hf)
      | true => exact lt_of_le_of_ne h1 (Ne.symm ht)

theorem xarr_pick {P : GTarget Γ} (ℓ : Γ.V) (β : Bool) (h : 0 < vMarg P ℓ β) :
    xarr P ℓ (pick P ℓ β) = β := by
  unfold pick
  by_cases hb : xarr P ℓ 0 = β
  · rw [if_pos hb]; exact hb
  · rw [if_neg hb]
    unfold xarr at hb ⊢
    by_cases hf : vMarg P ℓ false = 0
    · rw [if_pos hf] at hb ⊢
      rcases Bool.eq_false_or_eq_true β with hβ | hβ
      · exact absurd hβ.symm hb
      · subst hβ; rw [hf] at h; exact absurd h (lt_irrefl 0)
    · rw [if_neg hf] at hb ⊢
      by_cases ht : vMarg P ℓ true = 0
      · rw [if_pos ht] at hb ⊢
        rcases Bool.eq_false_or_eq_true β with hβ | hβ
        · subst hβ; rw [ht] at h; exact absurd h (lt_irrefl 0)
        · exact absurd hβ.symm hb
      · rw [if_neg ht] at hb ⊢
        have h0 : decide ((0 : Fin 2) = 1) = false := by decide
        have h1 : decide ((1 : Fin 2) = 1) = true := by decide
        rw [h0] at hb
        rw [h1]
        rcases Bool.eq_false_or_eq_true β with hβ | hβ
        · exact hβ.symm
        · exact absurd hβ.symm hb

end


theorem blockMarg_nonneg {P : GTarget Γ} (hP : IsLaw P) (A : Finset Γ.V) (w : Γ.V → Bool) :
    0 ≤ blockMarg A P w := by
  unfold blockMarg
  refine Finset.sum_nonneg fun u _ => ?_
  by_cases h : ∀ v ∈ A, u v = w v
  · rw [if_pos h]; exact hP.1 u
  · rw [if_neg h]

theorem blockMarg_le {P : GTarget Γ} (hP : IsLaw P) {A B : Finset Γ.V} (h : A ⊆ B)
    (w : Γ.V → Bool) : blockMarg B P w ≤ blockMarg A P w := by
  unfold blockMarg
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hb : ∀ v ∈ B, u v = w v
  · rw [if_pos hb, if_pos (fun v hv => hb v (h hv))]
  · rw [if_neg hb]
    by_cases ha : ∀ v ∈ A, u v = w v
    · rw [if_pos ha]; exact hP.1 u
    · rw [if_neg ha]

namespace DSStruct

variable (D : DSStruct Γ)

theorem edgeAt_inj_leaves {ℓ ℓ' : Γ.V} (h : D.leaf ℓ = true)
    (he : D.edgeAt ℓ' = D.edgeAt ℓ) : ℓ' = ℓ := by
  have hm : ℓ' ∈ (Finset.univ.filter fun u => D.edgeAt u = D.edgeAt ℓ) := by
    simp [he]
  rw [D.fib_leaf ℓ h, Finset.mem_singleton] at hm
  exact hm

theorem leaf_inc_disjoint {ℓ ℓ' : Γ.V} (h : D.leaf ℓ = true) (h' : D.leaf ℓ' = true)
    (hne : ℓ ≠ ℓ') : Disjoint (Γ.inc ℓ) (Γ.inc ℓ') := by
  rw [D.leaf_inc ℓ h, D.leaf_inc ℓ' h', Finset.disjoint_singleton]
  exact fun he => hne (D.edgeAt_inj_leaves h' he)

/-- Any set of leaves is a union of source-disjoint singletons, so its marginal is the product
of the one-vertex marginals. -/
theorem blockMarg_leaves {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hP : IsLaw P)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P)
    (S : Finset Γ.V) (hS : ∀ v ∈ S, D.leaf v = true) (w : Γ.V → Bool) :
    blockMarg S P w = ∏ ℓ ∈ S, vMarg P ℓ (w ℓ) := by
  classical
  set A : Γ.V → Finset Γ.V := fun v => if D.leaf v = true then {v} else ∅ with hA
  have hdisj : ∀ i j : Γ.V, i ≠ j → Disjoint ((A i).biUnion Γ.inc) ((A j).biUnion Γ.inc) := by
    intro i j hij
    by_cases hi : D.leaf i = true
    · by_cases hj : D.leaf j = true
      · simp only [hA, if_pos hi, if_pos hj, Finset.singleton_biUnion]
        exact D.leaf_inc_disjoint hi hj hij
      · simp [hA, hj]
    · simp [hA, hi]
  have hcov : S.biUnion A = S := by
    ext v
    simp only [Finset.mem_biUnion, hA]
    constructor
    · rintro ⟨u, hu, hv⟩
      by_cases h : D.leaf u = true
      · rw [if_pos h, Finset.mem_singleton] at hv; exact hv ▸ hu
      · rw [if_neg h] at hv; simp at hv
    · intro hv
      exact ⟨v, hv, by rw [if_pos (hS v hv)]; exact Finset.mem_singleton_self v⟩
  have hkey := blockMarg_biUnion_of_sourceDisjoint hP hsym hdiag A hdisj S w
  rw [hcov] at hkey
  rw [hkey]
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  simp only [hA, if_pos (hS ℓ hℓ)]
  exact blockMarg_singleton P ℓ w

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

theorem vtx_of_leaf {v : Γ.V} (h : D.leaf v = true) : D.vtx (D.edgeAt v) = v :=
  D.edgeAt_inj_leaves h (D.vtx_edgeAt (D.edgeAt v))

@[simp] theorem mem_leaves {v : Γ.V} {y : Γ.Edge} :
    v ∈ D.leaves y ↔ D.leaf v = true ∧ D.root v = y := by simp [DSStruct.leaves]

@[simp] theorem mem_comp {v : Γ.V} {y : Γ.Edge} : v ∈ D.comp y ↔ D.root v = y := by
  simp [DSStruct.comp]

theorem leaf_of_mem_leaves {v : Γ.V} {y : Γ.Edge} (h : v ∈ D.leaves y) : D.leaf v = true :=
  (D.mem_leaves.1 h).1

theorem ctrs_not_leaf {y : Γ.Edge} (hy : D.leaf (D.vtx y) = false) :
    ∀ v ∈ D.ctrs y, D.leaf v = false := by
  intro v hv
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]; exact hy
  · rw [Finset.mem_singleton.1 h]; exact D.mate_not_leaf _

theorem ctrs_disjoint_leaves {y : Γ.Edge} (hy : D.leaf (D.vtx y) = false) :
    Disjoint (D.ctrs y) (D.leaves y) := by
  refine Finset.disjoint_left.2 fun v hv hv' => ?_
  have := (D.mem_leaves.1 hv').1
  rw [D.ctrs_not_leaf hy v hv] at this
  simp at this

theorem comp_eq {y : Γ.Edge} (hy : D.leaf (D.vtx y) = false) :
    D.comp y = D.ctrs y ∪ D.leaves y := by
  have hfib : (Finset.univ.filter fun u => D.edgeAt u = y) = D.ctrs y := by
    have := D.fib_ctr (D.vtx y) hy
    rwa [D.vtx_edgeAt y] at this
  ext v
  simp only [D.mem_comp, Finset.mem_union, D.mem_leaves]
  constructor
  · intro hv
    by_cases h : D.leaf v = true
    · exact Or.inr ⟨h, hv⟩
    · refine Or.inl ?_
      have : D.edgeAt v = y := by rw [← D.root_ctr v (by simpa using h)]; exact hv
      have hm : v ∈ (Finset.univ.filter fun u => D.edgeAt u = y) := by simp [this]
      rwa [hfib] at hm
  · rintro (hv | ⟨h1, h2⟩)
    · have hl : D.leaf v = false := D.ctrs_not_leaf hy v hv
      rw [D.root_ctr v hl]
      have hm : v ∈ (Finset.univ.filter fun u => D.edgeAt u = y) := by rwa [hfib]
      simpa using hm
    · exact h2

theorem jOf_edgeAt {P : GTarget Γ} {ℓ : Γ.V} (h : D.leaf ℓ = true) (ξ : Γ.V → Bool) :
    D.jOf P ξ (D.edgeAt ℓ) = pick P ℓ (ξ ℓ) := by
  unfold DSStruct.jOf
  rw [D.vtx_of_leaf h, if_pos h]

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

/-- The mass of the conditioning event, evaluated by the conditional-marginal identity. -/
theorem evtMass_eq {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (y : Γ.Edge) (j : Γ.Edge → Fin 2)
    (w : Γ.V → Bool) :
    D.evtMass P Δ y
      = blockMarg (D.leaves y) P
          (fun v => if v ∈ D.leaves y then xarr P v (j (D.edgeAt v)) else w v)
        * blockMarg (D.leaves y) P (fun v => xarr P v (flipIdx (j (D.edgeAt v)))) := by
  have h := centreLeaf_mass hsym hdiag (D.leaves y) D.edgeAt
    (fun ℓ hℓ => D.leaf_inc ℓ (D.leaf_of_mem_leaves hℓ)) j ∅ (by simp) (xarr P) w
  rw [Finset.empty_union] at h
  rw [← h]
  unfold DSStruct.evtMass
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [if_pos (show ∀ v ∈ (∅ : Finset Γ.V), gTwist (swapTwist j) ω 0 v = w v by simp), one_mul]
  exact congrArg (· * Δ ω) (ind_congr Iff.rfl)

theorem evtMass_pos {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hP : IsLaw P)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (y : Γ.Edge) :
    0 < D.evtMass P Δ y := by
  rw [D.evtMass_eq hsym hdiag y (fun _ => 0) (fun _ => false)]
  have hl : ∀ v ∈ D.leaves y, D.leaf v = true := fun v hv => D.leaf_of_mem_leaves hv
  rw [D.blockMarg_leaves hP hsym hdiag _ hl, D.blockMarg_leaves hP hsym hdiag _ hl]
  refine mul_pos (Finset.prod_pos fun ℓ hℓ => ?_) (Finset.prod_pos fun ℓ hℓ => ?_)
  · rw [if_pos hℓ]
    exact vMarg_xarr_pos hP ℓ _
  · exact vMarg_xarr_pos hP ℓ _

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

theorem tabLaw_isLaw {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hP : IsLaw P) (hΔ : IsLaw Δ)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (y : Γ.Edge) :
    IsLaw (D.tabLaw P Δ y) := by
  have hpos := D.evtMass_pos hP hsym hdiag y
  constructor
  · intro T
    refine div_nonneg (Finset.sum_nonneg fun ω _ => ?_) hpos.le
    have h1 : (0 : ℝ) ≤ (if D.evt P y ω then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if D.tableOf P ω = T then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg h1 h2) (hΔ.1 ω)
  · unfold DSStruct.tabLaw
    rw [← Finset.sum_div]
    have hnum : (∑ T : (Γ.V → Bool) → (Γ.V → Bool), ∑ ω : GAssign Γ 2,
        ((if D.evt P y ω then (1 : ℝ) else 0) * (if D.tableOf P ω = T then (1 : ℝ) else 0))
          * Δ ω) = D.evtMass P Δ y := by
      rw [Finset.sum_comm]
      unfold DSStruct.evtMass
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_ite_eq (Finset.univ : Finset ((Γ.V → Bool) → (Γ.V → Bool)))
        (D.tableOf P ω) (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ (D.tableOf P ω)), mul_one]
    rw [hnum]
    exact div_self (ne_of_gt hpos)

theorem lat_isLaw {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hP : IsLaw P) (hΔ : IsLaw Δ)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P) (e : Γ.Edge) :
    IsLaw (D.lat P Δ e) := by
  have htab := D.tabLaw_isLaw hP hΔ hsym hdiag e
  unfold DSStruct.lat
  by_cases h : D.leaf (D.vtx e) = true
  · simp only [if_pos h]
    refine ⟨fun a => ?_, ?_⟩
    · show (0 : ℝ) ≤ if a.1 = dfltTable Γ then vMarg P (D.vtx e) a.2 else 0
      split_ifs with ha
      · exact vMarg_nonneg hP _ _
      · exact le_refl 0
    · rw [Fintype.sum_prod_type]
      have hinner : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
          (∑ β : Bool, if T = dfltTable Γ then vMarg P (D.vtx e) β else 0)
            = if T = dfltTable Γ then (1 : ℝ) else 0 := by
        intro T
        by_cases hT : T = dfltTable Γ
        · simp only [if_pos hT]
          rw [Fintype.sum_bool]
          rw [add_comm]
          exact vMarg_sum hP _
        · simp [hT]
      simp only [hinner]
      rw [Finset.sum_ite_eq' (Finset.univ : Finset ((Γ.V → Bool) → (Γ.V → Bool)))
        (dfltTable Γ) (fun _ => (1 : ℝ))]
      exact if_pos (Finset.mem_univ (dfltTable Γ))
  · simp only [if_neg h]
    refine ⟨fun a => ?_, ?_⟩
    · show (0 : ℝ) ≤ if a.2 = false then D.tabLaw P Δ e a.1 else 0
      split_ifs with ha
      · exact htab.1 _
      · exact le_refl 0
    · rw [Fintype.sum_prod_type]
      have hinner : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
          (∑ β : Bool, if β = false then D.tabLaw P Δ e T else 0) = D.tabLaw P Δ e T := by
        intro T; rw [Fintype.sum_bool]; simp
      simp only [hinner]
      exact htab.2

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

theorem leaves_subset_comp (y : Γ.Edge) : D.leaves y ⊆ D.comp y :=
  fun _ hv => D.mem_comp.2 (D.mem_leaves.1 hv).2

/-- The conditional mass that the reconstructed centre source assigns to the outcomes `w` at
the two centres of the component `y`. -/
noncomputable def ctrFactor (P : GTarget Γ) (Δ : GAssign Γ 2 → ℝ) (y : Γ.Edge)
    (w : Γ.V → Bool) : ℝ :=
  (∑ ω : GAssign Γ 2,
      ((if ∀ v ∈ D.ctrs y, gTwist (swapTwist (D.jOf P w)) ω 0 v = w v then (1 : ℝ) else 0) *
        (if D.evt P y ω then (1 : ℝ) else 0)) * Δ ω) / D.evtMass P Δ y

/-- **The component identity.**  The centre factor times the leaf marginals of a component is
the marginal of the target on the whole component.  This is step (iii)–(iv) of the paper proof
in the form the reconstruction needs. -/
theorem ctrFactor_mul {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ} (hP : IsLaw P)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P) {y : Γ.Edge}
    (hy : D.leaf (D.vtx y) = false) (w : Γ.V → Bool) :
    D.ctrFactor P Δ y w * blockMarg (D.leaves y) P w = blockMarg (D.comp y) P w := by
  classical
  have hlf : ∀ ℓ ∈ D.leaves y, D.leaf ℓ = true := fun ℓ hℓ => D.leaf_of_mem_leaves hℓ
  have hB₁ : 0 < blockMarg (D.leaves y) P
      (fun v => xarr P v (flipIdx (D.jOf P w (D.edgeAt v)))) := by
    rw [D.blockMarg_leaves hP hsym hdiag _ hlf]
    exact Finset.prod_pos fun ℓ _ => vMarg_xarr_pos hP ℓ _
  have hmass := D.evtMass_eq hsym hdiag y (D.jOf P w) w
  have hnum : (∑ ω : GAssign Γ 2,
      ((if ∀ v ∈ D.ctrs y, gTwist (swapTwist (D.jOf P w)) ω 0 v = w v then (1 : ℝ) else 0) *
        (if D.evt P y ω then (1 : ℝ) else 0)) * Δ ω)
      = blockMarg (D.ctrs y ∪ D.leaves y) P
          (fun v => if v ∈ D.leaves y then xarr P v (D.jOf P w (D.edgeAt v)) else w v)
        * blockMarg (D.leaves y) P
          (fun v => xarr P v (flipIdx (D.jOf P w (D.edgeAt v)))) := by
    rw [← centreLeaf_mass hsym hdiag (D.leaves y) D.edgeAt
      (fun ℓ hℓ => D.leaf_inc ℓ (hlf ℓ hℓ)) (D.jOf P w) (D.ctrs y)
      (D.ctrs_disjoint_leaves hy) (xarr P) w]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [show (if D.evt P y ω then (1 : ℝ) else 0)
        = (if ∀ ℓ ∈ D.leaves y, ∀ m : Fin 2, readDiag ω m ℓ = xarr P ℓ m then (1 : ℝ) else 0)
      from ind_congr Iff.rfl]
  by_cases hz : blockMarg (D.leaves y) P w = 0
  · rw [hz, mul_zero]
    have h1 : blockMarg (D.comp y) P w ≤ blockMarg (D.leaves y) P w :=
      blockMarg_le hP (D.leaves_subset_comp y) w
    have h2 : 0 ≤ blockMarg (D.comp y) P w := blockMarg_nonneg hP _ w
    linarith
  · have hpos : 0 < blockMarg (D.leaves y) P w :=
      lt_of_le_of_ne (blockMarg_nonneg hP _ w) (Ne.symm hz)
    have hfac : ∀ ℓ ∈ D.leaves y, 0 < vMarg P ℓ (w ℓ) := by
      intro ℓ hℓ
      rw [D.blockMarg_leaves hP hsym hdiag _ hlf] at hpos
      by_contra hc
      push Not at hc
      have hzero : vMarg P ℓ (w ℓ) = 0 := le_antisymm hc (vMarg_nonneg hP _ _)
      rw [Finset.prod_eq_zero hℓ hzero] at hpos
      exact lt_irrefl 0 hpos
    have hw0 : (fun v => if v ∈ D.leaves y then xarr P v (D.jOf P w (D.edgeAt v)) else w v)
        = w := by
      funext v
      by_cases hv : v ∈ D.leaves y
      · rw [if_pos hv, D.jOf_edgeAt (hlf v hv) w]
        exact xarr_pick v (w v) (hfac v hv)
      · rw [if_neg hv]
    rw [hw0] at hmass hnum
    rw [D.comp_eq hy]
    unfold DSStruct.ctrFactor
    rw [hnum, hmass]
    field_simp

end DSStruct


/-- A vertex's twisted reading depends on the relabelling only through its incident sources. -/
theorem gTwist_congr {π π' : Γ.Edge → Equiv.Perm (Fin t)} {ω : GAssign Γ t} {r : Fin t}
    {v : Γ.V} (h : ∀ e ∈ Γ.inc v, π e = π' e) : gTwist π ω r v = gTwist π' ω r v := by
  have hf : (fun e : Γ.inc v => π e.1 r) = (fun e : Γ.inc v => π' e.1 r) := by
    funext e; rw [h e.1 e.2]
  show ω ⟨v, fun e => π e.1 r⟩ = ω ⟨v, fun e => π' e.1 r⟩
  rw [hf]

namespace DSStruct

variable (D : DSStruct Γ)

/-- The vertices whose chosen source is `e`. -/
def fib (e : Γ.Edge) : Finset Γ.V := Finset.univ.filter fun v => D.edgeAt v = e

theorem fib_of_leaf {e : Γ.Edge} (h : D.leaf (D.vtx e) = true) : D.fib e = {D.vtx e} := by
  have := D.fib_leaf (D.vtx e) h
  rwa [D.vtx_edgeAt e] at this

theorem fib_of_ctr {e : Γ.Edge} (h : D.leaf (D.vtx e) = false) : D.fib e = D.ctrs e := by
  have := D.fib_ctr (D.vtx e) h
  rwa [D.vtx_edgeAt e] at this

/-- A leaf source is the centre source of no component. -/
theorem comp_of_leaf {e : Γ.Edge} (h : D.leaf (D.vtx e) = true) : D.comp e = ∅ := by
  ext v
  simp only [D.mem_comp, Finset.notMem_empty, iff_false]
  intro hv
  by_cases hl : D.leaf v = true
  · have hm : D.mate v ∈ D.fib e := by
      simp only [DSStruct.fib, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← D.root_leaf v hl]; exact hv
    rw [D.fib_of_leaf h, Finset.mem_singleton] at hm
    have := D.mate_not_leaf v
    rw [hm, h] at this
    exact absurd this (by simp)
  · have hl' : D.leaf v = false := by simpa using hl
    have hm : v ∈ D.fib e := by
      simp only [DSStruct.fib, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← D.root_ctr v hl']; exact hv
    rw [D.fib_of_leaf h, Finset.mem_singleton] at hm
    rw [hm, h] at hl'
    exact absurd hl' (by simp)

theorem leaves_of_leafEdge {e : Γ.Edge} (h : D.leaf (D.vtx e) = true) : D.leaves e = ∅ :=
  Finset.subset_empty.1 (D.comp_of_leaf h ▸ D.leaves_subset_comp e)

/-- The decoder is local: the outcome at `v` depends only on the sources incident to `v`. -/
theorem dec_local (z z' : Γ.Edge → DSLat Γ) (v : Γ.V)
    (h : ∀ e ∈ Γ.inc v, z e = z' e) : D.dec z v = D.dec z' v := by
  have hv : z (D.edgeAt v) = z' (D.edgeAt v) := h _ (D.edgeAt_inc v)
  have hloc : D.locVec z v = D.locVec z' v := by
    funext u
    unfold DSStruct.locVec
    by_cases hu : D.leaf u = true ∧ D.mate u = v
    · rw [if_pos hu, if_pos hu, h (D.edgeAt u) (by rw [← hu.2]; exact D.edgeAt_inc_mate u)]
    · rw [if_neg hu, if_neg hu]
  unfold DSStruct.dec
  rw [hv, hloc]

/-- At a centre, the reconstructed table evaluated on the local leaf values reads the twisted
observation used by the conditional-marginal identity. -/
theorem tableOf_ctr (P : GTarget Γ) (ω : GAssign Γ 2) {v : Γ.V} (hv : D.leaf v = false)
    (w : Γ.V → Bool) :
    D.tableOf P ω (D.locOut w v) v = gTwist (swapTwist (D.jOf P w)) ω 0 v := by
  unfold DSStruct.tableOf
  refine gTwist_congr fun e he => ?_
  unfold swapTwist
  congr 1
  unfold DSStruct.jOf
  by_cases hl : D.leaf (D.vtx e) = true
  · rw [if_pos hl, if_pos hl]
    have hmem := D.edgeAt_mem (D.vtx e) v (by rw [D.vtx_edgeAt e]; exact he)
    have hne : v ≠ D.vtx e := by
      intro hvv; rw [hvv, hl] at hv; simp at hv
    have hmate : D.mate (D.vtx e) = v := by
      rcases hmem with h | h
      · exact absurd h hne
      · exact h.symm
    unfold DSStruct.locOut
    rw [if_pos ⟨hl, hmate⟩]
  · rw [if_neg hl, if_neg hl]

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

/-- The indicator that a source value gives the vertex `v` the outcome `w v`. -/
def condw (w : Γ.V → Bool) (v : Γ.V) (a : DSLat Γ) : ℝ :=
  if D.leaf v = true then (if a.2 = w v then 1 else 0)
  else (if a.1 (D.locOut w v) v = w v then 1 else 0)

theorem condw_leaf {w : Γ.V → Bool} {v : Γ.V} (h : D.leaf v = true) (a : DSLat Γ) :
    D.condw w v a = if a.2 = w v then 1 else 0 := by unfold DSStruct.condw; rw [if_pos h]

theorem condw_ctr {w : Γ.V → Bool} {v : Γ.V} (h : D.leaf v = false) (a : DSLat Γ) :
    D.condw w v a = if a.1 (D.locOut w v) v = w v then 1 else 0 := by
  unfold DSStruct.condw; rw [if_neg (by simp [h])]

theorem lat_leaf {P : GTarget Γ} {Δ : GAssign Γ 2 → ℝ} {e : Γ.Edge}
    (h : D.leaf (D.vtx e) = true) (a : DSLat Γ) :
    D.lat P Δ e a = if a.1 = dfltTable Γ then vMarg P (D.vtx e) a.2 else 0 := by
  unfold DSStruct.lat; rw [if_pos h]

theorem lat_ctr {P : GTarget Γ} {Δ : GAssign Γ 2 → ℝ} {e : Γ.Edge}
    (h : D.leaf (D.vtx e) = false) (a : DSLat Γ) :
    D.lat P Δ e a = if a.2 = false then D.tabLaw P Δ e a.1 else 0 := by
  unfold DSStruct.lat; rw [if_neg (by simp [h])]

/-- The per-source factor of the reconstructed model at a leaf source. -/
theorem factor_leaf {P : GTarget Γ} {Δ : GAssign Γ 2 → ℝ} {e : Γ.Edge}
    (he : D.leaf (D.vtx e) = true) (w : Γ.V → Bool) :
    (∑ a : DSLat Γ, D.lat P Δ e a * ∏ v ∈ D.fib e, D.condw w v a)
      = vMarg P (D.vtx e) (w (D.vtx e)) := by
  classical
  have hprod : ∀ a : DSLat Γ, (∏ v ∈ D.fib e, D.condw w v a)
      = if a.2 = w (D.vtx e) then (1 : ℝ) else 0 := by
    intro a
    rw [D.fib_of_leaf he, Finset.prod_singleton, D.condw_leaf he]
  simp only [hprod, D.lat_leaf he]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
      (∑ β : Bool, (if T = dfltTable Γ then vMarg P (D.vtx e) β else 0) *
        (if β = w (D.vtx e) then (1 : ℝ) else 0))
        = if T = dfltTable Γ then vMarg P (D.vtx e) (w (D.vtx e)) else 0 := by
    intro T
    by_cases hT : T = dfltTable Γ
    · simp only [if_pos hT]
      rw [Fintype.sum_bool]
      cases w (D.vtx e) <;> simp
    · simp [hT]
  simp only [hinner]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset ((Γ.V → Bool) → (Γ.V → Bool)))
    (dfltTable Γ) (fun _ => vMarg P (D.vtx e) (w (D.vtx e))),
    if_pos (Finset.mem_univ (dfltTable Γ))]

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

/-- The per-source factor of the reconstructed model at a centre source. -/
theorem factor_ctr {P : GTarget Γ} {Δ : GAssign Γ 2 → ℝ} (hP : IsLaw P)
    (hsym : GSymmetric 2 Δ) (hdiag : pushforward Δ readDiag = gTensorPow 2 P) {e : Γ.Edge}
    (he : D.leaf (D.vtx e) = false) (w : Γ.V → Bool) :
    (∑ a : DSLat Γ, D.lat P Δ e a * ∏ v ∈ D.fib e, D.condw w v a) = D.ctrFactor P Δ e w := by
  classical
  have hc : D.leaf (D.mate (D.vtx e)) = false := D.mate_not_leaf _
  have hbc : D.vtx e ≠ D.mate (D.vtx e) := fun h => D.mate_ne (D.vtx e) h.symm
  have hM : D.evtMass P Δ e ≠ 0 := ne_of_gt (D.evtMass_pos hP hsym hdiag e)
  set G : ((Γ.V → Bool) → (Γ.V → Bool)) → ℝ := fun T =>
    (if T (D.locOut w (D.vtx e)) (D.vtx e) = w (D.vtx e) then (1 : ℝ) else 0) *
      (if T (D.locOut w (D.mate (D.vtx e))) (D.mate (D.vtx e)) = w (D.mate (D.vtx e))
        then (1 : ℝ) else 0) with hGdef
  have hprod : ∀ a : DSLat Γ, (∏ v ∈ D.fib e, D.condw w v a) = G a.1 := by
    intro a
    rw [D.fib_of_ctr he]
    unfold DSStruct.ctrs
    rw [Finset.prod_pair hbc, D.condw_ctr he, D.condw_ctr hc, hGdef]
  simp only [hprod, D.lat_ctr he]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
      (∑ β : Bool, (if β = false then D.tabLaw P Δ e T else 0) * G (T, β).1)
        = D.tabLaw P Δ e T * G T := by
    intro T; rw [Fintype.sum_bool]; simp
  simp only [hinner]
  -- the table sum against the conditioned witness
  have hGtab : ∀ ω : GAssign Γ 2, G (D.tableOf P ω)
      = (if ∀ v ∈ D.ctrs e, gTwist (swapTwist (D.jOf P w)) ω 0 v = w v then (1 : ℝ) else 0) := by
    intro ω
    rw [hGdef]
    simp only []
    rw [D.tableOf_ctr P ω he w, D.tableOf_ctr P ω hc w, ind_mul_ind]
    refine ind_congr ?_
    unfold DSStruct.ctrs
    constructor
    · rintro ⟨h1, h2⟩ v hv
      rcases Finset.mem_insert.1 hv with h | h
      · rw [h]; exact h1
      · rw [Finset.mem_singleton.1 h]; exact h2
    · intro h
      exact ⟨h _ (Finset.mem_insert_self _ _),
        h _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  unfold DSStruct.ctrFactor
  rw [eq_div_iff hM, Finset.sum_mul]
  have hterm : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
      D.tabLaw P Δ e T * G T * D.evtMass P Δ e
        = ∑ ω : GAssign Γ 2,
            ((if D.evt P e ω then (1 : ℝ) else 0) * (if D.tableOf P ω = T then (1 : ℝ) else 0)
              * G T) * Δ ω := by
    intro T
    unfold DSStruct.tabLaw
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hM, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [Finset.sum_congr rfl fun T _ => hterm T, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [← hGtab ω]
  have : ∀ T : (Γ.V → Bool) → (Γ.V → Bool),
      (if D.evt P e ω then (1 : ℝ) else 0) * (if D.tableOf P ω = T then (1 : ℝ) else 0) * G T
        = (if D.evt P e ω then (1 : ℝ) else 0) *
          (if D.tableOf P ω = T then G T else 0) := by
    intro T; by_cases h : D.tableOf P ω = T <;> simp [h]
  rw [Finset.sum_congr rfl fun T _ => this T, ← Finset.mul_sum,
    Finset.sum_ite_eq (Finset.univ : Finset ((Γ.V → Bool) → (Γ.V → Bool))) (D.tableOf P ω) G,
    if_pos (Finset.mem_univ (D.tableOf P ω))]
  ring

end DSStruct


namespace DSStruct

variable (D : DSStruct Γ)

/-- The decoder indicator, written as a product over the sources. -/
theorem dec_indicator (P : GTarget Γ) (Δ : GAssign Γ 2 → ℝ) (w : Γ.V → Bool)
    (z : Γ.Edge → DSLat Γ) :
    (if D.dec z = w then (∏ e : Γ.Edge, D.lat P Δ e (z e)) else 0)
      = ∏ e : Γ.Edge, (D.lat P Δ e (z e) * ∏ v ∈ D.fib e, D.condw w v (z e)) := by
  classical
  rw [Finset.prod_mul_distrib]
  have h2 : (∏ e : Γ.Edge, ∏ v ∈ D.fib e, D.condw w v (z e))
      = ∏ v : Γ.V, D.condw w v (z (D.edgeAt v)) := by
    rw [← Finset.prod_fiberwise Finset.univ D.edgeAt
      (fun v => D.condw w v (z (D.edgeAt v)))]
    refine Finset.prod_congr rfl fun e _ => Finset.prod_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.1 hv).2]
  have h3 : (∏ v : Γ.V, D.condw w v (z (D.edgeAt v))) = if D.dec z = w then (1 : ℝ) else 0 := by
    by_cases hlf : ∀ ℓ : Γ.V, D.leaf ℓ = true → (z (D.edgeAt ℓ)).2 = w ℓ
    · have hloc : ∀ v : Γ.V, D.locVec z v = D.locOut w v := by
        intro v
        funext u
        unfold DSStruct.locVec DSStruct.locOut
        by_cases hu : D.leaf u = true ∧ D.mate u = v
        · rw [if_pos hu, if_pos hu, hlf u hu.1]
        · rw [if_neg hu, if_neg hu]
      have hv : ∀ v : Γ.V,
          D.condw w v (z (D.edgeAt v)) = if D.dec z v = w v then (1 : ℝ) else 0 := by
        intro v
        unfold DSStruct.condw DSStruct.dec
        by_cases hl : D.leaf v = true
        · rw [if_pos hl, if_pos hl]
        · rw [if_neg hl, if_neg hl, hloc v]
      have hiff : (∀ v ∈ (Finset.univ : Finset Γ.V), D.dec z v = w v) ↔ D.dec z = w := by
        constructor
        · intro h; funext v; exact h v (Finset.mem_univ v)
        · intro h v _; rw [h]
      rw [Finset.prod_congr rfl (fun v _ => hv v), Finset.prod_boole]
      simp only [hiff]
    · push Not at hlf
      obtain ⟨ℓ, hl, hne⟩ := hlf
      have hz : D.condw w ℓ (z (D.edgeAt ℓ)) = 0 := by
        rw [D.condw_leaf hl, if_neg hne]
      rw [Finset.prod_eq_zero (Finset.mem_univ ℓ) hz]
      have hdz : D.dec z ≠ w := by
        intro h
        refine hne ?_
        have hcf := congrFun h ℓ
        unfold DSStruct.dec at hcf
        rw [if_pos hl] at hcf
        exact hcf
      rw [if_neg hdz]
  rw [h2, h3]
  by_cases h : D.dec z = w
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The double-star reconstruction.**  A target passing the order-two Navascués–Wolfe test on
a pair graph carrying a double-star structure is compatible. -/
theorem gCompatible_of_dsStruct (D : DSStruct Γ) {Δ : GAssign Γ 2 → ℝ} {P : GTarget Γ}
    (hP : IsLaw P) (hΔ : IsLaw Δ) (hsym : GSymmetric 2 Δ)
    (hdiag : pushforward Δ readDiag = gTensorPow 2 P) : GCompatible Γ P := by
  classical
  let _ : Inhabited (DSLat Γ) := ⟨(dfltTable Γ, false)⟩
  refine gCompatible_of_localDecoder (A := DSLat Γ) (D.lat P Δ)
    (fun e => D.lat_isLaw hP hΔ hsym hdiag e) D.dec (D.dec_local) P ?_
  funext w
  simp only [pushforward]
  rw [Finset.sum_congr rfl fun z _ => D.dec_indicator P Δ w z]
  rw [sum_prod_pi (fun e a => D.lat P Δ e a * ∏ v ∈ D.fib e, D.condw w v a)]
  -- the per-source factors
  have hK : ∀ e : Γ.Edge, (∑ a : DSLat Γ, D.lat P Δ e a * ∏ v ∈ D.fib e, D.condw w v a)
      = (if D.leaf (D.vtx e) = true then (1 : ℝ) else D.ctrFactor P Δ e w) *
        (if D.leaf (D.vtx e) = true then vMarg P (D.vtx e) (w (D.vtx e)) else 1) := by
    intro e
    by_cases he : D.leaf (D.vtx e) = true
    · rw [if_pos he, if_pos he, one_mul, D.factor_leaf he]
    · have he' : D.leaf (D.vtx e) = false := by simpa using he
      rw [if_neg he, if_neg he, mul_one, D.factor_ctr hP hsym hdiag he']
  rw [Finset.prod_congr rfl fun e _ => hK e, Finset.prod_mul_distrib]
  -- the target, decomposed over the components
  have hcov : (Finset.univ : Finset Γ.Edge).biUnion D.comp = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    exact ⟨D.root v, trivial, D.mem_comp.2 rfl⟩
  have hPw : (∏ e : Γ.Edge, blockMarg (D.comp e) P w) = P w := by
    rw [← blockMarg_biUnion_of_sourceDisjoint hP hsym hdiag D.comp D.comp_sourceDisjoint
      Finset.univ w, hcov, blockMarg_univ]
  have hcomp : ∀ e : Γ.Edge, blockMarg (D.comp e) P w
      = (if D.leaf (D.vtx e) = true then (1 : ℝ) else D.ctrFactor P Δ e w)
        * blockMarg (D.leaves e) P w := by
    intro e
    by_cases he : D.leaf (D.vtx e) = true
    · rw [if_pos he, one_mul, D.comp_of_leaf he, D.leaves_of_leafEdge he]
    · have he' : D.leaf (D.vtx e) = false := by simpa using he
      rw [if_neg he]
      exact (D.ctrFactor_mul hP hsym hdiag he' w).symm
  have hleaves : (∏ e : Γ.Edge, blockMarg (D.leaves e) P w)
      = ∏ ℓ ∈ D.allLeaves, vMarg P ℓ (w ℓ) := by
    have h1 : ∀ e : Γ.Edge, blockMarg (D.leaves e) P w
        = ∏ ℓ ∈ D.allLeaves.filter (fun ℓ => D.root ℓ = e), vMarg P ℓ (w ℓ) := by
      intro e
      have h2 : D.leaves e = D.allLeaves.filter (fun ℓ => D.root ℓ = e) := by
        unfold DSStruct.leaves DSStruct.allLeaves
        rw [Finset.filter_filter]
      rw [← h2]
      exact D.blockMarg_leaves hP hsym hdiag _ (fun v hv => D.leaf_of_mem_leaves hv) w
    rw [Finset.prod_congr rfl fun e _ => h1 e]
    exact Finset.prod_fiberwise D.allLeaves D.root (fun ℓ => vMarg P ℓ (w ℓ))
  have hB : (∏ e : Γ.Edge,
        (if D.leaf (D.vtx e) = true then vMarg P (D.vtx e) (w (D.vtx e)) else (1 : ℝ)))
      = ∏ ℓ ∈ D.allLeaves, vMarg P ℓ (w ℓ) := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij' D.vtx D.edgeAt ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp [DSStruct.allLeaves, he]
    · intro ℓ hℓ
      simp only [DSStruct.allLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      simp [Finset.mem_filter, D.vtx_of_leaf hℓ, hℓ]
    · intro e _; exact D.vtx_edgeAt e
    · intro ℓ hℓ
      simp only [DSStruct.allLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      exact D.vtx_of_leaf hℓ
    · intro e _; rfl
  rw [← hPw, Finset.prod_congr rfl fun e _ => hcomp e, Finset.prod_mul_distrib, hleaves, hB]

end DSStruct

end TriangleInflation.Graph
