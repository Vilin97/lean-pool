/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Defs

/-!
# Local flips

Statements split from the original `Statements.lean` skeleton (one file per proving task).
Every statement here is proved except `flip_gExpFeasible`; see AUDIT-NOTES for the
mathematics.

The mathematics of this file is that `flipKernel η` is the product kernel of independent
per-coordinate flips. Three structural facts carry every statement below.

* `flipKernel_sum`: each row of the kernel is a law, so flips preserve laws.
* `flipLaw_pushforward`: flips commute with marginalization to an *injectively selected* set
  of coordinates. Injectivity is what makes the selected flips independent; it fails for a
  selection that reads one coordinate twice, and each application below supplies its own
  injectivity (the diagonal rows are distinct because no vertex is isolated, an injectable
  set has one copied observation per vertex, ancestrally independent blocks are disjoint).
* `flipLaw_sigma`: the flip of a product law over disjoint blocks is the product of the
  flipped blocks.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/- The helper lemmas below live in their own namespace: several of them (`inc_nonempty`,
`gAncestors_nonempty`, `gRelabelEquiv`) are also proved, under the same names, in files that
import this one. -/
namespace Flips

/-! ## Finite-sum helpers -/

/-- Summing a product of per-coordinate weights over all dependent functions factorizes into
the product of the per-coordinate sums. -/
theorem sum_prod_pi {α : Type*} [Fintype α] [DecidableEq α] {β : α → Type*}
    [∀ a, Fintype (β a)] (g : ∀ a, β a → ℝ) :
    ∑ v : (∀ a, β a), ∏ a, g a (v a) = ∏ a, ∑ b, g a b := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Integrating a function against a pushforward is integrating its pullback. -/
theorem sum_pushforward_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) (h : β → ℝ) :
    ∑ b, pushforward w F b * h b = ∑ a, w a * h (F a) := by
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by simp

/-- Postcomposing the read map with a bijection transports the pushforward. -/
theorem pushforward_equiv {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (w : α → ℝ) (F : α → β) (e : β ≃ γ) (c : γ) :
    pushforward w (fun a => e (F a)) c = pushforward w F (e.symm c) := by
  simp only [pushforward, ← Equiv.eq_symm_apply]

/-- The same, read as a change of coordinates on the target of the read map. -/
theorem pushforward_equiv' {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (w : α → ℝ) (F : α → β) (e : β ≃ γ) (b : β) :
    pushforward w F b = pushforward w (fun a => e (F a)) (e b) := by
  rw [pushforward_equiv, Equiv.symm_apply_apply]

/-! ## The flip kernel -/

/-- Every transition probability of the flip kernel is nonnegative for `η ∈ [0,1]`. -/
theorem flipKernel_nonneg {ι : Type} [Fintype ι] {η : ℝ} (h0 : 0 ≤ η)
    (h1 : η ≤ 1) (x y : ι → Bool) : 0 ≤ flipKernel η x y := by
  classical
  unfold flipKernel
  exact Finset.prod_nonneg fun i _ => by split <;> linarith

/-- Every transition probability of the flip kernel is positive for `η ∈ (0,1)`. -/
theorem flipKernel_pos {ι : Type} [Fintype ι] {η : ℝ} (h0 : 0 < η)
    (h1 : η < 1) (x y : ι → Bool) : 0 < flipKernel η x y := by
  classical
  unfold flipKernel
  exact Finset.prod_pos fun i _ => by split <;> linarith

/-- Each row of the flip kernel is a law: the per-coordinate weights `1 - η` and `η` sum to
one, for every `η`. -/
theorem flipKernel_sum {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (x : ι → Bool) :
    ∑ y, flipKernel η x y = 1 := by
  simp only [flipKernel]
  rw [sum_prod_pi (β := fun _ : ι => Bool) (fun i b => if x i = b then 1 - η else η)]
  refine Finset.prod_eq_one fun i _ => ?_
  cases x i <;> simp

/-- The flip kernel is exchangeable: relabelling the coordinates by a bijection leaves it
unchanged. -/
theorem flipKernel_comp {ι κ : Type} [Fintype ι] [Fintype κ]
    (η : ℝ) (e : κ ≃ ι) (x y : ι → Bool) :
    flipKernel η (fun j => x (e j)) (fun j => y (e j)) = flipKernel η x y := by
  classical
  simpa [flipKernel] using Equiv.prod_comp e (fun i => if x i = y i then 1 - η else η)

/-- Marginalizing the flip kernel to an injectively selected set of coordinates gives the
flip kernel of the selected coordinates: the unselected coordinates sum out. -/
theorem flipKernel_marginal {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
     (η : ℝ) {f : κ → ι} (hf : Function.Injective f) (x : ι → Bool)
    (z : κ → Bool) :
    pushforward (flipKernel η x) (fun ω j => ω (f j)) z = flipKernel η (fun j => x (f j)) z := by
  classical
  set s : Finset ι := Finset.univ.map ⟨f, hf⟩ with hs
  set Z : ι → Bool := Function.extend f z (fun _ => false) with hZdef
  have hZf : ∀ j, Z (f j) = z j := fun j => hf.extend_apply z _ j
  have hmem : ∀ j, f j ∈ s := by intro j; simp [hs]
  have hcond : ∀ ω : ι → Bool, ((fun j => ω (f j)) = z) ↔ (∀ i ∈ s, ω i = Z i) := by
    intro ω
    constructor
    · intro h i hi
      simp only [hs, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_univ, true_and] at hi
      obtain ⟨j, rfl⟩ := hi
      rw [hZf]
      exact congrFun h j
    · intro h
      funext j
      rw [h _ (hmem j), hZf]
  set g : ι → Bool → ℝ := fun i b =>
    (if i ∈ s then (if b = Z i then (1 : ℝ) else 0) else 1) * (if x i = b then 1 - η else η)
    with hg
  have key : ∀ ω : ι → Bool,
      (if (fun j => ω (f j)) = z then flipKernel η x ω else 0) = ∏ i, g i (ω i) := by
    intro ω
    rw [hg]
    simp only
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_boole]
    simp only [flipKernel]
    by_cases hcc : (∀ i ∈ s, ω i = Z i)
    · rw [ite_eq_left hcc, ite_eq_left ((hcond ω).mpr hcc), one_mul]
    · rw [ite_eq_right hcc, ite_eq_right (fun hh => hcc ((hcond ω).mp hh)), zero_mul]
  have hstep : ∀ i, (∑ b, g i b) = if i ∈ s then (if x i = Z i then 1 - η else η) else 1 := by
    intro i
    rw [hg]
    by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false, Fintype.sum_bool] <;>
      cases hzi : Z i <;> cases hxi : x i <;> norm_num
  simp only [pushforward]
  rw [Finset.sum_congr rfl (fun ω _ => key ω), sum_prod_pi g,
    Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_ite_mem, Finset.univ_inter, hs,
    Finset.prod_map]
  simp only [flipKernel, Function.Embedding.coeFn_mk, hZf]

/-! ## Flips against marginals and products -/

/-- Flips commute with marginalization to an injectively selected set of coordinates: the
marginal of a flipped law is the flipped marginal. -/
theorem flipLaw_pushforward {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (η : ℝ) {f : κ → ι} (hf : Function.Injective f) (P : (ι → Bool) → ℝ) :
    pushforward (flipLaw η P) (fun ω j => ω (f j))
      = flipLaw η (pushforward P (fun ω j => ω (f j))) := by
  funext z
  have hswap : ∀ ω : ι → Bool,
      (if (fun j => ω (f j)) = z then (∑ x, P x * flipKernel η x ω) else 0)
        = ∑ x, P x * (if (fun j => ω (f j)) = z then flipKernel η x ω else 0) := by
    intro ω; split <;> simp
  calc pushforward (flipLaw η P) (fun ω j => ω (f j)) z
      = ∑ ω : ι → Bool, ∑ x : ι → Bool,
          P x * (if (fun j => ω (f j)) = z then flipKernel η x ω else 0) := by
        simp only [pushforward, flipLaw]
        exact Finset.sum_congr rfl fun ω _ => hswap ω
    _ = ∑ x : ι → Bool, P x * pushforward (flipKernel η x) (fun ω j => ω (f j)) z := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => by simp only [pushforward, Finset.mul_sum]
    _ = ∑ x : ι → Bool, P x * flipKernel η (fun j => x (f j)) z :=
        Finset.sum_congr rfl fun x _ => by rw [flipKernel_marginal η hf]
    _ = ∑ u : κ → Bool, pushforward P (fun ω j => ω (f j)) u * flipKernel η u z := by
        rw [sum_pushforward_mul]
    _ = flipLaw η (pushforward P (fun ω j => ω (f j))) z := rfl

/-- Flips of a law that is a product over disjoint blocks are the product of the flipped
blocks: independent flips factorize along the blocks. -/
theorem flipLaw_sigma {α : Type} [Fintype α] [DecidableEq α] {β : α → Type}
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] (η : ℝ)
    (Q : ∀ a, (β a → Bool) → ℝ) (U : (Σ a, β a) → Bool) :
    flipLaw η (fun u => ∏ a, Q a (fun b => u ⟨a, b⟩)) U
      = ∏ a, flipLaw η (Q a) (fun b => U ⟨a, b⟩) := by
  classical
  set e : ((Σ a, β a) → Bool) ≃ (∀ a, β a → Bool) :=
    Equiv.piCurry (fun (a : α) (_ : β a) => Bool) with he
  have hker : ∀ v : ∀ a, β a → Bool,
      flipKernel η (e.symm v) U = ∏ a, flipKernel η (v a) (fun b => U ⟨a, b⟩) := by
    intro v
    simp only [flipKernel]
    rw [Fintype.prod_sigma (fun p : Σ a, β a => if (e.symm v) p = U p then 1 - η else η)]
    rfl
  calc flipLaw η (fun u => ∏ a, Q a (fun b => u ⟨a, b⟩)) U
      = ∑ v : ∀ a, β a → Bool,
          (∏ a, Q a (fun b => (e.symm v) ⟨a, b⟩)) * flipKernel η (e.symm v) U :=
        (Equiv.sum_comp e.symm (fun u => (∏ a, Q a (fun b => u ⟨a, b⟩)) * flipKernel η u U)).symm
    _ = ∑ v : ∀ a, β a → Bool, ∏ a, (Q a (v a) * flipKernel η (v a) (fun b => U ⟨a, b⟩)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hker v, Finset.prod_mul_distrib]
        rfl
    _ = ∏ a, ∑ w : β a → Bool, Q a w * flipKernel η w (fun b => U ⟨a, b⟩) :=
        sum_prod_pi (fun a w => Q a w * flipKernel η w (fun b => U ⟨a, b⟩))
    _ = ∏ a, flipLaw η (Q a) (fun b => U ⟨a, b⟩) := rfl

/-! ## Injectivity of the selections used below -/

/-- No vertex is isolated, so every vertex carries at least one source. -/
theorem inc_nonempty (Γ : PairGraph) (v : Γ.V) : (Γ.inc v).Nonempty := by
  obtain ⟨w, hw⟩ := Γ.no_isolated v
  refine ⟨⟨s(v, w), ?_⟩, ?_⟩
  · simpa using hw
  · simp [PairGraph.inc]

/-- Every copied observation has at least one copied latent ancestor. -/
theorem gAncestors_nonempty (o : GObs Γ t) : (gAncestors o).Nonempty := by
  obtain ⟨e, he⟩ := inc_nonempty Γ o.1
  exact ⟨(e, o.2 ⟨e, he⟩), Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩⟩

/-- Ancestrally independent sets of copied observations are disjoint: a shared member would
contribute its (nonempty) set of ancestors to both. -/
theorem disjoint_of_ancestrallyIndependent {S T : Finset (GObs Γ t)}
    (h : GAncestrallyIndependent S T) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro o hoS hoT
  obtain ⟨a, ha⟩ := gAncestors_nonempty o
  exact (Finset.disjoint_left.mp h (Finset.mem_biUnion.mpr ⟨o, hoS, ha⟩))
    (Finset.mem_biUnion.mpr ⟨o, hoT, ha⟩)

/-- On an injectable set the vertex determines the copied observation, so the party read is
an injective selection of coordinates. -/
theorem injectable_vertex_injective {S : Finset (GObs Γ t)} (hS : GInjectable S) :
    Function.Injective (fun o : S => o.1.1) := by
  obtain ⟨ι, hι⟩ := hS
  have key : ∀ o ∈ S, o = copyObs ι o.1 := by
    intro o ho
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (hι ho)
    subst hv
    rfl
  intro o p hop
  simp only at hop
  apply Subtype.ext
  rw [key o.1 o.2, key p.1 p.2, hop]

/-- The copied observation that diagonal row `r` reads at vertex `v`. -/
def diagObs (Γ : PairGraph) (t : ℕ) (p : Σ _ : Fin t, Γ.V) : GObs Γ t := ⟨p.2, fun _ => p.1⟩

theorem readDiag_eq (ω : GAssign Γ t) (r : Fin t) (v : Γ.V) :
    readDiag ω r v = ω (diagObs Γ t ⟨r, v⟩) := rfl

/-- The diagonal read is the curried selection of the diagonal observations. -/
theorem readDiag_factor (Γ : PairGraph) (t : ℕ) :
    (readDiag : GAssign Γ t → (Fin t → Γ.V → Bool))
      = fun ω => (Equiv.piCurry (fun (_ : Fin t) (_ : Γ.V) => Bool))
          (fun p => ω (diagObs Γ t p)) := rfl

/-- The `t · |V|` diagonal observations are distinct: the vertex is the first component, and
the row index is recovered from any incident source, of which there is at least one. -/
theorem diagObs_injective (Γ : PairGraph) (t : ℕ) : Function.Injective (diagObs Γ t) := by
  rintro ⟨r, v⟩ ⟨r', v'⟩ hEq
  simp only [diagObs, Sigma.mk.injEq] at hEq
  obtain ⟨hv, hfn⟩ := hEq
  subst hv
  obtain ⟨e, he⟩ := inc_nonempty Γ v
  have hrr : r = r' := congrFun (eq_of_heq hfn) ⟨e, he⟩
  subst hrr
  rfl

/-- Relabelling copy indices is a bijection of copied observations. -/
def gPermEquiv (π : Γ.Edge → Equiv.Perm (Fin t)) : GObs Γ t ≃ GObs Γ t where
  toFun := gPerm π
  invFun := gPerm (fun e => (π e).symm)
  left_inv := by intro o; simp [gPerm]
  right_inv := by intro o; simp [gPerm]

/-- Relabelling copy indices is a bijection of assignments. -/
def gRelabelEquiv (π : Γ.Edge → Equiv.Perm (Fin t)) : GAssign Γ t ≃ GAssign Γ t where
  toFun := gRelabel π
  invFun := gRelabel (fun e => (π e).symm)
  left_inv := by intro ω; funext o; simp [gRelabel, gPerm]
  right_inv := by intro ω; funext o; simp [gRelabel, gPerm]

end Flips

open Flips

/-! ## Local flips -/

/-- Independent flips of every coordinate with probability `η ∈ [0,1]` send laws to laws. -/
theorem flipLaw_isLaw {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (P : (ι → Bool) → ℝ) (hP : IsLaw P) : IsLaw (flipLaw η P) := by
  refine ⟨fun y => ?_, ?_⟩
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hP.1 x) (flipKernel_nonneg h0 h1 x y)
  · simp only [flipLaw]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, flipKernel_sum, mul_one]
    exact hP.2

/-- Flips with `0 < η < 1` make every atom strictly positive (AUDIT-NOTES A7). -/
theorem flip_full_support {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (h0 : 0 < η)
    (h1 : η < 1) (P : (ι → Bool) → ℝ) (hP : IsLaw P) : ∀ y, 0 < flipLaw η P y := by
  intro y
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < P x := by
    by_contra hc
    push Not at hc
    have hzero : ∑ x, P x = 0 :=
      Finset.sum_eq_zero fun x _ => le_antisymm (hc x) (hP.1 x)
    rw [hP.2] at hzero
    exact one_ne_zero hzero
  refine Finset.sum_pos'
    (fun x _ => mul_nonneg (hP.1 x) (flipKernel_pos h0 h1 x y).le)
    ⟨x₀, Finset.mem_univ _, mul_pos hx₀ (flipKernel_pos h0 h1 x₀ y)⟩

/-- Flipping every copied observation independently preserves symmetry under the copy-index
action, because the flip kernel is exchangeable. -/
theorem flip_symmetric (η : ℝ) (Δ : GAssign Γ t → ℝ) (h : GSymmetric t Δ) :
    GSymmetric t (flipLaw η Δ) := by
  intro π ω
  have key : ∀ x : GAssign Γ t,
      Δ (gRelabel π x) * flipKernel η (gRelabel π x) (gRelabel π ω)
        = Δ x * flipKernel η x ω := by
    intro x
    rw [h π x]
    congr 1
    exact flipKernel_comp η (gPermEquiv π) x ω
  calc flipLaw η Δ (gRelabel π ω)
      = ∑ x : GAssign Γ t,
          Δ (gRelabelEquiv π x) * flipKernel η (gRelabelEquiv π x) (gRelabel π ω) :=
        (Equiv.sum_comp (gRelabelEquiv π)
          (fun x => Δ x * flipKernel η x (gRelabel π ω))).symm
    _ = ∑ x : GAssign Γ t, Δ x * flipKernel η x ω :=
        Finset.sum_congr rfl fun x _ => key x
    _ = flipLaw η Δ ω := rfl

/-- Flipping the witness flips the diagonal law: the `t · |V|` diagonal observations are
distinct, so their flips are independent, and the diagonal law of the flipped witness is the
tensor power of the flipped target. -/
theorem flip_diagonal (η : ℝ) (Δ : GAssign Γ t → ℝ) (P : GTarget Γ)
    (h : pushforward Δ readDiag = gTensorPow t P) :
    pushforward (flipLaw η Δ) readDiag = gTensorPow t (flipLaw η P) := by
  classical
  rw [readDiag_factor] at h
  have hDsel : pushforward Δ
        (fun (ω : GAssign Γ t) (p : Σ _ : Fin t, Γ.V) => ω (diagObs Γ t p))
      = fun u => ∏ r : Fin t, P (fun v => u ⟨r, v⟩) := by
    funext u
    rw [pushforward_equiv' Δ (fun (ω : GAssign Γ t) (p : Σ _ : Fin t, Γ.V) => ω (diagObs Γ t p))
      (Equiv.piCurry (fun (_ : Fin t) (_ : Γ.V) => Bool)) u, h]
    rfl
  funext y
  rw [readDiag_factor, pushforward_equiv (flipLaw η Δ)
      (fun (ω : GAssign Γ t) (p : Σ _ : Fin t, Γ.V) => ω (diagObs Γ t p))
      (Equiv.piCurry (fun (_ : Fin t) (_ : Γ.V) => Bool)) y,
    flipLaw_pushforward η (diagObs_injective Γ t) Δ, hDsel,
    flipLaw_sigma η (fun _ : Fin t => P)]
  rfl

/-- Flips preserve the injectable-marginal prescriptions: an injectable set has one copied
observation per vertex, so the flips on it are independent. -/
theorem flip_injectableMarginals (η : ℝ) (Δ : GAssign Γ t → ℝ) (P : GTarget Γ)
    (h : GInjectableMarginals t Δ P) :
    GInjectableMarginals t (flipLaw η Δ) (flipLaw η P) := by
  intro S hS
  have h1 : pushforward (flipLaw η Δ) (gRestrict S)
      = flipLaw η (pushforward Δ (gRestrict S)) :=
    flipLaw_pushforward (f := fun o : S => (o : GObs Γ t)) η
      (fun _ _ hab => Subtype.ext hab) Δ
  have h2 : pushforward (flipLaw η P) (gPartyRead S)
      = flipLaw η (pushforward P (gPartyRead S)) :=
    flipLaw_pushforward η (injectable_vertex_injective hS) P
  rw [h1, h2, h S hS]

/-- Flips preserve the ancestral-independence prescriptions: ancestrally independent blocks
are disjoint sets of copied observations, so the flips across blocks are independent. -/
theorem flip_ancestralProducts (η : ℝ) (Δ : GAssign Γ t → ℝ) (P : GTarget Γ)
    (h : GAncestralProducts t Δ P) :
    GAncestralProducts t (flipLaw η Δ) (flipLaw η P) := by
  classical
  intro n S hinj hai
  have hfinj : Function.Injective
      (fun p : Σ m : Fin n, (S m : Finset (GObs Γ t)) => (p.2 : GObs Γ t)) := by
    rintro ⟨m, o⟩ ⟨m', o'⟩ hEq
    simp only at hEq
    have hm : m = m' := by
      by_contra hne
      have hdisj := disjoint_of_ancestrallyIndependent (hai m m' hne)
      rw [Finset.disjoint_left] at hdisj
      have ho' : (o : GObs Γ t) ∈ S m' := by rw [hEq]; exact o'.2
      exact hdisj o.2 ho'
    subst hm
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Subtype.ext hEq
  have hfactor : (fun (ω : GAssign Γ t) m => gRestrict (S m) ω)
      = fun ω => (Equiv.piCurry (fun (m : Fin n) (_ : (S m : Finset (GObs Γ t))) => Bool))
          (fun p => ω (p.2 : GObs Γ t)) := rfl
  have hprod := h n S hinj hai
  rw [hfactor] at hprod
  have hDsel : pushforward Δ (fun (ω : GAssign Γ t)
        (p : Σ m : Fin n, (S m : Finset (GObs Γ t))) => ω (p.2 : GObs Γ t))
      = fun ψ => ∏ m : Fin n, pushforward P (gPartyRead (S m)) (fun o => ψ ⟨m, o⟩) := by
    funext ψ
    rw [pushforward_equiv' Δ (fun (ω : GAssign Γ t)
        (p : Σ m : Fin n, (S m : Finset (GObs Γ t))) => ω (p.2 : GObs Γ t))
      (Equiv.piCurry (fun (m : Fin n) (_ : (S m : Finset (GObs Γ t))) => Bool)) ψ,
      hprod]
    rfl
  funext φ
  rw [hfactor, pushforward_equiv (flipLaw η Δ) (fun (ω : GAssign Γ t)
      (p : Σ m : Fin n, (S m : Finset (GObs Γ t))) => ω (p.2 : GObs Γ t))
      (Equiv.piCurry (fun (m : Fin n) (_ : (S m : Finset (GObs Γ t))) => Bool)) φ,
    flipLaw_pushforward η hfinj Δ, hDsel,
    flipLaw_sigma η (fun m => pushforward P (gPartyRead (S m)))]
  exact Finset.prod_congr rfl fun m _ =>
    (congrFun (flipLaw_pushforward η (injectable_vertex_injective (hinj m)) P) (φ m)).symm

/-- The packaged consequence: local flips of the target stay AI feasible at the same
order. -/
theorem flip_gAIFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) (η : ℝ) (h0 : 0 ≤ η)
    (h1 : η ≤ 1) (h : GAIFeasible Γ t P) : GAIFeasible Γ t (flipLaw η P) := by
  obtain ⟨Δ, hlaw, hsym, hdiag, hinjm, hanc⟩ := h
  exact ⟨flipLaw η Δ, flipLaw_isLaw η h0 h1 Δ hlaw, flip_symmetric η Δ hsym,
    flip_diagonal η Δ P hdiag, flip_injectableMarginals η Δ P hinjm,
    flip_ancestralProducts η Δ P hanc⟩

end TriangleInflation.Graph
