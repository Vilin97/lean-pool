/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/

import LeanPool.ConnesKreimer.PowerSeriesLogMul
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Connes–Kreimer / Foissy (planar, R1) coproduct as a genuine Mathlib `Coalgebra` instance.
    Combinatorial core (List.Perm) proven below verbatim from `Coassoc.lean`; the Mathlib bridge
    lifts it to equality of linear maps. LOCAL — not part of the published godsil tree. -/

open scoped TensorProduct

namespace CK

/-- Planar rooted trees, represented by the forest of children below the root. -/
inductive RTree where
  | node : List RTree → RTree
deriving Inhabited

/-- A planar rooted forest is a list of planar rooted trees. -/
abbrev Forest := List RTree

/-- Formal sums of coproduct tensor monomials, represented by their forest pairs. -/
abbrev Tens := List (Forest × Forest)

/-- Product on formal tensor monomials, multiplying the two tensor legs by forest concatenation. -/
def tmul (x y : Tens) : Tens :=
  x.flatMap (fun (p, r) => y.map (fun (p', r') => (p ++ p', r ++ r')))

mutual
  /-- The Connes-Kreimer coproduct on one rooted tree, as a formal list of tensor terms. -/
  def coprodTree : RTree → Tens
    | .node F => ([RTree.node F], []) :: (coprodForest F).map (fun (p, r) => (p, [RTree.node r]))
  /-- The multiplicative extension of the coproduct from trees to forests. -/
  def coprodForest : Forest → Tens
    | []      => [([], [])]
    | t :: ts => tmul (coprodTree t) (coprodForest ts)
end

@[simp] theorem _root_.CK.tmul_unit_left (y : Tens) : tmul [([], [])] y = y := by simp [tmul]

@[simp] theorem _root_.CK.tmul_unit_right (x : Tens) : tmul x [([], [])] = x := by
  induction x with
  | nil => rfl
  | cons a xs ih => obtain ⟨p, r⟩ := a; simp [tmul, List.append_nil]

theorem _root_.CK.tmul_append_left (x₁ x₂ y : Tens) :
    tmul (x₁ ++ x₂) y = tmul x₁ y ++ tmul x₂ y := by simp [tmul, List.flatMap_append]

theorem _root_.CK.tmul_cons (p r : Forest) (xs y : Tens) :
    tmul ((p, r) :: xs) y =
      y.map (fun (p', r') => (p ++ p', r ++ r')) ++ tmul xs y := by
  simp [tmul]

theorem _root_.CK.tmul_assoc (x y z : Tens) : tmul (tmul x y) z = tmul x (tmul y z) := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨p, r⟩ := a
    rw [tmul_cons, tmul_append_left, ih, tmul_cons]
    congr 1
    simp [tmul, List.flatMap_map, List.map_flatMap, List.append_assoc, Function.comp_def]

theorem _root_.CK.coprodForest_append (F G : Forest) :
    coprodForest (F ++ G) = tmul (coprodForest F) (coprodForest G) := by
  induction F with
  | nil => simp [coprodForest, tmul_unit_left]
  | cons t ts ih =>
    change coprodForest (t :: (ts ++ G)) = _
    rw [show coprodForest (t :: (ts ++ G)) = tmul (coprodTree t) (coprodForest (ts ++ G)) from rfl,
        ih, ← tmul_assoc,
        show tmul (coprodTree t) (coprodForest ts) = coprodForest (t :: ts) from rfl]

open List in
theorem _root_.CK.perm_middle_swap {α} (A B C D : List α) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  calc (A ++ B) ++ (C ++ D)
      = A ++ ((B ++ C) ++ D) := by simp [List.append_assoc]
    _ ~ A ++ ((C ++ B) ++ D) := (List.perm_append_comm).append_right D |>.append_left A
    _ = (A ++ C) ++ (B ++ D) := by simp [List.append_assoc]

open List in
theorem _root_.CK.flatMap_append_distrib {α β} (l : List α) (X Y : α → List β) :
    (l.flatMap (fun a => X a ++ Y a)).Perm (l.flatMap X ++ l.flatMap Y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left (X a ++ Y a) ih).trans ?_
    exact perm_middle_swap (X a) (Y a) (as.flatMap X) (as.flatMap Y)

open List in
theorem _root_.CK.flatMap_const_nil {α β} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  simp_all

theorem _root_.CK.flatMap_singleton_eq_map {α β} (g : α → β) (l : List α) :
    l.flatMap (fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

open List in
theorem _root_.CK.flatMap_comm {α β γ} (l1 : List α) (l2 : List β)
    (f : α → β → List γ) :
    (l1.flatMap (fun a => l2.flatMap (fun b => f a b))).Perm
    (l2.flatMap (fun b => l1.flatMap (fun a => f a b))) := by
  induction l1 with
  | nil => simp [flatMap_const_nil]
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_right _ (List.Perm.refl _)).trans ?_
    refine (List.Perm.append_left (l2.flatMap (fun b => f a b)) ih).trans ?_
    exact (flatMap_append_distrib l2 (fun b => f a b) (fun b => as.flatMap (fun a => f a b))).symm

theorem _root_.CK.Perm.flatMap_congr_right {α β} (l : List α) {f g : α → List β}
    (h : ∀ a, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons]; exact (h a).append ih

/-- Formal sums of triple tensor monomials, represented by forest triples. -/
abbrev _root_.CK.Tens3 := List (Forest × Forest × Forest)

/-- Expand the left tensor leg of every coproduct term. -/
def _root_.CK.coLeft (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest p).map (fun (a, b) => (a, b, r)))

/-- Expand the right tensor leg of every coproduct term. -/
def _root_.CK.coRight (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest r).map (fun (b, c) => (p, b, c)))

/-- Product on formal triple tensor monomials, multiplying all three tensor legs. -/
def _root_.CK.tmul3 (x y : Tens3) : Tens3 :=
  x.flatMap (fun (a, b, c) => y.map (fun (a', b', c') => (a ++ a', b ++ b', c ++ c')))

theorem _root_.CK.coLeft_tmul (x y : Tens) :
    (coLeft (tmul x y)).Perm (tmul3 (coLeft x) (coLeft y)) := by
  simp only [coLeft, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem _root_.CK.coRight_tmul (x y : Tens) :
    (coRight (tmul x y)).Perm (tmul3 (coRight x) (coRight y)) := by
  simp only [coRight, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem _root_.CK.coprodTree_node (F : Forest) :
    coprodTree (RTree.node F)
      = ([RTree.node F], []) :: (coprodForest F).map (fun pr => (pr.1, [RTree.node pr.2])) := rfl

theorem _root_.CK.coprodForest_single (t : RTree) : coprodForest [t] = coprodTree t := by
  change tmul (coprodTree t) (coprodForest []) = coprodTree t
  rw [show coprodForest ([] : Forest) = [([], [])] from rfl, tmul_unit_right]

theorem _root_.CK.tmul3_perm {a a' b b' : Tens3} (ha : a.Perm a') (hb : b.Perm b') :
    (tmul3 a b).Perm (tmul3 a' b') := by
  refine (ha.flatMap_right _).trans ?_
  exact Perm.flatMap_congr_right a' (fun _ => hb.map _)

mutual
  theorem _root_.CK.coassocTree (t : RTree) :
      (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := by
    cases t with
    | node F =>
      simp only [coLeft, coRight, coprodTree_node, coprodForest_single, List.map_cons,
        List.flatMap_cons, List.map_map, List.flatMap_map, Function.comp_def,
        show coprodForest ([] : Forest) = [([], [])] from rfl]
      refine List.Perm.cons _ ?_
      have hR2 :
          (List.flatMap (fun a => (a.fst, [RTree.node a.snd], []) ::
              List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
              (coprodForest F)).Perm
          (List.map (fun x => (x.fst, [RTree.node x.snd], [])) (coprodForest F)
            ++ List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
                (coprodForest a.snd)) (coprodForest F)) := by
        have h := flatMap_append_distrib (coprodForest F)
          (fun a => [(a.fst, [RTree.node a.snd], [])])
          (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
        rwa [flatMap_singleton_eq_map] at h
      have hkey :
          (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F)).Perm
          (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F)) := by
        have e1 :
            (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F))
            = (coLeft (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coLeft, List.map_flatMap, List.map_map, Function.comp_def]
        have e2 :
            (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F))
            = (coRight (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coRight, List.map_flatMap, List.map_map, Function.comp_def]
        rw [e1, e2]
        exact (coassocForest F).map _
      exact (List.Perm.append_left _ hkey).trans hR2.symm
  theorem _root_.CK.coassocForest (F : Forest) :
      (coLeft (coprodForest F)).Perm (coRight (coprodForest F)) := by
    cases F with
    | nil => exact .refl _
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl]
      refine (coLeft_tmul _ _).trans ?_
      refine (tmul3_perm (coassocTree t) (coassocForest ts)).trans ?_
      exact (coRight_tmul _ _).symm
end

/-! ### Mathlib bridge: lift the combinatorial coassoc to a `Coalgebra` instance. -/

variable (k : Type*) [CommRing k]

/-- Carrier: forests with k-coefficients (product = forest concatenation). -/
abbrev _root_.CK.H := MonoidAlgebra k (FreeMonoid RTree)

/-- Extensionality for linear maps out of `H k`, tested on the forest basis. A `Forest`-indexed
    repackaging of `MonoidAlgebra.lhom_ext'` (`Forest` and `FreeMonoid RTree` are definitionally
    but not reducibly equal, and `rw` needs the former). -/
theorem _root_.CK.lhom_ext {N : Type*} [AddCommMonoid N] [Module k N] ⦃φ ψ : H k →ₗ[k] N⦄
    (h : ∀ (f : Forest) (b : k),
      φ (MonoidAlgebra.single f b) = ψ (MonoidAlgebra.single f b)) : φ = ψ :=
  MonoidAlgebra.lhom_ext' fun f => LinearMap.ext fun b => h (FreeMonoid.toList f) b

/-- Pure 2-tensor of a cut `(p, r)`. -/
noncomputable def _root_.CK.e2 (pr : Forest × Forest) : H k ⊗[k] H k :=
  MonoidAlgebra.single pr.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 (1 : k)

/-- Pure 3-tensor of an iterated cut `(a, b, c)`, associated to the right. -/
noncomputable def _root_.CK.e3 (t : Forest × Forest × Forest) : H k ⊗[k] (H k ⊗[k] H k) :=
  MonoidAlgebra.single t.1 (1 : k) ⊗ₜ[k]
    (MonoidAlgebra.single t.2.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single t.2.2 (1 : k))

/-- Δ on a basis forest. -/
noncomputable def _root_.CK.Δ₀ (f : Forest) : H k ⊗[k] H k := ((coprodForest f).map (e2 k)).sum

/-- E3 of a triple-tensor list. -/
noncomputable def _root_.CK.E3 (l : Tens3) : H k ⊗[k] (H k ⊗[k] H k) := (l.map (e3 k)).sum

/-- Comultiplication. -/
noncomputable def _root_.CK.Δ : H k →ₗ[k] H k ⊗[k] H k :=
  Finsupp.linearCombination k (Δ₀ k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.Δ_single (f : Forest) (b : k) :
    Δ k (MonoidAlgebra.single f b) = b • Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f b) = b • Δ₀ k f
  rw [Finsupp.linearCombination_single]

/-- E3 distributes over `flatMap`. -/
theorem _root_.CK.E3_flatMap (L : Tens) (g : Forest × Forest → Tens3) :
    E3 k (L.flatMap g) = (L.map (fun x => E3 k (g x))).sum := by
  unfold E3
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A linear map commutes with a `List.sum` of mapped terms. -/
theorem _root_.CK.linmap_list_sum {α} {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] (φ : M →ₗ[k] N) (l : List α) (h : α → M) :
    φ ((l.map h).sum) = (l.map (fun a => φ (h a))).sum := by
  rw [map_list_sum, List.map_map]; rfl

/-- The per-cut computation: `assoc ∘ rTensor Δ` on a pure 2-tensor `e2 (p,r)`
    equals `E3` of the left-leg refinement. This is the heart of the coassoc bridge. -/
theorem _root_.CK.elem_lemma (pr : Forest × Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (e2 k pr))
      = E3 k ((coprodForest pr.1).map (fun ab => (ab.1, ab.2, pr.2))) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, LinearMap.rTensor_tmul, Δ_single, one_smul, Δ₀]
  -- Ψ : y ↦ assoc (y ⊗ single r 1), linear; push through the list sum.
  let Ψ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
      (TensorProduct.mk k (H k ⊗[k] H k) (H k)).flip (MonoidAlgebra.single r 1)
  have hΨ : (TensorProduct.assoc k (H k) (H k) (H k))
        ((((coprodForest p).map (e2 k)).sum) ⊗ₜ[k] MonoidAlgebra.single r (1 : k))
      = Ψ (((coprodForest p).map (e2 k)).sum) := rfl
  rw [hΨ, linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  obtain ⟨a, b⟩ := ab
  simp only [Function.comp_def, Ψ, e2, e3, LinearMap.coe_comp, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, LinearMap.flip_apply, TensorProduct.assoc_tmul]

/-- Right-leg analogue: `lTensor Δ` on `e2 (p,r)` equals `E3` of the right-leg refinement.
    No `assoc` needed — the tensor is already right-associated. -/
theorem _root_.CK.elem_lemma_R (pr : Forest × Forest) :
    LinearMap.lTensor (H k) (Δ k) (e2 k pr)
      = E3 k ((coprodForest pr.2).map (fun bc => (pr.1, bc.1, bc.2))) := by
  rw [e2, LinearMap.lTensor_tmul, Δ_single, one_smul, Δ₀]
  let Θ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    TensorProduct.mk k (H k) (H k ⊗[k] H k) (MonoidAlgebra.single pr.1 1)
  change Θ (((coprodForest pr.2).map (e2 k)).sum) = _
  rw [linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bc _
  simp only [Function.comp_def, Θ, e2, e3, TensorProduct.mk_apply]

/-- LHS structural map on `Δ₀ f`. -/
theorem _root_.CK.lhs_core (f : Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ₀ k f))
      = E3 k (coLeft (coprodForest f)) := by
  rw [Δ₀]
  let Φ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ LinearMap.rTensor (H k) (Δ k)
  have hΦ : (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (((coprodForest f).map (e2 k)).sum))
      = Φ (((coprodForest f).map (e2 k)).sum) := rfl
  rw [hΦ, linmap_list_sum, coLeft, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma k pr

/-- RHS structural map on `Δ₀ f`. -/
theorem _root_.CK.rhs_core (f : Forest) :
    LinearMap.lTensor (H k) (Δ k) (Δ₀ k f) = E3 k (coRight (coprodForest f)) := by
  rw [Δ₀]
  rw [linmap_list_sum, coRight, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma_R k pr

/-- The combinatorial coassoc, transported to `E3`. -/
theorem _root_.CK.perm_E3 (f : Forest) :
    E3 k (coLeft (coprodForest f)) = E3 k (coRight (coprodForest f)) :=
  (List.Perm.map (e3 k) (coassocForest f)).sum_eq

/-- **Coassociativity** as an equality of linear maps. -/
theorem _root_.CK.coassoc_map :
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
        LinearMap.rTensor (H k) (Δ k) ∘ₗ Δ k
      = LinearMap.lTensor (H k) (Δ k) ∘ₗ Δ k := by
  apply CK.lhom_ext
  intro f b
  change (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b)))
      = LinearMap.lTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b))
  rw [Δ_single]
  simp only [map_smul]
  rw [lhs_core, rhs_core, perm_E3]

/-! ### Counit. -/

/-- Counit monoid hom: every generator ↦ 0, so a word ↦ `0 ^ len` = indicator of empty. -/
def _root_.CK.εmon : FreeMonoid RTree →* k := FreeMonoid.lift (fun _ => (0 : k))

@[simp] theorem _root_.CK.εmon_nil : εmon k ([] : Forest) = 1 := map_one _

@[simp] theorem _root_.CK.εmon_of (a : RTree) : εmon k (FreeMonoid.of a) = 0 := rfl

@[simp] theorem _root_.CK.εmon_cons (a : RTree) (l : Forest) : εmon k (a :: l) = 0 := by
  change εmon k (FreeMonoid.of a * FreeMonoid.ofList l) = 0
  rw [map_mul, εmon_of, zero_mul]

theorem _root_.CK.εmon_append (p p' : Forest) : εmon k (p ++ p') = εmon k p * εmon k p' := by
  induction p with
  | nil => simp
  | cons a as ih => simp

/-- Counit as an algebra hom, then linear. -/
noncomputable def _root_.CK.εalg : H k →ₐ[k] k :=
  MonoidAlgebra.lift k k (FreeMonoid RTree) (εmon k)

/-- The Connes-Kreimer counit as a linear map. -/
noncomputable def _root_.CK.ε : H k →ₗ[k] k := (εalg k).toLinearMap

theorem _root_.CK.ε_single (f : Forest) (b : k) :
    ε k (MonoidAlgebra.single f b) = b * εmon k f := by
  have h : εalg k (MonoidAlgebra.single (FreeMonoid.ofList f) b)
      = b * εmon k (FreeMonoid.ofList f) := by
    rw [εalg, MonoidAlgebra.lift_single, smul_eq_mul]
  exact h

/-- Scalar smul commutes with a `List.sum`. -/
theorem _root_.CK.smul_list_sum {M : Type*} [AddCommMonoid M] [Module k M] (c : k) (l : List M) :
    c • l.sum = (l.map (fun x => c • x)).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [smul_add, ih]

/-- Smul through a mapped `List.sum`. -/
theorem _root_.CK.smul_list_sum' {α M : Type*} [AddCommMonoid M] [Module k M]
    (c : k) (l : List α) (F : α → M) :
    c • (l.map F).sum = (l.map (fun x => c • F x)).sum := by
  rw [smul_list_sum, List.map_map]; rfl

/-- Pull a base-ring scalar out of the right tensor leg (avoids `CompatibleSMul`). -/
theorem _root_.CK.tmul_scalar_right (m : H k) (c : k) :
    m ⊗ₜ[k] c = c • (m ⊗ₜ[k] (1 : k)) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- Pull a base-ring scalar out of the left tensor leg. -/
theorem _root_.CK.tmul_scalar_left (c : k) (m : H k) :
    (c : k) ⊗ₜ[k] m = c • ((1 : k) ⊗ₜ[k] m) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [TensorProduct.smul_tmul']

/-- Generic map-over-`flatMap` `List.sum` distribution. -/
theorem _root_.CK.map_flatMap_sum {α β : Type*} {M : Type*} [AddCommMonoid M]
    (L : List α) (G : α → List β) (h : β → M) :
    ((L.flatMap G).map h).sum = (L.map (fun a => ((G a).map h).sum)).sum := by
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! The left-counit collapse: `ε` on the left leg selects the unique `([], f)` cut. -/
mutual
  theorem _root_.CK.collapseL_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.1 • g pr.2)).sum = g [t] := by
    cases t with
    | node F =>
      rw [coprodTree_node]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, εmon_cons,
        zero_smul, zero_add]
      exact collapseL_forest F (fun r => g [RTree.node r])
  theorem _root_.CK.collapseL_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.1 • g pr.2)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.1 • g q.2)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.1 • g (pr.2 ++ ts))).sum from ?_]
      · exact collapseL_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.1 •
            ((coprodForest ts).map (fun x => εmon k x.1 • g (pr.2 ++ x.2))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.1 x.1, mul_smul]
        · congr 1
          exact collapseL_forest ts (fun r => g (pr.2 ++ r))
end

/-! The right-counit collapse: `ε` on the right leg selects the unique `(f, [])` cut. -/
mutual
  theorem _root_.CK.collapseR_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.2 • g pr.1)).sum = g [t] := by
    cases t with
    | node F =>
      simp only [coprodTree_node, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        εmon_nil, εmon_cons, zero_smul, one_smul]
      simp_all
  theorem _root_.CK.collapseR_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.2 • g pr.1)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.2 • g q.1)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.2 • g (pr.1 ++ ts))).sum from ?_]
      · exact collapseR_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.2 •
            ((coprodForest ts).map (fun x => εmon k x.2 • g (pr.1 ++ x.1))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.2 x.2, mul_smul]
        · congr 1
          exact collapseR_forest ts (fun r => g (pr.1 ++ r))
end

/-- `(ε ⊗ id) ∘ Δ` on a basis forest gives `1 ⊗ single f 1`. -/
theorem _root_.CK.rTensor_ε_Δ₀ (f : Forest) :
    LinearMap.rTensor (H k) (ε k) (Δ₀ k f) = (1 : k) ⊗ₜ[k] MonoidAlgebra.single f 1 := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr => LinearMap.rTensor (H k) (ε k) (e2 k pr))).sum
        = ((coprodForest f).map (fun pr =>
            εmon k pr.1 • ((1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 1))).sum from ?_]
  · exact collapseL_forest (k := k) f (fun r => (1 : k) ⊗ₜ[k] MonoidAlgebra.single r 1)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [e2, LinearMap.rTensor_tmul, ε_single, one_mul]
    apply tmul_scalar_left

/-- `(id ⊗ ε) ∘ Δ` on a basis forest gives `single f 1 ⊗ 1`. -/
theorem _root_.CK.lTensor_ε_Δ₀ (f : Forest) :
    LinearMap.lTensor (H k) (ε k) (Δ₀ k f) = MonoidAlgebra.single f 1 ⊗ₜ[k] (1 : k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr => LinearMap.lTensor (H k) (ε k) (e2 k pr))).sum
        = ((coprodForest f).map (fun pr =>
            εmon k pr.2 • (MonoidAlgebra.single pr.1 1 ⊗ₜ[k] (1 : k)))).sum from ?_]
  · exact collapseR_forest (k := k) f (fun r => MonoidAlgebra.single r 1 ⊗ₜ[k] (1 : k))
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [e2, LinearMap.lTensor_tmul, ε_single, one_mul]
    apply tmul_scalar_right

theorem _root_.CK.single_smul_one (f : FreeMonoid RTree) (b : k) :
    MonoidAlgebra.single f b = b • MonoidAlgebra.single f 1 := by
  simp

noncomputable instance : CoalgebraStruct k (H k) where
  comul := Δ k
  counit := ε k

noncomputable instance _root_.CK.instCKCoalg : Coalgebra k (H k) where
  coassoc := coassoc_map k
  rTensor_counit_comp_comul := by
    apply CK.lhom_ext
    intro f b
    change LinearMap.rTensor (H k) (ε k) (Δ k (MonoidAlgebra.single f b))
        = (TensorProduct.mk k k (H k)) 1 (MonoidAlgebra.single f b)
    rw [Δ_single, map_smul,
        rTensor_ε_Δ₀, TensorProduct.mk_apply, single_smul_one (k := k) (f := f) (b := b)]
    exact (TensorProduct.tmul_smul b (1 : k) (MonoidAlgebra.single f 1 : H k)).symm
  lTensor_counit_comp_comul := by
    apply CK.lhom_ext
    intro f b
    change LinearMap.lTensor (H k) (ε k) (Δ k (MonoidAlgebra.single f b))
        = (TensorProduct.mk k (H k) k).flip 1 (MonoidAlgebra.single f b)
    rw [Δ_single, map_smul,
        lTensor_ε_Δ₀, LinearMap.flip_apply, TensorProduct.mk_apply,
        single_smul_one (k := k) (f := f) (b := b)]
    exact TensorProduct.smul_tmul' b (MonoidAlgebra.single f 1 : H k) (1 : k)

/-! ### Bialgebra: `Δ` and `ε` are algebra homs. -/

/-- `single` of a concatenation is the product (algebra structure of `H`). -/
theorem _root_.CK.single_append (p p' : Forest) :
    (MonoidAlgebra.single (p ++ p') (1 : k) : H k)
      = (MonoidAlgebra.single p 1 : H k) * (MonoidAlgebra.single p' 1 : H k) := by
  have h : (MonoidAlgebra.single (FreeMonoid.ofList p * FreeMonoid.ofList p') (1 : k) : H k)
      = (MonoidAlgebra.single (FreeMonoid.ofList p) (1 : k) : H k) *
        (MonoidAlgebra.single (FreeMonoid.ofList p') (1 : k) : H k) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  exact h

/-- `e2` is multiplicative across leg-wise concatenation. -/
theorem _root_.CK.e2_mul (pr pr' : Forest × Forest) :
    e2 k (pr.1 ++ pr'.1, pr.2 ++ pr'.2) = e2 k pr * e2 k pr' := by
  simp only [e2, Algebra.TensorProduct.tmul_mul_tmul, single_append]

/-- Left-distribute a product over a `List.sum`. -/
theorem _root_.CK.mul_list_sum {M : Type*} [NonUnitalNonAssocSemiring M] (a : M) (L : List M) :
    a * L.sum = (L.map (fun b => a * b)).sum := by
  induction L with
  | nil => simp
  | cons b bs ih => simp [mul_add, ih]

/-- Product of two `List.sum`s is the double sum. -/
theorem _root_.CK.list_sum_mul_sum {M : Type*} [NonUnitalNonAssocSemiring M] (L1 L2 : List M) :
    L1.sum * L2.sum = (L1.flatMap (fun a => L2.map (fun b => a * b))).sum := by
  induction L1 with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, add_mul, ih, mul_list_sum, List.flatMap_cons, List.sum_append]

/-- `Δ₀` is multiplicative. -/
theorem _root_.CK.Δ₀_mul (F G : Forest) : Δ₀ k (F ++ G) = Δ₀ k F * Δ₀ k G := by
  rw [Δ₀, Δ₀, Δ₀, coprodForest_append, list_sum_mul_sum, tmul]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, e2_mul]

/-- `Δ` is multiplicative on all of `H` (reduce to the forest basis, bilinearly). -/
theorem _root_.CK.Δ_mul (a b : H k) : Δ k (a * b) = Δ k a * Δ k b := by
  induction a using MonoidAlgebra.induction_on with
  | of F =>
    induction b using MonoidAlgebra.induction_on with
    | of G =>
      simp only [MonoidAlgebra.of_apply]
      change Δ k ((MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k))
          = Δ k (MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            Δ k (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k)
      rw [← single_append, Δ_single, Δ_single, Δ_single, one_smul, one_smul, one_smul]
      exact Δ₀_mul k F G
    | add b1 b2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | smul r b hb => rw [mul_smul_comm, map_smul, map_smul, hb, mul_smul_comm]
  | add a1 a2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | smul r a ha => rw [smul_mul_assoc, map_smul, map_smul, ha, smul_mul_assoc]

/-- `Δ 1 = 1`. -/
theorem _root_.CK.Δ_one : Δ k (1 : H k) = 1 := by
  rw [show (1 : H k) = MonoidAlgebra.single (M := FreeMonoid RTree) ([] : Forest) (1 : k) from rfl,
      Δ_single, one_smul]
  rw [Δ₀, show coprodForest ([] : Forest) = [([], [])] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, e2]
  rfl

noncomputable instance _root_.CK.instCKBialg : Bialgebra k (H k) :=
  Bialgebra.mk' k (H k)
    (map_one (εalg k))
    (fun {a b} => map_mul (εalg k) a b)
    (Δ_one k)
    (fun {a b} => Δ_mul k a b)

/-! ### Toward HopfAlgebra: node count (grading) and its conservation under cuts.
    Conservation `|p| + |r| = |f|` makes the antipode recursion well-founded
    (`r ≠ [] ⟹ |p| < |f|`). -/

mutual
  /-- Number of nodes in a rooted tree. -/
  def _root_.CK.sizeT : RTree → Nat
    | .node F => 1 + sizeF F
  /-- Number of nodes in a rooted forest. -/
  def _root_.CK.sizeF : Forest → Nat
    | []      => 0
    | t :: ts => sizeT t + sizeF ts
end

theorem _root_.CK.sizeF_append (F G : Forest) : sizeF (F ++ G) = sizeF F + sizeF G := by
  induction F with
  | nil => simp [sizeF]
  | cons t ts ih => simp only [List.cons_append, sizeF, ih]; ring

mutual
  theorem _root_.CK.size_consTree (t : RTree) :
      ∀ pr ∈ coprodTree t, sizeF pr.1 + sizeF pr.2 = sizeT t := by
    cases t with
    | node F =>
      intro pr hpr
      rw [coprodTree_node] at hpr
      simp only [List.mem_cons, List.mem_map] at hpr
      rcases hpr with h | ⟨q, hq, rfl⟩
      · subst h; simp [sizeF, sizeT]
      · simp only [sizeF, sizeT]
        have := size_consForest F q hq
        omega
  theorem _root_.CK.size_consForest (f : Forest) :
      ∀ pr ∈ coprodForest f, sizeF pr.1 + sizeF pr.2 = sizeF f := by
    cases f with
    | nil =>
      intro pr hpr
      simp only [show coprodForest ([] : Forest) = [([], [])] from rfl, List.mem_singleton] at hpr
      subst hpr; simp [sizeF]
    | cons t ts =>
      intro pr hpr
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          tmul] at hpr
      simp only [List.mem_flatMap, List.mem_map] at hpr
      obtain ⟨a, ha, b, hb, rfl⟩ := hpr
      have h1 := size_consTree t a ha
      have h2 := size_consForest ts b hb
      simp only [sizeF, sizeF_append]
      omega
end

theorem _root_.CK.sizeF_pos {f : Forest} (h : f ≠ []) : 0 < sizeF f := by
  cases f with
  | nil => exact absurd rfl h
  | cons t ts => cases t with | node F => simp [sizeF, sizeT]

/-- A forest as an `H`-basis element, with the index forced to `FreeMonoid RTree`
    via `ofList` (so it is always typed `H k`, even on the empty forest). -/
noncomputable def _root_.CK.sf (r : Forest) : H k := MonoidAlgebra.single (FreeMonoid.ofList r) 1

@[simp] theorem _root_.CK.sf_nil : sf k [] = 1 := by
  rw [sf, FreeMonoid.ofList_nil, ← MonoidAlgebra.one_def]

theorem _root_.CK.sf_append (a b : Forest) : sf k (a ++ b) = sf k a * sf k b := by
  rw [sf, sf, sf, MonoidAlgebra.single_mul_single, mul_one, FreeMonoid.ofList_append]

/-- The antipode on the forest basis, by well-founded recursion on node count.
    `S(∅) = 1`; `S(f) = -Σ_{(p,r) cut, r ≠ ∅} S(p)·r`. Recursion decreases since
    `|p| < |f|`. -/
noncomputable def _root_.CK.antipodeF : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).attach.map
        (fun pr => antipodeF pr.val.1 * sf k pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hr : pr.val.2 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hr
  have hlt : sizeF pr.val.1 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

/-! ### Antipode as a linear map + the left convolution axiom (`S ⋆ id = η∘ε`). -/

/-- The antipode linear map obtained by extending `antipodeF` from the forest basis. -/
noncomputable def _root_.CK.antipode : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.antipode_single (f : Forest) (b : k) :
    antipode k (MonoidAlgebra.single f b) = b • antipodeF k f := by
  change Finsupp.linearCombination k (antipodeF k) (Finsupp.single f b) = b • antipodeF k f
  rw [Finsupp.linearCombination_single]

/-- `antipodeF` on a nonempty forest, as a plain (non-`attach`) sum. -/
theorem _root_.CK.antipodeF_cons (t : RTree) (ts : Forest) :
    antipodeF k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).map
          (fun pr => antipodeF k pr.1 * sf k pr.2)).sum := by
  conv_lhs => rw [antipodeF]
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- `r ++ b` is nonempty when `r` is. -/
theorem _root_.CK.isEmpty_append_of_ne {r b : Forest} (h : r ≠ []) :
    (r ++ b).isEmpty = false := by
  simp_all

/-- Filtering cuts by "empty right leg" factorizes over `tmul`. -/
theorem _root_.CK.filter_emptyR_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.2.isEmpty)
      = tmul (A.filter (fun pr => pr.2.isEmpty)) (B.filter (fun pr => pr.2.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases r with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-right cut of a tree `t` is `([t], [])`. -/
  theorem _root_.CK.coprodTree_filter_emptyR (t : RTree) :
      (coprodTree t).filter (fun pr => pr.2.isEmpty) = [([t], [])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_nil, ite_true, List.filter_map, Function.comp_def]
      simp_all
  theorem _root_.CK.coprodForest_filter_emptyR (f : Forest) :
      (coprodForest f).filter (fun pr => pr.2.isEmpty) = [(f, [])] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyR t
      have hts := coprodForest_filter_emptyR ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyR_tmul, ht, hts]
      simp [tmul]
end

/-- Filtering cuts by "empty left leg" factorizes over `tmul`. -/
theorem _root_.CK.filter_emptyL_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.1.isEmpty)
      = tmul (A.filter (fun pr => pr.1.isEmpty)) (B.filter (fun pr => pr.1.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases p with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-left cut of a tree `t` is `([], [t])`. -/
  theorem _root_.CK.coprodTree_filter_emptyL (t : RTree) :
      (coprodTree t).filter (fun pr => pr.1.isEmpty) = [([], [t])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.filter_map,
        Function.comp_def]
      rw [coprodForest_filter_emptyL F]
      rfl
  theorem _root_.CK.coprodForest_filter_emptyL (f : Forest) :
      (coprodForest f).filter (fun pr => pr.1.isEmpty) = [([], f)] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyL t
      have hts := coprodForest_filter_emptyL ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyL_tmul, ht, hts]
      simp [tmul]
end

/-- Split a mapped `List.sum` by a boolean predicate. -/
theorem _root_.CK.map_sum_filter_split {α : Type*} (L : List α) (P : α → Bool)
    (g : α → H k) :
    (L.map g).sum
      = ((L.filter P).map g).sum + ((L.filter (fun x => !P x)).map g).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact (List.Perm.map g (List.filter_append_perm P L).symm).sum_eq

/-- **Left convolution axiom** on a basis forest: `(S ⋆ id)(f) = ε(f)·1`. Near-definitional. -/
theorem _root_.CK.leftConvF (f : Forest) :
    ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF, one_mul, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.2.isEmpty)
          (g := fun pr => antipodeF k pr.1 * sf k pr.2),
        coprodForest_filter_emptyR]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, mul_one]
    rw [εmon_cons, zero_smul, antipodeF_cons]
    abel

/-- `μ ∘ (S ⊗ id)` on a pure 2-tensor `e2 (p,r)` gives `S(p)·r`. -/
theorem _root_.CK.mul_rTensor_antipode_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (e2 k pr))
      = antipodeF k pr.1 * sf k pr.2 := by
  rw [e2, LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_single, one_smul]
  rfl

/-- `μ ∘ (S ⊗ id) ∘ Δ` on a basis forest equals `ε(f)·1` (left antipode identity). -/
theorem _root_.CK.rTensor_antipode_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum from ?_]
  · exact leftConvF k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_rTensor_antipode_e2 k pr

/-! ### Mirror (right) antipode `S'`, satisfying `id ⋆ S' = η∘ε`. -/

/-- The right antipode by well-founded recursion on node count.
    `S'(∅) = 1`; `S'(f) = -Σ_{(p,r) cut, p ≠ ∅} p·S'(r)`. Decreases since `|r| < |f|`. -/
noncomputable def _root_.CK.antipodeF' : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).attach.map
        (fun pr => sf k pr.val.1 * antipodeF' pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hp : pr.val.1 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hp
  have hlt : sizeF pr.val.2 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

theorem _root_.CK.antipodeF'_cons (t : RTree) (ts : Forest) :
    antipodeF' k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).map
          (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum := by
  conv_lhs => rw [antipodeF']
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- Right convolution `id ⋆ S'` on a basis forest equals `ε(f)·1`. Near-definitional. -/
theorem _root_.CK.rightConvF' (f : Forest) :
    ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF', mul_one, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.1.isEmpty)
          (g := fun pr => sf k pr.1 * antipodeF' k pr.2),
        coprodForest_filter_emptyL]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, one_mul]
    rw [εmon_cons, zero_smul, antipodeF'_cons]
    abel

/-- The mirrored antipode candidate used to prove the right convolution identity. -/
noncomputable def _root_.CK.antipode' : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF' k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.antipode'_single (f : Forest) (b : k) :
    antipode' k (MonoidAlgebra.single f b) = b • antipodeF' k f := by
  change Finsupp.linearCombination k (antipodeF' k) (Finsupp.single f b) = b • antipodeF' k f
  rw [Finsupp.linearCombination_single]

theorem _root_.CK.mul_lTensor_antipode'_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (e2 k pr))
      = sf k pr.1 * antipodeF' k pr.2 := by
  rw [e2, LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode'_single, one_smul]
  rfl

/-- `μ ∘ (id ⊗ S') ∘ Δ` on a basis forest equals `ε(f)·1` (right antipode identity). -/
theorem _root_.CK.lTensor_antipode'_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum from ?_]
  · exact rightConvF' k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_lTensor_antipode'_e2 k pr

/-- Left antipode identity as a linear-map equality (the Hopf left axiom). -/
theorem _root_.CK.leftAntipode_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply CK.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.rTensor (H k) (antipode k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (Δ₀ k f))
        = εmon k f • (1 : H k) from rTensor_antipode_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-- Right antipode identity for `S'` as a linear-map equality. -/
theorem _root_.CK.rightAntipode'_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply CK.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.lTensor (H k) (antipode' k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (Δ₀ k f))
        = εmon k f • (1 : H k) from lTensor_antipode'_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-- The left and right antipodes coincide (a left convolution-inverse of `id` that has
    a right convolution-inverse must equal it — pure monoid algebra in `WithConv`). -/
theorem _root_.CK.antipode_eq_antipode' : antipode k = antipode' k := by
  have hSI : WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k))
      = 1 := by
    apply WithConv.ext
    rw [LinearMap.convMul_def]
    exact leftAntipode_eq k
  have hIS' : WithConv.toConv (LinearMap.id (R := k) (M := H k)) * WithConv.toConv (antipode' k)
      = 1 := by
    apply WithConv.ext
    rw [LinearMap.convMul_def]
    exact rightAntipode'_eq k
  have key : WithConv.toConv (antipode k) = WithConv.toConv (antipode' k) := by
    calc WithConv.toConv (antipode k)
        = WithConv.toConv (antipode k) * 1 := (mul_one _).symm
      _ = WithConv.toConv (antipode k)
            * (WithConv.toConv (LinearMap.id (R := k) (M := H k)) *
                WithConv.toConv (antipode' k)) := by
            rw [hIS']
      _ = (WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k)))
            * WithConv.toConv (antipode' k) := (mul_assoc _ _ _).symm
      _ = 1 * WithConv.toConv (antipode' k) := by rw [hSI]
      _ = WithConv.toConv (antipode' k) := one_mul _
  simp_all

noncomputable instance : HopfAlgebraStruct k (H k) where
  antipode := antipode k

noncomputable instance _root_.CK.instCKHopf : HopfAlgebra k (H k) where
  mul_antipode_rTensor_comul := leftAntipode_eq k
  mul_antipode_lTensor_comul := by
    change LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode k) ∘ₗ Δ k
        = Algebra.linearMap k (H k) ∘ₗ ε k
    rw [antipode_eq_antipode']
    exact rightAntipode'_eq k

/-! ### Adams operators `Ψₙ = id^{⋆n}` and the antipode as `Ψ₋₁`.

    The convolution ring `WithConv (H k →ₗ[k] H k)` (Mathlib `LinearMap.convRing`) turns the
    identity into a ring element whose convolution powers are the Adams (Hopf-power) operators.
    `Ψ₀ = u∘ε` (the convolution unit), `Ψ₁ = id`, the semigroup law `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`, and the
    identity is a convolution UNIT whose inverse is the antipode — i.e. `Ψ₋₁ = S`. This is the
    first combinatorial-Hopf Adams-operator layer in any ITP (Aguiar–Lauve theory; the Eulerian
    idempotent `e⁽¹⁾ = log_⋆ id` is the heavier next step, needing connected-graded nilpotence). -/

/-- The `n`-th Adams operator `Ψₙ = id^{⋆n}`: the `n`-th convolution power of the identity in the
    convolution ring `WithConv (H k →ₗ[k] H k)`. -/
noncomputable def _root_.CK.adams (n : ℕ) : H k →ₗ[k] H k :=
  ((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n).ofConv

theorem _root_.CK.toConv_adams (n : ℕ) :
    WithConv.toConv (adams k n)
      = (WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n :=
  WithConv.toConv_ofConv _

/-- `Ψ₀ = u∘ε` is the convolution unit. -/
@[simp] theorem _root_.CK.toConv_adams_zero : WithConv.toConv (adams k 0) = 1 := by
  rw [toConv_adams, pow_zero]

/-- `Ψ₁ = id`. -/
@[simp] theorem _root_.CK.adams_one : adams k 1 = LinearMap.id (R := k) (M := H k) := by
  rw [adams, pow_one, WithConv.ofConv_toConv]

/-- The convolution-power semigroup law `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`. -/
theorem _root_.CK.toConv_adams_add (m n : ℕ) :
    WithConv.toConv (adams k (m + n))
      = WithConv.toConv (adams k m) * WithConv.toConv (adams k n) := by
  rw [toConv_adams, toConv_adams, toConv_adams, pow_add]

/-- `S ⋆ id = u∘ε`: the antipode is a left convolution inverse of `Ψ₁ = id`. -/
theorem _root_.CK.antipode_convMul_id :
    WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k)) = 1 := by
  apply WithConv.ext
  rw [LinearMap.convMul_def]
  exact leftAntipode_eq k

/-- `id ⋆ S = u∘ε`: the antipode is also a right convolution inverse of `Ψ₁ = id`. -/
theorem _root_.CK.id_convMul_antipode :
    WithConv.toConv (LinearMap.id (R := k) (M := H k)) * WithConv.toConv (antipode k) = 1 := by
  rw [antipode_eq_antipode']
  apply WithConv.ext
  rw [LinearMap.convMul_def]
  exact rightAntipode'_eq k

/-- `Ψ₁ = id` is a convolution UNIT, with the antipode as its (two-sided) inverse. This is the
    precise sense in which `Ψ₋₁ = S`. -/
noncomputable def _root_.CK.adamsUnit : (WithConv (H k →ₗ[k] H k))ˣ where
  val := WithConv.toConv (LinearMap.id (R := k) (M := H k))
  inv := WithConv.toConv (antipode k)
  val_inv := id_convMul_antipode k
  inv_val := antipode_convMul_id k

/-- `Ψ₋₁ = S`: the inverse of the Adams unit `Ψ₁` is the antipode. -/
theorem _root_.CK.adamsUnit_inv_val : (adamsUnit k)⁻¹.val = WithConv.toConv (antipode k) := rfl

/-! ### Part 2 — local nilpotency of `J = id − u∘ε` (the connected-graded engine for `log_⋆`).

    `J` kills the empty forest and is the identity on nonempty ones. Its convolution powers
    `J^{⋆k}` vanish on every basis forest of fewer than `k` nodes (`Jc_pow_ofConv_sf_eq_zero`):
    each of the `k` convolution factors must absorb at least one node, so `k` nodes are needed.
    Hence the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is finite in each degree — the
    connected-graded local nilpotency on which the Aguiar–Lauve Eulerian spectrum rests. -/

/-- `Δ` on a basis forest, packaged for `sf`. -/
theorem _root_.CK.Δ_sf (f : Forest) : Δ k (sf k f) = Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f (1 : k)) = Δ₀ k f
  rw [Finsupp.linearCombination_single, one_smul]

/-- `ε` on a basis forest: the counit of `sf f` is `εmon f`. -/
theorem _root_.CK.ε_sf (p : Forest) : ε k (sf k p) = εmon k p := by
  have h := ε_single k p 1
  rw [one_mul] at h
  exact h

/-- `μ ∘ (F ⊗ G)` on a pure cut-tensor `e2 (p,r)` is `F(p)·G(r)`. -/
theorem _root_.CK.mul_map_e2 (F G : H k →ₗ[k] H k) (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (TensorProduct.map F G (e2 k pr))
      = F (sf k pr.1) * G (sf k pr.2) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

/-- `comul` on a basis forest equals the combinatorial `Δ₀`. -/
theorem _root_.CK.comul_sf (f : Forest) :
    (Coalgebra.comul (R := k) (A := H k)) (sf k f) = Δ₀ k f := Δ_sf k f

/-- **Convolution-on-basis engine.** `(F ⋆ G)` on a basis forest is the sum over cuts:
    `(F ⋆ G)(f) = Σ_{(p,r) ∈ coprodForest f} F(p)·G(r)`. Reusable for all of Part 2. -/
theorem _root_.CK.conv_ofConv_sf (F G : H k →ₗ[k] H k) (f : Forest) :
    (WithConv.toConv F * WithConv.toConv G).ofConv (sf k f)
      = ((coprodForest f).map (fun pr => F (sf k pr.1) * G (sf k pr.2))).sum := by
  rw [LinearMap.convMul_def]
  change LinearMap.mul' k (H k) (TensorProduct.map F G (Coalgebra.comul (R := k) (sf k f))) = _
  rw [comul_sf, Δ₀,
      show LinearMap.mul' k (H k) (TensorProduct.map F G (((coprodForest f).map (e2 k)).sum))
        = (LinearMap.mul' k (H k) ∘ₗ TensorProduct.map F G) (((coprodForest f).map (e2 k)).sum)
        from rfl,
      linmap_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  rw [LinearMap.comp_apply]
  exact mul_map_e2 k F G pr

/-- The augmentation projector `J = id − u∘ε`, as an element of the convolution ring. -/
noncomputable def _root_.CK.Jc : WithConv (H k →ₗ[k] H k) := WithConv.toConv LinearMap.id - 1

/-- The convolution unit `1 = u∘ε` on a basis forest: `ε(f)·1`. -/
theorem _root_.CK.convOne_ofConv_sf (p : Forest) :
    (1 : WithConv (H k →ₗ[k] H k)).ofConv (sf k p) = εmon k p • (1 : H k) := by
  rw [LinearMap.convOne_def]
  change
    (Algebra.linearMap k (H k) ∘ₗ Coalgebra.counit (R := k)) (sf k p)
      = εmon k p • (1 : H k)
  rw [LinearMap.comp_apply]
  change Algebra.linearMap k (H k) (ε k (sf k p)) = εmon k p • (1 : H k)
  rw [ε_sf, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

/-- `J = id − u∘ε` on a basis forest: kills the empty forest, identity otherwise. -/
theorem _root_.CK.Jc_ofConv_sf (p : Forest) :
    (Jc k).ofConv (sf k p) = sf k p - εmon k p • (1 : H k) := by
  rw [Jc, WithConv.ofConv_sub, LinearMap.sub_apply, WithConv.ofConv_toConv,
      LinearMap.id_apply, convOne_ofConv_sf]

/-- **Local nilpotency.** `J^{⋆n} = (id − u∘ε)^{⋆n}` vanishes on every basis forest with fewer
    than `n` nodes. Proof: induction on `n` via the convolution engine and degree conservation;
    in a nonzero cut the left leg carries ≥1 node, so the right leg has `< n−1` nodes and the
    induction hypothesis kills it, while an empty left leg is killed by `J` directly. -/
theorem _root_.CK.Jc_pow_ofConv_sf_eq_zero :
    ∀ (n : ℕ) (f : Forest), sizeF f < n → ((Jc k) ^ n).ofConv (sf k f) = 0 := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd hf (Nat.not_lt_zero _)
  | succ m ih =>
    intro f hf
    have hrec : ((Jc k) ^ (m + 1)).ofConv (sf k f)
        = ((coprodForest f).map (fun pr =>
            (Jc k).ofConv (sf k pr.1) * ((Jc k) ^ m).ofConv (sf k pr.2))).sum := by
      have hsplit : (Jc k) ^ (m + 1)
          = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ m).ofConv) := by
        rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]
        exact pow_succ' _ _
      rw [hsplit, conv_ofConv_sf]
    rw [hrec]
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨pr, hpr, rfl⟩ := hx
    obtain ⟨p, r⟩ := pr
    have hcons := size_consForest f (p, r) hpr
    by_cases hp : p = []
    · subst hp
      rw [Jc_ofConv_sf, sf_nil, εmon_nil, one_smul, sub_self, zero_mul]
    · have hpos : 0 < sizeF p := sizeF_pos hp
      have hr : sizeF r < m := by simp only at hcons ⊢; omega
      rw [ih r hr, mul_zero]

/-! ### The Adams eigenvalue on primitives: `Ψₙ(x) = n·x` for primitive `x`.

    The first piece of the Aguiar–Lauve spectrum, valid on ANY connected graded bialgebra (no
    commutativity needed): the primitives are the eigenspace of every Adams operator `Ψₙ` with
    eigenvalue `n`. Proof is at the element level (not the basis): on a primitive `x`, the recursion
    `Ψₙ₊₁ = id ⋆ Ψₙ` and `Δx = x⊗1 + 1⊗x` give `Ψₙ₊₁(x) = x + Ψₙ(x)`, and `Ψₙ` fixes the unit. -/

/-- A primitive element: `Δx = x⊗1 + 1⊗x`. -/
def _root_.CK.IsPrimitive (x : H k) : Prop := Δ k x = x ⊗ₜ[k] (1 : H k) + (1 : H k) ⊗ₜ[k] x

/-- Convolution at the element level: `(F ⋆ G)(x) = μ((F⊗G)(Δx))`. -/
theorem _root_.CK.conv_apply (F G : H k →ₗ[k] H k) (x : H k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (H k) (TensorProduct.map F G (Δ k x)) := by
  rw [LinearMap.convMul_def]; rfl

/-- `Δ(1) = 1⊗1` (the unit is grouplike), in pure-tensor form. -/
theorem _root_.CK.Δ_one_tmul : Δ k (1 : H k) = (1 : H k) ⊗ₜ[k] (1 : H k) := by
  rw [Δ_one, Algebra.TensorProduct.one_def]

/-- `Ψₙ₊₁ = id ⋆ Ψₙ` evaluated: `Ψₙ₊₁(x) = μ((id⊗Ψₙ)(Δx))`. -/
theorem _root_.CK.adams_succ_apply (n : ℕ) (x : H k) :
    adams k (n + 1) x
      = LinearMap.mul' k (H k) (TensorProduct.map LinearMap.id (adams k n) (Δ k x)) := by
  change (((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ (n + 1)).ofConv) x = _
  rw [pow_succ',
      show (WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n
        = WithConv.toConv (adams k n) from rfl]
  exact conv_apply k LinearMap.id (adams k n) x

/-- Every Adams operator fixes the unit: `Ψₙ(1) = 1`. -/
theorem _root_.CK.adams_unit (n : ℕ) : adams k n (1 : H k) = 1 := by
  induction n with
  | zero =>
    change ((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ 0).ofConv (1 : H k) = 1
    rw [pow_zero]
    have h := convOne_ofConv_sf k []
    simp_all
  | succ m ih =>
    rw [adams_succ_apply, Δ_one_tmul, TensorProduct.map_tmul, LinearMap.id_apply, ih,
        LinearMap.mul'_apply, one_mul]

/-- **Adams eigenvalue on primitives**: for primitive `x`, `Ψₙ₊₁(x) = (n+1)·x`. The
    primitives are the eigenspace of `Ψₙ` with eigenvalue `n`, and `S = Ψ₋₁` acts as `−1`,
    recovering `S(x) = −x`. -/
theorem _root_.CK.adams_primitive (n : ℕ) {x : H k} (hx : IsPrimitive k x) :
    adams k (n + 1) x = (n + 1) • x := by
  induction n with
  | zero => simp [adams_one]
  | succ m ih =>
    rw [adams_succ_apply, hx, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearMap.id_apply, adams_unit, map_add, LinearMap.mul'_apply,
        LinearMap.mul'_apply, mul_one, one_mul, ih]
    conv_rhs => rw [succ_nsmul]
    exact add_comm _ _

/-! ### The first Eulerian idempotent `e⁽¹⁾ = log_⋆(id)` as a linear map.

    Over a `ℚ`-algebra the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is, by the local
    nilpotency above, finite on each basis forest (only `k ≤ |f|` contribute). We define `e⁽¹⁾`
    by that finite per-degree sum, mirroring how `Δ` and the antipode are defined on the basis.
    `e⁽¹⁾` kills the unit and fixes primitives (eigenvalue `1`) — the connected-graded projector
    onto primitives that begins the Aguiar–Lauve spectral decomposition. -/

variable [Algebra ℚ k]

/-- Coefficient `(-1)^{j+1}/j` of the convolution-log series, pushed into `k`. `j = 0 ↦ 0`. -/
noncomputable def _root_.CK.eulerCoef (j : ℕ) : k := algebraMap ℚ k ((-1) ^ (j + 1) / (j : ℚ))

@[simp] theorem _root_.CK.eulerCoef_zero : eulerCoef k 0 = 0 := by
  simp [eulerCoef]

@[simp] theorem _root_.CK.eulerCoef_one : eulerCoef k 1 = 1 := by
  simp [eulerCoef]

/-- `e⁽¹⁾` on a basis forest: the finite log series `Σ_{j=0}^{|f|} ((-1)^{j+1}/j)·J^{⋆j}(f)`
    (the `j=0` term is `0`; terms with `j > |f|` are absent — and would vanish anyway). -/
noncomputable def _root_.CK.eulerian1F (f : Forest) : H k :=
  ((List.range (sizeF f + 1)).map
    (fun j => eulerCoef k j • ((Jc k ^ j).ofConv (sf k f)))).sum

/-- The first Eulerian idempotent `e⁽¹⁾ : H → H`, linear extension of `eulerian1F`. -/
noncomputable def _root_.CK.eulerian1 : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (eulerian1F k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem _root_.CK.eulerian1_sf (f : Forest) : eulerian1 k (sf k f) = eulerian1F k f := by
  change Finsupp.linearCombination k (eulerian1F k) (Finsupp.single f (1 : k)) = eulerian1F k f
  rw [Finsupp.linearCombination_single, one_smul]

/-- `e⁽¹⁾` kills the unit: there are no positive-degree terms on the empty forest. -/
@[simp] theorem _root_.CK.eulerian1_one : eulerian1 k (1 : H k) = 0 := by
  rw [show (1 : H k) = sf k [] from (sf_nil k).symm, eulerian1_sf, eulerian1F,
      show sizeF ([] : Forest) = 0 from rfl]
  simp [List.range_succ, List.range_zero, eulerCoef_zero]

/-- `e⁽¹⁾` fixes the generating primitive `•` (eigenvalue `1`): only the `j=1` term survives,
    with coefficient `1`, and `J(•) = •`. -/
theorem _root_.CK.eulerian1_dot : eulerian1 k (sf k [RTree.node []]) = sf k [RTree.node []] := by
  rw [eulerian1_sf, eulerian1F, show sizeF [RTree.node []] = 1 from rfl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.map_append, List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add,
    eulerCoef_zero, eulerCoef_one, zero_smul, one_smul]
  rw [pow_one, Jc_ofConv_sf, εmon_cons, zero_smul, sub_zero]

/-- **Idempotency on the primitive `•`**: `e⁽¹⁾(e⁽¹⁾ •) = e⁽¹⁾ •`. Immediate from `eulerian1_dot`
    (since `e⁽¹⁾` fixes `•`); likewise `e⁽¹⁾` is idempotent on anything it fixes or kills.

    NOTE (honest scope): the GENERAL projector identity `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` is **false** on this
    *planar* (Foissy) Hopf algebra — it is neither commutative nor cocommutative, and the Eulerian
    idempotents are orthogonal idempotents only in the (co)commutative case (Patras, Loday).
    Explicit
    counterexample (verified numerically in `ConnesKreimerEval.lean`): on the cherry, `e⁽¹⁾∘e⁽¹⁾`
    and `e⁽¹⁾` differ in the `•·ℓ₂` vs `ℓ₂·•` terms — exactly the planar non-commutativity. Genuine
    idempotency (the Hodge/Eulerian decomposition) lives on the commutative quotient (`A2` in the
    seam), not here. -/
theorem _root_.CK.eulerian1_idem_dot :
    eulerian1 k (eulerian1 k (sf k [RTree.node []])) = eulerian1 k (sf k [RTree.node []]) := by
  simp only [eulerian1_dot]

/-! ### `e⁽¹⁾` fixes every primitive (Phase 1: the element-level primitive facts).
    For primitive `x`: `ε(x)=0`, `J(x)=x`, and `J^{⋆k}(x)=0` for `k ≥ 2` (each higher factor must
    absorb the unit, which `J` kills). These feed the operator identity in Phase 2. -/

omit [Algebra ℚ k] in
/-- A primitive element has zero counit (forced by the counit axiom `(ε⊗id)∘Δ = 1⊗·`). -/
theorem _root_.CK.IsPrimitive.counit_zero {x : H k} (hx : IsPrimitive k x) : ε k x = 0 := by
  have hc : LinearMap.rTensor (H k) (ε k) (Δ k x) = (1 : k) ⊗ₜ[k] x :=
    Coalgebra.rTensor_counit_comul (R := k) (A := H k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil]] at hc
  have ha : (ε k x) ⊗ₜ[k] (1 : H k) = 0 := by
    simp_all
  have h1 : ε k x • (1 : H k) = 0 := by
    have := congrArg (TensorProduct.lid k (H k)) ha; simpa using this
  have h2 := congrArg (ε k) h1
  rwa [map_smul, map_zero, show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil],
       smul_eq_mul, mul_one] at h2

omit [Algebra ℚ k] in
/-- `J = id − u∘ε` at the element level: `J(x) = x − ε(x)·1`. -/
theorem _root_.CK.Jc_ofConv_apply (x : H k) : (Jc k).ofConv x = x - ε k x • (1 : H k) := by
  rw [Jc, WithConv.ofConv_sub, LinearMap.sub_apply, WithConv.ofConv_toConv, LinearMap.id_apply]
  congr 1
  rw [LinearMap.convOne_def]
  change Algebra.linearMap k (H k) (ε k x) = ε k x • (1 : H k)
  rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

omit [Algebra ℚ k] in
/-- `J` kills the unit. -/
theorem _root_.CK.Jc_ofConv_one : (Jc k).ofConv (1 : H k) = 0 := by
  rw [Jc_ofConv_apply,
    show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil],
    one_smul, sub_self]

omit [Algebra ℚ k] in
/-- `J^{⋆(j+1)}` kills the unit (the first factor `J(1)=0`). -/
theorem _root_.CK.Jc_pow_succ_ofConv_one (j : ℕ) : ((Jc k) ^ (j + 1)).ofConv (1 : H k) = 0 := by
  have hsplit : (Jc k) ^ (j + 1)
      = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ j).ofConv) := by
    rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]; exact pow_succ' _ _
  rw [hsplit, conv_apply, Δ_one_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      Jc_ofConv_one, zero_mul]

omit [Algebra ℚ k] in
/-- `J` fixes a primitive: `J(x) = x`. -/
theorem _root_.CK.Jc_ofConv_primitive {x : H k} (hx : IsPrimitive k x) : (Jc k).ofConv x = x := by
  rw [Jc_ofConv_apply, hx.counit_zero, zero_smul, sub_zero]

omit [Algebra ℚ k] in
/-- `J^{⋆(k+2)}` kills a primitive: each of the two top factors absorbs the unit (`J(1)=0`). -/
theorem _root_.CK.Jc_pow_ofConv_primitive {x : H k} (hx : IsPrimitive k x) (j : ℕ) :
    ((Jc k) ^ (j + 2)).ofConv x = 0 := by
  have hsplit : (Jc k) ^ (j + 2)
      = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ (j + 1)).ofConv) := by
    rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]; exact pow_succ' _ _
  rw [hsplit, conv_apply, hx, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add,
      LinearMap.mul'_apply, LinearMap.mul'_apply, Jc_pow_succ_ofConv_one, Jc_ofConv_one,
      mul_zero, zero_mul, add_zero]

/-! ### `e⁽¹⁾` fixes every primitive (Phase 2: assembling the operator identity).
    `e⁽¹⁾` agrees on degree-`≤N` elements with the finite truncation `Σ_{j≤N} c_j J^{⋆j}` (extra
    terms vanish by nilpotency); on a primitive only the `j=1` term survives, giving `e⁽¹⁾(x)=x`. -/

/-- Bridge: a `List.range` map-sum equals the corresponding `Finset.range` sum. -/
theorem _root_.CK.list_range_sum_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    ((List.range m).map g).sum = ∑ j ∈ Finset.range m, g j := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The degree-`N` truncation of `log_⋆(id)`, as a linear map. -/
noncomputable def _root_.CK.logTrunc (N : ℕ) : H k →ₗ[k] H k :=
  ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv)

theorem _root_.CK.logTrunc_apply (N : ℕ) (y : H k) :
    logTrunc k N y = ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv y) := by
  simp [logTrunc, LinearMap.sum_apply, LinearMap.smul_apply]

/-- On a basis forest of degree `≤ N`, `e⁽¹⁾` equals the degree-`N` truncation (nilpotency kills
    the surplus terms). -/
theorem _root_.CK.eulerian1F_eq_logTrunc (f : Forest) (N : ℕ) (h : sizeF f ≤ N) :
    eulerian1F k f = logTrunc k N (sf k f) := by
  rw [eulerian1F, list_range_sum_eq, logTrunc_apply]
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hjnot => ?_)
  · rw [Finset.mem_range] at hj ⊢; omega
  · rw [Finset.mem_range, not_lt] at hjnot
    rw [Jc_pow_ofConv_sf_eq_zero k j f (by omega), smul_zero]

omit [Algebra ℚ k] in
/-- A linear endomorphism of `H` is the basis-sum of its values on the singletons (proved by
    `exact`, sidestepping the `MonoidAlgebra`/`Finsupp` syntactic wall in `rw`). -/
theorem _root_.CK.lmap_eq_sum (g : H k →ₗ[k] H k) (y : H k) :
    g y = y.coeff.sum (fun a b => g (MonoidAlgebra.single a b)) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single y]
  exact map_finsuppSum g y.coeff MonoidAlgebra.single

/-- `e⁽¹⁾` agrees with the truncation `logTrunc N` on any element supported in degrees `≤ N`. -/
theorem _root_.CK.eulerian1_eq_logTrunc (x : H k) (N : ℕ)
    (hN : ∀ f ∈ x.coeff.support, sizeF f ≤ N) :
    eulerian1 k x = logTrunc k N x := by
  rw [lmap_eq_sum k (eulerian1 k) x, lmap_eq_sum k (logTrunc k N) x]
  refine Finsupp.sum_congr (fun a ha => ?_)
  have hsf : (MonoidAlgebra.single a (x.coeff a) : H k)
      = (x.coeff a) • sf k (FreeMonoid.toList a) := by
    rw [sf, FreeMonoid.ofList_toList]
    exact single_smul_one (k := k) (f := a) (b := x.coeff a)
  rw [hsf, map_smul, map_smul, eulerian1_sf,
      eulerian1F_eq_logTrunc k (FreeMonoid.toList a) N (hN a ha)]

/-- **`e⁽¹⁾` fixes every primitive**: `e⁽¹⁾(x) = x` for primitive `x`. Only the `j=1` term of the
    log series survives (`J(x)=x`; `j=0` has coefficient `0`; `j≥2` vanish), so `e⁽¹⁾(x)=x`. The
    primitives are exactly the eigenvalue-`1` eigenspace of `e⁽¹⁾`. -/
theorem _root_.CK.eulerian1_primitive {x : H k} (hx : IsPrimitive k x) : eulerian1 k x = x := by
  set N := x.coeff.support.sup sizeF + 1 with hNdef
  have hbound : ∀ f ∈ x.coeff.support, sizeF f ≤ N := by
    intro f hf
    exact le_trans (Finset.le_sup (f := sizeF) hf) (by rw [hNdef]; exact Nat.le_succ _)
  rw [eulerian1_eq_logTrunc k x N hbound, logTrunc_apply]
  have key : ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv x)
      = eulerCoef k 1 • ((Jc k ^ 1).ofConv x) := by
    refine Finset.sum_eq_single 1 (fun j _ hj1 => ?_) (fun h1 => ?_)
    · rcases j with _ | _ | j
      · rw [eulerCoef_zero, zero_smul]
      · exact absurd rfl hj1
      · rw [Jc_pow_ofConv_primitive k hx j, smul_zero]
    · rw [Finset.mem_range, not_lt] at h1; omega
  rw [key, eulerCoef_one, one_smul, pow_one, Jc_ofConv_primitive k hx]

/-! ### A2 — the commutative quotient `H_ab = H / ⟨ab − ba⟩`
    (Foissy's planar → commutative map).

    Abelianizing the (forest) product turns the planar Hopf algebra into a commutative one. This is
    the algebra step (S1): the quotient ring `RingQuot` by the commutator relation, shown
    commutative.
    The coproduct, counit and antipode descend in the following stones, giving the classical
    (commutative) Connes–Kreimer / Butcher Hopf algebra, where the Eulerian idempotents become
    genuine orthogonal idempotents. -/

/-- The commutator relation `x·y ∼ y·x` on `H`. -/
inductive _root_.CK.commRel : H k → H k → Prop
  | mul (x y : H k) : commRel (x * y) (y * x)

/-- The commutative quotient `H_ab = H / ⟨ab − ba⟩`. -/
abbrev _root_.CK.Hab : Type _ := RingQuot (commRel k)

/-- The quotient algebra map `π : H → H_ab`. -/
noncomputable def _root_.CK.π : H k →ₐ[k] Hab k := RingQuot.mkAlgHom k (commRel k)

/-- `H_ab` is commutative: the relation forces `π(x)·π(y) = π(y)·x`. -/
noncomputable instance : CommRing (Hab k) where
  __ := (inferInstance : Ring (RingQuot (commRel k)))
  mul_comm a b := by
    obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) a
    obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) b
    rw [← map_mul, ← map_mul]
    exact RingQuot.mkAlgHom_rel k (commRel.mul x y)

omit [Algebra ℚ k] in
theorem _root_.CK.π_surjective : Function.Surjective (π k) :=
  RingQuot.mkAlgHom_surjective k (commRel k)

omit [Algebra ℚ k] in
theorem _root_.CK.π_mul_comm (x y : H k) : π k (x * y) = π k (y * x) :=
  RingQuot.mkAlgHom_rel k (commRel.mul x y)

/-! #### S2 — the coproduct descends to `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/

/-- `Δ` as an algebra homomorphism (the bialgebra coproduct), from `Δ_one` and `Δ_mul`. -/
noncomputable def _root_.CK.ΔAlg : H k →ₐ[k] H k ⊗[k] H k :=
  AlgHom.ofLinearMap (Δ k) (Δ_one k) (Δ_mul k)

omit [Algebra ℚ k] in
/-- `(π⊗π)∘Δ` respects the commutator relation, since `H_ab ⊗ H_ab` is commutative. -/
theorem _root_.CK.ΔAlg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) a
      = (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended coproduct `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/
noncomputable def _root_.CK.Δab : Hab k →ₐ[k] Hab k ⊗[k] Hab k :=
  RingQuot.liftAlgHom k
    ⟨(Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k), ΔAlg_resp_commRel k⟩

omit [Algebra ℚ k] in
/-- The descent square commutes: `Delta_ab ∘ π = (π⊗π) ∘ Δ`. -/
theorem _root_.CK.Δab_π (x : H k) :
    Δab k (π k x) = Algebra.TensorProduct.map (π k) (π k) (ΔAlg k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (ΔAlg_resp_commRel k) x

/-! #### S3 — the counit descends to `epsilon_ab : H_ab → k`. -/

omit [Algebra ℚ k] in
/-- `ε` respects the commutator relation (`k` is commutative). -/
theorem _root_.CK.εalg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    εalg k a = εalg k b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended counit `epsilon_ab : H_ab → k`. -/
noncomputable def _root_.CK.εab : Hab k →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨εalg k, εalg_resp_commRel k⟩

omit [Algebra ℚ k] in
theorem _root_.CK.εab_π (x : H k) : εab k (π k x) = εalg k x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (εalg_resp_commRel k) x

/-! #### S4 — `H_ab` is a coalgebra (coassoc + counit laws descend through `π`). -/

omit [Algebra ℚ k] in
/-- Extensionality on `H_ab`: a linear map out of `H_ab` is determined by its values on `π`. -/
theorem _root_.CK.Hab_lhom_ext {M : Type*} [AddCommMonoid M] [Module k M]
    {g₁ g₂ : Hab k →ₗ[k] M} (h : ∀ x : H k, g₁ (π k x) = g₂ (π k x)) :
    g₁ = g₂ := by
  ext u
  obtain ⟨x, rfl⟩ := π_surjective k u
  exact h x

omit [Algebra ℚ k] in
/-- `ε` (right) counit naturality: `(epsilon_ab⊗id)∘(π⊗π) = ε⊗π`. -/
theorem _root_.CK.εab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (ε k) (π k).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.rTensor_tmul,
      TensorProduct.map_tmul]
  change εab k (π k a) ⊗ₜ[k] π k b = ε k a ⊗ₜ[k] π k b
  rw [εab_π]; rfl

omit [Algebra ℚ k] in
/-- `ε` (left) counit naturality: `(id⊗epsilon_ab)∘(π⊗π) = π⊗ε`. -/
theorem _root_.CK.εab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (ε k) := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.lTensor_tmul,
      TensorProduct.map_tmul]
  change π k a ⊗ₜ[k] εab k (π k b) = π k a ⊗ₜ[k] ε k b
  rw [εab_π]; rfl

omit [Algebra ℚ k] in
/-- Left counitality on `H_ab`: `(epsilon_ab ⊗ id) ∘ Delta_ab = 1 ⊗ ·`. -/
theorem _root_.CK.rTensor_εab_comp_Δab :
    (LinearMap.rTensor (Hab k) (εab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = TensorProduct.mk k k (Hab k) 1 := by
  have hsplit : TensorProduct.map (ε k) (π k).toLinearMap
      = LinearMap.lTensor k (π k).toLinearMap ∘ₗ LinearMap.rTensor (H k) (ε k) := by
    simp_all
  apply Hab_lhom_ext
  intro x
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Δab_π, ← AlgHom.toLinearMap_apply,
      ← LinearMap.comp_apply,
      εab_rTensor_natural]
  change TensorProduct.map (ε k) (π k).toLinearMap (Δ k x) = (1 : k) ⊗ₜ[k] π k x
  rw [hsplit, LinearMap.comp_apply,
      show LinearMap.rTensor (H k) (ε k) (Δ k x) = (1 : k) ⊗ₜ[k] x from
        Coalgebra.rTensor_counit_comul (R := k) (A := H k) x,
      LinearMap.lTensor_tmul]
  rfl

omit [Algebra ℚ k] in
/-- Right counitality on `H_ab`: `(id ⊗ epsilon_ab) ∘ Delta_ab = · ⊗ 1`. -/
theorem _root_.CK.lTensor_εab_comp_Δab :
    (LinearMap.lTensor (Hab k) (εab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = (TensorProduct.mk k (Hab k) k).flip 1 := by
  have hsplit : TensorProduct.map (π k).toLinearMap (ε k)
      = LinearMap.rTensor k (π k).toLinearMap ∘ₗ LinearMap.lTensor (H k) (ε k) := by
    simp_all
  apply Hab_lhom_ext
  intro x
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Δab_π, ← AlgHom.toLinearMap_apply,
      ← LinearMap.comp_apply,
      εab_lTensor_natural]
  change TensorProduct.map (π k).toLinearMap (ε k) (Δ k x) = π k x ⊗ₜ[k] (1 : k)
  rw [hsplit, LinearMap.comp_apply,
      show LinearMap.lTensor (H k) (ε k) (Δ k x) = x ⊗ₜ[k] (1 : k) from
        Coalgebra.lTensor_counit_comul (R := k) (A := H k) x,
      LinearMap.rTensor_tmul]
  rfl

omit [Algebra ℚ k] in
/-- `Delta_ab ∘ π = (π⊗π) ∘ Δ` in purely linear (TensorProduct.map) form. -/
theorem _root_.CK.Δab_π' (x : H k) :
    Δab k (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  have h : (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap := by
    apply TensorProduct.ext'; simp_all
  rw [Δab_π, ← AlgHom.toLinearMap_apply, h]
  rfl

omit [Algebra ℚ k] in
/-- `Delta_ab ∘ π` in `.toLinearMap` form (for use inside compositions). -/
theorem _root_.CK.Δab_tl_π (x : H k) :
    (Δab k).toLinearMap (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  rw [AlgHom.toLinearMap_apply, Δab_π']

omit [Algebra ℚ k] in
/-- Coproduct (right) naturality for the descent:
    `(Delta_ab⊗id)∘(π⊗π) = ((π⊗π)⊗π)∘(Δ⊗id)`. -/
theorem _root_.CK.Δab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap) (π k).toLinearMap
          ∘ₗ LinearMap.rTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

omit [Algebra ℚ k] in
/-- Coproduct (left) naturality for the descent:
    `(id⊗Delta_ab)∘(π⊗π) = (π⊗(π⊗π))∘(id⊗Δ)`. -/
theorem _root_.CK.Δab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap)
          ∘ₗ LinearMap.lTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

omit [Algebra ℚ k] in
/-- Coassociativity on `H_ab`, descended from the planar coassociativity via `π`. -/
theorem _root_.CK.coassoc_Hab :
    (TensorProduct.assoc k (Hab k) (Hab k) (Hab k)).toLinearMap
        ∘ₗ (LinearMap.rTensor (Hab k) (Δab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = (LinearMap.lTensor (Hab k) (Δab k).toLinearMap) ∘ₗ (Δab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have CP : (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ k x)) = LinearMap.lTensor (H k) (Δ k) (Δ k x) :=
    LinearMap.congr_fun (Coalgebra.coassoc (R := k) (A := H k)) x
  have hR := LinearMap.congr_fun (Δab_rTensor_natural k) (Δ k x)
  have hL := LinearMap.congr_fun (Δab_lTensor_natural k) (Δ k x)
  have hAssoc := LinearMap.congr_fun
    (TensorProduct.map_map_comp_assoc_eq (π k).toLinearMap (π k).toLinearMap (π k).toLinearMap)
    (LinearMap.rTensor (H k) (Δ k) (Δ k x))
  simp only [LinearMap.comp_apply] at hR hL hAssoc ⊢
  rw [Δab_tl_π, hR, hL, ← hAssoc]
  exact congrArg _ CP

/-- `H_ab` is a coalgebra (the commutative Connes–Kreimer coalgebra). -/
noncomputable instance : CoalgebraStruct k (Hab k) where
  comul := (Δab k).toLinearMap
  counit := (εab k).toLinearMap

noncomputable instance _root_.CK.instHabCoalg : Coalgebra k (Hab k) where
  coassoc := coassoc_Hab k
  rTensor_counit_comp_comul := rTensor_εab_comp_Δab k
  lTensor_counit_comp_comul := lTensor_εab_comp_Δab k

/-! ### S5 — `H_ab` is a Bialgebra.
    `Δab`, `εab` are algebra homs by construction, so the four `Bialgebra.mk'`
    compatibilities are just `map_one`/`map_mul` (cf. planar `instCKBialg`, which
    needed a separate `Δ_mul` because there `Δ` was not yet packaged as an AlgHom). -/
noncomputable instance _root_.CK.instHabBialg : Bialgebra k (Hab k) :=
  Bialgebra.mk' k (Hab k)
    (map_one (εab k))
    (fun {a b} => map_mul (εab k) a b)
    (map_one (Δab k))
    (fun {a b} => map_mul (Δab k) a b)

/-! #### S6 — the antipode descends to `S_ab : H_ab → H_ab`, giving `HopfAlgebra k (H_ab)`.

`S = antipode k` is an algebra anti-homomorphism; composing with
`π` into the COMMUTATIVE quotient `H_ab` turns it into a genuine algebra hom, so it lifts
through `RingQuot`. The two antipode axioms then descend through `π` exactly like
coassociativity in S4. -/

/-- `π ∘ S : H → H_ab` as an algebra hom: on the commutative quotient the antipode
    anti-homomorphism becomes a homomorphism (`π(S(ab)) = π(Sb·Sa) = π(Sa)·π(Sb)`). -/
noncomputable def _root_.CK.SalgHom : H k →ₐ[k] Hab k :=
  AlgHom.ofLinearMap ((π k).toLinearMap ∘ₗ antipode k)
    (by
      have h1 : antipode k (1 : H k) = 1 := HopfAlgebra.antipode_one (R := k) (A := H k)
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1, map_one])
    (by
      intro a b
      have hmul : antipode k (a * b) = antipode k b * antipode k a :=
        HopfAlgebra.antipode_mul_antidistrib (R := k) a b
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [hmul, map_mul]
      exact mul_comm _ _)

omit [Algebra ℚ k] in
/-- `π ∘ S` respects the commutator relation (`H_ab` is commutative). -/
theorem _root_.CK.SalgHom_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    SalgHom k a = SalgHom k b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended antipode `S_ab : H_ab → H_ab`. -/
noncomputable def _root_.CK.Sab : Hab k →ₐ[k] Hab k :=
  RingQuot.liftAlgHom k ⟨SalgHom k, SalgHom_resp_commRel k⟩

omit [Algebra ℚ k] in
/-- The descent square: `S_ab ∘ π = π ∘ S`. -/
theorem _root_.CK.Sab_π (x : H k) : Sab k (π k x) = π k (antipode k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (SalgHom_resp_commRel k) x

omit [Algebra ℚ k] in
/-- `mu_ab ∘ (π⊗π) = π ∘ μ` (multiplication naturality, `π` an algebra hom). -/
theorem _root_.CK.mul'_π :
    LinearMap.mul' k (Hab k) ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = (π k).toLinearMap ∘ₗ LinearMap.mul' k (H k) := by
  apply TensorProduct.ext'
  simp_all

omit [Algebra ℚ k] in
/-- Antipode (left) naturality for the descent: `(S_ab⊗id)∘(π⊗π) = (π⊗π)∘(S⊗id)`. -/
theorem _root_.CK.Sab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (Sab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ LinearMap.rTensor (H k) (antipode k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, Sab_π]

omit [Algebra ℚ k] in
/-- Antipode (right) naturality for the descent: `(id⊗S_ab)∘(π⊗π) = (π⊗π)∘(id⊗S)`. -/
theorem _root_.CK.Sab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (Sab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ LinearMap.lTensor (H k) (antipode k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, Sab_π]

omit [Algebra ℚ k] in
/-- The (right-factor) left antipode identity, stated for `antipode k` rather than `antipode' k`
    (`id ⋆ S = u∘ε` re-expressed via `antipode = antipode'`). -/
theorem _root_.CK.lTensor_antipode_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  rw [antipode_eq_antipode']
  exact rightAntipode'_eq k

omit [Algebra ℚ k] in
/-- Left antipode identity on `H_ab`, descended through `π`. -/
theorem _root_.CK.rTensor_Sab_Δab :
    LinearMap.mul' k (Hab k) ∘ₗ LinearMap.rTensor (Hab k) (Sab k).toLinearMap
        ∘ₗ (Δab k).toLinearMap
      = Algebra.linearMap k (Hab k) ∘ₗ (εab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have hLeft := LinearMap.congr_fun (leftAntipode_eq k) x
  have hNat := LinearMap.congr_fun (Sab_rTensor_natural k) (Δ k x)
  have hMul := LinearMap.congr_fun (mul'_π k) (LinearMap.rTensor (H k) (antipode k) (Δ k x))
  simp only [LinearMap.comp_apply] at hLeft hNat hMul ⊢
  rw [Δab_tl_π, hNat, hMul, hLeft]
  change π k (Algebra.linearMap k (H k) (ε k x)) = Algebra.linearMap k (Hab k) (εab k (π k x))
  rw [εab_π]
  exact (π k).commutes (ε k x)

omit [Algebra ℚ k] in
/-- Right antipode identity on `H_ab`, descended through `π`. -/
theorem _root_.CK.lTensor_Sab_Δab :
    LinearMap.mul' k (Hab k) ∘ₗ LinearMap.lTensor (Hab k) (Sab k).toLinearMap
        ∘ₗ (Δab k).toLinearMap
      = Algebra.linearMap k (Hab k) ∘ₗ (εab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have hRight := LinearMap.congr_fun (lTensor_antipode_eq k) x
  have hNat := LinearMap.congr_fun (Sab_lTensor_natural k) (Δ k x)
  have hMul := LinearMap.congr_fun (mul'_π k) (LinearMap.lTensor (H k) (antipode k) (Δ k x))
  simp only [LinearMap.comp_apply] at hRight hNat hMul ⊢
  rw [Δab_tl_π, hNat, hMul, hRight]
  change π k (Algebra.linearMap k (H k) (ε k x)) = Algebra.linearMap k (Hab k) (εab k (π k x))
  rw [εab_π]
  exact (π k).commutes (ε k x)

noncomputable instance : HopfAlgebraStruct k (Hab k) where
  antipode := (Sab k).toLinearMap

/-- `H_ab` is a Hopf algebra: the commutative Connes–Kreimer / Butcher Hopf algebra of
    rooted forests, obtained from the planar one by the abelianization quotient. -/
noncomputable instance _root_.CK.instHabHopf : HopfAlgebra k (Hab k) where
  mul_antipode_rTensor_comul := rTensor_Sab_Δab k
  mul_antipode_lTensor_comul := lTensor_Sab_Δab k

/-! #### Toward the Eulerian-idempotent payoff — Adams operators on `H_ab`.

On the COMMUTATIVE `H_ab` the Eulerian idempotents `e⁽ⁱ⁾` become orthogonal idempotents
(Patras/Loday), so `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` HOLDS (unlike the planar non-idempotency of D1). The
principled route is via the Adams operators `Ψⁿ`: on a commutative Hopf algebra each `Ψⁿ` is an
algebra morphism, whence `Ψᵖ∘Ψq = Ψ^{pq}`, whence the `e⁽ⁱ⁾` are the orthogonal eigen-projectors.

Brick 1 (no commutativity yet): the Adams operators on `H_ab`, and their naturality through `π`
(`Ψⁿ_ab ∘ π = π ∘ Ψⁿ`), which both defines `Ψⁿ_ab` and ties it to the planar `Ψⁿ`. -/

/-- The Adams operators `Ψⁿ = id^{⋆n}` on `H_ab` (convolution powers of the identity). -/
noncomputable def _root_.CK.adamsAb (n : ℕ) : Hab k →ₗ[k] Hab k :=
  ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n).ofConv

omit [Algebra ℚ k] in
/-- Element-level convolution on `H_ab`: `(F⋆G)(x) = mu_ab((F⊗G)(Delta_ab x))`. -/
theorem _root_.CK.conv_apply_ab (F G : Hab k →ₗ[k] Hab k) (x : Hab k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (Hab k) (TensorProduct.map F G ((Δab k).toLinearMap x)) := by
  rw [LinearMap.convMul_def]; rfl

omit [Algebra ℚ k] in
/-- `Ψⁿ⁺¹_ab = id ⋆ Ψⁿ_ab` evaluated. -/
theorem _root_.CK.adamsAb_succ_apply (n : ℕ) (x : Hab k) :
    adamsAb k (n + 1) x
      = LinearMap.mul' k (Hab k)
          (TensorProduct.map LinearMap.id (adamsAb k n) ((Δab k).toLinearMap x)) := by
  change (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ (n + 1)).ofConv) x = _
  rw [pow_succ', show (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n
        = WithConv.toConv (adamsAb k n) from rfl]
  exact conv_apply_ab k LinearMap.id (adamsAb k n) x

omit [Algebra ℚ k] in
/-- **Adams naturality**: `Ψⁿ_ab ∘ π = π ∘ Ψⁿ`. The planar Adams operators descend to `H_ab`
    through the bialgebra quotient map `π`. -/
theorem _root_.CK.adamsAb_natural (n : ℕ) :
    (adamsAb k n) ∘ₗ (π k).toLinearMap = (π k).toLinearMap ∘ₗ (adams k n) := by
  induction n with
  | zero =>
    apply LinearMap.ext; intro x
    change (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv)
        ((π k).toLinearMap x)
      = (π k).toLinearMap (((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ 0).ofConv x)
    rw [pow_zero, pow_zero]
    change (1 : WithConv (Hab k →ₗ[k] Hab k)) ((π k).toLinearMap x)
       = (π k).toLinearMap ((1 : WithConv (H k →ₗ[k] H k)) x)
    rw [LinearMap.convOne_apply, LinearMap.convOne_apply, AlgHom.toLinearMap_apply]
    change algebraMap k (Hab k) (εab k (π k x)) = π k (algebraMap k (H k) (ε k x))
    rw [εab_π]
    exact ((π k).commutes (ε k x)).symm
  | succ m ih =>
    apply LinearMap.ext; intro x
    have hT : TensorProduct.map LinearMap.id (adamsAb k m)
          ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
        = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ TensorProduct.map LinearMap.id (adams k m) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
          LinearMap.comp_id, ih]
    have hTx := LinearMap.congr_fun hT (Δ k x)
    have hMul := LinearMap.congr_fun (mul'_π k)
      (TensorProduct.map LinearMap.id (adams k m) (Δ k x))
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hTx hMul ⊢
    rw [adamsAb_succ_apply, Δab_tl_π, hTx, hMul, adams_succ_apply]

/-! Brick 2 (commutativity enters): each Adams operator `Ψⁿ` is an ALGEBRA morphism on the
    commutative `H_ab`. We package `Ψⁿ` as an `AlgHom` built by composition:
    `Ψⁿ⁺¹ = mu_ab∘(id⊗Ψⁿ)∘Delta_ab`. This is a composite of the algebra homs
    `Delta_ab`, `id⊗Ψⁿ`, and `mu_ab`, and the multiplication is an algebra hom precisely
    because `H_ab` is commutative. -/

/-- `Ψⁿ` packaged as an algebra hom on the commutative `H_ab` (`Ψ₀ = u∘ε`,
    `Ψⁿ⁺¹ = mu_ab ∘ (id ⊗ Ψⁿ) ∘ Delta_ab`). -/
noncomputable def _root_.CK.adamsAbHom : ℕ → (Hab k →ₐ[k] Hab k)
  | 0 => (Algebra.ofId k (Hab k)).comp (εab k)
  | (n + 1) => (Algebra.TensorProduct.lmul' k).comp
      ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom n)).comp (Δab k))

omit [Algebra ℚ k] in
/-- The algebra-hom `Ψⁿ` and the convolution-power `Ψⁿ` agree as linear maps. -/
theorem _root_.CK.adamsAbHom_toLinearMap (n : ℕ) :
    (adamsAbHom k n).toLinearMap = adamsAb k n := by
  induction n with
  | zero =>
    apply LinearMap.ext; intro x
    change (Algebra.ofId k (Hab k)).comp (εab k) x = adamsAb k 0 x
    rw [AlgHom.comp_apply]
    change algebraMap k (Hab k) (εab k x) = adamsAb k 0 x
    rw [show adamsAb k 0
          = ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv from rfl, pow_zero]
    change algebraMap k (Hab k) (εab k x) = (1 : WithConv (Hab k →ₗ[k] Hab k)) x
    rw [LinearMap.convOne_apply]
    rfl
  | succ m ih =>
    apply LinearMap.ext; intro x
    rw [adamsAb_succ_apply]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
        = TensorProduct.map LinearMap.id (adamsAb k m) := by
      apply TensorProduct.ext'
      simp_all
    change Algebra.TensorProduct.lmul' k
        ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
      = LinearMap.mul' k (Hab k)
          (TensorProduct.map LinearMap.id (adamsAb k m) ((Δab k).toLinearMap x))
    rw [show (Algebra.TensorProduct.lmul' k)
            ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
          = LinearMap.mul' k (Hab k)
              ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
                ((Δab k).toLinearMap x)) from rfl,
        e1]

omit [Algebra ℚ k] in
/-- **Brick 2 — `Ψⁿ` is an algebra morphism on `H_ab`**: `Ψⁿ(ab) = Ψⁿ(a)·Ψⁿ(b)`. The key
    commutative-Hopf fact behind the orthogonality of the Eulerian idempotents. -/
theorem _root_.CK.adamsAb_mul (n : ℕ) (a b : Hab k) :
    adamsAb k n (a * b) = adamsAb k n a * adamsAb k n b := by
  rw [← adamsAbHom_toLinearMap]
  simp_all

/-! Brick 3: the Adams composition law `Ψᵖ ∘ Ψq = Ψ^{pq}`. Post-composition by an algebra hom
    distributes over convolution (`LinearMap.algHom_comp_convMul_distrib`), so an algebra-hom
    `φ` post-composed with `Ψᵖ = id^{⋆p}` gives `(φ ∘ id)^{⋆p} = (toConv φ)^p`.
    Taking `φ = Ψq` gives `Ψq ∘ Ψᵖ = (Ψq)^{⋆p} = id^{⋆qp} = Ψ^{qp}`. -/

omit [Algebra ℚ k] in
/-- An algebra hom `φ` post-composed with the Adams operator `Ψᵖ` is the `p`-th convolution power
    of `φ` itself: `φ ∘ Ψᵖ = (toConv φ)^p` in `WithConv`. -/
theorem _root_.CK.algHom_comp_adamsAb (φ : Hab k →ₐ[k] Hab k) (p : ℕ) :
    φ.toLinearMap ∘ₗ adamsAb k p = ((WithConv.toConv φ.toLinearMap) ^ p).ofConv := by
  induction p with
  | zero =>
    change φ.toLinearMap ∘ₗ ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv
       = ((WithConv.toConv φ.toLinearMap) ^ 0).ofConv
    rw [pow_zero, pow_zero]
    apply LinearMap.ext; simp_all
  | succ n ih =>
    change φ.toLinearMap ∘ₗ
        ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ (n + 1)).ofConv
         = ((WithConv.toConv φ.toLinearMap) ^ (n + 1)).ofConv
    rw [pow_succ' (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) n,
        LinearMap.algHom_comp_convMul_distrib, WithConv.ofConv_toConv, LinearMap.comp_id,
        show φ.toLinearMap ∘ₗ
            ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n).ofConv
          = ((WithConv.toConv φ.toLinearMap) ^ n).ofConv from ih,
        WithConv.toConv_ofConv, pow_succ' (WithConv.toConv φ.toLinearMap) n]

omit [Algebra ℚ k] in
/-- **Brick 3 — the Adams composition law `Ψᵖ ∘ Ψq = Ψ^{pq}`** on the commutative `H_ab`. The
    Adams (Hopf-power) operators form a commuting family of algebra endomorphisms realising the
    multiplicative monoid `(ℕ, ·)`; this is the structural reason the Eulerian idempotents are
    orthogonal. -/
theorem _root_.CK.adamsAb_comp (p q : ℕ) :
    adamsAb k p ∘ₗ adamsAb k q = adamsAb k (p * q) := by
  have h := algHom_comp_adamsAb k (adamsAbHom k p) q
  rw [adamsAbHom_toLinearMap] at h
  rw [h, show (WithConv.toConv (adamsAb k p))
        = (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p from
        WithConv.toConv_ofConv _, ← pow_mul]
  rfl

/-! Brick 4 — toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` on the commutative `H_ab`, via the
finite-difference engine.

    The route AVOIDS the full Eulerian decomposition / Vandermonde inversion. The point:
    if `v` is an Adams eigenvector with `Ψⁱ(v) = i·v` for all `i`, then expanding
    `J^{⋆j} = (id − u∘ε)^{⋆j}` into Adams operators and applying to `v` collapses
    each `J^{⋆j}(v)` to a scalar multiple of `v` by the finite-difference identity below.
    Hence `e⁽¹⁾` is the identity on its own image. -/

/-- **Finite-difference engine**: the `j`-th finite difference of the identity sequence `i ↦ i`,
    `∑ᵢ (-1)^{j-i} C(j,i)·i = δ_{j,1}`. This collapses the convolution-log of an
    Adams eigenvector to its weight-1 component, which is the combinatorial heart of the
    Eulerian idempotency on `H_ab`. -/
theorem _root_.CK.alternating_choose_weighted (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), ((-1 : ℤ) ^ (j - i) * (j.choose i) * i)
      = if j = 1 then 1 else 0 := by
  rcases j with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    have hinner : ∀ i ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1)) * ((i + 1 : ℕ) : ℤ))
          = (n + 1 : ℤ) * ((-1 : ℤ) ^ (n - i) * (n.choose i)) := by
      intro i _
      have hc : (((n + 1).choose (i + 1) : ℤ)) * ((i + 1 : ℕ) : ℤ)
          = (n + 1 : ℤ) * (n.choose i) := by
        exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
      rw [show n + 1 - (i + 1) = n - i from by omega, mul_assoc, hc]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - i) * (n.choose i))
        = (0 : ℤ) ^ n := by
      have hap := add_pow (1 : ℤ) (-1) n
      simp_all
    simp only [Nat.cast_zero, mul_zero, add_zero, Nat.sub_zero, hsum]
    rcases n with _ | m
    · simp
    · simp [pow_succ]

/-! Brick B (binomial expansion) — `J_ab^{⋆j}` into Adams operators on the commutative `H_ab`.
    Toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾`: expand the convolution-log's `J^{⋆j}` into the Adams
    basis so that, on an Adams eigenvector, `alternating_choose_weighted` collapses it. -/

-- **Brick B.** On the commutative `H_ab`, the convolution power
-- `J_ab^{⋆j} = (id − u∘ε)^{⋆j}` expands into Adams operators:
-- `(J_ab^j)(x) = Σ_{i=0}^{j} (-1)^{j-i} C(j,i) · Ψⁱ(x)`. Pure ring
-- algebra in the commutative convolution ring (`convCommRing`); no nilpotency needed. The
-- `maxHeartbeats 0` is the documented WithConv `whnf` cost. The proof itself is elementary
-- (`Commute.add_pow` on `id + (-1)`, then `ofConv` linearity per term via the `key` scalar bridge).
omit [Algebra ℚ k] in
theorem _root_.CK.JcAb_pow_ofConv_eq_adams_sum (j : ℕ) (x : Hab k) :
    ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv x
      = ∑ i ∈ Finset.range (j + 1),
          ((-1 : k) ^ (j - i) * (j.choose i : k)) • adamsAb k i x := by
  have hcomm : Commute (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)))
      (-1 : WithConv (Hab k →ₗ[k] Hab k)) :=
    Commute.neg_one_right (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)))
  have key : ∀ (e c : ℕ),
      (-1 : WithConv (Hab k →ₗ[k] Hab k)) ^ e * (c : WithConv (Hab k →ₗ[k] Hab k))
        = ((-1 : k) ^ e * (c : k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)) := by
    intro e c
    have hc : ((c : k) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
        = (c : WithConv (Hab k →ₗ[k] Hab k)) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    have hpow : (-1 : WithConv (Hab k →ₗ[k] Hab k)) ^ e
        = (-1 : k) ^ e • (1 : WithConv (Hab k →ₗ[k] Hab k)) := by
      rw [← neg_one_smul k (1 : WithConv (Hab k →ₗ[k] Hab k)), smul_pow, one_pow]
    rw [hpow, smul_mul_assoc, one_mul, mul_smul, hc]
  rw [sub_eq_add_neg, hcomm.add_pow, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, key (j - i) (j.choose i), mul_smul_comm, mul_one,
      WithConv.ofConv_smul, LinearMap.smul_apply]
  rfl

/-! Brick A scaffolding — `J^{⋆j}` naturality through `π` and per-degree nilpotency
on `H_ab`. -/

-- **Planar Brick B.** Same binomial expansion on the planar `H` (the convolution ring is
-- non-commutative, but `id` and `1` commute, so `Commute.add_pow` still applies). `maxHeartbeats 0`
-- for the WithConv `whnf` cost. Used to transport `J^{⋆j}` through `π`.
omit [Algebra ℚ k] in
theorem _root_.CK.Jc_pow_ofConv_eq_adams_sum (j : ℕ) (z : H k) :
    ((Jc k) ^ j).ofConv z
      = ∑ i ∈ Finset.range (j + 1),
          ((-1 : k) ^ (j - i) * (j.choose i : k)) • adams k i z := by
  have hcomm : Commute (WithConv.toConv (LinearMap.id (R := k) (M := H k)))
      (-1 : WithConv (H k →ₗ[k] H k)) :=
    Commute.neg_one_right (WithConv.toConv (LinearMap.id (R := k) (M := H k)))
  have key : ∀ (e c : ℕ),
      (-1 : WithConv (H k →ₗ[k] H k)) ^ e * (c : WithConv (H k →ₗ[k] H k))
        = ((-1 : k) ^ e * (c : k)) • (1 : WithConv (H k →ₗ[k] H k)) := by
    intro e c
    have hc : ((c : k) • (1 : WithConv (H k →ₗ[k] H k)))
        = (c : WithConv (H k →ₗ[k] H k)) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    have hpow : (-1 : WithConv (H k →ₗ[k] H k)) ^ e
        = (-1 : k) ^ e • (1 : WithConv (H k →ₗ[k] H k)) := by
      rw [← neg_one_smul k (1 : WithConv (H k →ₗ[k] H k)), smul_pow, one_pow]
    rw [hpow, smul_mul_assoc, one_mul, mul_smul, hc]
  rw [Jc, sub_eq_add_neg, hcomm.add_pow, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, key (j - i) (j.choose i), mul_smul_comm, mul_one,
      WithConv.ofConv_smul, LinearMap.smul_apply]
  rfl

-- **`J^{⋆j}` naturality through `π`.** Both Brick-B expansions plus Adams naturality.
omit [Algebra ℚ k] in
theorem _root_.CK.Jc_pow_ofConv_natural (j : ℕ) (z : H k) :
    π k (((Jc k) ^ j).ofConv z)
      = ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv (π k z) := by
  rw [Jc_pow_ofConv_eq_adams_sum, map_sum, JcAb_pow_ofConv_eq_adams_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hnat : π k (adams k i z) = adamsAb k i (π k z) := by
    have h := LinearMap.congr_fun (adamsAb_natural k i) z
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using h.symm
  rw [map_smul, hnat]

-- **Per-degree nilpotency on `H_ab`.** `J_ab^{⋆n}` kills `π`-images of forests with `< n` nodes
-- (transport of the planar `Jc_pow_ofConv_sf_eq_zero` through `π`). Makes the log series
-- finite per degree.
omit [Algebra ℚ k] in
theorem _root_.CK.JcAb_pow_ofConv_sf_eq_zero (n : ℕ) (f : Forest) (h : sizeF f < n) :
    ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ n).ofConv
      (π k (sf k f)) = 0 := by
  rw [← Jc_pow_ofConv_natural, Jc_pow_ofConv_sf_eq_zero k n f h, map_zero]

/-! Brick A core — the Φ_p ring-hom step: post-composition by `Ψᵖ` (`adamsAb p`, an
algebra hom) is a ⋆-ring hom, sending `J_ab ↦ Yᵖ − 1` (`Y = toConv id_ab`). This is
`Ψᵖ ∘ e = log(Yᵖ)`. -/

-- General: an algebra hom `φ` post-composed with a convolution power `g^{⋆j}` is the `j`-th
-- convolution power of `φ ∘ g`:
-- `φ ∘ (g^j).ofConv = ((toConv(φ ∘ g.ofConv))^j).ofConv`. Mirrors
-- `algHom_comp_adamsAb` (the case `g = toConv id`); pure `algHom_comp_convMul_distrib` induction.
omit [Algebra ℚ k] in
theorem _root_.CK.algHom_comp_convPow (φ : Hab k →ₐ[k] Hab k)
    (g : WithConv (Hab k →ₗ[k] Hab k)) (j : ℕ) :
    φ.toLinearMap ∘ₗ (g ^ j).ofConv
      = ((WithConv.toConv (φ.toLinearMap ∘ₗ g.ofConv)) ^ j).ofConv := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    apply LinearMap.ext; simp_all
  | succ n ih =>
    rw [pow_succ' g n, LinearMap.algHom_comp_convMul_distrib,
        show WithConv.toConv (φ.toLinearMap ∘ₗ (g ^ n).ofConv)
            = (WithConv.toConv (φ.toLinearMap ∘ₗ g.ofConv)) ^ n from by
          rw [ih, WithConv.toConv_ofConv],
        ← pow_succ']

-- **Φ_p on `J_ab`**: `Ψᵖ ∘ (J_ab^{⋆j}) = (Yᵖ − 1)^{⋆j}`. Post-composition
-- sends `J_ab ↦ Yᵖ − 1`.
omit [Algebra ℚ k] in
theorem _root_.CK.adamsAb_comp_JcAb_pow (p j : ℕ) (y : Hab k) :
    adamsAb k p (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv y)
      = (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p - 1) ^ j).ofConv y := by
  have hPhi : WithConv.toConv ((adamsAbHom k p).toLinearMap
        ∘ₗ (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1).ofConv)
      = (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p - 1 := by
    rw [WithConv.ofConv_sub, WithConv.ofConv_toConv, LinearMap.comp_sub, WithConv.toConv_sub]
    congr 1
    · rw [LinearMap.comp_id, adamsAbHom_toLinearMap, adamsAb, WithConv.toConv_ofConv]
    · have hu : (adamsAbHom k p).toLinearMap ∘ₗ (1 : WithConv (Hab k →ₗ[k] Hab k)).ofConv
          = (1 : WithConv (Hab k →ₗ[k] Hab k)).ofConv := by
        apply LinearMap.ext; simp_all
      rw [hu, WithConv.toConv_ofConv]
  have hgen := LinearMap.congr_fun
    (algHom_comp_convPow k (adamsAbHom k p)
      (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) j) y
  rw [LinearMap.comp_apply, hPhi, adamsAbHom_toLinearMap] at hgen
  exact hgen

/-! Brick A step 2 — eval₂ plumbing: bridge the PowerSeries coeff identity (`coeff_logTrunc_pow`)
    to the convolution sums via `eval₂ (X ↦ J_ab)`, then kill high powers with nilpotency. -/

/-- `J_ab = id − u∘ε` on `H_ab`, as a convolution-ring element. -/
noncomputable def _root_.CK.JcAb : WithConv (Hab k →ₗ[k] Hab k) :=
  WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1

/-- `r ↦ r • 1` as a ring hom `k →+* WithConv(H_ab)` (image central; `convCommRing`). -/
noncomputable def _root_.CK.smulOne : k →+* WithConv (Hab k →ₗ[k] Hab k) where
  toFun r := r • (1 : WithConv (Hab k →ₗ[k] Hab k))
  map_one' := one_smul _ _
  map_mul' r s := by rw [smul_mul_assoc, one_mul, smul_smul]
  map_zero' := zero_smul _ _
  map_add' r s := add_smul _ _ _

/-- The Eulerian coefficient `(-1)^{j+1}/j` equals the `j`-th coefficient of the formal `log`. -/
theorem _root_.CK.eulerCoef_eq_coeff_log (j : ℕ) :
    eulerCoef k j = PowerSeries.coeff j (PowerSeries.log k) := by
  rw [eulerCoef, PowerSeries.coeff_log]
  simp_all

omit [Algebra ℚ k] in
/-- `eval₂ smulOne J_ab P`, applied through `.ofConv` to `w`, is the explicit sum
    `Σₘ (P.coeff m) • (J_ab^m).ofConv w`. -/
theorem _root_.CK.eval₂_ofConv (P : Polynomial k) (w : Hab k) :
    (Polynomial.eval₂ (smulOne k) (JcAb k) P).ofConv w
      = ∑ m ∈ Finset.range (P.natDegree + 1), (P.coeff m) • ((JcAb k ^ m).ofConv w) := by
  rw [Polynomial.eval₂_eq_sum_range, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  change (((P.coeff m) • (1 : WithConv (Hab k →ₗ[k] Hab k))) * (JcAb k) ^ m).ofConv w = _
  rw [smul_mul_assoc, one_mul, WithConv.ofConv_smul, LinearMap.smul_apply]

/-- The truncated `∑ⱼ cⱼ X^j` polynomial has `coeff m = cₘ` for `m ≤ N`. -/
theorem _root_.CK.PR_coeff (N m : ℕ) (hm : m ≤ N) :
    (∑ j ∈ Finset.range (N + 1),
        Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) * Polynomial.X ^ j).coeff m
      = PowerSeries.coeff m (PowerSeries.log k) := by
  simp_all

/-- **(★) — the eigen-transport identity** on a per-degree-nilpotent `w`: applying `Ψᵖ`
    to the truncated convolution-log scales it by `p`. Proven by evaluating the polynomial
    `coeff_logTrunc_pow` identity at `J_ab` (`eval₂`), killing the surplus `J_ab^{>N}` by
    nilpotency. -/
theorem _root_.CK.star_identity (p N : ℕ) (w : Hab k)
    (hnil : ∀ m, N < m → ((JcAb k) ^ m).ofConv w = 0) :
    (∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j (PowerSeries.log k) •
        ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) ^ p - 1) ^ j).ofConv w)
      = (p : k) • ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv w) := by
  set Y := WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) with hY
  set PL : Polynomial k :=
    ∑ j ∈ Finset.range (N + 1),
      (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) *
        ((1 + Polynomial.X) ^ p - 1) ^ j) with hPL
  set PR : Polynomial k :=
    ∑ j ∈ Finset.range (N + 1),
      Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) * Polynomial.X ^ j with hPR
  set D : Polynomial k := PL - Polynomial.C (p : k) * PR with hD
  have hcomm : ∀ a : k, Commute ((smulOne k) a) (JcAb k) := by
    intro a
    change Commute (a • (1 : WithConv (Hab k →ₗ[k] Hab k))) (JcAb k)
    exact (Commute.one_left (JcAb k)).smul_left a
  have hYeq : (1 : WithConv (Hab k →ₗ[k] Hab k)) + JcAb k = Y := by
    rw [JcAb, hY]
    simp
  have hevPL : (Polynomial.eval₂ (smulOne k) (JcAb k) PL).ofConv w
      = ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((Y ^ p - 1) ^ j).ofConv w := by
    have hpoly : Polynomial.eval₂ (smulOne k) (JcAb k) PL
        = ∑ j ∈ Finset.range (N + 1),
            PowerSeries.coeff j (PowerSeries.log k) • (Y ^ p - 1) ^ j := by
      rw [← Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm PL]
      rw [hPL, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, map_sub, map_pow, map_add, map_one,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm
            (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k))),
          Polynomial.eval₂_C,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm Polynomial.X,
          Polynomial.eval₂_X, hYeq]
      change ((PowerSeries.coeff j (PowerSeries.log k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
            * (Y ^ p - 1) ^ j = _
      rw [smul_mul_assoc, one_mul]
    rw [hpoly, WithConv.ofConv_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
  have hevPR : (Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w
      = ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv w) := by
    have hpoly : Polynomial.eval₂ (smulOne k) (JcAb k) PR
        = ∑ j ∈ Finset.range (N + 1),
            PowerSeries.coeff j (PowerSeries.log k) • (JcAb k) ^ j := by
      rw [← Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm PR]
      rw [hPR, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm
            (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k))),
          Polynomial.eval₂_C,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm Polynomial.X,
          Polynomial.eval₂_X]
      change ((PowerSeries.coeff j (PowerSeries.log k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
            * (JcAb k) ^ j = _
      rw [smul_mul_assoc, one_mul]
    rw [hpoly, WithConv.ofConv_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
  have hDcoeff : ∀ m, m ≤ N → D.coeff m = 0 := by
    intro m hm
    have : IsAddTorsionFree k := IsAddTorsionFree.of_module_rat k
    rw [hD, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hPL,
        PowerSeries.polyPL_coeff (A := k) p N m hm, hPR, PR_coeff (k := k) N m hm,
        nsmul_eq_mul]
    ring
  have hD0 : (Polynomial.eval₂ (smulOne k) (JcAb k) D).ofConv w = 0 := by
    rw [eval₂_ofConv]
    apply Finset.sum_eq_zero
    intro m _
    rcases le_or_gt m N with h | h
    · rw [hDcoeff m h, zero_smul]
    · rw [hnil m h, smul_zero]
  have hevD : (Polynomial.eval₂ (smulOne k) (JcAb k) D).ofConv w
      = (Polynomial.eval₂ (smulOne k) (JcAb k) PL).ofConv w
        - (p : k) • (Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w := by
    rw [hD, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul_noncomm (smulOne k) (JcAb k) (fun n => hcomm (PR.coeff n)),
        Polynomial.eval₂_C, WithConv.ofConv_sub, LinearMap.sub_apply]
    congr 1
    change (((p : k) • (1 : WithConv (Hab k →ₗ[k] Hab k))) *
            Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w = _
    rw [smul_mul_assoc, one_mul, WithConv.ofConv_smul, LinearMap.smul_apply]
  rw [hevD, hevPL, hevPR, sub_eq_zero] at hD0
  exact hD0

/-- `π(e⁽¹⁾ y)` as a truncated convolution-log sum on `H_ab`, for any degree bound
    `M ≥ deg(y)`. -/
theorem _root_.CK.pi_eulerian1_eq (y : H k) (M : ℕ) (hMy : ∀ a ∈ y.coeff.support, sizeF a ≤ M) :
    π k (eulerian1 k y)
      = ∑ j ∈ Finset.range (M + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv (π k y)) := by
  rw [eulerian1_eq_logTrunc k y M hMy, logTrunc_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, eulerCoef_eq_coeff_log, Jc_pow_ofConv_natural, JcAb]

/-- **Adams eigen-relation on a basis forest**:
    `Ψᵖ(π(e⁽¹⁾(sf f))) = p · π(e⁽¹⁾(sf f))`. -/
theorem _root_.CK.adamsAb_eigen_basis (p : ℕ) (f : Forest) :
    adamsAb k p (π k (eulerian1 k (sf k f))) = (p : k) • π k (eulerian1 k (sf k f)) := by
  have hMy : ∀ a ∈ (sf k f).coeff.support, sizeF a ≤ sizeF f := by
    intro a ha
    have ha' : a = FreeMonoid.ofList f :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
    rw [ha']
    rfl
  rw [pi_eulerian1_eq k (sf k f) (sizeF f) hMy, map_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, JcAb, adamsAb_comp_JcAb_pow] :
    ∀ j ∈ Finset.range (sizeF f + 1),
      adamsAb k p
        (PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv (π k (sf k f))))
        = PowerSeries.coeff j (PowerSeries.log k) •
            ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) ^ p - 1) ^ j).ofConv
              (π k (sf k f)))]
  exact star_identity k p (sizeF f) (π k (sf k f))
    (fun m hm => JcAb_pow_ofConv_sf_eq_zero k m f hm)

/-- **Adams eigen-relation** (general): `Ψᵖ(π(e⁽¹⁾ x)) = p · π(e⁽¹⁾ x)` for all
    `x`. -/
theorem _root_.CK.adamsAb_eigen (p : ℕ) (x : H k) :
    adamsAb k p (π k (eulerian1 k x)) = (p : k) • π k (eulerian1 k x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    change adamsAb k p (π k (eulerian1 k (0 : H k)))
      = (p : k) • π k (eulerian1 k (0 : H k))
    simp
  | add f g hf hg =>
    have he : eulerian1 k ((f : H k) + (g : H k))
        = eulerian1 k (f : H k) + eulerian1 k (g : H k) :=
      map_add (eulerian1 k) (f : H k) (g : H k)
    simp_all
  | single a b =>
    have hsa : (MonoidAlgebra.single a b : H k) = b • sf k (FreeMonoid.toList a) := by
      rw [sf, FreeMonoid.ofList_toList]
      exact single_smul_one (k := k) (f := a) (b := b)
    rw [hsa]
    simp only [map_smul]
    rw [adamsAb_eigen_basis k p (FreeMonoid.toList a), smul_comm]

/-! Brick C — the finite-difference collapse: on an Adams eigenvector the convolution-log
truncation collapses to the eigenvector itself (only the weight-1 term survives). -/

/-- **Brick C (collapse).** On an Adams eigenvector `v` (`Ψⁱ(v) = i·v`), the truncated
    convolution-log is the identity: `Σⱼ≤M cⱼ · J_ab^{⋆j}(v) = v` (`M ≥ 1`). The
    `J_ab^{⋆j}` expands into Adams ops, the eigen-relation turns each into a scalar, and
    `alternating_choose_weighted` kills all but `j = 1`. -/
theorem _root_.CK.brickC (v : Hab k) (M : ℕ) (hM : 1 ≤ M)
    (heig : ∀ i, adamsAb k i v = (i : k) • v) :
    (∑ j ∈ Finset.range (M + 1), PowerSeries.coeff j (PowerSeries.log k) •
      ((JcAb k ^ j).ofConv v))
      = v := by
  have hcollapse : ∀ j, (JcAb k ^ j).ofConv v = (if j = 1 then (1 : k) else 0) • v := by
    intro j
    rw [JcAb, JcAb_pow_ofConv_eq_adams_sum,
        Finset.sum_congr rfl (fun i _ => by rw [heig i, smul_smul] :
          ∀ i ∈ Finset.range (j + 1),
            ((-1 : k) ^ (j - i) * (j.choose i : k)) • adamsAb k i v
              = ((-1 : k) ^ (j - i) * (j.choose i : k) * (i : k)) • v),
        ← Finset.sum_smul]
    congr 1
    rw [show (∑ i ∈ Finset.range (j + 1),
        (-1 : k) ^ (j - i) * (j.choose i : k) * (i : k))
        = ((if j = 1 then (1 : ℤ) else 0) : k) from by
          have h := congrArg (fun z : ℤ => (z : k)) (alternating_choose_weighted j)
          simpa using h]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcollapse j] :
      ∀ j ∈ Finset.range (M + 1),
        PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv v)
          = PowerSeries.coeff j (PowerSeries.log k) • ((if j = 1 then (1 : k) else 0) • v)),
      Finset.sum_eq_single 1]
  · rw [ite_eq_left rfl, one_smul, PowerSeries.coeff_one_log, one_smul]
  · intro b _ hb; rw [ite_eq_right hb, zero_smul, smul_zero]
  · intro h1; exact absurd (Finset.mem_range.2 (by omega : 1 < M + 1)) h1

/-- **`e⁽¹⁾ ∘ e⁽¹⁾ = e⁽¹⁾` on the commutative `H_ab`** (the Eulerian idempotency, via
    `π`). The first Eulerian idempotent is genuinely idempotent on the abelianized
    Connes–Kreimer / Butcher Hopf algebra. Combines `pi_eulerian1_eq`, the Adams
    eigen-relation `adamsAb_eigen`, and the Brick-C collapse. -/
theorem _root_.CK.eulerian1_idem_ab (x : H k) :
    π k (eulerian1 k (eulerian1 k x)) = π k (eulerian1 k x) := by
  set M := (eulerian1 k x).coeff.support.sup sizeF + 1 with hMdef
  have hMy : ∀ a ∈ (eulerian1 k x).coeff.support, sizeF a ≤ M := fun a ha =>
    le_trans (Finset.le_sup ha) (by rw [hMdef]; omega)
  rw [pi_eulerian1_eq k (eulerian1 k x) M hMy]
  exact brickC k (π k (eulerian1 k x)) M (by rw [hMdef]; omega) (fun i => adamsAb_eigen k i x)

end CK
