/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.QuasiTableau

/-! # Pre-interpolants (Definition 9.18)

Given the quasi-tableau `Q` of the cluster `C` (Def 9.8, `LoadedCluster.Q`) and the
formulas `θ_Δ` of Def 9.13 (`LoadedCluster.thetaOf`), we define by a leaf-to-root
induction a *pre-interpolant* `ι_x` for every node `x` of `Q`.

As in `Pdl.InterpolationCluster` a node of the quasi-tableau is given by its *address*,
the list of child indices leading to it from the root. Hence the internal variables `q_x`
for `x ∈ K_Q` are indexed by `List Nat`, and pre-interpolants are elements of
`QFormula (List Nat)`, the Q-formulas of Def 9.15.

The definition proceeds by recursion on the subtree, carrying along the address of its
root; the address is needed to look up the companion `c(x)` and to decide whether `x` is
itself a companion. Two cases of the definition presuppose facts about the quasi-tableau
that are not part of the data type, namely that nodes of type 2 and basic nodes of type 3
have a unique child. For nodes without children where the paper assumes one we return the
placeholder `⊤`; by Remark 9.9 (`QuasiTab.build_leaf_typ`) this does not happen in `C.Q`.
-/

@[expose] public section

namespace PDL

/-! ## The leading program of the loaded formula -/

/-- The leading program `α` of the loaded formula `~⌊α⌋ξ` of a sequent, if there is one.
For a basic sequent this program is atomic, see
`Sequent.isAtomic_of_basic_of_negLoad_mem_wForms`. -/
def Sequent.loadedProgOpt : Sequent → Option Program
  | ⟨_, _, none⟩ => none
  | ⟨_, _, some (Sum.inl (~'(⌊α⌋_)))⟩ => some α
  | ⟨_, _, some (Sum.inr (~'(⌊α⌋_)))⟩ => some α

/-- The leading program of the loaded formula, or `?'⊥` if the sequent is free.
Only used in the case `k(x) = 3` with `Δₓ` basic of Definition 9.18, where the sequent
is loaded. -/
def Sequent.loadedProg (X : Sequent) : Program := X.loadedProgOpt.getD (?'⊥)

/-! ## Definition 9.18 -/

namespace QuasiTab

mutual

/-- Def 9.18: the pre-interpolant `ι_x` of the node with address `x` in the quasi-tableau
`q`, where `θ` gives the formulas `θ_Δ` of Def 9.13.

The first argument `q` is the whole quasi-tableau (used to find companions), the argument
`n` is the subtree at address `x`, on which we recurse.

* `k(x) = 1` and `x` is a leaf: if `x` is a repeat, i.e. has a companion `c(x)`, then
  `ι_x := q_{c(x)}`; otherwise `Δ_x ∈ Λ₂[C⁺] \ Λ₂[C]` and `ι_x := θ_{Δ_x}`.
* `k(x) = 1` and `x` is a companion: `ι_x` is the fixpoint `QFormula.gfp x ι_y` where `y`
  is the unique child of `x`.
* `k(x) = 1` otherwise: `ι_x := ι_y` for the unique child `y`.
* `k(x) = 2`: `ι_x := [¬θ_{Δ_x}?] ι_y` for the unique child `y`.
* `k(x) = 3` with `Δ_x` basic: `ι_x := [a] ι_y` where `a` is the leading atomic program of
  the loaded formula of `Δ_x`.
* `k(x) = 3` with `Δ_x` not basic: `ι_x := ⋀ { ι_y | x ⋖Q y }`. -/
def iitpAt (q : QuasiTab) (θ : Sequent → Formula) :
    (n : QuasiTab) → (x : List Nat) → QFormula (List Nat)
  | .QNode .one Δ [], x =>
      match q.companionOpt x with
      | some c => .var c
      | none => .fma (θ Δ)
  | .QNode .one _ (y :: _), x =>
      let ι := iitpAt q θ y (x ++ [0])
      if x ∈ q.companions then ι.gfp x else ι
  | .QNode .two Δ (y :: _), x => .boxes [?'(~ θ Δ)] (iitpAt q θ y (x ++ [0]))
  | .QNode .two _ [], _ => .fma ⊤ -- does not occur, see Remark 9.9
  | .QNode .three Δ next, x =>
      if Δ.basic then
        match next with
        | [] => .fma ⊤ -- does not occur, see Remark 9.9
        | (y :: _) => .boxes [Δ.loadedProg] (iitpAt q θ y (x ++ [0]))
      else
        QFormula.conj (iitpList q θ next x 0)
  termination_by n => sizeOf n

/-- Auxiliary function for `iitpAt`: the pre-interpolants of a list of children, where
`i` is the index of the first one, needed to build their addresses. -/
def iitpList (q : QuasiTab) (θ : Sequent → Formula) :
    (ns : List QuasiTab) → (x : List Nat) → (i : Nat) → List (QFormula (List Nat))
  | [], _, _ => []
  | n :: ns, x, i => iitpAt q θ n (x ++ [i]) :: iitpList q θ ns x (i + 1)
  termination_by ns => sizeOf ns

end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end QuasiTab
end PDL

namespace PDL
namespace QuasiTab

end QuasiTab

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X}

/-- Def 9.18: the pre-interpolant `ι_x` of the node with address `x` of the quasi-tableau
`Q` of the cluster `C`, where `θ` gives the interpolants of the exit nodes of `C`.
When there is no node at address `x` we return the placeholder `⊤`. -/
noncomputable def iitp (C : LoadedCluster tab) (θ : FinePathIn tab → Formula) (x : List Nat) :
    QFormula (List Nat) :=
  match C.Q.atOpt x with
  | none => .fma ⊤
  | some n => QuasiTab.iitpAt C.Q (C.thetaOf θ) n x

/-- The pre-interpolant of the root of the quasi-tableau. This is the formula `ι_{c_Q}`
that Def 9.20 turns into the interpolant of the root of the cluster. -/
noncomputable def rootIitp (C : LoadedCluster tab) (θ : FinePathIn tab → Formula) :
    QFormula (List Nat) :=
  C.iitp θ QuasiTab.rootAddress

end LoadedCluster

/-! ## Unfolding lemmas for Definition 9.18 -/

namespace QuasiTab

variable {q : QuasiTab} {θ : Sequent → Formula}

@[simp]
lemma iitpAt_one_leaf_repeat {Δ x c} (h : q.companionOpt x = some c) :
    iitpAt q θ (.QNode .one Δ []) x = .var c := by
  rw [iitpAt]; simp [h]

@[simp]
lemma iitpAt_one_leaf_exit {Δ x} (h : q.companionOpt x = none) :
    iitpAt q θ (.QNode .one Δ []) x = .fma (θ Δ) := by
  rw [iitpAt]; simp [h]

lemma iitpAt_one_node {Δ x y ys} :
    iitpAt q θ (.QNode .one Δ (y :: ys)) x =
      (if x ∈ q.companions then (iitpAt q θ y (x ++ [0])).gfp x
        else iitpAt q θ y (x ++ [0])) := by
  rw [iitpAt]

lemma iitpAt_two {Δ x y ys} :
    iitpAt q θ (.QNode .two Δ (y :: ys)) x =
      .boxes [?'(~ θ Δ)] (iitpAt q θ y (x ++ [0])) := by
  rw [iitpAt]

lemma iitpAt_three_basic {Δ x y ys} (h : Δ.basic) :
    iitpAt q θ (.QNode .three Δ (y :: ys)) x =
      .boxes [Δ.loadedProg] (iitpAt q θ y (x ++ [0])) := by
  rw [iitpAt]; simp [h]

lemma iitpAt_three_not_basic {Δ x next} (h : ¬ Δ.basic) :
    iitpAt q θ (.QNode .three Δ next) x = QFormula.conj (iitpList q θ next x 0) := by
  rw [iitpAt.eq_def]; simp [h]

@[simp]
lemma iitpList_nil {x i} : iitpList q θ [] x i = [] := by rw [iitpList]

@[simp]
lemma iitpList_cons {n ns x i} :
    iitpList q θ (n :: ns) x i = iitpAt q θ n (x ++ [i]) :: iitpList q θ ns x (i + 1) := by
  rw [iitpList]

lemma length_iitpList {ns : List QuasiTab} {x i} : (iitpList q θ ns x i).length = ns.length := by
  induction ns generalizing i with
  | nil => simp
  | cons n ns IH => simp [IH]

/-- The `j`-th element of `iitpList` is the pre-interpolant of the `j`-th child. -/
lemma iitpList_getElem {ns : List QuasiTab} {x i j} (hj : j < ns.length) :
    (iitpList q θ ns x i)[j]'(by rw [length_iitpList]; exact hj)
      = iitpAt q θ ns[j] (x ++ [i + j]) := by
  induction ns generalizing i j with
  | nil => simp at hj
  | cons n ns IH =>
    cases j with
    | zero => simp
    | succ j =>
      have heq : i + 1 + j = i + (j + 1) := by omega
      simpa [heq] using IH (i := i + 1) (j := j) (by simpa using hj)

end QuasiTab

/-! ## Unfolding Definition 9.18 at the level of addresses

The lemmas above are about the recursion on subtrees. Here we restate them for the
pre-interpolants `LoadedCluster.iitp` of the nodes of `Q`, which are given by addresses. -/

namespace QuasiTab

/-- Going to the child with index `i` of the node at address `x`. -/
lemma atOpt_snoc (q : QuasiTab) (x : List Nat) (i : Nat) :
    q.atOpt (x ++ [i]) = (q.atOpt x).bind (fun n => n.children[i]?) := by
  induction x generalizing q with
  | nil =>
      change q.atOpt [i] = _
      rw [atOpt]
      cases h : q.children[i]? <;> simp [atOpt, h]
  | cons j x IH =>
      change q.atOpt (j :: (x ++ [i])) = _
      rw [atOpt]
      cases h : q.children[j]? with
      | none => simp [atOpt, h]
      | some c => simp only [IH c, atOpt, h]

end QuasiTab

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}
  {θ : FinePathIn tab → Formula} {x : List Nat}

lemma iitp_of_atOpt {n} (h : C.Q.atOpt x = some n) :
    C.iitp θ x = QuasiTab.iitpAt C.Q (C.thetaOf θ) n x := by
  rw [iitp, h]

/-- The pre-interpolant of the first child of a node. -/
lemma iitp_first_child {k Δ y ys} (h : C.Q.atOpt x = some (.QNode k Δ (y :: ys))) :
    C.iitp θ (x ++ [0]) = QuasiTab.iitpAt C.Q (C.thetaOf θ) y (x ++ [0]) := by
  rw [iitp, QuasiTab.atOpt_snoc, h]
  rfl

/-- Def 9.18, case `k(x) = 1` where `x` is a repeat leaf: `ι_x = q_{c(x)}`. -/
lemma iitp_one_leaf_repeat {Δ c} (h : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = some c) : C.iitp θ x = .var c := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_one_leaf_repeat hc]

/-- Def 9.18, case `k(x) = 1` where `x` is a leaf that is not a repeat: `ι_x = θ_{Δ_x}`. -/
lemma iitp_one_leaf_exit {Δ} (h : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = none) : C.iitp θ x = .fma (C.thetaOf θ Δ) := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_one_leaf_exit hc]

/-- Def 9.18, case `k(x) = 1` where `x` is a companion: `ι_x` is the fixpoint. -/
lemma iitp_one_companion {Δ y ys} (h : C.Q.atOpt x = some (.QNode .one Δ (y :: ys)))
    (hx : x ∈ C.Q.companions) : C.iitp θ x = (C.iitp θ (x ++ [0])).gfp x := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_one_node, ite_eq_left hx, iitp_first_child h]

/-- Def 9.18, case `k(x) = 1` where `x` is neither a leaf nor a companion: `ι_x = ι_y`. -/
lemma iitp_one_inner {Δ y ys} (h : C.Q.atOpt x = some (.QNode .one Δ (y :: ys)))
    (hx : x ∉ C.Q.companions) : C.iitp θ x = C.iitp θ (x ++ [0]) := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_one_node, ite_eq_right hx, iitp_first_child h]

/-- Def 9.18, case `k(x) = 2`: `ι_x = [¬θ_{Δ_x}?] ι_y`. -/
lemma iitp_two {Δ y ys} (h : C.Q.atOpt x = some (.QNode .two Δ (y :: ys))) :
    C.iitp θ x = .boxes [?'(~ C.thetaOf θ Δ)] (C.iitp θ (x ++ [0])) := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_two, iitp_first_child h]

/-- Def 9.18, case `k(x) = 3` with `Δ_x` basic: `ι_x = [a] ι_y`. -/
lemma iitp_three_basic {Δ y ys} (h : C.Q.atOpt x = some (.QNode .three Δ (y :: ys)))
    (hb : Δ.basic) : C.iitp θ x = .boxes [Δ.loadedProg] (C.iitp θ (x ++ [0])) := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_three_basic hb, iitp_first_child h]

/-- Def 9.18, case `k(x) = 3` with `Δ_x` not basic: `ι_x` is the conjunction of the
pre-interpolants of all children of `x`, see `iitpList_getElem_eq_iitp`. -/
lemma iitp_three_not_basic {Δ next} (h : C.Q.atOpt x = some (.QNode .three Δ next))
    (hb : ¬ Δ.basic) :
    C.iitp θ x = QFormula.conj (QuasiTab.iitpList C.Q (C.thetaOf θ) next x 0) := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_three_not_basic hb]

/-- The conjuncts in the case `k(x) = 3` with `Δ_x` not basic are indeed the
pre-interpolants of the children of `x`. -/
lemma iitpList_getElem_eq_iitp {Δ next} (h : C.Q.atOpt x = some (.QNode .three Δ next))
    {i : Nat} (hi : i < next.length) :
    (QuasiTab.iitpList C.Q (C.thetaOf θ) next x 0)[i]'
        (by rw [QuasiTab.length_iitpList]; exact hi)
      = C.iitp θ (x ++ [i]) := by
  rw [QuasiTab.iitpList_getElem hi, iitp, QuasiTab.atOpt_snoc, h]
  simp only [Option.bind_some, QuasiTab.children, List.getElem?_eq_getElem hi, Nat.zero_add]

end LoadedCluster

end PDL
