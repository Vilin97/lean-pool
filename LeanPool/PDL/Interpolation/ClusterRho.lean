/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.ClusterItp

/-! # The region formulas and the left half of the correctness of `θ_r`

This file continues the development of `Pdl.ClusterItp` with

* Definition 10.2: the region formulas `ρ_x`, and
* Lemma 10.3: `Γ₁ ⊨ θ_r`.
-/

@[expose] public section

namespace PDL

/-- A proper prefix of `x` is one of the addresses searched by `QuasiTab.companionOpt`. -/
lemma mem_inits_dropLast_of_prefix_ne {α} {z x : List α} (h : z <+: x)
    (hne : z ≠ x) : z ∈ x.inits.dropLast := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => exact absurd (by simp) hne
  | cons a t =>
    rw [List.inits_append, List.dropLast_append_of_ne_nil (by cases t <;> simp [List.inits])]
    exact List.mem_append_left _ ((List.mem_inits _ _).mpr (List.prefix_refl z))

/-! ## Two semantic lemmas -/

/-- `stepToStar` in the form used in the companion case of Lemma 10.3: if `φ` is preserved
along `α` and implies `ψ`, then `φ` implies `[α*]ψ`. -/
lemma evaluate_boxes_star {α : Program} {φ ψ : Formula}
    (h : ∀ (W : Type) (M : KripkeModel W) (v : W), evaluate M v φ →
      (∀ u, relate M α v u → evaluate M u φ) ∧ evaluate M v ψ)
    {W : Type} {M : KripkeModel W} {w : W} (hw : evaluate M w φ) :
    evaluate M w (⌈∗α⌉ψ) := by
  have hstar : φ ⊨ (⌈∗α⌉ψ) := by
    refine stepToStar ?_
    intro W' M' v hv ξ hξ
    simp only [List.mem_singleton] at hξ
    subst hξ
    exact h W' M' v (hv φ (by simp))
  exact hstar W M w (by simpa using hw) _ (by simp)

namespace QFormula

variable {Var : Type}

/-- Two substitutions that agree on the internal variables of a Q-formula give the same
formula. -/
lemma subst_congr {σ τ : Var → Formula} : ∀ (ι : QFormula Var),
    (∀ v ∈ ι.vars, σ v = τ v) → ι.subst σ = ι.subst τ
  | .fma _, _ => rfl
  | .var q, h => h q (by simp)
  | .and ι1 ι2, h => by
      simp only [subst_and]
      rw [subst_congr ι1 (fun v hv => h v (by simp [hv])),
        subst_congr ι2 (fun v hv => h v (by simp [hv]))]
  | .boxes as ι, h => by
      simp only [subst_boxes]
      rw [subst_congr ι (fun v hv => h v (by simpa using hv))]


end QFormula

namespace QuasiTab

/-- The label of a node built by `QuasiTab.build`. -/
@[simp]
lemma build_label {inC step Hist Δ} : (QuasiTab.build inC step Hist Δ).label = Δ := by
  rw [QuasiTab.build]; split <;> rfl

/-- Every node built by `QuasiTab.build` has type 1. -/
@[simp]
lemma build_typ {inC step Hist Δ} : (QuasiTab.build inC step Hist Δ).typ = Typ.one := by
  rw [QuasiTab.build]; split <;> rfl


end QuasiTab

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}
  {θ : FinePathIn tab → Formula} {x : List Nat}

/-! ## Definition 10.2: the region formulas -/

/-- Def 10.2: the formula `ρ_x = ⋁ { ⋀ Λ₁(t) | t ∈ R_x }` for a node `x` of the
quasi-tableau, where `R_x` is the region of `x` (Def 9.10). When there is no node at
address `x` we return `⊥`, the empty disjunction. -/
noncomputable def rho (C : LoadedCluster tab) (x : List Nat) : Formula :=
  match C.Q.atOpt x with
  | none => ⊥
  | some n => ((C.regionOf n).image (fun t => con t.label.left.pdlSort)).pdlDis

lemma rho_of_atOpt {n} (h : C.Q.atOpt x = some n) :
    C.rho x = ((C.regionOf n).image (fun t => con t.label.left.pdlSort)).pdlDis := by
  rw [rho, h]

/-- `ρ_x` holds iff some node of the region `R_x` has all its left formulas true. -/
lemma evaluate_rho_iff {W} {M : KripkeModel W} {w : W} {n} (h : C.Q.atOpt x = some n) :
    evaluate M w (C.rho x) ↔ ∃ t ∈ C.regionOf n, ∀ φ ∈ t.label.left, evaluate M w φ := by
  rw [rho_of_atOpt h, Finset.disEval]
  simp only [Finset.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨_, t, hev⟩
    simp [conEval] at hev
    grind
  · rintro ⟨t, ht, hev⟩
    simp only [conEval, Formula.mem_pdlSort]
    use t

/-- The region, and hence `ρ_x`, only depends on the type and the label of the node. -/
lemma rho_eq_of_typ_label {n m} {y : List Nat} (hx : C.Q.atOpt x = some n)
    (hy : C.Q.atOpt y = some m) (htyp : n.typ = m.typ) (hlab : n.label = m.label) :
    C.rho x = C.rho y := by
  rw [rho_of_atOpt hx, rho_of_atOpt hy, regionOf, regionOf, htyp, hlab]

/-- A variant of `rho_eq_of_typ_label` for nodes with the same region. -/
lemma rho_eq_of_regionOf {n m} {y : List Nat} (hx : C.Q.atOpt x = some n)
    (hy : C.Q.atOpt y = some m) (h : C.regionOf n = C.regionOf m) : C.rho x = C.rho y := by
  rw [rho_of_atOpt hx, rho_of_atOpt hy, h]

/-- Nodes of type 1 and of type 2 with the same label have the same region (Def 9.10). -/
lemma regionOf_one_eq_two {Δ next next'} :
    C.regionOf (.QNode .one Δ next) = C.regionOf (.QNode .two Δ next') := rfl

/-! ## Lemma 10.3: `Γ₁ ⊨ θ_r`

The proof of Lemma 10.3 in the paper goes through the claim that `ρ_x ⊨ σ(ι_x)` for every
node `x` of the quasi-tableau, where `σ` sends the internal variable `q_x` to the region
formula `ρ_x`. We call this claim `LoadedCluster.RhoSat`. -/

/-- The claim `ρ_x ⊨ ι_x⟨σ⟩` of the proof of Lemma 10.3, where the substitution `σ` sends
each internal variable `q_z` to the region formula `ρ_z`. -/
def RhoSat (C : LoadedCluster tab) (θ : FinePathIn tab → Formula) (x : List Nat) : Prop :=
  ∀ (W : Type) (M : KripkeModel W) (w : W),
    evaluate M w (C.rho x) → evaluate M w ((C.iitp θ x).subst C.rho)

/-! ### The cases of the claim

Each case of the leaf-to-root induction in the proof of Lemma 10.3 is a separate lemma.
Where the paper uses that the child of a node of type `k` has type `k+1` and the same
label — which is part of the construction in Def 9.8 but not of the data type `QuasiTab` —
this is an explicit hypothesis. -/

/-- Case `k(x) = 1` and `x` a repeat: `ι_x = q_{c(x)}` and `ρ_x = ρ_{c(x)}`. -/
lemma rhoSat_one_leaf_repeat {Δ c} (hx : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = some c) : C.RhoSat θ x := by
  intro W M w hw
  rw [C.iitp_one_leaf_repeat hx hc, QFormula.subst_var]
  -- the companion has the same label and also type 1, hence the same region
  have hspec := List.find?_some hc
  simp only [decide_eq_true_eq] at hspec
  obtain ⟨hlab, htyp⟩ := hspec
  rw [QuasiTab.labelAt, QuasiTab.labelAt, hx] at hlab
  rw [QuasiTab.typAt] at htyp
  cases hcm : C.Q.atOpt c with
  | none => rw [hcm] at hlab; simp at hlab
  | some m =>
    rw [hcm] at hlab htyp
    simp only [Option.map_some, Option.some.injEq] at hlab htyp
    have : C.rho x = C.rho c := by
      refine C.rho_eq_of_regionOf hx hcm ?_
      rw [regionOf, regionOf, htyp, hlab]
      rfl
    rwa [this] at hw

/-- Case `k(x) = 1` where `x` is neither a leaf nor a companion: `ι_x = ι_y` and
`ρ_x = ρ_y`, because the unique child `y` has type 2 and the same label. -/
lemma rhoSat_one_inner {Δ y ys} (hx : C.Q.atOpt x = some (.QNode .one Δ (y :: ys)))
    (hcomp : x ∉ C.Q.companions) (hy : y = .QNode .two Δ y.children)
    (IH : C.RhoSat θ (x ++ [0])) : C.RhoSat θ x := by
  intro W M w hw
  have hchild : C.Q.atOpt (x ++ [0]) = some y := QuasiTab.atOpt_child hx (by simp)
  have hrho : C.rho x = C.rho (x ++ [0]) := by
    refine C.rho_eq_of_regionOf hx hchild ?_
    conv_rhs => rw [hy]
    exact regionOf_one_eq_two
  rw [C.iitp_one_inner hx hcomp]
  exact IH W M w (hrho ▸ hw)


/-! ### Entailment from the left component of a node

The claim of the proof of Lemma 10.3 is often used in the equivalent form
`ρ_x ⊨ ι_x⟨σ⟩  iff  Λ₁(t) ⊨ ι_x⟨σ⟩ for all t ∈ R_x`, see `rhoSat_iff`. -/

lemma mem_plusNodesWithFine_iff (Δ : Sequent) (f : FinePathIn tab) :
    f ∈ C.plusNodesWithFine Δ ↔ f ∈ C.fineCLplus ∧ f.label.rightOnly = Δ := by
  simp [plusNodesWithFine]

lemma mem_plusNodesWithFine_of_mem_exitsWithFine {Δ : Sequent} {f : FinePathIn tab}
    (hf : f ∈ C.exitsWithFine Δ) : f ∈ C.plusNodesWithFine Δ := by
  rw [C.mem_exitsWithFine_iff] at hf
  exact (C.mem_plusNodesWithFine_iff Δ f).mpr ⟨by simp_all [fineCLplus], hf.2⟩

lemma mem_plusNodesWithFine_of_mem_nodesWithFine {Δ : Sequent} {f : FinePathIn tab}
    (hf : f ∈ C.nodesWithFine Δ) : f ∈ C.plusNodesWithFine Δ := by
  simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf
  exact (C.mem_plusNodesWithFine_iff Δ f).mpr ⟨by simp_all [fineCLplus], hf.2⟩

lemma mem_plusNodesWithFine_of_mem_nodesWithFineRight {Δ : Sequent} {f : FinePathIn tab}
    (hf : f ∈ C.nodesWithFineRight Δ) : f ∈ C.plusNodesWithFine Δ :=
  C.mem_plusNodesWithFine_of_mem_nodesWithFine (List.mem_of_mem_filter hf)

/-- A node of `C⁺` whose right component is not in `Λ₂[C]` is an exit node. -/
lemma mem_exitsWithFine_of_notMem_lambdaTwo {Δ : Sequent} {f : FinePathIn tab}
    (hf : f ∈ C.plusNodesWithFine Δ) (hΔ : Δ ∉ C.lambdaTwo) : f ∈ C.exitsWithFine Δ := by
  rw [C.mem_plusNodesWithFine_iff] at hf
  obtain ⟨hmem, hlab⟩ := hf
  rw [C.mem_exitsWithFine_iff]
  refine ⟨?_, hlab⟩
  simp_all only [fineCLplus, fineExits, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Finset.mem_union, List.mem_toFinset, Finset.mem_filter,
    Finset.mem_sup]
  rcases hmem with h | h
  · exact absurd
      (by simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset]; exact ⟨f, h, hlab⟩) hΔ
  · exact h

/-- The claim `RhoSat` in the form used in the proof: `Λ₁(t) ⊨ ι_x⟨σ⟩` for all `t ∈ R_x`. -/
lemma rhoSat_iff {n} (h : C.Q.atOpt x = some n) :
    C.RhoSat θ x ↔ ∀ t ∈ C.regionOf n, t.leftEntails ((C.iitp θ x).subst C.rho) := by
  constructor
  · intro H t ht W M w hw
    exact H W M w ((evaluate_rho_iff h).mpr ⟨t, ht, hw⟩)
  · intro H W M w hw
    obtain ⟨t, ht, hev⟩ := (evaluate_rho_iff h).mp hw
    exact H t ht W M w hev

/-- `Λ₁(t) ⊨ θ_Δ` for all exit nodes `t` with right component `Δ`, i.e. Lemma 9.14 (a)
in the form of an entailment. -/
lemma leftEntails_thetaOf (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    {Δ : Sequent} {t : FinePathIn tab} (ht : t ∈ C.exitsWithFine Δ) :
    t.leftEntails (C.thetaOf θ Δ) := by
  intro W M w hw
  by_contra hcon
  exact C.thetaOf_left θ hθ Δ t ht ⟨W, M, w, by
    intro φ hφ
    aesop⟩

/-- Case `k(x) = 1` where `x` is a leaf that is not a repeat: `ι_x = θ_{Δ_x}` and every
node of the region is an exit node, so Lemma 9.14 (a) applies. -/
lemma rhoSat_one_leaf_exit {Δ} (hx : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = none) (hΔ : Δ ∉ C.lambdaTwo)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) : C.RhoSat θ x := by
  rw [rhoSat_iff hx]
  intro t ht
  rw [C.iitp_one_leaf_exit hx hc, QFormula.subst_fma]
  exact C.leftEntails_thetaOf hθ (C.mem_exitsWithFine_of_notMem_lambdaTwo ht hΔ)


/-- Case `k(x) = 2`: the unique child `y` has type 3 and the same label `Δ`, and
`ι_x = [¬θ_Δ?]ι_y`. Here `R_x = C⁺_Δ` but `R_y = C^R_Δ`, so we use the inner induction of
the paper, which is `PaperFacts.leftPropagation`. -/
lemma rhoSat_two {Δ y ys} (hF : C.PaperFacts) (hΔ : Δ ∈ C.lambdaTwo)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hx : C.Q.atOpt x = some (.QNode .two Δ (y :: ys)))
    (hy : y = .QNode .three Δ y.children)
    (IH : C.RhoSat θ (x ++ [0])) : C.RhoSat θ x := by
  have hchild : C.Q.atOpt (x ++ [0]) = some y := QuasiTab.atOpt_child hx (by simp)
  have hreg : C.regionOf y = (C.nodesWithFineRight Δ).toFinset := by rw [hy]; rfl
  rw [rhoSat_iff hx]
  -- `σ(ι_x)` is implied both by `θ_Δ` and by `σ(ι_y)`
  have key : ∀ (W : Type) (M : KripkeModel W) (w : W),
      (evaluate M w (C.thetaOf θ Δ) ∨ evaluate M w ((C.iitp θ (x ++ [0])).subst C.rho))
        → evaluate M w ((C.iitp θ x).subst C.rho) := by
    intro W M w hw
    rw [C.iitp_two hx, QFormula.subst_boxes, evalBoxes]
    intro v hv
    rw [relateSeq_singleton] at hv
    simp only [relate, evaluate] at hv
    obtain ⟨rfl, hneg⟩ := hv
    rcases hw with h | h
    · exact absurd h hneg
    · exact h
  refine hF.leftPropagation Δ hΔ _ ?_ ?_
  · intro u hu W M w hw
    refine key W M w (Or.inr ((rhoSat_iff hchild).mp IH u ?_ W M w hw))
    rw [hreg]
    exact List.mem_toFinset.mpr hu
  · intro u hu W M w hw
    exact key W M w (Or.inl (C.leftEntails_thetaOf hθ hu W M w hw))

/-- Case `k(x) = 3` with `Δ_x` basic: the unique child `y` has type 1 and its label is the
sequent obtained by applying the modal rule, and `ι_x = [a]ι_y`. -/
lemma rhoSat_three_basic {Δ y ys} (hF : C.PaperFacts) (hΔ : Δ ∈ C.lambdaTwo) (hb : Δ.basic)
    (hx : C.Q.atOpt x = some (.QNode .three Δ (y :: ys)))
    (hy1 : y.typ = Typ.one) (hy2 : y.label ∈ C.stepOf Δ)
    (IH : C.RhoSat θ (x ++ [0])) : C.RhoSat θ x := by
  have hchild : C.Q.atOpt (x ++ [0]) = some y := QuasiTab.atOpt_child hx (by simp)
  have hreg : C.regionOf y = C.plusNodesWithFine y.label := by
    rw [regionOf, hy1]; rfl
  rw [rhoSat_iff hx]
  intro t ht W M w hw
  obtain ⟨u, hu, hstep⟩ := hF.modalStep Δ hΔ hb t (List.mem_toFinset.mp ht) y.label hy2
  rw [C.iitp_three_basic hx hb, QFormula.subst_boxes, evalBoxes]
  intro v hv
  rw [relateSeq_singleton] at hv
  exact (rhoSat_iff hchild).mp IH u (hreg ▸ hu) W M v (hstep W M w v hw hv)

/-- Case `k(x) = 3` with `Δ_x` not basic: the children `y_i` have type 1 and are labelled
with the sequents `Π_i` of the right rule applied at `Δ_x`, and `ι_x = ⋀ᵢ ι_{y_i}`. -/
lemma rhoSat_three_not_basic {Δ next} (hF : C.PaperFacts) (hΔ : Δ ∈ C.lambdaTwo)
    (hb : ¬ Δ.basic) (hx : C.Q.atOpt x = some (.QNode .three Δ next))
    (hnext : ∀ n ∈ next, n.typ = Typ.one ∧ n.label ∈ C.stepOf Δ)
    (IH : ∀ i, i < next.length → C.RhoSat θ (x ++ [i])) : C.RhoSat θ x := by
  rw [rhoSat_iff hx]
  intro t ht W M w hw
  rw [C.iitp_three_not_basic hx hb, QFormula.subst_conj, conEval]
  intro ψ hψ
  simp only [List.mem_map] at hψ
  obtain ⟨ι, hι, rfl⟩ := hψ
  obtain ⟨i, hi, rfl⟩ := C.mem_iitpList hx hι
  have hchild : C.Q.atOpt (x ++ [i]) = some next[i] := QuasiTab.atOpt_child hx hi
  obtain ⟨htyp, hmem⟩ := hnext next[i] (List.getElem_mem hi)
  have hreg : C.regionOf next[i] = C.plusNodesWithFine next[i].label := by
    rw [regionOf, htyp]; rfl
  obtain ⟨u, hu, hlab⟩ :=
    hF.rightRuleChildren Δ hΔ hb t (List.mem_toFinset.mp ht) next[i].label hmem
  refine (rhoSat_iff hchild).mp (IH i hi) u (hreg ▸ hu) W M w ?_
  rw [hlab]
  exact hw


/-- Case `k(x) = 1` where `x` is a companion: the unique child `y` has type 2 and the same
label, so `ρ_x = ρ_y`, and `ι_x = gfp x ι_y`. Writing the normal form of `ι_y` as
`⋀ᵢ[αᵢ]q_x ∧ ⋀ⱼ[βⱼ]q_{zⱼ} ∧ ψ` the induction hypothesis says that `ρ` implies
`[α]ρ ∧ ⋀ⱼ[βⱼ]σ(q_{zⱼ}) ∧ ψ` where `α = ⋃ᵢαᵢ`, so `stepToStar` gives the claim. -/
lemma rhoSat_one_companion {Δ y ys} (hx : C.Q.atOpt x = some (.QNode .one Δ (y :: ys)))
    (hcomp : x ∈ C.Q.companions) (hy : y = .QNode .two Δ y.children)
    (IH : C.RhoSat θ (x ++ [0])) : C.RhoSat θ x := by
  have hchild : C.Q.atOpt (x ++ [0]) = some y := QuasiTab.atOpt_child hx (by simp)
  have hrho : C.rho x = C.rho (x ++ [0]) := by
    refine C.rho_eq_of_regionOf hx hchild ?_
    conv_rhs => rw [hy]
    exact regionOf_one_eq_two
  -- the induction hypothesis, split into the conjuncts of the normal form of `ι_y`
  have IH' : ∀ (W : Type) (M : KripkeModel W) (v : W), evaluate M v (C.rho x) →
      ∀ s ∈ (C.iitp θ (x ++ [0])).Spl, evaluate M v (s.toQ.subst C.rho) := by
    intro W M v hv
    rw [← QFormula.eval_nf_iff, QFormula.eval_nf]
    exact IH W M v (hrho ▸ hv)
  intro W M w hw
  rw [C.iitp_one_companion hx hcomp, QFormula.gfp, QFormula.subst_boxes]
  refine evaluate_boxes_star ?_ hw
  intro W' M' v hv
  constructor
  · -- `ρ` is preserved along the union of the loop programs
    intro u hu
    rw [relate_unions] at hu
    obtain ⟨a, ha, hau⟩ := hu
    simp only [QFormula.loopProgs, List.mem_filterMap] at ha
    obtain ⟨s, hs, hprog⟩ := ha
    cases s with
    | fma _ => simp [QSimple.progToOpt] at hprog
    | boxVar as q =>
      simp only [QSimple.progToOpt] at hprog
      split at hprog
      case isTrue hq =>
        subst hq
        rw [Option.some.injEq] at hprog
        subst hprog
        have hev := IH' W' M' v hv _ hs
        rw [QSimple.toQ, QFormula.subst_boxes, QFormula.subst_var, evalBoxes] at hev
        exact hev u ((relate_steps_iff_relateSeq _ _ _ _).mp hau)
      case isFalse => simp at hprog
  · -- the conjuncts not mentioning `x` follow from the induction hypothesis
    change evaluate M' v (QFormula.subst C.rho (QFormula.dropVar x (C.iitp θ (x ++ [0]))))
    rw [QFormula.dropVar, QFormula.subst_conj, conEval]
    intro ψ hψ
    simp only [List.mem_map] at hψ
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hψ
    exact IH' W' M' v hv s (List.mem_of_mem_filter hs)


/-! ### The claim for all nodes of the quasi-tableau

The leaf-to-root induction of the proof of Lemma 10.3 follows the recursion of
`QuasiTab.build`, i.e. of Definition 9.8. -/

/-- Descending in the tree preserves being a proper prefix. -/
lemma prefix_append_ne {α} {z x : List α} (hz : z <+: x) {l : List α} (hl : l ≠ []) :
    z <+: x ++ l ∧ z ≠ x ++ l := by
  refine ⟨hz.trans (List.prefix_append _ _), ?_⟩
  intro hcon
  have h1 := hz.length_le
  rw [hcon, List.length_append] at h1
  have h2 : l.length ≠ 0 := by simpa using hl
  omega

/-- The claim `ρ_x ⊨ ι_x⟨σ⟩` for all nodes of the quasi-tableau, by leaf-to-root induction.
The hypothesis on the history is the invariant of Definition 9.8: every sequent in the
history of the construction is the label of a node of type 1 strictly above `x`, which is
what makes a leaf whose label is in the history a repeat. -/
lemma rhoSat_build (C : LoadedCluster tab) (hF : C.PaperFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    ∀ (Hist : List Sequent) (Δ : Sequent) (x : List Nat),
      C.Q.atOpt x = some (QuasiTab.build C.lambdaTwo C.stepOfL Hist Δ) →
      (∀ Z ∈ Hist, ∃ z, z <+: x ∧ z ≠ x ∧ C.Q.labelAt z = some Z ∧
        C.Q.typAt z = some Typ.one) →
      C.RhoSat θ x := by
  intro Hist Δ
  induction Hist, Δ using QuasiTab.build.induct (inC := C.lambdaTwo) with
  | case1 Hist Δ h IH =>
    intro x hx hHist
    rw [QuasiTab.build_of_node h] at hx
    set next := (C.stepOfL Δ).map
      (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi)
      with hnextdef
    have h2 : C.Q.atOpt (x ++ [0]) = some (.QNode .two Δ [.QNode .three Δ next]) :=
      QuasiTab.atOpt_child hx (by simp)
    have h3 : C.Q.atOpt ((x ++ [0]) ++ [0]) = some (.QNode .three Δ next) :=
      QuasiTab.atOpt_child h2 (by simp)
    have hlab : C.Q.labelAt x = some Δ := by rw [QuasiTab.labelAt, hx]; rfl
    have htyp : C.Q.typAt x = some Typ.one := by rw [QuasiTab.typAt, hx]; rfl
    -- the induction hypothesis for the children of the node of type 3
    have IHchild : ∀ i, i < next.length → C.RhoSat θ ((x ++ [0]) ++ [0] ++ [i]) := by
      intro i hi
      have hi' : i < (C.stepOfL Δ).length := by simpa [hnextdef] using hi
      have hat : C.Q.atOpt ((x ++ [0]) ++ [0] ++ [i])
          = some (QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist)
                    (C.stepOfL Δ)[i]) := by
        rw [QuasiTab.atOpt_child h3 hi]
        simp [hnextdef]
      refine IH (C.stepOfL Δ)[i] _ hat ?_
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ'
      · obtain ⟨hp, -⟩ := prefix_append_ne (z := x) (x := x) (List.prefix_refl x)
          (l := [0]) (by simp)
        obtain ⟨hp2, -⟩ := prefix_append_ne hp (l := [0]) (by simp)
        obtain ⟨hp3, hne3⟩ := prefix_append_ne hp2 (l := [i]) (by simp)
        exact ⟨x, hp3, hne3, hlab, htyp⟩
      · obtain ⟨z, hz1, -, hz3, hz4⟩ := hHist Z hZ'
        obtain ⟨hp, -⟩ := prefix_append_ne hz1 (l := [0]) (by simp)
        obtain ⟨hp2, -⟩ := prefix_append_ne hp (l := [0]) (by simp)
        obtain ⟨hp3, hne3⟩ := prefix_append_ne hp2 (l := [i]) (by simp)
        exact ⟨z, hp3, hne3, hz3, hz4⟩
    -- the node of type 3
    have h3sat : C.RhoSat θ ((x ++ [0]) ++ [0]) := by
      by_cases hb : Δ.basic
      · obtain ⟨Pi, rest, hPi⟩ : ∃ Pi rest, C.stepOfL Δ = Pi :: rest :=
          List.exists_cons_of_ne_nil (C.stepOfL_ne_nil (hF.exists_right Δ h.1))
        have hnextcons :
          next = QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi ::
            rest.map
              (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi) :=
              by rw [hnextdef, hPi, List.map_cons]
        have hPimem : Pi ∈ C.stepOf Δ := by
          have hmem : Pi ∈ C.stepOfL Δ := by rw [hPi]; exact List.mem_cons_self ..
          simpa [stepOfL, Finset.mem_seqSort] using hmem
        refine C.rhoSat_three_basic hF h.1 hb (hnextcons ▸ h3) (by simp) ?_
          (IHchild 0 (by rw [hnextcons]; simp))
        rw [QuasiTab.build_label]
        exact hPimem
      · refine C.rhoSat_three_not_basic hF h.1 hb h3 ?_ IHchild
        intro n hn
        rw [hnextdef, List.mem_map] at hn
        obtain ⟨Pi, hPi, rfl⟩ := hn
        exact ⟨by simp, by simpa [stepOfL] using hPi⟩
    -- the node of type 2 and the node of type 1
    have h2sat : C.RhoSat θ (x ++ [0]) := C.rhoSat_two hF h.1 hθ h2 rfl h3sat
    by_cases hcomp : x ∈ C.Q.companions
    · exact C.rhoSat_one_companion hx hcomp rfl h2sat
    · exact C.rhoSat_one_inner hx hcomp rfl h2sat
  | case2 Hist Δ h =>
    intro x hx hHist
    rw [QuasiTab.build_of_leaf h] at hx
    have hlab : C.Q.labelAt x = some Δ := by rw [QuasiTab.labelAt, hx]; rfl
    cases hc : C.Q.companionOpt x with
    | some c => exact C.rhoSat_one_leaf_repeat hx hc
    | none =>
      refine C.rhoSat_one_leaf_exit hx hc ?_ hθ
      intro hΔ
      have hHistΔ : Δ ∈ Hist := by
        by_contra hn
        exact h ⟨hΔ, hn⟩
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := hHist Δ hHistΔ
      rw [QuasiTab.companionOpt, List.find?_eq_none] at hc
      have hnot := hc z (mem_inits_dropLast_of_prefix_ne hz1 hz2)
      simp only [decide_eq_true_eq, not_and] at hnot
      exact hnot (by rw [hz3, hlab]) hz4

/-- The claim `ρ_x ⊨ ι_x⟨σ⟩` at the root of the quasi-tableau. -/
theorem rhoSat_root (C : LoadedCluster tab) (hF : C.PaperFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    C.RhoSat θ QuasiTab.rootAddress :=
  C.rhoSat_build hF hθ [] (nodeAt C.root).rightOnly QuasiTab.rootAddress rfl (by simp)

/-! ## Lemma 10.3 -/

open HasSat in
/-- Lemma 10.3: `Γ₁ ⊨ θ_r`, i.e. the left component of the root of the cluster together
with the negation of the interpolant of Definition 9.20 is unsatisfiable. -/
theorem left_unsat_neg_itp (C : LoadedCluster tab) (hF : C.PaperFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    ¬ satisfiable ({~ C.itp θ} ∪ (nodeAt C.root).left) := by
  rintro ⟨W, M, w, hw⟩
  have hneg : ¬ evaluate M w (C.itp θ) := hw (~C.itp θ) (by simp_all)
  have hleft : ∀ φ ∈ (nodeAt C.root).left, evaluate M w φ :=
    fun φ hφ => hw φ (by simp_all)
  rw [itp] at hneg
  split at hneg
  case isTrue => exact hneg (by simp)
  case isFalse hΓ₁ =>
    have hroot : C.Q.atOpt QuasiTab.rootAddress = some C.Q := rfl
    have hregion : C.root.toFine ∈ C.regionOf C.Q := by
      rw [regionOf, C.Q_typ, C.Q_label]
      refine C.mem_plusNodesWithFine_of_mem_nodesWithFine ?_
      simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
      exact ⟨C.root_toFine_mem_fineCL, by simp⟩
    have hrho : evaluate M w (C.rho QuasiTab.rootAddress) :=
      (evaluate_rho_iff hroot).mpr ⟨C.root.toFine, hregion, by simpa using hleft⟩
    have hsat : evaluate M w ((C.rootIitp θ).subst C.rho) := C.rhoSat_root hF hθ W M w hrho
    have heq : (C.rootIitp θ).subst C.rho = (C.rootIitp θ).subst (fun _ => ⊤) := by
      refine QFormula.subst_congr _ ?_
      intro v hv
      rw [C.rootIitp_vars hF θ hθ hΓ₁] at hv
      simp at hv
    rw [heq] at hsat
    exact hneg hsat

end LoadedCluster

end PDL
