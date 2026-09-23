/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Tactic.DepRewrite

public import LeanPool.PDL.Soundness

/-! # Flipping a tableau (for section 7)

Like the paper, we only prove interpolation for clusters with a loaded formulas on the right side.
For the case where the loaded formula is on the left, we flip the tableau left-to-right.

The lemmas here then allow us to prove `clusterInterpolation` from `clusterInterpolationRight`.
-/

@[expose] public section

namespace PDL

/-- Exchange the side of an optional loaded formula. -/
def Olf.flip : Olf → Olf := Option.map Sum.swap

@[simp]
lemma Olf.flip_inj {O1 O2 : Olf} : O1.flip = O2.flip ↔ O1 = O2 := by
  rcases O1 with (_|_|_) <;> rcases O2 with (_|_|_) <;> simp_all [Olf.flip]

@[simp]
lemma Olf.flip_flip {O : Olf} : O.flip.flip = O := by
  rcases O with (_|_|_) <;> simp_all [Olf.flip]

@[simp]
lemma Olf.flip_none : Olf.flip none = none := by simp [Olf.flip]

/-- Exchange both sequent components and the side of its loaded formula. -/
def Sequent.flip : Sequent → Sequent := fun ⟨L, R, O⟩ => ⟨R, L, O.flip⟩

@[simp]
lemma Sequent.flip_right {X : Sequent} : X.flip.right = X.left := by
  rcases X with ⟨L,R,_|_|_⟩ <;> simp [Sequent.flip, Olf.flip]

@[simp]
lemma Sequent.flip_left {X : Sequent} : X.flip.left = X.right := by
  rcases X with ⟨L,R,_|_|_⟩ <;> simp [Sequent.flip, Olf.flip]

@[simp]
lemma Sequent.flip_flip {X : Sequent} : X.flip.flip = X := by
  rcases X with ⟨L,R,O⟩
  simp_all [Sequent.flip, Olf.flip]

@[simp]
lemma Sequent.flip_isLoaded {X : Sequent} :
    X.flip.isLoaded ↔ X.isLoaded := by
  rcases X with ⟨L, R, O⟩
  simp only [Sequent.isLoaded, Sequent.flip, Olf.flip]
  grind

@[simp]
lemma Sequent.flip_isFree {X : Sequent} :
    X.flip.isFree ↔ X.isFree := by
  unfold Sequent.isFree
  simp

lemma Sequent.flip_eq_off {X Y : Sequent} : (X.flip = Y) = (X = Y.flip) := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  simp_all only [flip]
  rw [@propext_iff]
  constructor <;> intro h <;> cases h <;> convert rfl <;> simp

lemma Sequent.map_flip_map_flip {Hist} :
    (List.map Sequent.flip (List.map Sequent.flip Hist)) = Hist := by
  induction Hist <;> simp_all

/-- Flipping all sequents in a `Finset` twice gives back the same set. -/
@[simp]
lemma Sequent.image_flip_image_flip {S : Finset Sequent} :
    Finset.image Sequent.flip (Finset.image Sequent.flip S) = S := by
  rw [Finset.image_image]
  simp [Function.comp_def]

@[simp]
lemma basic_flip {X : Sequent} : X.flip.basic ↔ X.basic := by
  rcases X with ⟨L,R,O⟩
  unfold Sequent.basic Sequent.flip
  simp only
  simp only [Sequent.toFinset, Finset.union_assoc, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr,
    Formula.basic, decide_false, decide_true, Sequent.closed, not_or, not_exists, not_and]
  constructor
  · intro ⟨fs_basic, not_closed⟩
    constructor
    · intro φ φ_in
      apply fs_basic
      rcases φ_in with h|h|h|h
      · grind
      · grind
      · right
        right
        right
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, Sum.inr.injEq,
          exists_eq_right, Sum.swap_inr, reduceCtorEq, and_false, exists_false, or_false]
        exact h
      · right
        right
        left
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, reduceCtorEq,
          and_false, exists_false, Sum.swap_inr, Sum.inl.injEq, exists_eq_right, false_or]
        exact h
    · aesop
  · intro ⟨fs_basic, not_closed⟩
    constructor
    · intro φ φ_in
      apply fs_basic
      rcases φ_in with h|h|h|h
      · grind
      · grind
      · right
        right
        right
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, reduceCtorEq,
          and_false, exists_false, Sum.swap_inr, Sum.inl.injEq, exists_eq_right, false_or] at h
        exact h
      · right
        right
        left
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, Sum.inr.injEq,
          exists_eq_right, Sum.swap_inr, reduceCtorEq, and_false, exists_false, or_false] at h
        exact h
    · aesop

/-- Reflect a local rule by exchanging its left and right components. -/
def LocalRule.flip {Lcond Ocond Rcond ress} (lr : LocalRule (Lcond, Rcond, Ocond) ress) :
    LocalRule (Rcond, Lcond, Ocond.flip) (ress.image Sequent.flip) := by
  cases lr
  case oneSidedL YS orule YS_def =>
    apply LocalRule.oneSidedR orule
    aesop
  case oneSidedR YS orule YS_def =>
    apply LocalRule.oneSidedL orule
    aesop
  case LRnegL =>
    apply LocalRule.LRnegR
  case LRnegR =>
    apply LocalRule.LRnegL
  case loadedL YS χ lrule YS_def =>
    apply LocalRule.loadedR _ lrule
    subst YS_def
    rw [Finset.image_image]
    apply Finset.image_congr
    rintro ⟨L, (_|o)⟩ - <;> simp [Sequent.flip, Olf.flip]
  case loadedR lrule YS_def =>
    apply LocalRule.loadedL _ lrule
    subst YS_def
    rw [Finset.image_image]
    apply Finset.image_congr
    rintro ⟨L, (_|o)⟩ - <;> simp [Sequent.flip, Olf.flip]

lemma LocalRule.flip_flip {Lcond Ocond Rcond ress} (lr : LocalRule (Lcond, Rcond, Ocond) ress) :
    lr.flip.flip = Olf.flip_flip ▸ Sequent.image_flip_image_flip ▸ lr := by
  cases lr <;> simp_all [LocalRule.flip] <;> grind

/-- Note: is it possible and useful to rewrite this in more term and less tactic mode? -/
def LocalRuleApp.flip : LocalRuleApp → LocalRuleApp := by
  rintro ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  refine @LocalRuleApp.mk R L O.flip Rcond Lcond Ocond.flip _ rule.flip
    (C.image Sequent.flip) ?_ ?_
  · subst hC
    simp only [applyLocalRule]
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    rintro ⟨Lnew, Rnew, Onew⟩ -
    simp only [Function.comp_apply, Sequent.flip]
    rcases O with (_|_|_) <;> rcases Onew with (_|_|_) <;> rcases Ocond with (_|_|_)
      <;> simp [Olf.flip, Olf.change, SDiff.sdiff] <;> grind
  · rcases preconditionProof with ⟨hL, hR, hO⟩
    refine ⟨hR, hL, ?_⟩
    rcases O with (_|_|_) <;> rcases Ocond with (_|_|_) <;> simp_all [Olf.flip, Sum.swap]

@[simp]
lemma Sequent.flip_comp_flip : Sequent.flip ∘ Sequent.flip = id := by
  ext X
  rw [Function.comp_apply, Sequent.flip_flip, id_eq]

lemma LocalRuleApp.flip_flip {lra : LocalRuleApp} :
    lra.flip.flip = lra := by
  rcases lra with ⟨L, R, O, C, Lcond, Rcond, Ocond, ress, rule, hC, preconditionProof⟩
  simp only [flip, Olf.flip_flip, Sequent.image_flip_image_flip, mk.injEq, and_true, true_and]
  rw [LocalRule.flip_flip]
  grind

lemma Sequent.flip_mem_of_mem_image_flip {B : Finset Sequent} {Y : Sequent} :
    Y ∈ B.image Sequent.flip → Y.flip ∈ B := by aesop

/-- Reflect every rule and branch of a local tableau. -/
def LocalTableau.flip {X} : LocalTableau X → LocalTableau X.flip
  | (@byLocalRule X lra X_def next) => .byLocalRule lra.flip
      (by subst X_def; simp [LocalRuleApp.flip, Sequent.flip])
      (fun Y Y_in =>
        @Sequent.flip_flip Y ▸ (next Y.flip (Sequent.flip_mem_of_mem_image_flip Y_in)).flip)
  | (@sim X Xbas) => .sim (basic_flip.mpr Xbas)

lemma LocalTableau.flip_flip {lt : LocalTableau X} : lt.flip.flip = Sequent.flip_flip ▸ lt := by
  induction lt <;> simp only [flip]
  case byLocalRule X lra X_def next IH =>
    apply eq_of_heq
    rw! (castMode := .all) [Sequent.flip_flip] -- :-)
    simp only [heq_eq_eq, byLocalRule.injEq]
    constructor
    · exact LocalRuleApp.flip_flip
    · refine Function.hfunext rfl ?_
      intro X X' X_heq_X'
      apply Function.hfunext
      · rw [LocalRuleApp.flip_flip]
        grind
      · grind
  · grind

lemma LocalTableau.flip_inj {X} {lt : LocalTableau X} :
    lt.flip.flip = (Sequent.flip_flip ▸ lt) := by
  cases lt
  case byLocalRule =>
    rw [LocalTableau.flip_flip]
  · grind [LocalTableau.flip]

lemma endNodesOf_flip {X} {lt : LocalTableau X} {Y} :
    Y ∈ endNodesOf lt.flip → Y.flip ∈ endNodesOf lt := by
  intro Y_in
  induction lt
  case byLocalRule B next lra IH =>
    simp only [LocalTableau.flip, endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup,
      Finset.mem_attach, true_and, Subtype.exists] at *
    rcases Y_in with ⟨W, W_in_B, Y_in_end⟩
    refine ⟨W.flip, ?_, ?_⟩ <;> grind
  case sim Z Zbas =>
    simp_all [LocalTableau.flip]

lemma exists_flip_of_endNodesOf {X : Sequent} {ltf : LocalTableau X.flip} {Zf} :
     Zf ∈ endNodesOf ltf → ∃ Z, Zf = Z.flip ∧ Z ∈ endNodesOf ltf.flip := by
  intro Z_in
  cases ltf
  case byLocalRule lra next X_def =>
    simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
      true_and, Subtype.exists, LocalTableau.flip] at *
    rcases Z_in with ⟨Yf, Yf_in_B, Zf_via_Yf⟩
    refine ⟨Zf.flip, ?_, ⟨Yf.flip, ?_, ?_⟩⟩
    · simp
    · grind [LocalRuleApp.flip]
    · rw! (castMode := .all) [@Sequent.flip_flip Yf]
      simp only
      apply endNodesOf_flip
      rw [LocalTableau.flip_flip]
      grind
  case sim Xbas =>
    simp_all only [endNodesOf, Finset.mem_singleton, LocalTableau.flip]
    subst_eqs
    simp

/-- Reflect a PDL rule by exchanging the sequent components. -/
def PdlRule.flip {X Y} (r : PdlRule X Y) : PdlRule X.flip Y.flip := by
  cases r
  case loadL L δs α φ R in_L notBox Y_def =>
    apply PdlRule.loadR in_L notBox
    simp_all only [Sequent.flip, Prod.mk.injEq, true_and]
    rfl
  case loadR R δs α φ L in_R notBox Y_def =>
    apply PdlRule.loadL in_R notBox
    simp_all only [Sequent.flip, Prod.mk.injEq, true_and]
    rfl
  case freeL L R δs α φ X_def Y_def =>
    apply PdlRule.freeR
    all_goals
      subst X_def Y_def
      simp_all only [Sequent.flip]
      rfl
  case freeR L R δs α φ X_def Y_def =>
    apply PdlRule.freeL
    all_goals
      subst X_def Y_def
      simp_all only [Sequent.flip]
      rfl
  case modL L R a ξ X_def Y_def =>
    apply @PdlRule.modR Y.flip R L a X.flip ξ
    all_goals
      subst X_def Y_def
      cases ξ <;> simp_all [Sequent.flip,Olf.flip]
  case modR L R a ξ X_def Y_def =>
    apply @PdlRule.modL Y.flip R L a X.flip ξ
    all_goals
      subst X_def Y_def
      cases ξ <;> simp_all [Sequent.flip,Olf.flip]

lemma PdlRule.flip_flip {X Y} (r : PdlRule X Y) :
    r.flip.flip = (Sequent.flip_flip ▸ Sequent.flip_flip ▸ r) := by
  cases r <;> simp [PdlRule.flip] <;> grind

/-- Flipping sequents is injective. -/
@[simp]
lemma Sequent.flip_eq_flip_iff {X Y : Sequent} : X.flip = Y.flip ↔ X = Y := by
  constructor
  · intro h
    rw [← @Sequent.flip_flip X, ← @Sequent.flip_flip Y, h]
  · rintro rfl
    rfl

/-- Reflect a loaded-path repeat, preserving its history position. -/
def LoadedPathRepeat.flip {Hist X} : LoadedPathRepeat Hist X →
    LoadedPathRepeat (List.map Sequent.flip Hist) X.flip
| ⟨k, hk⟩ => by
  refine ⟨⟨k.1, ?_⟩, ?_⟩
  · simp_all [List.length_map]
  · rcases hk with ⟨same, path_loaded⟩
    constructor
    · simp only [List.get_eq_getElem, List.getElem_map, Sequent.flip_eq_flip_iff]
      exact same
    · simp only [List.get_eq_getElem, List.getElem_map, Sequent.flip_isLoaded]
      intro m m_lt
      apply path_loaded ⟨m, by grind⟩
      omega

lemma LoadedPathRepeat.flip_flip {Hist X} (lpr : LoadedPathRepeat Hist X) :
    lpr.flip.flip = Sequent.map_flip_map_flip ▸ Sequent.flip_flip ▸ lpr := by
  rcases lpr with ⟨k, hk⟩
  simp only [flip, List.get_eq_getElem]
  rw! [Sequent.map_flip_map_flip, Sequent.flip_flip]
  rfl

@[simp]
lemma flprep_flip {Hist} :
    flprep (List.map Sequent.flip Hist) X.flip ↔ flprep Hist X := by
  simp_all only [flprep, rep, ↓existsAndEq, List.mem_map, Sequent.flip_eq_flip_iff,
    exists_eq_right, and_true, Sequent.isFree, Sequent.flip_isLoaded]
  refine ⟨?_,?_⟩
  · rintro (frep|⟨⟨lpr⟩⟩ )
    · grind
    · have := lpr.flip
      right
      simp only [List.map_map, Sequent.flip_comp_flip, List.map_id_fun, id_eq, Sequent.flip_flip]
        at this
      exact ⟨this⟩
  · rintro (frep|⟨⟨lpr⟩⟩ )
    · grind
    · have := lpr.flip
      right
      exact ⟨this⟩

/-- Exchange the left and right sides throughout a tableau. -/
def Tableau.flip {Hist X} : Tableau Hist X → Tableau (Hist.map Sequent.flip) X.flip
| .loc nflprep nbas lt next =>  .loc (by simp only [flprep_flip]; exact nflprep)
                                  (by simp only [basic_flip]; exact nbas)
                                  lt.flip
                                  (fun Y Y_in =>
                                   @Sequent.flip_flip Y ▸ (next Y.flip (endNodesOf_flip Y_in)).flip)
| .pdl nflprep bas r next =>  .pdl (by simp only [flprep_flip]; exact nflprep)
                                (by simp only [basic_flip]; exact bas)
                                r.flip
                                next.flip
| .lrep lpr =>  .lrep lpr.flip

lemma Hist_flip {Hist} : List.map Sequent.flip (List.map Sequent.flip Hist) = Hist := by ext; simp

@[simp]
lemma Tableau.flip_flip {Hist X} {tab : Tableau Hist X} :
    tab.flip.flip = Sequent.flip_flip ▸ Hist_flip ▸ tab := by
  induction tab
  case loc Hist X nflprep nbas ltX next IH =>
    simp only [flip]
    rw! [LocalTableau.flip_flip]
    rw! (castMode := .all) [Sequent.flip_flip]
    simp only []
    convert Tableau.loc.congr_simp nflprep nbas ltX next next ?_
    · exact Sequent.map_flip_map_flip
    · exact Sequent.map_flip_map_flip
    case h Y W Y_eq_W Y_in W_in Y_heq_W =>
      subst Y_eq_W
      simp_all only [List.map_map, Sequent.flip_comp_flip, List.map_id_fun, id_eq, heq_eq_eq,
        eqRec_heq_iff]
      specialize IH Y Y_in
      rw! (castMode := .all) [@Sequent.flip_flip Y]
      simp_all
    · exact eq_of_heq (by assumption)
    · apply eqRec_heq_iff.mpr
      rfl
    all_goals rfl
  case pdl r next IH =>
    nth_rewrite 1 [Tableau.flip]
    nth_rewrite 1 [Tableau.flip]
    rw [IH]; clear IH
    rw [PdlRule.flip_flip]
    grind
  case lrep lpr =>
    grind [Tableau.flip, LoadedPathRepeat.flip_flip]

/-- Map a tableau path to the corresponding path in the reflected tableau. -/
def PathIn.flip {Hist X} {tab : Tableau Hist X} : PathIn tab → PathIn tab.flip
  | .nil => .nil
  | @PathIn.loc _ _ nflprep Xnbas ltX next Y Y_in tail =>
      @PathIn.loc _ _ _ _ _ _ Y.flip
        (by apply endNodesOf_flip; grind [LocalTableau.flip_flip])
        (by
          have := tail.flip
          convert this using 1
          · rfl
          · rw! [@Sequent.flip_flip Y]
            rfl
        )
  | .pdl tail => .pdl tail.flip

lemma PathIn_helper {HistA HistB XA XB} {tabA : Tableau HistA XA} {tabB : Tableau HistB XB}
    (hHist : HistA = HistB)
    (hX : XA = XB) :
    tabA = hHist ▸ hX ▸ tabB → PathIn tabA = PathIn tabB := by
  subst_eqs
  simp_all

lemma PathIn_type_flip_flip {Hist} {tab : Tableau Hist X} :
    PathIn tab.flip.flip = PathIn tab := by
  rw [Tableau.flip_flip]
  grind

/-- `Eq.mpr` is a heterogeneous identity. -/
theorem flip_aux_eq_mpr_heq {a b : Sort u} (h : a = b) (x : b) : HEq (Eq.mpr h x) x := by
  cases h; rfl

/-- Flipping a tableau twice gives back (heterogeneously) the original tableau. -/
theorem flip_aux_Tableau_flip_flip_heq {H X} (t : Tableau H X) : HEq t.flip.flip t := by
  rw [Tableau.flip_flip]; exact eqRec_heq_iff.mpr (eqRec_heq_iff.mpr HEq.rfl)

/-- Flipping a local tableau twice gives back (heterogeneously) the original one. -/
theorem flip_aux_LocalTableau_flip_flip_heq {X} (lt : LocalTableau X) : HEq lt.flip.flip lt := by
  rw [LocalTableau.flip_flip]; exact eqRec_heq_iff.mpr HEq.rfl

/-- Flipping a pdl rule twice gives back (heterogeneously) the original one. -/
theorem flip_aux_PdlRule_flip_flip_heq {X Y} (r : PdlRule X Y) : HEq r.flip.flip r := by
  rw [PdlRule.flip_flip]; exact eqRec_heq_iff.mpr (eqRec_heq_iff.mpr HEq.rfl)

/-- End nodes are invariant under flipping a local tableau twice. -/
theorem endNodesOf_flip_flip {X} (lt : LocalTableau X) :
    endNodesOf lt.flip.flip = endNodesOf lt := by
  rw [LocalTableau.flip_flip]; congr 1
  · exact Sequent.flip_flip
  · exact eqRec_heq _ _

/-- `PathIn.flip` respects heterogeneous equality of paths. -/
theorem PathIn_flip_heq {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) :
    HEq p1.flip p2.flip := by
  subst hH hX; obtain rfl := eq_of_heq ht; rw [eq_of_heq hp]

/-- `Tableau.flip` respects heterogeneous equality of tableaux. -/
theorem Tableau_flip_heq {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    (hH : H1 = H2) (hX : X1 = X2) (h : HEq t1 t2) : HEq t1.flip t2.flip := by
  subst hH hX; rw [eq_of_heq h]

/-- Flipping a path twice gives back (after casting along `PathIn_type_flip_flip`)
the original path. -/
theorem PathIn.flip_flip {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    PathIn_type_flip_flip ▸ (p.flip.flip) = p := by
  induction p with
  | nil =>
    apply eq_of_heq
    rw [eqRec_heq_iff]
    simp only [PathIn.flip]
    congr 1 <;> simp
  | @pdl Hist X Y nflprep bas r next tail IH =>
    apply eq_of_heq
    rw [eqRec_heq_iff]
    simp only [PathIn.flip]
    have hIH : HEq (tail.flip.flip) tail := eqRec_heq_iff.mp (heq_of_eq IH)
    have hr : HEq r.flip.flip r := by
      rw [PdlRule.flip_flip, eqRec_heq_iff, eqRec_heq_iff]
    have hnext : HEq next.flip.flip next := by
      rw! [Tableau.flip_flip]; rw [eqRec_heq_iff, eqRec_heq_iff]
    congr 1 <;> first
      | rfl | exact hIH | exact hr | exact hnext | exact proof_irrel_heq _ _ | simp_all
  | @loc Hist X nflprep nbas lt next Y Y_in tail IH =>
    apply eq_of_heq
    rw [eqRec_heq_iff]
    simp only [PathIn.flip]
    have htail : HEq (tail.flip.flip) tail := eqRec_heq_iff.mp (heq_of_eq IH)
    congr 1
    case e_1 => simp
    case e_2 => simp
    case e_5 => rw [LocalTableau.flip_flip, eqRec_heq_iff]
    case e_6 =>
      apply Function.hfunext rfl
      intro a a' ha
      obtain rfl := eq_of_heq ha
      apply Function.hfunext
      · rw [endNodesOf_flip_flip]
      · intro b b' hb
        simp only [eqRec_heq_iff]
        refine HEq.trans (Tableau_flip_heq (by simp) (by simp)
          (eqRec_heq_iff.mpr HEq.rfl)) ?_
        refine HEq.trans (flip_aux_Tableau_flip_flip_heq _) ?_
        rw! (castMode := .all) [Sequent.flip_flip]
        apply heq_of_eq; congr 1
    case e_9 =>
      refine HEq.trans ?_ htail
      refine HEq.trans (flip_aux_eq_mpr_heq _ _) ?_
      refine PathIn_flip_heq (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)
      simp only [eqRec_heq_iff]
      refine Tableau_flip_heq (by simp) (by simp) ?_
      rw! (castMode := .all) [Sequent.flip_flip]
      apply heq_of_eq; congr 1
    all_goals (try exact proof_irrel_heq _ _)
    all_goals (try (simp))
/-- Undo `PathIn.flip`: flipping twice is the identity (up to the cast). -/
def PathIn.unflip {X} {tab : Tableau .nil X} (p : PathIn tab.flip) : PathIn tab :=
  PathIn_type_flip_flip ▸ p.flip

@[simp]
lemma PathIn.flip_unflip {X} {tab : Tableau .nil X} (p : PathIn tab.flip) :
    p.unflip.flip = p := by
  apply eq_of_heq
  refine HEq.trans ?_ (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip p)))
  refine PathIn_flip_heq (by simp) (by simp) ((flip_aux_Tableau_flip_flip_heq tab).symm) ?_
  unfold PathIn.unflip
  exact cast_heq _ _

/-- A child of a `loc` path is again a `loc` path with the same first step. -/
lemma edge_loc_shape {Hist X Y} {nrep nbas} {lt : LocalTableau X}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    {Y_in : Y ∈ endNodesOf lt} {t : PathIn (next Y Y_in)}
    {q : PathIn (Tableau.loc nrep nbas lt next)} :
    (PathIn.loc Y_in t) ⋖_ q → ∃ s, q = PathIn.loc Y_in s ∧ t ⋖_ s := by
  rintro (⟨Hist', X', nrep', nbas', lt', next', Z, Z_in, h, rfl⟩
        | ⟨Hist', X', nrep', bas', Z, r, next', h, rfl⟩)
  · exact ⟨t.append (h ▸ PathIn.loc Z_in .nil), rfl,
      Or.inl ⟨Hist', X', nrep', nbas', lt', next', Z, Z_in, h, rfl⟩⟩
  · exact ⟨t.append (h ▸ PathIn.pdl .nil), rfl,
      Or.inr ⟨Hist', X', nrep', bas', Z, r, next', h, rfl⟩⟩

/-- A child of a `pdl` path is again a `pdl` path. -/
lemma edge_pdl_shape {Hist X Y} {nrep bas} {r : PdlRule X Y} {nx : Tableau (X :: Hist) Y}
    {t : PathIn nx} {q : PathIn (Tableau.pdl nrep bas r nx)} :
    (PathIn.pdl t) ⋖_ q → ∃ s, q = PathIn.pdl s ∧ t ⋖_ s := by
  rintro (⟨Hist', X', nrep', nbas', lt', next', Z, Z_in, h, rfl⟩
        | ⟨Hist', X', nrep', bas', Z, r', next', h, rfl⟩)
  · exact ⟨t.append (h ▸ PathIn.loc Z_in .nil), rfl,
      Or.inl ⟨Hist', X', nrep', nbas', lt', next', Z, Z_in, h, rfl⟩⟩
  · exact ⟨t.append (h ▸ PathIn.pdl .nil), rfl,
      Or.inr ⟨Hist', X', nrep', bas', Z, r', next', h, rfl⟩⟩

/-- A path of length zero is the empty path. -/
lemma PathIn.eq_nil_of_length_zero {Hist X} {tab : Tableau Hist X} {p : PathIn tab} :
    p.length = 0 → p = .nil := by
  cases p <;> simp

/-- The `edge` relation only depends on paths up to heterogeneous equality. -/
lemma edge_heq_congr {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 q1 : PathIn t1} {p2 q2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) (hq : HEq q1 q2) :
    (p1 ⋖_ q1) ↔ (p2 ⋖_ q2) := by
  subst hH hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp, eq_of_heq hq]

/-- The length of a path only depends on it up to heterogeneous equality. -/
lemma PathIn.length_heq_congr {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) :
    p1.length = p2.length := by
  subst hH hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp]

/-- Flipping a path does not change its length. -/
lemma PathIn.flip_length {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    p.flip.length = p.length := by
  induction p
  case nil => simp [PathIn.flip]
  case loc Hist X nflprep nbas lt next Y Y_in tail IH =>
    simp only [PathIn.flip, PathIn.length]
    rw [← IH]
    congr 1
    refine PathIn.length_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)
    refine HEq.trans (eqRec_heq _ _) ?_
    exact Tableau_flip_heq (by simp) (by simp) (by congr 1 <;> simp)
  case pdl IH => simp only [PathIn.flip, PathIn.length]; rw [IH]

/-- Variant of `nil_edge_loc_nil` where the tail is only known to have length zero. -/
lemma nil_edge_loc_of_length_zero {Hist X Y} {nrep nbas} {lt : LocalTableau X}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    {Y_in : Y ∈ endNodesOf lt} {u : PathIn (next Y Y_in)} (hu : u.length = 0) :
    (.nil : PathIn (Tableau.loc nrep nbas lt next)) ⋖_ (PathIn.loc Y_in u) := by
  rw [PathIn.eq_nil_of_length_zero hu]
  exact nil_edge_loc_nil

/-- Variant of `nil_edge_pdl_nil` where the tail is only known to have length zero. -/
lemma nil_edge_pdl_of_length_zero {Hist X Y} {nrep bas} {r : PdlRule X Y}
    {nx : Tableau (X :: Hist) Y} {u : PathIn nx} (hu : u.length = 0) :
    (.nil : PathIn (Tableau.pdl nrep bas r nx)) ⋖_ (PathIn.pdl u) := by
  rw [PathIn.eq_nil_of_length_zero hu]
  exact nil_edge_pdl_nil

/-- Flipping a tableau preserves the child relation. -/
lemma edge_flip_of_edge {Hist X} {tab : Tableau Hist X} :
    ∀ (p q : PathIn tab), p ⋖_ q → p.flip ⋖_ q.flip := by
  intro p
  induction p with
  | nil =>
    intro q pq
    cases q with
    | nil => exact absurd pq edge_is_irreflexive
    | loc Y_in s =>
      have hs : s.length = 0 := by
        have := length_succ_eq_length_of_edge pq
        simp only [PathIn.length] at this
        omega
      simp only [PathIn.flip, Tableau.flip]
      apply nil_edge_loc_of_length_zero
      refine (PathIn.length_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)).trans ?_
      · exact HEq.trans (eqRec_heq _ _) (Tableau_flip_heq (by simp) (by simp)
          (by congr 1 <;> simp))
      · rw [PathIn.flip_length]; exact hs
    | pdl s =>
      have hs : s.length = 0 := by
        have := length_succ_eq_length_of_edge pq
        simp only [PathIn.length] at this
        omega
      simp only [PathIn.flip, Tableau.flip]
      exact nil_edge_pdl_of_length_zero (by rw [PathIn.flip_length]; exact hs)
  | loc Y_in t IH =>
    intro q pq
    obtain ⟨s, rfl, ts⟩ := edge_loc_shape pq
    simp only [PathIn.flip, Tableau.flip]
    rw [loc_edge_loc_iff_edge]
    refine (edge_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)
      (flip_aux_eq_mpr_heq _ _)).mpr (IH s ts)
    exact HEq.trans (eqRec_heq _ _) (Tableau_flip_heq (by simp) (by simp)
      (by congr 1 <;> simp))
  | pdl t IH =>
    intro q pq
    obtain ⟨s, rfl, ts⟩ := edge_pdl_shape pq
    simp only [PathIn.flip, Tableau.flip]
    rw [pdl_edge_pdl_iff_edge]
    exact IH s ts

/-- Flipping a tableau does not change which nodes are children of which. -/
lemma edge_flip {H X} {tab : Tableau H X} {p q : PathIn tab} :
    (p.flip ⋖_ q.flip) ↔ p ⋖_ q := by
  constructor
  · intro h
    refine (edge_heq_congr (H2 := H) (X2 := X) (by simp) (by simp)
      (flip_aux_Tableau_flip_flip_heq tab)
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip p)))
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip q)))).mp (edge_flip_of_edge _ _ h)
  · exact edge_flip_of_edge p q

/-- The tableau at a path only depends on it up to heterogeneous equality. -/
lemma tabAt_heq_congr {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) :
    tabAt p1 = tabAt p2 := by
  subst hH hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp]

/-- The history of a path only depends on it up to heterogeneous equality. -/
lemma toHistory_heq_congr {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) :
    p1.toHistory = p2.toHistory := by
  subst hH hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp]

/-- The tableau at a flipped path is the flip of the tableau at the original path. -/
lemma tabAt_flip {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    tabAt p.flip
      = ⟨List.map Sequent.flip (tabAt p).1, (tabAt p).2.1.flip, (tabAt p).2.2.flip⟩ := by
  induction p
  case nil => simp [PathIn.flip, tabAt]
  case loc Hist X nflprep nbas lt next Y Y_in tail IH =>
    simp only [PathIn.flip, Tableau.flip]
    change _ = (⟨List.map Sequent.flip (tabAt tail).1, (tabAt tail).2.1.flip,
      (tabAt tail).2.2.flip⟩ : Σ H X, Tableau H X)
    rw [← IH]
    refine Eq.trans tabAt_loc (tabAt_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _))
    exact HEq.trans (eqRec_heq _ _) (Tableau_flip_heq (by simp) (by simp)
      (by congr 1 <;> simp))
  case pdl IH =>
    simp only [PathIn.flip]
    exact IH

/-- The sequent at a flipped path is the flip of the sequent at the original path. -/
lemma PathIn.nodeAt_flip {Hist X} {tab : Tableau Hist X} {e : PathIn tab} :
    nodeAt (e.flip) = (nodeAt e).flip := by
  unfold nodeAt
  rw [tabAt_flip]

/-- The history of a flipped path is the flip of the history of the original path. -/
lemma toHistory_flip {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    p.flip.toHistory = List.map Sequent.flip p.toHistory := by
  induction p
  case nil => simp [PathIn.flip, PathIn.toHistory]
  case loc Hist X nflprep nbas lt next Y Y_in tail IH =>
    simp only [PathIn.flip, PathIn.toHistory, List.map_append, List.map_cons, List.map_nil]
    rw [← IH]
    congr 1
    refine toHistory_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)
    exact HEq.trans (eqRec_heq _ _) (Tableau_flip_heq (by simp) (by simp)
      (by congr 1 <;> simp))
  case pdl IH =>
    simp only [PathIn.flip, PathIn.toHistory, List.map_append, List.map_cons, List.map_nil]
    rw [IH]

/-- Rewinding only depends on the path up to heterogeneous equality,
and on the index only via its value. -/
lemma PathIn.rewind_heq_congr {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2} {k1 : Fin (p1.toHistory.length + 1)}
    {k2 : Fin (p2.toHistory.length + 1)}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) (hk : (k1 : ℕ) = (k2 : ℕ)) :
    HEq (p1.rewind k1) (p2.rewind k2) := by
  subst hH hX
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hp
  obtain rfl : k1 = k2 := Fin.ext hk
  rfl

/-- Flipping commutes with rewinding. -/
lemma PathIn.flip_rewind {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    ∀ (k : Fin (p.toHistory.length + 1)) (k' : Fin (p.flip.toHistory.length + 1)),
    (k : ℕ) = (k' : ℕ) → (p.rewind k).flip = p.flip.rewind k' := by
  induction p
  case nil =>
    intro k k' hk
    simp [PathIn.rewind, PathIn.flip]
  case loc Hist X nflprep nbas lt next Y Y_in tail IH =>
    have hL : ((PathIn.loc Y_in tail :
        PathIn (Tableau.loc nflprep nbas lt next)).flip).toHistory.length
        = tail.toHistory.length + 1 := by rw [toHistory_flip]; simp
    simp only [PathIn.flip, Tableau.flip] at hL
    simp only [PathIn.flip, Tableau.flip]
    intro k k' hk
    cases k using Fin.lastCases with
    | last =>
      cases k' using Fin.lastCases with
      | last => simp [PathIn.rewind, PathIn.flip, Tableau.flip]
      | cast j' =>
        exfalso
        have hj := j'.isLt
        simp only [Fin.val_last, Fin.val_castSucc, PathIn.loc_length_eq] at hk
        omega
    | cast j =>
      cases k' using Fin.lastCases with
      | last =>
        exfalso
        have hj := j.isLt
        simp only [PathIn.loc_length_eq] at hj
        simp only [Fin.val_last, Fin.val_castSucc] at hk
        rw [hL] at hk
        omega
      | cast j' =>
        simp only [PathIn.rewind, Fin.lastCases_castSucc, Function.comp_apply, PathIn.flip]
        congr 1
        have hlen : tail.flip.toHistory.length = tail.toHistory.length := by
          rw [toHistory_flip]; simp
        have hm : (j : ℕ) < tail.flip.toHistory.length + 1 := by
          have := j.isLt
          simp only [PathIn.loc_length_eq] at this
          omega
        apply eq_of_heq
        refine HEq.trans (flip_aux_eq_mpr_heq _ _) ?_
        rw [IH (Fin.cast (PathIn.loc_length_eq Y_in tail) j) ⟨j, hm⟩ rfl]
        refine PathIn.rewind_heq_congr (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _).symm ?_
        · exact (HEq.trans (eqRec_heq _ _) (Tableau_flip_heq (by simp) (by simp)
            (by congr 1 <;> simp))).symm
        · simp only [Fin.val_castSucc] at hk
          simpa only [Fin.val_cast] using hk
  case pdl Hist X Z nrep bas r nx tail IH =>
    simp only [PathIn.flip, Tableau.flip]
    intro k k' hk
    cases k using Fin.lastCases with
    | last =>
      cases k' using Fin.lastCases with
      | last => simp [PathIn.rewind, PathIn.flip, Tableau.flip]
      | cast j' =>
        exfalso
        have := j'.isLt
        simp only [Fin.val_last, Fin.val_castSucc, PathIn.pdl_length_eq] at hk this
        rw [toHistory_flip] at this
        simp at this
        omega
    | cast j =>
      cases k' using Fin.lastCases with
      | last =>
        exfalso
        have := j.isLt
        simp only [Fin.val_last, Fin.val_castSucc, PathIn.pdl_length_eq] at hk this
        rw [toHistory_flip] at hk
        simp at hk
        omega
      | cast j' =>
        simp only [PathIn.rewind, Fin.lastCases_castSucc, Function.comp_apply, PathIn.flip]
        congr 1
        refine IH _ _ ?_
        simp only [Fin.val_castSucc] at hk
        simpa using hk

/-- If a path ends in a loaded-path-repeat, then so does the flipped path,
with a repeat at the same position in the history. -/
lemma tabAt_flip_lrep {Hist X} {tab : Tableau Hist X} (p : PathIn tab) lpr
    (h : (tabAt p).2.2 = .lrep lpr) :
    ∃ lpr' : LoadedPathRepeat (tabAt p.flip).1 (tabAt p.flip).2.1,
      (tabAt p.flip).2.2 = .lrep lpr' ∧ (lpr'.1 : ℕ) = (lpr.1 : ℕ) := by
  rw [tabAt_flip p, h]
  refine ⟨lpr.flip, by simp [Tableau.flip], ?_⟩
  rcases lpr with ⟨k, hk⟩
  simp [LoadedPathRepeat.flip]

/-- Flipping a tableau preserves the companion relation. -/
lemma companion_flip_of_companion {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ♥ q → p.flip ♥ q.flip := by
  rintro ⟨lpr, h, rfl⟩
  obtain ⟨lpr', h', hval⟩ := tabAt_flip_lrep p lpr h
  refine ⟨lpr', h', ?_⟩
  unfold companionOf
  apply PathIn.flip_rewind
  simp [hval]

/-- Flipping a tableau preserves the `cEdge` relation `◃`. -/
lemma cEdge_flip_of_cEdge {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃ q → p.flip ◃ q.flip := by
  rintro (h | h)
  · exact Or.inl (edge_flip_of_edge _ _ h)
  · exact Or.inr (companion_flip_of_companion h)

/-- Flipping a tableau preserves reachability via `◃`. -/
lemma cReach_flip_of_cReach {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃* q → p.flip ◃* q.flip := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (cEdge_flip_of_cEdge hstep)

/-- Flipping a tableau preserves chains of `◃`. (Note the ⁺ instead of *.) -/
lemma cEdgeTrans_flip_of_cEdgeTrans {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    p ◃⁺ q → p.flip ◃⁺ q.flip := by
  intro h
  induction h with
  | single h => apply Relation.TransGen.single (cEdge_flip_of_cEdge h)
  | tail _ hstep ih => exact ih.tail (cEdge_flip_of_cEdge hstep)

/-- Reachability via `◃` only depends on paths up to heterogeneous equality. -/
lemma cReach_heq_congr {X1 X2} {t1 : Tableau [] X1} {t2 : Tableau [] X2}
    {p1 q1 : PathIn t1} {p2 q2 : PathIn t2}
    (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) (hq : HEq q1 q2) :
    (p1 ◃* q1) ↔ (p2 ◃* q2) := by
  subst hX
  obtain rfl := eq_of_heq ht
  rw [eq_of_heq hp, eq_of_heq hq]

/-- Flipping a tableau changes neither the child nor the companion relation,
hence it also does not change reachability. -/
lemma cReach_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ◃* q.flip) ↔ p ◃* q := by
  constructor
  · intro h
    exact (cReach_heq_congr (X2 := X) (by simp) (flip_aux_Tableau_flip_flip_heq tab)
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip p)))
      (eqRec_heq_iff.mp (heq_of_eq (PathIn.flip_flip q)))).mp (cReach_flip_of_cReach h)
  · exact cReach_flip_of_cReach

lemma cEquiv_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ≡ᶜ q.flip) ↔ p ≡ᶜ q := by
  unfold cEquiv
  rw [cReach_flip, cReach_flip]

end PDL
