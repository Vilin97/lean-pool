/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoReductionChain
public import LeanPool.MarshallHall.MarshallHall.GrushkoUnsafe


/-!
## The full arbitrary-factor reduction

This file connects the local fold/unfold/contraction constructions to the
strong induction needed for the Grushko--Neumann theorem.  The first layer is
the change-of-basepoint transport used when the monochromatic run begins away
from the marked base.
-/

@[expose] public section




open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} [Group G] [Group H]
  {V : Type v} [Fintype V] [qV : Quiver V]
  [hV : HasInvolutiveReverse V]
  [∀ a b : V, Fintype (a ⟶ b)]

/-! ### Forgetting orientations of symmetrized paths -/

/-- Turns a formal reverse arrow into the actual reverse in an involutive quiver. -/
def symmArrowHom {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V qV) a b) :
    @Quiver.Hom V qV (show V from a) (show V from b) :=
  match e with
  | Sum.inl f => f
  | Sum.inr f => Quiver.reverse f

/-- Forgets formal symmetrization by replacing reversed arrows with their actual reverses. -/
def ordinaryPathOfSymm : ∀ {a b : Symmetrify V},
    @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V qV) a b →
      @Quiver.Path V qV (show V from a) (show V from b)
  | _, _, Path.nil => Path.nil
  | _, _, Path.cons p e =>
      (ordinaryPathOfSymm p).comp (symmArrowHom e).toPath

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem ordinaryPathOfSymm_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) a b) :
    L.pathRead (ordinaryPathOfSymm p) = L.symmPathRead p := by
  induction p with
  | nil =>
      simp only [ordinaryPathOfSymm, BinaryLabelling.symmPathRead_nil]
      simp only [BinaryLabelling.pathRead, BinaryLabelling.pathLabels,
        factorWordProd]
  | @cons z y p e ih =>
      simp only [ordinaryPathOfSymm]
      change L.pathRead
          ((ordinaryPathOfSymm p).comp (symmArrowHom e).toPath) =
        L.symmPathRead (p.comp e.toPath)
      rw [L.pathRead_comp, ih, L.pathRead_toPath,
        L.symmPathRead_comp, L.symmPathRead_toPath]
      cases e with
      | inl f => rfl
      | inr f =>
          exact congrArg (L.symmPathRead p * ·)
            (congrArg separatedMap (L.reverse_label f))

/-! ### Change of basepoint -/

/-- Moves the base vertex of a marked graph along a chosen path. -/
def rerootMarkedGraph {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {r : V} (t : @Quiver.Path V qV M.base r) :
    @MarkedBinaryGraph G H V _ _ qV hV n :=
  { base := r
    labeling := M.labeling
    loops := fun i => t.reverse.comp ((M.loops i).comp t) }

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem rerootMarkedGraph_read {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {r : V} (t : @Quiver.Path V qV M.base r)
    (ht : M.labeling.pathRead t = 1) :
    (rerootMarkedGraph M t).read = M.read := by
  funext i
  change M.labeling.pathRead
      (t.reverse.comp ((M.loops i).comp t)) = M.read i
  rw [M.labeling.pathRead_comp, M.labeling.pathRead_comp,
    M.labeling.pathRead_reverse, ht]
  simp only [inv_one, one_mul, mul_one]
  change M.labeling.pathRead (M.loops i) =
    M.labeling.pathRead (M.loops i)
  rfl

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem rerootMarkedGraph_isGenerating {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {r : V} (t : @Quiver.Path V qV M.base r)
    (ht : M.labeling.pathRead t = 1) (hgen : M.IsGenerating) :
    (rerootMarkedGraph M t).IsGenerating := by
  change Subgroup.closure (Set.range (rerootMarkedGraph M t).read) = ⊤
  rw [rerootMarkedGraph_read M t ht]
  exact hgen

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem rerootMarkedGraph_weaklyConnected {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {r : V} (t : @Quiver.Path V qV M.base r)
    (hconn : M.WeaklyConnected) :
    (rerootMarkedGraph M t).WeaklyConnected := by
  intro v
  obtain ⟨p⟩ := hconn v
  refine ⟨?_⟩
  exact ((@Quiver.Symmetrify.of V qV).mapPath t).reverse.comp p

/-! ### The reduction package used by the global induction -/

/-- Every generating connected marked graph with a reduced null run admits the required reducing
fold. -/
def HasReducedNullFold : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [qW : Quiver.{0, 0} W]
    [_hW : HasInvolutiveReverse W]
    [_hHomW : ∀ a b : W, Fintype (@Quiver.Hom W qW a b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := W) n),
    ReverseFree (V := W) → M.IsGenerating → M.WeaklyConnected →
      Fintype.card (AllArrow (V := W)) ≤
        2 * (n + Fintype.card W - 1) →
      1 < Fintype.card W →
      ∃ U : Type,
      ∃ hFU : Fintype U,
      ∃ qU : Quiver.{0, 0} U,
      ∃ hU : @HasInvolutiveReverse U qU,
      ∃ hHomU : ∀ a b : U, Fintype (@Quiver.Hom U qU a b),
        letI : Fintype U := hFU
        letI : Quiver U := qU
        letI : HasInvolutiveReverse U := hU
        letI (a b : U) : Fintype (a ⟶ b) := hHomU a b
        ∃ N : @MarkedBinaryGraph G H U _ _ qU hU n,
          Fintype.card U < Fintype.card W ∧
          @ReverseFree U qU hU ∧
          @MarkedBinaryGraph.IsGenerating n G H U _ _ qU hU N ∧
          @MarkedBinaryGraph.WeaklyConnected n G H U _ _ qU hU N ∧
          Fintype.card (@AllArrow U qU) ≤
            2 * (n + Fintype.card U - 1)

private theorem null_path_tail_read
    {V : Type} [qV : Quiver.{0, 0} V] [HasInvolutiveReverse V]
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    {a b c : Symmetrify V} (e : a ⟶ b) (q : Path b c)
    (h : L.symmPathRead (e.toPath.comp q) = 1) :
    L.symmPathRead q = (separatedMap (allArrowLabel L (symmOrientedArrow e)))⁻¹ := by
  rw [L.symmPathRead_comp] at h
  have hq := eq_inv_of_mul_eq_one_right h
  rw [L.symmPathRead_toPath] at hq
  simpa [symmLabel_eq_allArrowLabel_oriented] using hq

theorem exists_reduced_graph_of_minimal_null_path
    {V : Type} [Fintype V] [qV : Quiver.{0, 0} V]
    [hV : HasInvolutiveReverse V]
    [hHom : ∀ a b : V, Fintype (@Quiver.Hom V qV a b)]
    {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (hfree : ReverseFree (V := V)) (hgen : M.IsGenerating)
    (hconn : M.WeaklyConnected)
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1))
    {v : V} (hv : v ≠ M.base)
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V qV)
      (show Symmetrify V from M.base) (show Symmetrify V from v))
    (hp : M.labeling.symmPathRead p = 1)
    (hminimal : ∀ q : @Quiver.Path (Symmetrify V)
        (@Quiver.symmetrifyQuiver V qV)
        (show Symmetrify V from M.base) (show Symmetrify V from v),
        M.labeling.symmPathRead q = 1 → ¬ q.length < p.length) :
    ∃ U : Type,
      ∃ hFU : Fintype U,
      ∃ qU : Quiver.{0, 0} U,
      ∃ hU : @HasInvolutiveReverse U qU,
      ∃ hHomU : ∀ a b : U, Fintype (@Quiver.Hom U qU a b),
        letI : Fintype U := hFU
        letI : Quiver U := qU
        letI : HasInvolutiveReverse U := hU
        letI (a b : U) : Fintype (a ⟶ b) := hHomU a b
        ∃ N : @MarkedBinaryGraph G H U _ _ qU hU n,
          Fintype.card U < Fintype.card V ∧
          @ReverseFree U qU hU ∧
          @MarkedBinaryGraph.IsGenerating n G H U _ _ qU hU N ∧
          @MarkedBinaryGraph.WeaklyConnected n G H U _ _ qU hU N ∧
          Fintype.card (@AllArrow U qU) ≤
            2 * (n + Fintype.card U - 1) := by
  obtain ⟨r, hr, hrread, hrnonloop⟩ :=
    BinaryLabelling.exists_null_nonloop_run_of_minimal_null_path
      (L := M.labeling) p (by
        intro hzero
        apply hv
        exact (@Path.eq_of_length_zero (Symmetrify V)
          (@Quiver.symmetrifyQuiver V qV) M.base v p hzero).symm)
      hp hminimal
  obtain ⟨c, e, q, hsplit⟩ :=
    BinaryLabelling.exists_first_edge_comp (V := V) r.path r.nonempty
  have hecolor : binarySumIndex (G := G) (H := H)
      (M.labeling.symmLabel e) = r.color := by
    apply r.monochromatic
    rw [hsplit, M.labeling.symmPathLabels_comp]
    exact List.mem_append.mpr (Or.inl (by simp))
  have hqmono : M.labeling.symmIsMonochromatic q r.color := by
    intro z hz
    apply r.monochromatic z
    rw [hsplit, M.labeling.symmPathLabels_comp]
    exact List.mem_append.mpr (Or.inr hz)
  have hqread : M.labeling.symmPathRead q =
      (separatedMap (allArrowLabel M.labeling (symmOrientedArrow e)))⁻¹ :=
    null_path_tail_read M.labeling e q (by rw [← hsplit]; exact hrread)
  obtain ⟨t, ht⟩ := M.exists_null_path hgen
    (hconn (show V from r.source))
  let tOrd : @Quiver.Path V qV M.base (show V from r.source) :=
    ordinaryPathOfSymm t
  have htOrd : M.labeling.pathRead tOrd = 1 := by
    exact (ordinaryPathOfSymm_read M.labeling t).trans ht
  let Mroot : MarkedBinaryGraph (G := G) (H := H) (V := V) n :=
    rerootMarkedGraph M tOrd
  have hrootgen : Mroot.IsGenerating := by
    dsimp [Mroot]
    exact rerootMarkedGraph_isGenerating M tOrd htOrd hgen
  have hrootconn : Mroot.WeaklyConnected := by
    dsimp [Mroot]
    exact rerootMarkedGraph_weaklyConnected M tOrd hconn
  let e₀ : AllArrow (V := V) := symmOrientedArrow e
  have ha₀ : allArrowSource e₀ = Mroot.base := by
    change allArrowSource (symmOrientedArrow e) = (show V from r.source)
    exact symmOrientedArrow_source e
  have hb₀ : (show V from r.target) ≠ allArrowSource e₀ := by
    intro h
    apply hrnonloop
    calc
      (show V from r.source) = allArrowSource e₀ := by
        change (show V from r.source) = allArrowSource (symmOrientedArrow e)
        exact (symmOrientedArrow_source e).symm
      _ = (show V from r.target) := h.symm
  have hstart : (show V from c) = allArrowTarget e₀ := by
    change (show V from c) = allArrowTarget (symmOrientedArrow e)
    cases e <;> rfl
  let q₀ := hstart ▸ q
  have hq₀ : Mroot.labeling.symmIsMonochromatic q₀
      (unfoldEdgeColor Mroot.labeling e₀) := by
    have hqmono₀ : M.labeling.symmIsMonochromatic q₀ r.color := by
      intro z hz
      apply hqmono z
      have hlabels : M.labeling.symmPathLabels (hstart ▸ q) =
          M.labeling.symmPathLabels q := by
        exact M.labeling.symmPathLabels_cast hstart rfl q
      change z ∈ M.labeling.symmPathLabels (hstart ▸ q) at hz
      rw [hlabels] at hz
      exact hz
    rw [show Mroot.labeling = M.labeling from rfl]
    have hcolor : unfoldEdgeColor M.labeling e₀ =
        binarySumIndex (G := G) (H := H) (M.labeling.symmLabel e) := by
      dsimp [unfoldEdgeColor, e₀]
      rw [symmLabel_eq_allArrowLabel_oriented]
    rw [hcolor, hecolor]
    exact hqmono₀
  have hread₀ : Mroot.labeling.symmPathRead q₀ =
      (separatedMap (allArrowLabel Mroot.labeling e₀))⁻¹ := by
    rw [show Mroot.labeling = M.labeling from rfl]
    change M.labeling.symmPathRead q₀ =
      (separatedMap (allArrowLabel M.labeling
        (symmOrientedArrow e)))⁻¹
    have hcast : M.labeling.symmPathRead (hstart ▸ q) =
        M.labeling.symmPathRead q := by
      exact M.labeling.symmPathRead_cast hstart rfl q
    rw [show q₀ = hstart ▸ q by rfl, hcast, hqread]
  have hs := exists_safe_fold_after_unfold
    (M := Mroot) e₀ ha₀ q₀ hb₀ hq₀ hread₀ hrootgen hrootconn
  dsimp only at hs
  obtain ⟨e₁, ha₁, q₁, hq₁, hgen₁, hconn₁, hcard₁⟩ := hs
  let : Fintype (UnfoldVertex (allArrowSource e₀)) :=
    unfoldVertexFintype (allArrowSource e₀)
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver Mroot.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse Mroot.labeling e₀
  let (x y : UnfoldVertex (allArrowSource e₀)) : Fintype (x ⟶ y) :=
    unfoldQuiverHomFintype Mroot.labeling e₀ x y
  let : Fintype (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) :=
    foldVertexFintype (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))
  let : Quiver (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) :=
    foldQuiver e₁
  let : HasInvolutiveReverse (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) :=
    foldHasReverse e₁
  let (x y : foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) :
      Fintype (x ⟶ y) :=
    foldQuiverHomFintype e₁ x y
  have hrem := exists_removed_of_unfold_fold
    (M := Mroot) e₀ ha₀ hb₀ e₁ hfree hEuler
  dsimp only at hrem
  have hrem' := hrem ha₁ q₁ hq₁ hgen₁ hconn₁
  unfold HasRemovedMarkedGraph at hrem'
  obtain ⟨eₐ, haₐ, hnₐ, hdata⟩ := hrem'
  obtain ⟨hgenₐ, hconnₐ, hfreeₐ, hEulerₐ, hcardₐ⟩ := hdata
  let vFold : foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀)) :=
    foldVertexMk (unfoldOld (allArrowSource e₀))
  have hcardU : Fintype.card (RemovedVertex vFold) < Fintype.card V := by
    have hunfold : Fintype.card (UnfoldVertex (allArrowSource e₀)) =
        Fintype.card V + 1 := unfoldVertex_card (allArrowSource e₀)
    have hfold : Fintype.card (foldVertex (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
          (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) <
        Fintype.card (UnfoldVertex (allArrowSource e₀)) := hcard₁
    have hremoved : Fintype.card (RemovedVertex vFold) <
        Fintype.card (foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
            (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) :=
      hcardₐ
    omega
  have holdb : unfoldOld (allArrowSource e₀) ≠
      unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
        (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀) := by
    rw [unfoldVertexAt_of_ne Mroot.labeling (show V from r.target)
      (unfoldEdgeColor Mroot.labeling e₀) hb₀]
    intro h
    cases h
  let Nfold : MarkedBinaryGraph (G := G) (H := H)
      (V := foldVertex (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt Mroot.labeling (allArrowSource e₀) e₀
          (show V from r.target) (unfoldEdgeColor Mroot.labeling e₀))) n :=
    foldedMarkedGraphSymm (unfoldedMarkedGraphNew Mroot e₀ ha₀)
      e₁ ha₁ q₁ hq₁
  have hbaseFold : Nfold.base ≠ vFold := by
    dsimp [Nfold, vFold]
    intro h
    apply unfoldNew_ne_old (allArrowSource e₀)
    exact foldVertexMk_eq_of_not_eq h
      (unfoldOld_ne_new (allArrowSource e₀)) holdb
  refine ⟨RemovedVertex vFold, removedVertexFintype vFold,
    removeQuiver eₐ hnₐ, removeHasReverse eₐ hnₐ,
    (fun x y => removeQuiverHomFintype eₐ hnₐ x y), ?_⟩
  refine ⟨removedMarkedGraph Nfold hbaseFold eₐ haₐ hnₐ
      (unfoldEdgeColor Mroot.labeling e₀)
      (by
        intro e he
        exact foldedUnfoldOld_incident_color Mroot e₀ ha₀ hb₀ e₁ e he),
    hcardU, hfreeₐ, hgenₐ, hconnₐ, hEulerₐ⟩

theorem hasReducedNullFold :
    HasReducedNullFold (G := G) (H := H) := by
  intro n W hFW qW hW hHomW M hfree hgen hconn hEuler hcard
  obtain ⟨v, hv, p, hp, hminimal⟩ :=
    MarkedBinaryGraph.exists_minimal_null_nonloop_path
      (M := M) hgen hconn hcard
  exact exists_reduced_graph_of_minimal_null_path
    (M := M) hfree hgen hconn hEuler hv p hp hminimal

theorem separated_generators_of_hasReducedNullFold
    (hred : HasReducedNullFold (G := G) (H := H)) :
    HasSeparatedReduction (G := G) (H := H) := by
  have hP : ∀ k : ℕ,
      ∀ (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
        [hV : HasInvolutiveReverse V]
        [hHom : ∀ a b : V, Fintype (@Quiver.Hom V qV a b)]
        (n : ℕ) (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
        Fintype.card V = k →
        ReverseFree (V := V) → M.IsGenerating → M.WeaklyConnected →
        Fintype.card (AllArrow (V := V)) ≤
          2 * (n + Fintype.card V - 1) →
        ∃ s : Fin n → Sum G H,
          Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro V hFV qV hV hHom n M hcard hfree hgen hconn hEuler
        by_cases hone : Fintype.card V = 1
        · exact exists_separated_generators_of_euler_bound M hfree hgen
            hone hEuler
        · have hpos : 0 < Fintype.card V := by
            exact Fintype.card_pos_iff.mpr ⟨M.base⟩
          have htwo : 1 < Fintype.card V := by omega
          obtain ⟨U, hFU, qU, hU, hHomU, hpack⟩ :=
            hred n V M hfree hgen hconn hEuler htwo
          obtain ⟨N, hcardN, hfreeN, hgenN, hconnN, hEulerN⟩ := hpack
          let : Fintype U := hFU
          let : Quiver.{0, 0} U := qU
          let : HasInvolutiveReverse U := hU
          let (a b : U) : Fintype (a ⟶ b) := hHomU a b
          have hcard' : Fintype.card U < k := by
            simpa [hcard] using hcardN
          exact ih (V := U) (Fintype.card U) hcard' n N rfl
            hfreeN hgenN hconnN hEulerN
  intro n x hx
  let V : Type := RoseVertex (fun i =>
    binaryReducedLetters (G := G) (H := H) (x i))
  let : Fintype V := by
    dsimp [V]
    infer_instance
  let : Quiver V := by
    dsimp [V]
    exact roseQuiver (fun i =>
      binaryReducedLetters (G := G) (H := H) (x i))
  let : HasInvolutiveReverse V := by
    dsimp [V]
    exact roseHasReverse (fun i =>
      binaryReducedLetters (G := G) (H := H) (x i))
  let (a b : V) : Fintype (a ⟶ b) := by
    dsimp [V]
    exact roseHomFintype _ _ _
  let M : MarkedBinaryGraph (G := G) (H := H) (V := V) n :=
    reducedTupleRose x
  have hMgen : M.IsGenerating := by
    dsimp [M]
    exact reducedTupleRose_isGenerating x hx
  have hMconn : M.WeaklyConnected := by
    dsimp [M]
    exact reducedTupleRose_weaklyConnected x
  have hMfree : ReverseFree (V := V) := by
    intro e
    dsimp [V] at e ⊢
    exact rose_allArrow_reverse_ne _ e
  have hMEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1) := by
    dsimp [V]
    exact roseAllArrow_card_le_euler
      (fun i => binaryReducedLetters (G := G) (H := H) (x i))
  exact hP (Fintype.card V) V n M rfl hMfree hMgen hMconn hMEuler

theorem rank_coprod_eq_add
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H :=
  rank_coprod_eq_add_of_separated_reduction
    (separated_generators_of_hasReducedNullFold
      (hasReducedNullFold (G := G) (H := H)))

end GeneralGrushko
end MarshallHall
