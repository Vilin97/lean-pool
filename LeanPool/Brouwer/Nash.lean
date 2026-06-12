/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import LeanPool.Brouwer.BrouwerProduct
import LeanPool.Brouwer.Simplex

/-!
# Existence of mixed Nash equilibria

This file defines finite games (`FinGame`), mixed strategy profiles, and the
mixed Nash equilibrium predicate (`FinGame.mixedNashEquilibrium`). The best-response
correspondence is turned into a continuous self-map of the product of strategy
simplices, and `ExistsNashEq` derives the existence of a mixed Nash equilibrium in
every finite game from Brouwer's fixed-point theorem on a product of simplices.
-/

attribute [local instance] Classical.propDecidable
open BigOperators
open Function

noncomputable section

/-
A game is a set of maps from strategy profiles to real payoffs.
-/
universe u

/-- A game: a finite-or-infinite set of players, each with a set of pure
strategies and a real-valued payoff function on the profiles of all players. -/
structure Game where
    /-- The set of players. -/
    I : Type u
    --deEqI : DecidableEq I := inferInstance -- Decidable Eq
    HI : Inhabited I     -- at least one player
    /-- For each player, the set of pure strategies. -/
    SS : I → Type u
    HSS (i :I) : Inhabited (SS i) -- The set of strategies is nonempty
    --deEqSS (i : I) : DecidableEq (SS i)
    /-- The payoff of each player as a function of the strategy profile. -/
    g : I → (Π i, SS i) →  ℝ
    -- an elements in Π i, SS is a move of all players.
    -- g i is the payoff of the i-th player

attribute [instance] Game.HI Game.HSS

namespace Game

variable {G : Game}

/-- A strategy profile is a Nash equilibrium if no player can improve unilaterally. -/
def NashEquilibrium (x : (Π i, G.SS i)) :=
  ∀ (i : G.I)
    (y : Π i, G.SS i),
    (∀ j : G.I, i ≠ j → (x j = y j) ) →
     G.g i x ≥ G.g i y

instance {G : Game} {i : G.I} : Inhabited (G.SS i) := G.HSS i

end Game

open Game

/-- A finite game: a game with finitely many players and finite strategy sets. -/
structure FinGame extends Game.{u} where
  FinI : Fintype I
  FinSS : ∀ i : I , Fintype (SS i)

attribute [instance] FinGame.FinI FinGame.FinSS


namespace FinGame
variable {G : FinGame}

instance {G : FinGame} : Fintype G.I := G.FinI
instance {G : FinGame} {i : G.I} : Fintype (G.SS i) := G.FinSS i
-- instance mixed_SS_i_Inhabited {G : FinGame} {i : G.I} :
--     Inhabited (MixedStrategy (G.SS i)) := inferInstance

variable (G) in
/-- A mixed strategy profile of a finite game: a simplex point per player. -/
abbrev mixedS := (i : G.I) → stdSimplex ℝ (G.SS i)

/-- The expected payoff of player `i` under a mixed strategy profile. -/
def mixedG (i : G.I) (m : Π i, MixedStrategy (G.SS i)) : ℝ :=
  ∑ s : (Π j, G.SS j) , (∏ j, m j (s j)) * (G.g i s)

lemma mixed_g_linear : G.mixedG i (update  x i y) = ∑ s : G.SS i,
    y s * G.mixedG i (update x i (stdSimplex.pure s)) := by
  unfold mixedG
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext f
  conv => rhs
          conv => rhs
                  ext t
                  rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  have h : ∏ j, (update x i y j) (f j) =
           (update x i y i) (f i) * ∏ j ∈ Finset.univ \ {i}, (update x i y j) (f j) := by
           rw [Function.update_self]
           rw [← Finset.prod_update_of_mem (Finset.mem_univ i)]
           apply Finset.prod_congr rfl
           intro j hj
           by_cases h1 : j = i
           · rw [h1, Function.update_self]
             simp
           · push Not at h1
             rw [Function.update_of_ne (show j ≠ i by exact h1)]
             set t := fun j =>(update x i y j) (f j)
             have h2 : t j = (x j) (f j) := by
              unfold t
              rw [Function.update_of_ne (show j ≠ i by exact h1)]
             rw [Function.update_of_ne (show j ≠ i by exact h1)]
             rw [h2]
  rw [h,Function.update_self]
  have h1 : y (f i) = ∑ j : G.SS i, y j * (stdSimplex.pure j) (f i) := by
    calc
    _ = ∑ j : G.SS i, if j = (f i) then y (f i) else 0 := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr (rfl)
      intro x hx
      by_cases hxx : x = f i
      · nth_rw 1 [<-mul_one (y (f i))]
        rw [stdSimplex.pure_eval_eq hxx]
        simp [hxx]
      · simp only [hxx, ↓reduceIte, zero_eq_mul]
        right
        push Not at hxx
        rw [stdSimplex.pure_eval_neq hxx]
  rw [h1, Finset.sum_mul]
  congr 1
  ext g
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_update_of_mem (Finset.mem_univ i)]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h2 : j = i
  · rw [h2,Function.update_self]
    simp
  · push Not at h2
    nth_rw 2 [Function.update_of_ne (show j ≠ i by exact h2)]
    set p := fun j =>(update x i y j) (f j)
    have h3 : p j = (x j) (f j) := by
      unfold p
      rw [Function.update_of_ne (show j ≠ i by exact h2)]
    rw [Function.update_of_ne (show j ≠ i by exact h2)]
    rw [h3]

/-- The mixed extension of a finite game, as a `Game` on simplices. -/
def FinGame2MixedGame (G : FinGame) : Game := {
  I := G.I
  HI := G.HI
  SS := fun i => MixedStrategy (G.SS i)
  HSS := inferInstance
  /-
  Let m be the mixed strategy, then m j (s j) is the probabilty
  of j-th player take the strategy (s j),
      the actural probability for taking the strategy s is the product probability
  -/
  g := mixedG
}

-- Let μ denote the mixed Game
/-- Notation `μ G` for the mixed extension of a finite game `G`. -/
notation:999 "μ" rhs:60 => (FinGame2MixedGame rhs)

variable (G : FinGame)

--theorem ExistsNashEq : ∃ m :  (i:(μ G).I )→ (μ G).SS i, (μ G).NashEquilibrium m := by sorry
/-
@[simp]
noncomputable def with_hole {G: FinGame} (s : G.mixedS) (i : G.I)
    (x : MixedStrategy (G.SS i))
    := Function.update G.I (fun i => MixedStrategy (G.SS i)) s i x

-- comma_notation for mixed game
noncomputable instance comma.mixed {G : FinGame} {i : G.I}
    : CoeOut
        ((MixedStrategy (G.SS i)) × (@IFun' G.I (fun i => MixedStrategy (G.SS i)) i))
        (IFun (fun i => MixedStrategy (G.SS i)))
    where
  coe := @combinePair G.I (fun i=> MixedStrategy (G.SS i)) i
-/



/-- A mixed strategy profile is a Nash equilibrium of the mixed game. -/
def mixedNashEquilibrium {G : FinGame} (x : G.mixedS) :=
  ∀ (i:G.I), ∀ (y : MixedStrategy (G.SS  i)),
     G.mixedG i x ≥ G.mixedG i (update  x i y)



end FinGame

section Brouwer.mixedGame
variable {G : FinGame}


variable {n : ℕ} (eI : G.I ≃ Fin n)

/-- Reindex a mixed strategy profile along an equivalence `G.I ≃ Fin n`. -/
def reindex : G.mixedS → ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) :=
    fun x k => x (eI.symm k)

/-- The inverse of `reindex`, transporting along the equivalence. -/
def reindexInv : ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) → G.mixedS :=
    fun z i => (eI.symm_apply_apply i) ▸ z (eI i)

lemma reindex_right_inv :
  ∀ y, reindex eI (reindexInv eI y) = y := by
    intro y; funext k
    rw [reindex,reindexInv]
    have h1 : eI (eI.symm k) = k := eI.apply_symm_apply _
    have h2 : eI.symm (eI (eI.symm k)) = eI.symm k := eI.symm_apply_apply _
    apply eq_of_heq
    rw [eqRec_heq_iff_heq]
    rw [h1]








lemma reindex_left_inv {n : ℕ} (eI : G.I ≃ Fin n) :
  let reindex : G.mixedS → ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) :=
    fun w k => w (eI.symm k)
  let reindexInv : ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) → G.mixedS :=
    fun z i => (eI.symm_apply_apply i) ▸ z (eI i)
  ∀ x, reindexInv (reindex x) = x := by
    intro reindex reindexInv x; funext i
    dsimp [reindex, reindexInv]
    have h1 : eI.symm (eI i) = i := eI.symm_apply_apply i
    have h2 : eI (eI.symm (eI i)) = eI i := eI.apply_symm_apply _
    apply eq_of_heq
    rw [eqRec_heq_iff_heq]
    rw [h1]

/-- Lifts an equivalence `e : n ≃ m` to a function between simplices. -/
def mapSimplex {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m) :
    stdSimplex ℝ n → stdSimplex ℝ m :=
  fun x => ⟨fun i => x.1 (e.symm i), by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro i; exact x.2.1 (e.symm i)
    · have h_sum : ∑ i : m, x.1 (e.symm i) = ∑ j : n, x.1 j := by
        rw [← Finset.sum_equiv e.symm]
        · intro _; simp
        · intro _; simp
      rw [h_sum, x.2.2]⟩

@[simp]
lemma map_simplex_apply {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m) (x : stdSimplex ℝ n)
    (i : m) :
    (mapSimplex e x).1 i = x.1 (e.symm i) := rfl

/-- The simplex map induced by an equivalence is itself an equivalence. -/
def mapSimplexEquiv {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m) :
    (stdSimplex ℝ n) ≃ (stdSimplex ℝ m) where
  toFun := mapSimplex e
  invFun := mapSimplex e.symm
  left_inv x := by
    ext i
    change x.1 (e.symm (e i)) = x.1 i
    rw [e.symm_apply_apply]
  right_inv x := by
    ext i
    change x.1 (e (e.symm i)) = x.1 i
    rw [e.apply_symm_apply]

/-- Lifts component-wise equivalences to an equivalence on the space of mixed strategies. -/
def mapMixedSEquiv {G : FinGame} (e : (i : G.I) → G.SS i ≃ Fin (Fintype.card (G.SS i))) :
    FinGame.mixedS G ≃ ((i : G.I) → stdSimplex ℝ (Fin (Fintype.card (G.SS i)))) where
  toFun x i := mapSimplex (e i) (x i)
  invFun x i := mapSimplex (e i).symm (x i)
  left_inv x := by
    funext i; ext j
    change (x i).1 ((e i).symm ((e i) j)) = (x i).1 j
    rw [(e i).symm_apply_apply]
  right_inv x := by
    funext i; ext j
    change (x i).1 ((e i) ((e i).symm j)) = (x i).1 j
    rw [(e i).apply_symm_apply]




variable {G : FinGame}



theorem Brouwer.mixedGame (f : G.mixedS → G.mixedS) (hf : Continuous f) : ∃ x : G.mixedS,
    f x = x := by
  classical
  let n : ℕ := Fintype.card G.I
  let eI : G.I ≃ Fin n := Fintype.equivFin (G.I)
  have n_pos : 0 < n := Fintype.card_pos_iff.mpr (by infer_instance)
  letI : Inhabited (Fin n) := ⟨⟨0, n_pos⟩⟩
  have card_pos (i : G.I) : 0 < Fintype.card (G.SS i) := by
    haveI : Inhabited (G.SS i) := inferInstance
    exact Fintype.card_pos_iff.mpr inferInstance
  let card' : Fin n → ℕ+ := fun k => ⟨Fintype.card (G.SS (eI.symm k)), card_pos (eI.symm k)⟩
  let reindex : G.mixedS → ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) :=
    fun x k => x (eI.symm k)
  let reindexInv : ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) → G.mixedS :=
    fun y i => (eI.symm_apply_apply i) ▸ y (eI i)
  have reindex_left : ∀ x, reindexInv (reindex x) = x := reindex_left_inv eI
  have reindex_right : ∀ y, reindex (reindexInv y) = y := reindex_right_inv eI
  let eS : (k : Fin n) → G.SS (eI.symm k) ≃ Fin (card' k) := fun k => Fintype.equivFin _
  let map_idx : ((k : Fin n) → stdSimplex ℝ (G.SS (eI.symm k))) → ((k : Fin n)
      → stdSimplex ℝ (Fin (card' k))) :=
    fun y k => mapSimplex (eS k) (y k)
  let map_idx_inv : ((k : Fin n) → stdSimplex ℝ (Fin (card' k))) → ((k : Fin n)
      → stdSimplex ℝ (G.SS (eI.symm k))) :=
    fun z k => mapSimplex (eS k).symm (z k)
  have map_idx_left : ∀ y, map_idx_inv (map_idx y) = y := by
    intro y; funext k; ext j
    change (y k).1 ((eS k).symm ((eS k) j)) = (y k).1 j
    rw [(eS k).symm_apply_apply]
  have map_idx_right : ∀ z, map_idx (map_idx_inv z) = z := by
    intro z; funext k; ext j
    change (z k).1 ((eS k) ((eS k).symm j)) = (z k).1 j
    rw [(eS k).apply_symm_apply]
  let φ : G.mixedS → ProductSimplices card' := fun x => map_idx (reindex x)
  let φ_inv : ProductSimplices card' → G.mixedS := fun w => reindexInv (map_idx_inv w)
  have φ_left : ∀ x, φ_inv (φ x) = x := by intro x; simp [φ, φ_inv, reindex_left, map_idx_left]
  have φ_right : ∀ w, φ (φ_inv w) = w := by intro w; simp [φ, φ_inv, reindex_right, map_idx_right]
  have hφ_cont : Continuous φ := by
    apply continuous_pi; intro k
    have : (fun x : G.mixedS => (φ x) k) = (mapSimplex (eS k))
        ∘ (fun x : G.mixedS => x (eI.symm k)) := rfl
    have h_map : Continuous (mapSimplex (eS k)) := by
      apply Continuous.subtype_mk
      apply continuous_pi; intro i
      exact (continuous_apply ((eS k).symm i)).comp continuous_subtype_val
    simpa [this, φ, reindex, map_idx] using h_map.comp (continuous_apply (eI.symm k))
  have hφinv_cont : Continuous φ_inv := by
    apply continuous_pi; intro i
    have saai := eI.symm_apply_apply i
    have typeeq : (G.SS i ≃ Fin ↑(card' (eI i))) = (G.SS (eI.symm (eI i)) ≃ Fin ↑(card' ((eI i))))
        :=
      by rw [saai]
    let eSi : G.SS i ≃ Fin (card' (eI i)) :=
      typeeq.symm ▸ (eS (eI i))
    have : (fun w : ProductSimplices card' => (φ_inv w) i)
       = (fun w : ProductSimplices card' => mapSimplex eSi.symm (w (eI i))) := by
      funext w
      simp only [φ_inv, reindexInv, map_idx_inv]
      have h1 : eI (eI.symm (eI i)) = eI i := eI.apply_symm_apply _
      have h2 : eI.symm (eI (eI.symm (eI i))) = eI.symm (eI i) := eI.symm_apply_apply _
      apply eq_of_heq
      rw [eqRec_heq_iff_heq]
      congr
      · symm
        exact @eqRec_heq (Type _) (fun X => X) _ _ typeeq.symm (eS (eI i))
    have h_map : Continuous (mapSimplex eSi.symm) := by
      apply Continuous.subtype_mk
      apply continuous_pi; intro j
      exact (continuous_apply (((eSi.symm).symm j))).comp continuous_subtype_val
    have h_eval : Continuous (fun w : ProductSimplices card' => w (eI i)) :=
      continuous_apply (eI i)
    have h_comp : Continuous
        (fun w : ProductSimplices card' => mapSimplex eSi.symm (w (eI i))) :=
      h_map.comp h_eval
    simpa [this] using h_comp
  let f' : ProductSimplices card' → ProductSimplices card' := φ ∘ f ∘ φ_inv
  have hf' : Continuous f' := hφ_cont.comp (hf.comp hφinv_cont)
  obtain ⟨w, hw⟩ := Brouwer_Product (card := card') f' hf'
  refine ⟨φ_inv w, ?_⟩
  calc
    f (φ_inv w)
        = φ_inv (φ (f (φ_inv w))) := by simp [φ_left]
    _   = φ_inv (f' w) := rfl
    _   = φ_inv w := by simp [hw]

end Brouwer.mixedGame

section mixedNashEquilibrium
variable (G : FinGame)
open FinGame

/-noncomputable def evaluate_at_mixed (i : G.I) (σ : G.mixedS) : ℝ :=
  ∑ pureS : (Π i, G.SS i), (∏ i : G.I, σ i (pureS i)) * G.g i pureS

lemma mixed_g_eq_evaluate (i : G.I) (σ : G.mixedS) : evaluate_at_mixed G i σ = mixedG i σ := by
  simp [evaluate_at_mixed, mixedG]

  sorry-/



variable {G}

/-- The best-response improvement map used to build the Nash fixed-point map. -/
noncomputable abbrev gFunction (i : G.I) (σ : G.mixedS) (a : G.SS i) : ℝ :=
  σ i a + max 0 (mixedG i (Function.update σ i (stdSimplex.pure a)) - mixedG i σ)


lemma sigma_le_g_function (i : G.I) (σ : G.mixedS) (a : G.SS i) : σ i a ≤ gFunction i σ a := by
  rw [gFunction]; norm_num

lemma g_function_noneg (i : G.I) (σ : G.mixedS) (a : G.SS i) : 0 ≤ gFunction i σ a := by
  have h1: 0 ≤ σ i a:= (σ i).2.1 a
  linarith [sigma_le_g_function i σ a]

--variable (sigma : G.mixedS ) (i : G.I) (a : G.SS i)

lemma one_le_sum_g (i : G.I) (σ : G.mixedS) : 1 ≤ ∑ b : G.SS i, gFunction i σ b := by
  calc
  _ = ∑ b : G.SS i, σ i b := Eq.symm (σ i).2.2
  _ ≤ _ := Finset.sum_le_sum (by norm_num [sigma_le_g_function i σ])


/-- The unnormalized best-response update on a product of strategy simplices. -/
noncomputable abbrev nashMapAux (σ : G.mixedS) (i : G.I) (a : G.SS i) : ℝ :=
  gFunction i σ a / ∑ b : G.SS i, gFunction i σ b

lemma nash_map_cert (σ : G.mixedS) (i : G.I) :
  (nashMapAux σ i) ∈ MixedStrategy (G.SS i) := by
  unfold nashMapAux
  constructor
  · intro x;
    apply div_nonneg <| g_function_noneg i σ x
    linarith [one_le_sum_g i σ]
  · rw [<-Finset.sum_div]
    apply div_self
    linarith [one_le_sum_g i σ]


variable (G)

/-- The continuous self-map of the strategy product whose fixed points are Nash equilibria. -/
noncomputable def nashMap (σ : G.mixedS) : G.mixedS :=
  fun (i : G.I) ↦ ⟨nashMapAux σ i, nash_map_cert σ i⟩

lemma cg : Continuous fun a => gFunction (G:=G) i a s := by
  unfold gFunction
  apply Continuous.add
  · let f : G.mixedS → stdSimplex ℝ (G.SS i) := fun σ => σ i
    let g : stdSimplex ℝ (G.SS i) → ℝ := fun a => a s
    have hfg: g ∘ f = fun σ => σ i s := by
      ext σ; rfl
    rw [<-hfg]
    apply Continuous.comp
    · have hgg : g =  (fun a => a s) ∘ (fun a => a.1)  := rfl
      rw [hgg]
      apply Continuous.comp
      · apply continuous_apply
      · continuity
    · continuity
  · apply Continuous.max
    · continuity
    · unfold mixedG
      apply Continuous.sub
      · apply continuous_finsetSum
        intro i' _
        apply Continuous.mul
        · apply continuous_finsetProd
          intro i'' _
          by_cases h : i'' = i
          · rw [h]
            continuity
          · simp only [ne_eq, h, not_false_eq_true, Function.update_of_ne]
            have : (fun (a : G.mixedS) => (a i'') (i' i'')) = (fun f => f (i' i''))
                ∘ Subtype.val ∘ fun a => a i'' := by
              rfl
            rw [this]
            apply Continuous.comp
            · continuity
            · apply Continuous.comp <;> continuity
        · continuity
      · apply continuous_finsetSum
        intro i' _
        apply Continuous.mul
        · apply continuous_finsetProd
          intro i'' _
          by_cases h : i'' = i
          · have : (fun (a : G.mixedS) => (a i) (i' i)) = (fun f => f (i' i))
              ∘ Subtype.val ∘ fun a => a i := by
              rfl
            rw [h]
            rw [this]
            apply Continuous.comp
            · continuity
            · apply Continuous.comp <;> continuity
          · have : (fun (a : G.mixedS) => (a i'') (i' i'')) = (fun f => f (i' i''))
              ∘ Subtype.val ∘ fun a => a i'' := by
              rfl
            rw [this]
            apply Continuous.comp
            · continuity
            · apply Continuous.comp <;> continuity
        · continuity


lemma nash_map_cont : Continuous <| nashMap G :=
  by
  unfold nashMap
  unfold nashMapAux
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro s
  apply Continuous.div
  · apply cg
  · apply continuous_finsetSum
    intro i _; apply cg
  · intro σ
    apply ne_of_gt
    nlinarith [show 1 ≤ ∑ b : G.SS i, gFunction i σ b by apply one_le_sum_g i σ]


theorem ExistsNashEq : ∃ σ : G.mixedS , mixedNashEquilibrium σ := by {
  obtain ⟨σ, hs⟩ := Brouwer.mixedGame (nashMap G)  (nash_map_cont G)
  use σ
  intro i y
  by_cases H : ∀ t, G.mixedG i σ  ≥ G.mixedG i (update σ i (stdSimplex.pure t))
  · have h1 : ∃ t : G.SS i, mixedG i (update σ i (stdSimplex.pure t)) ≥  mixedG i (update σ i y)
      := by
      have h1 : G.mixedG i (update  σ i y) = ∑ s : G.SS i,
          y s * G.mixedG i (update σ i (stdSimplex.pure s)) := by apply mixed_g_linear
      rw [h1]
      obtain ⟨t,ht⟩ := Finite.exists_max (fun s => G.mixedG i (update σ i (stdSimplex.pure s)))
      use t
      simp only [ge_iff_le]
      have : ∑ s : G.SS i, y s * G.mixedG i (update σ i (stdSimplex.pure s))
             ≤ ∑ s : G.SS i, y s * G.mixedG i (update σ i (stdSimplex.pure t)) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left (ht s)
        have : 0 ≤ y s := (y).2.1 s
        exact this
      have h2 : ∑ s : G.SS i, y s  = 1 := by
        exact (y).2.2
      rw [← Finset.sum_mul, h2] at this
      simp only [one_mul] at this
      exact this
    obtain ⟨t, ht⟩ := h1
    specialize H t
    nlinarith
  · exfalso -- This case cannot happen
    push Not at H
    obtain ⟨t,ht⟩ := H
    have H1 :  1 < ∑ b, gFunction i σ b := by
      have h1 : 1 ≤ ∑ b : G.SS i, gFunction i σ b := by
        apply one_le_sum_g i σ
      have h2 : 1 ≠ ∑ b : G.SS i, gFunction i σ b := by
        intro h2
        replace h2 : ∑ b : G.SS i, σ i b  = ∑ b : G.SS i,   gFunction  i σ b := by
          have h3 : 1 = ∑ b : G.SS i, σ i b := Eq.symm (σ i).2.2
          rw [h3] at h2
          exact h2
        unfold gFunction at h2
        replace h2 : ∑ s : G.SS i, max 0 (mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ)
            = 0 := by
          rw [Finset.sum_add_distrib] at h2
          linarith
        replace h2 : mixedG i (update σ i (stdSimplex.pure t)) - mixedG i σ ≤ 0 := by
          by_cases h :  ∀ s : G.SS i, mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ ≤ 0
          · specialize h t
            simp only [tsub_le_iff_right, zero_add] at h
            simp only [tsub_le_iff_right, zero_add]
            exact h
          · exfalso
            simp only [tsub_le_iff_right, zero_add, not_forall, not_le] at h
            obtain ⟨s, hs⟩:= h
            have h3 : max 0 (mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ)
                = mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ := by simp; nlinarith
            have h4: ∀ s : G.SS i , 0 ≤ max 0 (mixedG i (update σ i (stdSimplex.pure s))
                - mixedG i σ) := by
                intro s
                simp
            have h5 : ∑ s : G.SS i, max 0 (mixedG i (update σ i (stdSimplex.pure s))
                - mixedG i σ) > 0 := by
              have f : mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ ≤ ∑ s : G.SS i,
                  max 0 (mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ) := by
                rw [← h3]
                set g :G.SS i → ℝ := fun s => max 0 (mixedG i (update σ i (stdSimplex.pure s))
                    - mixedG i σ)
                have h6 : g s = max 0 (mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ)
                    := by rfl
                rw [←h6]
                apply Finset.single_le_sum
                · have h4 : ∀ s : G.SS i, 0 ≤ g s := by
                    simp [g]
                  intro s _
                  apply h4
                · simp
              nlinarith
            nlinarith
        nlinarith
      rw [lt_iff_le_and_ne]
      exact ⟨h1, h2⟩
    have H2 : ∑ s, σ i s * G.mixedG i (update σ i (stdSimplex.pure s)) =
      G.mixedG i σ := by
      rw [← mixed_g_linear]
      simp
      -- have H2: G.mixedG i (update σ i (σ i)) = G.mixedG i σ  := by sorry\
    obtain ⟨s,hs1,hs2⟩:= stdSimplex.wsum_magic_ineq H2
    have : σ i s = σ i s / (∑ b : G.SS i, gFunction i σ b) := by
      nth_rw 1 [<-hs]
      calc
      _ = nashMapAux σ i s := by rw [nashMap];rfl
      _ = _ := by
        rw [nashMapAux,gFunction]
        have : max 0 (mixedG i (update σ i (stdSimplex.pure s)) - mixedG i σ)  = 0 := by
          simp only [sup_eq_left, tsub_le_iff_right, zero_add]
          apply hs2
        rw [this];norm_num
    have self_div_lemma {x y : ℝ} : x ≠ 0 → x = x/y →  y = 1 := by
      intro h1 h2
      have hy : y ≠ 0 := by
        rintro rfl
        simp only [div_zero] at h2
        exact h1 h2
      have hxy : x * y = x := by
        rw [eq_div_iff hy] at h2
        linarith
      have : x * y = x * 1 := by rw [hxy, mul_one]
      exact mul_left_cancel₀ h1 this
    have := self_div_lemma (by linarith) this
    linarith
}

end mixedNashEquilibrium
