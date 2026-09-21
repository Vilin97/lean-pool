/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixChainConclusion
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeContraction

/-! # Bridge Chain Transport -/

open Utilities

universe u

namespace Utilities.MarkedGraph

def bridge (M N : MarkedGraph.{u}) : MarkedGraph.{u} where
  graph := bridgeGraph M.graph N.graph M.right N.left
  left := Sum.inl M.left
  right := Sum.inr N.right

def bridgeChain (M : MarkedGraph.{u}) : List MarkedGraph.{u} → MarkedGraph.{u}
  | [] => M
  | N :: rest => bridgeChain (M.bridge N) rest

end Utilities.MarkedGraph

namespace Bananas
noncomputable def bridgeWedgeAssocIso (M N K : MarkedGraph.{u}) :
    CFGraphIso ((M.bridge N).wedge K).graph (M.bridge (N.wedge K)).graph := by
  change CFGraphIso
    (vertexWedge (bridgeGraph M.graph N.graph M.right N.left) K.graph
      (Sum.inr N.right) K.left)
    (bridgeGraph M.graph (vertexWedge N.graph K.graph N.right K.left)
      M.right (Sum.inl N.left))
  exact
    { vertexEquiv :=
        { toFun := fun z => match z with
            | Sum.inl (Sum.inl a) => Sum.inl a
            | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
            | Sum.inr c => Sum.inr (Sum.inr c)
          invFun := fun z => match z with
            | Sum.inl a => Sum.inl (Sum.inl a)
            | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
            | Sum.inr (Sum.inr c) => Sum.inr c
          left_inv := by rintro ((a | b) | c) <;> rfl
          right_inv := by rintro (a | (b | c)) <;> rfl }
      map_num_edges := by
        rintro ((a | a) | a) ((b | b) | b)
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inl a) (Sum.inl b) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b))
          simp
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inl a) (Sum.inr (Sum.inl b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inr b))
          simp only [num_edges_bridgeGraph_inl_inr,
            num_edges_vertexWedge_left]
          congr 1
          apply propext
          constructor
          · rintro ⟨ha, hb⟩
            exact ⟨ha, Sum.inl.inj hb⟩
          · rintro ⟨ha, hb⟩
            exact ⟨ha, congrArg Sum.inl hb⟩
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inl a) (Sum.inr (Sum.inr b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inl a)) (Sum.inr b)
          simp
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inl a)) (Sum.inl b) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl b))
          calc
            _ = num_edges (bridgeGraph M.graph
                  (vertexWedge N.graph K.graph N.right K.left) M.right
                    (Sum.inl N.left))
                  (Sum.inl b) (Sum.inr (Sum.inl a)) :=
                num_edges_symmetric _ _ _
            _ = (if b = M.right ∧ a = N.left then 1 else 0) := by
              rw [num_edges_bridgeGraph_inl_inr]
              congr 1
              apply propext
              constructor
              · rintro ⟨hb, ha⟩
                exact ⟨hb, Sum.inl.inj ha⟩
              · rintro ⟨hb, ha⟩
                exact ⟨hb, congrArg Sum.inl ha⟩
            _ = num_edges (bridgeGraph M.graph N.graph M.right N.left)
                  (Sum.inl b) (Sum.inr a) := by
              rw [num_edges_bridgeGraph_inl_inr]
            _ = num_edges (bridgeGraph M.graph N.graph M.right N.left)
                  (Sum.inr a) (Sum.inl b) := num_edges_symmetric _ _ _
            _ = _ := (num_edges_vertexWedge_left _ _ _ _ _ _).symm
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b))
          simp
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inl (Sum.inr a)) (Sum.inr b)
          simp only [num_edges_bridgeGraph_inr,
            num_edges_vertexWedge_left_right]
          by_cases h : a = N.right
          · subst a
            simp
          · rw [if_neg h, if_neg (fun he => h (Sum.inr.inj he))]
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inr a)) (Sum.inl b) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inr a) (Sum.inl (Sum.inl b))
          rw [num_edges_symmetric]
          simp
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inr a) (Sum.inl (Sum.inr b))
          simp only [num_edges_bridgeGraph_inr, num_edges_symmetric,
            num_edges_vertexWedge_left_right]
          by_cases h : b = N.right
          · subst b
            simp
          · rw [if_neg h, if_neg (fun he => h (Sum.inr.inj he))]
        · change num_edges (bridgeGraph M.graph
              (vertexWedge N.graph K.graph N.right K.left) M.right
                (Sum.inl N.left))
              (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) =
            num_edges (vertexWedge
              (bridgeGraph M.graph N.graph M.right N.left) K.graph
                (Sum.inr N.right) K.left)
              (Sum.inr a) (Sum.inr b)
          simp }

@[simp] theorem bridgeWedgeAssocIso_apply_left (M N K : MarkedGraph.{u}) :
    (bridgeWedgeAssocIso M N K).vertexEquiv ((M.bridge N).wedge K).left =
      (M.bridge (N.wedge K)).left := rfl

@[simp] theorem bridgeWedgeAssocIso_apply_right (M N K : MarkedGraph.{u}) :
    (bridgeWedgeAssocIso M N K).vertexEquiv ((M.bridge N).wedge K).right =
      (M.bridge (N.wedge K)).right := by
  change (bridgeWedgeAssocIso M N K).vertexEquiv
    (wedgeRightVertex (bridgeGraph M.graph N.graph M.right N.left) K.graph
      (Sum.inr N.right) K.left K.right) =
    Sum.inr (wedgeRightVertex N.graph K.graph N.right K.left K.right)
  unfold bridgeWedgeAssocIso
  by_cases h : K.right = K.left
  · simp only [wedgeRightVertex, dif_pos h]
    change Sum.inr (Sum.inl N.right) = Sum.inr (Sum.inl N.right)
    rfl
  · simp only [wedgeRightVertex, dif_neg h]
    change Sum.inr (Sum.inr
        (⟨K.right, h⟩ : {b : K.graph.V // b ≠ K.left})) =
      Sum.inr (Sum.inr
        (⟨K.right, h⟩ : {b : K.graph.V // b ≠ K.left}))
    rfl

/-! ## Rank-preserving transport with a distinguished left mark -/

/-- A graph isomorphism which also carries the displayed left mark. -/
structure LeftMarkedIso (M N : MarkedGraph.{u}) where
  iso : CFGraphIso M.graph N.graph
  map_left : iso.vertexEquiv M.left = N.left

namespace LeftMarkedIso

noncomputable def refl (M : MarkedGraph.{u}) : LeftMarkedIso M M where
  iso := CFGraphIso.refl M.graph
  map_left := rfl

noncomputable def symm {M N : MarkedGraph.{u}}
    (phi : LeftMarkedIso M N) : LeftMarkedIso N M where
  iso := phi.iso.symm
  map_left := by
    exact (phi.iso.vertexEquiv.symm_apply_eq).2 phi.map_left.symm

noncomputable def trans {M N K : MarkedGraph.{u}}
    (phi : LeftMarkedIso M N) (psi : LeftMarkedIso N K) :
    LeftMarkedIso M K where
  iso := phi.iso.trans psi.iso
  map_left := by simp [CFGraphIso.trans, phi.map_left, psi.map_left]

end LeftMarkedIso

/-- The fully right-associated vertex-wedge chain. -/
def rightChain (M : MarkedGraph.{u}) : List MarkedGraph.{u} → MarkedGraph.{u}
  | [] => M
  | N :: rest => M.wedge (rightChain N rest)

/-- Reassociate the library's left-associated chain all the way to the
right, retaining its outside left mark. -/
noncomputable def rightChainIso (M : MarkedGraph.{u}) :
    (rest : List MarkedGraph.{u}) → LeftMarkedIso (M.chain rest) (rightChain M rest)
  | [] => LeftMarkedIso.refl M
  | N :: rest => by
      let outer : LeftMarkedIso (M.chain (N :: rest))
          (M.wedge (N.chain rest)) :=
        { iso := markedChainReassocIso M N rest
          map_left := markedChainReassocIso_apply_left M N rest }
      let inner := rightChainIso N rest
      let congrIso := vertexWedgeCongrRight inner.iso M.right
        (N.chain rest).left (rightChain N rest).left inner.map_left
      let congr : LeftMarkedIso (M.wedge (N.chain rest))
          (M.wedge (rightChain N rest)) :=
        { iso := congrIso
          map_left := vertexWedgeCongrRight_apply_left inner.iso M.right
            (N.chain rest).left (rightChain N rest).left inner.map_left M.left }
      exact outer.trans congr

/-- The bridge/wedge reassociation as an isomorphism preserving the outside
left mark. -/
noncomputable def bridgeWedgeAssocLeftIso (M N K : MarkedGraph.{u}) :
    LeftMarkedIso ((M.bridge N).wedge K) (M.bridge (N.wedge K)) where
  iso := bridgeWedgeAssocIso M N K
  map_left := bridgeWedgeAssocIso_apply_left M N K

/-- A divisor map preserving degree, rank, genus, and the distinguished
one-chip divisor.  This is exactly the interface needed to transport both
ordinary and once-marked Brill--Noether statements. -/
structure LeftRankTransport (M N : MarkedGraph.{u}) where
  mapDiv : CFDiv M.graph → CFDiv N.graph
  map_sub : ∀ D E, mapDiv (D - E) = mapDiv D - mapDiv E
  map_zsmul : ∀ (n : ℤ) D, mapDiv (n • D) = n • mapDiv D
  map_one_chip : mapDiv (one_chip M.left) = one_chip N.left
  deg_map : ∀ D, deg (mapDiv D) = deg D
  rank_map : ∀ D, rank N.graph (mapDiv D) = rank M.graph D
  genus_eq : genus N.graph = genus M.graph

namespace LeftRankTransport

noncomputable def ofIso {M N : MarkedGraph.{u}} (phi : LeftMarkedIso M N) :
    LeftRankTransport M N where
  mapDiv := phi.iso.mapDiv
  map_sub := by intro D E; funext z; rfl
  map_zsmul := by intro n D; funext z; rfl
  map_one_chip := by
    rw [phi.iso.mapDiv_one_chip, phi.map_left]
  deg_map := phi.iso.deg_mapDiv
  rank_map := phi.iso.rank_mapDiv
  genus_eq := phi.iso.genus_eq

noncomputable def trans {M N K : MarkedGraph.{u}}
    (first : LeftRankTransport M N) (second : LeftRankTransport N K) :
    LeftRankTransport M K where
  mapDiv := fun D => second.mapDiv (first.mapDiv D)
  map_sub := by intro D E; rw [first.map_sub, second.map_sub]
  map_zsmul := by intro n D; rw [first.map_zsmul, second.map_zsmul]
  map_one_chip := by rw [first.map_one_chip, second.map_one_chip]
  deg_map := by intro D; rw [second.deg_map, first.deg_map]
  rank_map := by intro D; rw [second.rank_map, first.rank_map]
  genus_eq := second.genus_eq.trans first.genus_eq

end LeftRankTransport
private theorem bridgePushforward_one_chip_left (M N : MarkedGraph.{u}) :
    bridgePushforward M.graph N.graph M.right N.left
        (one_chip (Sum.inl M.left)) =
      one_chip (Sum.inl M.left : (M.wedge N).graph.V) := by
  have hSource :
      (one_chip (Sum.inl M.left) : CFDiv (M.bridge N).graph) =
        MarkedGraphs.liftLeftDivisor M.graph N.graph M.right N.left
          (one_chip M.left) := by
    funext z
    rcases z with a | b
    · simp only [MarkedGraphs.liftLeftDivisor_inl, one_chip]
      by_cases h : a = M.left
      · subst a
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun e => h (Sum.inl.inj e)), if_neg h]
    · simp [one_chip]
  rw [hSource, bridgePushforward_liftLeftDivisor]
  funext z
  rcases z with a | b
  · simp only [wedgeLiftLeftDivisor_left, one_chip]
    by_cases h : a = M.left
    · subst a
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun e => h (Sum.inl.inj e))]
  · simp [one_chip]

/-- Contract the bridge between two marked factors. -/
noncomputable def contractBridgeTransport (M N : MarkedGraph.{u}) :
    LeftRankTransport (M.bridge N) (M.wedge N) where
  mapDiv := bridgePushforward M.graph N.graph M.right N.left
  map_sub := by intro D E; exact map_sub _ D E
  map_zsmul := by intro n D; exact AddMonoidHom.map_zsmul _ n D
  map_one_chip := bridgePushforward_one_chip_left M N
  deg_map := deg_bridgePushforward M.graph N.graph M.right N.left
  rank_map := rank_bridgePushforward M.graph N.graph M.right N.left
  genus_eq := by
    change genus (vertexWedge M.graph N.graph M.right N.left) =
      genus (bridgeGraph M.graph N.graph M.right N.left)
    rw [genus_vertexWedge, genus_bridgeGraph]

/-- Move the initial bridge of a wedge-chain to the outside and contract it. -/
noncomputable def contractInitialBridge (M N : MarkedGraph.{u})
    (rest : List MarkedGraph.{u}) :
    LeftRankTransport ((M.bridge N).chain rest) ((M.wedge N).chain rest) := by
  let exposeSource := rightChainIso (M.bridge N) rest
  let exposeBridge : LeftMarkedIso (rightChain (M.bridge N) rest)
      (M.bridge (rightChain N rest)) := by
    cases rest with
    | nil => exact LeftMarkedIso.refl (M.bridge N)
    | cons K tail => exact bridgeWedgeAssocLeftIso M N (rightChain K tail)
  let contract := contractBridgeTransport M (rightChain N rest)
  let exposeTarget := (rightChainIso M (N :: rest)).symm
  exact ((LeftRankTransport.ofIso exposeSource).trans
    (LeftRankTransport.ofIso exposeBridge)).trans
      (contract.trans (LeftRankTransport.ofIso exposeTarget))

/-- Contract every separating edge in the displayed bridge chain. -/
noncomputable def contractBridgeChain (M : MarkedGraph.{u}) :
    (rest : List MarkedGraph.{u}) → LeftRankTransport (M.bridgeChain rest) (M.chain rest)
  | [] => LeftRankTransport.ofIso (LeftMarkedIso.refl M)
  | N :: rest =>
      (contractBridgeChain (M.bridge N) rest).trans
        (contractInitialBridge M N rest)

end Bananas
