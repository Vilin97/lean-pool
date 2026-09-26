/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.ProtectedChain


/-!
# Reindexing coherent protected chains
-/

@[expose] public section

namespace ScottishBook155

universe u

namespace ProtectedChain

variable {ι : Type u} {κ : Type u} [LinearOrder ι] [LinearOrder κ]
variable {r L : ℝ}

/-- The canonical inclusion of an ordered type into the same type with a new
top element. -/
noncomputable def withTopCoeOrderEmbedding {ι : Type u} [LinearOrder ι] :
    ι ↪o WithTop ι where
  toFun := fun i => i
  inj' := WithTop.coe_injective
  map_rel_iff' := by intro i j; simp

/-- Pull a protected chain back along an order embedding. -/
noncomputable def reindex (C : ProtectedChain (ι := ι) r L)
    (e : κ ↪o ι) : ProtectedChain (ι := κ) r L where
  stage k := C.stage (e k)
  sourceSystem := {
    embed := fun i j hij => C.sourceSystem.embed (e i) (e j) (e.monotone hij)
    project := fun i j hij => C.sourceSystem.project (e i) (e j) (e.monotone hij)
    embed_refl := fun i => C.sourceSystem.embed_refl (e i)
    embed_trans := fun i j k hij hjk =>
      C.sourceSystem.embed_trans (e i) (e j) (e k)
        (e.monotone hij) (e.monotone hjk)
    project_embed := fun a i j hai hij =>
      C.sourceSystem.project_embed (e a) (e i) (e j)
        (e.monotone hai) (e.monotone hij)
    project_retracts := fun i j hij =>
      C.sourceSystem.project_retracts (e i) (e j) (e.monotone hij)
    project_contractive := fun i j hij =>
      C.sourceSystem.project_contractive (e i) (e j) (e.monotone hij) }
  targetSystem := {
    embed := fun i j hij => C.targetSystem.embed (e i) (e j) (e.monotone hij)
    project := fun i j hij => C.targetSystem.project (e i) (e j) (e.monotone hij)
    embed_refl := fun i => C.targetSystem.embed_refl (e i)
    embed_trans := fun i j k hij hjk =>
      C.targetSystem.embed_trans (e i) (e j) (e k)
        (e.monotone hij) (e.monotone hjk)
    project_embed := fun a i j hai hij =>
      C.targetSystem.project_embed (e a) (e i) (e j)
        (e.monotone hai) (e.monotone hij)
    project_retracts := fun i j hij =>
      C.targetSystem.project_retracts (e i) (e j) (e.monotone hij)
    project_contractive := fun i j hij =>
      C.targetSystem.project_contractive (e i) (e j) (e.monotone hij) }
  compatible := fun i j hij => C.compatible (e i) (e j) (e.monotone hij)
  recovers := fun i j hij => C.recovers (e i) (e j) (e.monotone hij)

/-- Two successive reindexings are the reindexing by the composite order
embedding. -/
theorem reindex_comp {μ : Type u} [LinearOrder μ]
    (C : ProtectedChain (ι := ι) r L) (e : κ ↪o ι) (f : μ ↪o κ) :
    (C.reindex e).reindex f = C.reindex (f.trans e) := by
  rfl

/-- Reindexing depends only on the pointwise action of the order embedding. -/
theorem reindex_congr (C : ProtectedChain (ι := ι) r L) (e f : κ ↪o ι)
    (h : ∀ k, e k = f k) : C.reindex e = C.reindex f := by
  have hef : e = f := DFunLike.ext _ _ h
  subst f
  rfl

/-- Restrict a chain to the closed initial segment ending at `j`. -/
noncomputable def restrictionLE (C : ProtectedChain (ι := ι) r L) (j : ι) :
    ProtectedChain (ι := Set.Iic j) r L :=
  C.reindex (OrderEmbedding.subtype _)

/-- Restrict a chain to the open initial segment below `j`. -/
noncomputable def restrictionLT (C : ProtectedChain (ι := ι) r L) (j : ι) :
    ProtectedChain (ι := Set.Iio j) r L :=
  C.reindex (OrderEmbedding.subtype _)

end ProtectedChain

end ScottishBook155
