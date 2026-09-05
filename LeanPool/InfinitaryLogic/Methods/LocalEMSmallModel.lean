/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.SchemaLocalEMSource
import LeanPool.InfinitaryLogic.Methods.LocalEMSmall
import LeanPool.InfinitaryLogic.Methods.LocalEMCardinality
import LeanPool.InfinitaryLogic.Methods.HighlyTransitiveExistence
import LeanPool.InfinitaryLogic.ModelTheory.Hanf
/-!
# Small models of every infinite size: the countable-symbol core (issue #11 unit 7a)

**Marker, Theorem 11.2, countable-symbol core**: if `φ` has arbitrarily large models then for
every infinite `κ` it has a model of size EXACTLY `κ` realizing only countably many complete
`L_{ω₁ω}`-types (`exists_small_model_of_hasArbLargeModels_countable_symbols`).

The assembly keeps the identity of the local EM carrier throughout (it does NOT route through
the existential `tailTemplateRealizable_of_localEMContext_cross`, which forgets it): a source
model of size `≥ ℶ_{ω₁}` feeds the schema term source (`SchemaLocalEMSource.lean`, the
mixin-satisfying intermediate that itself realizes `φ` and carries the pairwise-distinct
`schemaSeq`); over the highly order-transitive skeleton `J` of size `κ`
(`HighlyTransitiveExistence.lean`) the schema context's carrier then has: satisfaction of `φ`
(the stage-0 bridge `realizes_stage0_sentence_of_skolemUniversal`), size exactly
`max ℵ₀ κ = κ` (`mk_carrier_eq`, injectivity from `schemaSeq_pairwise_ne`), and countably many
realized types (`lomega1omegaSmall` on the `localColim` reduct, descended to the seed language
by `Lomega1omegaSmall.of_expansion`).
-/

namespace FirstOrder.Language

open Cardinal

/-- **The countable-symbol small-model theorem** (Marker, Theorem 11.2 core): a sentence with
arbitrarily large models has, at every infinite `κ`, a model of size exactly `κ` realizing only
countably many complete `L_{ω₁ω}`-types. -/
theorem exists_small_model_of_hasArbLargeModels_countable_symbols {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)]
    {φ : L'.Sentenceω} (hφarb : HasArbLargeModels φ) {κ : Cardinal.{0}}
    (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ (N : Type) (_ : L'.Structure N),
      Sentenceω.Realize φ N ∧ Cardinal.mk N = κ ∧ Lomega1omegaSmall (L := L') N := by
  classical
  -- the large source model
  obtain ⟨M, instM, hφM, hMsize⟩ := hφarb (Cardinal.beth (Ordinal.omega 1))
  -- the highly order-transitive skeleton of size κ
  set W := highlyTransitiveOrderAt κ hκ with hW
  set J := W.Carrier with hJ
  let : LinearOrder J := W.linearOrder
  have : Infinite J := by
    rw [Cardinal.infinite_iff, W.card_eq]
    exact hκ
  -- the schema term source over the Morley seed
  obtain ⟨instLO, instWF⟩ := exists_wellFoundedLT M
  let : LinearOrder M := instLO
  have : WellFoundedLT M := instWF
  have : Nonempty M := Cardinal.mk_ne_zero_iff.mp
    (((lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.aleph0_le_beth _)).trans_le hMsize).ne')
  have hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M := hMsize
  set s₀ := LocalStage.ofSeq L' (morleySeed φ) with hs₀
  let : (localColim s₀).Structure M := localColimStructure s₀
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  let : L'.Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (LlocalInclusion s₀ 0).reduct _
  -- the schema context over J, with carrier identity kept
  set ctx := schemaTermLocalEMContext (s₀ := s₀) (M := M) hM J with hctx
  have hmem : (⟨0, φ⟩ : Σ n, (Llocal s₀ 0).BoundedFormulaω Empty n) ∈ Γlocal s₀ 0 := ⟨0, rfl⟩
  have hφsrc : Sentenceω.Realize φ (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTerm_realizes_stage0_sentence (s₀ := s₀) (M := M) hM φ hmem hφM
  have hinj : Function.Injective ctx.a := by
    intro i j hij
    by_contra hne
    exact schemaSeq_pairwise_ne (s₀ := s₀) (M := M) hM hne hij
  have : Countable (Σ l, (localColim s₀).Functions l) := localColim_fun_countable s₀
  -- the carrier, its structures, and the three conclusions
  let : (localColim s₀)[[J]].Structure ctx.Carrier := ctx.structure
  let : (Llocal s₀ 0)[[J]].Structure ctx.Carrier :=
    ((LlocalInclusion s₀ 0).addConstants J).reduct ctx.Carrier
  let instColim : (localColim s₀).Structure ctx.Carrier := ctx.structureBase
  let instL' : (Llocal s₀ 0).Structure ctx.Carrier :=
    ((Llocal s₀ 0).lhomWithConstants J).reduct ctx.Carrier
  have hexp : (LlocalInclusion s₀ 0).IsExpansionOn ctx.Carrier := by
    constructor
    · intro n f x
      rfl
    · intro n R x
      rfl
  refine ⟨ctx.Carrier, instL', ?_, ?_, ?_⟩
  · -- satisfaction: the stage-0 bridge
    exact LocalEMContext.realizes_stage0_sentence_of_skolemUniversal s₀ J
      (schemaTerm_localSkolemUniversalForColim hM) ctx subset_rfl
      (schemaTermLocalEMContext_omegaCompleteForColim (s₀ := s₀) (M := M) hM J)
      φ hmem hφsrc
  · -- size exactly κ
    rw [ctx.mk_carrier_eq hinj, W.card_eq]
    exact max_eq_right hκ
  · -- smallness: on the localColim reduct, then descended to L'
    exact Lomega1omegaSmall.of_expansion (LlocalInclusion s₀ 0)
      (ctx.lomega1omegaSmall W.highlyTransitive)

end FirstOrder.Language
