/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemmaClose
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitAdjoint
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29State

/-!
# The unit step of the dévissage

When every symmetric power of the remainder survives, the Key
Lemma splits a unit factor off it: the splitting algebra becomes
the new base, the complement becomes the new remainder, and the
mixed free part gains one unit summand.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The unit step of the dévissage**: when every symmetric
power of the remainder survives, the Key Lemma splits a unit
factor off it. -/
theorem devissageStepA
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (X : Ind C) :
    DevissageStepA (Ind C) L X := by
  intro st hSym
  letI := st.monObj
  letI := st.comm
  obtain ⟨sd⟩ := keyLemmaData_ind st.base st.rest st.restDual
    st.datum st.zigzag st.unit_ne_zero hSym
  letI := sd.monObj
  letI := sd.comm
  letI := sd.ofBase_monHom
  obtain ⟨e⟩ := st.decomp
  refine ⟨{ base := sd.carrier
            monObj := sd.monObj
            comm := sd.comm
            unit_ne_zero := sd.unit_ne_zero
            units := st.units + 1
            lines := st.lines
            rest := splitComplMod st.base sd.carrier sd.ofBase
              sd.ins sd.ins' st.datum sd.ins_linear
              sd.ins'_linear
            restDual := splitComplModDual st.base sd.carrier
              sd.ofBase sd.ins sd.ins' st.datum sd.ins_linear
              sd.ins'_linear
            datum := (baseChangeDatum st.base sd.carrier
              sd.ofBase st.datum).transfer sd.carrier
              (splitComplIncl st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear)
              (splitComplInclDual st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear)
              (splitComplProjMod st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear sd.pairMul sd.pairMul_def
                sd.delta_eq)
              (splitComplProjModDual st.base sd.carrier
                sd.ofBase sd.ins sd.ins' st.datum
                sd.ins_linear sd.ins'_linear sd.pairMul
                sd.pairMul_def sd.delta_eq)
            zigzag := modZigzagDatum_transfer sd.carrier
              (baseChangeDatum st.base sd.carrier sd.ofBase
                st.datum)
              (splitComplIncl st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear)
              (splitComplInclDual st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear)
              (splitComplProjMod st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear sd.pairMul sd.pairMul_def
                sd.delta_eq)
              (splitComplProjModDual st.base sd.carrier
                sd.ofBase sd.ins sd.ins' st.datum
                sd.ins_linear sd.ins'_linear sd.pairMul
                sd.pairMul_def sd.delta_eq)
              (baseChangeZigzag (Ind C) st.base _ _ st.rest
                st.restDual st.datum st.zigzag sd.carrier _ _
                sd.ofBase _)
              (splitComplIncl_proj st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear sd.pairMul sd.pairMul_def
                sd.delta_eq)
              (splitComplInclDual_proj st.base sd.carrier
                sd.ofBase sd.ins sd.ins' st.datum
                sd.ins_linear sd.ins'_linear sd.pairMul
                sd.pairMul_def sd.delta_eq)
              (splitComplMap_adj st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum st.zigzag
                sd.ins_linear sd.ins'_linear sd.pairMul
                sd.pairMul_def sd.delta_eq)
            decomp := ⟨transportDecomp st.base sd.carrier
              sd.ofBase L st.units st.lines e
              (splitDecompMod st.base sd.carrier sd.ofBase
                sd.ins sd.ins' st.datum sd.ins_linear
                sd.ins'_linear sd.pairMul sd.pairMul_def
                sd.delta_eq)⟩ }, rfl, rfl⟩

end RS
