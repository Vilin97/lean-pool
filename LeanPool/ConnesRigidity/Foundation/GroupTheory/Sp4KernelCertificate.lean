/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Kernel-checked finite certificate for the Sp₄(F₂) normal-subgroup argument in
Zhou §6. The exhaustive Boolean matrix search is isolated here from the
conceptual action and transvection lemmas.
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard0
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard1
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard2
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard3
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard4
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard5
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard6
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificateShard7

/-!
# Kernel-checked `Sp₄(𝔽₂)` normal-subgroup certificate

The 65,536 Boolean matrices are checked in independent shards so Lake can
compile the certificate in parallel. The public theorem is unchanged.
-/

namespace Connes
namespace Sp4

private theorem kernelDetectorBlocks (block : Fin 32) (high : Fin 8)
    (middle low : Fin 16) :
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * block.val + 256 * high.val + 16 * middle.val + low.val)) = true := by
  fin_cases block
  · exact kernelDetectorBlock0 high middle low
  · exact kernelDetectorBlock1 high middle low
  · exact kernelDetectorBlock2 high middle low
  · exact kernelDetectorBlock3 high middle low
  · exact kernelDetectorBlock4 high middle low
  · exact kernelDetectorBlock5 high middle low
  · exact kernelDetectorBlock6 high middle low
  · exact kernelDetectorBlock7 high middle low
  · exact kernelDetectorBlock8 high middle low
  · exact kernelDetectorBlock9 high middle low
  · exact kernelDetectorBlock10 high middle low
  · exact kernelDetectorBlock11 high middle low
  · exact kernelDetectorBlock12 high middle low
  · exact kernelDetectorBlock13 high middle low
  · exact kernelDetectorBlock14 high middle low
  · exact kernelDetectorBlock15 high middle low
  · exact kernelDetectorBlock16 high middle low
  · exact kernelDetectorBlock17 high middle low
  · exact kernelDetectorBlock18 high middle low
  · exact kernelDetectorBlock19 high middle low
  · exact kernelDetectorBlock20 high middle low
  · exact kernelDetectorBlock21 high middle low
  · exact kernelDetectorBlock22 high middle low
  · exact kernelDetectorBlock23 high middle low
  · exact kernelDetectorBlock24 high middle low
  · exact kernelDetectorBlock25 high middle low
  · exact kernelDetectorBlock26 high middle low
  · exact kernelDetectorBlock27 high middle low
  · exact kernelDetectorBlock28 high middle low
  · exact kernelDetectorBlock29 high middle low
  · exact kernelDetectorBlock30 high middle low
  · exact kernelDetectorBlock31 high middle low

private theorem kernelDetectorCheck_all (x : BitVec 16) :
    kernelDetectorCheck x = true := by
  have hxlt : x.toNat < 65536 := by
    simpa using x.toFin.isLt
  let block : Fin 32 := ⟨x.toNat / 2048, by omega⟩
  let high : Fin 8 := ⟨x.toNat % 2048 / 256, by omega⟩
  let middle : Fin 16 := ⟨x.toNat % 256 / 16, by omega⟩
  let low : Fin 16 := ⟨x.toNat % 16, Nat.mod_lt _ (by omega)⟩
  have hval :
      2048 * block.val + 256 * high.val + 16 * middle.val + low.val = x.toNat := by
    dsimp [block, high, middle, low]
    omega
  have hx : BitVec.ofNat 16
      (2048 * block.val + 256 * high.val + 16 * middle.val + low.val) = x := by
    apply BitVec.eq_of_toNat_eq
    have hxlt' : x.toNat < 2 ^ 16 := by
      norm_num at hxlt ⊢
      exact hxlt
    rw [BitVec.toNat_ofNat, hval, Nat.mod_eq_of_lt hxlt']
  rw [← hx]
  exact kernelDetectorBlocks block high middle low

/-- The finite symplectic factor has no nontrivial normal abelian subgroup.
This strengthens the elementary-abelian case used in Zhou §6. -/
theorem no_nontrivial_normal_abelian_subgroup
    (N : Subgroup Group) (hnormal : N.Normal)
    (hab : ∀ x y : N, x * y = y * x) : N = ⊥ := by
  exact no_nontrivial_normal_abelian_subgroup_of_kernelDetector
    kernelDetectorCheck_all N hnormal hab

end Sp4
end Connes
