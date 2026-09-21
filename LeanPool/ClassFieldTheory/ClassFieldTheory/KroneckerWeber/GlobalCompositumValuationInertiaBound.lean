/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
/-!
# The fixed-conductor local inertia bound for the auxiliary compositum

At each chosen ramified prime, the localization of the single global
compositum embeds in the common local cyclotomic field whose `p`-power part
is exactly the exponent selected from `L`.  The arbitrary-coprime local
bound therefore gives the sharp factor `φ(p^e)`.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The cardinality of the valuation-theoretic inertia group of the fixed
global compositum at its synchronized place above `p`.  Naming this natural
number keeps the completion/localization type out of later declaration
types. -/
noncomputable def kroneckerWeberGlobalCompositumValuationInertiaCard
    (p : Nat.Primes) [Fact p.1.Prime]
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) : ℕ := by
  let M := kroneckerWeberCompositumField L
  let wM :=
    kroneckerWeberGlobalCompositumCyclotomicPadicExtension (L := L) p hp
  let vK := Rat.AbsoluteValue.padic p.1
  let hw := HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
    vK wM (rationalPadicAbsoluteValue_nonarchimedean p.1)
  exact Nat.card
    (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
      (HilbertRamification.absoluteValueExtensionValuationSubring
        vK wM hw))

/-- The exact local factor used in the global product estimate. -/
theorem kroneckerWeberGlobalCompositumValuationInertiaCard_le
    (p : Nat.Primes) [Fact p.1.Prime]
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    kroneckerWeberGlobalCompositumValuationInertiaCard (L := L) p hp ≤
      Nat.totient
        (p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p) := by
  let M := kroneckerWeberCompositumField L
  let wM :=
    kroneckerWeberGlobalCompositumCyclotomicPadicExtension (L := L) p hp
  let r := kroneckerWeberLocalCompositumCoprimePart (L := L) p
  let e := kroneckerWeberLocalRamificationExponent (L := L) p
  have hpr : Nat.Coprime p.1 r :=
    kroneckerWeberLocalCompositumCoprimePart_coprime (L := L) p
  have hi :=
    kroneckerWeberGlobalCompositumLocalizationEmbedding (L := L) p hp
  change Nonempty
    (globalPadicLocalizationCyclotomicAlgHom p.1 M wM
      (r * p.1 ^ e)) at hi
  let i : globalPadicLocalizationCyclotomicAlgHom p.1 M wM
      (r * p.1 ^ e) := Classical.choice hi
  rw [kroneckerWeberGlobalCompositumValuationInertiaCard]
  exact globalPadicInertia_natCard_le_coprimeCyclotomicPrimePowTotient
    p.1 M wM r e hpr i

end KroneckerWeber

end
