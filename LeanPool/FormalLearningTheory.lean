/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

import LeanPool.FormalLearningTheory.Theorem

/-!
# Formal Learning Theory Kernel

Machine-verified computational learning theory, ported from
<https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel>.

The completed public results include:

* PAC/VC equivalence via `vc_characterization`.
* The bundled PAC, VC, compression-with-side-information, Rademacher, and
  sample-complexity statement `fundamental_theorem`.
* The Moran-Yehudayoff style compression-with-side-information equivalence
  `fundamental_vc_compression`.
* Gold-style identification results, including `gold_theorem` and
  `mind_change_characterization`.
* Online-learning characterizations and separations, including
  `littlestone_characterization`, `pac_not_implies_online`, and
  `ex_not_implies_pac`.

Sources include standard texts and papers in statistical and online learning
theory: Shalev-Shwartz and Ben-David for PAC/VC theory, Gold's 1967
identification-in-the-limit theorem, Littlestone's online-learning dimension,
and Moran-Yehudayoff compression with side information.
-/
