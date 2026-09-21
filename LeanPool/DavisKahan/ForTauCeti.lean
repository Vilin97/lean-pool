/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

-- Root of the temporary ForTauCeti extraction-staging library.
--
-- Intentionally empty. The lakefile's `globs = ["ForTauCeti.*"]` is authoritative
-- for what gets built, so every `ForTauCeti/` module is compiled directly and no
-- code needs to import this root. The staging layer's terminal state is empty or
-- deleted; see ForTauCeti/README.md.
